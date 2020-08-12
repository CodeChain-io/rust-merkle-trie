// Copyright 2018-2020 Kodebox, Inc.
// This file is part of CodeChain.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

use crate::nibbleslice::NibbleSlice;
use crate::node::Node as RlpNode;
use crate::proof::{CryptoProof, CryptoProofUnit, CryptoStructure};
use crate::{Node, Trie, TrieError};
use ccrypto::{blake256, BLAKE_NULL_RLP};
use cdb::HashDB;
use lru_cache::LruCache;
use primitives::Bytes;
use primitives::H256;
use std::cell::RefCell;

/// A `Trie` implementation using a generic `HashDB` backing database.
///
/// Use it as a `Trie` trait object. You can use `db()` to get the backing database object.
/// Use `get` and `contains` to query values associated with keys in the trie.
///
/// # Example
/// ```
/// use cdb::*;
/// use merkle_trie::*;
/// use primitives::H256;
///
/// let mut memdb = MemoryDB::new();
/// let mut root = H256::zero();
/// TrieFactory::create(&mut memdb, &mut root).insert(b"foo", b"bar").unwrap();
/// let t = TrieFactory::readonly(&memdb, &root).unwrap();
/// assert!(t.contains(b"foo").unwrap());
/// assert_eq!(t.get(b"foo").unwrap().unwrap(), b"bar".to_vec());
/// ```

pub(crate) struct TrieDB<'db> {
    db: &'db dyn HashDB,
    root: &'db H256,
    cache: RefCell<LruCache<H256, Vec<u8>>>,
}

/// Description of what kind of query will be made to the trie.
type Query<T> = dyn Fn(&[u8]) -> T;

impl<'db> TrieDB<'db> {
    /// Create a new trie with the backing database `db` and `root`
    /// Returns an error if `root` does not exist
    pub fn try_new(db: &'db dyn HashDB, root: &'db H256) -> crate::Result<Self> {
        let cache: RefCell<LruCache<H256, Vec<u8>>> = RefCell::new(LruCache::new(3000));
        if !db.contains(root) {
            Err(TrieError::InvalidStateRoot(*root))
        } else {
            Ok(TrieDB {
                db,
                root,
                cache,
            })
        }
    }

    /// Get auxiliary
    fn get_aux<T>(
        &self,
        path: &NibbleSlice<'_>,
        cur_node_hash: Option<H256>,
        query: &Query<T>,
    ) -> crate::Result<Option<T>> {
        match cur_node_hash {
            Some(hash) => {
                // FIXME: Refactoring is required to reduce access to the cache.
                //        the current code queries the cache twice when the data is cached.
                let node_rlp;
                let decoded_rlp = if self.cache.borrow_mut().contains_key(&hash) {
                    node_rlp = self.cache.borrow_mut().get_mut(&hash).unwrap().to_vec();
                    RlpNode::decoded(&node_rlp)
                } else {
                    node_rlp = self.db.get(&hash).ok_or_else(|| TrieError::IncompleteDatabase(hash))?;
                    self.cache.borrow_mut().insert(hash, (&*node_rlp).to_vec());
                    RlpNode::decoded(&node_rlp)
                };

                match decoded_rlp {
                    Some(RlpNode::Leaf(partial, value)) => {
                        if &partial == path {
                            Ok(Some(query(value)))
                        } else {
                            Ok(None)
                        }
                    }
                    Some(RlpNode::Branch(partial, children)) => {
                        if path.starts_with(&partial) {
                            self.get_aux(&path.mid(partial.len() + 1), children[path.at(partial.len()) as usize], query)
                        } else {
                            Ok(None)
                        }
                    }
                    None => Ok(None),
                }
            }
            None => Ok(None),
        }
    }

    /// Check if every leaf of the trie starting from `hash` exists
    fn is_complete_aux(&self, hash: &H256) -> bool {
        if let Some(node_rlp) = self.db.get(hash) {
            match RlpNode::decoded(node_rlp.as_ref()) {
                Some(RlpNode::Branch(.., children)) => {
                    children.iter().flatten().all(|child| self.is_complete_aux(child))
                }
                Some(RlpNode::Leaf(..)) => true,
                None => false,
            }
        } else {
            false
        }
    }
}

impl<'db> Trie for TrieDB<'db> {
    fn root(&self) -> &H256 {
        self.root
    }

    fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, TrieError> {
        let path = blake256(key);
        let root = *self.root;

        self.get_aux(&NibbleSlice::new(path.as_bytes()), Some(root), &|bytes| bytes.to_vec())
    }

    fn is_complete(&self) -> bool {
        *self.root == BLAKE_NULL_RLP || self.is_complete_aux(self.root)
    }
}

impl<'db> CryptoStructure for TrieDB<'db> {
    /// A proof creation logic for TrieDB.
    /// A proof is basically a list of serialized trie nodes, Vec<Bytes>.
    /// It starts from the one closest to the root and to the leaf. (It may not reach the leaf in absence case.)
    /// Each node can be decoded with RLP. (Note that RLP doesn't guarantee format detail, so you must check our serialization code.)
    /// In case of precense, the list will contain a path from the root to the leaf with the key.
    /// In case of absence, the list will contain a path to the last node that matches the key.
    //
    //          (A: [nil])
    //         /         \
    //      (B, g)        \
    //      /    \         \
    // (C, iant) (D, mail)  (E, clang)
    //
    // Here, the proof of key 'gmail' will be [(RLP encoding of A), (RLP encoding of B), (RLP encoding of D)]
    // Here, the proof of key 'galbi' (absence) will be [(RLP encoding of A), (RLP encoding of B)]
    fn make_proof(&self, key: &[u8]) -> crate::Result<(CryptoProofUnit, CryptoProof)> {
        // it creates a reversed proof for the sake of a more efficient push() operation. (than concat)
        fn make_proof_upto(
            db: &dyn HashDB,
            path: &NibbleSlice<'_>,
            hash: &H256,
        ) -> crate::Result<(Option<Bytes>, Vec<Bytes>)> {
            let node_rlp = db.get(&hash).ok_or_else(|| TrieError::IncompleteDatabase(*hash))?;

            match Node::decoded(&node_rlp) {
                Some(Node::Leaf(partial, value)) => {
                    if &partial == path {
                        Ok((Some(value.to_vec()), vec![node_rlp]))
                    } else {
                        Ok((None, vec![node_rlp]))
                    }
                }
                Some(Node::Branch(partial, children)) => {
                    if path.starts_with(&partial) {
                        match children[path.at(partial.len()) as usize] {
                            Some(x) => {
                                let (value, mut reversed_proof) =
                                    make_proof_upto(db, &path.mid(partial.len() + 1), &x)?;
                                reversed_proof.push(node_rlp);
                                Ok((value, reversed_proof))
                            }
                            None => Ok((None, vec![node_rlp])),
                        }
                    } else {
                        Ok((None, Vec::new()))
                    }
                }
                None => Ok((None, Vec::new())), // empty trie
            }
        }
        let path = blake256(key);
        let (value, reversed_proof) = make_proof_upto(self.db, &NibbleSlice::new(path.as_bytes()), self.root())?;
        let unit = CryptoProofUnit {
            root: *self.root(),
            key: key.to_vec(),
            value,
        };
        Ok((unit, CryptoProof(reversed_proof.iter().rev().cloned().collect())))
    }
}

#[cfg(test)]
mod tests {
    use cdb::MemoryDB;

    use super::*;
    use crate::*;

    fn delete_any_child(db: &mut MemoryDB, root: &H256) {
        let node_rlp = db.get(root).unwrap();
        match RlpNode::decoded(&node_rlp).unwrap() {
            RlpNode::Leaf(..) => {
                db.remove(root);
            }
            RlpNode::Branch(.., children) => {
                let first_child = children.iter().find(|c| c.is_some()).unwrap().unwrap();
                db.remove(&first_child);
            }
        }
    }

    #[test]
    fn get() {
        let mut memdb = MemoryDB::new();
        let mut root = H256::zero();
        {
            let mut t = TrieDBMut::new(&mut memdb, &mut root);
            t.insert(b"A", b"ABC").unwrap();
            t.insert(b"B", b"ABCBA").unwrap();
        }

        let t = TrieDB::try_new(&memdb, &root).unwrap();
        assert_eq!(t.get(b"A"), Ok(Some(b"ABC".to_vec())));
        assert_eq!(t.get(b"B"), Ok(Some(b"ABCBA".to_vec())));
        assert_eq!(t.get(b"C"), Ok(None));
    }

    #[test]
    fn is_complete_success() {
        let mut memdb = MemoryDB::new();
        let mut root = H256::zero();
        {
            let mut t = TrieDBMut::new(&mut memdb, &mut root);
            t.insert(b"A", b"ABC").unwrap();
            t.insert(b"B", b"ABCBA").unwrap();
        }

        let t = TrieDB::try_new(&memdb, &root).unwrap();
        assert!(t.is_complete());
    }

    #[test]
    fn is_complete_fail() {
        let mut memdb = MemoryDB::new();
        let mut root = H256::zero();
        {
            let mut t = TrieDBMut::new(&mut memdb, &mut root);
            t.insert(b"A", b"ABC").unwrap();
            t.insert(b"B", b"ABCBA").unwrap();
        }
        delete_any_child(&mut memdb, &root);

        let t = TrieDB::try_new(&memdb, &root).unwrap();
        assert!(!t.is_complete());
    }
}
