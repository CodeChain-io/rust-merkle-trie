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
use crate::{Trie, TrieError, Node};
use ccrypto::{blake256, BLAKE_NULL_RLP};
use cdb::HashDB;
use primitives::H256;
use crate::proof::{CryptoProofUnit, CryptoProof_MerkleTrie, CryptoProvable, CryptoStructure};

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
}

/// Description of what kind of query will be made to the trie.
type Query<T> = dyn Fn(&[u8]) -> T;

impl<'db> TrieDB<'db> {
    /// Create a new trie with the backing database `db` and `root`
    /// Returns an error if `root` does not exist
    pub fn try_new(db: &'db dyn HashDB, root: &'db H256) -> crate::Result<Self> {
        if !db.contains(root) {
            Err(TrieError::InvalidStateRoot(*root))
        } else {
            Ok(TrieDB {
                db,
                root,
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
                let node_rlp = self.db.get(&hash).ok_or_else(|| TrieError::IncompleteDatabase(hash))?;

                match RlpNode::decoded(&node_rlp) {
                    Some(RlpNode::Leaf(partial, value)) => {
                        if &partial == path {
                            Ok(Some(query(value)))
                        } else {
                            Ok(None)
                        }
                    }
                    Some(RlpNode::Branch(partial, children)) => {
                        if path.starts_with(&partial) {
                            self.get_aux(
                                &path.mid(partial.len() + 1),
                                children[path.mid(partial.len()).at(0) as usize],
                                query,
                            )
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

        self.get_aux(&NibbleSlice::new(&path), Some(root), &|bytes| bytes.to_vec())
    }

    fn is_complete(&self) -> bool {
        *self.root == BLAKE_NULL_RLP || self.is_complete_aux(self.root)
    }
}


impl<'db> CryptoStructure<H256, H256, Vec<u8>> for TrieDB<'db> {    
    fn make_proof<'k>(
        &self,
        key: &'k H256,
    ) -> crate::Result<(CryptoProofUnit<H256, H256, Vec<u8>>, Box<dyn CryptoProvable<H256, H256, Vec<u8>>>)> {

        type Unit = CryptoProofUnit<H256, H256, Vec<u8>>;
        struct UnitPartial<'k> {
            hash: &'k H256,
            key: &'k NibbleSlice<'k>,
            value: Option<Vec<u8>>
        };

        fn make_proof_upto<'k>(db: &'k dyn HashDB, path: &'k NibbleSlice<'_>, hash: &'k H256)
            -> crate::Result<(UnitPartial<'k>, Vec<Vec<u8>>)> {
        let node_rlp = db.get(&hash).ok_or_else(|| TrieError::IncompleteDatabase(*hash))?;

        match Node::decoded(&node_rlp) {
            Some(Node::Leaf(partial, value)) => {
                if &partial == path {
                    Ok((UnitPartial{hash: &hash, key: &path, value: Some(value.to_vec())}, vec![node_rlp]))
                } else {
                    Ok((UnitPartial{hash: &hash, key: &path, value: None}, vec![node_rlp]))
                }
            }
            Some(Node::Branch(partial, children)) => {
                debug_assert!(path.starts_with(&partial));
                let left_path = path.mid(partial.len() + 1);
                match children[path.mid(partial.len()).at(0) as usize] {
                    Some(x) => {
                        let r = make_proof_upto(db, &left_path, &x)?;
                        let u = UnitPartial{hash: hash, key: path, value: r.0.value};
                        Ok((u, [r.1, vec![node_rlp]].concat()))
                    },
                    None => Ok((UnitPartial{hash: &hash, key: &path, value: None}, vec![node_rlp]))
                }
            }
            None => Ok((UnitPartial{hash: &hash, key: &path, value: None}, Vec::new())) // empty trie
        }
    }

        let hash = blake256(key);
        let path = NibbleSlice::new(&hash);
        let x = make_proof_upto(self.db, &path, self.root())?;

        let value : Option<Vec<u8>> = match x.0.value {
            Some(x) => Some(x.to_vec()),
            None => None
        };

        

        let unit = Unit{hash: x.0.hash.clone(), key: hash.clone(), value: value};
        let provable = CryptoProof_MerkleTrie{proof: x.1.into_iter().map(|x| x.clone()).rev().collect()};
        Ok((unit, Box::new(provable)))
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
