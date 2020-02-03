// Copyright 2020 Kodebox, Inc.
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
use crate::node::Node;
use ccrypto::{blake256, BLAKE_NULL_RLP};
use primitives::H256;

// Unit of proof.
//#[derive(Clone, Eq, PartialEq, Debug, RlpEncodable, RlpDecodable)]
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CryptoProofUnit<H, K, V> {
    pub hash: H, // or root
    pub key: K,
    pub value: Option<V>, // None in case of absence
}

// Abstract trait of being cryptographically provable.
pub trait CryptoProvable<H, K, V> {
    // Does this verify the unit? Note: Invalid / ill-formed proof should return false, not abort or error
    fn verify(&self, test: &CryptoProofUnit<H, K, V>) -> bool;
}

// Abstract trait of being a data structure that can provide CryptoProvable for its element.
pub trait CryptoStructure<H, K, V> {
    fn make_proof(&self, key: &K) -> crate::Result<(CryptoProofUnit<H, K, V>, Box<dyn CryptoProvable<H, K, V>>)>;
}

// This is strongly bound to implementation of TrieDB. I want to specify that but rust has no HKT(?)
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CryptoProofMerkleTrie {
    pub proof: Vec<Vec<u8>>, // Starts with the closest node to root.
}

pub struct CryptoProofSkewedTree {
    // TODO
}


impl CryptoProvable<H256, H256, Vec<u8>> for CryptoProofMerkleTrie {
    // Proof should start with root node.
    fn verify(&self, test: &CryptoProofUnit<H256, H256, Vec<u8>>) -> bool {
        type Tunit = CryptoProofUnit<H256, H256, Vec<u8>>;

        // step1: verify the value
        fn step1(self_: &CryptoProofMerkleTrie, test: &Tunit) -> bool  {
            !self_.proof.is_empty() && 
            match Node::decoded(&self_.proof[self_.proof.len() - 1]) {
                Some(x) => match x {
                    Node::Leaf(_, value) => test.value.as_ref().unwrap() == &value,
                    _ => false,
                },
                _ => false,
            }
        };

        // step2: verify the root
        fn step2(self_: &CryptoProofMerkleTrie, test: &Tunit) -> bool {
            !self_.proof.is_empty() && blake256(&self_.proof[0]) == test.hash
        };

        // step3 (presence): verify the key
        fn step3_p(self_: &CryptoProofMerkleTrie, test: &Tunit) -> bool {
            fn verify_branch(path: &NibbleSlice<'_>, hash: &H256, proof: &[Vec<u8>]) -> bool {
                *hash == blake256(&proof[0])
                    && match Node::decoded(&proof[0]) {
                        Some(x) => match x {
                            Node::Leaf(partial, _) => path == &partial,
                            Node::Branch(partial, table) =>
                            // Note: Does Rust guarantee the short circuit evaluation?
                            {
                                proof.len() >= 2 && // detect ill-formed proof 
                            	path.starts_with(&partial) && // check path
								match table[path.mid(partial.len()).at(0) as usize] {
									Some(x) => verify_branch(&path.mid(partial.len() + 1), &x, &proof[1..]),
									None => false
								}
                            }
                        },
                        _ => false,
                    }
            };
            let hash = blake256(test.key);
            let path = NibbleSlice::new(&hash);
            !self_.proof.is_empty() && verify_branch(&path, &test.hash, &self_.proof)
        };

        // step3 (absence): verify the key.
        fn step3_a(self_: &CryptoProofMerkleTrie, test: &Tunit) -> bool {
            // special case of an empty trie.
            if self_.proof.is_empty() && test.hash == BLAKE_NULL_RLP {
                return true
            }
            fn verify_branch(path: &NibbleSlice<'_>, hash: &H256, proof: &[Vec<u8>]) -> bool {
                *hash == blake256(&proof[0])
                    && match Node::decoded(&proof[0]) {
                        Some(x) => match x {
                            Node::Leaf(partial, _) => path != &partial, // special case : there is only one leaf node in the trie
                            Node::Branch(partial, children) => {
                                // Note: Does Rust guarantee the short circuit evaluation?
                                path.starts_with(&partial)
                                    && match children[path.mid(partial.len()).at(0) as usize] {
                                        Some(x) => {
                                            proof.len() >= 2
                                                && verify_branch(&path.mid(partial.len() + 1), &x, &proof[1..])
                                        }
                                        None => true && proof.len() == 1,
                                    }
                            }
                        },
                        _ => false,
                    }
            };
            let hash = blake256(test.key);
            let path = NibbleSlice::new(&hash);
            verify_branch(&path, &test.hash, &self_.proof)
        };

        if test.value.is_some() {
            step1(self, test) && step2(self, test) && step3_p(self, test)
        } else {
            step2(self, test) && step3_a(self, test)
        }
    }
}


/*
Once an instance of this trait is constructed,
it is self-proven and doesn't require any further verification.
It is useful in non-serializing context.
This is enclosed by the module to prevent arbitrary struct initialization.
*/
mod verified {
    pub trait CryptoProvable<H, K, V, P>: super::CryptoProvable<H, K, V> {
        // It may return None for invalid proof.
        fn construct_and_verify(unit: &super::CryptoProofUnit<H, K, V>, proof: &P) -> Option<Box<Self>>;
    }

    pub struct CryptoProof<H, K, V> {
        unit: super::CryptoProofUnit<H, K, V>,
    }

    impl<H, K, V> super::CryptoProvable<H, K, V> for CryptoProof<H, K, V>
    where
        H: PartialEq + Clone,
        K: PartialEq + Clone,
        V: PartialEq + Clone,
    {
        // now the verification is just checking the unit
        fn verify(&self, test: &super::CryptoProofUnit<H, K, V>) -> bool {
            self.unit == *test
        }
    }

    impl<H, K, V, P> CryptoProvable<H, K, V, P> for CryptoProof<H, K, V>
    where
        H: PartialEq + Clone,
        K: PartialEq + Clone,
        V: PartialEq + Clone,
        P: super::CryptoProvable<H, K, V>,
    {
        fn construct_and_verify(unit: &super::CryptoProofUnit<H, K, V>, proof: &P) -> Option<Box<Self>> {
            if proof.verify(unit) {
                Some(Box::new(Self {
                    unit: unit.clone(),
                }))
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;
    use cdb::MemoryDB;

    type ProofUnit = CryptoProofUnit<H256, H256, Vec<u8>>;

    #[test]
    fn some_trie_1() {
        let mut memdb = MemoryDB::new();
        let mut root = H256::zero();
        {
            let mut t = TrieDBMut::new(&mut memdb, &mut root);
            t.insert(b"A", b"Beethoven").unwrap();
            t.insert(b"B", b"Tchaikovsky").unwrap();
            t.insert(b"C", b"Brahms").unwrap();
            t.insert(b"D", b"Mozart").unwrap();
            t.insert(b"E", b"Bruckner").unwrap();
            t.insert(b"F", b"Mahler").unwrap();
        }

        let t = TrieDB::try_new(&memdb, &root).unwrap();

        {
            let unit = ProofUnit{hash: t.root().clone(), key: blake256(b"B"), value: Some(b"Tchaikovsky".to_vec())};

            let proof = t.make_proof(&blake256(b"B")).unwrap();
            println!("{:?}", proof.0);

            assert_eq!(proof.1.verify(&unit), true);
        }


        let t = TrieDB::try_new(&memdb, &root).unwrap();
        assert_eq!(t.get(b"A"), Ok(Some(b"ABC".to_vec())));
        assert_eq!(t.get(b"B"), Ok(Some(b"ABCBA".to_vec())));
        assert_eq!(t.get(b"C"), Ok(None));
    }
}
