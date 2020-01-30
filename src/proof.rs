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
use crate::{Trie, TrieDB, TrieError};
use ccrypto::{blake256, BLAKE_NULL_RLP};
use cdb::HashDB;
use primitives::H256;

// Unit of proof.
//#[derive(Clone, Eq, PartialEq, Debug, RlpEncodable, RlpDecodable)]
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CryptoProofUnit<H, K, V> {
    hash: H, // or root
    key: K,
    value: V, // ignored in case of absence
    presence: bool,
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
pub struct CryptoProof_MerkleTrie {
    proof: Vec<Vec<u8>>, // Starts with the closest node to root.
}

// TODO : struct CryptoProof_SkewedTree


impl<'db> CryptoStructure<H256, H256, Vec<u8>> for TrieDB<'db> {
	fn make_proof<'k>(&self, key: &'k H256) 
	-> crate::Result<(CryptoProofUnit<H256, H256, Vec<u8>>, Box<dyn CryptoProvable<H256, H256, Vec<u8>>>)> {
		type Tunit = CryptoProofUnit<H256, H256, Vec<u8>>;
		type Tunit_partial = (H256, NibbleSlice<'k>, Vec<u8>, bool);

		fn make_proof_upto(self_: &TrieDB<'_>, path: &NibbleSlice<'_>, hash: &H256) 
		-> crate::Result<(Tunit_partial, Vec<Vec<u8>>)> {
			let node_rlp = self_.db.get(&hash).ok_or_else(|| TrieError::IncompleteDatabase(*hash))?;

			match Node::decoded(&node_rlp) {
				Some(Node::Leaf(partial, value)) => {
					if &partial == path {
						Ok((hash, path, value, true))
					} else {
						Ok((hash, path, value, false))
					}
				}
				Some(Node::Branch(partial, children)) => {
					if path.starts_with(&partial) {
						make_proof_upto(self_,
							&path.mid(partial.len() + 1),
							children[path.mid(partial.len()).at(0) as usize]
						)
					} else {
						Ok((hash, path, Vec::new(), false))
					}
				}
				None => Ok((hash, path, Vec::new(), false)),
			}
		}

		let hash = blake256(key);
		let path = NibbleSlice::new(&hash);
        match make_proof_upto(self, &path, self.root()) {
			Ok(x) => {
				let unit = Tunit{hash: x.0.0, key: x.0.1, value: x.0.2, presence: x.0.3};
				let provable = CryptoProof_MerkleTrie{proof: x.1};
				Ok((unit, Box::new(provable)))
			}
		}
    }
}

impl CryptoProvable<H256, H256, Vec<u8>> for CryptoProof_MerkleTrie {
    // Proof should start with root node.
    fn verify(&self, test: &CryptoProofUnit<H256, H256, Vec<u8>>) -> bool {
        type Tunit = CryptoProofUnit<H256, H256, Vec<u8>>;

        // step1: verify the value
        fn step1(self_: &CryptoProof_MerkleTrie, test: &Tunit) -> bool {
			!self_.proof.is_empty() &&
            match Node::decoded(&self_.proof[self_.proof.len() - 1]) {
                Some(x) => match x {
                    Node::Leaf(_, value) => test.value == value,
                    _ => false,
                },
                _ => false,
            }
        };

        // step2: verify the root
        fn step2(self_: &CryptoProof_MerkleTrie, test: &Tunit) -> bool {
			!self_.proof.is_empty() &&
            blake256(&self_.proof[0]) == test.hash
        };

        // step3 (presence): verify the key
        fn step3_p(self_: &CryptoProof_MerkleTrie, test: &Tunit) -> bool {
            fn verify_branch(path: &NibbleSlice<'_>, hash: &H256, proof: &[Vec<u8>]) -> bool {
                *hash == blake256(&proof[0])
                    && match Node::decoded(&proof[0]) {
                        Some(x) => match x {
                            Node::Leaf(partial, _) => path == &partial,
                            Node::Branch(partial, table) => 
                                // Note: Does Rust guarantee the short circuit evaluation?
                                proof.len() >= 2 && // detect ill-formed proof 
                            	path.starts_with(&partial) && // check path
								match table[path.mid(partial.len()).at(0) as usize] {
									Some(x) => verify_branch(&path.mid(partial.len() + 1), &x, &proof[1..]),
									None => false
								}
                            
                        },
                        _ => false,
                    }
            };
            let hash = blake256(test.key);
			let path = NibbleSlice::new(&hash);
			!self_.proof.is_empty() &&
            verify_branch(&path, &test.hash, &self_.proof)
        };

        // step3 (absence): verify the key.
        fn step3_a(self_: &CryptoProof_MerkleTrie, test: &Tunit) -> bool {
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
								path.starts_with(&partial) && 
								match children[path.mid(partial.len()).at(0) as usize] {
									Some(x) => {
										proof.len() >= 2 &&
										verify_branch(&path.mid(partial.len() + 1), &x, &proof[1..])
									},
									None => true && proof.len() == 1
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

        if test.presence {
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
                None
            } else {
                Some(Box::new(Self {
                    unit: unit.clone(),
                }))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;
}
