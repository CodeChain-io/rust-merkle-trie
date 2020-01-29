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
use crate::node::Node as Node;
use crate::{Trie, TrieError};
use ccrypto::{blake256, BLAKE_NULL_RLP};
use cdb::HashDB;
use primitives::H256;

// Unit of proof.
//#[derive(Clone, Eq, PartialEq, Debug, RlpEncodable, RlpDecodable)]
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CryptoProofUnit<H, K, V>
{
    hash: H, // or root
    key: K,
    value: V,
    presence: bool
}

// Abstract trait of being cryptographically provable.
pub trait CryptoProvable<H, K, V>
{
    // Does this verify the unit?
    fn verify(&self, test: &CryptoProofUnit<H, K, V>) -> bool;
}

// This is strongly bound to implementation of TrieDB. I want to specify that but rust has no HKT(?)
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CryptoProof_MerkleTrie {
    proof: Vec<Vec<u8>> // from Root to Leaf
}

impl CryptoProof_MerkleTrie {
    fn verify_p(&self, test: &CryptoProofUnit<H256, H256, Vec<u8>>) -> bool {
        type Tunit = CryptoProofUnit<H256, H256, Vec<u8>>;

        /*
        Here the assumption is that 
        - Don't trust RLP decoding
        */

        // step1: verify the value
        fn step1(self_: &CryptoProof_MerkleTrie, test: &Tunit) -> bool {
            match self_.proof.get(self_.proof.len() - 1) {
                None => false, // empty proof
                Some(elem) => {
                    match Node::decoded(elem) {
                        Some(x) => match x {
                            Node::Leaf(_, value) => {
                                if test.value == value {
                                    true
                                } else {
                                    false
                                }
                            },
                            _ => false
                        },
                        _ => false
                    }
                }
            }
        };

        // step2: verify the root
        fn step2(self_: &CryptoProof_MerkleTrie, test: &Tunit) -> bool {
            match self_.proof.get(0) {
                None => false,
                Some(elem) => blake256(elem) == test.hash
            }
        };

        // step3: verify the key
        fn step3(self_: &CryptoProof_MerkleTrie, test: &Tunit) -> bool {
            let path = NibbleSlice::new(&blake256(test.key));
            /*
            Invariants
            */
            fn verify_branch(path: &NibbleSlice<'_>, proof: &[Vec<u8>]) -> bool {
                match Node::decoded(&proof[0]) {
                    Some(x) => match x {
                        Node::Leaf(ns, _) => {
                            *path == ns
                        },
                        Node::Branch(ns, table) => {
                            let nibble = path.at(0);

                            // Note: Does Rust guarantee the short circuit evaluation?
                            proof.len() >= 2 && nibble == ns.at(0) && match table[nibble as usize] {
                                Some(x) => x == blake256(&proof[1]),
                                _ => false
                            } &&  {
                                let next_nibble = path.clone();
                                next_nibble.offset += 1;
                                verify_branch(&next_nibble, &proof[1..])
                            }
                        }
                    },
                    _ => false
                }
            };
            verify_branch(&path, &self_.proof)
        };
        step1(self, test) && step2(self, test) && step3(self, test)
    }

    fn verify_a(&self, test: &CryptoProofUnit<H256, H256, Vec<u8>>) -> bool {
        false
    }
}

impl CryptoProvable<H256, H256, Vec<u8>> for CryptoProof_MerkleTrie {
    // Proof should start with leaf node.
    fn verify(&self, test: &CryptoProofUnit<H256, H256, Vec<u8>>) -> bool {
        if test.presence {
            self.verify_p(test)
        }
        else {
            self.verify_a(test)
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
    pub trait CryptoProvable<H, K, V, P> : super::CryptoProvable<H, K, V> {
        fn construct_and_verify(unit: &super::CryptoProofUnit<H, K, V>, proof: &P) -> Option<Box<Self>>;
    }

    pub struct CryptoProof<H, K, V> {
        unit: super::CryptoProofUnit<H, K, V>,
    }

    impl<H, K, V> super::CryptoProvable<H, K, V> for CryptoProof<H, K, V> where
        H : PartialEq + Clone,
        K : PartialEq + Clone,
        V : PartialEq + Clone
    {
        fn verify(&self, test: &super::CryptoProofUnit<H, K, V>) -> bool {
            return self.unit == *test;
        }
    }

    impl<H, K, V, P> CryptoProvable<H, K, V, P> for CryptoProof<H, K, V> where
        H : PartialEq + Clone,
        K : PartialEq + Clone,
        V : PartialEq + Clone,
        P : super::CryptoProvable<H, K, V>
    {
        fn construct_and_verify(unit: &super::CryptoProofUnit<H, K, V>, proof: &P) -> Option<Box<Self>> {
            if proof.verify(unit) {
                None
            }
            else {
                Some(Box::new(Self{unit: unit.clone()}))
            }
        }
    }
}

