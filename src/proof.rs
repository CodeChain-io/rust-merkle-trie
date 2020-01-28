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
use crate::{Trie, TrieError};
use ccrypto::{blake256, BLAKE_NULL_RLP};
use cdb::HashDB;
use primitives::H256;

macro_rules! CRYPTOPROOF_ALL_EQ_CLONE {
    () => {
    H : PartialEq + Clone,
    P : PartialEq + Clone,
    V : PartialEq + Clone};
}


// Unit of proof.
//#[derive(Clone, Eq, PartialEq, Debug, RlpEncodable, RlpDecodable)]
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CryptoProofUnit<H, P, V>
{
    hash: H, // or root
    path: P,
    value: V,
    presence: bool
}

// Abstract trait of being cryptographically provable.
pub trait CryptoProvable<H, P, V>
{
    // Does this verify the unit?
    fn verify(&self, test: &CryptoProofUnit<H, P, V>) -> bool;
}

// This is strongly bound to implementation of TrieDB. I want to specify that but rust has no HKT(?)
#[derive(Eq, PartialEq, Debug)]
pub struct CryptoProof_MerkleTrie {
    proof: Vec<Vec<u8>>
}

impl CryptoProvable<H256, H256, &[u8]> for CryptoProof_MerkleTrie {
    // Proof should start with leaf node.
    fn verify(&self, test: &CryptoProofUnit<H256, H256, &[u8]>) -> bool {
        match self.proof.get(0) {
            None => return false,
            Some(elem) => {
                return false; // TODO
            }
        }
    }
}

/*
Once an instance of this trait is constructed,
it is self-proven and doesn't require any further verification.
It is useful in non-serializing context.
This is enclosed by the module to prevent arbitrary struct initialization.
*/
mod Verified {
    pub trait CryptoProvable<H, P, V, Pf> : super::CryptoProvable<H, P, V> {
        fn construct_and_verify(unit: &super::CryptoProofUnit<H, P, V>, proof: &Pf) -> Option<Box<Self>>;
    }

    pub struct CryptoProof<H, P, V> {
        unit: super::CryptoProofUnit<H, P, V>,
    }

    impl<H, P, V> super::CryptoProvable<H, P, V> for CryptoProof<H, P, V> where
        H : PartialEq + Clone,
        P : PartialEq + Clone,
        V : PartialEq + Clone
    {
        fn verify(&self, test: &super::CryptoProofUnit<H, P, V>) -> bool {
            return self.unit == *test;
        }
    }

    impl<H, P, V, Pf> CryptoProvable<H, P, V, Pf> for CryptoProof<H, P, V> where
        H : PartialEq + Clone,
        P : PartialEq + Clone,
        V : PartialEq + Clone,
        Pf : super::CryptoProvable<H, P, V>
    {
        fn construct_and_verify(unit: &super::CryptoProofUnit<H, P, V>, proof: &Pf) -> Option<Box<Self>> {
            if proof.verify(unit) {
                None
            }
            else {
                let www = unit.clone();
                Some(Box::new(Self{unit: www}))
            }
        }
    }
}

