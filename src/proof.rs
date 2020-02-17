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
use primitives::Bytes;
use primitives::H256;

// Unit of a proof.
//#[derive(Clone, Eq, PartialEq, Debug, RlpEncodable, RlpDecodable)]
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CryptoProofUnit {
    pub root: H256,
    pub key: Bytes,
    pub value: Option<Bytes>, // None in case of absence
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CryptoProof(pub Vec<Bytes>);

pub trait CryptoStructure {
    fn make_proof(&self, key: &[u8]) -> crate::Result<(CryptoProofUnit, CryptoProof)>;
}

/// A verification logic of TrieDB's Merkle proof.
/// For the format of proof, check the make_proof() function.
/// It verifies the proof with a given unit of test.
/// It should never abort or fail, but only return 'false' as a result of getting an invalid or ill-formed proof.
pub fn verify(proof: &CryptoProof, test: &CryptoProofUnit) -> bool {
    // step1: verify the value
    fn step1(proof: &CryptoProof, test: &CryptoProofUnit) -> bool {
        match Node::decoded(&proof.0.last().unwrap()) {
            Some(x) => match x {
                Node::Leaf(_, value) => test.value.as_ref().unwrap() == &value,
                _ => false,
            },
            _ => false,
        }
    };

    // step2: verify the root
    fn step2(proof: &CryptoProof, test: &CryptoProofUnit) -> bool {
        blake256(&proof.0[0]) == test.root
    };

    // step3 (presence): verify the key
    fn step3_p(proof: &CryptoProof, test: &CryptoProofUnit) -> bool {
        fn verify_branch(path: &NibbleSlice<'_>, hash: &H256, proof: &[Bytes]) -> bool {
            if *hash != blake256(&proof[0]) {
                return false
            }
            match Node::decoded(&proof[0]) {
                Some(Node::Leaf(partial, _)) => path == &partial,
                Some(Node::Branch(partial, table)) => {
                    if proof.len() < 2 {
                        // detect ill-formed proof
                        return false
                    }
                    if !path.starts_with(&partial) {
                        return false
                    }
                    match table[path.at(partial.len()) as usize] {
                        Some(x) => verify_branch(&path.mid(partial.len() + 1), &x, &proof[1..]),
                        None => false,
                    }
                }
                None => false,
            }
        };
        let path = blake256(&test.key);
        verify_branch(&NibbleSlice::new(&path), &test.root, &proof.0)
    };

    // step3 (absence): verify the key.
    fn step3_a(proof: &CryptoProof, test: &CryptoProofUnit) -> bool {
        fn verify_branch(path: &NibbleSlice<'_>, hash: &H256, proof: &[Bytes]) -> bool {
            if *hash != blake256(&proof[0]) {
                return false
            }
            match Node::decoded(&proof[0]) {
                Some(Node::Leaf(partial, _)) => path != &partial, // special case : there is only one leaf node in the trie,
                Some(Node::Branch(partial, children)) => {
                    if !path.starts_with(&partial) {
                        return false
                    }
                    match children[path.at(partial.len()) as usize] {
                        Some(x) => proof.len() >= 2 && verify_branch(&path.mid(partial.len() + 1), &x, &proof[1..]),
                        None => proof.len() == 1,
                    }
                }
                None => false,
            }
        };
        let path = blake256(&test.key);
        verify_branch(&NibbleSlice::new(&path), &test.root, &proof.0)
    };

    if proof.0.is_empty() {
        return test.root == BLAKE_NULL_RLP && test.value.is_none() // special case of an empty trie.
    }
    if test.value.is_some() {
        step1(proof, test) && step2(proof, test) && step3_p(proof, test)
    } else {
        step2(proof, test) && step3_a(proof, test)
    }
}


#[cfg(test)]
mod tests {
    extern crate rand;

    use super::*;
    use crate::*;
    use cdb::MemoryDB;
    use rand::{rngs::StdRng, Rng};

    fn simple_test<'db>(t: &TrieDB<'db>, key: Bytes, value: Option<&[u8]>, key_proof: &[u8], result: bool) {
        let unit = CryptoProofUnit {
            root: *t.root(),
            key,
            value: value.map(|x| x.to_vec()),
        };
        let proof = t.make_proof(key_proof).unwrap();
        assert_eq!(verify(&proof.1, &unit), result);
    }

    #[test]
    fn empty_trie() {
        let iteration = 100;
        let seed = [0 as u8; 32];
        let mut rng: StdRng = rand::SeedableRng::from_seed(seed);

        for _ in 0..iteration {
            let mut memdb = MemoryDB::new();
            let mut root = H256::zero();
            TrieDBMut::new(&mut memdb, &mut root);

            // unused pair
            let k1 = format!("{}", rng.gen::<u64>());
            let v1 = format!("{}", rng.gen::<u64>());
            let (keyu, valu) = { (k1.as_bytes(), v1.as_bytes()) };

            let t = TrieDB::try_new(&memdb, &root).unwrap();

            simple_test(&t, keyu.to_vec(), Some(valu), &keyu, false);
            simple_test(&t, keyu.to_vec(), None, &keyu, true);
        }
    }

    #[test]
    fn single_trie() {
        let iteration = 100;
        let seed = [0 as u8; 32];
        let mut rng: StdRng = rand::SeedableRng::from_seed(seed);

        for _ in 0..iteration {
            let mut memdb = MemoryDB::new();
            let mut root = H256::zero();
            let mut mt = TrieDBMut::new(&mut memdb, &mut root);

            // unused pair
            let ku = format!("{}", rng.gen::<u64>());
            let vu = format!("{}", rng.gen::<u64>());
            let (keyu, valu) = (ku.as_bytes(), vu.as_bytes());

            let k1 = format!("{}", rng.gen::<u64>());
            let v1 = format!("{}", rng.gen::<u64>());
            let (key1, val1) = (k1.as_bytes(), v1.as_bytes());
            mt.insert(key1, val1).unwrap();

            if key1 == keyu || val1 == valu {
                continue
            }

            let t = TrieDB::try_new(&memdb, &root).unwrap();

            // Be careful: there are some case where the proof is not unique.
            simple_test(&t, key1.to_vec(), Some(val1), &key1, true);
            simple_test(&t, key1.to_vec(), Some(val1), &keyu, true); //be careful!
            simple_test(&t, key1.to_vec(), Some(valu), &key1, false);
            simple_test(&t, key1.to_vec(), Some(valu), &keyu, false);
            simple_test(&t, key1.to_vec(), None, &key1, false);
            simple_test(&t, key1.to_vec(), None, &keyu, false);
            simple_test(&t, keyu.to_vec(), Some(val1), &key1, false);
            simple_test(&t, keyu.to_vec(), Some(val1), &keyu, false);
            simple_test(&t, keyu.to_vec(), Some(valu), &key1, false);
            simple_test(&t, keyu.to_vec(), Some(valu), &keyu, false);
            simple_test(&t, keyu.to_vec(), None, &key1, true); //be careful!
            simple_test(&t, keyu.to_vec(), None, &keyu, true);
        }
    }

    #[test]
    fn some_trie() {
        let iteration = 100;
        let size = 234;
        let seed = [0 as u8; 32];
        let mut rng: StdRng = rand::SeedableRng::from_seed(seed);

        for _ in 0..iteration {
            let mut memdb = MemoryDB::new();
            let mut root = H256::zero();
            let mut mt = TrieDBMut::new(&mut memdb, &mut root);

            // unused pair
            let ku = format!("{}", rng.gen::<u64>());
            let vu = format!("{}", rng.gen::<u64>());
            let (keyu, valu) = (ku.as_bytes(), vu.as_bytes());

            let k1 = format!("{}", rng.gen::<u64>());
            let v1 = format!("{}", rng.gen::<u64>());
            let (key1, val1) = (k1.as_bytes(), v1.as_bytes());
            mt.insert(key1, val1).unwrap();

            let k2 = format!("{}", rng.gen::<u64>());
            let v2 = format!("{}", rng.gen::<u64>());
            let (key2, val2) = (k2.as_bytes(), v2.as_bytes());
            mt.insert(key2, val2).unwrap();

            if key1 == keyu || val1 == valu || key2 == keyu || val2 == valu {
                continue
            }

            let mut flag = true;
            for _ in 0..size {
                let k = format!("{}", rng.gen::<u64>());
                let v = format!("{}", rng.gen::<u64>());
                mt.insert(k.as_bytes(), v.as_bytes()).unwrap();
                if k.as_bytes() == keyu || v.as_bytes() == valu {
                    flag = false;
                    break
                }
            }
            if !flag {
                continue // skip this iteration
            }

            let t = TrieDB::try_new(&memdb, &root).unwrap();

            simple_test(&t, key1.to_vec(), Some(val1), &key1, true);
            simple_test(&t, key1.to_vec(), Some(val1), &key2, false);
            simple_test(&t, key1.to_vec(), Some(val1), &keyu, false);
            simple_test(&t, key1.to_vec(), Some(val2), &key1, false);
            simple_test(&t, key1.to_vec(), Some(val2), &key2, false);
            simple_test(&t, key1.to_vec(), Some(val2), &keyu, false);
            simple_test(&t, key1.to_vec(), None, &key1, false);
            simple_test(&t, key1.to_vec(), None, &key2, false);
            simple_test(&t, key1.to_vec(), None, &keyu, false);

            simple_test(&t, keyu.to_vec(), Some(val1), &key1, false);
            simple_test(&t, keyu.to_vec(), Some(val1), &key2, false);
            simple_test(&t, keyu.to_vec(), Some(val1), &keyu, false);
            simple_test(&t, keyu.to_vec(), None, &key1, false);
            simple_test(&t, keyu.to_vec(), None, &key2, false);
            simple_test(&t, keyu.to_vec(), None, &keyu, true);
        }
    }

    // proof is created manually here
    #[test]
    fn some_malicious() {
        // TODO
    }
}
