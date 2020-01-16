# Merkle-Trie [![License: AGPL v3](https://img.shields.io/badge/License-AGPL%20v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)
The merkle trie used by [CodeChain](https://github.com/CodeChain-io/codechain) and [Foundry](https://github.com/CodeChain-io/foundry).

## Usage

The rust-merkle-trie crate provides merkle trie implementations. CodeChain and Foundry use a merkle trie to hold the states with authentication. We differ from the merkle patricia trie in Ethereum; details can be found [here](https://github.com/CodeChain-io/codechain/blob/master/spec/Merkle-Trie.md). 

Let's use the merkle trie to show an example:

```rust
use merkle_trie::{Trie, TrieFactory, TrieMut};
use cdb::MemoryDB;
use primitives::H256;

// initialize
let mut memdb = MemoryDB::new();
let mut root = H256::zero();
let mut trie = TrieDBMut::new(&mut memdb, &mut root);

// insert
trie.insert(&[0x01u8, 0x23], &[0x01u8, 0x23]).unwrap();
assert_eq!(*trie.root(), trie_root(vec![(vec![0x01u8, 0x23], vec![0x01u8, 0x23])]));

// get
assert_eq!(trie.get(&0x01u8, 0x23]).unwrap().unwrap(), vec!0x01u8, 0x23]);
assert_eq!(t.get(&[0x02u8]), Ok(None));

// remove
trie.remove(&0x01u8, 0x23]).unwrap();
assert_eq!(t.get(&0x01u8, 0x23]), Ok(None));
```


## Build

Download foundry code

```sh
git clone git@github.com:CodeChain-io/rust-merkle-trie.git
cd rust-merkle-trie
```

Build in debug mode

```sh
cargo build
```

## Test

Developers are strongly encouraged to write unit tests for new code, and to submit new unit tests for old code. Unit tests can be compiled and run with: `cargo test --all`. For more details, please refer to [Unit Tests](https://github.com/CodeChain-io/codechain/wiki/Unit-Tests).

## Benchmark

Official documentation for usage of cargo bench:  
https://doc.rust-lang.org/1.15.1/book/benchmark-tests.html

We can run the benchmark test with `cargo bench`:

```sh
cargo bench
```