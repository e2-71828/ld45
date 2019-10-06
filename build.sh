rustc lib.rs --edition 2018 --crate-type rlib
rustc --extern lib=./liblib.rlib --edition=2018 main.rs
