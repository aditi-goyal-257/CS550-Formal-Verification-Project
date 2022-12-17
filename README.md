# CS550-Formal-Verification-Project
This project works on formal verification of an algorithm for finding pair of closest points in 2D. This was done as a part of our project in CS550 - Formal Verification at EPFL.

## Running the code
In order to verify the implementation run
``` bash
stainless Main.scala ListLemmas.scala Utils.scala SparsityLemmas.scala SparsityDef.scala Point.scala BruteForce.scala Properties.scala
```
`stainless` could refer to the stainless.sh script that you may have downloaded from the `stainless-dotty-standalone` release from [here](https://github.com/epfl-lara/stainless/releases).

To run the algorithm on testcases mentioned in `TestCases.scala`:
``` bash
mkdir -p ~/.scalaobjects
scalac -d ~/.scalaobjects $(find <path-to-stainless>/stainless/frontends/library/stainless -name "*.scala") BruteForce.scala ListLemmas.scala Main.scala Point.scala Properties.scala SparsityDef.scala SparsityLemmas.scala TestCases.scala Utils.scala
scala -cp ~/.scalaobjects/ Testing
```

