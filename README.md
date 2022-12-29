# CS550-Formal-Verification-Project
This project works on formal verification of an algorithm for finding pair of closest points in 2D. This was done as a part of our project in CS550 - Formal Verification at EPFL.

## Running the code
In order to verify the implementation run
``` bash
stainless Main.scala listUtils/* sparsity/* classes/* BruteForce.scala theorems/*
```
`stainless` could refer to the stainless.sh script that you may have downloaded from the `stainless-dotty-standalone` release from [here](https://github.com/epfl-lara/stainless/releases).