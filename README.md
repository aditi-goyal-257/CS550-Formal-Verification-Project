# CS550-Formal-Verification-Project
This project works on formal verification of an algorithm for finding pair of closest points in 2D. This was done as a part of our project in CS550 - Formal Verification at EPFL.

## Running the code
In order to verify the implementation run
``` bash
stainless Main.scala listUtils/* sparsity/* classes/* BruteForce.scala theorems/*
```
`stainless` could refer to the stainless.sh script that you may have downloaded from the `stainless-dotty-standalone` release from [here](https://github.com/epfl-lara/stainless/releases).

### Runtime
In order to run the benchmarking experiments, navigate to the runtime folder. Then run script.sh with the path to stainless as an argument. You should now see the folder bin populated with runtimes.log and runtimes.pkl.  
``` bash
cd runtime
chmod u+rwx script.sh
./script.sh /path/to/stainless
```
An example usage would be <code> ./script.sh /home/user/Desktop/CS550/stainless/ </code>

You can now open Benchmarking.ipynb and runn all the cells. This notebook populates the pics folder where you can see your plots.
