#!/bin/bash

# Making directories to be used by Benchmarking.ipynb
rm -rf ./bin
rm -rf ./pics
mkdir -p ./bin
mkdir -p ./pics

# Looping from 2^1 to 2^23 and logging the runtime in bin/runtime.log
nPoint=32
for i in {5..23}
do
echo "Calculating time for n = $nPoint"
scalac -d ~/.scalaobjects $(find ${1}/frontends/library/stainless -name "*.scala")  ../BruteForce.scala ../listUtils/ListLemmas.scala ../Main.scala ../classes/Point.scala  ../sparsity/SparsityDef.scala ../sparsity/SparsityLemmas.scala ./src/TestCases.scala ./src/Unverified.scala ../listUtils/Utils.scala ../theorems/Theorems.scala ./src/Generator.scala && scala -cp ~/.scalaobjects/ Testing $nPoint
nPoint=$((nPoint*2)) 
done

