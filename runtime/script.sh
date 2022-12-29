#!/bin/bash
# Basic for loop
nPoints='6 18 54 162 486 1458 4000'
for nPoint in $nPoints
do
scalac -d ~/.scalaobjects $(find /home/suhas/Desktop/PADHAI/sem7/CS550/stainless/frontends/library/stainless -name "*.scala") BruteForce.scala ListLemmas.scala Main.scala Point.scala Properties.scala SparsityDef.scala SparsityLemmas.scala TestCases.scala Utils.scala Generator.scala && scala -cp ~/.scalaobjects/ Testing $nPoint
done

