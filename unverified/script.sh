#!/bin/bash
# Basic for loop
nPoint=2

for i in {1..30}
do
scalac -d ~/.scalaobjects Point.scala TestCases.scala   Generator.scala Unverified.scala && scala -cp ~/.scalaobjects/ Testing $nPoint
echo "Trying $nPoint" ;
nPoint=`expr 2 \* $nPoint` ;
done

