/* This file contains functions and lemmas for the brute force case,
where the number of points in the list is 2 or 3 */

import stainless.collection._
import stainless.lang._
import stainless.annotation._

import point2d.*
import helper.*
import listLemmas.*
import sparsity.*
import sparsityLemmas.*
import ClosestPoint.findClosestPairRec


object bruteForce:
     
    /* The base case of findClosestPairRec, given a list of points,
    returns the same list of points sorted by y-coordinates as well
    as well as closest pair of points */
    def bruteForce(l: List[Point]): (List[Point], PairPoint) =  
    {
        require(l.size <= 3 && l.size >= 2) 
        val z = mergeSortY(l)
        elementInsideListLemma(l, 1)
        if l.size == 2 then (z, (l(0), l(1)))
        else {
            elementInsideListLemma(l, 2)
            val a = l(0).distance(l(1))
            val b = l(0).distance(l(2))
            val c = l(1).distance(l(2))

            /* Explicitly make conditions for verification process*/
            if(a <= b  && b <= c){
                bruteForceConditionLemma(l(0), l(1), l(2))
                (z, (l(0), l(1)))
            }
            else if(a <= c && c <= b){
                bruteForceConditionLemma(l(1), l(0), l(2))
                (z, (l(1), l(0)))
            }
            else if(b <= a && a <= c){
                bruteForceConditionLemma(l(0), l(2), l(1))
                (z, (l(0), l(2)))
            }
            else if(b <=c && c <= a){
                bruteForceConditionLemma(l(2), l(0), l(1))
                (z, (l(2), l(0)))
            }
            else if(c <= a && a <= b){
                bruteForceConditionLemma(l(1), l(2), l(0))
                (z, (l(1), l(2)))
            }
            else{
                assert(c <= b && b <= a)
                bruteForceConditionLemma(l(2), l(1), l(0))
                (z, (l(2), l(1)))
            }
        }
    }.ensuring(res0 => isSortedY(res0._1) && deltaSparse(pairDistance(res0._2), l) && l.contains(res0._2._1) && l.contains(res0._2._2))

    /* Proves that if the list given to bruteForce is distinct, the
    points returned by it are also distinct */
    def bruteForceDistinctLemma(l: List[Point], sorted_y: List[Point], p: PairPoint) = {
        require(l.size >= 2 && l.size <= 3 && isSortedX(l) && isDistinct(l) && (sorted_y, p) == findClosestPairRec(l))
        val z = mergeSortY(l)
        mergeSortYDistinctLemma(l)
        if (l.size == 2) then distinctLemma(l, 0, 1)
        else {
            val a = l(0).distance(l(1))
            val b = l(0).distance(l(2))
            val c = l(1).distance(l(2))

            if(a <= b  && b <= c){
                distinctLemma(l, 0, 1)
            }
            else if(a <= c && c <= b){
                distinctLemma(l, 1, 0)
            }
            else if(b <= a && a <= c){
                distinctLemma(l, 0, 2)
            }
            else if(b <=c && c <= a){
                distinctLemma(l, 2, 0)
            }
            else if(c <= a && a <= b){
                distinctLemma(l, 1, 2)
            }
            else{
                assert(c <= b && b <= a)
                distinctLemma(l, 2, 1)
            }
        }
    }.ensuring(isDistinct(sorted_y) && p._1 != p._2)

    /* Assumes a certain ordering between distances of points,
    proves that it is deltaSparse where delta is the smallest distance between
    any pair of points */
    def bruteForceConditionLemma(p1: Point, p2: Point, p3: Point) = {
        require(p1.distance(p2) <= p1.distance(p3) && p1.distance(p3) <= p2.distance(p3))
        val a = p1.distance(p2)
        val b = p1.distance(p3)
        val c = p2.distance(p3)
        assert(a == p1.distance(p2))
        distanceCommutavityLemma(p1, p2)
        assert(a <= p2.distance(p1))

        assert(p1.distance(p2) <= p1.distance(p3))
        assert(a <= p1.distance(p3))
        distanceCommutavityLemma(p1, p3)
        assert(a <= p3.distance(p1))

        assert(deltaSparsePoint(a, p1, List(p3)))
        assert(deltaSparsePoint(a, p1, List(p2, p3)))

        assert(b <= p2.distance(p3))
        distanceCommutavityLemma(p2, p3)

        assert(deltaSparsePoint(b, p2, List(p3)))
        reducingDeltaPreservesPointSparsity(b, a, p2, List(p3))
        assert(deltaSparse(a, List(p3)))
        assert(deltaSparsePoint(a, p3, List()))
    }.ensuring(_ => deltaSparse(p1.distance(p2), List[Point](p1, p2, p3)))