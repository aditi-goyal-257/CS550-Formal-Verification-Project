/* This file contains the main properties used to prove the correctness
of functions in Main.scala */

import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.lang.StaticChecks._

import point2d.*
import helper.*
import listLemmas.*
import sparsity.*
import sparsityLemmas.*
import bruteForce.*
import ClosestPoint.findClosestPointInStrip
import ClosestPoint.findClosestPairInStrip
import ClosestPoint.combine
import ClosestPoint.findClosestPairRec
import ClosestPoint.findClosestPair


object lemmas:
    
    def findClosestPairinStripLemma(l : List[Point], res: PairPoint, x: PairPoint) = {
        require(isSortedY(l) && res == findClosestPairInStrip(x)(l))
    }.ensuring(_ => deltaSparse(pairDistance(res), l))


    def coordinateBoundLemma(p0: Point, l: BigInt, d: BigInt, @induct pr: List[Point]) = {
        require(p0.x <= l && d <= (p0.x - l)*(p0.x - l) && pr.forall(p => l <= p.x))
    }.ensuring(_ => pr.forall(p =>  d <= p0.distance(p)))

    /* Proving that on considering the 2-delta wide strip out of all the points,
    we do not lose on any possible answer */
    def divideAndConquerLemma(l1: List[Point], p0: Point, p1: Point, d: BigInt, l: BigInt, pl: List[Point], pr: List[Point], l2: List[Point]): Unit ={
        require(l1.contains(p0) && l1.contains(p1) && p0!=p1 && p0.distance(p1) < d && pl.forall(p => p.x <= l) && pr.forall(p => l <= p.x) && deltaSparse(d, pl) && deltaSparse(d, pr) && l1.content == pl.content ++ pr.content && l2 == l1.filter(p => p.distance(Point(l, p.y)) < d))
        
        if(pl.contains(p0)){
            if(pl.contains(p1)){
                deltaSparsityLemma(d, pl, p1, p0)
            }
            if(d <= p0.distance(Point(l, p0.y))){
                instantiateForAll(pl, p => p.x <= l, p0)
                instantiateForAll(pr, p => l <= p.x, p1)
            }
            filteringLemma(l1, p => p.distance(Point(l, p.y)) < d, p0)

            if(d <= p1.distance(Point(l, p1.y))){
                instantiateForAll(pl, p => p.x <= l, p0)
                instantiateForAll(pr, p => l <= p.x, p1)
            }
            filteringLemma(l1, p => p.distance(Point(l, p.y)) < d, p1)
        }
        else{
            if(pr.contains(p1)){
                deltaSparsityLemma(d, pr, p1, p0)
            }
            if(d <= p0.distance(Point(l, p0.y))){
                instantiateForAll(pl, p => p.x <= l, p1)
                instantiateForAll(pr, p => l <= p.x, p0)
            }
            filteringLemma(l1, p => p.distance(Point(l, p.y)) < d, p0)

            if(d <= p1.distance(Point(l, p1.y))){
                instantiateForAll(pl, p => p.x <= l, p1)
                instantiateForAll(pr, p => l <= p.x, p0)
            }
            filteringLemma(l1, p => p.distance(Point(l, p.y)) < d, p1)
        }
    }.ensuring(_ => l2.contains(p0) && l2.contains(p1))

    /* Correctness of the combine step */
    def combineLemma(ps: List[Point], pl: List[Point], pr: List[Point], l: BigInt, left_pair: PairPoint, right_pair: PairPoint, p: PairPoint) = {
        require(isSortedY(ps) && ps.content == pl.content ++ pr.content && pl.forall(p => p.x <= l) && deltaSparse(pairDistance(left_pair), pl) && pr.forall(p => l <= p.x) && deltaSparse(pairDistance(right_pair), pr) && p == combine(left_pair)(right_pair)(l)(ps))
        val d = pairDistance(p)
        if(!deltaSparse(d, ps)){
            val (p0, p1) = getCounterExampleDeltaSparsity(d, ps)
            reducingDeltaPreservesSparsity(pairDistance(left_pair), d, pl)
            reducingDeltaPreservesSparsity(pairDistance(right_pair), d, pr)
            val combine_filtered = ps.filter(p => p.distance(Point(l, p.y)) < pairDistance(compare(left_pair, right_pair)))
            filterSorted(ps, p => p.distance(Point(l, p.y)) < pairDistance(compare(left_pair, right_pair)))
            val filtered = ps.filter(p => p.distance(Point(l, p.y)) < d)
            filterSorted(ps, p => p.distance(Point(l, p.y)) < d)
            divideAndConquerLemma(ps, p0, p1, d, l, pl, pr, filtered)
            filteringTwiceEquivalentLemma(ps, l, d, pairDistance(compare(left_pair, right_pair)))
            filteringPreservesDeltaSparsity(combine_filtered, p => p.distance(Point(l, p.y)) < d, d)
            deltaSparsityLemma(d, filtered, p0, p1)
        }
    }.ensuring(_ => deltaSparse(pairDistance(p), ps))


    /************************* Lemmas to prove the pair returned has distinct points if the list had only distinct points ***************/

    def closestPointDistinctLemma(p: Point, d: BigInt, l: List[Point], res: Point) ={
        require(!l.isEmpty && isSortedY(l) && p.y <= l.head.y && findClosestPointInStrip(p)(d)(l) == res && !l.contains(p))
    }.ensuring(_ => res != p)

    def closestPairDistinctLemma(x: PairPoint, l: List[Point], res: PairPoint): Unit = {
        require(isDistinct(l) && isSortedY(l) && findClosestPairInStrip(x)(l) == res && x._1 != x._2)
        if(!l.isEmpty && !l.tail.isEmpty){
            val p1 = findClosestPointInStrip(l.head)(pairDistance(x))(l.tail)
            closestPointDistinctLemma(l.head, pairDistance(x), l.tail, p1)
            if(pairDistance(x) <= p1.distance(l.head)){
                val z  = findClosestPairInStrip(x)(l.tail)
                closestPairDistinctLemma(x, l.tail, z)
            }
            else{
                val z = findClosestPairInStrip((l.head, p1))(l.tail)
                closestPairDistinctLemma((l.head, p1), l.tail, z)
            }
        }

    }.ensuring(_ => res._1 != res._2)

    def combineDistinctLemma(lpoint: PairPoint, rpoint: PairPoint, div: BigInt, l: List[Point], res: PairPoint): Unit = {
        require(lpoint._1 != lpoint._2 && rpoint._1 != rpoint._2 && isDistinct(l) && isSortedY(l) && res == combine(lpoint)(rpoint)(div)(l))
        val z = compare(lpoint, rpoint)
        val d = pairDistance(z)
        val l2 = l.filter(p => p.distance(Point(div, p.y)) < d)
        filterSorted(l, p => p.distance(Point(div, p.y)) < d)
        filteringPreservesDistinct(l, p => p.distance(Point(div, p.y)) < d)
        closestPairDistinctLemma(z, l2, res)
    }.ensuring(_ => res._1 != res._2)


    def findClosestPairRecDistinctLemma(l: List[Point], sorted_y: List[Point], p: PairPoint): Unit = {
        require(l.size >= 2 && isSortedX(l) && isDistinct(l) && (sorted_y, p) == findClosestPairRec(l))
        decreases(l.size)
        if(l.size > 3){
            val (left_half, right_half) = l.splitAtIndex(l.size/2)
            // split(l, l.size/2)
            splitDistinctLemma(l, l.size/2)
            val (lsorted, lpoint) = findClosestPairRec(left_half)
            val (rsorted, rpoint) = findClosestPairRec(right_half)
            findClosestPairRecDistinctLemma(left_half, lsorted, lpoint)
            findClosestPairRecDistinctLemma(right_half, rsorted, rpoint)
            val sortedList = mergeY(lsorted, rsorted)
            mergeYDistinctLemma(lsorted, rsorted)
            val res = combine(lpoint)(rpoint)(right_half.head.x)(sortedList)
            combineDistinctLemma(lpoint, rpoint, right_half.head.x, sortedList, res)
        }
        else{
            bruteForceDistinctLemma(l, sorted_y, p)
        }
        
    }.ensuring(_ => isDistinct(sorted_y) && p._1 != p._2)



    /* Correctness of findClosestPairRec */
    def theorem1(xs: List[Point], ys: List[Point], p: PairPoint) = {
        require(1 < xs.length && isSortedX(xs) && (ys, p) == findClosestPairRec(xs))
    }.ensuring(_ => deltaSparse(pairDistance(p), xs))


    /* Correctness of findClosestPair proved by corollary1 + theorem2 + theorem3 */

    def corollary1(xs: List[Point], p: PairPoint) = {
        require(1 < xs.length && p == findClosestPair(xs))
    }.ensuring(_ => deltaSparse(pairDistance(p), xs))

    def theorem2(xs: List[Point], p0: Point, p1: Point) = {
        require(1 < xs.length && (p0, p1) == findClosestPair(xs))
    }.ensuring(_ => xs.contains(p0) && xs.contains(p1))

    def theorem3(xs: List[Point], p0: Point, p1: Point) = {
        require(1 < xs.length && isDistinct(xs) && (p0, p1) == findClosestPair(xs))
        mergeSortXDistinctLemma(xs)
        val l = mergeSortX(xs)
        val res = findClosestPairRec(l)
        findClosestPairRecDistinctLemma(l, res._1, res._2)
    }.ensuring(_ => p0!=p1)