/* Implementation of function for finding closest pair of points */

import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._

import point2d.*
import helper.*
import listLemmas.*
import sparsity.*
import sparsityLemmas.*
import bruteForce.*
import lemmas.*

object ClosestPoint {


    def findClosestPairInStrip(x: PairPoint)(@induct l: List[Point]):PairPoint =
    {
        require(isSortedY(l))
        if l.isEmpty || l.tail.isEmpty then x
        else {
            val p1 = findClosestPointInStrip(l.head)(pairDistance(x))(l.tail)
            assert(deltaSparsePoint(min(p1.distance(l.head), pairDistance(x)), l.head, l.tail))
            if pairDistance(x) <= p1.distance(l.head) then{
                //assert(min(p1.distance(l.head), pairDistance(x)) == pairDistance(x))
                // assert(deltaSparsePoint(pairDistance(x), l.head, l.tail))
                val z = findClosestPairInStrip(x)(l.tail)
                reducingDeltaPreservesPointSparsity(pairDistance(x), pairDistance(z), l.head, l.tail)
                // reducingPreservesPointSparsityLemma(l.tail, l.head, pairDistance(x), pairDistance(z))
                // assert(deltaSparsePoint(pairDistance(z), l.head, l.tail))
                z
            }
            else {
                // assert(deltaSparsePoint(p1.distance(l.head), l.head, l.tail))
                val z = findClosestPairInStrip((l.head, p1))(l.tail)
                reducingDeltaPreservesPointSparsity(l.head.distance(p1), pairDistance(z), l.head, l.tail)
                // reducingPreservesPointSparsityLemma(l.tail, l.head, p1.distance(l.head), pairDistance(z))
                // assert(deltaSparsePoint(p1.distance(l.head), l.head, l.tail))
                z
            }
        }
    }
    .ensuring(res0 => deltaSparse(pairDistance(res0), l) && pairDistance(res0) <= pairDistance(x) && (res0 == x || (l.contains(res0._1) && l.contains(res0._2))))
    
    // l (strip) is sorted by y coordinates
    def findClosestPointInStrip(p: Point)(d: BigInt)(l: List[Point]): Point =
    {
        require(!l.isEmpty && isSortedY(l) && p.y <= l.head.y)
        if l.tail.isEmpty then l.head
        else if d <= (l.head.y - p.y)*(l.head.y - p.y) then {

            tranisitiveSortedListLemmaY(l, p.y, l.head.y)
            // assert(l.forall(p1 => l.head.y <= p1.y))

            subtractingPreservesPredicate(l, l.head.y, p.y)
            // assert(l.forall(p1 => (l.head.y - p.y) <= (p1.y - p.y)))

            squaringPreservesPredicate(l, l.head.y - p.y, p.y)
            // assert(l.forall(p1 => (l.head.y - p.y)*(l.head.y - p.y) <= (p1.y - p.y)*(p1.y - p.y)))

            transitiveSquareSortedListLemmaY(l, l.head.y - p.y, p.y, d)
            // assert(l.forall(p1 => d <= (p1.y - p.y)*(p1.y - p.y)))
            
            addingPreservesPredicate(l, d, p.y, p.x)
            // assert(l.forall(p1 => d <= (p1.x - p.x)*(p1.x - p.x) + (p1.y - p.y)*(p1.y - p.y)))

            distanceFormulaValidForList(l, p)
            // assert(l.forall(p1 => p1.distance(p) == (p1.x - p.x)*(p1.x - p.x) + (p1.y - p.y)*(p1.y - p.y)))
           
            distanceTransitivityLemma(l, p, d)
            // assert(l.forall(p1 => d <= p1.distance(p)))
            addingPredicateToOrPreserves(d, p, l)
            // assert(l.forall(p1 => p == p1 || d <= p1.distance(p)))
            // assert(deltaSparsePoint(d, p, l))
            l.head
        }
        else{
            val p1 = findClosestPointInStrip(p)(min(d, p.distance(l.head)))(l.tail)
            if p.distance(l.head) <= p.distance(p1) then l.head else p1
        }
    }
    .ensuring(res0 => deltaSparsePoint(min(p.distance(res0), d), p, l) && l.contains(res0))

    

    // l (complete list) is sorted by y coordinates 
    def combine(lpoint: PairPoint)(rpoint: PairPoint)(div: BigInt)(l: List[Point]): PairPoint = {
        require(isSortedY(l))
        val z = compare(lpoint, rpoint)
        val d = pairDistance(z)
        val l2 = filterSorted(l)(p => p.distance(Point(div, p.y)) < d)
        findClosestPairInStrip(z)(l2)
    }.ensuring(res0 => deltaSparse(pairDistance(res0), filterSorted(l)(p => p.distance(Point(div, p.y)) < pairDistance(compare(lpoint, rpoint)))) && pairDistance(res0) <= pairDistance(compare(lpoint, rpoint)) && (lpoint ==res0 || rpoint ==res0 || l.contains(res0._1) && l.contains(res0._2)))
        

    // l (complete list) is sorted by x coordinates, return sorted by y coordinates
    def findClosestPairRec(l: List[Point]): (List[Point], PairPoint) ={
        require(l.size >= 2 && isSortedX(l))
        decreases(l.size)
        if l.size <= 3 then bruteForce(l)
        else{
            val (left_half, right_half) = split(l, l.size/2)
            // assert(isSortedX(left_half))
            // assert(isSortedX(right_half))
            val (lsorted, lpoint) = findClosestPairRec(left_half)
            val (rsorted, rpoint) = findClosestPairRec(right_half)
            val sortedList = mergeY(lsorted, rsorted)
            val res = combine(lpoint)(rpoint)(right_half.head.x)(sortedList)
            combineLemma(sortedList, left_half, right_half, right_half.head.x, lpoint, rpoint, res)
            // assert(deltaSparse(pairDistance(res), sortedList))
            // assert(sortedList.content == l.content)
            subsetPreservesDeltaSparsity(pairDistance(res), sortedList, l)
            (sortedList, res)
        }
    }.ensuring(res0 => res0._1.content == l.content && isSortedY(res0._1) && deltaSparse(pairDistance(res0._2), l) && l.contains(res0._2._1) && l.contains(res0._2._2))

    def findClosestPair(l: List[Point]): PairPoint = {
        require(l.size >= 2)
        val p = findClosestPairRec(mergeSortX(l))._2
        subsetPreservesDeltaSparsity(pairDistance(p), mergeSortX(l), l)
        p
    }.ensuring(res0 => deltaSparse(pairDistance(res0), l) && l.contains(res0._1) && l.contains(res0._2))
}