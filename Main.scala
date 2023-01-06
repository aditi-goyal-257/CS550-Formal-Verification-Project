/* Implementation of function for finding closest pair of points */

import stainless.collection._
import stainless.lang._
import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.equations._
import stainless.lang.StaticChecks._

import point2d.*
import helper.*
import listLemmas.*
import sparsity.*
import sparsityLemmas.*
import bruteForce.*
import lemmas.*

object ClosestPoint {

   /* Finds the point closest to p in list l (sorted by y-coordinates) If there is no point which has distance less than d, then first point having difference in y-coordinate from p of atleast d is returned */

    def findClosestPointInStrip(p: Point)(d: BigInt)(l: List[Point]): Point =
    {
        require(!l.isEmpty && isSortedY(l) && p.y <= l.head.y)
        if l.tail.isEmpty then l.head
        else if d <= (l.head.y - p.y)*(l.head.y - p.y) then {
            ghost { transitiveDistanceProperty(p, d, l.head, l.tail) }
            l.head
        }
        else{
            val p1 = findClosestPointInStrip(p)(min(d, p.distance(l.head)))(l.tail)
            if p.distance(l.head) <= p.distance(p1) then l.head else p1
        }
    }
    .ensuring(res0 => deltaSparsePoint(min(p.distance(res0), d), p, l) && l.contains(res0))


    /* Finds the closest pair in strip. If the closest pair has distance atleast as distance between points in x, then x is returned*/

    def findClosestPairInStrip(x: PairPoint)(@induct l: List[Point]):PairPoint =
    {
        require(isSortedY(l))
        if l.isEmpty || l.tail.isEmpty then x
        else {
            val p1 = findClosestPointInStrip(l.head)(pairDistance(x))(l.tail)
            assert(deltaSparsePoint(min(p1.distance(l.head), pairDistance(x)), l.head, l.tail))
            if pairDistance(x) <= p1.distance(l.head) then{
                val z = findClosestPairInStrip(x)(l.tail)
                ghost { reducingDeltaPreservesPointSparsity(pairDistance(x), pairDistance(z), l.head, l.tail) }
                z
            }
            else {
                val z = findClosestPairInStrip((l.head, p1))(l.tail)
                ghost { reducingDeltaPreservesPointSparsity(l.head.distance(p1), pairDistance(z), l.head, l.tail) }
                z
            }
        }
    }
    .ensuring(res0 => deltaSparse(pairDistance(res0), l) && pairDistance(res0) <= pairDistance(x) && (res0 == x || (l.contains(res0._1) && l.contains(res0._2))))

    /* Combining answers from left and right halves separated by x-coordinate div */

    def combine(lpoint: PairPoint)(rpoint: PairPoint)(div: BigInt)(l: List[Point]): PairPoint = {
        require(isSortedY(l) && l.contains(lpoint._1) && l.contains(lpoint._2) && l.contains(rpoint._1) && l.contains(rpoint._2))
        val z = compare(lpoint, rpoint)
        val d = pairDistance(z)
        val l2 = l.filter(p => p.distance(Point(div, p.y)) < d)
        ghost { filterSorted(l, p => p.distance(Point(div, p.y)) < d) }
        findClosestPairInStrip(z)(l2)
    }.ensuring(res0 => deltaSparse(pairDistance(res0), l.filter(p => p.distance(Point(div, p.y)) < pairDistance(compare(lpoint, rpoint)))) && pairDistance(res0) <= pairDistance(compare(lpoint, rpoint)) && l.contains(res0._1) && l.contains(res0._2))
        
    /* Find closest pair of points in list l sorted by x-coordinates. Also returns l sorted by y-coordinates */

    def findClosestPairRec(l: List[Point]): (List[Point], PairPoint) = {
        require(l.size >= 2 && isSortedX(l))
        decreases(l.size)
        if l.size <= 3 then bruteForce(l)
        else{
            val (left_half, right_half) = l.splitAtIndex(l.size/2)
            ghost { split(l, l.size/2) }
            val (lsorted, lpoint) = findClosestPairRec(left_half)
            val (rsorted, rpoint) = findClosestPairRec(right_half)
            val sortedList = mergeY(lsorted, rsorted)
            val res = combine(lpoint)(rpoint)(right_half.head.x)(sortedList)
            ghost {
                combineLemma(sortedList, left_half, right_half, right_half.head.x, lpoint, rpoint, res)
                subsetPreservesDeltaSparsity(pairDistance(res), sortedList, l)
            }
            (sortedList, res)
        }
    }.ensuring(res0 => res0._1.content == l.content && isSortedY(res0._1) && deltaSparse(pairDistance(res0._2), l) && l.contains(res0._2._1) && l.contains(res0._2._2))

    /* Find closest pair of points in list l */

    def findClosestPair(l: List[Point]): PairPoint = {
        require(l.size >= 2)
        val p = findClosestPairRec(mergeSortX(l))._2
        ghost { subsetPreservesDeltaSparsity(pairDistance(p), mergeSortX(l), l) }
        p
    }.ensuring(res0 => deltaSparse(pairDistance(res0), l) && l.contains(res0._1) && l.contains(res0._2))
}