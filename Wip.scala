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


    /* Main theorems and lemmas */

    def findClosestPairinStripLemma(l : List[Point], res: PairPoint, x: PairPoint) = {
        require(isSortedY(l) && res == findClosestPairInStrip(x)(l))
    }.ensuring(deltaSparse(pairDistance(res), l))


    def coordinateBoundLemma(p0: Point, l: BigInt, d: BigInt, @induct pr: List[Point]) = {
        require(p0.x <= l && d <= (p0.x - l)*(p0.x - l) && pr.forall(p => l <= p.x))
    }.ensuring(pr.forall(p =>  d <= p0.distance(p)))


    def divideAndConquerLemma(l1: List[Point], p0: Point, p1: Point, d: BigInt, l: BigInt, pl: List[Point], pr: List[Point], l2: List[Point]): Unit ={
        require(l1.contains(p0) && l1.contains(p1) && p0!=p1 && p0.distance(p1) < d && pl.forall(p => p.x <= l) && pr.forall(p => l <= p.x) && deltaSparse(d, pl) && deltaSparse(d, pr) && l1.content == pl.content ++ pr.content && l2 == l1.filter(p => p.distance(Point(l, p.y)) < d))
        
        if(pl.contains(p0)){
            if(pl.contains(p1)){
                deltaSparsityLemma(d, pl, p1, p0)
            }
            // assert(pr.contains(p1))
            if(d <= p0.distance(Point(l, p0.y))){
                // assert(d <= (p0.x -l)*(p0.x - l))
                // assert(d <= (p0.x -l)*(p0.x -l) + (p0.y - p1.y)*(p0.y - p1.y))
                instantiateForAll(pl, p => p.x <= l, p0)
                instantiateForAll(pr, p => l <= p.x, p1)
                // assert(d <= (p0.x -p1.x)*(p0.x -p1.x) + (p0.y - p1.y)*(p0.y - p1.y))
                // assert(d <= p0.distance(p1))
            }
            filteringLemma(l1, p => p.distance(Point(l, p.y)) < d, p0)
            // assert(l2.contains(p0))

            if(d <= p1.distance(Point(l, p1.y))){
                // assert(d <= (p1.x -l)*(p1.x - l))
                // assert(d <= (p1.x -l)*(p1.x -l) + (p1.y - p0.y)*(p1.y - p0.y))
                instantiateForAll(pl, p => p.x <= l, p0)
                instantiateForAll(pr, p => l <= p.x, p1)
                // assert(d <= (p0.x -p1.x)*(p0.x -p1.x) + (p0.y - p1.y)*(p0.y - p1.y))
                // assert(d <= p0.distance(p1))
            }
            filteringLemma(l1, p => p.distance(Point(l, p.y)) < d, p1)
            // assert(l2.contains(p1))
        }
        else{
            // assert(pr.contains(p0))
            if(pr.contains(p1)){
                deltaSparsityLemma(d, pr, p1, p0)
            }
            // assert(pl.contains(p1))
            if(d <= p0.distance(Point(l, p0.y))){
                // assert(d <= (p0.x -l)*(p0.x - l))
                // assert(d <= (p0.x -l)*(p0.x -l) + (p0.y - p1.y)*(p0.y - p1.y))
                instantiateForAll(pl, p => p.x <= l, p1)
                instantiateForAll(pr, p => l <= p.x, p0)
                // assert(d <= (p0.x -p1.x)*(p0.x -p1.x) + (p0.y - p1.y)*(p0.y - p1.y))
                // assert(d <= p0.distance(p1))
            }
            filteringLemma(l1, p => p.distance(Point(l, p.y)) < d, p0)
            // assert(l2.contains(p0))

            if(d <= p1.distance(Point(l, p1.y))){
                // assert(d <= (p1.x -l)*(p1.x - l))
                // assert(d <= (p1.x -l)*(p1.x -l) + (p1.y - p0.y)*(p1.y - p0.y))
                instantiateForAll(pl, p => p.x <= l, p1)
                instantiateForAll(pr, p => l <= p.x, p0)
                // assert(d <= (p0.x -p1.x)*(p0.x -p1.x) + (p0.y - p1.y)*(p0.y - p1.y))
                // assert(d <= p0.distance(p1))
            }
            filteringLemma(l1, p => p.distance(Point(l, p.y)) < d, p1)
            // assert(l2.contains(p1))
            
        }

        //true
    }.ensuring(_ => l2.contains(p0) && l2.contains(p1))

    def combineLemma(ps: List[Point], pl: List[Point], pr: List[Point], l: BigInt, left_pair: PairPoint, right_pair: PairPoint, p: PairPoint) = {
        require(isSortedY(ps) && ps.content == pl.content ++ pr.content && pl.forall(p => p.x <= l) && deltaSparse(pairDistance(left_pair), pl) && pr.forall(p => l <= p.x) && deltaSparse(pairDistance(right_pair), pr) && p == combine(left_pair)(right_pair)(l)(ps))

        val d = pairDistance(p)
        if(!deltaSparse(d, ps)){
            val (p0, p1) = getCounterExampleDeltaSparsity(d, ps)
            
            // assert(ps.contains(p0))
            // assert(ps.contains(p1))
            // assert(p0 != p1)
            // assert(p0.distance(p1) < d)
            // assert(pl.forall(p => p.x <= l))
            // assert(pr.forall(p => l <= p.x))
            // assert(d <= pairDistance(left_pair))
            reducingDeltaPreservesSparsity(pairDistance(left_pair), d, pl)
            // assert(deltaSparse(d, pl))
            reducingDeltaPreservesSparsity(pairDistance(right_pair), d, pr)
            //assert(pairDistance(p) <= )

            val combine_filtered = filterSorted(ps)(p => p.distance(Point(l, p.y)) < pairDistance(compare(left_pair, right_pair)))

            val filtered = filterSorted(ps)(p => p.distance(Point(l, p.y)) < d)

            divideAndConquerLemma(ps, p0, p1, d, l, pl, pr, filtered)
            // assert(filtered.contains(p0))
            // assert(filtered.contains(p1))
            // assert(d <= pairDistance(compare(left_pair, right_pair)))
            // assert(deltaSparse(d, combine_filtered))
            filteringTwiceEquivalentLemma(ps, l, d, pairDistance(compare(left_pair, right_pair)))
            // assert(filtered == filterSorted(combine_filtered)(p => p.distance(Point(l, p.y)) < d))
            // assert(deltaSparse(d, combine_filtered))
            filteringPreservesDeltaSparsity(combine_filtered, p => p.distance(Point(l, p.y)) < d, d)
            // assert(deltaSparse(d, filtered))
            deltaSparsityLemma(d, filtered, p0, p1)

            //get contradiction using divide and conquer lemma
        }

    }.ensuring(deltaSparse(pairDistance(p), ps))
    

    def theorem1(xs: List[Point], ys: List[Point], p: PairPoint) = {
        require(1 < xs.length && isSortedX(xs) && (ys, p) == findClosestPairRec(xs))
    }.ensuring(deltaSparse(pairDistance(p), xs))

    def corollary1(xs: List[Point], p: PairPoint) = {
        require(1 < xs.length && p == findClosestPair(xs))
    }.ensuring(deltaSparse(pairDistance(p), xs))

    def theorem2(xs: List[Point], p0: Point, p1: Point) = {
        require(1 < xs.length && (p0, p1) == findClosestPair(xs))
    }.ensuring(xs.contains(p0) && xs.contains(p1))

    def theorem3(xs: List[Point], p0: Point, p1: Point) = {
        require(1 < xs.length && isDistinct(xs) && (p0, p1) == findClosestPair(xs))
        mergeSortXDistinctLemma(xs)
        val l = mergeSortX(xs)
        val res = findClosestPairRec(l)
        findClosestPairRecDistinctLemma(l, res._1, res._2)
    }.ensuring(p0!=p1)


    def closestPointDistinctLemma(p: Point, d: BigInt, l: List[Point], res: Point) ={
        require(!l.isEmpty && isSortedY(l) && p.y <= l.head.y && findClosestPointInStrip(p)(d)(l) == res && !l.contains(p))
    }.ensuring(res != p)

    def closestPairDistinctLemma(x: PairPoint, l: List[Point], res: PairPoint): Unit = {
        require(isDistinct(l) && isSortedY(l) && findClosestPairInStrip(x)(l) == res && x._1 != x._2)
        if(!l.isEmpty && !l.tail.isEmpty){
            // assert(!l.tail.contains(l.head))
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

    }.ensuring(res._1 != res._2)

    def combineDistinctLemma(lpoint: PairPoint, rpoint: PairPoint, div: BigInt, l: List[Point], res: PairPoint): Unit = {
        require(lpoint._1 != lpoint._2 && rpoint._1 != rpoint._2 && isDistinct(l) && isSortedY(l) && res == combine(lpoint)(rpoint)(div)(l))
        
        val z = compare(lpoint, rpoint)
        val d = pairDistance(z)
        val l2 = filterSorted(l)(p => p.distance(Point(div, p.y)) < d)
        filteringPreservesDistinct(l, p => p.distance(Point(div, p.y)) < d)
        // assert(isDistinct(l2))
        closestPairDistinctLemma(z, l2, res)
    }.ensuring(res._1 != res._2)

    


    def findClosestPairRecDistinctLemma(l: List[Point], sorted_y: List[Point], p: PairPoint): Unit = {
        require(l.size >= 2 && isSortedX(l) && isDistinct(l) && (sorted_y, p) == findClosestPairRec(l))
        decreases(l.size)
        if(l.size > 3){
            val (left_half, right_half) = split(l, l.size/2)
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
        
    }.ensuring(isDistinct(sorted_y) && p._1 != p._2)

 
    // @extern
    // def main(args: Array[String]): Unit = {
    //     println("hello")
    // }

}