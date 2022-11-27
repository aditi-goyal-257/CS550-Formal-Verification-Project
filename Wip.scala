import stainless.collection._
import stainless.lang._
import stainless.annotation._

import point2d.*
import helper.*
 
object ClosestPoint {


    def findClosestPairInStrip(x: PairPoint)(l: List[Point]):PairPoint =
    {
        require(isSortedY(l))
        if l.isEmpty || l.tail.isEmpty then x
        else {
            val p1 = findClosestPointInStrip(l.head)(pairDistance(x))(l.tail)
            if pairDistance(x) <= p1.distance(l.head) then
                findClosestPairInStrip(x)(l.tail)
            else findClosestPairInStrip((l.head, p1))(l.tail)
        }
    }
    //.ensuring(res0 => deltaSparse(min(pairDistance(x), pairDistance(res0)), l))
    
    // l (strip) is sorted by y coordinates
    def findClosestPointInStrip(p: Point)(d: BigInt)(l: List[Point]): Point =
    {
        require(!l.isEmpty)
        if (p.y - l.head.y)*(p.y - l.head.y) >= d then l.head
        else{
            if l.tail.isEmpty then l.head
            else{
                val p1 = findClosestPointInStrip(p)(min(d, p.distance(l.head)))(l.tail)
                if p.distance(l.head) <= p.distance(p1) then l.head else p1
            }
        }
    }
    //.ensuring(res0 => deltaSparsePoint(p.distance(res0), p, l))

    

    // l (complete list) is sorted by y coordinates 
    def combine(lpoint: PairPoint)(rpoint: PairPoint)(div: BigInt)(l: List[Point]): PairPoint =
        require(isSortedY(l))
        val z = compare(lpoint, rpoint)
        findClosestPairInStrip(z)(filterSorted(l)(p => (p.x - div)*(p.x - div) < pairDistance(z)))
        

    def bruteForce(l: List[Point]): (List[Point], PairPoint) =  
    {
        require(l.size <= 3 && l.size >= 2) 
        val z = mergeSortY(l)
        if l.size == 2 then (z, (l(0), l(1)))
        else (z, compare(compare((l(0), l(1)), (l(0), l(2))), (l(1), l(2)))) 
    }.ensuring(res0 => isSortedY(res0._1))

    // l (complete list) is sorted by x coordinates, return sorted by y coordinates
    def findClosestPairRec(l: List[Point]): (List[Point], PairPoint) ={
        require(l.size >= 2 && isSortedX(l))
        decreases(l.size)
        if l.size <= 3 then bruteForce(l)
        else{
            val (left_half, right_half) = split(l, l.size/2)
            assert(isSortedX(left_half))
            assert(isSortedX(right_half))
            val (lsorted, lpoint) = findClosestPairRec(left_half)
            val (rsorted, rpoint) = findClosestPairRec(right_half)
            val sortedList = mergeY(lsorted, rsorted)
            (sortedList, combine(lpoint)(rpoint)(right_half.head.x)(sortedList))
        }
    }.ensuring(res0 => isSortedY(res0._1))

    def findClosestPair(l: List[Point]) =
        require(l.size >= 2)
        findClosestPairRec(mergeSortX(l))._1


    @extern
    def main(args: Array[String]): Unit = {
        //println(inc(1))
    }

}