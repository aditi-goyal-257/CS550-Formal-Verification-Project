import stainless.collection._
import stainless.lang._
import stainless.annotation._

/* Contains general geometric functionalities */
object point2d:
    /* Point class */
    class Point (val x: BigInt, val y: BigInt){

        /* Computes the square of distance between 2 points */
        def distance(that: Point): BigInt = {
            (x - that.x)*(x - that.x) + (y - that.y)*(y - that.y)
        }

    }

    def distanceCommutavityLemma(p1: Point, p2: Point) = {        
    }.ensuring(_ => p1.distance(p2) == p2.distance(p1))

    type PairPoint = (Point, Point)
    
    /* Gives square of distance between the 2 points in the input pair */
    def pairDistance(x: PairPoint): BigInt = x._1.distance(x._2)


    /* Given 2 pairs of points, returns the pair with smaller distance*/
    def compare(p1: PairPoint, p2: PairPoint): PairPoint =  {
        if (pairDistance(p1) < pairDistance(p2)) then p1 else p2
    }

    
    /* Returns true if square of distance betwee p and every point in list l is at least delta */
    def deltaSparsePoint(delta: BigInt, p: Point, l: List[Point]): Boolean = {
        if l.isEmpty then true else (p == l.head || delta <= l.head.distance(p)) && deltaSparsePoint(delta, p, l.tail)
    }.ensuring(res0 => res0 == l.forall(p1 => p == p1 || delta <= p1.distance(p)))

    /* Returns true if square of distance between any two points in list is at least delta */
    def deltaSparse(delta: BigInt, l: List[Point]): Boolean = {
        if l.isEmpty then true else {
            deltaSparsePoint(delta, l.head, l.tail) && deltaSparse(delta, l.tail)
        }
    }

    def deltaSparsePointLemma(delta: BigInt, p0: Point, l: List[Point], p1: Point):Unit ={
        require(deltaSparsePoint(delta, p0, l) && l.contains(p1))
        if(l.head != p1){
            l.tail.contains(p1)
            deltaSparsePointLemma(delta, p0, l.tail, p1)
        }
    }.ensuring(p0 == p1 || delta <= p1.distance(p0))

    def deltaSparsityLemma(delta: BigInt, l: List[Point], p0: Point, p1: Point):Unit = {
        require(deltaSparse(delta, l) && l.contains(p0) && l.contains(p1) && p0 != p1)
        if (l.head == p0){
            assert(l.tail.contains(p1))
            deltaSparsePointLemma(delta, p0, l.tail, p1)
        } else if(l.head == p1){
            assert(l.tail.contains(p0))
            deltaSparsePointLemma(delta, p1, l.tail, p0)
            distanceCommutavityLemma(p0, p1)
        }
        else{
            deltaSparsityLemma(delta, l.tail, p0, p1)
        }
    }.ensuring(p0 == p1||delta <= p1.distance(p0))

    def getCounterExampleDeltaSparsityPoint(delta: BigInt, p: Point, l: List[Point]): Point ={
        require(!deltaSparsePoint(delta, p, l))
        if p == l.head || delta <= l.head.distance(p) then getCounterExampleDeltaSparsityPoint(delta, p, l.tail)
        else l.head
    }.ensuring(res0 => res0.distance(p) < delta && l.contains(res0) && res0 != p)

    

    def getCounterExampleDeltaSparsity(delta: BigInt, l: List[Point]): PairPoint = {
        require(!deltaSparse(delta, l))
        if(deltaSparsePoint(delta, l.head, l.tail)) then getCounterExampleDeltaSparsity(delta, l.tail)
        else (l.head, getCounterExampleDeltaSparsityPoint(delta, l.head, l.tail))
    }.ensuring(res0 => pairDistance(res0) < delta && l.contains(res0._1) && l.contains(res0._2) && res0._1 != res0._2)

    def reducingDeltaPreservesPointSparsity(delta1: BigInt, delta2: BigInt, p: Point, @induct l: List[Point]) = {
        require(deltaSparsePoint(delta1, p, l) && delta2 <= delta1)
    }.ensuring(deltaSparsePoint(delta2, p, l))

    def reducingDeltaPreservesSparsity(delta1: BigInt, delta2: BigInt, @induct l: List[Point]): Unit = {
        require(deltaSparse(delta1, l) && delta2 <= delta1)
        if(!l.isEmpty) then {
            reducingDeltaPreservesPointSparsity(delta1, delta2, l.head, l)
            reducingDeltaPreservesSparsity(delta1, delta2, l.tail)
        }
    }.ensuring(deltaSparse(delta2, l))


    def subsetPreservesDeltaSparsity(delta: BigInt, l1: List[Point], l2: List[Point]): Unit = {
        require(deltaSparse(delta, l1) && l2.content.subsetOf(l1.content))
        if(!deltaSparse(delta, l2)){
            val (p0, p1) = getCounterExampleDeltaSparsity(delta, l2)
            assert(l1.contains(p0))
            assert(l1.contains(p1))
            deltaSparsityLemma(delta, l1, p0, p1)
        }

    }.ensuring(deltaSparse(delta, l2))

    def isDistinct(l: List[Point]): Boolean ={
        if l.isEmpty then true else !l.tail.contains(l.head) && isDistinct(l.tail)
    }

    def elementInsideListLemma(l: List[Point], index: BigInt): Unit = {
        require(index > 0 && index < l.size)
        if(index != 1){
            elementInsideListLemma(l.tail, index-1)
        }
    }.ensuring(l.tail.contains(l(index)))

    def distinctLemma(l: List[Point], index1: BigInt, index2: BigInt): Unit = {
        require(index1 >= 0 && index1 < l.size && index2 >= 0  && index2 < l.size && index1 != index2 && isDistinct(l))
        if(!l.isEmpty){
            if(index1 == 0){
                assert(index2 > 0 && index2 < l.size)
                elementInsideListLemma(l, index2)
                assert(l.tail.contains(l(index2)))
                assert(!l.tail.contains(l(index1)))
                assert(l(index1)!=l(index2))
            }
            else if(index2 == 0){
                elementInsideListLemma(l, index1)
                assert(l.tail.contains(l(index1)))
                assert(!l.tail.contains(l(index2)))
                assert(l(index1)!=l(index2))
            }
            else{
                distinctLemma(l.tail, index1-1, index2-1)
            }
        }
    }.ensuring(l(index1) != l(index2))


    
    @extern
    def main(args: Array[String]): Unit = {
        val l = Cons[Point](Point(BigInt("-5"), BigInt("4")), Cons[Point](Point(BigInt("-5"), BigInt("5")), Nil[Point]()))
        val delta = BigInt("2")
        val a = deltaSparsePoint(delta, l.head, l)
        println(a)
        println(l.forall(p1 => (l.head == p1) || (delta <= (l.head).distance(p1))))
        assert(a == l.forall(p1 => (l.head == p1) || (delta <= (l.head).distance(p1))))
    }
