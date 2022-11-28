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
        if l.isEmpty then true else delta <= l.head.distance(p) && deltaSparsePoint(delta, p, l.tail)
    }.ensuring(res0 => res0 == l.forall(p1 => delta <= p1.distance(p)))

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
    }.ensuring(delta <= p1.distance(p0))

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
    }.ensuring(delta <= p1.distance(p0))

    @extern
    def main(args: Array[String]): Unit = {
        val l = Cons[Point](Point(BigInt("-5"), BigInt("4")), Cons[Point](Point(BigInt("-5"), BigInt("5")), Nil[Point]()))
        val delta = BigInt("2")
        val a = deltaSparsePoint(delta, l.head, l)
        println(a)
        println(l.forall(p1 => (l.head == p1) || (delta <= (l.head).distance(p1))))
        assert(a == l.forall(p1 => (l.head == p1) || (delta <= (l.head).distance(p1))))
    }
