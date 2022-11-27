import stainless.collection._
import stainless.lang._
import stainless.annotation._

/* Contains general geometric functionalities */
package point2d:

    /* Point class */
    class Point (val x: BigInt, val y: BigInt){

        /* Computes the square of distance between 2 points */
        def distance(that: Point): BigInt = (x - that.x)*(x - that.x) + (y - that.y)*(y - that.y)

    }

    type PairPoint = (Point, Point)
    
    /* Gives square of distance between the 2 points in the input pair */
    def pairDistance(x: PairPoint): BigInt = x._1.distance(x._2)


    /* Given 2 pairs of points, returns the pair with smaller distance*/
    def compare(p1: PairPoint, p2: PairPoint): PairPoint = 
        if (pairDistance(p1) < pairDistance(p2)) then p1 else p2

    
    /* Returns true if square of distance betwee p and every point in list l is at least delta */
    def deltaSparsePoint(delta: BigInt, p: Point, l: List[Point]): Boolean =
        if l.isEmpty then true else p.distance(l.head) >= delta && deltaSparsePoint(delta, p, l.tail)

    /* Returns true if square of distance between any two points in list is at least delta */
    def deltaSparse(delta: BigInt, l: List[Point]): Boolean =
        if l.isEmpty then true else deltaSparsePoint(delta, l.head, l.tail) && deltaSparse(delta, l.tail)
