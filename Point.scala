import stainless.collection._
import stainless.lang._
import stainless.annotation._

package point2d:

    class Point (val x: BigInt, val y: BigInt){
        def distance(that: Point): BigInt = (x - that.x)*(x - that.x) + (y - that.y)*(y - that.y)
    }

    type PairPoint = (Point, Point)

    def pairDistance(x: PairPoint): BigInt = x._1.distance(x._2)

    def compare(p1: PairPoint, p2: PairPoint): PairPoint = 
        if (pairDistance(p1) < pairDistance(p2)) then p1 else p2

    def deltaSparsePoint(delta: BigInt, p: Point, l: List[Point]): Boolean =
        if l.isEmpty then true else p.distance(l.head) >= delta && deltaSparsePoint(delta, p, l.tail)

    def deltaSparse(delta: BigInt, l: List[Point]): Boolean =
        if l.isEmpty then true else deltaSparsePoint(delta, l.head, l.tail) && deltaSparse(delta, l.tail)
