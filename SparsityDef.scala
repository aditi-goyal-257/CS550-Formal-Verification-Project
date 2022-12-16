import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.lang.StaticChecks._

import point2d.*

object sparsity:

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

    /* If a list is not delta point sparse wrt to a point p, give a point in the
    list which has a distance less than delta from p */
    def getCounterExampleDeltaSparsityPoint(delta: BigInt, p: Point, l: List[Point]): Point ={
        require(!deltaSparsePoint(delta, p, l))
        if p == l.head || delta <= l.head.distance(p) then getCounterExampleDeltaSparsityPoint(delta, p, l.tail)
        else l.head
    }.ensuring(res0 => res0.distance(p) < delta && l.contains(res0) && res0 != p)

    /* If a list is not delta sparse, return a pair of points from list  which
    are less than delta distance apart from each other */
    def getCounterExampleDeltaSparsity(delta: BigInt, l: List[Point]): PairPoint = {
        require(!deltaSparse(delta, l))
        if(deltaSparsePoint(delta, l.head, l.tail)) then getCounterExampleDeltaSparsity(delta, l.tail)
        else (l.head, getCounterExampleDeltaSparsityPoint(delta, l.head, l.tail))
    }.ensuring(res0 => pairDistance(res0) < delta && l.contains(res0._1) && l.contains(res0._2) && res0._1 != res0._2)