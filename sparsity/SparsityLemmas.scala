import stainless.collection._
import stainless.lang._
import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.lang.StaticChecks._

import point2d.*
import sparsity.*

object sparsityLemmas:

    /* Taking a point from a delta point sparse list wrt p0 ensures distance
    between the point and p0 is atleast delta */
    @ghostAnnot
    def deltaSparsePointLemma(delta: BigInt, p0: Point, l: List[Point], p1: Point):Unit ={
        require(deltaSparsePoint(delta, p0, l) && l.contains(p1))
        if(l.head != p1){
            l.tail.contains(p1)
            deltaSparsePointLemma(delta, p0, l.tail, p1)
        }
    }.ensuring(_ => p0 == p1 || delta <= p1.distance(p0))

    /* Having 2 distinct points from a delta sparse list ensures that the
    distance between those 2 points is atleast delta */
    @ghostAnnot
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
    }.ensuring(_ => p0 == p1||delta <= p1.distance(p0))

    /* Reducing delta in the delta point sparsity still preserves the
    sparsity property */
    @ghostAnnot
    def reducingDeltaPreservesPointSparsity(delta1: BigInt, delta2: BigInt, p: Point, @induct l: List[Point]) = {
        require(deltaSparsePoint(delta1, p, l) && delta2 <= delta1)
    }.ensuring(_ => deltaSparsePoint(delta2, p, l))

    /* Reducing delta in the delta sparsity for a list still preserves
    the sparsity property */
    @ghostAnnot
    def reducingDeltaPreservesSparsity(delta1: BigInt, delta2: BigInt, @induct l: List[Point]): Unit = {
        require(deltaSparse(delta1, l) && delta2 <= delta1)
        if(!l.isEmpty) then {
            reducingDeltaPreservesPointSparsity(delta1, delta2, l.head, l)
            reducingDeltaPreservesSparsity(delta1, delta2, l.tail)
        }
    }.ensuring(_ => deltaSparse(delta2, l))

    /* Taking subset of a delta sparse list still preserves
    the sparsity property */
    @ghostAnnot
    def subsetPreservesDeltaSparsity(delta: BigInt, l1: List[Point], l2: List[Point]): Unit = {
        require(deltaSparse(delta, l1) && l2.content.subsetOf(l1.content))
        if(!deltaSparse(delta, l2)){
            val (p0, p1) = getCounterExampleDeltaSparsity(delta, l2)
            assert(l1.contains(p0))
            assert(l1.contains(p1))
            deltaSparsityLemma(delta, l1, p0, p1)
        }

    }.ensuring(_ => deltaSparse(delta, l2))