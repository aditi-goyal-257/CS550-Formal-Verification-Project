import stainless.collection._
import stainless.lang._
import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.lang.StaticChecks._

import point2d.*
import helper.*
import sparsity.*

object listLemmas:

   /********************* Generic list lemmas *********************************/

   /* l(index) is contained in l.tail for any list given index
   is atleast 0 and less than size of the list*/
    @ghostAnnot
    def elementInsideListLemma[T](l: List[T], index: BigInt): Unit = {
        require(index > 0 && index < l.size)
        if(index != 1){
            elementInsideListLemma(l.tail, index-1)
        }
    }.ensuring(_ => l.tail.contains(l(index)))

    /* Properties for value returned by indexOf function
    for an element in list */
    @ghostAnnot
    def indexOfElementPresentLemma[T](l: List[T], p: T): Unit = {
        require(l.contains(p))
        if(l.head != p){
            indexOfElementPresentLemma(l.tail, p)
        }
    }.ensuring(_ => l.indexOf(p) < l.size && l(l.indexOf(p)) == p)

    @ghostAnnot
    def takeSameProperty[T](l: List[T], index: BigInt, index2: BigInt): Unit = {
        require(index >= 0 && index2 >= 0 &&index < l.size && index2 < index)
        if(index2 > 0){
            takeSameProperty(l.tail, index-1, index2 - 1)
        }
    }.ensuring(_ => l(index2) == l.take(index)(index2))

    @ghostAnnot
    def dropSameProperty[T](l: List[T], index: BigInt, index2: BigInt): Unit = {
        require(index2 >= 0 && index >= 0 && index2 + index < l.size && index + index2 >= 0)
        if(index > 0){
            dropSameProperty(l.tail, index-1, index2)
        }

    }.ensuring(_ => l(index2 + index) == l.drop(index)(index2))

    /***************************  Lemmas related to list containing distinct points **********************/

    /* Taking 2 different indices for a list with distinct points
    ensures that the points at those indices are not equal */
    @ghostAnnot
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
    }.ensuring(_ => l(index1) != l(index2))

    /* l.take from distinct list l ensures resulting list
    is also distinct */
    @ghostAnnot
    def takeDistinctLemma(l: List[Point], index: BigInt): Unit = {
        require(isDistinct(l))
        if(index >= 0 && !l.isEmpty){
            val z = l.tail.take(index-1)
            takeDistinctLemma(l.tail, index-1)
            assert(!z.contains(l.head))
        }
    }.ensuring(_ => isDistinct(l.take(index)))


    /* l.drop from distinct list l ensures resulting list
    is also distinct */
    @ghostAnnot
    def dropDistinctLemma(l: List[Point], index: BigInt) : Unit = {
        require(isDistinct(l))
        if(!l.isEmpty && index > 0){
            dropDistinctLemma(l.tail, index-1)
        }

    }.ensuring(_ => isDistinct(l.drop(index)))


   /* Splitting a distinct list ensures the 2 parts are
   distinct as well as don't have any point in common */
    @ghostAnnot
    def splitDistinctLemma(l: List[Point], index: BigInt): Unit = {
        require(isDistinct(l) && index >= 0)
        takeDistinctLemma(l, index)
        dropDistinctLemma(l, index)
        val a = l.splitAtIndex(index)
        val intersection = a._1.&(a._2)
        if(!intersection.isEmpty){
            val common_elem = intersection.head
            val index1 = a._1.indexOf(common_elem)
            // assert(a._1.contains(common_elem))
            val index2 = a._2.indexOf(common_elem)
            indexOfElementPresentLemma(a._1, common_elem)
            indexOfElementPresentLemma(a._2, common_elem)
            distinctLemma(l, index1, index2+a._1.size)
            dropSameProperty(l, index, index2)
            takeSameProperty(l, index, index1)
        }
    }.ensuring(_ => {
        val a = l.splitAtIndex(index)
        isDistinct(a._1) && isDistinct(a._2)&&
        (a._1.&(a._2)).isEmpty
    })


    /* MergeSort by X coordinates ensures a distinct list remains distinct */
    @ghostAnnot
    def mergeSortXDistinctLemma(l: List[Point]) : Unit = {
        require(isDistinct(l))
        if(!l.isEmpty && !l.tail.isEmpty){
            val(lhalf, rhalf) = l.splitAtIndex(l.size/2)
            splitDistinctLemma(l, l.size/2)
            mergeSortXDistinctLemma(lhalf)
            mergeSortXDistinctLemma(rhalf)
            val sorted_left = mergeSortX(lhalf)
            val sorted_right = mergeSortX(rhalf)
            mergeXDistinctLemma(sorted_left, sorted_right)
        }

    }.ensuring(_ => isDistinct(mergeSortX(l)))

    /* MergeSort by Y coordinates ensures a distinct list remains distinct */
    @ghostAnnot
    def mergeSortYDistinctLemma(l: List[Point]) : Unit = {
        require(isDistinct(l))
        if(!l.isEmpty && !l.tail.isEmpty){
            val(lhalf, rhalf) = l.splitAtIndex(l.size/2)
            splitDistinctLemma(l, l.size/2)
            mergeSortYDistinctLemma(lhalf)
            mergeSortYDistinctLemma(rhalf)
            val sorted_left = mergeSortY(lhalf)
            val sorted_right = mergeSortY(rhalf)
            mergeYDistinctLemma(sorted_left, sorted_right)
        }

    }.ensuring(_ => isDistinct(mergeSortY(l)))

    /* Provided 2 distinct sorted lists to mergeX, which don't
    have any common point ensures resulting list is also distinct */
    @ghostAnnot
    def mergeXDistinctLemma(l1: List[Point], l2: List[Point]): Unit = {
        require(isSortedX(l1) && isSortedX(l2) && isDistinct(l1) && isDistinct(l2) && l1.&(l2) == List[Point]())
        if(!l1.isEmpty && !l2.isEmpty){
            if(l1.head.x <= l2.head.x){
                assert(!(l1.tail ++ l2).contains(l1.head))
                mergeXDistinctLemma(l1.tail, l2)
            }
            else{
                assert(!(l1 ++ l2.tail).contains(l2.head))
                mergeXDistinctLemma(l1, l2.tail)
            }
        }
    }.ensuring(_ => isDistinct(mergeX(l1, l2)))

    /* Provided 2 distinct sorted lists to mergeY, which don't
    have any common point ensures resulting list is also distinct */
    @ghostAnnot
    def mergeYDistinctLemma(l1: List[Point], l2: List[Point]): Unit = {
        require(isSortedY(l1) && isSortedY(l2) && isDistinct(l1) && isDistinct(l2) && l1.&(l2) == List[Point]())
        if(!l1.isEmpty && !l2.isEmpty){
            if(l1.head.y <= l2.head.y){
                assert(!(l1.tail ++ l2).contains(l1.head))
                mergeYDistinctLemma(l1.tail, l2)
            }
            else{
                assert(!(l1 ++ l2.tail).contains(l2.head))
                mergeYDistinctLemma(l1, l2.tail)
            }
        }
    }.ensuring(_ => isDistinct(mergeY(l1, l2)))

    /*******************************  Lemmas related to filtering **************************/

    /* Given an element in list which satisfies certain predicate,
    applying filter on the list results a list which contains the
    element */
    @ghostAnnot
    def filteringLemma[T](l: List[T], predicate: T => Boolean, p: T): Unit = {
        require(l.contains(p) && predicate(p))
        if l.head != p then {
            l.tail.contains(p)
            filteringLemma(l.tail, predicate, p)
        }
    }.ensuring(_ => l.filter(predicate).contains(p))


    /* Given a distinct list, filtering based on any predicate
    ensures that resulting list is also distinct */
    @ghostAnnot
    def filteringPreservesDistinct(l: List[Point], predicate: Point => Boolean): Unit = {
        require(isDistinct(l))
        if(!l.isEmpty){
            if(predicate(l.head)){
                assert(!l.tail.contains(l.head))
                assert(!l.tail.filter(predicate).contains(l.head))
                filteringPreservesDistinct(l.tail, predicate)
            }
            else{
                filteringPreservesDistinct(l.tail, predicate)
            }
        }
    }.ensuring(_ => isDistinct(l.filter(predicate)))

    /* A delta sparse point list is still delta sparse point after filtering
    based on any predicate */
    @ghostAnnot
    def filteringPreservesDeltaPointSparsity(@induct l: List[Point], predicate: Point => Boolean, p: Point, delta: BigInt): Unit = {
        require(isSortedY(l) && deltaSparsePoint(delta, p, l))
    }.ensuring(_ => deltaSparsePoint(delta, p, l.filter(predicate)))

    /* A delta sparse  list is still delta sparse after filtering based on
    any predicate */
    @ghostAnnot
    def filteringPreservesDeltaSparsity(l: List[Point], predicate: Point => Boolean, delta: BigInt): Unit = {
        require(isSortedY(l) && deltaSparse(delta, l))
        if(!l.isEmpty){
            if(!predicate(l.head)){
                filteringPreservesDeltaSparsity(l.tail, predicate, delta)
            }
            else{
                filteringPreservesDeltaPointSparsity(l.tail, predicate, l.head, delta)
                filteringPreservesDeltaSparsity(l.tail, predicate, delta)
            }
        }
    }.ensuring(_ => deltaSparse(delta, l.filter(predicate)))

    @ghostAnnot
    def filteringTwiceEquivalentLemma(@induct ps: List[Point], l: BigInt, d1: BigInt, d2: BigInt): Unit = {
        require(isSortedY(ps) && d1 <= d2)
    }.ensuring(_ => ps.filter(p => p.distance(Point(l, p.y)) < d1 ) == ps.filter(p => p.distance(Point(l, p.y)) < d2).filter(p => p.distance(Point(l, p.y)) < d1))


   /********************** Lemma related to sorted lists **************/


    /* Provided a list sorted by X coordinates and 2 indices,
    the largest index point corresponds to larger X-coordinate */
    @ghostAnnot
    def indexPreservesSorting(l: List[Point], a: BigInt, b: BigInt): Unit = {
        require(isSortedX(l) && a<=b)
        if(a >= 0 && b < l.size){
            if(a == 0){
                assert(l.forall(p => l.head.x <= p.x))
                listContainsElement(l, b)
                assert(l.contains(l(b)))
                instantiateForAll(l,p => l.head.x <= p.x ,l(b))
            }
            else{
                indexPreservesSorting(l.tail, a-1, b-1)
            }
        }
    }.ensuring(_ => a < 0 || b >= l.size || l(a).x <= l(b).x)


    /******************* Generic lemmas for list of points ******************/
    @ghostAnnot
    def transitiveDistanceProperty(p: Point, d: BigInt, firstp: Point, @induct l: List[Point]): Unit = {
        require(isSortedY(l) && l.forall(p1 => firstp.y <= p1.y) && p.y <= firstp.y && d <= (firstp.y - p.y)*(firstp.y - p.y))
    }.ensuring(_ => deltaSparsePoint(min(p.distance(firstp), d), p, firstp::l))