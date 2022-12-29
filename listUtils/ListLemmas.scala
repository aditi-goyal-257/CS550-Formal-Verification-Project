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

    /* Provided 2 distinct sorted lists to mergeXAcc, which don't
    have any common point ensures resulting list is also distinct */
    @ghostAnnot
    def mergeXAccDistinctLemma(l1: List[Point], l2: List[Point] , acc: List[Point]): Unit = {
        require(isSortedX(l1) && isSortedX(l2) && isReverseSortedX(acc) && (l1.isEmpty || {val a = l1.head.x; acc.forall(p => p.x <= a)}) && (l2.isEmpty || {val a = l2.head.x; acc.forall(p => p.x <= a)}) && isDistinct(l1) && isDistinct(l2) && isDistinct(acc) && l1.&(l2) == List[Point]() && l1.&(acc)== List[Point]() && l2.&(acc) == List[Point]())
        
        if(l1.isEmpty && l2.isEmpty) then assert(isDistinct(acc))
        else if (l1.isEmpty) then {
            mergeXLemma(l2.head, acc)
            if(!l2.tail.isEmpty){
                val a = l2.tail.head
                instantiateForAll(l2.tail, p => l2.head.x <= p.x, a)
                tranisitiveSortedListIncreasingLemmaX(acc, l2.tail.head.x, l2.head.x)
            }
            mergeXAccDistinctLemma(l1 , l2.tail , l2.head :: acc)
        }
        else if (l2.isEmpty) then {
            mergeXLemma(l1.head, acc)
            if(!l1.tail.isEmpty){
                instantiateForAll(l1.tail, p => l1.head.x <= p.x, l1.tail.head)
                tranisitiveSortedListIncreasingLemmaX(acc, l1.tail.head.x, l1.head.x)
            }
            mergeXAccDistinctLemma( l1.tail, l2,  l1.head :: acc)
        }
        else if l1.head.x <= l2.head.x then {
            mergeXLemma(l1.head, acc)
            if(!l1.tail.isEmpty){
                instantiateForAll(l1.tail, p => l1.head.x <= p.x, l1.tail.head)
                tranisitiveSortedListIncreasingLemmaX(acc, l1.tail.head.x, l1.head.x)
            }
            mergeXAccDistinctLemma(l1.tail , l2 , l1.head :: acc)
        }
        else{
            mergeXLemma(l2.head, acc)
            if(!l2.tail.isEmpty){
                instantiateForAll(l2.tail, p => l2.head.x <= p.x, l2.tail.head)
                tranisitiveSortedListIncreasingLemmaX(acc, l2.tail.head.x, l2.head.x)
            }
            mergeXAccDistinctLemma(l1 , l2.tail , l2.head:: acc)
        }
        
    }.ensuring(_ => isDistinct(mergeXAcc(l1, l2, acc))) 
    
    /* Provided 2 distinct sorted lists to mergeX, which don't
    have any common point ensures resulting list is also distinct */
    @ghostAnnot
    def mergeXDistinctLemma(l1: List[Point], l2: List[Point]): Unit = {
        require(isSortedX(l1) && isSortedX(l2) && isDistinct(l1) && isDistinct(l2) && l1.&(l2) == List[Point]())
        mergeXAccDistinctLemma(l1, l2, List[Point]())
        reversePreservesDistinct(mergeXAcc(l1, l2, List[Point]()))
    }.ensuring(_ => isDistinct(mergeX(l1, l2)))

    @ghostAnnot
    def lastIndexProperty(@induct l: List[Point]): Unit= {
    }.ensuring(_ => l.isEmpty || l(l.size -1) == l.last)
    
    /* Given a non-empty distinct list, it's init is also distinct */
    @ghostAnnot
    def initIsDistinct(@induct l: List[Point]): Unit = {
        require(isDistinct(l))
    }.ensuring(_ => l.isEmpty || isDistinct(l.init))

    /* Given a distinct list, reversing it also produces a distinct list */
    @ghostAnnot
    def reversePreservesDistinct(l: List[Point]): Unit = {
        require(isDistinct(l))
        if(!l.isEmpty){
            if(!l.tail.isEmpty){
                reversePreservesDistinct(l.tail)
                distinctLemma(l, 0, l.size - 1)
                assert(l(0) == l.head)
                lastIndexProperty(l)
                assert(l(l.size -1) == l.last)
                assert(l.head != l.last)
                initIsDistinct(l)
                assert(isDistinct(l.init))
                reversePreservesDistinct(l.init)
                reverseProperty(l)
            }
        }
        assert(isDistinct(l.reverse))
        assert(l.isEmpty || !l.init.contains(l.last))

    }.ensuring(_ => isDistinct(l.reverse) && (l.isEmpty || !l.init.contains(l.last)))
    
    /* Provided 2 distinct sorted lists to mergeYAcc, which don't
    have any common point ensures resulting list is also distinct */
    @ghostAnnot
    def mergeYAccDistinctLemma(l1: List[Point], l2: List[Point], acc: List[Point]): Unit = {
        require(isSortedY(l1) && isSortedY(l2) && isReverseSortedY(acc) && (l1.isEmpty || {val a = l1.head.y; acc.forall(p => p.y <= a)}) && (l2.isEmpty || {val a = l2.head.y; acc.forall(p => p.y <= a)}) && isDistinct(l1) && isDistinct(l2) && isDistinct(acc) && l1.&(l2) == List[Point]() && l1.&(acc) == List[Point]() && l2.&(acc) == List[Point]())
        
        if(l1.isEmpty && l2.isEmpty) then assert(isDistinct(acc))
        else if (l1.isEmpty) then {
            mergeYLemma(l2.head, acc)
            if(!l2.tail.isEmpty){
                val a = l2.tail.head
                instantiateForAll(l2.tail, p => l2.head.y <= p.y, a)
                tranisitiveSortedListIncreasingLemmaY(acc, l2.tail.head.y, l2.head.y)
            }
            mergeYAccDistinctLemma(l1 , l2.tail , l2.head :: acc)
        }
        else if (l2.isEmpty) then {
            mergeYLemma(l1.head, acc)
            if(!l1.tail.isEmpty){
                instantiateForAll(l1.tail, p => l1.head.y <= p.y, l1.tail.head)
                tranisitiveSortedListIncreasingLemmaY(acc, l1.tail.head.y, l1.head.y)
            }
            mergeYAccDistinctLemma( l1.tail, l2,  l1.head :: acc)
        }
        else if l1.head.y <= l2.head.y then {
            mergeYLemma(l1.head, acc)
            if(!l1.tail.isEmpty){
                instantiateForAll(l1.tail, p => l1.head.y <= p.y, l1.tail.head)
                tranisitiveSortedListIncreasingLemmaY(acc, l1.tail.head.y, l1.head.y)
            }
            mergeYAccDistinctLemma(l1.tail , l2 , l1.head :: acc)
        }
        else{
            mergeYLemma(l2.head, acc)
            if(!l2.tail.isEmpty){
                instantiateForAll(l2.tail, p => l2.head.y <= p.y, l2.tail.head)
                tranisitiveSortedListIncreasingLemmaY(acc, l2.tail.head.y, l2.head.y)
            }
            mergeYAccDistinctLemma(l1 , l2.tail , l2.head:: acc)
        }

    }.ensuring(_ => isDistinct(mergeYAcc(l1, l2, acc)))
    
    /* Provided 2 distinct sorted lists to mergeY, which don't
    have any common point ensures resulting list is also distinct */
    @ghostAnnot
    def mergeYDistinctLemma(l1: List[Point], l2: List[Point]): Unit = {
        require(isSortedY(l1) && isSortedY(l2) && isDistinct(l1) && isDistinct(l2) && l1.&(l2) == List[Point]())
        mergeYAccDistinctLemma(l1, l2, List[Point]())
        reversePreservesDistinct(mergeYAcc(l1, l2, List[Point]()))
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