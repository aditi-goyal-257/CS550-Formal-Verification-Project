/* This file contains generic functionality related to sorting and
other utility functions like splitting list*/

import stainless.collection._
import stainless.lang._
import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.equations._
import point2d._
import sparsity._
import sparsityLemmas._
import stainless.lang.StaticChecks._

package helper:

    /* Returns the minimum of two BigInt */
    def min(x: BigInt, y: BigInt) = if (x < y) then x else y


    /* Returns true if all the points in the list are distinct, otherwise false */
    def isDistinct(l: List[Point]): Boolean ={
        if l.isEmpty then true else !l.tail.contains(l.head) && isDistinct(l.tail)
    }

    /* l(index) is in l where index respects the bounds*/
    def listContainsElement[T](l: List[T], a: BigInt): Unit= {
        require(a >= 0 && a < l.size)
        if(a != 0){
            listContainsElement(l.tail, a-1)
        }
    }.ensuring(_ => l.contains(l(a)))


    /* Lemma to prove that if some predicate is true for every element
       of a list, it is also true for any individual element */
    @ghostAnnot
    def instantiateForAll[T](l: List[T], predicate: T => Boolean, p: T): Unit ={
        require(l.forall(predicate) && l.contains(p))
        assert(!l.isEmpty)
        if(l.tail.isEmpty) then
            assert(l.head == p)
        else if(l.head  == p) then
            assert(predicate(l.head))
        else
            assert(l.tail.contains(p))
            instantiateForAll(l.tail, predicate, p)

    }.ensuring(_ => predicate(p))

    /* Lemma to prove if a predicate is valid for two lists it is also true for a list which is made up of the other two lists */
    @ghostAnnot
    def wholeImpliesSubsetLemma[T](l1: List[T], l2: List[T], l3: List[T], predicate: T => Boolean): Unit = {
        require(l1.forall(predicate) && l2.forall(predicate) && l3.content.subsetOf(l1.content ++ l2.content))
        if !l3.isEmpty then {
            if l1.content.contains(l3.head) then {
                assert(l1.contains(l3.head))
                instantiateForAll(l1, predicate, l3.head)
                assert(predicate(l3.head))
                wholeImpliesSubsetLemma(l1, l2, l3.tail, predicate)}
            else {
                assert(l2.content.contains(l3.head))
                instantiateForAll(l2, predicate, l3.head)
                assert(predicate(l3.head))
                wholeImpliesSubsetLemma(l1, l2, l3.tail, predicate)
            }
        }
    }.ensuring(_=> l3.forall(predicate))

    /**************************************** Functions related to X-coordinates of points ************************************************/

    /* Check if list is sorted by X coordinates */
    def isSortedX(l: List[Point]): Boolean = {
        if l.isEmpty then true
        else l.forall(p => l.head.x <= p.x) && isSortedX(l.tail)
    }

    def isReverseSortedX(l: List[Point]): Boolean = {
        if l.isEmpty then true
        else l.forall(p => p.x <= l.head.x) && isReverseSortedX(l.tail)
    }

     /* Lemma to imply transitivity of <= operation on elements of a list (x-coordinates) */
    @ghostAnnot
    def tranisitiveSortedListLemmaX(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(a <= b && l.forall(p => b <= p.x))
    }.ensuring(_ => l.forall(p => a <= p.x))

    @ghostAnnot
    def tranisitiveSortedListIncreasingLemmaX(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(b <= a && l.forall(p => p.x <= b))
    }.ensuring(_ => l.forall(p => p.x <= a))

    @ghostAnnot
    def mergeXLemma(p0: Point, l: List[Point]): Unit = {
        require(isReverseSortedX(l)  && l.forall(p => p.x <= p0.x))
    }.ensuring(_ => isReverseSortedX(p0 :: l))

    @ghostAnnot
    def headSmallerX(@induct l: List[Point]): Unit = {
        require(isReverseSortedX(l))
    }.ensuring(_ => l.isEmpty || l.last.x <= l.head.x)

    @ghostAnnot
    def initIsReverseSortedX(@induct l: List[Point]): Unit = {
        require(isReverseSortedX(l))
        if(!l.isEmpty){
            if(!l.tail.isEmpty){
                initIsReverseSortedX(l.tail)
                assert(isReverseSortedX(l.tail.init))
                assert(l.tail.init == l.init.tail)
                assert(l.tail.forall(p => p.x <= l.head.x))
                wholeImpliesSubsetLemma(l.tail, List[Point](), l.init.tail, p => p.x <= l.head.x)
                assert({val a = l.tail.last.x
                    l.tail.init.forall(p => a <= p.x)})
                // assert(l.tail.last == l.last)
                tranisitiveSortedListLemmaX(l.tail.init, l.last.x, l.tail.last.x)
                assert({val a = l.last.x;
                    l.tail.init.forall(p => a <= p.x)})
                headSmallerX(l)
            }
        }
    }.ensuring(_ => l.isEmpty || (isReverseSortedX(l.init) && {val a = l.last.x; 
        l.init.forall(p => a <= p.x)}))

    @ghostAnnot
    def reverseSortingLemmaX(l: List[Point]): Unit = {
        require(isReverseSortedX(l))
        if(!l.isEmpty) then {
            val z = l.init
            initIsReverseSortedX(l)
            assert(isReverseSortedX(z))
            reverseSortingLemmaX(z)
            assert({val a = l.last.x; l.init.forall(p => a <= p.x)})
            wholeImpliesSubsetLemma(l.init, List[Point](), l.init.reverse, {val a = l.last.x; p => a <= p.x})
            assert({val a = l.last.x; val b = l.init.reverse; b.forall(p => a <= p.x)})
            assert(isSortedX(l.init.reverse))
            reverseProperty(l)
            // assert(l.init.reverse.forall())
        }
    }.ensuring(_ => isSortedX(l.reverse))

    /* Merge sort function to sort a list of points according to their x-coordinates */
    def mergeSortX(l: List[Point]): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAtIndex(l.size/2)
            mergeX(mergeSortX(lhalf), mergeSortX(rhalf))
        }
    }.ensuring(res0 => l.size == res0.size && isSortedX(res0) && l.content == res0.content)

    def mergeXAcc(l1: List[Point], l2: List[Point] , acc: List[Point]): List[Point] = {
        require(isSortedX(l1) && isSortedX(l2) && isReverseSortedX(acc) && (l1.isEmpty || {val a = l1.head.x; acc.forall(p => p.x <= a)}) && (l2.isEmpty || {val a = l2.head.x; acc.forall(p => p.x <= a)}))
        
        if(l1.isEmpty && l2.isEmpty) then acc
        else if (l1.isEmpty) then {
            ghost { mergeXLemma(l2.head, acc) }
            if(!l2.tail.isEmpty){
                val a = l2.tail.head
                ghost { instantiateForAll(l2.tail, p => l2.head.x <= p.x, a) }
                ghost { tranisitiveSortedListIncreasingLemmaX(acc, l2.tail.head.x, l2.head.x) }
            }
            mergeXAcc(l1 , l2.tail , l2.head :: acc)
        }
        else if (l2.isEmpty) then {
            ghost { mergeXLemma(l1.head, acc) }
            if(!l1.tail.isEmpty){
                ghost { instantiateForAll(l1.tail, p => l1.head.x <= p.x, l1.tail.head) }
                ghost { tranisitiveSortedListIncreasingLemmaX(acc, l1.tail.head.x, l1.head.x) }
            }
            mergeXAcc( l1.tail, l2,  l1.head :: acc)
        }
        else if l1.head.x <= l2.head.x then {
            ghost { mergeXLemma(l1.head, acc) }
            if(!l1.tail.isEmpty){
                ghost { instantiateForAll(l1.tail, p => l1.head.x <= p.x, l1.tail.head) }
                ghost { tranisitiveSortedListIncreasingLemmaX(acc, l1.tail.head.x, l1.head.x) }
            }
            mergeXAcc(l1.tail , l2 , l1.head :: acc)
        }
        else{
            ghost { mergeXLemma(l2.head, acc) }
            if(!l2.tail.isEmpty){
                ghost { instantiateForAll(l2.tail, p => l2.head.x <= p.x, l2.tail.head) }
                ghost { tranisitiveSortedListIncreasingLemmaX(acc, l2.tail.head.x, l2.head.x) }
            }
            mergeXAcc(l1 , l2.tail , l2.head:: acc)
        }
        
    }.ensuring(res0 => isReverseSortedX(res0) && l1.size + l2.size + acc.size == res0.size && l1.content ++ l2.content ++ acc.content == res0.content) 

    /* Merge 2 lists sorted by X-coordinates to obtain a sorted list */
    def mergeX(l1: List[Point], l2: List[Point]): List[Point]={
        require(isSortedX(l1) && isSortedX(l2))
        val z = mergeXAcc(l1, l2, List[Point]())
        ghost { reverseSortingLemmaX(z) }
        z.reverse
    }.ensuring(res0 => l1.size + l2.size == res0.size && isSortedX(res0) && res0.content == l1.content ++ l2.content)

    /************************************** Functions related to y-coordinates **************************************/


    /* Check if list is sorted by Y coordinates */
    def isSortedY(l: List[Point]): Boolean =
        if l.isEmpty then true
        else l.forall(p => l.head.y <= p.y) && isSortedY(l.tail)

    @ghostAnnot
    def isReverseSortedY(l: List[Point]): Boolean = {
        if l.isEmpty then true
        else l.forall(p => p.y <= l.head.y) && isReverseSortedY(l.tail)
    }

    /* Lemma to imply transitivity of <= operation on elements of a list (y-coordinates) */
    @ghostAnnot
    def tranisitiveSortedListLemmaY(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(a <= b && l.forall(p => b <= p.y))
    }.ensuring(_ => l.size == 0 || l.forall(p => a <= p.y))

    @ghostAnnot
    def tranisitiveSortedListIncreasingLemmaY(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(b <= a && l.forall(p => p.y <= b))
    }.ensuring(_ => l.size == 0 || l.forall(p => p.y <= a))
    
    /* Merge sort function to sort a list of points according to their y-coordinates */    
    def mergeSortY(l: List[Point]): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAtIndex(l.size/2)
            mergeY(mergeSortY(lhalf), mergeSortY(rhalf))
        }
    }.ensuring(res0 => l.size == res0.size && isSortedY(res0) && l.content == res0.content)
    
    @ghostAnnot
    def headSmallerY(@induct l: List[Point]): Unit = {
        require(isReverseSortedY(l))
    }.ensuring(_ => l.isEmpty || l.last.y <= l.head.y)

    @ghostAnnot
    def initIsReverseSortedY(@induct l: List[Point]): Unit = {
        require(isReverseSortedY(l))
        if(!l.isEmpty){
            if(!l.tail.isEmpty){
                initIsReverseSortedY(l.tail)
                assert(isReverseSortedY(l.tail.init))
                assert(l.tail.init == l.init.tail)
                assert(l.tail.forall(p => p.y <= l.head.y))
                wholeImpliesSubsetLemma(l.tail, List[Point](), l.init.tail, p => p.y <= l.head.y)
                assert({val a = l.tail.last.y
                    l.tail.init.forall(p => a <= p.y)})
                // assert(l.tail.last == l.last)
                tranisitiveSortedListLemmaY(l.tail.init, l.last.y, l.tail.last.y)
                assert({val a = l.last.y;
                    l.tail.init.forall(p => a <= p.y)})
                headSmallerY(l)
            }
        }
    }.ensuring(_ => l.isEmpty || (isReverseSortedY(l.init) && {val a = l.last.y; 
        l.init.forall(p => a <= p.y)}))

    @ghostAnnot
    def reverseProperty(@induct l:  List[Point]): Unit ={
    }.ensuring(_ => l.isEmpty || l.reverse == l.last :: l.init.reverse)

    @ghostAnnot
    def reverseSortingLemmaY(l: List[Point]): Unit = {
        require(isReverseSortedY(l))
        if(!l.isEmpty) then {
            val z = l.init
            initIsReverseSortedY(l)
            assert(isReverseSortedY(z))
            reverseSortingLemmaY(z)
            assert({val a = l.last.y; l.init.forall(p => a <= p.y)})
            wholeImpliesSubsetLemma(l.init, List[Point](), l.init.reverse, {val a = l.last.y; p => a <= p.y})
            assert({val a = l.last.y; val b = l.init.reverse; b.forall(p => a <= p.y)})
            assert(isSortedY(l.init.reverse))
            reverseProperty(l)
            // assert(l.init.reverse.forall())
        }
    }.ensuring(_ => isSortedY(l.reverse))

    @ghostAnnot
    def mergeYLemma(p0: Point, l: List[Point]): Unit = {
        require(isReverseSortedY(l)  && l.forall(p => p.y <= p0.y))
    }.ensuring(_ => isReverseSortedY(p0 :: l))

    def mergeYAcc(l1: List[Point], l2: List[Point] , acc: List[Point]): List[Point] = {
        require(isSortedY(l1) && isSortedY(l2) && isReverseSortedY(acc) && (l1.isEmpty || {val a = l1.head.y; acc.forall(p => p.y <= a)}) && (l2.isEmpty || {val a = l2.head.y; acc.forall(p => p.y <= a)}))
        
        if(l1.isEmpty && l2.isEmpty) then acc
        else if (l1.isEmpty) then {
            ghost { mergeYLemma(l2.head, acc) }
            if(!l2.tail.isEmpty){
                val a = l2.tail.head
                ghost { instantiateForAll(l2.tail, p => l2.head.y <= p.y, a) }
                ghost { tranisitiveSortedListIncreasingLemmaY(acc, l2.tail.head.y, l2.head.y) } 
            }
            mergeYAcc(l1 , l2.tail , l2.head :: acc)
        }
        else if (l2.isEmpty) then {
            ghost { mergeYLemma(l1.head, acc) }
            if(!l1.tail.isEmpty){
                ghost { instantiateForAll(l1.tail, p => l1.head.y <= p.y, l1.tail.head) }
                ghost { tranisitiveSortedListIncreasingLemmaY(acc, l1.tail.head.y, l1.head.y) }
            }
            mergeYAcc( l1.tail, l2,  l1.head :: acc)
        }
        else if l1.head.y <= l2.head.y then {
            ghost { mergeYLemma(l1.head, acc) }
            if(!l1.tail.isEmpty){
                ghost { instantiateForAll(l1.tail, p => l1.head.y <= p.y, l1.tail.head) }
                ghost { tranisitiveSortedListIncreasingLemmaY(acc, l1.tail.head.y, l1.head.y) }
            }
            mergeYAcc(l1.tail , l2 , l1.head :: acc)
        }
        else{
            ghost { mergeYLemma(l2.head, acc) }
            if(!l2.tail.isEmpty){
                ghost { instantiateForAll(l2.tail, p => l2.head.y <= p.y, l2.tail.head) }
                ghost { tranisitiveSortedListIncreasingLemmaY(acc, l2.tail.head.y, l2.head.y) }
            }
            mergeYAcc(l1 , l2.tail , l2.head:: acc)
        }
        
    }.ensuring(res0 => isReverseSortedY(res0) && l1.size + l2.size + acc.size == res0.size && l1.content ++ l2.content ++ acc.content == res0.content) 

    def mergeY(l1: List[Point], l2: List[Point]): List[Point]={
        require(isSortedY(l1) && isSortedY(l2))
        val z = mergeYAcc(l1, l2, List[Point]())
        ghost { reverseSortingLemmaY(z) }
        z.reverse
    }.ensuring(res0 => l1.size + l2.size == res0.size && isSortedY(res0) && res0.content == l1.content ++ l2.content)

     /* Function that implements `list.filter` and proves that filtering
    few elements of list sorted by Y-coordinates results in a sorted list */
    @ghostAnnot
    def filterSorted(l: List[Point], p: Point => Boolean): Unit = {
        require(isSortedY(l))
        if(!l.isEmpty){
            assert(l.forall(p => l.head.y <= p.y))
            val tail_sorted = l.tail.filter(p)
            filterSorted(l.tail, p)
            assert(l.forall(p => l.head.y <= p.y))
            wholeImpliesSubsetLemma(l, List(), tail_sorted, (p => l.head.y <= p.y))
            assert(tail_sorted.forall(p => l.head.y <= p.y))
        }
    }.ensuring(_ => isSortedY(l.filter(p)) && l.filter(p).content.subsetOf(l.content))


    /********************************* Take, drop and split for sorted lists ************************/

    /* Proves that list.take preserves sorted property */
    @ghostAnnot
    def take(l: List[Point], index: BigInt): Unit = {
        require(isSortedX(l))
        if(!l.isEmpty && index > 0){
            val z = l.tail.take(index-1)
            take(l.tail, index - 1)
            assert(index -1 < 0 || index - 1 >= l.tail.size || {val a = l.tail(index-1).x
                z.forall(p => p.x <= a)})
            if !z.isEmpty then
                tranisitiveSortedListLemmaX(z, l.head.x, l.tail.head.x)
            if(index >= 1 && index < l.size){
                listContainsElement(l.tail, index -1)
                assert(l(index) == l.tail(index-1))
                assert(isSortedX(l.tail))
                val a = l.tail(index - 1).x
                val b = l(index).x
                tranisitiveSortedListIncreasingLemmaX(z, b, a)
                assert(z.forall(p=> p.x <= b))
                instantiateForAll(l, p=> l.head.x <= p.x, l(index))
                assert(l.head.x <= b)
                assert((l.head::z).forall(p=> p.x <= b))
            }
        }
    }.ensuring(_ => isSortedX(l.take(index)) && (l.isEmpty || l.take(index).isEmpty || l.head == l.take(index).head) &&
    (l.take(index).isEmpty || index < 0 || index >= l.size || {val a = l(index).x
        l.take(index).forall(p => p.x <= a)}))


    /* Proves that list.drop preserves sorted property */
    @ghostAnnot
    def drop(l: List[Point], index: BigInt): Unit = {
        require(isSortedX(l))
        if(!l.isEmpty && index > 0){
            drop(l.tail, index-1)
        }
    }.ensuring(_ => isSortedX(l.drop(index)) && (index < 0 || index >=l.size || l.drop(index).isEmpty || l.drop(index).head == l(index)))



    /* Proves that list.spliyAtIndex preserves sorted property */
    @ghostAnnot
    def split(l: List[Point], index: BigInt): Unit = {
        require(isSortedX(l))
        if(!l.isEmpty) {
            val left = l.take(index)
            val right = l.drop(index)
            take(l, index)
            drop(l, index)
        }
    }.ensuring(_ => isSortedX(l.take(index)) && isSortedX(l.drop(index)) && (index < 0 || index - 1 >= l.size || l.drop(index).isEmpty ||
    {val z = l.drop(index).head.x
        l.take(index).forall(p => p.x <= z)}))