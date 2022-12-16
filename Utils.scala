/* This file contains generic functionality related to sorting and
other utility functions like splitting list*/

import stainless.collection._
import stainless.lang._
import stainless.annotation._
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

     /* Lemma to imply transitivity of <= operation on elements of a list (x-coordinates) */
    def tranisitiveSortedListLemmaX(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(isSortedX(l) && a <= b && l.forall(p => b <= p.x))
    }.ensuring(_ => l.forall(p => a <= p.x))

    def tranisitiveSortedListIncreasingLemmaX(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(isSortedX(l) && a <= b && l.forall(p => p.x <= a))
    }.ensuring(_ => l.forall(p => p.x <= b))


    /* Merge sort function to sort a list of points according to their x-coordinates */    
    def mergeSortX(l: List[Point]): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAtIndex(l.size/2)
            mergeX(mergeSortX(lhalf), mergeSortX(rhalf))
        }
    }.ensuring(res0 => l.size == res0.size && isSortedX(res0) && l.content == res0.content)

    /* Merge 2 lists sorted by X-coordinates to obtain a sorted list */
    def mergeX(l1: List[Point], l2: List[Point]): List[Point]={
        require( isSortedX(l1) && isSortedX(l2))
        if l1.isEmpty then l2
        else if l2.isEmpty then l1
        else if l1.head.x <= l2.head.x then {
            tranisitiveSortedListLemmaX(l2, l1.head.x, l2.head.x)
            val z = mergeX(l1.tail, l2)
            wholeImpliesSubsetLemma(l1, l2, z, p => l1.head.x <= p.x)
            l1.head::z
        }
        else {
            tranisitiveSortedListLemmaX(l1, l2.head.x, l1.head.x)
            val z = mergeX(l1, l2.tail)
            wholeImpliesSubsetLemma(l1, l2, z, p => l2.head.x <= p.x)
            l2.head::z

        }
    }.ensuring(res0 => l1.size + l2.size == res0.size && isSortedX(res0) && res0.content == l1.content ++ l2.content)

    /************************************** Functions related to y-coordinates **************************************/


    /* Check if list is sorted by Y coordinates */
    def isSortedY(l: List[Point]): Boolean =
        if l.isEmpty then true
        else l.forall(p => l.head.y <= p.y) && isSortedY(l.tail)

    /* Lemma to imply transitivity of <= operation on elements of a list (y-coordinates) */
    def tranisitiveSortedListLemmaY(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(isSortedY(l) && a <= b && l.forall(p => b <= p.y))
    }.ensuring(_ => l.size == 0 || l.forall(p => a <= p.y))
    
    /* Merge sort function to sort a list of points according to their y-coordinates */    
    def mergeSortY(l: List[Point]): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAtIndex(l.size/2)
            mergeY(mergeSortY(lhalf), mergeSortY(rhalf))
        }
    }.ensuring(res0 => l.size == res0.size && isSortedY(res0) && l.content == res0.content)
    
    /* Merge 2 lists sorted by X-coordinates to obtain a sorted list */
    def mergeY(l1: List[Point], l2: List[Point]): List[Point]={
        require(isSortedY(l1) && isSortedY(l2))
        if l1.isEmpty then l2
        else if l2.isEmpty then l1
        else if l1.head.y <= l2.head.y then {
            tranisitiveSortedListLemmaY(l2, l1.head.y, l2.head.y)
            val z = mergeY(l1.tail, l2)
            wholeImpliesSubsetLemma(l1, l2, z, p => l1.head.y <= p.y)
            l1.head::z
        }
        else {
            tranisitiveSortedListLemmaY(l1, l2.head.y, l1.head.y)
            val z = mergeY(l1, l2.tail) 
            wholeImpliesSubsetLemma(l1, l2, z, p => l2.head.y <= p.y)
            l2.head::z
        }
    }.ensuring(res0 => l1.size + l2.size == res0.size && isSortedY(res0) && res0.content == l1.content ++ l2.content)

     /* Function that implements `list.filter` and proves that filtering
    few elements of list sorted by Y-coordinates results in a sorted list */
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
                tranisitiveSortedListIncreasingLemmaX(z, a, b)
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
    def drop(l: List[Point], index: BigInt): Unit = {
        require(isSortedX(l))
        if(!l.isEmpty && index > 0){
            drop(l.tail, index-1)
        }
    }.ensuring(_ => isSortedX(l.drop(index)) && (index < 0 || index >=l.size || l.drop(index).isEmpty || l.drop(index).head == l(index)))

    

    /* Proves that list.spliyAtIndex preserves sorted property */
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