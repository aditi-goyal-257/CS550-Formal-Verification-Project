import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import point2d._

/* Contains generic functionality related to sorting and other utility functions */

package helper:

    /* Returns the minimum of two BigInt */
    def min(x: BigInt, y: BigInt) = if (x < y) then x else y

    /**************************************** Functions related to X-coordinates of points ************************************************/

    /* Check if list is sorted by X coordinates */
    def isSortedX(l: List[Point]): Boolean = {
        if l.isEmpty then true
        else l.forall(p => l.head.x <= p.x) && isSortedX(l.tail)
    }

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

    def listContainsElement(l: List[Point], a: BigInt): Unit= {
        require(a >= 0 && a < l.size)
        if(a != 0){
            listContainsElement(l.tail, a-1)
        }
    }.ensuring(_ => l.contains(l(a)))

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

    /* Lemma to imply transitivity of <= operation on elements of a list (x-coordinates) */
    def tranisitiveSortedListLemmaX(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(isSortedX(l) && a <= b && l.forall(p => b <= p.x))
    }.ensuring(_ => l.forall(p => a <= p.x))

    def tranisitiveSortedListIncreasingLemmaX(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(isSortedX(l) && a <= b && l.forall(p => p.x <= a))
    }.ensuring(_ => l.forall(p => p.x <= b))

    /* Function that implements `list.take` and proves that taking first
    few elements of list sorted by X-coordinates results in a sorted list */
    def take(l: List[Point], index: BigInt): List[Point] = {
        require(isSortedX(l))
        if l.isEmpty || index <= 0 then List[Point]()
        else{
            val z = take(l.tail, index-1)
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
            l.head::z
        }        
    }.ensuring(res0 => isSortedX(res0) && (l.isEmpty || res0.isEmpty || l.head == res0.head) && res0 == l.take(index) && 
    (res0.isEmpty || index < 0 || index >= l.size || {val a = l(index).x
        res0.forall(p => p.x <= a)}))

    /* Function that implements `list.drop` and proves that dropping first
    few elements of list sorted by X-coordinates results in a sorted list */
    def drop(@induct l: List[Point], index: BigInt): List[Point] = {
        require(isSortedX(l))
        if l.isEmpty then List[Point]()
        else if index <= 0 then l
        else{
            drop(l.tail, index-1)
        }
    }.ensuring(res0 => isSortedX(res0) && res0 == l.drop(index) && (index < 0 || index >=l.size || res0.isEmpty || res0.head == l(index)))

    /* Function that implements `list.splitAtIndex` and proves that splitting
    a list sorted by X-coordinates results into two sorted lists */
    def split(l: List[Point], index: BigInt): (List[Point], List[Point]) = {
        require(isSortedX(l))
        if l.isEmpty then (l, l)
        else {
            val left = take(l, index)
            val right = drop(l, index)
            if(!right.isEmpty){
                assert(index <0 || index >= l.size || l(index).x == right.head.x)
                if(index >= 0 && index < l.size){
                assert({val a = l(index).x
                    left.forall(p => p.x <= a)})
                }
            }
            (left, right)
        }
    }.ensuring(res0 => isSortedX(res0._1) && isSortedX(res0._2) && res0 == l.splitAtIndex(index) && (index < 0 || index - 1 >= l.size || res0._2.isEmpty || res0._1.forall(p => p.x <= res0._2.head.x)))

    /************************************** Functions related to y-coordinates **************************************/

    def isSortedY(l: List[Point]): Boolean =
        if l.isEmpty then true
        else l.forall(p => l.head.y <= p.y) && isSortedY(l.tail)

    def mergeSortY(l: List[Point]): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAtIndex(l.size/2)
            mergeY(mergeSortY(lhalf), mergeSortY(rhalf))
        }
    }.ensuring(res0 => l.size == res0.size && isSortedY(res0) && l.content == res0.content)

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
    def filterSorted(@induct l: List[Point])(p: Point => Boolean): List[Point] = {
        require(isSortedY(l))
        if l.isEmpty then l
        else {
            assert(l.forall(p => l.head.y <= p.y))
            val tail_sorted = filterSorted(l.tail)(p)
            assert(l.forall(p => l.head.y <= p.y))
            wholeImpliesSubsetLemma(l, List(), tail_sorted, (p => l.head.y <= p.y))
            assert(tail_sorted.forall(p => l.head.y <= p.y))
            if p(l.head) then l.head::tail_sorted else tail_sorted
        }
        
    }.ensuring(res0 => isSortedY(res0) && res0.content.subsetOf(l.content) && res0 == l.filter(p))

    def tranisitiveSortedListLemmaY(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(isSortedY(l) && a <= b && l.forall(p => b <= p.y))
    }.ensuring(_ => l.size == 0 || l.forall(p => a <= p.y))

    /*************************************************** Generic utility functions and lemmas *******************************************************/

    /* Lemma to prove that if some predicate is true for every element
       of a list, it is also true for any individual element */
    def instantiateForAll(l: List[Point], predicate: Point => Boolean, p: Point): Unit ={
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
    def wholeImpliesSubsetLemma(l1: List[Point], l2: List[Point], l3: List[Point], predicate: Point => Boolean): Unit = {
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

    def subtractingPreservesPredicate(@induct l: List[Point], a: BigInt, b: BigInt) ={
        require(l.forall(p => a <= p.y))
    }.ensuring(l.forall(p => a - b <= p.y - b))

    def squaringPreservesPredicate(@induct l: List[Point], a: BigInt, b: BigInt) ={
        require(l.forall(p => a <= p.y - b) && a>=0)
    }.ensuring(l.forall(p => a*a <= (p.y - b)*(p.y - b)))

    def transitiveSquareSortedListLemmaY(@induct l: List[Point], a: BigInt, b: BigInt, c: BigInt) ={
        require(l.forall(p => a*a <= (p.y -b)*(p.y - b)) && c <= a*a)
    }.ensuring(l.forall(p => c <= (p.y - b)*(p.y - b)))

    def addingPreservesPredicate(@induct l: List[Point], a: BigInt, b: BigInt, c: BigInt) = {
        require(l.forall(p => a <= (p.y - b)*(p.y - b)))
    }.ensuring(l.forall(p => a <= (p.x - c)*(p.x - c) + (p.y - b)*(p.y - b)))

    def distanceFormulaValidForList(@induct l: List[Point], p: Point) ={
    }.ensuring(l.forall(p1 => p1.distance(p) == (p1.x - p.x)*(p1.x - p.x) + (p1.y - p.y)*(p1.y - p.y)))

    def distanceTransitivityLemma(@induct l: List[Point], p: Point, d: BigInt) = {
        require(l.forall(p1 => p1.distance(p) == (p1.x - p.x)*(p1.x - p.x) + (p1.y - p.y)*(p1.y - p.y)) && l.forall(p1 => d <= (p1.x - p.x)*(p1.x - p.x) + (p1.y - p.y)*(p1.y - p.y)))
    }.ensuring(l.forall(p1 => d <= p1.distance(p)))
    
    // def reducingPreservesPointSparsityLemma(@induct l: List[Point], p: Point, d: BigInt, x: BigInt) = {
    //     require(deltaSparsePoint(d, p, l) && x <= d)
    // }.ensuring(deltaSparsePoint(x, p, l))

    def addingPredicateToOrPreserves(d: BigInt, p: Point, @induct l: List[Point]) = {
        require(l.forall(p1 => d <= p1.distance(p)))
    }.ensuring(_ => l.forall(p1 => p == p1 || d <= p1.distance(p)))


    def filteringLemma(l: List[Point], predicate: Point => Boolean, p: Point): Unit = {
        require(l.contains(p) && predicate(p))
        if l.head != p then {
            l.tail.contains(p)
            filteringLemma(l.tail, predicate, p)
        }
    }.ensuring(l.filter(predicate).contains(p))



    def filteringPreservesDeltaPointSparsity(@induct l: List[Point], predicate: Point => Boolean, p: Point, delta: BigInt): Unit = {
        require(isSortedY(l) && deltaSparsePoint(delta, p, l))
    }.ensuring(deltaSparsePoint(delta, p, filterSorted(l)(predicate)))

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
    }.ensuring(deltaSparse(delta, filterSorted(l)(predicate)))


    def tp(@induct ps: List[Point], l: BigInt, d1: BigInt, d2: BigInt): Unit = {
        require(isSortedY(ps) && d1 <= d2)
    }.ensuring(filterSorted(ps)(p => p.distance(Point(l, p.y)) < d1 ) == filterSorted(filterSorted(ps)(p => p.distance(Point(l, p.y)) < d2))(p => p.distance(Point(l, p.y)) < d1))

    



    