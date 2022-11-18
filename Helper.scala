import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import point2d._

package helper:

    def min(x: BigInt, y: BigInt) = if (x < y) then x else y

    // // def isSorted(l: List[Point])(by_y : Boolean): Boolean =
    // //     if l.isEmpty || l.tail.isEmpty then true 
    // //     else if by_y then l.head.y <= l.tail.head.y && isSorted(l.tail)(by_y)
    // //     else l.head.x <= l.tail.head.x && isSorted(l.tail)(by_y)

    def isSorted(l: List[Point])(by_y : Boolean): Boolean =
        if l.isEmpty then true
        else if by_y then l.forall(p => l.head.y <= p.y) && isSorted(l.tail)(by_y)
        else l.forall(p => l.head.x <= p.x) && isSorted(l.tail)(by_y)

    def mergeSort(l: List[Point])(by_y: Boolean): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAtIndex(l.size/2)
            merge(mergeSort(lhalf)(by_y), mergeSort(rhalf)(by_y))(by_y)
        }
    }.ensuring(res0 => l.size == res0.size && isSorted(res0)(by_y) && l.content == res0.content)

    def filterSorted(@induct l: List[Point])(p: Point => Boolean): List[Point] = {
        require(isSorted(l)(true))
        if l.isEmpty then l
        else {
            assert(l.forall(p => l.head.y <= p.y))
            val tail_sorted = filterSorted(l.tail)(p)
            assert(l.forall(p => l.head.y <= p.y))
            tp(l, List(), tail_sorted, (p => l.head.y <= p.y))
            assert(tail_sorted.forall(p => l.head.y <= p.y))
            if p(l.head) then l.head::tail_sorted else tail_sorted
        }
        
    }.ensuring(res0 => isSorted(res0)(true) && res0.content.subsetOf(l.content))

    def tranisitiveSortedListLemmaY(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(isSorted(l)(true) && a <= b && l.forall(p => b <= p.y))
    }.ensuring(_ => l.size == 0 || l.forall(p => a <= p.y))

    def tranisitiveSortedListLemmaX(@induct l:List[Point], a: BigInt, b: BigInt) = {
        require(isSorted(l)(false) && a <= b && l.forall(p => b <= p.x))
    }.ensuring(_ => l.size == 0 || l.forall(p => a <= p.x))

    // // isSorted(filterSorted(l)(p))(true)
    
    // // if p(l.head )

   



    def merge(l1: List[Point], l2: List[Point])(by_y: Boolean): List[Point]={
        require(isSorted(l1)(by_y) && isSorted(l2)(by_y))
        // decreases(l1.size + l2.size)
        if l1.isEmpty then l2
        else if l2.isEmpty then l1
        else if by_y then {
            (if l1.head.y <= l2.head.y then {
                //assert(l1.head.y <= l2.head.y)
                
                tranisitiveSortedListLemmaY(l2, l1.head.y, l2.head.y)
                assert(l2.forall(p => l1.head.y <= p.y) && l1.tail.forall(p => l1.head.y <= p.y))
                
                val z = merge(l1.tail, l2)(true)
                
                assert(isSorted(z)(true))
                tp(l1, l2, z, p => l1.head.y <= p.y)
                assert(z.forall(p => l1.head.y <= p.y))
                l1.head::z
            } else {
                tranisitiveSortedListLemmaY(l1, l2.head.y, l1.head.y)
                assert(l1.forall(p => l2.head.y <= p.y) && l2.tail.forall(p => l2.head.y <= p.y))
                
                val z = merge(l1, l2.tail)(true)
                
                assert(isSorted(z)(true))
                tp(l1, l2, z, p => l2.head.y <= p.y)
                assert(z.forall(p => l2.head.y <= p.y))
                l2.head::z
            })
        }
        else {(if l1.head.x <= l2.head.x then {
            tranisitiveSortedListLemmaX(l2, l1.head.x, l2.head.x)
            assert(l2.forall(p => l1.head.x <= p.x) && l1.tail.forall(p => l1.head.x <= p.x))
                
            val z = merge(l1.tail, l2)(false)
            
            assert(isSorted(z)(false))
            tp(l1, l2, z, p => l1.head.x <= p.x)
            assert(z.forall(p => l1.head.x <= p.x))
            l1.head::z
            
        } else {
            tranisitiveSortedListLemmaX(l1, l2.head.x, l1.head.x)
                assert(l1.forall(p => l2.head.x <= p.x) && l2.tail.forall(p => l2.head.x <= p.x))
                
                val z = merge(l1, l2.tail)(false)
                
                assert(isSorted(z)(false))
                tp(l1, l2, z, p => l2.head.x <= p.x)
                assert(z.forall(p => l2.head.x <= p.x))
                l2.head::z

            })}
    }.ensuring(res0 => l1.size + l2.size == res0.size && isSorted(res0)(by_y) && res0.content == l1.content ++ l2.content)

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

    def tp(l1: List[Point], l2: List[Point], l3: List[Point], predicate: Point => Boolean): Unit = {
        require(l1.forall(predicate) && l2.forall(predicate) && l3.content.subsetOf(l1.content ++ l2.content))
        if !l3.isEmpty then {
            if l1.content.contains(l3.head) then {
                assert(l1.contains(l3.head))
                instantiateForAll(l1, predicate, l3.head)
                assert(predicate(l3.head))
                tp(l1, l2, l3.tail, predicate)} 
            else {
                assert(l2.content.contains(l3.head))
                instantiateForAll(l2, predicate, l3.head)
                assert(predicate(l3.head))
                tp(l1, l2, l3.tail, predicate)
            }
        }
    }.ensuring(_=> l3.forall(predicate))
