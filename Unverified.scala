import stainless.collection._
import stainless.lang._
import stainless.annotation._
 
object ClosestPoint {

    class Point (val x: BigInt, val y: BigInt){
        def distance(that: Point): BigInt = (x - that.x)*(x - that.x) + (y - that.y)*(y - that.y)
    }

    def min(x: BigInt, y: BigInt) = if (x < y) then x else y

    def findClosestPairInStrip(x: (Point, Point))(l: List[Point]):(Point, Point) =
        if l.isEmpty || l.tail.isEmpty then x
        else {
            val p1 = findClosestPointInStrip(l.head)(x._1.distance(x._2))(l.tail)
            if x._1.distance(x._2) <= p1.distance(l.head) then
                findClosestPairInStrip(x)(l.tail)
            else findClosestPairInStrip((l.head, p1))(l.tail)
        }
    
    // l (strip) is sorted by y coordinates
    def findClosestPointInStrip(p: Point)(d: BigInt)(l: List[Point]): Point =
        require(!l.isEmpty)
        if (p.y - l.head.y)*(p.y - l.head.y) >= d then l.head
        else{
            if l.tail.isEmpty then l.head
            else{
                val p1 = findClosestPointInStrip(p)(min(d, p.distance(l.head)))(l.tail)
                if p.distance(l.head) <= p.distance(p1) then l.head else p1
            }
        }

    // l (complete list) is sorted by y coordinates 
    def combine(lpoint: (Point, Point))(rpoint: (Point, Point))(div: BigInt)(l: List[Point]): (Point, Point) =
        val z = if lpoint._1.distance(lpoint._2) <= rpoint._1.distance(rpoint._2) then lpoint else rpoint
        findClosestPairInStrip(z)(l.filter(p => (p.x - div)*(p.x - div) < z._1.distance(z._2)))

    def mergeSort(l: List[Point])(f: (Point, Point) => Boolean): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAtIndex(l.size/2)
            merge(mergeSort(lhalf)(f), mergeSort(rhalf)(f))(f)
        }
    }.ensuring(l.size == _.size)


    def merge(l1: List[Point], l2: List[Point])(f: (Point, Point) => Boolean): List[Point]={
        if l1.isEmpty then l2
        else if l2.isEmpty then l1
        else if f(l1.head, l2.head) then l1.head::merge(l1.tail, l2)(f)
        else l2.head::merge(l1, l2.tail)(f)
    }.ensuring(l1.size + l2.size == _.size)
    
    // l (complete list) is sorted by x coordinates, return sorted by y coordinates
    def findClosestPairRec(l: List[Point]): (List[Point], (Point, Point)) =
        require(l.size >= 2)
        if l.size <= 3 then (List[Point](), (l(0), l(1)))
        else{
            val (left_half, right_half) = l.splitAtIndex(l.size/2)
            val (lsorted, lpoint) = findClosestPairRec(left_half)
            val (rsorted, rpoint) = findClosestPairRec(right_half)
            val sortedList = merge(lsorted, rsorted)(_.y <= _.y)
            (sortedList, combine(lpoint)(rpoint)(right_half.head.x)(sortedList))
        }

    def findClosestPair(l: List[Point]) =
        require(l.size >= 2)
        findClosestPairRec(mergeSort(l)(_.x <= _.x))._1


    // def closestPair(x: List[Point]): (Point, Point) = {
    //     require(x.size >= 2)
    //     if (x.size == )
    // }

    def inc(x: Int) = x




    @extern
    def main(args: Array[String]): Unit = {
        println(inc(1))
    }

}