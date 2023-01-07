/* Implementation of function for finding closest pair of points */



import point2d.*

object ClosestPointUnverified:

    def min(x: BigInt, y: BigInt): BigInt = {
        if x < y then x else y
    }

    /* Merge sort function to sort a list of points according to their x-coordinates */
    def mergeSortX(l: List[Point]): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAt(l.size/2)
            mergeX(mergeSortX(lhalf), mergeSortX(rhalf))
        }
    }
    /* Tail recursive merge operation keeping an accumulator */
    def mergeXAcc(l1: List[Point], l2: List[Point] , acc: List[Point]): List[Point] = {
        
        if(l1.isEmpty && l2.isEmpty) then acc
        else if (l1.isEmpty) then {
            if(!l2.tail.isEmpty){
                val a = l2.tail.head
            }
            mergeXAcc(l1 , l2.tail , l2.head :: acc)
        }
        else if (l2.isEmpty) then {
            if(!l1.tail.isEmpty){
            }
            mergeXAcc( l1.tail, l2,  l1.head :: acc)
        }
        else if l1.head.x <= l2.head.x then {
            if(!l1.tail.isEmpty){
            }
            mergeXAcc(l1.tail , l2 , l1.head :: acc)
        }
        else{
            mergeXAcc(l1 , l2.tail , l2.head:: acc)
        }
        
    }
    /* Merge 2 lists sorted by X-coordinates to obtain a sorted list */
    def mergeX(l1: List[Point], l2: List[Point]): List[Point]={
        val z = mergeXAcc(l1, l2, List[Point]())
        z.reverse
    }


    /* Tail recursive merge operation keeping an accumulator */
    def mergeYAcc(l1: List[Point], l2: List[Point] , acc: List[Point]): List[Point] = {
        
        if(l1.isEmpty && l2.isEmpty) then acc
        else if (l1.isEmpty) then {
            if(!l2.tail.isEmpty){
                val a = l2.tail.head
            }
            mergeYAcc(l1 , l2.tail , l2.head :: acc)
        }
        else if (l2.isEmpty) then {
            mergeYAcc( l1.tail, l2,  l1.head :: acc)
        }
        else if l1.head.y <= l2.head.y then {
            mergeYAcc(l1.tail , l2 , l1.head :: acc)
        }
        else{
            mergeYAcc(l1 , l2.tail , l2.head:: acc)
        }
        
    }

    /* Merge 2 lists sorted by X-coordinates to obtain a sorted list */
    def mergeY(l1: List[Point], l2: List[Point]): List[Point]={
        val z = mergeYAcc(l1, l2, List[Point]())
        z.reverse
    }

    /* Merge sort function to sort a list of points according to their y-coordinates */    
    def mergeSortY(l: List[Point]): List[Point] = {
        if l.isEmpty || l.tail.isEmpty then l
        else{
            val (lhalf, rhalf) = l.splitAt(l.size/2)
            mergeY(mergeSortY(lhalf), mergeSortY(rhalf))
        }
    }
    

   /* Finds the point closest to p in list l (sorted by y-coordinates)
   If there is no point which has distance less than d, then first point
   having difference in y-coordinate from p of atleast d is returned */
    def bruteForce(l: List[Point]): (List[Point], PairPoint) =  
    {
        val z = mergeSortY(l)
        if l.size == 2 then (z, (l(0), l(1)))
        else {
            val a = l(0).distance(l(1))
            val b = l(0).distance(l(2))
            val c = l(1).distance(l(2))

            /* Explicitly make conditions for verification process*/
            if(a <= b  && b <= c){
                (z, (l(0), l(1)))
            }
            else if(a <= c && c <= b){
                (z, (l(1), l(0)))
            }
            else if(b <= a && a <= c){
                (z, (l(0), l(2)))
            }
            else if(b <=c && c <= a){
                (z, (l(2), l(0)))
            }
            else if(c <= a && a <= b){
                (z, (l(1), l(2)))
            }
            else{
                assert(c <= b && b <= a)
                (z, (l(2), l(1)))
            }
        }
    }

    def findClosestPointInStrip(p: Point)(d: BigInt)(l: List[Point]): Point =
    {
        if l.tail.isEmpty then l.head
        else if d <= (l.head.y - p.y)*(l.head.y - p.y) then {
            //transitiveDistanceProperty(p, d, l.head, l.tail)
            l.head
        }
        else{
            val p1 = findClosestPointInStrip(p)(min(d, p.distance(l.head)))(l.tail)
            if p.distance(l.head) <= p.distance(p1) then l.head else p1
        }
    }


    /* Finds the closest pair in strip. If the closest pair has distance atleast
    as distance between points in x, then x is returned*/

    def findClosestPairInStrip(x: PairPoint)(l: List[Point]):PairPoint =
    {
        if l.isEmpty || l.tail.isEmpty then x
        else {
            val p1 = findClosestPointInStrip(l.head)(pairDistance(x))(l.tail)
            if pairDistance(x) <= p1.distance(l.head) then{
                val z = findClosestPairInStrip(x)(l.tail)
                z
            }
            else {
                val z = findClosestPairInStrip((l.head, p1))(l.tail)
                z
            }
        }
    }    
    /* Combining answers from left and right halves separated by x-coordinate div */

    def combine(lpoint: PairPoint)(rpoint: PairPoint)(div: BigInt)(l: List[Point]): PairPoint = {
        val z = compare(lpoint, rpoint)
        val d = pairDistance(z)
        val l2 = l.filter(p => p.distance(Point(div, p.y)) < d)
        findClosestPairInStrip(z)(l2)
    }        
    /* Find closest pair of points in list l sorted by x-coordinates.
    Also returns l sorted by y-coordinates */

    def findClosestPairRec(l: List[Point]): (List[Point], PairPoint) ={
        if l.size <= 3 then bruteForce(l)
        else{
            val (left_half, right_half) = l.splitAt(l.size/2)
            val (lsorted, lpoint) = findClosestPairRec(left_half)
            val (rsorted, rpoint) = findClosestPairRec(right_half)
            val sortedList = mergeY(lsorted, rsorted)
            val res = combine(lpoint)(rpoint)(right_half.head.x)(sortedList)
            (sortedList, res)
        }
    }    
    /* Find closest pair of points in list l */

    def findClosestPair(l: List[Point]): PairPoint = {
        val p = findClosestPairRec(mergeSortX(l))._2
        p
    }
