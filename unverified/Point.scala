/* Point class and basic functions related to points */


object point2d:
    /* Point class */
    class Point (val x: BigInt, val y: BigInt){

        /* Computes the square of distance between 2 points */
        def distance(that: Point): BigInt = {
            (x - that.x)*(x - that.x) + (y - that.y)*(y - that.y)
        }

    }
    

    type PairPoint = (Point, Point)
    
    /* Gives square of distance between the 2 points in the input pair */
    def pairDistance(x: PairPoint): BigInt = x._1.distance(x._2)

    /* Given 2 pairs of points, returns the pair with smaller distance*/
    def compare(p1: PairPoint, p2: PairPoint): PairPoint =  {
        if (pairDistance(p1) < pairDistance(p2)) then p1 else p2
    }