/* Point class and basic functions related to points */

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object point2d:
    /* Point class */
    class Point (val x: BigInt, val y: BigInt){

        /* Computes the square of distance between 2 points */
        def distance(that: Point): BigInt = {
            (x - that.x)*(x - that.x) + (y - that.y)*(y - that.y)
        }

        override def toString(): String = s"Point(${x},${y})"

    }
    def distanceCommutavityLemma(p1: Point, p2: Point) = {        
    }.ensuring(_ => p1.distance(p2) == p2.distance(p1))

    type PairPoint = (Point, Point)
    
    /* Gives square of distance between the 2 points in the input pair */
    def pairDistance(x: PairPoint): BigInt = x._1.distance(x._2)

    /* Given 2 pairs of points, returns the pair with smaller distance*/
    def compare(p1: PairPoint, p2: PairPoint): PairPoint =  {
        if (pairDistance(p1) < pairDistance(p2)) then p1 else p2
    }