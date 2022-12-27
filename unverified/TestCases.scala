import stainless.collection._
import stainless.lang._
import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.equations._
import stainless.lang.StaticChecks._


import scala.annotation.tailrec
import java.io._

import point2d.*
// import helper.*
// import listLemmas.*
// import sparsity.*
// import sparsityLemmas.*
// import bruteForce.*
// import lemmas.*
import ClosestPointUnverified.*
import Generator.*



object Testing:
    extension (pt: Point) {
        def printPoint (): String = {
            s"Point(${pt.x},${pt.y})"
        }
    }

    def prettyDisplay(p: PairPoint): String = {
        s"${p._1.printPoint()}, ${p._2.printPoint()}"
    }

    @tailrec
    def generateSomePoints(n: Int, acc: List[Point] = List[Point]() ): List[Point] = {

        if(n == 0) then acc else generateSomePoints(n-1 , pointGenerator.generate() :: acc )

    }
       
    def main(args: Array[String]): Unit = {
        val n = args(0).toInt

        

        for (ti <- 0 to 10) {

            val points6 =  generateSomePoints(n )

            // points6.map(p => println( p.printPoint()))
            // println(" \n\n ")

            val fw = new FileWriter("runtimes.log", true)




            val msBefore = System.currentTimeMillis;
            val closestPair = findClosestPair(points6);
            val msAfter = System.currentTimeMillis;

            fw.write(s"Ran for ${n} points in ${msAfter - msBefore} ms\n")
            fw.close



        }
        

        


    }