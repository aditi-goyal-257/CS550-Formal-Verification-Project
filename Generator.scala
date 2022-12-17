import point2d.*

trait Generator[+T]:
    def generate(): T

object Generator {

    

    val integers = new Generator[BigInt]: 
        val rand = java.util.Random(234523)
        def generate() = rand.nextInt()

    val bigIntegers = new Generator[BigInt]: 
        val rand = java.util.Random(234523)
        def generate() = BigInt(rand.nextInt())

    val pairs = new Generator[(BigInt, BigInt)]:
        def generate() = (integers.generate(), integers.generate())

    val pointGenerator = new Generator[(Point)]:
        
        def generate() = Point(bigIntegers.generate() , bigIntegers.generate())


}


