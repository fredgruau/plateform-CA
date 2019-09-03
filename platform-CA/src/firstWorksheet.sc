object firstWorksheet {
  def square (x:Double):Double = {
  return x*x
 }                                                //> square: (x: Double)Double
  square(5)                                       //> res0: Double = 25.0
  def great(name:String):Unit = {
  println(s"Hello, $name")
  }                                               //> great: (name: String)Unit
  great("nick")                                   //> Hello, nick
}