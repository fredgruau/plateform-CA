object firstWorksheet {;import org.scalaide.worksheet.runtime.library.WorksheetSupport._; def main(args: Array[String])=$execute{;$skip(74); 
  def square (x:Double):Double = {
  return x*x
 };System.out.println("""square: (x: Double)Double""");$skip(12); val res$0 = 
  square(5);System.out.println("""res0: Double = """ + $show(res$0));$skip(65); 
  def great(name:String):Unit = {
  println(s"Hello, $name")
  };System.out.println("""great: (name: String)Unit""");$skip(16); 
  great("nick")}
}
