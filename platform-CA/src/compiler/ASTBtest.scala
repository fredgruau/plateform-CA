package compiler

import junit.framework.TestCase
import junit.framework.Assert.assertEquals
import junit.framework.Assert.fail 
import ASTB._



class ASTBtest extends TestCase {
  private def eval(b:ASTB[B]):Boolean =b match{
  case True() => true
  case False() => false
  case Or(x,y) => eval(x)|eval(y)  
  case And(x,y) => eval(x)&eval(y)
  case Xor(x,y) => eval(x)^eval(y) 
} 
  
 def toBinary(n:Int,size:Int): List[Boolean] =
    if(size==0)  List() else   (if (n%2==1) true else false ) ::toBinary(n/2,size-1)
        
  def toInt(xs: List[Boolean]):Int = (0 /: xs) ( (x,y)=>  2*x +( if(y) 1 else 0)   )
  def toASTB(x:Boolean)=if(x) True() else False()
 def carryFromCode(x:Boolean,y:Boolean,z:Boolean)= eval(carry( toASTB(x), toASTB(y), toASTB(z)))
 def fromASTB  (x:Boolean,y:Boolean,z:Boolean, op:(ASTB[B],ASTB[B],ASTB[B])=>ASTB[B])=eval(op( toASTB(x), toASTB(y), toASTB(z)));
 def scanRight[T1,T2](init:T1, xs:List[T2] , op:(T1,T2)=>T1):List[T1]= {
       var result=List(init);var carry=init; 
        for(elt<- xs){carry=op(carry,elt);result=carry::result} 
        return(result.tail) } 
 private def eval(exp:ASTB[I]):List[Boolean] = exp match { 
    case ConstInt(n,size) =>   toBinary(n,size).reverse 
    case Or(x,y) => (eval(x),eval(y)) .zipped.map(_ | _)
    case And(x,y) => (eval(x),eval(y)) .zipped.map(_ & _)
    case Xor(x,y) => (eval(x),eval(y)) .zipped.map(_ ^ _)
    
   case ScanRight2(x,y,op,v) => scanRight[Boolean,(Boolean,Boolean)]( eval(v) ,
       (eval(x).reverse,eval(y).reverse) .zipped.map ((x,y)=>(x,y))  ,
       ( u:Boolean,v:(Boolean,Boolean))=> v match { case(v1,v2)=>   fromASTB(u,v1,v2,op) }
    )
   case _ => List(true, false)
  } 
def testCarry() {assertEquals(eval(carry(True(),True(),False())), true) 
assertEquals(eval(carry(True(),False(),False())), false)
}

val trois =ConstInt(3,5)
val un =ConstInt(1,5)
val quatre =ConstInt(4,5)
val cinq =add(quatre,un)
val sept =Or(trois,quatre)
val six=add(trois,trois)
def testConstInt() {assert(toInt(eval(trois))== 3 )  }
def testOr() {assert(toInt(eval(sept))== 7 )  }
def testAdd1() {assert(toInt(eval(cinq))== 5,eval(cinq) )  }
def testAdd() {assert(toInt(eval(six))== 6,eval(six) )  }


 
}