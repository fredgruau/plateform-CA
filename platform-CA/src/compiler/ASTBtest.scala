package compiler

import junit.framework.TestCase
import junit.framework.Assert.assertEquals
import junit.framework.Assert.fail 
import ASTB._


/**Test the correct implementation of integer operation, by evaluating them */
class ASTBtest extends TestCase {
  private def eval(b:ASTB[B]):Boolean =b match{
  case True(1) => true
  case False(1) => false
  case Or(x,y) => eval(x)|eval(y)  
  case And(x,y) => eval(x)&eval(y)
  case Xor(x,y) => eval(x)^eval(y) 
} 
  
 /** Binary code, LSB at head */ 
 def toBinary(n:Int,size:Int): List[Boolean] =
    if(size==0)  List() else   (if (n%2==1) true else false ) ::toBinary(n/2,size-1)
         
 def toInt(xs: List[Boolean]):Int = (  xs:\ 0 ) ( (x,y)=>  2*y +( if(x) 1 else 0)   )
 def toASTB(x:Boolean)=if(x) True[B](1) else False[B](1)
 def carryFromCode(x:Boolean,y:Boolean,z:Boolean)= eval(carry( toASTB(x), toASTB(y), toASTB(z)))
 def fromASTB  (x:Boolean,y:Boolean,z:Boolean, op:(ASTB[B],ASTB[B],ASTB[B])=>ASTB[B])=eval(op( toASTB(x), toASTB(y), toASTB(z)));
def fromASTB  (x:Boolean,y:Boolean , op:(ASTB[B],ASTB[B] )=>ASTB[B])=eval(op( toASTB(x), toASTB(y) ));
 def scanRight[T1,T2](init:T1, xs:List[T2] , op:(T1,T2)=>T1):List[T1]= {
       var result=List(init);var carry=init; 
        for(elt<- xs){carry=op(carry,elt);result=carry::result} 
        return(result.tail) }  
 /**Forget the additional most significant new bits. */
 def scanLeft[T1,T2](init:T1, xs:List[T2] , op:(T1,T2)=>T1):List[T1]= {
       var result=List(init);var carry=init; 
        for(elt<- xs){carry=op(carry,elt);result=carry::result} 
        return(result.tail.reverse) }  // the .tail forget the supplementary bit.
 private def eval(exp:ASTB[I]):List[Boolean] = exp match { 
    case ConstInt(n,size) =>   toBinary(n,size) 
    case Or(x,y) => (eval(x),eval(y)) .zipped.map(_ | _)
    case And(x,y) => (eval(x),eval(y)) .zipped.map(_ & _)
    case Xor(x,y) => (eval(x),eval(y)) .zipped.map(_ ^ _)
    

    case ScanLeft2Init(x,y,op,v) => scanLeft[Boolean,(Boolean,Boolean)]( eval(v) ,
       (eval(x),eval(y)) .zipped.map ((x,y)=>(x,y))  ,
       ( u:Boolean,v:(Boolean,Boolean))=> v match { case(v1,v2)=>   fromASTB(u,v1,v2,op) }
    )       
    case ScanLeft1Init(x,op,v) => scanLeft[Boolean, Boolean ]( eval(v) ,
       eval(x)   ,       ( u:Boolean,w: Boolean )=>   fromASTB(u,w,op) 
    )    
    case ScanRight2(x,y,op,v) => scanRight[Boolean,(Boolean,Boolean)]( eval(v) ,
       (eval(x).reverse,eval(y).reverse) .zipped.map ((x,y)=>(x,y))  ,
       ( u:Boolean,v:(Boolean,Boolean))=> v match { case(v1,v2)=>   fromASTB(u,v1,v2,op) }
    )
    case _ => List(true, false)
  }
 

def testBinary(){println(toInt(toBinary(3,5)));assertEquals(toInt(toBinary(3,5)),3)  }
def testCarry() {assertEquals(eval(carry(True(1),True(1),False(1))), true);
                 assertEquals(eval(carry(True(1),False(1),False(1))), false)}
val quatre =ConstInt(4,5); val trois =ConstInt(3,5); def testConstInt() {assert(toInt(eval(trois))== 3 )  }
val sept =Or(trois,quatre); def testOr() {assert(toInt(eval(sept))== 7 )  }
val un =ConstInt(1,5);val cinq =add(quatre,un);def testAdd1() {assert(toInt(eval(cinq))== 5,eval(cinq) )  }
val six=add(trois,trois); def s() {assert(toInt(eval(six))== 6, eval(six) )  }
}