import static org.hamcrest.core.Is.is;
import static org.junit.Assert.*;

import java.util.*;
import java.text.*;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.JUnitCore;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import java.lang.NumberFormatException;
import java.lang.ArithmeticException;


public class CalcTest {
   public static void main(String[] args) {
      JUnitCore.main( CalcTest.class.getName() );
   }

   @Test(expected=ArithmeticException.class)
   public void zerodiv1(){
     Calc c = new Calc();
     c.eval("1/0");
   }

   @Test(expected=ArithmeticException.class)
   public void zerodiv2(){
     Calc c = new Calc();
     c.eval("1/(2-2)");
   }

   @Test(expected=ParseCancellationException.class)
   public void parseTest1() {
      Calc c = new Calc();
      c.eval("@");
   }

   @Test(expected=ParseCancellationException.class)
   public void parseTest2() {
      Calc c = new Calc();
      c.eval("1+#3@");
   }

   @Test(expected=ParseCancellationException.class)
   public void parseTest3() {
      Calc c = new Calc();
      c.eval("1+-3");
   }

   @Test
   public void funcTest() {
      Calc c = new Calc();
      assertEquals(c.eval("101").longValue() , 101);
      assertEquals(c.eval("-1+2").longValue() , 1);
      assertEquals(c.eval("1+(-3)").longValue() , -2);
      assertEquals(c.eval("-(1+2*3)+(4*(5+6))").longValue() , 37);
      assertEquals(c.eval("22-(4+5)*2").longValue() , 4);
      assertEquals(c.eval("9-6/7*8").longValue() , 9);
      assertEquals(c.eval("2/(1+1)").longValue() , 1);
      assertEquals(c.eval("-9/(0*2+3)").longValue() , -3);
      assertEquals(c.eval("000222+(-00232)*44").longValue() , -9986);
      assertEquals(c.eval("-(-(-3))").longValue() , -3);
      assertEquals(c.eval("8*6/7").longValue() , 6);
   }
}
 
