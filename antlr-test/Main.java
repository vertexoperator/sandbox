import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.io.IOException;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import java.lang.NumberFormatException;
import java.math.BigInteger;
import java.lang.ArithmeticException;
import java.util.Scanner;

public class Main{
    private static final String PROMPT = ">> ";
    public static void main(String[] args) throws Exception{
           Calc c = new Calc();
           Scanner stdReader = new Scanner(System.in);
          
           try{
              System.out.print(PROMPT);
              while ( stdReader.hasNextLine() ) {
                 String line = stdReader.nextLine();
                 if (line.equals("exit"))break;
                 if (line.equals("")){
                    System.out.print(PROMPT);
                    continue;
                 }
                 try{
                    BigInteger val = c.eval(line);
                    System.out.println(val);
                 }catch(ParseCancellationException e){
                    System.out.println("SyntaxError: invalid syntax");
                 }catch(ArithmeticException e){
                    //00除算が発生したはず
                    System.out.println("ZeroDivisionError: integer division or modulo by zero");
                 }catch(Exception e){
                    e.printStackTrace();
                 }
                 System.out.print(PROMPT);
              }
              stdReader.close();
           } catch(IllegalStateException e){
              e.printStackTrace();
           } finally {
              if(stdReader!=null) stdReader.close();
           }
    }

}
