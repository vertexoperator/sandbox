import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.io.IOException;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import java.lang.NumberFormatException;
import java.math.BigInteger;
import java.lang.ArithmeticException;


public class Main{
    private static final String PROMPT = ">> ";
    public static void main(String[] args) throws Exception{
           Calc c = new Calc();
           BufferedReader stdReader = new BufferedReader(new InputStreamReader(System.in));
           System.out.print(PROMPT);
           String line;
           try{
              while ((line = stdReader.readLine()) != null) {
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
           } catch(IOException e){
              e.printStackTrace();
           } finally {
              try{
                 if(stdReader!=null) stdReader.close();
              } catch (IOException e){
                 e.printStackTrace();
              }
           }
    }

}
