import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.ANTLRErrorStrategy;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import java.lang.NumberFormatException;
import java.math.BigInteger;
import java.util.*;

public class Calc{
    public BigInteger eval(@NotNull String s){
        CharStream input = new ANTLRInputStream(s);
        ArithLexer lexer = new ArithLexer(input);
        TokenStream tokens = new CommonTokenStream(lexer);
        ArithParser parser = new ArithParser(tokens);
        ANTLRErrorStrategy errHandler =  new CalcErrorStrategy();
        parser.setErrorHandler( errHandler );
        parser.addParseListener(new ArithBaseListener());
        ArithParser.StartContext uu = parser.start();
        return new ExprNode(uu.expr()).eval();
    }

    private static class ExprNode {
       private List<String> ops;
       private List<MexprNode> mexprs;
       public ExprNode(ArithParser.ExprContext ctx){
            ops = new ArrayList<String>();
            mexprs = new ArrayList<MexprNode>();
            if(ctx.prefix!=null && ctx.prefix.getText().equals("-")){
                 ops.add("-");
            }else{
                 ops.add("+");
            }
            mexprs.add(new MexprNode(ctx.mexpr(0)));
            List<ArithParser.AddsubContext> _ops = ctx.addsub();
            for(int i=0 ; i<_ops.size();i++){
                if(_ops.get(i).PLUS()!=null){
                       ops.add("+");
                }else{
                       ops.add("-");
                }
                mexprs.add(new MexprNode(ctx.mexpr(i+1)));
            } 
       }
       public BigInteger eval(){
            BigInteger ret = new BigInteger("0");
            for(int i = 0 ; i < ops.size() ; i++){
               if(ops.get(i).equals("+")){
                   ret = ret.add( mexprs.get(i).eval() );
               }else{
                   ret = ret.subtract( mexprs.get(i).eval() );
               }
            }
            return ret;
       }
    }

    private static class MexprNode{
       private List<String> ops;
       private List<AtomNode> atoms;

       public MexprNode(ArithParser.MexprContext ctx){
            ops = new ArrayList<String>();
            atoms = new ArrayList<AtomNode>();
            atoms.add( new AtomNode(ctx.atom(0)) );
            List<ArithParser.MuldivContext> _ops = ctx.muldiv();
            for(int i=0 ; i<_ops.size();i++){
                if(_ops.get(i).MUL()!=null){
                       ops.add("*");
                }else{
                       ops.add("/");
                }
                atoms.add(new AtomNode(ctx.atom(i+1)));
            }
       }

       public BigInteger eval(){
          BigInteger ret = atoms.get(0).eval();
          for(int i = 0 ; i < ops.size() ; i++){
               if(ops.get(i).equals("*")){
                   ret = ret.multiply( atoms.get(i+1).eval() );
               }else{
                   ret = ret.divide( atoms.get(i+1).eval() );
               }
          }
          return ret;
       }
    }

    private static class AtomNode {
       private BigInteger val = null;
       private ExprNode expr = null;

       public AtomNode(ArithParser.AtomContext ctx){
            if (ctx.INT()!=null){
                 String s = ctx.INT().getSymbol().getText();
                 val = new BigInteger(s);
            }else{
                 expr = new ExprNode(ctx.expr());
            }
       }
       public BigInteger eval(){
            if(val!=null)return val;
            return expr.eval();
       }
    }

}
