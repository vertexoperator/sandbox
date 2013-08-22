import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.ANTLRErrorStrategy;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import java.util.List;
import java.lang.NumberFormatException;
import java.math.BigInteger;
import java.util.Stack;


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
        return eval(uu.expr());
    }

    /* evalExprは再帰呼び出しを含んでいるので、非再帰バージョンも作っておく */
    /*
       data Node = Lit BigInteger
                 | Op String
                 | Expr ExprContext
                 | MExpr MexprContext
                 | Atom AtomContext
    */
    private static class Node {
       private BigInteger _n = null;
       private String _op = null; /* 四則演算 '+' , '-' , '*' , '/' */
       private ArithParser.ExprContext _expr = null;
       private ArithParser.MexprContext _mexpr = null;
       private ArithParser.AtomContext _atom = null;

       public Node(BigInteger n){
          _n = n;
       }
       public Node(String op){
          _op = op;
       }
       public Node(ArithParser.ExprContext expr){
          _expr = expr;
       }
       public Node(ArithParser.MexprContext mexpr){
          _mexpr = mexpr;
       }
       public Node(ArithParser.AtomContext atom){
          _atom = atom;
       }

       public BigInteger INT(){
          return _n;
       }
       public String op(){
          return _op;
       }
       public ArithParser.ExprContext expr(){
          return _expr;
       }
       public ArithParser.MexprContext mexpr(){
          return _mexpr;
       }
       public ArithParser.AtomContext atom(){
          return _atom;
       }
    }

    private BigInteger eval(@NotNull ArithParser.ExprContext ctx){
        BigInteger ret;
        Stack<Node> stack = new Stack<Node>();
        Stack<Node> args = new Stack<Node>();
        stack.push(new Node(ctx));
        while(true){
            assert(!stack.empty());
            Node it = stack.pop();
            if(it.INT()!=null){
                if(stack.empty()){
                   ret = it.INT();
                   break; /* 終了*/
                }else{
                   args.push(it);
                }
            }else if(it.expr()!=null){
               ArithParser.ExprContext ec = it.expr();
               if(ec.prefix!=null && ec.prefix.getText().equals("-")){
                   args.push(new Node(new BigInteger("0")));
                   args.push(new Node(ec.mexpr(0)));
                   args.push(new Node("-"));
               }else{
                   args.push(new Node(ec.mexpr(0)));
               }
               List<ArithParser.AddsubContext> ops = ec.addsub();
               for(int i=0 ; i<ops.size();i++){
                   args.push(new Node(ec.mexpr(i+1)));
                   if(ops.get(i).PLUS()!=null){
                       args.push(new Node("+"));
                   }else{
                       args.push(new Node("-"));
                   }
               }
               for(;!args.empty();){
                   stack.push(args.pop());
               }
            }else if(it.mexpr()!=null){
               ArithParser.MexprContext mc = it.mexpr();
               List<ArithParser.MuldivContext> ops = mc.muldiv();
               args.push( new Node(mc.atom(0)) );
               for(int i=0 ; i<ops.size();i++){
                   args.push( new Node(mc.atom(i+1)) );
                   if(ops.get(i).MUL()!=null){
                       args.push(new Node("*"));
                   }else{
                       args.push(new Node("/"));
                   }
               }
               for(;!args.empty();){
                   stack.push(args.pop());
               }
            }else if(it.atom()!=null){
                ArithParser.AtomContext ac = it.atom();
                if (ac.INT()!=null){
                    String s = ac.INT().getSymbol().getText();
                    stack.push(new Node(new BigInteger(s)));
                }else{
                    stack.push(new Node(ac.expr()));
                }
            }else if(it.op()!=null){
                String op = it.op();
                assert(!args.empty());
                if(op.equals("+")){
                    BigInteger rhs = args.pop().INT();
                    BigInteger lhs = args.pop().INT();
                    BigInteger res = lhs.add( rhs );
                    stack.push( new Node(res) );
                }else if(op.equals("-")){
                    BigInteger rhs = args.pop().INT();
                    BigInteger lhs = args.pop().INT();
                    BigInteger res = lhs.subtract( rhs );
                    stack.push( new Node(res) );
                }else if(op.equals("*")){
                    BigInteger rhs = args.pop().INT();
                    BigInteger lhs = args.pop().INT();
                    BigInteger res = lhs.multiply( rhs );
                    stack.push( new Node(res) );
                }else if(op.equals("/")){
                    BigInteger rhs = args.pop().INT();
                    BigInteger lhs = args.pop().INT();
                    BigInteger res = lhs.divide( rhs );
                    stack.push( new Node(res) );
                }else{
                  assert false: "illegal arithmetic operation? : " +op;
                }
            }else{
                 assert(false);
            }
        }
        return ret;
    }

    /* こっちは再帰版 */
    private BigInteger evalExpr(@NotNull ArithParser.ExprContext ctx){
           List<ArithParser.MexprContext> mexprs = ctx.mexpr();
           List<ArithParser.AddsubContext> ops = ctx.addsub();
           assert(mexprs.size() == ops.size()+1);
           BigInteger ret = evalMexpr(mexprs.get(0));
           if(ctx.prefix!=null && ctx.prefix.getText().equals("-")){
               ret = ret.negate();
           }
           for(int i=0 ; i<ops.size();i++){
              ArithParser.AddsubContext op = ops.get(i);
              ArithParser.MexprContext mexpr = mexprs.get(i+1);
              if(op.PLUS()!=null){
                 ret = ret.add ( evalMexpr( mexpr ) );
              }else{
                 ret = ret.subtract( evalMexpr( mexpr ) );
              }
           }
           return ret;
    }
    
    private BigInteger evalMexpr(@NotNull ArithParser.MexprContext ctx){
           List<ArithParser.AtomContext> atoms = ctx.atom();
           List<ArithParser.MuldivContext> ops = ctx.muldiv();
           assert(atoms.size() == ops.size()+1);
           BigInteger ret = evalAtom(atoms.get(0));
           for(int i=0 ; i<ops.size();i++){
              ArithParser.MuldivContext op = ops.get(i);
              ArithParser.AtomContext atom = atoms.get(i+1);
              if(op.MUL()!=null){
                 ret = ret.multiply( evalAtom( atom ) );
              }else{
                 ret = ret.divide( evalAtom( atom ) );
              }
           }
           return ret;
    }

    private BigInteger evalAtom(@NotNull ArithParser.AtomContext ctx){
        if (ctx.INT()!=null){
           String s = ctx.INT().getSymbol().getText();
           if(s.length() > 8){
              throw new NumberFormatException("入力可能な数値は8桁までです:"+s);
           }  
           return new BigInteger(s);
        }else{
           return evalExpr(ctx.expr());
        }
    }
}
