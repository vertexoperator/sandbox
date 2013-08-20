grammar Arith;
@rulecatch {
    catch (RecognitionException e) {
        System.out.println("rulecatch");
        throw e;
    }
}

@lexer::members {
  @Override
  public void recover(final LexerNoViableAltException e) {
      throw new ParseCancellationException(e);
  }

}


expr : prefix=('+' | '-')? mexpr (addsub mexpr)*;
mexpr : atom (muldiv atom)*;
atom : INT | '(' expr ')';
addsub: (PLUS|MINUS);
muldiv : (MUL | DIV);

PLUS : '+';
MINUS : '-';
MUL : '*';
DIV : '/';
INT   : ('0'..'9')+ ;
WS    : ( ' '
        | '\r' '\n'
        | '\n'
        | '\t'
        )+ -> skip;

