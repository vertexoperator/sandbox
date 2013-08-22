import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.atn.*;

public class CalcErrorStrategy extends BailErrorStrategy {

    @Override
    public Token recoverInline(Parser recognizer)
        throws RecognitionException
    {
         InputMismatchException e = new InputMismatchException(recognizer);
         for (ParserRuleContext context = recognizer.getContext(); context != null; context = context.getParent()) {
             context.exception = e;
         }
         reportError(recognizer);
         throw new ParseCancellationException(e);
    }
    
    protected void reportUnwantedToken(@NotNull Parser recognizer) {
	if (inErrorRecoveryMode(recognizer)) {
		return;
	}

	beginErrorCondition(recognizer);
	Token t = recognizer.getCurrentToken();
	String tokenName = getTokenErrorDisplay(t);
	IntervalSet expecting = getExpectedTokens(recognizer);
	String msg = "extraneous input "+tokenName+" expecting "+
		expecting.toString(recognizer.getTokenNames());
	recognizer.notifyErrorListeners(t, msg, null);
    }

    protected void reportMissingToken(@NotNull Parser recognizer) {
	if (inErrorRecoveryMode(recognizer)) {
		return;
	}

	beginErrorCondition(recognizer);
	Token t = recognizer.getCurrentToken();
	IntervalSet expecting = getExpectedTokens(recognizer);
	String msg = "missing "+expecting.toString(recognizer.getTokenNames())+
			" at "+getTokenErrorDisplay(t);
	recognizer.notifyErrorListeners(t, msg, null);
    }

    protected void reportError(@NotNull Parser recognizer) {
       int nextTokenType = recognizer.getInputStream().LA(2);
       IntervalSet expecting = getExpectedTokens(recognizer);
       if ( !expecting.contains(nextTokenType) ) {
           reportUnwantedToken(recognizer);
       }else{
           int currentSymbolType = recognizer.getInputStream().LA(1);
           // if current token is consistent with what could come after current
           // ATN state, then we know we're missing a token; error recovery
           // is free to conjure up and insert the missing token
           ATNState currentState = recognizer.getInterpreter().atn.states.get(recognizer.getState());
           ATNState next = currentState.transition(0).target;
           ATN atn = recognizer.getInterpreter().atn;
           IntervalSet expectingAtLL2 = atn.nextTokens(next, recognizer.getContext());
           if ( expectingAtLL2.contains(currentSymbolType) ) {
               reportMissingToken(recognizer);
           }
       }
    }


}
