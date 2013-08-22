ANTLR_SRC = Arith.g
ANTLR_OBJS = ArithBaseListener.java  ArithLexer.java  ArithListener.java  ArithParser.java
SRCS = CalcErrorStrategy.java Calc.java Main.java CalcTest.java
OBJS = $(SRCS:.java=.class) $(ANTLR_OBJS:.java=.class)
CLASSPATH = .:./antlr-4.1-complete.jar:./junit-4.10.jar
JAVAC = javac
JAVA = java
OPTION = -Xlint:all

test: $(OBJS)
	$(JAVA) -cp $(CLASSPATH) CalcTest

run: $(OBJS)
	$(JAVA) -cp $(CLASSPATH) Main


$(OBJS): $(ANTLR_OBJS) $(SRCS)
	$(JAVAC) $(OPTION) -cp $(CLASSPATH) $(ANTLR_OBJS) $(SRCS)

$(ANTLR_OBJS):
	java -cp $(CLASSPATH) org.antlr.v4.Tool $(ANTLR_SRC)

clean:
	rm *.tokens
	rm Arith*.java
	rm *.class	
