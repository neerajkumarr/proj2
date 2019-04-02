import java.io.*;
import java.util.*;
import java.util.Map.Entry;

public class CheckTrueFalse {

	static HashSet<String> listOfSymbols = new HashSet<String>();
	
	public static void main(String[] args) {

		if( args.length != 3){
			//takes three arguments
			System.out.println("Usage: " + args[0] +  " [wumpus-rules-file] [additional-knowledge-file] [input_file]\n");
			exit_function(0);
		}
		//create some buffered IO streams
		String buffer;
		BufferedReader inputStream;
		BufferedWriter outputStream;
		//create the knowledge base and the statement
		LogicalExpression knowledge_base = new LogicalExpression();
		LogicalExpression stmt1 = new LogicalExpression();
		LogicalExpression stmt2 = new LogicalExpression();
		TTEntails tt_entails = new TTEntails();
		TTEntails.mdl model = tt_entails.new mdl();

		//open the wumpus_rules.txt
		try {
			inputStream = new BufferedReader( new FileReader( args[0] ) );
			//load the wumpus rules
			System.out.println("\nloading the wumpus rules...");
			knowledge_base.setConnective("and");
			while(  ( buffer = inputStream.readLine() ) != null ) 
			{
				if( !(buffer.startsWith("#") || (buffer.equals( "" )) )) 
				{
					//the line is not a comment
					LogicalExpression subExpression = readExpression( buffer );
					knowledge_base.setSubexpression( subExpression );
				}
			}		
			//close the input file
			inputStream.close();
		} catch(Exception e) 
		{
			System.out.println("failed to open " + args[0] );
			e.printStackTrace();
			exit_function(0);
		}
		//end reading wumpus rules
		//read the additional knowledge file
		try {
			inputStream = new BufferedReader( new FileReader( args[1] ) );
			//load the additional knowledge
			System.out.println("loading the additional knowledge...");
			// the connective for knowledge_base is already set.  no need to set it again.
			// i might want the LogicalExpression.setConnective() method to check for that
			//knowledge_base.setConnective("and");
			while(  ( buffer = inputStream.readLine() ) != null) 
			{
				if( !(buffer.startsWith("#") || (buffer.equals("") ))) 
				{
					String tmpbuf = buffer;
					if(tmpbuf.contains("not")) {
						String[] splittmp = tmpbuf.split(" ");
						splittmp[1] = splittmp[1].substring(0, splittmp[1].length()-1);
						model.hashMap.put(splittmp[1], false);
					}
					else {
						tmpbuf = tmpbuf.trim();
						model.hashMap.put(tmpbuf, true);
					}
					LogicalExpression subExpression = readExpression( buffer );
					knowledge_base.setSubexpression( subExpression );
				}
			}
			//close the input file
			inputStream.close();
		} catch(Exception e) {
			System.out.println("failed to open " + args[1] );
			e.printStackTrace();
			exit_function(0);
		}
		//end reading additional knowledge
		// check for a valid knowledge_base
		if( !valid_expression( knowledge_base ) ) {
			System.out.println("invalid knowledge base");
			exit_function(0);
		}
		// print the knowledge_base
		//knowledge_base.print_expression("\n");

		String beta1 = "", beta2 = "";
		// read the statement file
		try {
			inputStream = new BufferedReader( new FileReader( args[2] ) );
			System.out.println("Loading the statement file...");
			Get_sym(knowledge_base);
			Set<String> uniqueSetSymbol = listOfSymbols;
			//buffer = inputStream.readLine();
			// actually read the statement file
			// assuming that the statement file is only one line long
			while( ( buffer = inputStream.readLine() ) != null ) {
				if( !buffer.startsWith("#") ) {
					if(buffer.contains("not")) {
						beta1 = buffer;
						String[] splitbuf = buffer.split(" ");
						beta2 = splitbuf[1].substring(splitbuf[1].length() - 1);
					}
					else {
						beta1 = buffer;
						beta2 = "(not " + buffer + ")";
					}
					//the line is not a comment
					stmt1 = readExpression( beta1 );
					stmt2 = readExpression( beta2 );
					if (valid_expression(stmt1)&& !isValidInput(beta1, uniqueSetSymbol)) {
						System.out.println("invalid statement");
						return;
					}
					break;
				} 
			}
			//close the input file
			inputStream.close();
		} catch(Exception e) {
			System.out.println("failed to open " + args[2] );
			e.printStackTrace();
			exit_function(0);
		}
		// end reading the statement file
		// check for a valid statement
		if( !valid_expression( stmt1 ) ) {
			System.out.println("invalid statement");
			exit_function(0);
		}
		
		boolean otpt1 = tt_entails.tt_entails(knowledge_base, stmt1, model);
		boolean otpt2 = tt_entails.tt_entails(knowledge_base, stmt2, model);

		try {
			outputStream = new BufferedWriter(new FileWriter(new File("result.txt")));
			if (otpt1 != otpt2) {
				System.out.println("definitely " + otpt1);
				outputStream.write("definitely " + otpt1);
			} else if (otpt1 == otpt2 && otpt1 == false) {
				System.out.println("possibly true, possibly false");
				outputStream.write("possibly true, possibly false");
			} else if (otpt1 == otpt2 && otpt1 == true) {
				System.out.println("both true and false");
				outputStream.write("both true and false");
			}
			outputStream.close();
		} catch (IOException e) {
			System.out.println("Error message : " + e.getMessage());
			e.printStackTrace();
		}
	} //end of main

	private static boolean isValidInput(String beta, Set<String> set) {
		// TODO Auto-generated method stub
		Iterator<String> i = set.iterator();
		boolean boolean12 = false;
		while(i.hasNext()) {
			if(i.next().equals(beta))
				boolean12 = true;
		}
		if(beta.contains("(or") || beta.contains("(and") || beta.contains("(xor") || beta.contains("(not") || beta.contains("(if")	|| beta.contains("(iff"))
			boolean12 = true;
		return boolean12;
	}

	private static void Get_sym(LogicalExpression logEx) {
		// TODO Auto-generated method stub
		if(!(logEx.getUniqueSymbol() == null))
			listOfSymbols.add(logEx.getUniqueSymbol());
		else {
			for(int i = 0; i < logEx.getSubexpressions().size(); i++) {
				LogicalExpression logEx1 = logEx.getSubexpressions().get(i);
				Get_sym(logEx1);
				if(!(logEx1.getUniqueSymbol() == null))
					listOfSymbols.add(logEx1.getUniqueSymbol());
			}
		}
	}

	/* this method reads logical expressions
	 * if the next string is a:
	 * - '(' => then the next 'symbol' is a subexpression
	 * - else => it must be a unique_symbol
	 * 
	 * it returns a logical expression
	 * 
	 * notes: i'm not sure that I need the counter
	 * 
	 */
	public static LogicalExpression readExpression( String input_string ) 
	{
		LogicalExpression result = new LogicalExpression();
		//trim the whitespace off
		input_string = input_string.trim();
		if( input_string.startsWith("(") ) 
		{
			//its a subexpression
			String symbolString = "";
			// remove the '(' from the input string
			symbolString = input_string.substring( 1 );
			if( !symbolString.endsWith(")" ) ) 
			{
				// missing the closing paren - invalid expression
				System.out.println("missing ')' !!! - invalid expression! - readExpression():-" + symbolString );
				exit_function(0);
			}
			else 
			{
				//remove the last ')'
				//it should be at the end
				symbolString = symbolString.substring( 0 , ( symbolString.length() - 1 ) );
				symbolString.trim();
				// read the connective into the result LogicalExpression object					  
				symbolString = result.setConnective( symbolString );
			}
			//read the subexpressions into a vector and call setSubExpressions( Vector );
			result.setSubexpressions( read_subexpressions( symbolString ) );
		} 
		else 
		{   	
			// the next symbol must be a unique symbol
			// if the unique symbol is not valid, the setUniqueSymbol will tell us.
			result.setUniqueSymbol( input_string );
		}
		return result;
	}

	/* this method reads in all of the unique symbols of a subexpression
	 * the only place it is called is by read_expression(String, long)(( the only read_expression that actually does something ));
	 * 
	 * each string is EITHER:
	 * - a unique Symbol
	 * - a subexpression
	 * - Delineated by spaces, and paren pairs
	 * 
	 * it returns a vector of logicalExpressions
	 * 
	 * 
	 */

	public static Vector<LogicalExpression> read_subexpressions( String input_string ) {

		Vector<LogicalExpression> symList = new Vector<LogicalExpression>();
		LogicalExpression newExpression;// = new LogicalExpression();
		String newSymbol = new String();
		input_string.trim();

		while( input_string.length() > 0 ) {
			newExpression = new LogicalExpression();
			if( input_string.startsWith( "(" ) ) {
				//its a subexpression.
				// have readExpression parse it into a LogicalExpression object
				// find the matching ')'
				int parenCounter = 1;
				int matchingIndex = 1;
				while( ( parenCounter > 0 ) && ( matchingIndex < input_string.length() ) ) {
					if( input_string.charAt( matchingIndex ) == '(') {
						parenCounter++;
					} else if( input_string.charAt( matchingIndex ) == ')') {
						parenCounter--;
					}
					matchingIndex++;
				}
				// read untill the matching ')' into a new string
				newSymbol = input_string.substring( 0, matchingIndex );
				// pass that string to readExpression,
				newExpression = readExpression( newSymbol );
				// add the LogicalExpression that it returns to the vector symList
				symList.add( newExpression );
				// trim the logicalExpression from the input_string for further processing
				input_string = input_string.substring( newSymbol.length(), input_string.length() );
			} else {
				//its a unique symbol ( if its not, setUniqueSymbol() will tell us )
				// I only want the first symbol, so, create a LogicalExpression object and
				// add the object to the vector
				if( input_string.contains( " " ) ) {
					//remove the first string from the string
					newSymbol = input_string.substring( 0, input_string.indexOf( " " ) );
					input_string = input_string.substring( (newSymbol.length() + 1), input_string.length() );
				} else {
					newSymbol = input_string;
					input_string = "";
				}
				newExpression.setUniqueSymbol( newSymbol );
				symList.add( newExpression );
			}
			input_string.trim();
			if( input_string.startsWith( " " )) {
				//remove the leading whitespace
				input_string = input_string.substring(1);
			}
		}
		return symList;
	}

	/* this method checks to see if a logical expression is valid or not 
	 * a valid expression either:
	 * ( this is an XOR )
	 * - is a unique_symbol
	 * - has:
	 *  -- a connective
	 *  -- a vector of logical expressions
	 *  
	 * */
	public static boolean valid_expression(LogicalExpression expression)
	{
		// checks for an empty symbol
		// if symbol is not empty, check the symbol and
		// return the truthiness of the validity of that symbol
		if ( !(expression.getUniqueSymbol() == null) && ( expression.getConnective() == null ) ) {
			// we have a unique symbol, check to see if its valid
			return valid_symbol( expression.getUniqueSymbol() );
		}
		// symbol is empty, so
		// check to make sure the connective is valid
		// check for 'if / iff'
		if ( ( expression.getConnective().equalsIgnoreCase("if") )  ||
				( expression.getConnective().equalsIgnoreCase("iff") ) ) {
			// the connective is either 'if' or 'iff' - so check the number of connectives
			if (expression.getSubexpressions().size() != 2) {
				System.out.println("error: connective \"" + expression.getConnective() +
						"\" with " + expression.getSubexpressions().size() + " arguments\n" );
				return false;
			}
		}
		// end 'if / iff' check
		// check for 'not'
		else   if ( expression.getConnective().equalsIgnoreCase("not") ) {
			// the connective is NOT - there can be only one symbol / subexpression
			if ( expression.getSubexpressions().size() != 1)
			{
				System.out.println("error: connective \""+ expression.getConnective() + "\" with "+ expression.getSubexpressions().size() +" arguments\n" ); 
				return false;
			}
		}
		// end check for 'not'
		// check for 'and / or / xor'
		else if ( ( !expression.getConnective().equalsIgnoreCase("and") )  &&
				( !expression.getConnective().equalsIgnoreCase( "or" ) )  &&
				( !expression.getConnective().equalsIgnoreCase("xor" ) ) ) {
			System.out.println("error: unknown connective " + expression.getConnective() + "\n" );
			return false;
		}
		// end check for 'and / or / not'
		// end connective check
		// checks for validity of the logical_expression 'symbols' that go with the connective
		for( Enumeration<LogicalExpression> e = expression.getSubexpressions().elements(); e.hasMoreElements(); ) {
			LogicalExpression testExpression = (LogicalExpression)e.nextElement();
			// for each subExpression in expression,
			//check to see if the subexpression is valid
			if( !valid_expression( testExpression ) ) {
				return false;
			}
		}
		// if the method made it here, the expression must be valid
		return true;
	}

	/** this function checks to see if a unique symbol is valid */
	//////////////////// this function should be done and complete
	// originally returned a data type of long.
	// I think this needs to return true /false
	//public long valid_symbol( String symbol ) {
	public static boolean valid_symbol( String symbol ) {
		if (  symbol == null || ( symbol.length() == 0 )) {
			return false;
		}

		for ( int counter = 0; counter < symbol.length(); counter++ ) {
			if ( (symbol.charAt( counter ) != '_') &&
					( !Character.isLetterOrDigit( symbol.charAt( counter ) ) ) ) {
				System.out.println("String: " + symbol + " is invalid! Offending character:---" + symbol.charAt( counter ) + "---\n");
				return false;
			}
		}
		// the characters of the symbol string are either a letter or a digit or an underscore,
		//return true
		return true;
	}

	private static void exit_function(int value) {
		System.out.println("exiting from checkTrueFalse");
		System.exit(value);
	}	
}

class TTEntails {
	Set<String> symList = new HashSet<String>();	
	int counter = 0;

	public boolean tt_entails(LogicalExpression knowledge_base, LogicalExpression statement, mdl model) {
		List<String> symList = Get_sym(knowledge_base, statement);
		symList = removesym(model,symList);
		return tt_check_all(knowledge_base, statement, symList, model);
	}

	private List<String> removesym(mdl model, List<String> symbolList2) {
		Iterator<Entry<String,Boolean>> i = model.hashMap.entrySet().iterator();
		while (i.hasNext()) {	    	
			Entry<String,Boolean> pair = (Entry<String,Boolean>)i.next();
			symbolList2.remove(pair.getKey());	       
		}
		return symbolList2;
	}

	boolean pl_True(LogicalExpression kb, mdl model){
		Vector<LogicalExpression> vector = kb.getSubexpressions();
		Boolean boolean12 = false;

		if( kb.getConnective() == null ) {						
			return model.hashMap.get(kb.getUniqueSymbol());			
		}
		
		else if(kb.getConnective()!=null && kb.getConnective().equalsIgnoreCase("or")){			
			for(int i=0;i<vector.size();i++){
				boolean12 = boolean12 || pl_True(vector.get(i),model);
			}
			return boolean12;		
		}
		
		else if(kb.getConnective()!=null && kb.getConnective().equalsIgnoreCase("not")){			
			return !(pl_True(kb.getNextSubexpression(),model));
		}
		
		
		else if(kb.getConnective()!=null && kb.getConnective().equalsIgnoreCase("iff")){			
			return boolean12 == pl_True(vector.get(1),model);
		}
		
		else if(kb.getConnective()!=null && kb.getConnective().equalsIgnoreCase("if")){		
			boolean12 = !(boolean12 && !(pl_True(vector.get(1),model)));
			return boolean12;			
		}
		else if(kb.getConnective()!=null && kb.getConnective().equalsIgnoreCase("and")){			
			boolean12 = true;
			for(int i = 0; i < vector.size(); i++){				
				boolean12 = boolean12 && pl_True(vector.get(i),model);
				if(boolean12==false){	
					return boolean12;
				}
			}
			return boolean12;
		}
		else if(kb.getConnective()!=null && kb.getConnective().equalsIgnoreCase("xor")){			
			int truthCounter=0;
			for(int i = 0; i < vector.size(); i++){
				boolean retrieved = pl_True(vector.get(i),model);
				if(retrieved==true)
					truthCounter++;
				if(truthCounter>1)
					return false;
				boolean12 = ((boolean12||retrieved) && !(boolean12 && retrieved));
			}
			return boolean12;
		}
		return true;
	}

	public boolean tt_check_all(LogicalExpression kb, LogicalExpression beta,	List<String> symbols, mdl model) {		
		if (symbols.isEmpty()) 
		{			
			boolean pl_true = pl_True(kb, model);			
			if(pl_true)
			{
				return pl_True(beta, model);		
			}				
			else
			{
				return true;	
			}				
		} 
		else 
		{
			String P = (String)symbols.get(0);			
			List<String> rest = symbols.subList(1, symbols.size());			
			mdl trueModel = model.extend(P, true);
			mdl falseModel = model.extend(P, false);
			return (tt_check_all(kb, beta, rest, trueModel) && (tt_check_all(kb, beta, rest, falseModel)));
		}		
	}

	List<String> Get_sym(LogicalExpression kb, LogicalExpression beta){		
		Get_sym(kb);
		Get_sym(beta);		
		List<String> list = new ArrayList<String>(symList);
		return list;
	}
	void Get_sym(LogicalExpression logEx){
		if(!(logEx.getUniqueSymbol() == null))
			symList.add(logEx.getUniqueSymbol());
		else {
			for(int i = 0 ; i < logEx.getSubexpressions().size(); i++ ){
				LogicalExpression logEx1 = logEx.getSubexpressions().get(i);
				Get_sym(logEx1);
				if(!(logEx1.getUniqueSymbol() == null))
					symList.add(logEx1.getUniqueSymbol());			
			}
		}
	}		

	
	

	

	class mdl{
		public HashMap<String,Boolean> hashMap = new HashMap<String,Boolean>();
		public mdl extend(String symbol, boolean b) {
			mdl model = new mdl();
			model.hashMap.putAll(this.hashMap);
			model.hashMap.put(symbol, b);
			return model;
		}
	}
}