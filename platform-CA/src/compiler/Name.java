package compiler;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;
public class Name {
	
	

  	//appel: setName((AST)progCompiled, ""); 
	//static void printableDeep(Object o, int n){ 

	static int nbCap(String s){int caps=0; for (int i=0; i<s.length(); i++)  if (Character.isUpperCase(s.charAt(i))) caps++; return caps;};
	
  /**for hashtable, name = connteneur name + hashtablename + "yyy*+ the key name. */
	public static void setName(Object conteneur, String conteneurName) {		Class c = conteneur.getClass();
	  do {java.lang.reflect.Field[] fs = c.getDeclaredFields();
	  for (java.lang.reflect.Field f : fs) {	Object o2 = null;	f.setAccessible(true);String fieldName = f.getName();	try {	o2 = f.get(conteneur);
		} catch (IllegalArgumentException e) {	e.printStackTrace();		} catch (IllegalAccessException e) {e.printStackTrace();}
		if (o2 instanceof AST  ) setNameField(  conteneur,  conteneurName, (AST)o2 ,  fieldName )  ;
	    else if (o2 instanceof HashMap ) { 
		   HashMap m = (HashMap<?, ?>) o2;	for ( Object  a :m.entrySet())  {Object key = ((Map.Entry) a).getKey(); Object value =  ((Map.Entry) a).getValue();
	        if(value instanceof AST && key  instanceof AST  )  setNameField(  conteneur,  conteneurName+fieldName+"yyy" , (AST)value  , ((AST)key).name());
	        else if(value instanceof AST && key  instanceof Integer  )  setNameField(  conteneur,  conteneurName+fieldName+"yyy" , (AST)value  , ""+((Integer)key) );
	                		} }  }
	  c = c.getSuperclass();
	} while (c != Object.class); }

	static int compteurToto=0;
	/**When a field is accessed through different path, each path give a possible name, we want to minimise the path length, wich the number of uppercap */
	public static void setNameField(Object conteneur, String conteneurName,AST fieldToName ,String fieldName) {	
		if(fieldName==null) fieldName="toto"+compteurToto++;
		Boolean hide=  fieldToName.hidden();
		if(fieldName.charAt(0)=='_') 	{fieldName=fieldName.substring(1);hide=true;}; 
		//if( ! conteneur.doNotUseForName.contains(fieldName) )  
		{	if (!conteneurName.equals("")) 	fieldName = ("" + fieldName.charAt(0)).toUpperCase() + fieldName.substring(1).toLowerCase();
		    //if(fieldToName.ignoreForName)  	fieldName="";
	     	if (fieldToName.name() == null || fieldToName.name() != null && nbCap(fieldToName.name()) > nbCap(conteneurName + fieldName)	)
	        	{ fieldToName.setName(conteneurName + fieldName);setName(fieldToName, fieldToName.name()); 
	        	  if (fieldToName.shown()) 
	        		fieldToName.addAfter( "_" );	 
	        	  else if (hide)  fieldToName.addBefore( "_");	}	} 	 }
	 

}
