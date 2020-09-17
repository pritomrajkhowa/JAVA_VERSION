# February 20, 2016

# February 29, 2016: 1. change axioms for if1 and if2 to make all axioms of the form x = ... 2. add last label as an output of translate0

# March 10 - April 27: a new translation for while-loop that parameterizes loop input variables and replaces smallest macros by inductive definition. Also a small correction to simplify()

# April 29: combining the two translations (c2l.py.old3 and c2l.py.old4): keep the old translation for program variables but use a new way to inductively define smallest macro: 
# N(x,y) = if C(x,y) then 0 else C(f(x),g(x)), where f and g is the new value of x and y, respectively, after one iteration
# in c2l.py.old4, f and g are the output functions for the body, here we parameterize f and g first, and use f(1,x) and g(1,y) to replace f(x) and g(y), respectively

# May 18: (not done yet) making functions first-order objects by using "+": f+[t1,...,tk,v] stands for the
# function f1 such that forall x1,...,xk: 
# f1(x1,...,xk) = ite(x1=t1 & ... & xk=tk, v, f(x1,...,xk))
# A translator from C to FOL in python 

# June 18: add solve_rec() by Pritom to solve recurrences in translating while-loop
# assume that the only dynamic functions are the program variables given by v and the system generated temporary functions including big N (is_program_var())
# this makes _base redundant

# August 30: add function definitions and function calls and define program as a sequence of functions. See program definitions just before translate1()

#example run: translate1(fact,vfact,1) or translate1(fact,vfact,2)


"""
Assumptions:
1. Program variables:
  - can be any word \w+
  - cannot be _x\d*, _n\d*, _N\d*,_y\d* 
    (these are reserved for general variables,
    natural number variables, and smallest macro constants
    in our axioms)
  - for a variable, its temporary variants are constructed 
    by adding to it TEMP+number
    and its output values after a labeled statement are 
    constructed by adding to it LABEL+number.
    (Currently, TEMP is empty and LABEL is '_'.) 
    This menas that if V is a variable, then
    V+TEMP+\d+ and V+LABEL+\d+ are not allowed to be variables 
    (right now it means that
    V1,V2,... and V_1,V_2,... cannot be variables).
  - smallest is a reserved word so cannot be a variable
"""


import sys
import os


currentdirectory = os.path.dirname(os.path.realpath(__file__))

sys.path.append(currentdirectory+"/packages/ply/")
sys.path.append(currentdirectory+"/packages/plyj/")
sys.path.append(currentdirectory+"/packages/pycparser1/")
sys.path.append(currentdirectory+"/packages/regex/")
sys.path.append(currentdirectory+"/packages/mpmath/")
sys.path.append(currentdirectory+"/packages/sympy/")



import plyj.parser
import plyj.model as m
import copy
import time
import datetime
from sympy import *
import regex


current_milli_time = lambda: int(round(time.time() * 1000))

"""

Construction Parser

"""
p = plyj.parser.Parser()

def getParser():
	global p
	return p





from pycparser1 import parse_file,c_parser, c_ast, c_generator
import ConfigParser
import regex


def is_empty(any_structure):
    if any_structure:
        return False
    else:
        return True




def is_number(s):
    if s=='j':
    	return False
    try:
        float(s) # for int, long and float
    except ValueError:
        try:
            complex(s) # for complex
        except ValueError:
            return False
    return True

def is_hex(input_string):
        flag=True
        if input_string is None:
            return None
        try:
            flag=int(input_string, 16)
        except ValueError:
            return None
	if flag:
		if '0x' in input_string:
    			return str(int(input_string, 16))
    		else:
    			return None
	else:
    		return None



"""
#Axiom Class
#Plain Python object to store Information about a Axiom
"""
class axiomclass(object):
 	def __init__(self, frame_axioms , output_equations , other_axioms, inputvariable, vfact, constraints, const_var_map, asserts, assumes,variables):
        	self.frame_axioms = frame_axioms
        	self.output_equations = output_equations
        	self.other_axioms = other_axioms
        	self.inputvariable = inputvariable
        	self.vfact = vfact
        	self.constraints = constraints
        	self.const_var_map = const_var_map
        	self.asserts = asserts
        	self.assumes = assumes
                self.variables = variables
                
        def getFrame_axioms(self):
        	return self.frame_axioms
        def getOutput_equations(self):
        	return self.output_equations
        def getOther_axioms(self):
        	return self.other_axioms
        def getInputvariable(self):
        	return self.inputvariable
        def getVfact(self):
        	return self.vfact
        def getConstraints(self):
        	return self.constraints
        def getConst_var_map(self):
        	return self.const_var_map
        def getAsserts(self):
    	        return self.asserts
    	def setAsserts(self,asserts):
		self.asserts=asserts
    	def getAssumes(self):
        	return self.assumes
    	def getVariables(self):
        	return self.variables
        def setFrame_axioms(self,frame_axioms):
        	self.frame_axioms=frame_axioms
        def setOutput_equations(self,output_equations):
        	self.output_equations=output_equations
        def setOther_axioms(self,other_axioms):
        	self.other_axioms=other_axioms
        def setInputvariable(self,inputvariable):
        	self.inputvariable=inputvariable
        def setVfact(self,vfact):
        	self.vfact=vfact
        def setConstraints(self,constraints):
        	self.constraints=constraints
        def setConst_var_map(self,const_var_map):
        	self.const_var_map=const_var_map
        def setAsserts(self,asserts):
    	        self.asserts=asserts
    	def setAssumes(self,assumes):
        	self.assumes=assumes
    	def setVariables(self,variables):
        	self.variables=variables

"""
#Sort Class
#Plain Python object to store Information about a Java  Class 
"""
class sortclass(object):
 	def __init__(self, sortname , varmap):
        	self.sortname = sortname
        	self.varmap = varmap
        def getSortname(self):
        	return self.sortname
        def getVarmap(self):
        	return self.varmap
        
        
"""

#Member Method Class
#Plain Python object to store Information about Member Method of a Java Class 
"""
class membermethodclass(object):
 	def __init__(self, methodname, returnType , inputvar, localvar, body, usedCounter, serialNo,tempoary):
        	self.methodname = methodname
        	self.inputvar = inputvar
        	self.returnType = returnType
        	self.localvar = localvar
        	self.body = body
        	self.usedCounter = usedCounter
        	self.serialNo = serialNo
        	self.tempoary = tempoary
        def getMethodname(self):
        	return self.methodname
        def getreturnType(self):
        	return self.returnType
        def getInputvar(self):
        	return self.inputvar
        def getLocalvar(self):
        	return self.localvar
        def getBody(self):
		return self.body
	def getUsedCounter(self):
		return self.usedCounter
	def getSerialNo(self):
		return self.serialNo
	def getTempoary(self):
		return self.tempoary
	def setInputvar(self, inputvar):
	        self.inputvar=inputvar
	def setLocalvar(self, localvar):
	        self.localvar=localvar
	def setBody(self, body):
		self.body=body
	def setUsedCounter(self, usedCounter):
		self.usedCounter=usedCounter
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setTempoary(self,tempoary):
		self.tempoary=tempoary
"""

#Variable Class 

#Plain Python Object to store information about variable

"""
class variableclass(object):
	def __init__(self, variablename, variableType, modifiers, dimensions, initialvalue, structType):
        	self.variablename = variablename
        	self.variableType = variableType
        	self.modifiers = modifiers
        	self.dimensions = dimensions
        	self.initialvalue = initialvalue
        	self.structType = structType
	def getVariablename(self):
		return self.variablename
	def getVariableType(self):
		return self.variableType
	def getModifiers(self):
		return self.modifiers
	def getDimensions(self):
		return self.dimensions
	def getInitialvalue(self):
		return self.initialvalue
        def setInitialvalue(self,initialvalue):
		self.initialvalue=initialvalue
	def getStructType(self):
		return self.structType
	def setStructType(self,initialvalue):
		self.structType=structType


"""

#Expression Class
#Plain Python object to store Information about Java Expression 
"""
class expressionclass(object):
 	def __init__(self, expression, serialNo, isPrime, degree):
        	self.expression = expression
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpression(self):
        	return self.expression
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpression(self, expression):
		self.expression=expression
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
	def setDegree(self, degree):
		self.degree=degree


"""

#Block Class
#Plain Python object to store Information about Block of Java Expression 
"""
class blockclass(object):
 	def __init__(self, expression, predicate, serialNo ,isPrime ,degree):
        	self.expression = expression
        	self.predicate = predicate
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpression(self):
        	return self.expression
        def getPredicate(self):
        	return self.predicate
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpression(self, expression):
		self.expression=expression
	def setPredicate(self, predicate):
		self.predicate=predicate
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
       	def setDegree(self, degree):
		self.degree=degree


"""

#Block Class
#Plain Python object to store Information about if else Java Loop 
"""
class Ifclass(object):
 	def __init__(self, predicate, expressionif, expressionelse, serialNo ,isPrime ,degree):
        	self.predicate = predicate
        	self.expressionif = expressionif
        	self.expressionelse = expressionelse
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpressionif(self):
        	return self.expressionif
        def getExpressionelse(self):
        	return self.expressionelse
        def getPredicate(self):
        	return self.predicate
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpressionif(self, expressionif):
		self.expressionif=expressionif
	def setExpressionelse(self, expressionelse):
		self.expressionelse=expressionelse
	def setPredicate(self, predicate):
		self.predicate=predicate
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
       	def setDegree(self, degree):
		self.degree=degree


"""

#Struct Class
#Plain Python object to store Information about Struct (C Expression) 
"""
class structclass(object):
 	def __init__(self, name, isTypeDef, variablemap , defName, isPointer):
        	self.name = name
        	self.isTypeDef = isTypeDef
        	self.variablemap = variablemap
        	self.defName = defName
        	self.isPointer = isPointer
        def getName(self):
        	return self.name
        def getIsTypeDef(self):
        	return self.isTypeDef
        def getVariablemap(self):
        	return self.variablemap
        def getDefName(self):
        	return self.defName
        def getIsPointer(self):
        	return self.isPointer
        def setName(self, name):
		self.name=name
	def setIsTypeDef(self, isTypeDef):
		self.isTypeDef=isTypeDef
	def setVariablemap(self, variablemap):
		self.variablemap=variablemap
	def setDefName(self, defName):
		self.defName=defName
       	def setIsPointer(self, isPointer):
		self.isPointer=isPointer






"""

#Variable Class 

#Plain Python Object to store information about variable

"""
class variableclass(object):
	def __init__(self, variablename, variableType, modifiers, dimensions, initialvalue, structType):
        	self.variablename = variablename
        	self.variableType = variableType
        	self.modifiers = modifiers
        	self.dimensions = dimensions
        	self.initialvalue = initialvalue
        	self.structType = structType
	def getVariablename(self):
		return self.variablename
	def getVariableType(self):
		return self.variableType
	def getModifiers(self):
		return self.modifiers
	def getDimensions(self):
		return self.dimensions
	def getInitialvalue(self):
		return self.initialvalue
        def setInitialvalue(self,initialvalue):
		self.initialvalue=initialvalue
	def getStructType(self):
		return self.structType
	def setStructType(self,initialvalue):
		self.structType=structType


"""

#Expression Class
#Plain Python object to store Information about Java Expression 
"""
class expressionclass(object):
 	def __init__(self, expression, serialNo, isPrime, degree):
        	self.expression = expression
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpression(self):
        	return self.expression
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpression(self, expression):
		self.expression=expression
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
	def setDegree(self, degree):
		self.degree=degree


"""

#Block Class
#Plain Python object to store Information about Block of Java Expression 
"""
class blockclass(object):
 	def __init__(self, expression, predicate, serialNo ,isPrime ,degree):
        	self.expression = expression
        	self.predicate = predicate
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpression(self):
        	return self.expression
        def getPredicate(self):
        	return self.predicate
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpression(self, expression):
		self.expression=expression
	def setPredicate(self, predicate):
		self.predicate=predicate
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
       	def setDegree(self, degree):
		self.degree=degree


"""

#Block Class
#Plain Python object to store Information about if else Java Loop 
"""
class Ifclass(object):
 	def __init__(self, predicate, expressionif, expressionelse, serialNo ,isPrime ,degree):
        	self.predicate = predicate
        	self.expressionif = expressionif
        	self.expressionelse = expressionelse
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpressionif(self):
        	return self.expressionif
        def getExpressionelse(self):
        	return self.expressionelse
        def getPredicate(self):
        	return self.predicate
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpressionif(self, expressionif):
		self.expressionif=expressionif
	def setExpressionelse(self, expressionelse):
		self.expressionelse=expressionelse
	def setPredicate(self, predicate):
		self.predicate=predicate
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
       	def setDegree(self, degree):
		self.degree=degree


"""

#Struct Class
#Plain Python object to store Information about Struct (C Expression) 
"""
class structclass(object):
 	def __init__(self, name, isTypeDef, variablemap , defName, isPointer):
        	self.name = name
        	self.isTypeDef = isTypeDef
        	self.variablemap = variablemap
        	self.defName = defName
        	self.isPointer = isPointer
        def getName(self):
        	return self.name
        def getIsTypeDef(self):
        	return self.isTypeDef
        def getVariablemap(self):
        	return self.variablemap
        def getDefName(self):
        	return self.defName
        def getIsPointer(self):
        	return self.isPointer
        def setName(self, name):
		self.name=name
	def setIsTypeDef(self, isTypeDef):
		self.isTypeDef=isTypeDef
	def setVariablemap(self, variablemap):
		self.variablemap=variablemap
	def setDefName(self, defName):
		self.defName=defName
       	def setIsPointer(self, isPointer):
		self.isPointer=isPointer

#c_ast.Assignment(op=statement.operator, lvalue=, rvalue=]

#Java Program 
#Plain Python object to store Information about Java Program 

class javaProgramClass(object):
 	def __init__(self, filename, import_list , classes):
        	self.filename = filename
        	self.import_list = import_list
        	self.classes = classes
        def getFilename(self):
        	return self.filename
        def getImport_list(self):
        	return self.import_list
        def getClasses(self):
        	return self.classes
           
#Java Class 
#Plain Python object to store Information about Java Class 

class javaClass(object):
 	def __init__(self, name, membervariables , membermethods, constructors):
        	self.name = name
        	self.membervariables = membervariables
        	self.membermethods = membermethods
        	self.constructors = constructors
        def getName(self):
        	return self.name
        def getMembervariables(self):
        	return self.membervariables
        def getMembermethods(self):
        	return self.membermethods
        def getConstructors(self):
        	return self.constructors




"""

Organization of AST 

"""
               
def organizeStatementToObject(statements):
	count=0
	degree=0
	expressions=[]
	for statement in statements:
		if type(statement) is m.Assignment:
			count=count+1
			expression=expressionclass(statement, count, True,degree)
			expressions.append(expression)
		elif type(statement) is m.While:
			if type(statement.predicate) is m.Unary:
				if type(statement.predicate.expression) is m.ConditionalOr:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
				elif type(statement.predicate.expression) is m.ConditionalAnd:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
				elif type(statement.predicate.expression) is m.Relational:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
				elif type(statement.predicate.expression) is m.Equality:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
			elif type(statement.predicate) is m.ConditionalAnd:
				blockexpressions=[]
				if statement.body is not None:
					degree=degree+1
					count,blockexpressions=blockToExpressions(statement.body, degree, count)
					degree=degree-1
				block=blockclass( blockexpressions, statement.predicate, count , True, degree)
				expressions.append(block)
			elif type(statement.predicate) is m.ConditionalOr:
				blockexpressions=[]
				if statement.body is not None:
					degree=degree+1
					count,blockexpressions=blockToExpressions(statement.body, degree, count)
					degree=degree-1
				block=blockclass( blockexpressions, statement.predicate, count , True, degree)
				expressions.append(block)
			elif type(statement.predicate) is m.Relational:
				blockexpressions=[]
				if statement.body is not None:
					degree=degree+1
					count,blockexpressions=blockToExpressions(statement.body, degree, count)
					degree=degree-1
				block=blockclass( blockexpressions, statement.predicate, count , True, degree)
				expressions.append(block)
			elif type(statement.predicate) is m.Equality:
				blockexpressions=[]
				if statement.body is not None:
					degree=degree+1
					count,blockexpressions=blockToExpressions(statement.body, degree, count)
					degree=degree-1
				block=blockclass( blockexpressions, statement.predicate, count , True, degree)
				expressions.append(block)
		else:
			if type(statement) is m.IfThenElse:
				count,ifclass=ifclassCreator(statement, degree, count)
				expressions.append(ifclass)
					
     	return expressions		

"""

#Finding last expression or block inside a block

"""

def primeStatement(expressions):
	previous=None
	if type(expressions) is Ifclass:
		primeStatement(expressions.getExpressionif())
		primeStatement(expressions.getExpressionelse())
		previous=expressions
        else:
         	if expressions is not None:
         		for expression in expressions:
	 			if previous is not None:
	 				previous.setIsPrime(False)
	 			if type(expression) is blockclass:
	 				primeStatement(expression.getExpression())
	 			if type(expression) is Ifclass:
	 				primeStatement(expression.getExpressionif())
	 				if expression.getExpressionelse() is not None:
	 					primeStatement(expression.getExpressionelse())
				previous=expression

"""

Converting code block,while loop ,conditional expression and expression to corresponding Classes

"""

def blockToExpressions(body, degree, count):
	expressions=[]
	if body is not None:
		for statement in body:
			if type(statement) is m.Assignment:
				count=count+1
				expression=expressionclass(statement, count, True,degree)
				expressions.append(expression)
			elif type(statement) is m.While:
				if type(statement.predicate) is m.Relational:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
				elif type(statement.predicate) is m.Equality:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
			else:
				if type(statement) is m.IfThenElse:
					count,ifclass=ifclassCreator(statement, degree, count)
					expressions.append(ifclass)
	return count,expressions



"""

Block of Statement to Array of Statement Compatible to Translator Program 

"""
def programToinductiveDefination(expressions, allvariable):
	programsstart=""
	programsend=""
	statements=""
	for expression in expressions:
		if type(expression) is expressionclass:
			if type(expression.getExpression()) is m.Assignment:
				if type(expression.getExpression().lhs) is m.Name:
					var=expression.getExpression().lhs.value
					if expression.getIsPrime()==False:
						if programsstart=="":
							programsstart="['-1','seq',['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"
							programsend="]"
						else:
							programsstart+=",['-1','seq',['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"
							programsend+="]"
					else:
                                                if programsstart=="":
                                                     programsstart+="['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
                                                else:
                                                    programsstart+=",['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
                                else:
                                	stmt=createArrayList(expression.getExpression().lhs)
                                	#var="'gt"+str(stmt.count(','))+"',["+stmt+"]"
                                	var="'gt"+"',["+stmt+"]"
					if expression.getIsPrime()==False:
						if programsstart=="":
							programsstart="['-1','seq',['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"
							programsend="]"
						else:
							programsstart+=",['-1','seq',['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"
							programsend+="]"
					else:
				                if programsstart=="":
				                        programsstart+="['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
				                else:
				                        programsstart+=",['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend

		elif type(expression) is blockclass:
			predicatestmt="['-1','while',"+predicateCreator(expression.predicate)+","+programToinductiveDefination( expression.getExpression(), allvariable)+"]"
			if expression.getIsPrime()==False:
				if programsstart=="":
					programsstart="['-1','seq',"+predicatestmt
					programsend="]"
				else:
					programsstart+=",['-1','seq',"+predicatestmt
					programsend+="]"
			else:
				programsstart+=","+predicatestmt+programsend
		elif type(expression) is Ifclass:
			condition=predicateCreator(expression.predicate)
			expressionif=None
			expressionelse=None
			predicatestmt=""
			if expression.getExpressionif() is not None:
				expressionif=programToinductiveDefination( expression.getExpressionif(), allvariable)
			if expression.getExpressionelse() is not None:
				if type(expression.getExpressionelse()) is Ifclass:
					#expressionelse=programToinductiveDefination( expression.getExpressionelse().getExpressionif(), allvariable)
					expressionelse=programToinductiveDefinationIfElse( expression.getExpressionelse(), allvariable)
				else:
					expressionelse=programToinductiveDefination( expression.getExpressionelse(), allvariable)
			if expressionif is not None and expressionelse is not None:
                          	predicatestmt="['-1','if2',"+condition+","+expressionif+","+expressionelse+"]"
			elif expressionif is not None and expressionelse is None:
				predicatestmt="['-1','if1',"+condition+","+expressionif+"]"
			if expression.getIsPrime()==False:
				if programsstart=="":
					programsstart="['-1','seq',"+predicatestmt
					programsend="]"
				else:
					programsstart+=",['-1','seq',"+predicatestmt
					programsend+="]"
			else:
				if programsstart=="":
					programsstart=predicatestmt+programsend
				else:
					programsstart+=","+predicatestmt+programsend
	if programsstart[0]==',':
		programsstart=programsstart[1:]	
	return programsstart		


"""

IfElse Block Statement to Array of Statement Compatible to Translator Program 

"""
def programToinductiveDefinationIfElse(expression, allvariable):
	programsstart=""
	programsend=""
	statements=""
	if type(expression) is expressionclass:
		if type(expression.getExpression()) is m.Assignment:
			if type(expression.getExpression().lhs) is m.Name:
				var=expression.getExpression().lhs.value
				if expression.getIsPrime()==False:
					if programsstart=="":
						programsstart="['-1','seq',['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"
						programsend="]"
					else:
						programsstart+=",['-1','seq',['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"
						programsend+="]"
				else:
                                	if programsstart=="":
                                        	programsstart+="['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
                                        else:
                                               	programsstart+=",['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
                        else:
                                stmt=createArrayList(expression.getExpression().lhs)
			        #var="'gt"+str(stmt.count(','))+"',["+stmt+"]"
			        var="'gt"+"',["+stmt+"]"
				if expression.getIsPrime()==False:
					if programsstart=="":
						programsstart="['-1','seq',['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"
						programsend="]"
					else:
						programsstart+=",['-1','seq',['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"
						programsend+="]"
				else:
					if programsstart=="":
						programsstart+="['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
					else:
						programsstart+=",['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend

	elif type(expression) is blockclass:
		predicatestmt="['-1','while',"+predicateCreator(expression.predicate)+","+programToinductiveDefination( expression.getExpression(), allvariable)+"]"
		if expression.getIsPrime()==False:
			if programsstart=="":
				programsstart="['-1','seq',"+predicatestmt
				programsend="]"
			else:
				programsstart+=",['-1','seq',"+predicatestmt
				programsend+="]"
		else:
			if programsstart=="":
				programsstart+=","+predicatestmt+programsend
			
	elif type(expression) is Ifclass:
		condition=predicateCreator(expression.predicate)
		expressionif=None
		expressionelse=None
		predicatestmt=""
		if expression.getExpressionif() is not None:
			expressionif=programToinductiveDefination( expression.getExpressionif(), allvariable)
		if expression.getExpressionelse() is not None:
			if type(expression.getExpressionelse()) is Ifclass:
				#expressionelse=programToinductiveDefination( expression.getExpressionelse().getExpressionif(), allvariable)
				expressionelse=programToinductiveDefinationIfElse( expression.getExpressionelse(), allvariable)
			else:
				expressionelse=programToinductiveDefination( expression.getExpressionelse(), allvariable)
		if expressionif is not None and expressionelse is not None:
                	predicatestmt="['-1','if2',"+condition+","+expressionif+","+expressionelse+"]"
		elif expressionif is not None and expressionelse is None:
			predicatestmt="['-1','if1',"+condition+","+expressionif+"]"
		if expression.getIsPrime()==False:
			if programsstart=="":
				programsstart="['-1','seq',"+predicatestmt
				programsend="]"
			else:
				programsstart+=",['-1','seq',"+predicatestmt
				programsend+="]"
		else:
			if programsstart=="":
				programsstart=predicatestmt+programsend
			else:
				programsstart+=","+predicatestmt+programsend
 	return programsstart
"""

Conditionl Expression of If Loop or While Loop to a Array of Statement Compatible to Translator Program 

"""
    
def predicateCreator(statement):
	expression=""
	if type(statement) is m.Unary:
		if type(statement.expression) is m.Relational:
			if type(statement.expression.lhs) is m.Name:
		    		expression+="['"+getOperatorCmpl(statement.expression.operator)+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
		    	elif type(statement.expression.lhs) is m.Literal:
    				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
    			elif type(statement.expression.lhs) is m.Additive:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
			else:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
		elif type(statement.expression) is m.Equality:
			if type(statement.expression.lhs) is m.Name:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
			elif type(statement.expression.lhs) is m.Literal:
    				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
    			elif type(statement.expression.lhs) is m.Additive:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
			else:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
    		elif type(statement.expression) is m.ConditionalOr:    
			expression+="['and',"+predicateCreatorCmpl(statement.expression.lhs)+","+predicateCreatorCmpl(statement.expression.rhs)+"]"
		elif type(statement.expression) is m.ConditionalAnd:    
	    		expression+="['or',"+predicateCreatorCmpl(statement.expression.lhs)+","+predicateCreatorCmpl(statement.expression.rhs)+"]"
	elif type(statement) is m.Relational:    
    		if type(statement.lhs) is m.Name:
    			expression+="['"+statement.operator+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Literal:
    			expression+="['"+statement.operator+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Additive:
    			expression+="['"+statement.operator+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
    		else:
    			expression+="['"+statement.operator+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
    	elif type(statement) is m.Equality:    
    		if type(statement.lhs) is m.Name:
    			expression+="['"+statement.operator+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Literal:
    			expression+="['"+statement.operator+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Additive:
		    	expression+="['"+statement.operator+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
		else:
    			expression+="['"+statement.operator+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
	elif type(statement) is m.ConditionalOr:    
	    	expression+="['or',"+predicateCreator(statement.lhs)+","+predicateCreator(statement.rhs)+"]"
	elif type(statement) is m.ConditionalAnd:    
	    	expression+="['and',"+predicateCreator(statement.lhs)+","+predicateCreator(statement.rhs)+"]"
	return expression
	


"""

Program Expression to a Array of Statement Compatible to Translator Program 

"""

def expressionCreator(statement):
    expression=""
    if type(statement) is m.Name:
    	if '.length' in statement.value:
    		axm=statement.value.split('.')
    		expression+="expres('length',["+axm[0]+"])"
    	else:
    		expression+="expres('"+statement.value+"')"
    elif type(statement) is m.Literal:
    	expression+="expres('"+statement.value+"')"
    elif type(statement) is m.MethodInvocation:
    	function=""
    	parameter=""
    	for argument in statement.arguments:
    		if parameter=="":
    			parameter=expressionCreator(argument)
    		else:
    			parameter+=","+expressionCreator(argument)
    	if "power"==statement.name:
    		function="['**',"+parameter+"]"
    	else:
		function="['"+statement.name+"',"+parameter+"]"
    	expression+=function
    elif type(statement) is m.Unary:
    	expression+="['-',"+expressionCreator(statement.expression)+"]"
    elif type(statement) is m.ArrayAccess:
    	stmt=createArrayList(statement)
    	#expression+="expres('at"+str(stmt.count(','))+"',["+stmt+"])"
    	expression+="expres('at"+"',["+stmt+"])"
    else:
    	if type(statement.lhs) is m.Name:
    		if '.length' in statement.lhs.value:
    		    	axm=statement.lhs.value.split('.')
    			expression+="expres('length',["+axm[0]+"])"
    		else:
        		expression+="expres('"+statement.operator+"',[expres('"+statement.lhs.value+"')"
    	elif type(statement.lhs) is m.Literal:
    		expression+="expres('"+statement.operator+"',[expres('"+statement.lhs.value+"')"
    	else:
        	if type(statement.lhs) is m.Additive:
            		expression+="expres('"+statement.operator+"',["+expressionCreator(statement.lhs)
        	else :
            		expression+="expres('"+statement.operator+"',["+expressionCreator(statement.lhs)
    	if type(statement.rhs) is m.Name:
        	expression+=",expres('"+statement.rhs.value+"')])"
    	elif type(statement.rhs) is m.Literal:
        	expression+=",expres('"+statement.rhs.value+"')])"
    	elif type(statement.rhs) is m.ArrayAccess:
    		stmt=createArrayList(statement.rhs)
    		#expression+="expres('at"+str(stmt.count(','))+"',["+stmt+"])"
    		expression+="expres('at"+"',["+stmt+"])"
    	else:
        	if type(statement.rhs) is m.Additive:
        		expression+=","+expressionCreator(statement.rhs)+"])"
        	else :
        		expression+=","+expressionCreator(statement.rhs)+"])"
    return expression
    
"""

Construct Array List

"""
def createArrayList(statement):
	if type(statement) is m.ArrayAccess:
		stmt=''
		if type(statement) is m.ArrayAccess:
			stmt=createArrayList(statement.target)
		stmt+=",expres('"+statement.index.value+"')"
		return stmt
	else:
		return "expres('"+statement.value+"')"







"""
 
Program Expression to Collect literal parameters
 
"""
 
def expressionCollectConstant(statement,fun_parameter):
     expression=""
     if type(statement) is m.Name:
     	expression+=statement.value
     elif type(statement) is m.Literal:
     	expression+=statement.value
     elif type(statement) is m.MethodInvocation:
     	function=""
     	parameter=""
     	key=None
     	if "power"==statement.name:
		function="['**',"+parameter+"]"
	else:
		key=statement.name
 		function="['"+statement.name+"',"+parameter+"]"
     	parameterlist=[]
     	for argument in statement.arguments:
     		if parameter=="":
     			parameter=expressionCollectConstant(argument,fun_parameter)
     			if '_n' not in parameter:
     				parameterlist.append(parameter)     				
     		else:
     			parameterstr=expressionCollectConstant(argument,fun_parameter)
     			parameter+=","+expressionCollectConstant(argument,fun_parameter)
     			if '_n' not in parameterstr:
     				parameterlist.append(parameterstr)
     				
     	if key is not None:
     		fun_parameter[key]=parameterlist
     	expression+=function
     elif type(statement) is m.Unary:
     	expression+="['-',"+expressionCollectConstant(statement.expression,fun_parameter)+"]"
     else:
     	if type(statement.lhs) is m.Name:
         	expression+="expres('"+statement.operator+"',[expres('"+statement.lhs.value+"')"
     	elif type(statement.lhs) is m.Literal:
     		expression+="expres('"+statement.operator+"',[expres('"+statement.lhs.value+"')"
     	else:
         	if type(statement.lhs) is m.Additive:
             		expression+="expres('"+statement.operator+"',["+expressionCollectConstant(statement.lhs,fun_parameter)
         	else :
             		expression+="expres('"+statement.operator+"',["+expressionCollectConstant(statement.lhs,fun_parameter)
     	if type(statement.rhs) is m.Name:
         	expression+=",expres('"+statement.rhs.value+"')])"
     	elif type(statement.rhs) is m.Literal:
         	expression+=",expres('"+statement.rhs.value+"')])"
     	else:
         	if type(statement.rhs) is m.Additive:
         		expression+=","+expressionCollectConstant(statement.rhs,fun_parameter)+"])"
         	else :
         		expression+=","+expressionCollectConstant(statement.rhs,fun_parameter)+"])"
     return expression
   


	
"""

Complement of Conditionl Expression of If Loop or While Loop to a Array of Statement Compatible to Translator Program 

"""
    
def predicateCreatorCmpl(statement):
	expression=""
	if type(statement) is m.Unary:
		if type(statement.expression) is m.Relational:
			if type(statement.expression.lhs) is m.Name:
		    		expression+="['"+statement.expression.operator+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
		    	elif type(statement.expression.lhs) is m.Literal:
    				expression+="['"+statement.expression.operator+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
    			elif type(statement.expression.lhs) is m.Additive:
				expression+="['"+statement.expression.operator+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
			else:
				expression+="['"+statement.expression.operator+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
    		if type(statement.expression) is m.Equality:
			if type(statement.expression.lhs) is m.Name:
				expression+="['"+statement.expression.operator+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
			elif type(statement.expression.lhs) is m.Literal:
    				expression+="['"+statement.expression.operator+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
    			elif type(statement.expression.lhs) is m.Additive:
				expression+="['"+statement.expression.operator+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
			else:
				expression+="['"+statement.expression.operator+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
		elif type(statement.expression) is m.ConditionalOr:    
			expression+="['and',"+predicateCreator(statement.expression.lhs)+","+predicateCreator(statement.expression.rhs)+"]"
		elif type(statement.expression) is m.ConditionalAnd:    
	    		expression+="['or',"+predicateCreator(statement.expression.lhs)+","+predicateCreator(statement.expression.rhs)+"]"
	elif type(statement) is m.Relational:    
    		if type(statement.lhs) is m.Name:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Literal:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Additive:
		    	expression+="['"+getOperatorCmpl(statement.operator)+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
		else:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
    	elif type(statement) is m.Equality:    
    		if type(statement.lhs) is m.Name:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Literal:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Additive:
			expression+="['"+getOperatorCmpl(statement.operator)+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
		else:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
    	elif type(statement) is m.ConditionalOr:    
		expression+="['and',"+predicateCreatorCmpl(statement.lhs)+","+predicateCreatorCmpl(statement.rhs)+"]"
	elif type(statement) is m.ConditionalAnd:    
		expression+="['or',"+predicateCreatorCmpl(statement.lhs)+","+predicateCreatorCmpl(statement.rhs)+"]"
	
	return expression



"""

Conditionl Loop to a Array of Statement Compatible to Translator Program 
IfClass Creator

"""

def ifclassCreator(statement, degree, count):
	if type(statement.predicate) is m.Relational:
		predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	elif type(statement.predicate) is m.Equality:
            	predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	elif type(statement.predicate) is m.ConditionalOr:
	        predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	elif type(statement.predicate) is m.ConditionalAnd:
		predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	elif type(statement.predicate) is m.Unary:
		predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	ifclass=Ifclass(predicate, blockexpressions1, blockexpressions2, count ,True ,degree)
	return count,ifclass

"""

Validation of Variables

"""

def validationOfInput(allvariable):
	for variable in allvariable.keys():
		if variable=='S' or variable=='Q' or variable=='N' or variable=='in' or variable=='is':
			return True
	return False



def syntaxTranslate_Java(statements):
	update_statements=[]
   	for statement in statements:
   		if type(statement) is plyj.model.Unary:
   			if statement.sign=='x++':
   				update_statements.append(plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.expression),  rhs=plyj.model.Additive(operator='+',lhs=syntaxTranslateStmt_Java(statement.expression), rhs=plyj.model.Literal(value='1'))))
   			elif statement.sign=='++x':
   				update_statements.append(plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.expression),  rhs=plyj.model.Additive(operator='+',lhs=syntaxTranslateStmt_Java(statement.expression), rhs=plyj.model.Literal(value='1'))))
   			elif statement.sign=='x--':
			   	update_statements.append(plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.expression),  rhs=plyj.model.Additive(operator='-',lhs=syntaxTranslateStmt_Java(statement.expression), rhs=plyj.model.Literal(value='1'))))
			elif statement.sign=='--x':
   				update_statements.append(plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.expression),  rhs=plyj.model.Additive(operator='-',lhs=syntaxTranslateStmt_Java(statement.expression), rhs=plyj.model.Literal(value='1'))))
   			else:
   				update_statements.append(statement)
   		elif type(statement) is plyj.model.Assignment:
   			if statement.operator=='+=':
   				update_statements.append(plyj.model.Assignment(operator='=',lhs=statement.lhs,  rhs=plyj.model.Additive(operator='+',lhs=syntaxTranslateStmt_Java(statement.lhs), rhs=syntaxTranslateStmt_Java(statement.rhs))))
   			elif statement.operator=='-=':
   				update_statements.append(plyj.model.Assignment(operator='=',lhs=statement.lhs,  rhs=plyj.model.Additive(operator='-',lhs=syntaxTranslateStmt_Java(statement.lhs), rhs=syntaxTranslateStmt_Java(statement.rhs))))
   			elif statement.operator=='*=':
			   	update_statements.append(plyj.model.Assignment(operator='=',lhs=statement.lhs,  rhs=plyj.model.Multiplicative(operator='*',lhs=syntaxTranslateStmt_Java(statement.lhs), rhs=syntaxTranslateStmt_Java(statement.rhs))))
			elif statement.operator=='/=':
   				update_statements.append(plyj.model.Assignment(operator='=',lhs=statement.lhs,  rhs=plyj.model.Multiplicative(operator='/',lhs=syntaxTranslateStmt_Java(statement.lhs), rhs=syntaxTranslateStmt_Java(statement.rhs))))
   			else:
   				update_statements.append(syntaxTranslateStmt_Java(statement))					
   		elif type(statement) is plyj.model.For:
   			stmts=[]
   			for stmt in statement.init:
   				update_statements.append(stmt)
   			for stmt in statement.update:
   				stmts.append(stmt)
			for stmt in statement.body.statements:
				stmts.append(stmt)
			stmts=syntaxTranslate_Java(stmts)
			update_statements.append(plyj.model.While(predicate=syntaxTranslateStmt_Java(statement.predicate),body=plyj.model.Block(statements=stmts)))
		elif type(statement) is plyj.model.DoWhile:
   			stmts=syntaxTranslate_Java(statement.body.statements)
   			for stmt in stmts:
   				update_statements.append(stmt)
   			update_statements.append(plyj.model.While(predicate=syntaxTranslateStmt_Java(statement.predicate),body=plyj.model.Block(statements=stmts)))		
   		elif type(statement) is plyj.model.While:
		   	stmts=syntaxTranslate_Java(statement.body.statements)
		   	for stmt in stmts:
		   		update_statements.append(stmt)
   			update_statements.append(plyj.model.While(predicate=syntaxTranslateStmt_Java(statement.predicate),body=plyj.model.Block(statements=stmts)))		
   		elif type(statement) is plyj.model.Switch:
                	update_statements.append(convertToIfElse_Java(statement.switch_cases,statement.expression))
   		elif type(statement) is plyj.model.IfThenElse:
   			update_statements.append(syntaxTranslate_Java_If(statement))
   		else:
   			update_statements.append(syntaxTranslateStmt_Java(statement))
	return  update_statements
  
  
  
def syntaxTranslate_Java_If(statement):
 	stmt_if=None
 	stmt_else=None
        if type(statement.if_true) is plyj.model.Block:
            stmt_if=syntaxTranslate_Java(statement.if_true.statements)
        else:
            new_if_list=[]
            new_if_list.append(statement.if_true)
            stmt_if=syntaxTranslate_Java(new_if_list)
 	
 	if type(statement.if_false) is plyj.model.IfThenElse:
                print statement.if_false
 		stmt_else=syntaxTranslate_Java_If(statement.if_false) 		
 	else:
 		if statement.if_false is not None:
                    if type(statement.if_false) is plyj.model.Block:
                        stmt_else=syntaxTranslate_Java(statement.if_false.statements)
                        stmt_else=plyj.model.Block(statements=stmt_else)
                    else:
                        new_else_list=[]
                        new_else_list.append(statement.if_false)
                        stmt_else=syntaxTranslate_Java(new_else_list)
                        stmt_else=plyj.model.Block(statements=stmt_else)
                        
 	return plyj.model.IfThenElse(predicate=syntaxTranslateStmt_Java(statement.predicate),if_true=plyj.model.Block(statements=stmt_if),if_false=stmt_else)
    
 
 
def syntaxTranslateStmt_Java(statement):
	if type(statement) is plyj.model.Unary:
		if statement.sign=='x++':
	   		return plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.expression),  rhs=plyj.model.Additive(operator='+',lhs=syntaxTranslateStmt_Java(statement.expression), rhs=plyj.model.Literal(value='1')))
	   	elif statement.sign=='++x':
	   		return plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.expression),  rhs=plyj.model.Additive(operator='+',lhs=syntaxTranslateStmt_Java(statement.expression), rhs=plyj.model.Literal(value='1')))
	   	elif statement.sign=='x--':
			return plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.expression),  rhs=plyj.model.Additive(operator='-',lhs=syntaxTranslateStmt_Java(statement.expression), rhs=plyj.model.Literal(value='1')))
		elif statement.sign=='--x':
   			return plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.expression),  rhs=plyj.model.Additive(operator='-',lhs=syntaxTranslateStmt_Java(statement.expression), rhs=plyj.model.Literal(value='1')))
   		else:
   			return statement
	else:
		if type(statement) is plyj.model.Additive:
			return plyj.model.Additive(operator=statement.operator,lhs=syntaxTranslateStmt_Java(statement.lhs),rhs=syntaxTranslateStmt_Java(statement.rhs))
		elif type(statement) is plyj.model.Multiplicative:
			return plyj.model.Multiplicative(operator=statement.operator,lhs=syntaxTranslateStmt_Java(statement.lhs),rhs=syntaxTranslateStmt_Java(statement.rhs))
		elif type(statement) is plyj.model.Relational:
			return plyj.model.Relational(operator=statement.operator,lhs=syntaxTranslateStmt_Java(statement.lhs),rhs=syntaxTranslateStmt_Java(statement.rhs))
		elif type(statement) is plyj.model.Equality:
			return plyj.model.Equality(operator=statement.operator,lhs=syntaxTranslateStmt_Java(statement.lhs),rhs=syntaxTranslateStmt_Java(statement.rhs))
		elif type(statement) is plyj.model.FieldAccess:
			args=[]
			if type(statement.target) is plyj.model.FieldAccess:
				args.appens(syntaxTranslateStmt_Java(statement.target))
				return plyj.model.MethodInvocation(name=statement.name,arguments=args)
			else:
				if statement.target=='this':
					args.append(plyj.model.Name(value='_c1'))
				else:
					args.append(plyj.model.Name(value=statement.target))
				return plyj.model.MethodInvocation(name=statement.name,arguments=args)
		elif type(statement) is plyj.model.Assignment:
			return plyj.model.Assignment(operator='=',lhs=syntaxTranslateStmt_Java(statement.lhs),  rhs=syntaxTranslateStmt_Java(statement.rhs))
		elif type(statement) is plyj.model.ArrayAccess:
			return plyj.model.ArrayAccess(index=syntaxTranslateStmt_Java(statement.index),target=syntaxTranslateStmt_Java(statement.target))
		elif type(statement) is plyj.model.Return:
			return plyj.model.Return(result=syntaxTranslateStmt_Java(statement.result))
		elif type(statement) is plyj.model.MethodInvocation:
			args=[]
                        if statement.target is not None:
                            args.append(statement.target)
			for para in statement.arguments:
				args.append(syntaxTranslateStmt_Java(para))
			function_name=syntaxTranslateStmt_Java(statement.name)
			if function_name=='println':
				return None
			return plyj.model.MethodInvocation(name=function_name,arguments=args,target=None)
		elif type(statement) is plyj.model.Name:
			if '.' in statement.value:
				functions = statement.value.split('.')
				return constructFieldAccess2Function(functions)
			else:
				return statement
		else:
			return statement    
   
  
  
def constructFieldAccess2Function(term_list):
 	if len(term_list[2:])>0:
 		args=[]
 		args.append(constructFieldAccess2Function(term_list[1:]))
 		return plyj.model.MethodInvocation(name=term_list[0],arguments=args)
 	else:
 		args=[]
		args.append(plyj.model.Name(value=term_list[1]))
 		return plyj.model.MethodInvocation(name=term_list[0],arguments=args)
  
  
  


"""

Covert Switch Case to If-Else-If loop

"""


def convertToIfElse_Java(statements,condition):
	if statements is not None and len(statements)>0:
		statement=statements[0]
		stmts=[]
		for stmt in statement.body:
			if type(stmt) is not plyj.model.Break:
				stmts.append(stmt)
		new_condition=None
		for case in statement.cases:
			if case!='default':
				if new_condition is None:
					new_condition=plyj.model.Equality(operator='==',lhs=condition,rhs=case)
				else:
					new_condition=plyj.model.Relational(operator='||',lhs=new_condition,rhs=plyj.model.Equality(operator='==',lhs=condition,rhs=case))
			else:
				new_condition=None
	if len(statements[1:])>0:
		return plyj.model.IfThenElse(predicate=new_condition,if_true=plyj.model.Block(statements=stmts),if_false=convertToIfElse_Java(statements[1:],condition))
	else:
		if new_condition is not None:
			return plyj.model.IfThenElse(predicate=new_condition,if_true=plyj.model.Block(statements=stmts),if_false=None)
		else:
			return plyj.model.Block(statements=stmts)




#Java Basic Data Type

defineDetaillist=[]
 
defineMap={}


java_basic_datatype=['byte','short','int','long','float','double','boolean','char']


#file_name='benchmark/test.java'
#file_name = 'cav_experiment/benchmarks/cbmc-java/'

def translate_Java(file_name):

	program=translate2JavaObject(file_name)

        #parser = GnuCParser()
        #ast = parser.parse(text)  
        #generator = c_generator.CGenerator()

	if program is not None:
		javaclass_list=program.getClasses()
		for classname in javaclass_list:
			class_object=javaclass_list[classname]
			print 'Class Name'
			print class_object.getName()
			if class_object is not None:
				list_membervariables = class_object.getMembervariables() 
				list_membermethods = class_object.getMembermethods()
				list_constructors = class_object.getConstructors()
				print '		Member Variables'
				var_list="{"
				for x in list_membervariables.keys():
					if list_membervariables[x].getDimensions()>0:
						var_list+=' '+x+':array'
					else:
						var_list+=' '+x+':'+list_membervariables[x].getVariableType()
				var_list+='}'
				print '		'+var_list
				counter=0
				
				
				
				for membermethodname in list_membermethods.keys():
					counter=counter+1
					membermethod=list_membermethods[membermethodname]
					statements=programTransformation(c_ast.Compound(block_items=membermethod.getBody()),list_membermethods,membermethodname)
					localvarmap=getVariables(c_ast.Compound(block_items=statements))
					for x in membermethod.getLocalvar():
						if x not in localvarmap.keys():
							localvarmap[x]=membermethod.getLocalvar()[x]
					membermethod.setLocalvar(localvarmap)
					membermethod.setBody(statements)
					print '		Member Method'
					print '		'+membermethod.getMethodname()
					print '		return Type'
					#print membermethod.getreturnType()
					print '		Input Variables'
					var_list="{"
					for x in membermethod.getInputvar():
						if membermethod.getInputvar()[x].getDimensions()>0:
							var_list+=' '+x+':array'
						else:
							var_list+=' '+x+':'+membermethod.getInputvar()[x].getVariableType()
					var_list+='}'
					print '		'+var_list
					print '		Local Variables'
					var_list="{"
					for x in membermethod.getLocalvar():
						if membermethod.getLocalvar()[x].getDimensions()>0:
							var_list+=' '+x+':array'
						else:
							var_list+=' '+x+':'+membermethod.getLocalvar()[x].getVariableType()
					var_list+='}'
					print '		'+var_list
					#allvariable={}
					#for x in membermethod.getInputvar():
					#	allvariable[x]=membermethod.getInputvar()[x]
					#for x in membermethod.getLocalvar():
                                	#	allvariable[x]=membermethod.getLocalvar()[x]
                                	#for x in list_membervariables.keys():
                                	#	allvariable[x]=list_membervariables[x]
                                        #print membermethod.getBody()
                                        #for stmt in membermethod.getBody():
                                        #    print stmt
                                        generator = c_generator.CGenerator()

                                        for program_body in membermethod.getBody():

                                            function_body=c_ast.Compound(block_items=program_body)

                                            #print(generator.visit(function_body))
                                            #print intersect2(list_membervariables.keys(),membermethod.getLocalvar().keys())
                                        
                                 
                                            membermethod=membermethodclass(membermethod.getMethodname(),membermethod.getreturnType(),membermethod.getInputvar(),membermethod.getLocalvar(),function_body,0,counter,None)
 					    program,variablesarray,fname,iputmap,opvariablesarray=translate2IntForm_Java(membermethod.getMethodname(),membermethod.getreturnType(),membermethod.getBody(),membermethod.getInputvar(),membermethod.getLocalvar(),list_membervariables,class_object.getName())
                                            f,o,a,cm,assert_map,assume_map,assert_key_map=translate1(program,variablesarray,1)
				
				
				return_map={}
				for membermethodname in list_membermethods.keys():
					membermethod=list_membermethods[membermethodname]
					if membermethod.getreturnType() in return_map.keys():
						method_list=return_map[membermethod.getMethodname()]
						method_list.append(membermethod.getMethodname())
						return_map[membermethod.getreturnType()]=method_list
					else:
						method_list=[]
						method_list.append(membermethod.getMethodname())
						return_map[membermethod.getreturnType()]=method_list
				
                                for membermethodname in list_membermethods.keys():
                                	membermethod=list_membermethods[membermethodname]
                                	print membermethod.getMethodname()
                                	for x in membermethod.getInputvar():
						variable_type = membermethod.getInputvar()[x].getVariableType()
						if variable_type in return_map.keys():
							print x+'<---------->'+str(return_map[variable_type])
                                	print '---------------------------'




#file_name='test.java'         
#file_name='benchmark/IntStack.java'  
                        
def translate2JavaObject(file_name):
	if not(os.path.exists(file_name)): 
		print "File not exits"
		return
	start_time=current_milli_time()
	p = getParser()
	tree = p.parse_file(file_name)
	javaclass_list={}
	import_list={}
        for type_decl in tree.type_declarations:
            className=type_decl.name
            list_membervariables={}
            list_membermethods={}
            list_constructors={}
            for element in type_decl.body:
                
                if type(element) is plyj.model.FieldDeclaration:
                    if type(element.type) is plyj.model.Type:
                        if type(element.type.name) is plyj.model.Name:
                            variableType=element.type.name.value
                            dimensions=element.type.dimensions
                            variablename=element.variable_declarators[0].variable.name
                            initialvalue=element.variable_declarators[0].initializer
                            modifiers=element.modifiers
			    variable=variableclass(variablename, variableType, modifiers, dimensions, initialvalue,None)
			    list_membervariables[variablename]=variable
                        else:
                            variableType=element.type.name
                            dimensions=element.type.dimensions
                            variablename=element.variable_declarators[0].variable.name
                            initialvalue=element.variable_declarators[0].initializer
                            modifiers=element.modifiers
                            variable=variableclass(variablename, variableType, modifiers, dimensions, initialvalue,None)
                            list_membervariables[variablename]=variable
                    else:
                        variableType=element.type
                        dimensions=0
                        variablename=element.variable_declarators[0].variable.name
                        initialvalue=element.variable_declarators[0].initializer
                        modifiers=element.modifiers
                        variable=variableclass(variablename, variableType, modifiers, dimensions, initialvalue,None)
                        list_membervariables[variablename]=variable
                else:
                    if type(element) is plyj.model.MethodDeclaration:
                        inputvar={}
                        localvar={}
                        usedCounter=0
                    	serialNo=0
                        for para in element.parameters:
                        	variablename=para.variable.name
                        	dimensions=0
                        	initialvalue=None
                        	modifiers=para.modifiers
                        	if type(para.type) is plyj.model.Type:
                        		if type(para.type.name) is plyj.model.Name:
                        			variableType=para.type.name.value
                        		else:
                        			variableType=para.type.name
                        		dimensions=para.type.dimensions
                        	else:
                        		if type(para.type) is plyj.model.Name:
                        			variableType=para.type.value
                        		else:
                        			variableType=para.type
				variable=variableclass(variablename, variableType, modifiers, dimensions, initialvalue, None)
				inputvar[variablename]=variable
                        methodname=element.name
                        methodmodifiers=element.modifiers
                        returnType=element.return_type
			body=syntaxTranslate_Java(element.body)
                        getLocalVaribales(body,localvar)
                        body=translateSyntaxJ2CBlock(body)
     			memberclass=membermethodclass(methodname, returnType , inputvar, localvar, body, usedCounter, serialNo, None)
			list_membermethods[methodname+str(len(inputvar.keys()))]=memberclass
                    elif type(element) is plyj.model.ConstructorDeclaration:
                    	inputvar={}
                    	localvar={}
                    	usedCounter=0
                    	serialNo=0
                    	for para in element.parameters:
				variablename=para.variable.name
			        dimensions=0
			        initialvalue=None
			        modifiers=para.modifiers
			        if type(para.type) is plyj.model.Type:
			        	if type(para.type.name) is plyj.model.Name:
			                	variableType=para.type.name.value
			                else:
			                        variableType=para.type.name
			                dimensions=para.type.dimensions
			        else:
			                if type(para.type) is plyj.model.Name:
			                	variableType=para.type.value
			                else:
			                	variableType=para.type
				variable=variableclass(variablename, variableType, modifiers, dimensions, initialvalue,None)
				inputvar[variablename]=variable
                    	methodname=element.name
                    	returnType=None
                    	body=syntaxTranslate_Java(element.block)
                    	memberclass=membermethodclass(methodname, returnType , inputvar, localvar, body, usedCounter, serialNo,None)
 			list_constructors[methodname+str(len(inputvar.keys()))]=memberclass
 		javaclass=javaClass(className, list_membervariables , list_membermethods, list_constructors)
 		javaclass_list[className]=javaclass
 	program=javaProgramClass(file_name, import_list , javaclass_list)   
 	return program


#Get Local Variables 

def getLocalVaribales(statements,localvariables):
        update_statements=[]
	for element in statements:
		if type(element) is plyj.model.VariableDeclaration:
                    if type(element.type) is plyj.model.Type:
                        if type(element.type.name) is plyj.model.Name:
                            variableType=element.type.name.value
                            dimensions=element.type.dimensions
                            variablename=element.variable_declarators[0].variable.name
                            initialvalue=element.variable_declarators[0].initializer
                            modifiers=element.modifiers
			    variable=variableclass(variablename, variableType, modifiers, dimensions, initialvalue)
			    localvariables[variablename]=variable
                            if initialvalue is not None:
                                update_statements.append(element)
                                update_statements.append(plyj.model.Assignment(operator='=',lhs=element.variable_declarators[0].variable,  rhs=initialvalue))
                            else:
                                update_statements.append(element)
                        else:
                            variableType=element.type.name
                            dimensions=element.type.dimensions
                            variablename=element.variable_declarators[0].variable.name
                            initialvalue=element.variable_declarators[0].initializer
                            modifiers=element.modifiers
                            variable=variableclass(variablename, variableType, modifiers, dimensions, initialvalue)
                            localvariables[variablename]=variable
                            if initialvalue is not None:
                                update_statements.append(element)
                                update_statements.append(plyj.model.Assignment(operator='=',lhs=element.variable_declarators[0].variable,  rhs=initialvalue))
                            else:
                                update_statements.append(element)
                    else:
                        variableType=element.type
                        dimensions=0
                        variablename=element.variable_declarators[0].variable.name
                        initialvalue=element.variable_declarators[0].initializer
                        modifiers=element.modifiers
                        variable=variableclass(variablename, variableType, modifiers, dimensions, initialvalue, None)
                        localvariables[variablename]=variable
                        if initialvalue is not None:
                            update_statements.append(element)
                            update_statements.append(plyj.model.Assignment(operator='=',lhs=element.variable_declarators[0].variable,  rhs=initialvalue))
                        else:
                            update_statements.append(element)
                elif type(element) is plyj.model.While:
                        update_statements.append(plyj.model.While(predicate=element.predicate,body=plyj.model.Block(statements=getLocalVaribales(element.body.statements,localvariables))))
                elif type(element) is plyj.model.IfThenElse:
                        update_statements.append(getLocalVaribales_If(element,localvariables))
                else:
                        update_statements.append(element)
        return update_statements




def getLocalVaribales_If(statement,localvariables):
 	stmt_if=None
 	stmt_else=None
 	stmt_if=getLocalVaribales(statement.if_true.statements,localvariables)
 	if type(statement.if_false) is plyj.model.IfThenElse:
 		stmt_else=getLocalVaribales_If(statement.if_false,localvariables) 		
 	else:
 		if statement.if_false is not None:
                    stmt_else=getLocalVaribales(statement.if_false.statements,localvariables)
                    stmt_else=plyj.model.Block(statements=stmt_else)
 	return plyj.model.IfThenElse(predicate=statement.predicate,if_true=plyj.model.Block(statements=stmt_if),if_false=stmt_else)


def translateSyntaxJ2CBlock(statements):
	update_statements=[]
	for statement in statements:
            if type(statement) is plyj.model.While:
		update_statements.append(c_ast.While(cond=stmtTranslateJ2C(statement.predicate), stmt=c_ast.Compound(block_items=translateSyntaxJ2CBlock(statement.body.statements))))
            elif type(statement) is plyj.model.IfThenElse:
                update_statements.append(translateSyntaxJ2CBlock_If(statement))
            else:
                if type(statement) is not plyj.model.VariableDeclaration:
                	update_statements.append(stmtTranslateJ2C(statement))
                else:
			if statement.variable_declarators[0].initializer is not None:
                                if type(statement.variable_declarators[0].initializer) is plyj.model.InstanceCreation:
                                    if type(statement.variable_declarators[0].initializer.type) is plyj.model.Type:
                                        print '############'
                                        print statement.variable_declarators[0].initializer.type.name.value
                                        statement.variable_declarators[0].initializer= plyj.model.Name(value='NOTNULL')
                                        print statement.variable_declarators[0].initializer
                                        print '############'
				update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=statement.variable_declarators[0].variable.name), rvalue=stmtTranslateJ2C(syntaxTranslateStmt_Java(statement.variable_declarators[0].initializer))))
        return update_statements
    
    
def translateSyntaxJ2CBlock_If(statement):
 	stmt_if=None
 	stmt_else=None
 	stmt_if=translateSyntaxJ2CBlock(statement.if_true.statements)
 	if type(statement.if_false) is plyj.model.IfThenElse:
 		stmt_else=translateSyntaxJ2CBlock_If(statement.if_false) 		
 	else:
 		if statement.if_false is not None:
                    stmt_else=translateSyntaxJ2CBlock(statement.if_false.statements)
                    stmt_else=c_ast.Compound(block_items=stmt_else) 
        return c_ast.If(cond=stmtTranslateJ2C(statement.predicate), iftrue=c_ast.Compound(block_items=stmt_if) ,iffalse=stmt_else)

    
    
			
def stmtTranslateJ2C(statement):
	if type(statement) is plyj.model.Assignment:
		return c_ast.Assignment(op=statement.operator, lvalue=stmtTranslateJ2C(statement.lhs), rvalue=stmtTranslateJ2C(statement.rhs))
	elif type(statement) is plyj.model.Unary:
		return c_ast.UnaryOp(op=statement.operator, expr=stmtTranslateJ2C(statement.expression))
	elif type(statement) is plyj.model.Additive:
		return c_ast.BinaryOp(op=statement.operator, left=stmtTranslateJ2C(statement.lhs), right=stmtTranslateJ2C(statement.rhs))
	elif type(statement) is plyj.model.Multiplicative:
		return c_ast.BinaryOp(op=statement.operator, left=stmtTranslateJ2C(statement.lhs), right=stmtTranslateJ2C(statement.rhs))
	elif type(statement) is plyj.model.Relational:
		return c_ast.BinaryOp(op=statement.operator, left=stmtTranslateJ2C(statement.lhs), right=stmtTranslateJ2C(statement.rhs))
	elif type(statement) is plyj.model.Equality:
		return c_ast.BinaryOp(op=statement.operator, left=stmtTranslateJ2C(statement.lhs), right=stmtTranslateJ2C(statement.rhs))
	elif type(statement) is plyj.model.Literal:
		return c_ast.Constant(type='int', value=statement.value)
	elif type(statement) is plyj.model.Name:
		return c_ast.ID(name=statement.value)
	elif type(statement) is plyj.model.Break:
		return c_ast.Break()
	elif type(statement) is plyj.model.Continue:
		return c_ast.Continue()
	elif type(statement) is plyj.model.ArrayAccess:
                return constructArrayC2Java(statement)
        elif type(statement) is plyj.model.Return:
        	return c_ast.Return(expr=stmtTranslateJ2C(statement.result))
        elif type(statement) is plyj.model.MethodInvocation:
                return creatFunctionCall(statement.name,statement.arguments)
       
        	

            

def constructArrayC2Java(statement):
    if type(statement) is plyj.model.ArrayAccess:
        if type(statement.target) is plyj.model.ArrayAccess:
            return c_ast.ArrayRef(name=constructArrayC2Java(statement.target), subscript=stmtTranslateJ2C(statement.index))
        else:
            return c_ast.ArrayRef(name=stmtTranslateJ2C(statement.target), subscript=stmtTranslateJ2C(statement.index))
        
        
#name='fun'
#parameterlist=['X','Y']
	
def creatFunctionCall(name,parameterlist):
    str_parameterlist=None
    generator = c_generator.CGenerator()
    for para in parameterlist:
        if str_parameterlist==None:
            str_parameterlist=generator.visit(stmtTranslateJ2C(para))
        else:
            str_parameterlist+=','+generator.visit(stmtTranslateJ2C(para))
    if str_parameterlist is not None:
        function=name+'('+str_parameterlist+')'
    else:
        function=name+'()'
    main_function='void main(){'+function+';}'
    parser = c_parser.CParser()
    ast = parser.parse(main_function)
    return ast.ext[0].body.block_items[0]



        	




def programTransformation(function_body,functionMap,medthodname):

    generator = c_generator.CGenerator()   
   
    global break_count
    global continue_count
    global new_variable
    global dummyCount
    global count__VERIFIER_nondet
    
    new_variable={}
        
    #Handling Pointer
    
    #print '#######'
    #print(generator.visit(function_body))
    #print '#######'
    
    
    #statements= handlingPointer(function_body.block_items)
    
    #function_body.show()
    
    statements=function_body.block_items
        
    #Syntax translation of the function body
    
#print '#######1'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######1'
        
    statements=syntaxTranslate(statements)

    #print '#######1'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######1'

    statements=arrangeEmptyStatement(statements)
    #print '#######11'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######11'
   
    #Convert Initiation to assignments   
    
    statements=construct_program(statements)
    
    
    #print '#######2'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######2'

    #print(generator.visit(c_ast.Compound(block_items=statements)))
    
    #Reconstruct Program by Removing assert,assume,error
    
    statements=reconstructPreDefinedFun(statements)
    
    pa_update_statements=copy.deepcopy(statements)
    
    pa_update_statements=removeEmptyIfLoop(pa_update_statements)
    
    pa_update_statements=change_var_name(pa_update_statements)
    
    #print '#######2'
    #print(generator.visit(c_ast.Compound(block_items=pa_update_statements)))
    #print '#######2' 
    
    
    #pa_update_statements = organizeDeclaration(pa_update_statements)
    
    #pa_update_statements = getVariablesInit(pa_update_statements)
    
    
    
    
    
    #print '#######3'
    #print(generator.visit(c_ast.Compound(block_items=pa_update_statements)))
    #print '#######3'
    
    #print '#######3'
    #print(generator.visit(c_ast.Compound(block_items=pa_update_statements)))
    #print '#######3'
        
    #Replace return by goto statement
        
    statements=remove_return(statements,functionMap[medthodname])
    
    #print '#######4'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######4'
    
        
    #Replace goto structured statement
        
    statements=gotoremoval(statements)
    
    #print '#######5'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######5'
        
    update_statements=[]
        
    #Add new variable
        
    for var in new_variable.keys():
    	if isBoolVariable( var )==True:
    	    	#temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['_Bool'])), init=c_ast.Constant(type='_Bool', value=None), bitsize=None)
                temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
    		update_statements.append(temp)
    	else:
    		temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
    		update_statements.append(temp)
        	
    for statement in statements:
    	update_statements.append(statement)
        	
    #print '#######5'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######5' 
      
      
    #Remove Empty If Loops  
    
    update_statements=removeEmptyIfLoop(update_statements)
        
    #Remove Dead Code
    
    #print '#######6'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######6'
    
    
    update_statements=removeDeadCode(update_statements)
    
    
    #print '#######7'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######7'
        
    #Simplify Conditions
        
    statements=simplifyProgram(update_statements)
    
    
    #print '#######8'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######8'
    
    #Add Break Removal Modules
    
    
    break_map={}
    break_count=0
    continue_count=0
    
    statements=getBreakStmt(statements,break_map)
    
    #print '#######9'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######9'
    
    
    statements=changeConditionProgram(statements)
    
    
    #print '#######10'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######10'
    
        
    update_statements=[]
    
    for var in new_variable.keys():
    	if isBoolVariable( var )==True:
    	    	#temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['_Bool'])), init=c_ast.Constant(type='_Bool', value=None), bitsize=None)
                temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
       		update_statements.append(temp)
    	else:
    		temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
       		update_statements.append(temp)
        	
    for statement in statements:
    	update_statements.append(statement)
    
    dummyCount=0
    
    #print '#######10'
    #print(generator.visit(c_ast.Compound(block_items=update_statements)))
    #print '#######10'
    
    
    statements=functionToAssignment(update_statements,functionMap)
    
    
    
    
    #print '#######11'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######11'
       
    update_statements=[]
    
    if dummyCount>0:
    	for x in range(0, dummyCount):
    		temp=c_ast.Decl(name='_'+str(x+1)+'DUMMY', quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname='_'+str(x+1)+'DUMMY', quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
       		update_statements.append(temp)
    for statement in statements:
    	update_statements.append(statement)
        
    #count__VERIFIER_nondet=0
    
    #print 'xxxxx1'
    
    update_statements=getVariablesInit(update_statements)
    
    #print 'xxxxx2'
    
    update_statements=change_var_name(update_statements)
    
    #print 'xxxxx3'

    return update_statements,pa_update_statements



"""

Syntax translation module

"""



def syntaxTranslate(statements):
        update_statements=[]
        for statement in statements:
                if type(statement) is c_ast.UnaryOp:
                        
                        if statement.op=='++' or statement.op=='p++':
                                update_statements.append(c_ast.Assignment(op='=',lvalue=statement.expr, rvalue=c_ast.BinaryOp(op='+',left=statement.expr, right=c_ast.Constant('int','1'))))
                        elif statement.op=='--' or statement.op=='p--':
                                update_statements.append(c_ast.Assignment(op='=',lvalue=statement.expr, rvalue=c_ast.BinaryOp(op='-',left=statement.expr, right=c_ast.Constant('int','1'))))
                        else:
                                update_statements.append(statement)
                elif type(statement) is c_ast.For:
                        if type(statement.init) is c_ast.DeclList:
                            for stmt in statement.init.decls:
                                update_statements.append(stmt)
                        else:
                            update_statements.append(statement.init)
                        if type(statement.stmt) is c_ast.Compound:
                        	new_block_items=statement.stmt.block_items
                        	if new_block_items is None:
                                    new_block_items=[]
                        	new_block_items.append(statement.next)
                        	new_block_items=syntaxTranslate(new_block_items)
                        	new_stmt=c_ast.Compound(block_items=new_block_items)
                        	update_while=c_ast.While(statement.cond,new_stmt)
                        	update_statements.append(update_while)
                        else:
                        	new_block_items=[]
                        	new_block_items.append(statement.stmt)
                        	new_block_items.append(statement.next)
				new_block_items=syntaxTranslate(new_block_items)
				new_stmt=c_ast.Compound(block_items=new_block_items)
				update_while=c_ast.While(statement.cond,new_stmt)
                        	update_statements.append(update_while)
                elif type(statement) is c_ast.DoWhile:
                	if type(statement.stmt) is c_ast.Compound:
		        	new_block_items=statement.stmt.block_items
		        	if new_block_items is None:
                                    new_block_items=[]
		        	for item in new_block_items:
		        		update_statements.append(item)
		        	new_block_items=syntaxTranslate(new_block_items)
		        	new_stmt=c_ast.Compound(block_items=new_block_items)
		        	update_while=c_ast.While(statement.cond,new_stmt)
                        	update_statements.append(update_while)
                        else:
                        	new_block_items=[]
                        	new_block_items.append(statement.stmt)
                        	for item in new_block_items:
					update_statements.append(item)
				new_block_items=syntaxTranslate(new_block_items)
				new_stmt=c_ast.Compound(block_items=new_block_items)
				update_while=c_ast.While(statement.cond,new_stmt)
                        	update_statements.append(update_while)
                elif type(statement) is c_ast.Switch:
                	stmts=statement.stmt.block_items
                	statement=convertToIfElse(stmts,statement.cond)
                	#update_statements.append(statement)
                        update_statements.append(syntaxTranslateIf(statement))
                elif type(statement) is c_ast.While:
                	if type(statement.stmt) is c_ast.Compound:
                		update_statements.append(c_ast.While(cond=syntaxTranslateStmt(statement.cond),stmt=c_ast.Compound(block_items=syntaxTranslate(statement.stmt.block_items))))
                	else:
                		new_block_items=[]
				new_block_items.append(statement.stmt)
				update_statements.append(c_ast.While(cond=syntaxTranslateStmt(statement.cond),stmt=c_ast.Compound(block_items=syntaxTranslate(new_block_items))))
                elif type(statement) is c_ast.If:
                	update_statements.append(syntaxTranslateIf(statement))
                elif type(statement) is c_ast.Assignment:
                	if statement.op=='+=':
                		if type(statement.lvalue) is c_ast.ID:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='+', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                		else:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='+', left=statement.lvalue, right=statement.rvalue)))
                	elif statement.op=='-=':
                		if type(statement.lvalue) is c_ast.ID:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='-', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                		else:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='-', left=statement.lvalue.name, right=statement.rvalue)))
                	elif statement.op=='/=':
                		if type(statement.lvalue) is c_ast.ID:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='/', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                		else:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='/', left=statement.lvalue, right=statement.rvalue)))
                	elif statement.op=='%=':
                		if type(statement.lvalue) is c_ast.ID:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='%', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                		else:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='%', left=statement.lvalue, right=statement.rvalue)))
                	elif statement.op=='*=':
                		if type(statement.lvalue) is c_ast.ID:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='*', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                		else:
                			update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='*', left=statement.lvalue, right=statement.rvalue)))
                	
                	else:
                		if type(statement.rvalue) is c_ast.Assignment:
                			stmts=[]
                			separateAllAssignment(statement,stmts)
                			for stmt in stmts:
                				update_statements.append(stmt)
                		else:
                			if type(statement.lvalue) is c_ast.ID and type(statement.rvalue) is c_ast.TernaryOp:
                                            
                                            update_statements.append(syntaxTranslateStmtTernaryOp(statement))
                                            
                                        else:
                                            update_statements.append(c_ast.Assignment(op=statement.op, lvalue=statement.lvalue, rvalue=statement.rvalue))
                
                elif type(statement) is c_ast.ExprList:
                    statement=syntaxTranslate(statement.exprs)
                    for exp_stmt in statement:
                         update_statements.append(exp_stmt)
                elif type(statement) is c_ast.Label:
			update_statements.append(c_ast.Label(name=statement.name, stmt=None))
			if type(statement.stmt) is c_ast.Compound:
				new_block_items=syntaxTranslate(statement.stmt.block_items)
				for item in new_block_items:
					update_statements.append(item)	
			else:
				if statement.stmt is not None:
					new_block_items=[]
					new_block_items.append(statement.stmt)
					new_block_items=syntaxTranslate(new_block_items)
					for item in new_block_items:
						update_statements.append(item)

                elif type(statement) is c_ast.Compound:
                	new_stmts=syntaxTranslate(statement.block_items)
                	for stmt in new_stmts:
                		update_statements.append(stmt)
                	
                else:
                        if type(statement) is not c_ast.EmptyStatement:
                        	update_statements.append(statement)
        return update_statements



def syntaxTranslateIf(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=syntaxTranslate(statement.iftrue.block_items))
			else:
				new_iftrue=c_ast.Compound(block_items=[])
		else:
			if type(statement.iftrue) is c_ast.UnaryOp:
				new_iftrue=syntaxTranslateStmt(statement.iftrue)
			elif type(statement.iftrue) is c_ast.BinaryOp:
				new_iftrue=syntaxTranslateStmt(statement.iftrue)
			else:
				new_blocks=[]
				new_blocks.append(statement.iftrue)
				new_iftrue=c_ast.Compound(block_items=syntaxTranslate(new_blocks))
				
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=syntaxTranslate(statement.iffalse.block_items))
			else:
				new_iffalse=c_ast.Compound(block_items=[])
		else:
			if type(statement.iffalse) is c_ast.If:
				new_iffalse=syntaxTranslateIf(statement.iffalse)
			else:
				if type(statement.iffalse) is c_ast.UnaryOp:
					new_iffalse=syntaxTranslateStmt(statement.iffalse)
				elif type(statement.iffalse) is c_ast.BinaryOp:
					new_iffalse=syntaxTranslateStmt(statement.iffalse)
				else:
					new_blocks=[]
					new_blocks.append(statement.iffalse)
					new_iffalse=c_ast.Compound(block_items=syntaxTranslate(new_blocks))
	return c_ast.If(cond=syntaxTranslateStmt(statement.cond), iftrue=new_iftrue, iffalse=new_iffalse)


#
# Change Assignment statement to a list of Assignment statements
#


def separateAllAssignment(statement,stmts):
	if type(statement) is c_ast.Assignment:
		if type(statement.rvalue) is c_ast.Assignment:
			value=separateAllAssignment(statement.rvalue,stmts)
			stmts.append(c_ast.Assignment(op=statement.op, lvalue=statement.lvalue, rvalue=value))
			return value
		else:
			stmts.append(c_ast.Assignment(op=statement.op, lvalue=statement.lvalue, rvalue=statement.rvalue))
			return statement.rvalue
	return None
	

"""

Covert Switch Case to If-Else-If loop

"""



def convertToIfElse(statements,condition):
	if statements is not None and len(statements)>0:
		statement=statements[0]
		if type(statement) is not c_ast.Default:
			new_condition_left=constructCondition(statements,condition)
			new_condition_right,new_block_items,statements,is_break=constructBody(statements,condition)
			new_compund_left=c_ast.Compound(block_items=new_block_items)
			
			if new_condition_left is not None:
				new_Else_stmt=convertToIfElse(statements,condition)
				new_If_stmt=c_ast.If(cond=c_ast.BinaryOp(op='||', left=new_condition_left, right=new_condition_right),iftrue=new_compund_left,iffalse=new_Else_stmt)
				return new_If_stmt
			else:
				new_Else_stmt=convertToIfElse(statements,condition)
				new_If_stmt=c_ast.If(cond=new_condition_right,iftrue=new_compund_left,iffalse=new_Else_stmt)
				return new_If_stmt
		else:
			update_stmts=[]
			for stmt in statement.stmts:
				#if type(stmt) is not c_ast.Break:
                                update_stmts.append(stmt)
			return c_ast.Compound(block_items=update_stmts)
		

	return None


def syntaxTranslateStmt(statement):
	if type(statement) is c_ast.UnaryOp:
		if statement.op=='++' or statement.op=='p++':
	        	return c_ast.Assignment(op='=',lvalue=statement.expr, rvalue=c_ast.BinaryOp(op='+',left=statement.expr, right=c_ast.Constant('int','1')))
		elif statement.op=='--' or statement.op=='p--':
	        	return c_ast.Assignment(op='=',lvalue=statement.expr, rvalue=c_ast.BinaryOp(op='-',left=statement.expr, right=c_ast.Constant('int','1')))
	        else:
                        return statement
	else:
		if type(statement) is c_ast.BinaryOp:
			return c_ast.BinaryOp(op=statement.op,left=syntaxTranslateStmt(statement.left),right=syntaxTranslateStmt(statement.right))
		else:
			return statement



def syntaxTranslateStmtTernaryOp(statement):
    new_blocks_true=[]
    
    new_blocks_true.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=statement.rvalue.iftrue))
    new_iftrue=c_ast.Compound(block_items=syntaxTranslate(new_blocks_true))
                        
    new_blocks_false=[]
    
    new_blocks_false.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=statement.rvalue.iffalse))
    new_iffalse=c_ast.Compound(block_items=syntaxTranslate(new_blocks_false))
                        
    return c_ast.If(cond=statement.rvalue.cond,iftrue=new_iftrue,iffalse=new_iffalse)




"""

Covert Switch Case to If-Else-If loop

"""

	
def constructCondition(statements,condition):
	if statements is not None and len(statements)>0:
		statement=statements[0]
		if type(statement) is not c_ast.Default:
			if len(statement.stmts)==0:
				new_condition_left=c_ast.BinaryOp(op='==', left=condition, right=statement.expr)
				new_condition_right=constructCondition(statements[1:],condition)
				if new_condition_right is None:
					return new_condition_left
				else:
					return c_ast.BinaryOp(op='||', left=new_condition_left, right=new_condition_right)
			else:
				return None
		else:
			return None
	return None


"""

Covert Switch Case to If-Else-If loop

"""


def constructBody(statements,condition):
	if statements is not None and len(statements)>0:
		statement=statements[0]
		if type(statement) is not c_ast.Default:
			if len(statement.stmts)>0:
				update_stmts=[]
				new_condition=c_ast.BinaryOp(op='==', left=condition, right=statement.expr)
				is_break=False
				for stmt in statement.stmts:
					if type(stmt) is c_ast.Break:
						is_break=True;
					else:
						update_stmts.append(stmt)
				return new_condition,update_stmts,statements[1:],is_break
			else:
				return constructBody(statements[1:],condition)
		else:
			return None,None,None,False
	return None,None,None,False


def arrangeEmptyStatement(statements):
    update_statements=[]
    for statement in statements:
        if type(statement) is c_ast.If:
            stmt=arrangeEmptyStatementIf(statement)
            if stmt is not None:
            	update_statements.append(stmt)
        elif type(statement) is c_ast.While:
            if type(statement.stmt) is c_ast.EmptyStatement:
                update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=[])))
            elif statement.stmt.block_items is not None:
            	stmt=arrangeEmptyStatement(statement.stmt.block_items)
            	if stmt is not None:
                	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=stmt)))
                else:
                	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=[])))
            else:
                update_statements.append(statement)
        else:
            update_statements.append(statement)
    return update_statements
           

    


def arrangeEmptyStatementIf(statement):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.EmptyStatement:
            if type(statement.iffalse) is c_ast.Compound:
                return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=statement.iffalse, iffalse=None)
            else:
                return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=statement.iffalse, iffalse=None)
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=arrangeEmptyStatement(statement.iftrue.block_items)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
            
        if type(statement.iffalse) is c_ast.Compound:
            if statement.iffalse.block_items is not None:
                new_block_items=arrangeEmptyStatement(statement.iffalse.block_items)
                new_iffalse=c_ast.Compound(block_items=new_block_items)
            else:
                new_iffalse=statement.iffalse
        elif type(statement.iffalse) is c_ast.If:
            new_iffalse=arrangeEmptyStatementIf(statement.iffalse)
        else:
            new_iffalse=statement.iffalse
            
    if new_iftrue is not None and new_iffalse is None:
        return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
    elif new_iftrue is not None and new_iffalse is not None:
        return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
    elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
	return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
    elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
	return new_iffalse
    else:
	return None



#
#Convert Initiation to assignments   
#

def construct_program(statements):
    update_statements=[]
    for statement in statements:
    	if type(statement) is c_ast.Decl:
    		if type(statement.type) is c_ast.ArrayDecl:
                        if statement.init is not None:
                        	program=''                        	
			        d_list=[]
			        a_list=[]
			        
			        if statement.type.dim is None:
			        	d_list_update,a_list_update=getDimesnion4Init(statement.init)
			        	for x1 in d_list_update:
			        		d_list.append('initial_value'+x1)
			        	for x1 in a_list_update:
			        		a_list.append(x1)
			        else:
			        	for x in range(0, int(statement.type.dim.value)):
			        		d_list.append('initial_value.exprs['+str(x)+']')
			                	a_list.append('['+str(x)+']') 
			        	d_list,a_list=getDimesnion(statement.type,d_list,a_list)
                        	initial_value=statement.init
                        	for x1 in range(0, len(d_list)):
                                        stmt_value=eval(d_list[x1])
                                        if type(stmt_value) is c_ast.Constant:
                                            program=program+statement.name+a_list[x1]+'='+str(eval(d_list[x1]+'.value'))+';'
                                        else:
                                            if type(stmt_value) is c_ast.UnaryOp: 
                                                program=program+statement.name+a_list[x1]+'= '+stmt_value.op+str(eval(d_list[x1]+'.expr.value'))+';'
                        	
                        	program='int main{'+program+'}'
                        	parser = c_parser.CParser()
                        	ast1 = parser.parse(program)
                        	function_body = ast1.ext[0].body                        	
                        	statement.init=None
                        	update_statements.append(statement)
                        	for new_statement in function_body.block_items:
                        		update_statements.append(new_statement)
                        else:
                        	update_statements.append(statement)
                        
                else:
                	update_statements.append(statement)
        else:
        	update_statements.append(statement)
    return update_statements


def getDimesnion(statement,d_list,a_list):
    if type(statement.type) is c_ast.ArrayDecl:
        d_list_update=[]
        a_list_update=[]
        for x1 in range(0, len(d_list)):
            for x2 in range(0, int(statement.type.dim.value)):
                d_list_update.append(d_list[x1]+'.exprs['+str(x2)+']')
                a_list_update.append(a_list[x1]+'['+str(x2)+']')
        return getDimesnion(statement.type,d_list_update,a_list_update)
    else:
        return d_list,a_list
        

def getDimesnion4Init(statement):
	d_list_update=[]
       	a_list_update=[]
	if type(statement) is c_ast.InitList:
		count=0
		for x in statement.exprs:
			if type(x) is c_ast.InitList:
				new_d_list_update,new_a_list_update=getDimesnion4Init(x)
				for x1 in new_d_list_update:
					d_list_update.append('.exprs['+str(count)+']'+x1)
				for x1 in new_a_list_update:
					a_list_update.append('['+str(count)+']'+x1)
			else:
				d_list_update.append('.exprs['+str(count)+']')
				a_list_update.append('['+str(count)+']')
			count=count+1
	return d_list_update,a_list_update



#
#Reconstruct Program by Removing assert,assume,error
#

def reconstructPreDefinedFun(statements):
	global fail_count
	global error_count
	global assume_count
	global assert_count
	global new_variable
        global counter_variableMap
        global counter_variableMap_Conf
        global array_size_variableMap
        
        counter_variableMap={}

        counter_variableMap_Conf={}

        array_size_variableMap={}
        
	statements=getPreDefinedFun(statements,0,{})
        
        
    	update_statements=[]
        temp_update_statements=[]

    	for var in new_variable.keys():
    		if type(new_variable[var]) is str:
    			temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
    		else:
    			temp=new_variable[var]
    		temp_update_statements.append(temp)
                
        for statement in temp_update_statements:
            update_statements.append(statement)
    	for statement in statements:
            update_statements.append(statement)

        #for statement in statements:
        #    #statement.show()
        #    #if type(statement) is not c_ast.Decl:
        #    update_statements.append(statement)
        
    	new_variable={}
    	return update_statements



counter_variableMap={}

counter_variableMap_Conf={}

array_size_variableMap={}

def getPreDefinedFun(statements,degree,dec_map):
	update_statements=[]
	global fail_count
	global error_count
	global assume_count
	global assert_count
	global new_variable
        global counter_variableMap
        global counter_variableMap_Conf
        global array_size_variableMap
        #print '$$$$$$$$$$$$$$$$$@@@@@@@@@@@@'
        #print new_variable
        #print '$$$$$$$$$$$$$$$$$@@@@@@@@@@@@'
	for statement in statements:
		if type(statement) is c_ast.If:
			stmt=getPreDefinedFunIf(statement,degree,dec_map)
			if stmt is not None:
				update_statements.append(stmt)
		elif type(statement) is c_ast.While:
			local_counter_varMap=getCounterVariables(statement.cond,counter_variableMap)

			getConfirmationVariables(statement.stmt.block_items,counter_variableMap,counter_variableMap_Conf)
                        

                        getCounterVariablesConst(statement.cond,array_size_variableMap)
                        
                        getArraySizeVar(local_counter_varMap,counter_variableMap_Conf,array_size_variableMap)
                        

                        degree=degree+1
                        
			new_block_items1=getPreDefinedFun(statement.stmt.block_items,degree,dec_map)
                        
                        degree=degree-1
                        
                        
			for item in local_counter_varMap.keys():
				if item in counter_variableMap.keys():
					del counter_variableMap[item]
				if item in counter_variableMap_Conf.keys():
					del counter_variableMap_Conf[item]
                                if item in array_size_variableMap.keys():
                                        del array_size_variableMap[item]
			#start comment on 16/08/2017
			#if degree==0:
                        #    array_size_variableMap.clear()
                        #    for var in dec_map.keys():
                        #        if type(dec_map[var]) is str:
                        #            temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
                        #        else:
                        #            temp=dec_map[var]
                        #        update_statements.append(temp)
                        #        del dec_map[var]
                        #        del new_variable[var]
                        #end comment on 16/08/2017
			update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=new_block_items1)))
		#elif type(statement) is c_ast.Label:
		#	if statement.name=='ERROR':
                #                print 'XXXXXXXXXXXXXXXXXXXXXXXX'
		#		fail_count=fail_count+1
		#		update_statements.append(statement)
		#		update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1')))
		#		new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                #                dec_map['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
		#		
		#	else:
		#		update_statements.append(statement)
		elif type(statement) is c_ast.FuncCall:
			parameters=[]
			if statement.args is not None:
				for param in statement.args.exprs:
					if type(param) is c_ast.ID:
						parameters.append(param)
					elif type(param) is c_ast.Constant:
						parameters.append(param)
					elif type(param) is c_ast.BinaryOp:
						parameters.append(param)
					elif type(param) is c_ast.FuncCall:
						parameters.append(param)
					else:
						parameters.append(param)
                                if statement.name.name=='__VERIFIER_assert':
                                    new_statement=None
                                    for parameter in parameters:
                                            if new_statement is None:
                                                    assert_count=assert_count+1
                                                    new_var_name=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE')
                                                    if len(counter_variableMap_Conf.keys())>0:
                                                        
                                                            if len(counter_variableMap_Conf)==degree:
                                                                new_var_name=create_Assert_Array(new_var_name,counter_variableMap_Conf.keys(),counter_variableMap_Conf)
                                                            elif len(counter_variableMap)==degree:
                                                                new_var_name=create_Assert_Array(new_var_name,counter_variableMap.keys(),counter_variableMap)
                                                            else:
                                                                new_var_name=create_Assert_Array(new_var_name,counter_variableMap_Conf.keys(),counter_variableMap_Conf)
                                                            
                                                
                                                    status,parameter=modificationOfCondition(parameter)
                                                    if status==True:
                                                            parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
						
                                                    new_statement= c_ast.Assignment(op='=', lvalue=new_var_name, rvalue=parameter)
						#new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                    if len(counter_variableMap_Conf.keys())>0:
                                            
                                                            new_variable['_'+str(assert_count)+'_'+'PROVE']=creatArrayDec('_'+str(assert_count)+'_'+'PROVE',array_size_variableMap.keys(),degree)
                                                            dec_map['_'+str(assert_count)+'_'+'PROVE']=creatArrayDec('_'+str(assert_count)+'_'+'PROVE',array_size_variableMap.keys(),degree)
                                                        
                                                    else:
                                                            new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                        
                                                            dec_map['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                        
                                                #print '#############@@@@@@@@'
                                                #print new_variable['_'+str(assert_count)+'_'+'PROVE'].show()
						#print '#############@@@@@@@@'
                                            else:
                                                    assert_count=assert_count+1
                                                    
                                                    new_var_name=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE')
                                                    if len(counter_variableMap_Conf.keys())>0:
                                                            if len(counter_variableMap_Conf)==degree:
                                                                new_var_name=create_Assert_Array(new_var_name,counter_variableMap_Conf.keys(),counter_variableMap_Conf)
                                                            elif len(counter_variableMap)==degree:
                                                                new_var_name=create_Assert_Array(new_var_name,counter_variableMap.keys(),counter_variableMap)
                                                            else:
                                                                new_var_name=create_Assert_Array(new_var_name,counter_variableMap_Conf.keys(),counter_variableMap_Conf)
                                                            #new_var_name=create_Assert_Array(new_var_name,counter_variableMap_Conf.keys(),counter_variableMap_Conf)

                                                    status,stmt=modificationOfCondition(parameter)
                                                    if status==True:
                                                            parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
                                                    new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=new_var_name, rvalue=parameter), right=new_statement)
                                                    #new_variable['_'+str(assert_count)+'_'+'PROVE']='Array'
                                                    if len(counter_variableMap_Conf.keys())>0:
                                                            new_variable['_'+str(assert_count)+'_'+'PROVE']=creatArrayDec('_'+str(assert_count)+'_'+'PROVE',array_size_variableMap.keys(),degree)
                                                            

                                                        
                                                            dec_map['_'+str(assert_count)+'_'+'PROVE']=creatArrayDec('_'+str(assert_count)+'_'+'PROVE',array_size_variableMap.keys(),degree)
                                                    else:
                                                            new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                        
                                                            dec_map['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                        

                                    update_statements.append(new_statement)
                                elif statement.name.name=='__VERIFIER_assume':
                                    new_statement=None
                                    for parameter in parameters:
                                            if new_statement is None:
                                                    assume_count=assume_count+1
						
                                                    new_var_name=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME')
                                                    if len(counter_variableMap_Conf.keys())>0:
                                                            new_var_name=create_Assert_Array(new_var_name,counter_variableMap_Conf.keys(),counter_variableMap_Conf)

                                                    status,parameter=modificationOfCondition(parameter)
                                                    if status==True:
                                                            parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
						
                                                    new_statement= c_ast.Assignment(op='=', lvalue=new_var_name, rvalue=parameter)
                                                    if len(counter_variableMap_Conf.keys())>0:
                                                        new_variable['_'+str(assume_count)+'_'+'ASSUME']=creatArrayDec('_'+str(assume_count)+'_'+'ASSUME',array_size_variableMap.keys(),degree)
                                                    
                                                        dec_map['_'+str(assume_count)+'_'+'ASSUME']=creatArrayDec('_'+str(assume_count)+'_'+'ASSUME',array_size_variableMap.keys(),degree)
                                                    
                                                    else:
                                                        new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                                    
                                                        dec_map['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                            else:
                                                    assume_count=assume_count+1
						
                                                    new_var_name=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME')
                                                    if len(counter_variableMap_Conf.keys())>0:
                                                            new_var_name=create_Assert_Array(new_var_name,counter_variableMap_Conf.keys(),counter_variableMap_Conf)
						
                                                    status,stmt=modificationOfCondition(parameter)
                                                    if status==True:
                                                            parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))						
						
                                                    new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=new_var_name, rvalue=parameter), right=new_statement)
                                                    if len(counter_variableMap_Conf.keys())>0:
                                                        new_variable['_'+str(assume_count)+'_'+'ASSUME']=creatArrayDec('_'+str(assume_count)+'_'+'ASSUME',array_size_variableMap.keys(),degree)
                                                    
                                                        dec_map['_'+str(assume_count)+'_'+'ASSUME']=creatArrayDec('_'+str(assume_count)+'_'+'ASSUME',array_size_variableMap.keys(),degree)
                                                    
                                                    else:
                                                        new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                                    
                                                        dec_map['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                    update_statements.append(new_statement)
				else:
                                    update_statements.append(statement)
			else:
				if statement.name.name=='__VERIFIER_error':
                                    fail_count=fail_count+1
                                    #update_statements.append(statement)
                                    update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1')))
                                    new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                                    dec_map['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                                else:
                                    update_statements.append(statement)
		
		else:
			update_statements.append(statement)
	return update_statements
	


#
#Get Counter Variable
#

def getCounterVariables(statement,variableMap):
	variableMap_Local={}
	if type(statement) is c_ast.UnaryOp:
		if type(statement.expr) is c_ast.ID:
			variableMap[statement.expr.name]=statement.expr.name
			variableMap_Local[statement.expr.name]=statement.expr.name
	        else:
                        temp_variableMap=getCounterVariables(statement.expr,variableMap)
                        if temp_variableMap is not None:
                        	for item in temp_variableMap.keys():
                        		variableMap_Local[item]=item
	elif type(statement) is c_ast.ID:
		variableMap[statement.name]=statement.name
		variableMap_Local[statement.name]=statement.name
	#elif type(statement) is c_ast.ArrayRef:
	#	getCounterVariables(statement.expr,variableMap)
	elif type(statement) is c_ast.BinaryOp:
		if type(statement.left) is c_ast.ID:
			variableMap[statement.left.name]=statement.left.name
			variableMap_Local[statement.left.name]=statement.left.name
		else:
			temp_variableMap=getCounterVariables(statement.left,variableMap)
			if temp_variableMap is not None:
				for item in temp_variableMap.keys():
                        		variableMap_Local[item]=item
		if type(statement.right) is c_ast.ID:
			variableMap[statement.right.name]=statement.right.name
			variableMap_Local[statement.right.name]=statement.right.name
		else:
			temp_variableMap=getCounterVariables(statement.right,variableMap)
			if temp_variableMap is not None:
				for item in temp_variableMap.keys():
                        		variableMap_Local[item]=item
        elif type(statement) is c_ast.ArrayRef:
                getAllSubScripts(statement,variableMap,variableMap_Local)
	return variableMap_Local


#
#Get Varible Constant from Condition
#

def getCounterVariablesConst(statement,variableMap):
	if type(statement) is c_ast.UnaryOp:
		if type(statement.expr) is c_ast.ID:
			variableMap[statement.expr.name]=statement.expr.name
	        else:
                        getCounterVariablesConst(statement.expr,variableMap)    
	elif type(statement) is c_ast.ID:
		variableMap[statement.name]=statement.name
        elif type(statement) is c_ast.Constant:
                variableMap[statement.value]=statement.value
	#elif type(statement) is c_ast.ArrayRef:
	#	getCounterVariables(statement.expr,variableMap)
	elif type(statement) is c_ast.BinaryOp:
		if type(statement.left) is c_ast.ID:
			variableMap[statement.left.name]=statement.left.name
		else:
			getCounterVariablesConst(statement.left,variableMap)
		if type(statement.right) is c_ast.ID:
			variableMap[statement.right.name]=statement.right.name
		else:
			getCounterVariablesConst(statement.right,variableMap)









def getAllSubScripts(statement,variableMap,variableMap_Local):
    if type(statement.subscript) is c_ast.ID:
        variableMap[statement.subscript.name]=statement.name
        variableMap_Local[statement.subscript.name]=statement.name
    if type(statement.name) is c_ast.ArrayRef:
        getAllSubScripts(statement.name,variableMap,variableMap_Local)
#
#Get Counter Variable
#

def getCounterVariablesConf(statement,variableMap):
	variableMap_Local={}
	if type(statement) is c_ast.UnaryOp:
		if type(statement.expr) is c_ast.ID:
			variableMap[statement.expr.name]=statement.expr.name
	        else:
                        getCounterVariablesConf(statement.expr,variableMap)    
	elif type(statement) is c_ast.ID:
		variableMap[statement.name]=statement.name
        #elif type(statement) is c_ast.Constant:
        #        variableMap[statement.value]=statement.value
	#elif type(statement) is c_ast.ArrayRef:
	#	getCounterVariables(statement.expr,variableMap)
	elif type(statement) is c_ast.BinaryOp:
		if type(statement.left) is c_ast.ID:
			variableMap[statement.left.name]=statement.left.name
		else:
			getCounterVariablesConf(statement.left,variableMap)
		if type(statement.right) is c_ast.ID:
			variableMap[statement.right.name]=statement.right.name
		else:
			getCounterVariablesConf(statement.right,variableMap)






#
#Confirmation of Counter Variable
#

def getConfirmationVariables(statements,variableMap,variableMap_Conf):
    for statement in statements:
    	if type(statement) is c_ast.Assignment:
        	if type(statement.lvalue) is c_ast.ID:
            		if statement.lvalue.name in variableMap.keys():
            			variableMapExp={}
                		getCounterVariablesConf(statement.rvalue,variableMapExp)
                		if statement.lvalue.name in variableMapExp.keys():
                   			 variableMap_Conf[statement.lvalue.name]=statement.lvalue.name

def getArraySizeVar(local_counter_varMap,counter_variableMap_Conf,array_size_variableMap):
    for var in local_counter_varMap.keys():
        if var in counter_variableMap_Conf.keys() and var in array_size_variableMap.keys():
            #array_size_variableMap[var]=var
            del array_size_variableMap[var]
                




#create_Assert_Array(['x','y'],{'x':'x','y':'y'})
def create_Assert_Array(array_name,items,variableMap):
	if len(items)>0:
		if len(items[1:])>0:
			return c_ast.ArrayRef(name=create_Assert_Array(array_name,items[:-1],variableMap), subscript=c_ast.ID(name=items[-1]))	
		else:
			return c_ast.ArrayRef(name=array_name, subscript=c_ast.ID(name=items[-1]))
	return None
	


#creatArrayDec('a',['x','y']).show()

def creatArrayDec(name,parameterlist,degree):
    str_parameterlist=None
    count=0
    generator = c_generator.CGenerator()
    #for para in parameterlist:
    #    if is_number(para)==True and '.' in para:
    #        para=str(int(para.split(".")[0]))
    arraysize=1000000
    if degree==2:
        arraysize=100000
    elif degree==3:
        arraysize=100000
        
    for x in range(0, degree):
        if str_parameterlist==None:
            
            str_parameterlist='['+str(arraysize)+']'
        else:
            str_parameterlist='['+str(arraysize)+']'+str_parameterlist
        #if count<degree:
        #    if str_parameterlist==None:
        #        str_parameterlist='['+para+']'
        #        #str_parameterlist='['+']'
        #    else:
        #        str_parameterlist='['+para+']'+str_parameterlist
        #count=count+1
    #print '-----------@@@@@@@@@@@@'
    #print parameterlist
    #print count
    #print degree
    #print '-----------@@@@@@@@@@@@'

            #str_parameterlist='['+']'+str_parameterlist
    if str_parameterlist is not None:
        function='int '+name+str_parameterlist
    else:
        function='int '+name
    main_function='void main(){'+function+';}'
    parser = c_parser.CParser()
    ast = parser.parse(main_function)
    return ast.ext[0].body.block_items[0]







#
#Reconstruct Program by Removing assert,assume,error
#

def getPreDefinedFunIf(statement,degree,dec_map):
	new_iftrue=None
	new_iffalse=None
	global fail_count
	global error_count
	global assume_count
	global assert_count
	global new_variable

	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Label:
			#if statement.iftrue.name=='ERROR':
			#	fail_count=fail_count+1
			#	new_block_items1=[]
			#	new_block_items1.append(c_ast.Label(name=statement.iftrue.name, stmt=[]))
			#	new_block_items1.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1')))
			#	new_iftrue=c_ast.Compound(block_items=new_block_items1)
			#	new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                        #        dec_map['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
			if type(statement.iftrue) is c_ast.FuncCall:
				parameters=[]
				if statement.iftrue.args is not None:
					for param in statement.iftrue.args.exprs:
						if type(param) is c_ast.ID:
							parameters.append(param)
						elif type(param) is c_ast.Constant:
							parameters.append(param)
						elif type(param) is c_ast.BinaryOp:
							parameters.append(param)
						elif type(param) is c_ast.FuncCall:
							parameters.append(param)
						else:
							parameters.append(param)
                                        if statement.iftrue.name.name=='__VERIFIER_assert':
                                            new_statement=None
                                            for parameter in parameters:
                                                    if new_statement is None:
                                                            assert_count=assert_count+1
                                                            status,parameter=modificationOfCondition(parameter)
                                                            if status==True:
                                                                    parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
                                                            new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter)
                                                            new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                            dec_map['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                    else:
                                                            assert_count=assert_count+1
                                                            status,parameter=modificationOfCondition(parameter)
                                                            if status==True:
                                                                    parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
                                                            new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter), right=new_statement)
                                                            new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                            dec_map['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                            new_iftrue=new_statement
                                        elif statement.iftrue.name.name=='__VERIFIER_assume':
                                            new_statement=None
                                            for parameter in parameters:
                                                    if new_statement is None:
                                                            assume_count=assume_count+1
                                                            new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter)
                                                            new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                                            dec_map['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                                    else:
                                                            assume_count=assume_count+1
                                                            new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter), right=new_statement)
                                                            new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                                            dec_map['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                            new_iftrue=new_statement
                                        elif statement.name.name=='__VERIFIER_error':
                                            fail_count=fail_count+1
                                            new_block_items1=[]
                                            #new_block_items1.append(c_ast.Label(name=statement.iftrue.name, stmt=[]))
                                            new_block_items1.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1')))
                                            new_iftrue=c_ast.Compound(block_items=new_block_items1)
                                            new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                                            dec_map['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                                        else:
                                            new_iftrue=statement.iftrue
                                
		elif type(statement.iftrue) is c_ast.Compound:
                    
                        #degree=degree+1
                        
			new_block_items=getPreDefinedFun(statement.iftrue.block_items,degree,dec_map)
                        
                        #degree=degree-1
                        
			new_iftrue=c_ast.Compound(block_items=new_block_items)
		else:
			new_iftrue=statement.iftrue
			
        if type(statement.iffalse) is c_ast.Label:
                    #if statement.iffalse.name=='ERROR':
                    #        fail_count=fail_count+1
                    #        new_block_items1=[]
                    #        #new_block_items1.append(statement.iffalse)
                    #        new_block_items1.append(c_ast.Label(name=statement.iftrue.name, stmt=[]))
                    #        new_block_items1.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1')))
                    #        new_iffalse=c_ast.Compound(block_items=new_block_items1)
                    #        new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                    #        dec_map['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                    if type(statement.iffalse) is c_ast.FuncCall:
                            parameters=[]
                            if statement.iffalse.args is not None:
                                    for param in statement.iftrue.args.exprs:
                                            if type(param) is c_ast.ID:
                                                    parameters.append(param)
                                            elif type(param) is c_ast.Constant:
                                                    parameters.append(param)
                                            elif type(param) is c_ast.BinaryOp:
                                                    parameters.append(param)
                                    if statement.name.name=='__VERIFIER_assert':
                                            new_statement=None
                                            for parameter in parameters:
                                                    if new_statement is None:
                                                            assert_count=assert_count+1
                                                            new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter)
                                                            new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                            dec_map['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                    else:
                                                            assert_count=assert_count+1
                                                            new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter), right=new_statement)
                                                            new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                                            dec_map['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
                                            new_iffalse=new_statement
                                    elif statement.name.name=='__VERIFIER_assume':
                                            new_statement=None
                                            for parameter in parameters:
                                                    if new_statement is None:
                                                            assume_count=assume_count+1
                                                            new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter)
                                                            new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                                            dec_map['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                                    else:
                                                            assume_count=assume_count+1
                                                            new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter), right=new_statement)
                                                            new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                                            dec_map['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
                                            new_iffalse=new_statement
                                    elif statement.name.name=='__VERIFIER_error':
                                            fail_count=fail_count+1
                                            new_block_items1=[]
                                            #new_block_items1.append(c_ast.Label(name=statement.iftrue.name, stmt=[]))
                                            new_block_items1.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1')))
                                            new_iftrue=c_ast.Compound(block_items=new_block_items1)
                                            new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                                            dec_map['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
                                    else:
                                        new_iffalse=statement.iffalse
        elif type(statement.iffalse) is c_ast.Compound:
                    
                #degree=degree+1
                        
                new_block_items=getPreDefinedFun(statement.iffalse.block_items,degree,dec_map)
                        
                #degree=degree-1
                        
                new_iffalse=c_ast.Compound(block_items=new_block_items)
        else:
                if type(statement.iffalse) is c_ast.If:
                    new_iffalse=getPreDefinedFunIf(statement.iffalse,degree,dec_map)
                else:
                        new_iffalse=statement.iffalse
				
	if new_iftrue is not None and new_iffalse is None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
	elif new_iftrue is not None and new_iffalse is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
		return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
		return new_iffalse
	else:
		return None


def removeEmptyIfLoop(statements):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.If:
			statement=removeEmptyIfLoop_If(statement)
			if statement is not None:
				update_statements.append(statement)
		elif type(statement) is c_ast.While:
                        if len(statement.stmt.block_items)>0:
                            new_block_items=removeEmptyIfLoop(statement.stmt.block_items)
                            update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=new_block_items)))
		else:
			if statement is not None:
				if type(statement) is not c_ast.EmptyStatement:
					update_statements.append(statement)
	return update_statements
			
			
			
def removeEmptyIfLoop_If(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if len(statement.iftrue.block_items)==0:
				new_iftrue=None
			else:
				new_block=removeEmptyIfLoop(statement.iftrue.block_items)
				if len(new_block)==0:
					new_iftrue=None
				else:
					new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.EmptyStatement:
				new_iftrue=None
			else:
				new_iftrue=statement.iftrue
				
		if type(statement.iffalse) is c_ast.Compound:
			if len(statement.iffalse.block_items)==0:
				new_iffalse=None
			else:
				new_block=removeEmptyIfLoop(statement.iffalse.block_items)
				if len(new_block)==0:
					new_iffalse=None 
				else:
					new_iffalse=c_ast.Compound(block_items=new_block) 
		elif type(statement.iffalse) is c_ast.If:
			result=removeEmptyIfLoop_If(statement.iffalse)
			if result is not None:
				new_iffalse=result
		else:
			if type(statement.iffalse) is c_ast.EmptyStatement:
				new_iftrue=None
			else:
				new_iffalse=statement.iffalse
	
	
	if new_iftrue is not None and new_iffalse is None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
	elif new_iftrue is not None and new_iffalse is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
		return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
		return new_iffalse
	else:
		return None

		
		
def returnReplacement(statements,end_label_map):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.If:
			statement=returnReplacementIf(statement,end_label_map)
			if statement is not None:
				update_statements.append(statement)
		elif type(statement) is c_ast.While:
			new_block_items=returnReplacement(statement.stmt.block_items,end_label_map)
			update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=new_block_items)))
		elif type(statement) is c_ast.Return:
			if statement.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.expr))
				update_statements.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				update_statements.append(c_ast.Goto(name=label))
				end_label_map[label]=label
		elif type(statement) is c_ast.Label:
			update_statements.append(c_ast.Label(name=statement.name, stmt=None))
			if type(statement.stmt) is c_ast.Return:
				if statement.stmt.expr is not None:
					label='Label'+str(len(end_label_map.keys())+1)
					update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.stmt.expr))
					update_statements.append(c_ast.Goto(name=label))
					end_label_map[label]=label
				else:
					label='Label'+str(len(end_label_map.keys())+1)
					update_statements.append(c_ast.Goto(name=label))
					end_label_map[label]=label
			else:
				if statement.stmt is not None:
					update_statements.append(statement.stmt)
			
		else:
			update_statements.append(statement)
	return update_statements
	
	
	
	
	
	
def returnReplacementIf(statement,end_label_map):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Return:
			new_block=[]
			if statement.iftrue.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.iftrue.expr))
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.Compound:
				new_block=returnReplacement(statement.iftrue.block_items,end_label_map)
				new_iftrue=c_ast.Compound(block_items=new_block)
			else:
                                new_iftrue=statement.iftrue
			
		if type(statement.iffalse) is c_ast.Return:
			new_block=[]
			if statement.iffalse.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.iffalse.expr))
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			new_iffalse=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iffalse) is c_ast.Compound:
				new_block=returnReplacement(statement.iffalse.block_items,end_label_map)
				new_iffalse=c_ast.Compound(block_items=new_block)
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=returnReplacementIf(statement.iffalse,end_label_map)
				else:
                                        new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)



def change_var_name(statements):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Decl:
			if type(statement.type) is c_ast.ArrayDecl:
                                if checkingArrayName(statement.type)==True:
                                    statement=c_ast.Decl(name=statement.name+'_var', quals=statement.quals, storage=statement.storage, funcspec=statement.funcspec, type=renameArrayName(statement.type), init=statement.init, bitsize=statement.bitsize)
                                statement.type.dim=change_var_name_stmt(statement.type.dim)
			else:
                            if type(statement.type) is not c_ast.PtrDecl:
				if is_number(statement.type.declname[-1])==True:
					statement=c_ast.Decl(name=statement.name+'_var', quals=statement.quals, storage=statement.storage, funcspec=statement.funcspec, type=c_ast.TypeDecl(declname=statement.type.declname+'_var', quals=statement.type.quals, type=statement.type.type), init=statement.init, bitsize=statement.bitsize)
				elif statement.type.declname in ['S','Q','N','in','is','limit']:
					statement=c_ast.Decl(name=statement.name+'_var', quals=statement.quals, storage=statement.storage, funcspec=statement.funcspec, type=c_ast.TypeDecl(declname=statement.type.declname+'_var', quals=statement.type.quals, type=statement.type.type), init=statement.init, bitsize=statement.bitsize)
			update_statements.append(statement)
		elif type(statement) is c_ast.If:
			update_statements.append(change_var_nameIf(statement))
		elif type(statement) is c_ast.While:
                        if type(statement.stmt) is c_ast.Assignment:
                                new_block=[]
                                new_block.append(statement.stmt)
                                update_statements.append(c_ast.While(cond=change_var_name_stmt(statement.cond),stmt=c_ast.Compound(block_items=change_var_name(new_block))))
                        elif type(statement.stmt) is c_ast.UnaryOp:
                                new_block=[]
                                new_block.append(statement.stmt)
                                update_statements.append(c_ast.While(cond=change_var_name_stmt(statement.cond),stmt=c_ast.Compound(block_items=change_var_name(new_block))))
			elif type(statement.stmt) is c_ast.EmptyStatement:
                                statement
                                #update_statements.append(statement)
			elif statement.stmt.block_items is not None:
				update_statements.append(c_ast.While(cond=change_var_name_stmt(statement.cond),stmt=c_ast.Compound(block_items=change_var_name(statement.stmt.block_items))))	
			else:
				update_statements.append(c_ast.While(cond=change_var_name_stmt(statement.cond),stmt=c_ast.Compound(block_items=statement.stmt.block_items)))	
		elif type(statement) is c_ast.Assignment:
			update_statements.append(c_ast.Assignment(op=statement.op,lvalue=change_var_name_stmt(statement.lvalue),rvalue=change_var_name_stmt(statement.rvalue)))
		elif type(statement) is c_ast.Return:
                    statement.expr=change_var_name_stmt(statement.expr)
                    update_statements.append(statement)
                elif type(statement) is c_ast.FuncCall:
                    if statement.args is not None:
                        new_expr=[]
                        for exp in statement.args.exprs:
                            new_expr.append(change_var_name_stmt(exp))
                        update_statements.append(c_ast.FuncCall(name=statement.name,args=c_ast.ExprList(exprs=new_expr)))
                    else:
                        update_statements.append(statement)
		else:
			update_statements.append(statement)
	return update_statements
	


	
def change_var_nameIf(statement):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.Assignment:
        	new_iftrue=c_ast.Assignment(op=statement.iftrue.op,lvalue=change_var_name_stmt(statement.iftrue.lvalue),rvalue=change_var_name_stmt(statement.iftrue.rvalue))
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=change_var_name(statement.iftrue.block_items)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
       
    
        if type(statement.iffalse) is c_ast.Assignment:
		new_iffalse=c_ast.Assignment(op=statement.iffalse.op,lvalue=change_var_name_stmt(statement.iffalse.lvalue),rvalue=change_var_name_stmt(statement.iffalse.rvalue))
	elif type(statement.iffalse) is c_ast.Compound:
		if statement.iffalse.block_items is not None:
	        	new_block_items=change_var_name(statement.iffalse.block_items)
	                new_iffalse=c_ast.Compound(block_items=new_block_items)
	        else:
	                new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.If:
		new_iffalse=change_var_nameIf(statement.iffalse)
	else:
        	new_iffalse=statement.iffalse
        	
    return c_ast.If(cond= change_var_name_stmt(statement.cond), iftrue=new_iftrue, iffalse=new_iffalse)


def change_var_name_stmt(statement):
	if type(statement) is c_ast.BinaryOp:
		if type(statement.left) is c_ast.ID:
			if is_number(statement.left.name[-1])==True:
				stmt_left=c_ast.ID(name=statement.left.name+'_var')
			elif statement.left.name in ['S','Q','N','in','is','limit']:
				stmt_left=c_ast.ID(name=statement.left.name+'_var')
			else:
				stmt_left=change_var_name_stmt(statement.left)
		else:
			stmt_left=change_var_name_stmt(statement.left)
		
		if type(statement.right) is c_ast.ID:
			if is_number(statement.right.name[-1])==True:
				stmt_right=c_ast.ID(name=statement.right.name+'_var')
			elif statement.right.name in ['S','Q','N','in','is','limit']:
				stmt_right=c_ast.ID(name=statement.right.name+'_var')
			else:
				stmt_right=change_var_name_stmt(statement.right)
		else:
			stmt_right=change_var_name_stmt(statement.right)
		return c_ast.BinaryOp(op=statement.op, left=stmt_left, right=stmt_right)
	elif type(statement) is c_ast.UnaryOp:
		if type(statement.expr) is c_ast.ID:
			if is_number(statement.expr.name[-1])==True:
				stmt=c_ast.ID(name=statement.expr.name+'_var')
			elif statement.expr.name in ['S','Q','N','in','is','limit']:
				stmt=c_ast.ID(name=statement.expr.name+'_var')
			else:
				stmt=change_var_name_stmt(statement.expr)
		else:
			stmt=change_var_name_stmt(statement.expr)
		return c_ast.UnaryOp(op=statement.op, expr=stmt)
	elif type(statement) is c_ast.ID:
		if is_number(statement.name[-1])==True:
			return c_ast.ID(name=statement.name+'_var')
		elif statement.name in ['S','Q','N','in','is','limit']:
			return c_ast.ID(name=statement.name+'_var')
		else:
                        return statement
        elif type(statement) is c_ast.FuncCall:
            if statement.args is not None:
                new_expr=[]
                for exp in statement.args.exprs:
                    new_expr.append(change_var_name_stmt(exp))
                return c_ast.FuncCall(name=statement.name,args=c_ast.ExprList(exprs=new_expr))
            else:
                return statement
	
	else:
		if type(statement) is c_ast.ArrayRef:
                    return renameArrayName(statement)
                    #if checkingArrayName(statement)==True:
                    #    return renameArrayName(statement)
                    #else:
                    #    return statement
                elif type(statement) is c_ast.StructRef:
                    return c_ast.StructRef(name=change_var_name_stmt(statement.name),type=change_var_name_stmt(statement.type),field=statement.field)
                else:
                    return statement


def change_var_name_stmt1(statement,count,var_map,in_var_map,fun_count,all_var_int):
	if type(statement) is c_ast.BinaryOp:
		if type(statement.left) is c_ast.ID:
			if statement.left.name in var_map.keys() or statement.left.name in in_var_map.keys():
                                if statement.left.name in all_var_int:
                                    stmt_left=c_ast.ID(name='f'+str(fun_count)+'_'+str(count)+'_'+statement.left.name)
                                else:
                                    stmt_left=statement.left
			else:
				stmt_left=statement.left
		else:
			stmt_left=change_var_name_stmt1(statement.left)
            
		if type(tatement.right) is c_ast.ID:
			if statement.right.name in var_map.keys() or statement.right.name in in_var_map.keys():
                                if statement.right.name in all_var_int:
                                    stmt_right=c_ast.ID(name='f'+str(fun_count)+'_'+str(count)+'_'+statement.right.name)
                                else:
                                    stmt_right=statement.right
			else:
				stmt_right=statement.right
		else:
			stmt_right=change_var_name_stmt1(statement.right)
            
		return c_ast.BinaryOp(op=statement.op, left=stmt_left, right=stmt_right)
	elif type(statement) is c_ast.UnaryOp:
		if type(statement.expr) is c_ast.ID:
			if statement.expr.name in var_map.keys() or statement.expr.name in in_var_map.keys():
                                if statement.expr.name in all_var_int:
                                    stmt=c_ast.ID(name='f'+str(fun_count)+'_'+str(count)+'_'+statement.expr.name)
                                else:
                                    stmt=statement.expr
                        else:
				stmt=statement.expr
		else:
			stmt=change_var_name_stmt1(statement.expr)
		return c_ast.UnaryOp(op=statement.op, expr=stmt)
	elif type(statement) is c_ast.ID:
		if statement.name in var_map.keys() or statement.name in in_var_map.keys():
			if statement.name in all_var_int:
                            return c_ast.ID(name='f'+str(fun_count)+'_'+str(count)+'_'+statement.name)
                        else:
                            return statement
                            
		else:
                        return statement
        elif type(statement) is c_ast.FuncCall:
            if statement.args is not None:
                new_expr=[]
                for exp in statement.args.exprs:
                    new_expr.append(change_var_name_stmt1(exp))
                return c_ast.FuncCall(name=statement.name,args=c_ast.ExprList(exprs=new_expr))
            else:
                return statement
	
	else:
		if type(statement) is c_ast.ArrayRef:
                    return renameArrayName1(statement)
                    #if checkingArrayName(statement)==True:
                    #    return renameArrayName(statement)
                    #else:
                    #    return statement
                else:
                    return statement









def change_var_name_decl(statement):
    if type(statement) is c_ast.Decl:
        if type(statement.type) is c_ast.ArrayDecl:
            if is_number(statement.name[-1])==True:
                statement.name=statement.name+'_var'
                renameArrayName(statement.type)
            elif statement.name in ['S','Q','N','in','is','limit']:
                statement.name=statement.name+'_var'
                renameArrayName(statement.type)
            else:
                statement.type.dim=change_var_name_stmt(statement.type.dim)
        else:
            if is_number(statement.type.declname[-1])==True:
                statement.name=statement.name+'_var' 
                statement.type=c_ast.TypeDecl(declname=statement.type.declname+'_var', quals=statement.type.quals, type=statement.type.type)
            elif statement.type.declname in ['S','Q','N','in','is','limit']:
                statement.name=statement.name+'_var'  
                statement.type=c_ast.TypeDecl(declname=statement.type.declname+'_var', quals=statement.type.quals, type=statement.type.type)
        return statement
    return statement









count__VERIFIER_nondet=0


def organize__VERIFIER_nondet(statements):
        global count__VERIFIER_nondet
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Decl:
			if type(statement.type) is c_ast.ArrayDecl:
                                update_statements.append(statement)
			else:
                                init_values=None
                                if statement.init is not None:
                                    init_values=copy.deepcopy(statement.init)
                                statement=c_ast.Decl(name=statement.name, quals=statement.quals, storage=statement.storage, funcspec=statement.funcspec, type=c_ast.TypeDecl(declname=statement.type.declname, quals=statement.type.quals, type=statement.type.type), init=None, bitsize=statement.bitsize)
                                update_statements.append(statement)
                                if init_values is not None:
                                        update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name=statement.name),rvalue=organize__VERIFIER_nondet_stmt(init_values)))
		elif type(statement) is c_ast.If:
			update_statements.append(organize__VERIFIER_nondetIf(statement))
		elif type(statement) is c_ast.While:
			if statement.stmt.block_items is not None:
				update_statements.append(c_ast.While(cond=organize__VERIFIER_nondet_stmt(statement.cond),stmt=c_ast.Compound(block_items=organize__VERIFIER_nondet(statement.stmt.block_items))))	
			else:
				update_statements.append(c_ast.While(cond=organize__VERIFIER_nondet_stmt(statement.cond),stmt=c_ast.Compound(block_items=statement.stmt.block_items)))	
		elif type(statement) is c_ast.Assignment:
			update_statements.append(c_ast.Assignment(op=statement.op,lvalue=organize__VERIFIER_nondet_stmt(statement.lvalue),rvalue=organize__VERIFIER_nondet_stmt(statement.rvalue)))
		else:
			update_statements.append(statement)
	return update_statements
	


	
def organize__VERIFIER_nondetIf(statement):
    global count__VERIFIER_nondet
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.Assignment:
        	new_iftrue=c_ast.Assignment(op=statement.iftrue.op,lvalue=organize__VERIFIER_nondet_stmt(statement.iftrue.lvalue),rvalue=organize__VERIFIER_nondet_stmt(statement.iftrue.rvalue))
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=change_var_name(statement.iftrue.block_items)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
       
       
        if type(statement.iffalse) is c_ast.Assignment:
		new_iftrue=c_ast.Assignment(op=statement.iffalse.op,lvalue=organize__VERIFIER_nondet_stmt(statement.iffalse.lvalue),rvalue=organize__VERIFIER_nondet_stmt(statement.iffalse.rvalue))
	elif type(statement.iffalse) is c_ast.Compound:
		if statement.iffalse.block_items is not None:
	        	new_block_items=change_var_name(statement.iffalse.block_items)
	                new_iffalse=c_ast.Compound(block_items=new_block_items)
	        else:
	                new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.If:
		new_iffalse=organize__VERIFIER_nondetIf(statement.iffalse)
	else:
        	new_iffalse=statement.iffalse
        	
    return c_ast.If(cond= organize__VERIFIER_nondet_stmt(statement.cond), iftrue=new_iftrue, iffalse=new_iffalse)


def organize__VERIFIER_nondet_stmt(statement):
        global count__VERIFIER_nondet
	if type(statement) is c_ast.BinaryOp:
		if type(statement.left) is c_ast.ID:
			stmt_left=organize__VERIFIER_nondet_stmt(statement.left)
		else:
			stmt_left=organize__VERIFIER_nondet_stmt(statement.left)
		
		if type(statement.right) is c_ast.ID:
			stmt_right=organize__VERIFIER_nondet_stmt(statement.right)
		else:
			stmt_right=organize__VERIFIER_nondet_stmt(statement.right)
		return c_ast.BinaryOp(op=statement.op, left=stmt_left, right=stmt_right)
	elif type(statement) is c_ast.UnaryOp:
		if type(statement.expr) is c_ast.ID:
			stmt=organize__VERIFIER_nondet_stmt(statement.expr)
		else:
			stmt=organize__VERIFIER_nondet_stmt(statement.expr)
		return c_ast.UnaryOp(op=statement.op, expr=stmt)
	elif type(statement) is c_ast.ID:
		if '__VERIFIER_nondet' in statement.name:
                        count__VERIFIER_nondet=count__VERIFIER_nondet+1
			return c_ast.ID(name=statement.name+str(count__VERIFIER_nondet))
		else:
			return statement
	elif type(statement) is c_ast.FuncCall:
                if '__VERIFIER_nondet' in statement.name.name:
                    count__VERIFIER_nondet=count__VERIFIER_nondet+1
                    statement.name=c_ast.ID(name=statement.name.name+str(count__VERIFIER_nondet))
                return statement
	else:
                return statement

			    
"""
 
Goto removal Modules Start

"""

new_variable={}

break_count=0

continue_count=0



def remove_return(statements,membermethod):
	end_label_map={}
	statements=returnReplacement(statements,end_label_map)
	update_statements=[]
        if isRetPresent(statements)==True:
            if membermethod is not None:
                if membermethod.getreturnType() is not None and membermethod.getreturnType() is not 'array':
                    temp=c_ast.Decl(name='RET', quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname='RET', quals=[], type=c_ast.IdentifierType(names=[membermethod.getreturnType()])), init=c_ast.Constant(type=membermethod.getreturnType(), value='0'), bitsize=None)
                    update_statements.append(temp)
                else:
                    temp=c_ast.Decl(name='RET', quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname='RET', quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
                    update_statements.append(temp)
	for statement in statements:
		update_statements.append(statement)
	for label in end_label_map.keys():
    		update_statements.append(c_ast.Label(name=label, stmt=None))
    	return update_statements



def isRetPresent(statements):
    status_flag=False
    for statement in statements:
        if type(statement) is c_ast.Assignment:
            if type(statement.lvalue) is not c_ast.UnaryOp and type(statement.lvalue.name) is str and 'RET' in statement.lvalue.name:
                status_flag=True
        elif type(statement) is c_ast.If:
            if isRetPresentIf(statement)==True:
                status_flag=True
    return status_flag

def isRetPresentIf(statement):
        status_flag=False
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
                                if isRetPresent(statement.iftrue.block_items)==True:
                                    status_flag=True
		else:
                    if type(statement.iftrue) is c_ast.Assignment:
                        if type(statement.iftrue.lvalue) is not c_ast.UnaryOp and type(statement.iftrue.lvalue.name) is str and 'RET' in statement.iftrue.lvalue.name:
                            status_flag=True
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
                            if isRetPresent(statement.iffalse.block_items)==True:
                                    status_flag=True
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=isRetPresentIf(statement.iffalse)
		else:
                    if type(statement.iffalse) is c_ast.Assignment:
                        if type(statement.iffalse.lvalue) is not c_ast.UnaryOp and type(statement.iffalse.lvalue.name) is str and 'RET' in statement.iffalse.lvalue.name:
                            status_flag=True
	return status_flag


"""

Is Variable is present and Type


"""

def isVarPresnt(statements,variable_name):
    status_flag=False
    for statement in statements:
        if type(statement) is c_ast.Assignment:
                flag_r=isVarPresntStmt(statement.rvalue,variable_name)
                flag_l=isVarPresntStmt(statement.lvalue,variable_name)
                if flag_r==True and flag_l==True:
                    return True
                elif flag_r==False and flag_l==True:
                    return True 
                elif flag_r==True and flag_l==False:
                    return True 
        elif type(statement) is c_ast.If:
            if isVarPresntIf(statement,variable_name)==True:
                return True
        elif type(statement) is c_ast.While:
            if type(statement.stmt) is c_ast.Compound:
                if isVarPresnt(statement.stmt.block_items,variable_name)==True:
                    return True
    return False

def isVarPresntIf(statement,variable_name):
        status_flag=False
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
                                if isVarPresnt(statement.iftrue.block_items,variable_name)==True:
                                    status_flag=True
		else:
                    if type(statement.iftrue) is c_ast.Assignment:
                        flag_r=isVarPresntStmt(statement.iftrue.rvalue,variable_name)
                        flag_l=isVarPresntStmt(statement.iftrue.lvalue,variable_name)
                        if flag_r==True and flag_l==True:
                            status_flag = True
                        elif flag_r==False and flag_l==True:
                            status_flag = True 
                        elif flag_r==True and flag_l==False:
                            status_flag = True
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
                            if isVarPresnt(statement.iffalse.block_items,variable_name)==True:
                                    status_flag=True
		elif type(statement.iffalse) is c_ast.If:
			if isVarPresntIf(statement.iffalse,variable_name):
                            status_flag=True
		else:
                    if type(statement.iffalse) is c_ast.Assignment:
                        flag_r=isVarPresntStmt(statement.iffalse.rvalue,variable_name)
                        flag_l=isVarPresntStmt(statement.iffalse.lvalue,variable_name)
                        if flag_r==True and flag_l==True:
                            status_flag = True
                        elif flag_r==False and flag_l==True:
                            status_flag = True 
                        elif flag_r==True and flag_l==False:
                            status_flag = True
	return status_flag


def isVarPresntStmt(statement,variable_name):
	if type(statement) is c_ast.UnaryOp:
                return isVarPresntStmt(statement.expr,variable_name)
        elif type(statement) is c_ast.BinaryOp:
                flag_r=isVarPresntStmt(statement.right,variable_name)
                flag_l=isVarPresntStmt(statement.left,variable_name)
                if flag_r==True and flag_l==True:
                    return True
                elif flag_r==False and flag_l==True:
                    return True 
                elif flag_r==True and flag_l==False:
                    return True 
                else:
                    return False 
        elif type(statement) is c_ast.ID:
            if variable_name==statement.name:
                return True
            else:
                return False
        elif type(statement) is c_ast.StructRef:
            return isVarPresntStmt(statement.name,variable_name)
        elif type(statement) is c_ast.ArrayRef:
            if variable_name == getArrayName(statement):
                return True
            else:
                return False
	else:
            return False









"""

Method for simplification of Condition

"""

def simplifyCondition(statement):
	if type(statement) is c_ast.UnaryOp:
		if statement.op=='!':
			if type(statement.expr) is c_ast.ID:
				return statement
			elif type(statement.expr) is c_ast.Constant:
				return statement
			elif type(statement.expr) is c_ast.ArrayRef:
				return statement
			elif type(statement.expr) is c_ast.FuncCall:
				return statement
			else:
				return getComplement(statement.expr)
		else:
			return c_ast.UnaryOp(op=statement.op,expr=simplifyCondition(statement.expr))
	elif type(statement) is c_ast.BinaryOp:
		return c_ast.BinaryOp(op=statement.op,left=simplifyCondition(statement.left), right=simplifyCondition(statement.right))
	else:
		return statement

"""

Method for Generate  Complement of Condition

"""


def getComplement(statement):
	if type(statement) is c_ast.UnaryOp:
		if statement.op=='!': 
			return simplifyCondition(statement.expr)
		else:
			return c_ast.UnaryOp(op=statement.op,expr=simplifyCondition(statement.expr))
	
	elif type(statement) is c_ast.BinaryOp:
		if statement.op=='<':
			return c_ast.BinaryOp(op='>=',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='>':
			return c_ast.BinaryOp(op='<=',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='<=':
			return c_ast.BinaryOp(op='>',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='>=':
			return c_ast.BinaryOp(op='<',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='!=':
			return c_ast.BinaryOp(op='==',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='==':
			return c_ast.BinaryOp(op='!=',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='&&':
			return c_ast.BinaryOp(op='||',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='||':
			return c_ast.BinaryOp(op='&&',left=getComplement(statement.left), right=getComplement(statement.right))
		else:
			return c_ast.BinaryOp(op=statement.op,left=getComplement(statement.left), right=getComplement(statement.right))


	else:
		return statement




"""

For Whole program

"""

def changeCondition(statement):
	if type(statement) is c_ast.ID:
		return c_ast.BinaryOp(op='>',left=statement,right=c_ast.Constant(type='int', value='0'))
	elif type(statement) is c_ast.Constant:
		return c_ast.BinaryOp(op='>',left=statement,right=c_ast.Constant(type='int', value='0'))
	elif type(statement) is c_ast.FuncCall:
		return c_ast.BinaryOp(op='>',left=statement,right=c_ast.Constant(type='int', value='0'))
	elif type(statement) is c_ast.ArrayRef:
		return c_ast.BinaryOp(op='>',left=statement,right=c_ast.Constant(type='int', value='0'))
	elif type(statement) is c_ast.UnaryOp:
		if statement.op=='!':
			if type(statement.expr) is c_ast.ID:
				return c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			elif type(statement.expr) is c_ast.Constant:
				return c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			elif type(statement.expr) is c_ast.FuncCall:
				return c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			elif type(statement.expr) is c_ast.ArrayRef:
				return c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			else:
				return statement
		else:
			return statement
	elif type(statement) is c_ast.BinaryOp:
                left_stmt=None
                right_stmt=None
                if statement.op=='||':
                    if type(statement.left) is c_ast.ID:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.Constant:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.FuncCall:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.ArrayRef:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    else:
                        left_stmt=changeCondition(statement.left)
                        
                    if type(statement.right) is c_ast.ID:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.Constant:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.FuncCall:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.ArrayRef:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    else:
                        right_stmt=changeCondition(statement.right)
                    return c_ast.BinaryOp(op=statement.op,left=left_stmt, right=right_stmt)
                elif statement.op=='&&':
                    if type(statement.left) is c_ast.ID:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.Constant:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.FuncCall:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.ArrayRef:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    else:
                        left_stmt=changeCondition(statement.left)
                        
                    if type(statement.right) is c_ast.ID:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.Constant:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.FuncCall:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.ArrayRef:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    else:
                        right_stmt=changeCondition(statement.right)
                    return c_ast.BinaryOp(op=statement.op,left=left_stmt, right=right_stmt)
                else:
                 	return statement
                        
		
	else:
		return statement




def modificationOfCondition(statement):
	if type(statement) is c_ast.ID:
		return True,statement
	elif type(statement) is c_ast.Constant:
		return True,statement
	elif type(statement) is c_ast.FuncCall:
		return True,statement
	elif type(statement) is c_ast.UnaryOp:
		if statement.op=='!':
			status,statement.expr=modificationOfCondition(statement.expr)
			if status==True:
				return False,c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			else:
				return True,statement
		else:
			return True,statement
	elif type(statement) is c_ast.BinaryOp:
		left_stmt=None
                right_stmt=None
		if statement.op=='||':
			status,left_stmt=modificationOfCondition(statement.left)
			if status==True:
				left_stmt=c_ast.BinaryOp(op='>',left=left_stmt,right=c_ast.Constant(type='int', value='0'))
			status=False
			status,right_stmt=modificationOfCondition(statement.right)
			if status==True:
				right_stmt=c_ast.BinaryOp(op='>',left=right_stmt,right=c_ast.Constant(type='int', value='0'))
			return False,c_ast.BinaryOp(op=statement.op,left=left_stmt, right=right_stmt)
		elif statement.op=='&&':
			status,left_stmt=modificationOfCondition(statement.left)
			if status==True:
				left_stmt=c_ast.BinaryOp(op='>',left=left_stmt,right=c_ast.Constant(type='int', value='0'))
			status=False
			status,right_stmt=modificationOfCondition(statement.right)
			if status==True:
				right_stmt=c_ast.BinaryOp(op='>',left=right_stmt,right=c_ast.Constant(type='int', value='0'))
			return False,c_ast.BinaryOp(op=statement.op,left=left_stmt, right=right_stmt)
		elif statement.op=='>':
			return False,statement
		elif statement.op=='<':
			return False,statement
		elif statement.op=='>=':
			return False,statement
		elif statement.op=='<=':
			return False,statement
		elif statement.op=='=':
			return False,statement
		elif statement.op=='==':
			return False,statement
		elif statement.op=='!=':
			return False,statement
		else:
			status1,left_stmt=modificationOfCondition(statement.left)
			status2,right_stmt=modificationOfCondition(statement.right)
			if status1==True and status2==True:
				return True,c_ast.BinaryOp(op=statement.op,left=left_stmt,right=right_stmt)
			else:
				return False,c_ast.BinaryOp(op=statement.op,left=left_stmt,right=right_stmt)
			
	else:
		return False,statement
		


def changeConditionProgram(statements):
	if statements is not None:
		update_statements=[]
		for statement in statements:
			if type(statement) is c_ast.If:
				update_statements.append(changeConditionProgramIf(statement))
			elif type(statement) is c_ast.While:
				update_statements.append(c_ast.While(cond=changeCondition(statement.cond),stmt=c_ast.Compound(block_items=changeConditionProgram(statement.stmt.block_items))))
			else:
				update_statements.append(statement)
		return update_statements			
	return None



def changeConditionProgramIf(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=changeConditionProgram(statement.iftrue.block_items))
			else:
				new_iftrue=statement.iftrue
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=changeConditionProgram(statement.iffalse.block_items))
			else:
				new_iftrue=statement.iffalse
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=changeConditionProgramIf(statement.iffalse)
		else:
			new_iffalse=statement.iffalse
	return c_ast.If(cond=changeCondition(statement.cond),iftrue=new_iftrue,iffalse=new_iffalse)




def simplifyProgram(statements):
	if statements is not None:
		update_statements=[]
		for statement in statements:
			if type(statement) is c_ast.If:
				update_statements.append(simplifyProgram_If(statement))
			elif type(statement) is c_ast.While:
				update_statements.append(c_ast.While(cond=simplifyCondition(statement.cond),stmt=c_ast.Compound(block_items=simplifyProgram(statement.stmt.block_items))))
			else:
				update_statements.append(statement)
		return update_statements			
	return None



def simplifyProgram_If(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=simplifyProgram(statement.iftrue.block_items))
			else:
				new_iftrue=statement.iftrue
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=simplifyProgram(statement.iffalse.block_items))
			else:
				new_iftrue=statement.iffalse
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=simplifyProgram_If(statement.iffalse)
		else:
			new_iffalse=statement.iffalse
	return c_ast.If(cond=simplifyCondition(statement.cond),iftrue=new_iftrue,iffalse=new_iffalse)



def removeDeadCode(statements):
	update_statements=[]
	flag=False
	if statements is not None:
		for statement in statements:
			if type(statement) is c_ast.Goto:
				flag=True
			elif type(statement) is c_ast.Label:
				flag=False
				stmts=statement.stmt
				if stmts is not None:
					for stmt in stmts:
						update_statements.append(stmt)
			else:
				if flag==False:
					update_statements.append(statement)
	return update_statements



def gotoremoval(statements):
	if statements is not None:
		label_map=constructLabelTable(statements,0,0,0)
		updateLabelTable(statements,0,0,0,label_map)
		keys=label_map.keys()
		for key in keys:
			labelMap={}
			listL=label_map[key]
			if len(listL[3])>1:
		    		statements=removeMultipleLabel(statements,key,labelMap)
		    		statements=addMultipleLabel(statements,key,labelMap)
		    		label_map=constructLabelTable(statements,0,0,0)
    				updateLabelTable(statements,0,0,0,label_map)
    			else:
    				if len(listL[3])==0:
					#statements=removeOrphanLabel(statements,key)
					label_map=constructLabelTable(statements,0,0,0)
    					updateLabelTable(statements,0,0,0,label_map)
    			
		label_map=constructLabelTable(statements,0,0,0)
    		updateLabelTable(statements,0,0,0,label_map)
    		
    		
		blank_label_map1={}
		blank_label_map2={}
		for element in label_map.keys():
			temp_list=label_map[element]
			temp_temp_list=temp_list[3]
			temp_temp_list1=[]
			temp_temp_list2=[]
			for iteam in temp_temp_list:
				if iteam[3] is not None:
					temp_temp_list1.append(iteam)
				else:
					temp_temp_list2.append(iteam)
			
			
			if len(temp_temp_list1)>0:
				temp_list1=[]
				temp_list1.append(temp_list[0])
				temp_list1.append(temp_list[1])
				temp_list1.append(temp_list[2])
				temp_list1.append(temp_temp_list1)
				blank_label_map1[element]=temp_list1
			
			if len(temp_temp_list2)>0:
				temp_list2=[]
				temp_list2.append(temp_list[0])
				temp_list2.append(temp_list[1])
				temp_list2.append(temp_list[2])
				temp_list2.append(temp_temp_list2)
				blank_label_map2[element]=temp_list2
		
		#print '$$$$$$$$$$$'
                #print statements
                #print '$$$$$$$$$$$'
		label_map=blank_label_map1
		keys=label_map.keys()
		if len(keys)>0:
			item=keys[0]
			element = label_map[item]
    			lists = element[3]
    			for list in lists:
    				if element[0]>=list[0] and element[1]>=list[1]:
                                        #print 'xxxxx1'
        				statements=goto_finder(statements,item)
                                        #print '$$$$$$$$$$$1'
                                        #generator = c_generator.CGenerator()
                                        #print(generator.visit(c_ast.Compound(block_items=statements)))
                                        #print item
                                        #print '$$$$$$$$$$$1'
    					statements=go_block_finder(statements,item)
    					statements=gotoremoval(statements)
    				else:
                                        if element[1]>=1:
                                                #print 'xxxxx2'
    						statements=label_finder_inside(statements,item)
    						statements=go_block_finder(statements,item)
       						statements=gotoremoval(statements)
       					else:
                                                #print 'xxxxx3'
						statements=label_finder(statements,item)
						statements=go_block_finder(statements,item)
       						statements=gotoremoval(statements)
    	return statements





#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label
testcount=0

def go_block_finder(statements,label):
	if statements is not None:
		flag_block_label=check_label_block(statements,label)  
		flag_block_goto=check_goto_block_Sp(statements,label)
		if flag_block_label==True and flag_block_goto==True:
                        #print 'XXXYYYYY1'
                        #print '#######jai shree ram'
                        #generator = c_generator.CGenerator() 
                        #print(generator.visit(c_ast.Compound(block_items=statements)))
                        #print '#######jai shree ram'
			return remove_goto_block(statements,label)
		else:
			update_statements=[]
                        #print 'XXXYYYYY2'
			for statement in statements:
				if type(statement) is c_ast.If:
					update_statements.append(go_block_finder_if(statement,label))
				elif type(statement) is c_ast.While:
					update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=go_block_finder(statement.stmt.block_items,label))))
				else:
					update_statements.append(statement)
		return update_statements
	return statements
				


#Finding Goto in a If Block to Call gotomovein
#Parameter pass statement 
#Label

def go_block_finder_if(statement,label):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=go_block_finder(statement.iftrue.block_items,label))
			else:
				new_iftrue=statement.iftrue
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=go_block_finder(statement.iffalse.block_items,label))
			else:
				new_iftrue=statement.iffalse
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=go_block_finder_if(statement.iffalse,label)
		else:
			new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond,iftrue=new_iftrue,iffalse=new_iffalse)






#Method to Remove Goto 


def remove_goto_block(statements,label): 
	flag_block_label=check_label_block(statements,label)  
	flag_block_goto=check_goto_block_Sp(statements,label)
	flag_block2,condition=check_goto(statements,label)
	flag_label=False
	flag_goto=False
	new_statements1=[]
	new_statements2=[]
	process_part1=False
	process_part2=False
	if flag_block_label==True and flag_block_goto==True:
                #print '#######1234'
                #generator = c_generator.CGenerator() 
                #print(generator.visit(c_ast.Compound(block_items=statements)))
                #print '#######1234'
		for statement in statements:
			#print type(statement)
			#print flag_label
			#print flag_goto
			if type(statement) is c_ast.Label:
				if label==statement.name:
					process_part2=True			
					if flag_goto==True:
                                                #print 'XXXX1'
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2),iffalse=None))
						if type(statement.stmt) is c_ast.Assignment:
							new_statements1.append(statement.stmt)
						elif type(statement.stmt) is c_ast.Compound:
							if statement.stmt is not None and statement.stmt.block_items is not None:
								for stmt in statement.stmt.block_items:
									new_statements1.append(stmt)
						else:
							new_statements1.append(statement.stmt)
						flag_label=False
						flag_goto=False
					else:
						#print 'XXXX2'
						if type(statement.stmt) is c_ast.Assignment:
							new_statements2.append(statement.stmt)
						elif type(statement.stmt) is c_ast.Compound:
							if statement.stmt is not None and statement.stmt.block_items is not None:
								for stmt in statement.stmt.block_items:
									new_statements2.append(stmt)
						
						#print '%%%%%%%%%%%%%%%%%%%%%%%%%'
                                                #print statement.stmt
                                                #for y in new_statements2:
                                                #    print y
                                                #print '%%%%%%%%%%%%%%%%%%%%%%%%%'
						flag_label=True
				else:
					if flag_goto==True or flag_label==True:
                                                #print 'XXXX3'
						if type(statement.stmt) is c_ast.Assignment:
                                                        new_statements2.append(c_ast.Label(name=statement.name, stmt=None))
							new_statements2.append(statement.stmt)
						elif type(statement.stmt) is c_ast.Compound:
                                                        new_statements2.append(c_ast.Label(name=statement.name, stmt=None))
							if statement.stmt is not None and statement.stmt.block_items is not None:
								for stmt in statement.stmt.block_items:
									new_statements2.append(stmt)
                                                else:
                                                    new_statements2.append(statement)
					else:
						new_statements1.append(statement)
			elif type(statement) is c_ast.If:
				flag_block_goto=check_goto_block_If(statement,label)
				if flag_block_goto:
					process_part1=True
					if flag_label==True:
                                                #print 'XXXX4'
                                                #print '$$$$$$$$$$$$$$$$$$1'
                                                #statement.show()
                                                #print '$$$$$$$$$$$$$$$$$$1'
						statement_1,statement_2=getRidOfGoto2(statement,label)
                                                #print '$$$$$$$$$$$$$$$$$$2'
                                                #print statement_1
                                                #print statement_2
                                                #statement.show()
                                                #print '$$$$$$$$$$$$$$$$$$'
						for stmt in new_statements2:
							new_statements1.append(stmt)
                    						
						new_break_map={}
                                                if statement_1 is not None:
                                                    new_statements2=new_statements2+statement_1
						new_statements2=reOrganizeBreaks(new_statements2,new_break_map)

						new_statements1.append(c_ast.While(cond=condition, stmt=c_ast.Compound(block_items=new_statements2)))
                                                new_statements1.append(statement_2)
						new_statements1=addingBreakVariables(new_statements1,new_break_map)
						flag_label=False
						flag_goto=False
					else:
						#print 'XXXX5'
                                                #print '#######12345'
                                                #generator = c_generator.CGenerator() 
                                                #print(generator.visit(statement))
                                                #print '#######12345'
						statement=getRidOfGoto(statement,label)
                                                #print '#######123456'
                                                #generator = c_generator.CGenerator() 
                                                #print(generator.visit(statement))
                                                #print '#######123456'
						new_statements1.append(statement)
						flag_goto=True
				else:
					if flag_goto==True or flag_label==True:
						new_statements2.append(statement)
					else:
						new_statements1.append(statement)
			else:
				if flag_goto==True or flag_label==True:
					new_statements2.append(statement)
				else:
					new_statements1.append(statement)
	
	#print '$$$$$$$$$$$$$$$$$4'
        #print process_part1
        #print process_part2
	#print '$$$$$$$$$$$$$$$$$4'
	if process_part1==True and process_part2==True:
		return new_statements1
	else:
		return None
		#return None
				
				
def remove_goto_block_sp(statements,label): 
	flag_block_label=check_label_block(statements,label)  
	flag_block_goto=check_goto_block_Sp(statements,label)
	flag_block2,condition=check_goto(statements,label)
	flag_label=False
	flag_goto=False
	new_statements1=[]
	new_statements2=[]
	if flag_block_label==True and flag_block_goto==True:
		for statement in statements:
			if type(statement) is c_ast.If:
				flag_block_goto=check_goto_block_If(statement,label)
				flag_label_sp=check_label_block_If(statement,label)  
				if flag_label_sp==True and flag_block_goto==False:
					new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2),iffalse=None))
					stmt=update_If_removegoto(statement,label,condition)
					new_statements1.append(stmt)
				elif flag_block_goto:
					if flag_label==True:
						statement=getRidOfGoto(statement,label)
						for stmt in new_statements2:
							new_statements1.append(stmt)
						new_statements1.append(statement)
						
						new_break_map={}
						new_statements2=reOrganizeBreaks(new_statements2,new_break_map)

						new_statements1.append(c_ast.While(cond=condition, stmt=c_ast.Compound(block_items=new_statements2)))
						new_statements1=addingBreakVariables(new_statements1,new_break_map)
						flag_label=False
						flag_goto=False
					else:
						statement=getRidOfGoto(statement,label)
						new_statements1.append(statement)
						flag_goto=True
				else:
					if flag_goto==True or flag_label==True:
						new_statements2.append(statement)
					else:
						new_statements1.append(statement)
			else:
				if flag_goto==True or flag_label==True:
					new_statements2.append(statement)
				else:
					new_statements1.append(statement)
	
	return new_statements1



def update_If_removegoto(statement,label,condition):
	new_if_stmt=None
	new_else_stmt=None
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Label:
				if statement.iftrue.name==label:
                                        new_statements=[]
                                        new_statements.append(c_ast.If(cond=condition,iftrue=c_ast.Goto(name=label),iffalse=None))
                                        new_statements.append(statement.iftrue)
                                        new_if_stmt=c_ast.Compound(block_items=remove_goto_block(new_statements,label))
                                else:
                                	new_if_stmt=statement.iftrue
                                        
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			status=False
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Label:
                                                        if element.name==label:
                                                                status = True
                                        if status==True:
                                        	new_statements=[]
                                        	new_statements.append(c_ast.If(cond=condition,iftrue=c_ast.Goto(name=label),iffalse=None))
                                        	for element in statement.iftrue.block_items:
                                        		new_statements.append(element)
                                        	new_if_stmt=c_ast.Compound(block_items=remove_goto_block(new_statements,label))
                                        else:
                                        	new_if_stmt=statement.iftrue
                                        		
                                                                
			if type(statement.iffalse) is c_ast.Label:
                                if statement.iffalse.name==label:
                                         new_statements=[]
					 new_statements.append(c_ast.If(cond=condition,iftrue=c_ast.Goto(name=label),iffalse=None))
					 new_statements.append(statement.iftrue)
                                         new_if_stmt=c_ast.Compound(block_items=remove_goto_block(new_statements,label))
                                else:
                                	new_else_stmt=statement.iffalse
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			status=False
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Label:
	            					if element.name==label:
                                                                status = True
                                        if status==True:
						new_statements=[]
					        new_statements.append(c_ast.If(cond=condition,iftrue=c_ast.Goto(name=label),iffalse=None))
					        for element in statement.iffalse.block_items:
					        	new_statements.append(element)
					        new_else_stmt=c_ast.Compound(block_items=remove_goto_block(new_statements,label))
					else:
                                        	new_else_stmt=statement.iffalse
				else:
					if type(statement.iffalse) is c_ast.If:
						new_else_stmt=update_If_removegoto(statement.iffalse,label,condition)
	return c_ast.If(cond=c_ast.BinaryOp(op='&&', left=statement.cond, right=condition),iftrue=new_if_stmt,iffalse=new_else_stmt)







    
    
def constructLabelTable(statements,level,block,lineCount):
	label_map={}
	if statements is not None:
		for statement in statements:
			if type(statement) is c_ast.If:
				block=block+1
				label_map_temp=constructLabelTable_If(statement,level,block,lineCount)
	            		for item in label_map_temp:
            				label_map[item]=label_map_temp[item]
            			block=block-1
			elif type(statement) is c_ast.Label:
				lineCount=lineCount+1
			        info=[]
			        info.append(level)
	            		info.append(block)
	            		info.append(lineCount)
	            		info.append([])
				label_map[statement.name]=info
	        	else:
	        		if type(statement) is c_ast.While:
	        			level=level+1
	            			label_map_temp=constructLabelTable(statement.stmt.block_items,level,block,lineCount)
	            			for item in label_map_temp:
            					label_map[item]=label_map_temp[item]
            				level=level-1
            			else:
            				lineCount=lineCount+1
	return label_map




def constructLabelTable_If(statement,level,block,lineCount):
	label_map={}
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Label:
				lineCount=lineCount+1	            				
				info=[]
				info.append(level)
				info.append(block)
				info.append(lineCount)
				info.append([])
				label_map[statement.iftrue.name]=info
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Label:
							lineCount=lineCount+1	            				
	            					info=[]
	            					info.append(level)
	            					info.append(block)
	            					info.append(lineCount)
	            					info.append([])
	            					label_map[element.name]=info
	            				elif type(element) is c_ast.If:
	            					block=block+1
							label_map_temp=constructLabelTable_If(element,level,block,lineCount)
							for item in label_map_temp:
            							label_map[item]=label_map_temp[item]
            						block=block-1
						else:
							if type(element) is c_ast.While:
								level=level+1
						        	label_map_temp=constructLabelTable(element.stmt.block_items,level,block,lineCount)
						        	for item in label_map_temp:
					            			label_map[item]=label_map_temp[item]
            							level=level-1
            						else:
            							lineCount=lineCount+1
	
			if type(statement.iffalse) is c_ast.Label:
				lineCount=lineCount+1	            				
				info=[]
				info.append(level)
				info.append(block)
				info.append(lineCount)
				info.append([])
				label_map[statement.iffalse.name]=statement.iffalse.name
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Label:
	            					lineCount=lineCount+1
	            					info=[]
							info.append(level)
	            					info.append(block)
	            					info.append(lineCount)
	            					info.append([])
	            					label_map[element.name]=info
	            				elif type(element) is c_ast.If:
	            					block=block+1
							label_map_temp=constructLabelTable_If(element,level,block,lineCount)
							for item in label_map_temp:
            							label_map[item]=label_map_temp[item]
            						block=block-1
						else:
							if type(element) is c_ast.While:
								level=level+1
						        	label_map_temp=constructLabelTable(element.stmt.block_items,level,block,lineCount)
						        	for item in label_map_temp:
					            			label_map[item]=label_map_temp[item]
            							level=level-1
            						else:
            							lineCount=lineCount+1
				else:
					if type(statement.iffalse) is c_ast.If:
						label_map_temp=constructLabelTable_If(statement.iffalse,level,block,lineCount)
						for item in label_map_temp:
							label_map[item]=label_map_temp[item]
	return label_map

    
    

def updateLabelTable(statements,level,block,lineCount,label_map):
	if statements is not None:
		for statement in statements:
			if type(statement) is c_ast.If:
				updateLabelTable_If(statement,level,block,lineCount,label_map)
	        	else:
	        		if type(statement) is c_ast.While:
	        			level=level+1
	            			updateLabelTable(statement.stmt.block_items,level,block,lineCount,label_map)
            				level=level-1
            			elif type(statement) is c_ast.Goto:
                                    lineCount=lineCount+1	            				
                                    info=[]
                                    info.append(level)
                                    info.append(block)
                                    info.append(lineCount)
                                    info.append(None)
                                    if statement.name in label_map.keys():
					info_update=label_map[statement.name]
				        list=info_update[3]
				        list.append(info)	
            			
            			else:
            				lineCount=lineCount+1





def updateLabelTable_If(statement,level,block,lineCount,label_map):
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Goto:
				lineCount=lineCount+1	            				
				info=[]
				info.append(level)
				info.append(block)
				info.append(lineCount)
				info.append(statement.cond)
				if statement.iftrue.name in label_map.keys():
					info_update=label_map[statement.iftrue.name]
				        list=info_update[3]
				        list.append(info)		

			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Goto:
							lineCount=lineCount+1	            				
	            					info=[]
	            					info.append(level)
	            					info.append(block)
	            					info.append(lineCount)
	            					info.append(statement.cond)
	            					if element.name in label_map.keys():
	            						info_update=label_map[element.name]
	            						list=info_update[3]
	            						list.append(info)
	            				elif type(element) is c_ast.If:
	            					block=block+1
							updateLabelTable_If(element,level,block,lineCount,label_map)
            						block=block-1
						else:
							if type(element) is c_ast.While:
								level=level+1
						        	updateLabelTable(element.stmt.block_items,level,block,lineCount,label_map)
            							level=level-1
            						else:
            							lineCount=lineCount+1
	
			if type(statement.iffalse) is c_ast.Goto:
				lineCount=lineCount+1	            				
				info=[]
				info.append(level)
				info.append(block)
				info.append(lineCount)
				info.append(statement.cond)
				if statement.iffalse.name in label_map.keys():
					info_update=label_map[statement.iffalse.name]
					list=info_update[3]
					list.append(info)
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Goto:
	            					lineCount=lineCount+1
	            					info=[]
							info.append(level)
	            					info.append(block)
	            					info.append(lineCount)
	            					info.append(statement.cond)
	            					if element.name in label_map.keys():
	            						info_update=label_map[element.name]
	            						list=info_update[3]
	            						list.append(info)
	            				elif type(element) is c_ast.If:
	            					block=block+1
							updateLabelTable_If(element,level,block,lineCount,label_map)
            						block=block-1
						else:
							if type(element) is c_ast.While:
								level=level+1
						        	updateLabelTable(element.stmt.block_items,level,block,lineCount,label_map)
            							level=level-1
            						else:
            							lineCount=lineCount+1
				else:
					if type(statement.iffalse) is c_ast.If:
						updateLabelTable_If(statement.iffalse,level,block,lineCount,label_map)
					
					
#Check a label in a block of statement


def check_label_block(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.If:
                        temp_status=check_label_block_If(statement,label)
                        if temp_status==True:
                               status=True 
		elif type(statement) is c_ast.Label:
                        if statement.name==label:
                                status = True
	return status
	



def check_label_block_sp(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.Label:
                        if statement.name==label:
                                status = True
	return status

#Check a label in the blocks of statement of if loop
	
def check_label_block_If(statement,label):
        status=False
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Label:
				if statement.iftrue.name==label:
                                        status = True
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Label:
                                                        if element.name==label:
                                                                status = True
                                                                
			if type(statement.iffalse) is c_ast.Label:
                                if statement.iffalse.name==label:
                                        status = True
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Label:
	            					if element.name==label:
                                                                status = True
				else:
					if type(statement.iffalse) is c_ast.If:
						temp_status = check_label_block_If(statement.iffalse,label)
						if temp_status==True:
                                                	status=True
	return status



#Check a label in statement


def check_label(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.If:
                        temp_status=check_label_If(statement,label)
                        if temp_status==True:
                               status=True 
		elif type(statement) is c_ast.Label:
                        if statement.name==label:
                                status = True
	        else:
	        	if type(statement) is c_ast.While:
	            		temp_status= check_label(statement.stmt.block_items,label)
	            		if temp_status==True:
                                        status=True
	return status



def check_label_sp(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.If:
                        temp_status=check_label_If(statement,label)
                        if temp_status==True:
                               status=True 
		elif type(statement) is c_ast.Label:
                        if statement.name==label:
                                status = True
	return status



#Check a label in statement of if loop

def check_label_If(statement,label):
        status=False
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Label:
				if statement.iftrue.name==label:
                                        status = True
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Label:
                                                        if element.name==label:
                                                                status = True
	            				elif type(element) is c_ast.If:
							temp_status = check_label_If(element,label)
							if temp_status==True:
                                                               status=True
						else:
							if type(element) is c_ast.While:
						        	temp_status = check_label(element.stmt.block_items,label)
						        	if temp_status==True:
                                                                        status=True
	
			if type(statement.iffalse) is c_ast.Label:
                                if statement.iffalse.name==label:
                                        status = True
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Label:
	            					if element.name==label:
                                                                status = True
	            				elif type(element) is c_ast.If:
                                                        temp_status = check_label_If(element,label)
                                                        if temp_status==True:
                                                                status=True
						else:
							if type(element) is c_ast.While:
								temp_status = check_label(element.stmt.block_items,label)
								if temp_status==True:
                                                                        status=True

				else:
					temp_status = check_label_If(statement.iffalse,label)
					if temp_status==True:
                                                status=True
	return status





#Check a goto-label in a block of statement


def check_goto_block(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.Goto:
                        if statement.name==label:
                                status = True

	return status


def check_goto_block_Sp(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.Goto:
                        if statement.name==label:
                                status = True
               	elif type(statement) is c_ast.If:
                	temp_status=check_goto_block_If(statement,label)
                	if temp_status==True:
                		status=True
	return status
	
	

#Check a label in the blocks of statement of if loop
	
def check_goto_block_If(statement,label):
        status=False
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Goto:
				if statement.iftrue.name==label:
                                        status = True
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Goto:
                                                        if element.name==label:
                                                                status = True
			if type(statement.iffalse) is c_ast.Label:
                                if statement.iffalse.name==label:
                                        status = True
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Goto:
	            					if element.name==label:
                                                                status = True
				else:
					if type(statement.iffalse) is c_ast.If:
						temp_status = check_goto_block_If(statement.iffalse,label)
						if temp_status==True:
                                                	status=True
	return status



#Check a label in statement


def check_goto(statements,label):
        status=False
        condition=None
	for statement in statements:
		if type(statement) is c_ast.If:
                        temp_status,temp_cond=check_goto_If(statement,label)
                        if temp_status==True:
                               status=True
                               condition=temp_cond
		elif type(statement) is c_ast.Goto:
                        if statement.name==label:
                                status = True
	        else:
	        	if type(statement) is c_ast.While:
	            		temp_status,temp_cond= check_goto(statement.stmt.block_items,label)
	            		if temp_status==True:
                                        status=True
                                        condition=temp_cond
	return status,condition




#Check a label in statement of if loop

def check_goto_If(statement,label):
        status=False
        condition=None
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Goto:
				if statement.iftrue.name==label:
                                        status = True
                                        condition=statement.cond
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Goto:
                                                        if element.name==label:
                                                                status = True
                                                                condition=statement.cond
	            				elif type(element) is c_ast.If:
							temp_status,temp_cond = check_goto_If(element,label)
							if temp_status==True:
                                                               status=True
                                                               #condition=temp_cond
                                                               condition=c_ast.BinaryOp(op='&&', left=temp_cond, right=statement.cond)
						else:
							if type(element) is c_ast.While:
						        	temp_status,temp_cond = check_goto(element.stmt.block_items,label)
						        	if temp_status==True:
                                                                        status=True
                                                                        condition=temp_cond
	
			if type(statement.iffalse) is c_ast.Goto:
                                if statement.iffalse.name==label:
                                        status = True
                                        condition = c_ast.UnaryOp(op='!', expr=statement.cond)
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Goto:
	            					if element.name==label:
                                                                status = True
                                                                condition = c_ast.UnaryOp(op='!', expr=statement.cond)
	            				elif type(element) is c_ast.If:
                                                        temp_status,temp_cond = check_goto_If(element,label)
                                                        if temp_status==True:
                                                                status=True
                                                                #condition=temp_cond
                                                                condition=c_ast.BinaryOp(op='&&', left=temp_cond, right=c_ast.UnaryOp(op='!', expr=statement.cond))
						else:
							if type(element) is c_ast.While:
								temp_status,temp_cond = check_goto(element.stmt.block_items,label)
								if temp_status==True:
                                                                        status=True
                                                                        condition=temp_cond

				else:
					temp_status,temp_cond = check_goto_If(statement.iffalse,label)
					if temp_status==True:
                                                status=True
                                                #condition=temp_cond
                                                condition=c_ast.BinaryOp(op='&&', left=temp_cond, right=c_ast.UnaryOp(op='!', expr=statement.cond))
	return status,condition






#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label


def label_finder(statements,label):
	if statements is not None:
		flag_block1=check_label_block(statements,label)
		if flag_block1==True:
			return gotomoveout(statements,label)
		else:
			update_statements=[]
			if statements is not None:
				for statement in statements:
					if type(statement) is c_ast.If:
						update_statements.append(label_finder_if(statement,label))
					elif type(statement) is c_ast.While:
						update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=label_finder(statement.stmt.block_items,label))))
					else:
						update_statements.append(statement)
				return update_statements
			return statements
	return statements
				




#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label


def label_finder_inside(statements,label):
	if statements is not None:
		flag_block1=check_label_block(statements,label)
		flag_block2=check_label_block_sp(statements,label)
		flag_block3=check_goto_block_Sp(statements,label)
		#if flag_block1==False and flag_block2==False and flag_block3==False:
		if flag_block2==False and flag_block3==False:
			status,condition=check_goto(statements,label)
			if status==True:
				statements=gotomoveout_inside(statements,label)
				flag_block1=check_label_block(statements,label)
				flag_block2=check_label_block_sp(statements,label)
				flag_block3=check_goto_block_Sp(statements,label)
				#if flag_block1==False and flag_block2==False and flag_block3==True:
				if flag_block2==False and flag_block3==True:
					statements=gotomovein(statements,label)
	return statements







#Finding Goto in a If Block to Call gotomovein
#Parameter pass statement 
#Label

def label_finder_if(statement,label):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=label_finder(statement.iftrue.block_items,label))
			else:
				new_iftrue=statement.iftrue
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=label_finder(statement.iffalse.block_items,label))	
			else:
				new_iffalse=statement.iffalse
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=label_finder_if(statement.iffalse,label)
		else:
			new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond,iftrue=new_iftrue,iffalse=new_iffalse)






#Method to Move Goto Outside
#Parameter pass statement 
#Label


def gotomoveout(statements,label):
	flag_block1=check_label_block(statements,label)
	update_statements=[]
	condition=None
	if flag_block1==True:
		for statement in statements:
			if type(statement) is c_ast.If:
				flag_block2,condition=check_goto_If(statement,label)
				flag_stmt2=check_goto_block_If(statement,label)
				if flag_block2==True and flag_stmt2==False:
					statement=gotomoveoutrec_if(statement,label)
			                update_statements.append(statement)
			                update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
				elif flag_block2==True and flag_stmt2==True:
					statement=getRidOfGoto(statement,label)
			                if statement is not None:
			                	update_statements.append(statement)
			                	update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
			        else:
					update_statements.append(statement)
			
			elif type(statement) is c_ast.While:
				flag_block2,condition=check_goto(statement.stmt.block_items,label)
				flag_stmt2=check_goto_block(statement.stmt.block_items,label)
				if flag_block2==True and flag_stmt2==False:
					stmts=gotomoveoutrec(statement.stmt.block_items,label)
					stmts.append(c_ast.If(cond=condition, iftrue=c_ast.Break(), iffalse=None))
					statement=c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=stmts))
					update_statements.append(statement)
					update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
				elif flag_block2==True and flag_stmt2==True:
			                update_statements.append(statement)
			        else:
					update_statements.append(statement)
			                       
			else:
				update_statements.append(statement)
                                
		return update_statements




#Method to Move Goto Outside
#Parameter pass statement 
#Label


def gotomoveout_inside(statements,label):
	update_statements=[]
	condition=None
	for statement in statements:
		if type(statement) is c_ast.If:
			flag_block2,condition=check_goto_If(statement,label)
			flag_stmt2=check_goto_block_If(statement,label)
			if flag_block2==True and flag_stmt2==False:
				statement=gotomoveoutrec_if(statement,label)
			        update_statements.append(statement)
			        update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
			elif flag_block2==True and flag_stmt2==True:
				statement=getRidOfGoto(statement,label)
			        if statement is not None:
			                update_statements.append(statement)
			                update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
			else:
				update_statements.append(statement)
			
		elif type(statement) is c_ast.While:
			flag_block2,condition=check_goto(statement.stmt.block_items,label)
			flag_stmt2=check_goto_block(statement.stmt.block_items,label)
			if flag_block2==True and flag_stmt2==False:
				stmts=gotomoveoutrec(statement.stmt.block_items,label)
				stmts.append(c_ast.If(cond=condition, iftrue=c_ast.Break(), iffalse=None))
				statement=c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=stmts))
				update_statements.append(statement)
				update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
			elif flag_block2==True and flag_stmt2==True:
			        update_statements.append(statement)
			else:
				update_statements.append(statement)
			                       
		else:
			update_statements.append(statement)
                                
	return update_statements












#Method to Move Goto Outside Recursive
#Parameter pass statement 
#Label

def gotomoveoutrec(statements,label):
	new_statements1=[]
	new_statements2=[]
	flag=False
	condition=None
	for statement in statements:
		if type(statement) is c_ast.If:
			flag_block2,condition_new=check_goto_If(statement,label)
			flag_stmt2=check_goto_block_If(statement,label)
			if condition_new is not None:
				condition=condition_new
			if flag_block2==True and flag_stmt2==False:
				statement=gotomoveoutrec_if(statement,label)
                        	new_statements1.append(statement)
                        	flag=True
			elif flag_block2==True and flag_stmt2==True:
				statement=getRidOfGoto(statement,label)
                                flag=True
                                if statement is not None:
                                	new_statements1.append(statement)
                        else:
                        	if flag==True:
					new_statements2.append(statement)
				else:
                        		new_statements1.append(statement)

		elif type(statement) is c_ast.While:
			flag_block2,condition_new=check_goto(statement.stmt.block_items,label)
			flag_stmt2=check_goto_block(statement.stmt.block_items,label)
			if condition_new is not None:
				condition=condition_new
			if flag_block2==True and flag_stmt2==False:
				stmts=gotomoveoutrec(statement.stmt.block_items,label)
				stmts.append(c_ast.If(cond=condition, iftrue=c_ast.Break(), iffalse=None))
				statement=c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=stmts))
				new_statements1.append(statement)
			elif flag_block2==True and flag_stmt2==True:
                                flag=True
                                new_statements1.append(statement)
                        else:
                        	if flag==True:
					new_statements2.append(statement)
				else:
                        		new_statements1.append(statement)
                       
                else:
                	if flag==True:
				new_statements2.append(statement)
			else:
                        	new_statements1.append(statement)
	if condition is not None:
                if len(new_statements2)>0:
                	new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
        	statements=new_statements1

        return statements



#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label
				
				
def gotomoveoutrec_if(statement,label):
	#print statement.show()
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Goto:
			if statement.iftrue.name==label:
	                	status = True
		else:
		        if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
		        	flag_block2,condition=check_goto(statement.iftrue.block_items,label)
				flag_stmt2=check_goto_block(statement.iftrue.block_items,label)
				if flag_block2==True and flag_stmt2==False:
					statement.iftrue.block_items=gotomoveoutrec(statement.iftrue.block_items,label)
					statement.iftrue=c_ast.Compound(block_items=statement.iftrue.block_items)
				elif flag_block2==True and flag_stmt2==True:
					statement.iftrue=c_ast.Compound(block_items=statement.iftrue.block_items)
	                                                                
		if type(statement.iffalse) is c_ast.Label:
	        	if statement.iffalse.name==label:
	                	status = True
		else:
			if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
				flag_block2,condition=check_goto(statement.iffalse.block_items,label)
				flag_stmt2=check_goto_block(statement.iffalse.block_items,label)
				if flag_block2==True and flag_stmt2==False:
					statement.iffalse.block_items=gotomoveoutrec(statement.iffalse.block_items,label)
					statement.iffalse=c_ast.Compound(block_items=statement.iffalse.block_items)
				elif flag_block2==True and flag_stmt2==True:
					statement.iffalse=c_ast.Compound(block_items=statement.iffalse.block_items)
			else:
				if type(statement.iffalse) is c_ast.If: 
					gotomoveoutrec_if(statement.iffalse,label)
	#print statement.show()
	return c_ast.If(cond=statement.cond, iftrue=statement.iftrue, iffalse=statement.iffalse)
				



#Updating Each If Else for Goto
#Parameter pass statement 
#Label
		
	
def getRidOfGoto(statement,label):
	generator = c_generator.CGenerator()
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Goto:
			if statement.iftrue.name==label:
	                	new_iftrue=None
		else:
		        if type(statement.iftrue) is c_ast.Compound:
		        	new_block=[]
				for stmt in statement.iftrue.block_items:
					if type(stmt) is c_ast.Goto:
						if stmt.name!=label:
							new_block.append(stmt)
					else:
						
						if stmt is not None:
                                                    if type(stmt) is c_ast.Label:
                                                        if stmt.name!=label:
                                                            new_block.append(stmt)
                                                    else: 
                                                        new_block.append(stmt)
				new_iftrue=c_ast.Compound(block_items=new_block)
                                     
		
		if type(statement.iffalse) is c_ast.Label:
	        	if statement.iffalse.name==label:
	                	new_iffalse=None
		else:
			if type(statement.iffalse) is c_ast.Compound:
				new_block=[]
				for stmt in statement.iffalse.block_items:
					if type(stmt) is c_ast.Goto:
						if stmt.name!=label:
							new_block.append(stmt)
					else:
						if stmt is not None:
                                                    if type(stmt) is c_ast.Label and stmt.name!=label:
                                                        new_block.append(stmt)
                                                    else: 
                                                        new_block.append(stmt)

				new_iffalse=c_ast.Compound(block_items=new_block)
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=getRidOfGoto(statement.iffalse,label)
	if new_iftrue is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	else:
		return None


def getRidOfGoto2(statement,label):
	generator = c_generator.CGenerator()
	new_iftrue=None
	new_iffalse=None
        up_statemets=[]
        down_statemets=[]
        up_statemets_else=[]
        down_statemets_else=[]
        flag=False
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Goto:
			if statement.iftrue.name==label:
	                	new_iftrue=None
		else:
		        if type(statement.iftrue) is c_ast.Compound:
                                up_statemets=[]
                                down_statemets=[]
				for stmt in statement.iftrue.block_items:
                                        
                                        if stmt is not None:
                                            if type(stmt) is c_ast.Goto:
                                                    if stmt.name!=label:
                                                            if flag==False:
                                                                up_statemets.append(stmt)
                                                            else:
                                                                down_statemets.append(stmt)
                                                    else:
                                                        flag==True
                                                            
                                            else:
                                                    if flag==False:
                                                        up_statemets.append(stmt)
                                                    else:
                                                        down_statemets.append(stmt)
				
				if len(down_statemets)==0:
                                    new_iftrue=None
                                else:
                                    new_iftrue=c_ast.Compound(block_items=down_statemets)
                                     
		if type(statement.iffalse) is c_ast.Label:
	        	if statement.iffalse.name==label:
	                	new_iffalse=None
		else:
			if type(statement.iffalse) is c_ast.Compound:
				new_block=[]
				for stmt in statement.iffalse.block_items:
					if type(stmt) is c_ast.Goto:
						if stmt.name!=label:
							new_block.append(stmt)
					else:
						new_block.append(stmt)
				new_iffalse=c_ast.Compound(block_items=new_block)
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=getRidOfGoto(statement.iffalse,label)
	if new_iftrue is not None:
                if len(up_statemets)==0:
                    return None,up_statemets,c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
                else:
                    return up_statemets,c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	elif new_iftrue is None and new_iffalse is not None:
		if len(up_statemets)==0:
                    return None,c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
                else:
                    return up_statemets,c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
	else:
		if len(up_statemets)==0:
                    return None,None
                else:
                    return up_statemets,None



#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label


def goto_finder(statements,label):
	flag_block1=check_goto_block_Sp(statements,label)
	if flag_block1==True:
		flag_block1=check_label_block_sp(statements,label)
		if flag_block1==True:
			return statements
		else:
			return gotomovein(statements,label)
	else:
		update_statements=[]
		for statement in statements:
			if type(statement) is c_ast.If:
				update_statements.append(goto_finder_if(statement,label))
			elif type(statement) is c_ast.While:
				update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=goto_finder(statement.stmt.block_items,label))))
			else:
				update_statements.append(statement)
		return update_statements


#Finding Goto in a If Block to Call gotomovein
#Parameter pass statement 
#Label

def goto_finder_if(statement,label):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Compound:
				if statement.iftrue.block_items is not None:
					new_iftrue=c_ast.Compound(block_items=goto_finder(statement.iftrue.block_items,label))
				else:
					new_iftrue=statement.iftrue				
			else:
				new_iftrue=statement.iftrue
			if type(statement.iffalse) is c_ast.Compound:
				if statement.iffalse.block_items is not None:
					new_iffalse=c_ast.Compound(block_items=goto_finder(statement.iffalse.block_items,label))
				else:
					new_iffalse=statement.iffalse
			elif type(statement.iffalse) is c_ast.If:
				new_iffalse=goto_finder_if(statement.iffalse,label)
			else:
				new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond,iftrue=new_iftrue,iffalse=new_iffalse)




#Method to Move Goto Inside
#Parameter pass statement 
#Label

def gotomovein(statements,label):
	flag_block1=check_goto_block_Sp(statements,label)
	new_statements1=[]
	new_statements2=[]
	flag=False
	if flag_block1==True:
		flag_block1,condition=check_goto(statements,label)
		for statement in statements:
			if type(statement) is c_ast.If:
				flag_stmt3=check_goto_block_If(statement,label)				
				flag_block2=check_label_If(statement,label)
				flag_stmt2=check_label_block_If(statement,label)
				if flag_stmt3==True:
					if flag_block2==True and flag_stmt2==True:
						new_statements1.append(statement)
					else:
						para_list=[]
                                                para_list.append(condition)
						newFun=c_ast.FuncCall(name=c_ast.ID(name='_Bool2Int'), args=c_ast.ExprList(exprs=para_list))
						new_statement=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='bool_go_'+label), rvalue=newFun)
						new_variable['bool_go_'+label]='bool_go_'+label
						condition=c_ast.BinaryOp(op='>', left=c_ast.ID(name='bool_go_'+label), right=c_ast.Constant(type='int', value='0'))
						new_statements1.append(new_statement)
						flag=True
				else:
					if flag_block2==True and flag_stmt2==False:
						flag=False
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
						new_statements1.append(updateIfBlock(statement,label,condition))

						new_statements2=[]
					else:
						if flag_block2==True and flag_stmt2==True:
							flag=False
							new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
							new_statements1.append(updateIfBlock(statement,label,condition))
							new_statements2=[]
						else:
							if flag==False:
								new_statements1.append(statement)
							else:
								new_statements2.append(statement)
			elif type(statement) is c_ast.While:
				flag_block2=check_label(statement.stmt.block_items,label)
				#flag_stmt2=check_label_block(statement.stmt.block_items,label)
				flag_stmt2=check_label_block_sp(statement.stmt.block_items,label)			
				if flag_block2==False and flag_stmt2==False:
					statement=c_ast.While(cond=statement.cond, stmt=statement.stmt)
				elif flag_block2==True and flag_stmt2==True:
					if len(new_statements2)>0:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
					new_cond=c_ast.BinaryOp(op='||', left=condition, right=statement.cond)
					new_blocks=[]
					new_blocks.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.stmt.block_items:
						new_blocks.append(stmt)
					new_blocks.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='bool_go_'+label) , rvalue= c_ast.Constant(type='int', value='0')))
					statement=c_ast.While(cond=new_cond, stmt=c_ast.Compound(block_items=new_blocks))
					flag=False
					new_statements2=[]
				elif flag_block2==True and flag_stmt2==False:
					if len(new_statements2)>0:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
					new_cond=c_ast.BinaryOp(op='||', left=condition, right=statement.cond)
					new_blocks=[]
					new_blocks.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.stmt.block_items:
						new_blocks.append(stmt)
					new_blocks.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='bool_go_'+label) , rvalue= c_ast.Constant(type='int', value='0')))
					new_blocks=gotomoveinrec(new_blocks,label,condition)
					statement=c_ast.While(cond=new_cond, stmt=c_ast.Compound(block_items=new_blocks))
					flag=False
					new_statements2=[]
				else:
					statement=c_ast.While(cond=statement.cond, stmt=statement.stmt)
				if flag==False:
					new_statements1.append(statement)
				else:
					new_statements2.append(statement)
			else:
				if flag==False:
					new_statements1.append(statement)
				else:
					new_statements2.append(statement)

		return new_statements1
	else:
		return statements



#Method to Move Goto Inside Recursive 
#Parameter pass statement 
#Label


def gotomoveinrec(statements,label,condition):
	flag_block1,condition=check_goto(statements,label)
	new_statements1=[]
	new_statements2=[]
	flag=False
	if flag_block1==True:
		for statement in statements:
			if type(statement) is c_ast.If:
				flag_stmt3=check_goto_block_If(statement,label)				
				flag_block2=check_label_If(statement,label)
				flag_stmt2=check_label_block_If(statement,label)
				if flag_stmt3==True:
					if flag_block2==True and flag_stmt2==True:
						new_statements1.append(statement)
					else:
						flag=True
				else:
					if flag_block2==True and flag_stmt2==False:
						flag=False
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
						new_statements1.append(updateIfBlock(statement,label,condition))

						new_statements2=[]
					else:
						if flag_block2==True and flag_stmt2==True:
							flag=False
							if len(new_statements2)>0:
								new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
							new_statements1.append(updateIfBlock(statement,label,condition))
							new_statements2=[]
						else:
							if flag==False:
								new_statements1.append(statement)
							else:
								new_statements2.append(statement)
			elif type(statement) is c_ast.While:
				flag_block2=check_label(statement.stmt.block_items,label)
				#flag_stmt2=check_label_block(statement.stmt.block_items,label)
				flag_stmt2=check_label_block_sp(statement.stmt.block_items,label)
				if flag_block2==False and flag_stmt2==False:
					statement=c_ast.While(cond=statement.cond, stmt=statement.stmt)
				elif flag_block2==True and flag_stmt2==True:
					if len(new_statements2)>0:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
					new_cond=c_ast.BinaryOp(op='||', left=condition, right=statement.cond)
					new_blocks=[]
					new_blocks.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.stmt.block_items:
						new_blocks.append(stmt)
					new_blocks.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='bool_go_'+label) , rvalue= c_ast.Constant(type='int', value='0')))
					statement=c_ast.While(cond=new_cond, stmt=c_ast.Compound(block_items=new_blocks))
					flag=False
					new_statements2=[]
				elif flag_block2==True and flag_stmt2==False:
					if len(new_statements2)>0:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
					new_cond=c_ast.BinaryOp(op='||', left=condition, right=statement.cond)
					new_blocks=[]
					new_blocks.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.stmt.block_items:
						new_blocks.append(stmt)
					new_blocks.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='bool_go_'+label) , rvalue= c_ast.Constant(type='int', value='0')))
					new_blocks=gotomoveinrec(new_blocks,label,condition)
					statement=c_ast.While(cond=new_cond, stmt=c_ast.Compound(block_items=new_blocks))
					flag=False
					new_statements2=[]
				else:
					statement=c_ast.While(cond=statement.cond, stmt=statement.stmt)
				if flag==False:
					new_statements1.append(statement)
				else:
					new_statements2.append(statement)
			else:
				if flag==False:
					new_statements1.append(statement)
				else:
					new_statements2.append(statement)
		return new_statements1
	else:
		return statements




#Updating Each If Else for Goto
#Parameter pass statement 
#Label

def updateIfBlock(statement,label,condition):
	new_iftrue=None
	new_iffalse=None
	new_condtion=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Goto:
			if statement.iftrue.name==label:
				new_block=[]
				new_block.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
				new_block.append(statement.iftrue)
		        	new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.Compound:
				flag_stmt=check_label(statement.iftrue.block_items,label)
				flag_stmt_block=check_label_block_sp(statement.iftrue.block_items,label)
			        if flag_stmt==True:
			        	new_block=[]
			        	new_block.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.iftrue.block_items:
						new_block.append(stmt)
					if flag_stmt_block==False:
						new_block=gotomoveinrec(new_block,label,condition)
					new_iftrue=c_ast.Compound(block_items=new_block)
				else:
					new_condtion=c_ast.BinaryOp(op='&&', left=c_ast.UnaryOp(op='!', expr=condition), right=statement.cond)
					new_iftrue=statement.iftrue
                         
			
		if type(statement.iffalse) is c_ast.Label:
			new_block=[]
			new_block.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
			new_block.append(statement.iffalse)
		        new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iffalse) is c_ast.Compound:
				flag_stmt=check_label(statement.iffalse.block_items,label)
				flag_stmt_block=check_label_block_sp(statement.iffalse.block_items,label)
				if flag_stmt==True:
			        	new_block=[]
			        	new_block.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.iffalse.block_items:
						new_block.append(stmt)
					if flag_stmt_block==False:
						new_block=gotomoveinrec(new_block,label,condition)
					new_iffalse=c_ast.Compound(block_items=new_block)
				else:
					new_condtion=c_ast.BinaryOp(op='&&', left=c_ast.UnaryOp(op='!', expr=condition), right=statement.cond)
					new_iffalse=statement.iffalse
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=updateIfBlock(statement.iffalse,label,condition)
	if new_condtion is not None:
		return c_ast.If(cond=new_condtion, iftrue=new_iftrue, iffalse=new_iffalse)
	else:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	
	
	

def reOrganizeBreaks(statements,new_break_map):
	update_statement=[]
	if statements is not None:
		for statement in statements:
			if type(statement) is c_ast.If:
				statement=reOrganizeBreaksIf(statement,new_break_map)
				update_statement.append(statement)
			elif type(statement) is c_ast.Break:
				update_statement.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='do_break'+str(len(new_break_map.keys())+1)), rvalue=c_ast.Constant(type='int', value='1')))
				new_break_map['do_break'+str(len(new_break_map.keys())+1)]='do_break'+str(len(new_break_map.keys())+1)
				update_statement.append(statement)
			else:
				update_statement.append(statement)
		return update_statement
	else:
		return None


def reOrganizeBreaksIf(statement,new_break_map):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Break:
			new_block=[]
			new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='do_break'+str(len(new_break_map.keys())+1)), rvalue=c_ast.Constant(type='int', value='1')))
			new_break_map['do_break'+str(len(new_break_map.keys())+1)]='do_break'+str(len(new_break_map.keys())+1)
			new_block.append(statement.iftrue)
			new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.Compound:
				new_block=reOrganizeBreaks(statement.iftrue.block_items,new_break_map)
				new_iftrue=c_ast.Compound(block_items=new_block)
		
		if type(statement.iffalse) is c_ast.Break:
			new_block=[]
			new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='do_break'+str(len(new_break_map.keys())+1)), rvalue=c_ast.Constant(type='int', value='1')))
			new_break_map['do_break'+str(len(new_break_map.keys())+1)]='do_break'+str(len(new_break_map.keys())+1)
			new_block.append(statement.iffalse)
			new_iffalse=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iffalse) is c_ast.Compound:
				new_block=reOrganizeBreaks(statement.iffalse.block_items,new_break_map)
				new_iffalse=c_ast.Compound(block_items=new_block)
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=reOrganizeBreaksIf(statement.iffalse,new_break_map)
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
		
		
		
def addingBreakVariables(statements,new_break_map):
	for variable in new_break_map.keys():
		global new_variable
		new_variable[variable]=variable
		new_block=[]
		new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=variable), rvalue=c_ast.Constant(type='int', value='0')))
		new_block.append(c_ast.Break())
		new_iftrue=c_ast.Compound(block_items=new_block)
		statements.append(c_ast.If(cond=c_ast.BinaryOp(op='==', left=c_ast.ID(name=variable), right=c_ast.Constant(type='int', value='1')), iftrue=new_iftrue, iffalse=None))
	return statements
	
	

def removeEmptyIfLoop(statements):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.If:
			statement=removeEmptyIfLoop_If(statement)
			if statement is not None:
				update_statements.append(statement)
		elif type(statement) is c_ast.While:
                        if len(statement.stmt.block_items)>0:
                            new_block_items=removeEmptyIfLoop(statement.stmt.block_items)
                            update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=new_block_items)))
		else:
			if statement is not None:
				if type(statement) is not c_ast.EmptyStatement:
					update_statements.append(statement)
	return update_statements
			
			
			
def removeEmptyIfLoop_If(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if len(statement.iftrue.block_items)==0:
				new_iftrue=None
			else:
				new_block=removeEmptyIfLoop(statement.iftrue.block_items)
				if len(new_block)==0:
					new_iftrue=None
				else:
					new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.EmptyStatement:
				new_iftrue=None
			else:
				new_iftrue=statement.iftrue
				
		if type(statement.iffalse) is c_ast.Compound:
			if len(statement.iffalse.block_items)==0:
				new_iffalse=None
			else:
				new_block=removeEmptyIfLoop(statement.iffalse.block_items)
				if len(new_block)==0:
					new_iffalse=None 
				else:
					new_iffalse=c_ast.Compound(block_items=new_block) 
		elif type(statement.iffalse) is c_ast.If:
			result=removeEmptyIfLoop_If(statement.iffalse)
			if result is not None:
				new_iffalse=result
		else:
			if type(statement.iffalse) is c_ast.EmptyStatement:
				new_iftrue=None
			else:
				new_iffalse=statement.iffalse
	
	
	if new_iftrue is not None and new_iffalse is None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
	elif new_iftrue is not None and new_iffalse is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
		return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
		return new_iffalse
	else:
		return None

		
		
def returnReplacement(statements,end_label_map):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.If:
			statement=returnReplacementIf(statement,end_label_map)
			if statement is not None:
				update_statements.append(statement)
		elif type(statement) is c_ast.While:
			new_block_items=returnReplacement(statement.stmt.block_items,end_label_map)
			update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=new_block_items)))
		elif type(statement) is c_ast.Return:
			if statement.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.expr))
				update_statements.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				update_statements.append(c_ast.Goto(name=label))
				end_label_map[label]=label
		elif type(statement) is c_ast.Label:
			update_statements.append(c_ast.Label(name=statement.name, stmt=None))
			if type(statement.stmt) is c_ast.Return:
				if statement.stmt.expr is not None:
					label='Label'+str(len(end_label_map.keys())+1)
					update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.stmt.expr))
					update_statements.append(c_ast.Goto(name=label))
					end_label_map[label]=label
				else:
					label='Label'+str(len(end_label_map.keys())+1)
					update_statements.append(c_ast.Goto(name=label))
					end_label_map[label]=label
			else:
				if statement.stmt is not None:
					update_statements.append(statement.stmt)
			
		else:
			update_statements.append(statement)
	return update_statements
	
	
	
	
	
	
def returnReplacementIf(statement,end_label_map):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Return:
			new_block=[]
			if statement.iftrue.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.iftrue.expr))
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.Compound:
				new_block=returnReplacement(statement.iftrue.block_items,end_label_map)
				new_iftrue=c_ast.Compound(block_items=new_block)
			else:
                                new_iftrue=statement.iftrue
			
		if type(statement.iffalse) is c_ast.Return:
			new_block=[]
			if statement.iffalse.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.iffalse.expr))
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			new_iffalse=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iffalse) is c_ast.Compound:
				new_block=returnReplacement(statement.iffalse.block_items,end_label_map)
				new_iffalse=c_ast.Compound(block_items=new_block)
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=returnReplacementIf(statement.iffalse,end_label_map)
				else:
                                        new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)









"""
 
Goto removal Modules End 

"""


break_count=0

continue_count=0	
	


def getBreakStmt(statements,break_map):
	update_statement1=[]
	update_statement2=[]
	flag=False
	global break_count
	global continue_count
        global new_variable
	for statement in statements:
		if type(statement) is c_ast.If:
			if flag==False:
				break_map_temp={}
				statement=getBreakStmtIf(statement,break_map_temp)
				for e_break in break_map_temp.keys():
					break_map[e_break]=break_map_temp[e_break]
				update_statement1.append(statement)
				if len(break_map_temp.keys())>0:
					flag=True
			else:
				update_statement2.append(statement)
		elif type(statement) is c_ast.While:
			break_map_temp={}
			new_block_items1=getBreakStmt(statement.stmt.block_items,break_map_temp)
			new_block_items2=[]
			new_condtion=statement.cond
			if len(break_map_temp.keys())>0:
				for var_name in break_map_temp.keys():
                                        new_block_items2.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='0')))
					if break_map_temp[var_name]=='Break':
						temp_new_condition=c_ast.BinaryOp(op='&&', left=new_condtion, right=c_ast.BinaryOp(op='==', left=c_ast.ID(name=var_name), right=c_ast.Constant(type='int', value='0')))
						new_condtion=temp_new_condition
			
                        for item in new_block_items1:
                            new_block_items2.append(item)
			if flag==False:
				update_statement1.append(c_ast.While(cond=new_condtion, stmt=c_ast.Compound(block_items=new_block_items2)))
			else:
				update_statement2.append(c_ast.While(cond=new_condtion, stmt=c_ast.Compound(block_items=new_block_items2)))
		elif type(statement) is c_ast.Break:
                        break_count=break_count+1
                        var_name='break_'+str(break_count)+'_flag'
                        new_variable[var_name]=var_name
                        update_statement1.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Break'
		elif type(statement) is c_ast.Continue:
		        continue_count=continue_count+1
		       	var_name='continue_'+str(continue_count)+'_flag'
		        new_variable[var_name]=var_name
		        update_statement1.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Continue'
		else:
			if flag==False:
				update_statement1.append(statement)
			else:
				update_statement2.append(statement)
	if flag==True:
		update_condition=None
		for var_name in break_map.keys():
			if update_condition is None:
				update_condition=c_ast.BinaryOp(op='==', left=c_ast.ID(name=var_name), right=c_ast.Constant(type='int', value='0'))
			else:
				update_condition=c_ast.BinaryOp(op='&&', left=update_condition, right=c_ast.BinaryOp(op='==', left=c_ast.ID(name=var_name), right=c_ast.Constant(type='int', value='0')))
		if len(update_statement2)>0:
			update_statement1.append(c_ast.If(cond=update_condition, iftrue=c_ast.Compound(block_items=update_statement2), iffalse=None))
		
		return getBreakStmt(update_statement1,break_map)
	else:
		return update_statement1
			
		




def getBreakStmtIf(statement,break_map):
	new_iftrue=None
	new_iffalse=None
	global break_count
	global new_variable
	global continue_count
	if type(statement) is c_ast.If:
			
		if type(statement.iftrue) is c_ast.Break:
                        new_block_items=[]
                        break_count=break_count+1
                        var_name='break_'+str(break_count)+'_flag'
                        new_variable[var_name]=var_name
                        new_block_items.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Break'
			new_iftrue=c_ast.Compound(block_items=new_block_items)
		elif type(statement.iftrue) is c_ast.Continue:
		        new_block_items=[]
		        break_count=break_count+1
		        var_name='continue_'+str(continue_count)+'_flag'
		        new_variable[var_name]=var_name
		        new_block_items.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Continue'
			new_iftrue=c_ast.Compound(block_items=new_block_items)
		elif type(statement.iftrue) is c_ast.Compound:
			new_block_items=getBreakStmt(statement.iftrue.block_items,break_map)
			new_iftrue=c_ast.Compound(block_items=new_block_items)
		else:
			new_iftrue=statement.iftrue
			
		if type(statement.iffalse) is c_ast.Break:
                        new_block_items=[]
                        break_count=break_count+1
                        var_name='break_'+str(break_count)+'_flag'
                        new_variable[var_name]=var_name
                        new_block_items.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Break'
			new_iffalse=c_ast.Compound(block_items=new_block_items)
		elif type(statement.iffalse) is c_ast.Continue:
		        new_block_items=[]
		        continue_count=continue_count+1
		        var_name='continue_'+str(continue_count)+'_flag'
		        new_variable[var_name]=var_name
		        new_block_items.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Continue'
			new_iffalse=c_ast.Compound(block_items=new_block_items)	
		elif type(statement.iffalse) is c_ast.Compound:
			new_block_items=getBreakStmt(statement.iffalse.block_items,break_map)
			new_iffalse=c_ast.Compound(block_items=new_block_items)
		else:
			if type(statement.iffalse) is c_ast.If:
				new_iffalse=getBreakStmtIf(statement.iffalse,break_map)
			else:
				new_iffalse=statement.iffalse
	if new_iftrue is not None and new_iffalse is None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
	elif new_iftrue is not None and new_iffalse is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
		return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
		return new_iffalse
	else:
		return None


dummyCount=0
    
def functionToAssignment(statements,functionMap):
 	global dummyCount
 	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.FuncCall:
			if  '__VERIFIER' not in statement.name.name:
				dummyCount=dummyCount+1
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='_'+str(dummyCount)+'DUMMY'), rvalue=statement))
			else:
				update_statements.append(statement)
		elif type(statement) is c_ast.If:
	                	update_statements.append(functionToAssignmentIf(statement,functionMap))
	        elif type(statement) is c_ast.While:
	        	if type(statement.stmt) is c_ast.Compound:
	                	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=functionToAssignment(statement.stmt.block_items,functionMap))))
			else:
				if statement.stmt is not None:
					if type(statement) is c_ast.EmptyStatement:
						new_block=[]
						update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=new_block)))	
					else:
						new_block=[]
						new_block.append(statement.stmt)
						update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=functionToAssignment(new_block,functionMap))))
				else:
			        	update_statements.append(statement)
		else:
                	update_statements.append(statement)
        return update_statements
                	
                	
                	
def functionToAssignmentIf(statement,functionMap):
      new_iftrue=None
      new_iffalse=None
      global dummyCount
      if type(statement) is c_ast.If:
          if type(statement.iftrue) is c_ast.Compound:
	  	new_block_items=functionToAssignment(statement.iftrue.block_items,functionMap)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
          elif type(statement.iftrue) is c_ast.FuncCall:
          	if  '__VERIFIER' not in statement.iftrue.name.name:
	  		dummyCount=dummyCount+1
	  		new_iftrue=c_ast.Assignment(op='=',lvalue=c_ast.ID(name='_'+str(dummyCount)+'DUMMY'), rvalue=statement.iftrue)
	  	else:
	  		new_iftrue=statement.iftrue
          else:
               new_iftrue=statement.iftrue
              
          if type(statement.iffalse) is c_ast.Compound:
              if statement.iffalse.block_items is not None:
                  new_block_items=functionToAssignment(statement.iffalse.block_items,functionMap)
                  new_iffalse=c_ast.Compound(block_items=new_block_items)
              else:
                  new_iffalse=statement.iffalse
          elif type(statement.iffalse) is c_ast.FuncCall:
          	if  '__VERIFIER' not in statement.iffalse.name.name:
	      		dummyCount=dummyCount+1
	      		new_iffalse=c_ast.Assignment(op='=',lvalue=c_ast.ID(name='_'+str(dummyCount)+'DUMMY'), rvalue=statement.iffalse)
	      	else:
	      		new_iffalse=statement.iffalse
          elif type(statement.iffalse) is c_ast.If:
              new_iffalse=functionToAssignmentIf(statement.iffalse,functionMap)
          else:
              new_iffalse=statement.iffalse
      return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)


def getDummyFunction(f,o,a,cm):
	new_o={}
	for eq in o.keys():
		if o[eq][0]=='e':
			lefthandstmt=expr2string1(o[eq][1])
			if 'DUMMY' in lefthandstmt:
				new_eq=[]
				new_eq.append('s0')
				new_eq.append(o[eq][2])
				new_o[eq]=new_eq
			else:
				new_o[eq]=o[eq]
		else:
			new_o[eq]=o[eq]
	#return f,new_o,a,cm
	return f,o,a,cm









def getVariablesInit(statements):
    update_statement=[]
    for decl in statements:
        if type(decl) is c_ast.Decl:
            if type(decl.type) is not c_ast.ArrayDecl and type(decl.type) is not c_ast.PtrDecl:
                if decl.init is not None and '_PROVE' not in decl.name:
                    new_word=None
                    if new_word is None:
                        new_word=copy.deepcopy(decl.init)
                    decl=c_ast.Decl(name=decl.name, quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=c_ast.TypeDecl(declname=decl.type.declname, quals=decl.type.quals, type=decl.type.type), init=None, bitsize=decl.bitsize)
                    update_statement.append(decl)
                    if '_PROVE' not in decl.name:
                        if new_word is not None:
                            update_statement.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=decl.name), rvalue=new_word))
                else:
                    update_statement.append(decl)
            else:
                update_statement.append(decl)
        elif type(decl) is c_ast.While:
        	new_block_temp=getVariablesInit(decl.stmt.block_items)
                update_statement.append(c_ast.While(cond=decl.cond, stmt=c_ast.Compound(block_items=new_block_temp)))
        elif type(decl) is c_ast.If:
                update_statement.append(getVariablesInit_If(decl))
        else:
             update_statement.append(decl)
    return update_statement


def getVariablesInit_If(statement):
	If_stmt=None
        Else_stmt=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			new_block_temp=getVariablesInit(statement.iftrue.block_items)
                        If_stmt=c_ast.Compound(block_items=new_block_temp)
                else:
                    If_stmt=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_block_temp=getVariablesInit(statement.iffalse.block_items)
				Else_stmt=c_ast.Compound(block_items=new_block_temp)
                        else:
                            Else_stmt=statement.iffalse
		else:
			if type(statement.iffalse) is c_ast.If:
				Else_stmt=getVariablesInit_If(statement.iffalse)
                        else:
                                Else_stmt=statement.iffalse
	return c_ast.If(cond=statement.cond, iftrue=If_stmt, iffalse=Else_stmt)

#Get All Variables


def getVariables(function_body):
    #statements=handlingPointer(function_body.block_items)
    statements=function_body.block_items
    #for decl in function_body.block_items:
    return getVariablesC(statements)


#Get Variable 

def getVariablesC(statements):
    localvarmap={}
    if statements is None:
        return localvarmap
    for decl in statements:
        if type(decl) is c_ast.Decl:
            var_type=None
            initial_value=None
            structType=None
            if type(decl.type) is c_ast.ArrayDecl:
                #if checkingArrayName(decl.type)==True:
                if is_number(decl.name[-1])==True:
                    decl=c_ast.Decl(name=decl.name+'_var', quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=renameArrayName(decl.type), init=decl.init, bitsize=decl.bitsize)
                elif decl.name in ['S','Q','N','in','is']:
                    decl=c_ast.Decl(name=decl.name+'_var', quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=renameArrayName(decl.type), init=decl.init, bitsize=decl.bitsize)
            elif type(decl.type) is c_ast.PtrDecl:
                if type(decl.type.type) is c_ast.TypeDecl:
                    if is_number(decl.type.type.declname[-1])==True:
                        decl.type.type=c_ast.TypeDecl(decl.type.type.declname+'_var', quals=decl.type.type.quals, type=decl.type.type.type)
                    elif decl.name in ['S','Q','N','in','is']:
                        decl.type.type=c_ast.TypeDecl(decl.type.type.declname+'_var', quals=decl.type.type.quals, type=decl.type.type.type)
            else:
                if is_number(decl.type.declname[-1])==True :
                    decl=c_ast.Decl(name=decl.name+'_var', quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=c_ast.TypeDecl(declname=decl.type.declname+'_var', quals=decl.type.quals, type=decl.type.type), init=decl.init, bitsize=decl.bitsize)


            if type(decl.type) is c_ast.ArrayDecl:
            	degree=0
                dimensionmap={}
	    	var_type,degree,structType=getArrayDetails(decl,degree,dimensionmap)
		variable=variableclass(decl.name, var_type,None,dimensionmap,initial_value,structType)
	    elif type(decl.type) is c_ast.PtrDecl:
                degree=0
                dimensionmap={}
	    	var_type,degree,structType=getArrayDetails(decl,degree,dimensionmap)
		variable=variableclass(decl.name, var_type,'Pointer',dimensionmap,initial_value,structType)
	    else:
            	for child in decl.children():
                    
            		if type(child[1]) is c_ast.TypeDecl:
                		if type(child[1].type) is c_ast.IdentifierType:
                    			var_type=child[1].type.names[0]
				else:
					if type(child[1].type) is c_ast.Struct:
						structType=child[1].type.name
                                                var_type=child[1].type.name
					else:
                    				initial_value=child[1].value
                    	else:
                    		if type(child[1]) is c_ast.FuncCall:
			    		parameter=''
					if child[1].args is not None:
			    			for param in child[1].args.exprs:
			    				if type(param) is c_ast.ID:
			    					if parameter=='':
					        			parameter = "expres('"+param.name+"')"
					        		else:
					        			parameter += ",expres('"+param.name+"')"
			    				elif type(param) is c_ast.Constant:
			    		    			if parameter=='':
									parameter = "expres('"+param.value+"')"
								else:
					        			parameter += ",expres('"+param.value+"')"
							else:
								if type(statement) is c_ast.ArrayRef:
									degree=0
									stmt,degree=createArrayList_C(statement,degree)
								    	if parameter=='':
										parameter = "expres('d"+str(degree)+'array'+"',["+stmt+"])"
									else:
		        							parameter += ","+"expres('d"+str(degree)+'array'+"',["+stmt+"])"
						#initial_value="['"+child[1].name.name+"',"+parameter+"]"
						initial_value="['"+child[1].name.name+"',"+parameter+"]"
					else:
						#initial_value="expres('"+child[1].name.name+"'"+")"
						initial_value=child[1].name.name
				else:
					if type(child[1]) is c_ast.Constant:
						initial_value=child[1].value
                                        elif type(child[1]) is c_ast.ID:
						initial_value=child[1].name
					else:
                                                #print expressionCreator_C(child[1])
						initial_value=child[1]
            	#print '##############################'
                #print decl.name
                #print var_type
            	#print '##############################'
            	variable=variableclass(decl.name, var_type,None,None,initial_value,structType)
            localvarmap[decl.name]=variable
        elif type(decl) is c_ast.While:
        	localvarmap_temp=getVariablesC(decl.stmt.block_items)
        	for var in localvarmap_temp.keys():
        		localvarmap[var]=localvarmap_temp[var]
        elif type(decl) is c_ast.If:
        	localvarmap_temp=getVariablesC_If(decl)
        	for var in localvarmap_temp.keys():
        		localvarmap[var]=localvarmap_temp[var]
    return localvarmap


def getVariablesC_If(statement):
	localvarmap={}
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			localvarmap_temp=getVariablesC(statement.iftrue.block_items)
		        for var in localvarmap_temp.keys():
        			localvarmap[var]=localvarmap_temp[var]				
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				localvarmap_temp=getVariablesC(statement.iffalse.block_items)
				for var in localvarmap_temp.keys():
        				localvarmap[var]=localvarmap_temp[var]	
		else:
			if type(statement.iffalse) is c_ast.If:
				localvarmap_temp=getVariablesC_If(statement.iffalse)
				for var in localvarmap_temp.keys():
        				localvarmap[var]=localvarmap_temp[var]	
	return localvarmap





def getVariablesInit(statements):
    update_statement=[]
    for decl in statements:
        if type(decl) is c_ast.Decl:
            if type(decl.type) is not c_ast.ArrayDecl and type(decl.type) is not c_ast.PtrDecl:
                if decl.init is not None and '_PROVE' not in decl.name:
                    new_word=None
                    if new_word is None:
                        new_word=copy.deepcopy(decl.init)
                    decl=c_ast.Decl(name=decl.name, quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=c_ast.TypeDecl(declname=decl.type.declname, quals=decl.type.quals, type=decl.type.type), init=None, bitsize=decl.bitsize)
                    update_statement.append(decl)
                    if '_PROVE' not in decl.name:
                        if new_word is not None:
                            update_statement.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=decl.name), rvalue=new_word))
                else:
                    update_statement.append(decl)
            else:
                update_statement.append(decl)
        elif type(decl) is c_ast.While:
        	new_block_temp=getVariablesInit(decl.stmt.block_items)
                update_statement.append(c_ast.While(cond=decl.cond, stmt=c_ast.Compound(block_items=new_block_temp)))
        elif type(decl) is c_ast.If:
                update_statement.append(getVariablesInit_If(decl))
        else:
             update_statement.append(decl)
    return update_statement


def getVariablesInit_If(statement):
	If_stmt=None
        Else_stmt=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			new_block_temp=getVariablesInit(statement.iftrue.block_items)
                        If_stmt=c_ast.Compound(block_items=new_block_temp)
                else:
                    If_stmt=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_block_temp=getVariablesInit(statement.iffalse.block_items)
				Else_stmt=c_ast.Compound(block_items=new_block_temp)
                        else:
                            Else_stmt=statement.iffalse
		else:
			if type(statement.iffalse) is c_ast.If:
				Else_stmt=getVariablesInit_If(statement.iffalse)
                        else:
                                Else_stmt=statement.iffalse
	return c_ast.If(cond=statement.cond, iftrue=If_stmt, iffalse=Else_stmt)




def translate2IntForm_Java(function_name,function_type,function_body,parametermap,localvarmap,class_variable,class_name):
    if function_body is None: 
        print "Empty Body"
	return None
        
    start_time=current_milli_time()
    
    statements=function_body.block_items
       
    #localvarmap=getVariables(function_body)
    
    
    print 'Program Body'
    
    generator = c_generator.CGenerator()
    
    
    print(generator.visit(function_body))

    membermethod=membermethodclass(function_name,function_type,parametermap,localvarmap,function_body,0,0,None)
    print "Function Name:"
    print membermethod.getMethodname()
    print "Return Type:"
    print membermethod.getreturnType()
    print "Input Variables:"
    var_list="{"
    for x in membermethod.getInputvar():
        if membermethod.getInputvar()[x].getDimensions()>0:
            var_list+=' '+x+':array'
	else:
	    var_list+=' '+x+':'+membermethod.getInputvar()[x].getVariableType()
    var_list+='}'
    print var_list
    print "Local Variables:"
    var_list="{"
    for x in membermethod.getLocalvar():
        if membermethod.getLocalvar()[x].getDimensions()>0:
            var_list+=' '+x+':array'
	else:
            var_list+=' '+x+':'+membermethod.getLocalvar()[x].getVariableType()
    var_list+='}'
    print var_list
    allvariable={}
    program_dec_start=""
    program_dec_end=""
    for lvap in localvarmap:
        var=localvarmap[lvap]
        var.setInitialvalue(None)
        if var is not None and var.getInitialvalue() is not None:
	    if type(var.getInitialvalue()) is not c_ast.BinaryOp and '__VERIFIER_nondet' in var.getInitialvalue():
	    	defineDetailtemp=[]
	    	parameter_list=[]
	    	parameter_list.append('int')
		defineDetailtemp.append(var.getInitialvalue())
		defineDetailtemp.append(0)
		defineDetailtemp.append(parameter_list)
		defineDetaillist.append(defineDetailtemp)
            if program_dec_start=="":
            	if type(var.getInitialvalue()) is c_ast.BinaryOp:
            	        program_dec_start="['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+expressionCreator_C(var.getInitialvalue())+"]"
                	program_dec_end="]"
            	else:
            		if is_hex(str(var.getInitialvalue())) is not None:
                		program_dec_start="['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+is_hex(str(var.getInitialvalue()))+"')]"
                	else:
                		program_dec_start="['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+str(var.getInitialvalue())+"')]"
                	program_dec_end="]"
            else:
            	if type(var.getInitialvalue()) is c_ast.BinaryOp:
            	        program_dec_start+=",['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+expressionCreator_C(var.getInitialvalue())+"]"
                	program_dec_end+="]"
            	else:
            		if is_hex(str(var.getInitialvalue())) is not None:
                		program_dec_start+=",['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+is_hex(str(var.getInitialvalue()))+"')]"
                	else:
                		program_dec_start+=",['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+str(var.getInitialvalue())+"')]"
                	program_dec_end+="]"
    for x in membermethod.getInputvar():
        allvariable[x]=membermethod.getInputvar()[x]
    for x in membermethod.getLocalvar():
        allvariable[x]=membermethod.getLocalvar()[x]
    


       
    expressions=organizeStatementToObject_C(statements)
    
    primeStatement(expressions)
    variablesarray={}
    opvariablesarray={}
    count=0
    arrayFlag=False
    for variable in allvariable:
        count+=1
        if allvariable[variable].getDimensions()>0:
            variablesarray[variable]=eval("['_y"+str(count)+"','array']")
            opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','array']")
            list_parameter="'array'"
            for i in range(0, allvariable[variable].getDimensions()):
                if list_parameter=='':
                    list_parameter="'int'"
                else:
                    list_parameter+=",'int'"
            list_parameter+=",'"+allvariable[variable].getVariableType()+"'"
            #key1=str(allvariable[variable].getDimensions())+'array'
            key1='d'+str(allvariable[variable].getDimensions())+'array'
            arrayFlag=True
            if key1 not in variablesarray.keys():
             	count+=1
                variablesarray[key1]=eval("['_y"+str(count)+"',"+list_parameter+"]")
                opvariablesarray[key1+"1"]=eval("['_y"+str(count)+"',"+list_parameter+"]")
        else:
            variablesarray[variable]=eval("['_y"+str(count)+"','"+allvariable[variable].getVariableType()+"']")
            opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','"+allvariable[variable].getVariableType()+"']")

    for variable in class_variable:
        count+=1
        if class_variable[variable].getDimensions()>0:
            variablesarray[variable]=eval("['_y"+str(count)+"','"+class_name+"','array']")
            opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','array']")
            list_parameter="'"+class_name+"','array'"
            for i in range(0, class_variable[variable].getDimensions()):
                if list_parameter=='':
                    list_parameter="'int'"
                else:
                    list_parameter+=",'int'"
            list_parameter+=",'"+class_variable[variable].getVariableType()+"'"
            #key1=str(allvariable[variable].getDimensions())+'array'
            key1='d'+str(class_variable[variable].getDimensions())+'array'
            arrayFlag=True
            if key1 not in variablesarray.keys():
             	count+=1
                variablesarray[key1]=eval("['_y"+str(count)+"',"+list_parameter+"]")
                opvariablesarray[key1+"1"]=eval("['_y"+str(count)+"',"+list_parameter+"]")
        else:
            variablesarray[variable]=eval("['_y"+str(count)+"','"+class_name+"','"+class_variable[variable].getVariableType()+"']")
            opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','"+class_name+"','"+class_variable[variable].getVariableType()+"']")
    
    if program_dec_start=="":
        str_program=programToinductiveDefination_C(expressions , allvariable)
    else:
        str_program=program_dec_start+','+programToinductiveDefination_C(expressions , allvariable)+program_dec_end
    program=eval(str_program)
    return program,variablesarray,membermethod.getMethodname(),membermethod.getInputvar(),opvariablesarray




"""

Organization of AST 

"""
               
def organizeStatementToObject_C(statements):
	count=0
	degree=0
	expressions=[]
	for statement in statements:
                if type(statement) is c_ast.Assignment:
			count=count+1
			expression=expressionclass(statement, count, True,degree)
			expressions.append(expression)
                elif type(statement) is c_ast.While:
                    blockexpressions=[]
                    if statement.stmt is not None:
                        degree=degree+1
			count,blockexpressions=blockToExpressions_C(statement.stmt.block_items, degree, count)
			degree=degree-1
		    block=blockclass( blockexpressions, statement.cond, count , True, degree)
		    expressions.append(block)
		else:
			if type(statement) is c_ast.If:
				count,ifclass=ifclassCreator_C(statement, degree, count)
				expressions.append(ifclass)
			else:
				count=count+1
				expression=expressionclass(statement, count, True,degree)
				expressions.append(expression)
					
     	return expressions



"""

Organization of AST 

"""


               
def organize__VERIFIER_nondet_C(statements,count):
	expressions=[]
	for statement in statements:
                if type(statement) is c_ast.Assignment:
			expressions.append(expression)
                elif type(statement) is c_ast.While:
                    blockexpressions=[]
                    if statement.stmt is not None:
			count,blockexpressions=organize__VERIFIER_nondet_C(statement.stmt.block_items,count)
		    block=blockclass( blockexpressions, statement.cond, count , True, degree)
		    expressions.append(block)
		else:
			if type(statement) is c_ast.If:
				count,ifclass=ifclassCreator_C(statement, degree, count)
				expressions.append(ifclass)
			else:
				count=count+1
				expression=expressionclass(statement, count, True,degree)
				expressions.append(expression)
					
     	return expressions,count

"""

Conditionl Loop to a Array of Statement Compatible to Translator Program 
IfClass Creator

"""

def ifclassCreator_C(statement, degree, count):
        blockexpressions1=None
	blockexpressions2=None
	predicate=statement.cond
	#print statement.iftrue.show()
	#print statement.iffalse.show()
        if statement.iftrue is not None:
        	if type(statement.iftrue) is c_ast.Compound:
            		count,blockexpressions1=blockToExpressions_C(statement.iftrue.block_items, degree, count)
            	else:
            		new_block_items=[]
            		new_block_items.append(statement.iftrue)
            		count,blockexpressions1=blockToExpressions_C(new_block_items, degree, count)
        if statement.iffalse is not None and type(statement.iffalse) is c_ast.If:
        	count,blockexpressions2=ifclassCreator_C(statement.iffalse, degree, count)
        else:
        	if statement.iffalse is not None:
        		if type(statement.iffalse) is c_ast.Compound:
        			count,blockexpressions2=blockToExpressions_C(statement.iffalse.block_items, degree, count)
        		else:
        			new_block_items=[]
        			new_block_items.append(statement.iffalse)
            			count,blockexpressions2=blockToExpressions_C(new_block_items, degree, count)
	ifclass=Ifclass(predicate, blockexpressions1, blockexpressions2, count ,True ,degree)
	return count,ifclass



"""

Converting code block,while loop ,conditional expression and expression to corresponding Classes

"""

def blockToExpressions_C(body, degree, count):
	expressions=[]
	if body is not None:
		for statement in body:
                    if type(statement) is c_ast.Assignment:
			count=count+1
			expression=expressionclass(statement, count, True,degree)
			expressions.append(expression)
                    elif type(statement) is c_ast.While:
                        blockexpressions=[]
                        if statement.stmt is not None:
                            degree=degree+1
                            count,blockexpressions=blockToExpressions_C(statement.stmt.block_items, degree, count)
                            degree=degree-1
                        block=blockclass( blockexpressions, statement.cond, count , True, degree)
                        expressions.append(block)
                    else:
			if type(statement) is c_ast.If:
				count,ifclass=ifclassCreator_C(statement, degree, count)
				expressions.append(ifclass)
	return count,expressions




"""

Block of Statement to Array of Statement Compatible to Translator Program 

"""
def programToinductiveDefination_C(expressions, allvariable):
	programsstart=""
	programsend=""
	statements=""
	for expression in expressions:
		if type(expression) is expressionclass:
                    
			if type(expression.getExpression()) is c_ast.Assignment:
                                var=None
                                if type(expression.getExpression().lvalue) is c_ast.ID:
                                    var=str(eval("expres('"+str(expression.getExpression().lvalue.name)+"')"))
                                elif type(expression.getExpression().lvalue) is c_ast.Constant:
                                    var=str(eval("expres('"+str(expression.getExpression().lvalue.value)+"')"))
                                elif type(expression.getExpression().lvalue) is c_ast.ArrayRef:
                                    degree=0
       				    stmt,degree=createArrayList_C(expression.getExpression().lvalue,degree)
                                    var=str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
                                    
                                    
                                elif type(expression.getExpression().lvalue) is c_ast.FuncCall:
                                	parameter=''
				        statement=expression.getExpression().lvalue
					if statement.args is not None:
						for param in statement.args.exprs:
							if type(param) is c_ast.ID:
								if parameter=='':
									parameter = str(eval("expres('"+param.name+"')"))
								else:
									parameter += ","+str(eval("expres('"+param.name+"')"))
							elif type(param) is c_ast.Constant:
								if parameter=='':
									parameter = str(eval("expres('"+param.value+"')"))
								else:
									parameter += ","+str(eval("expres('"+param.value+"')"))
							elif type(param) is c_ast.BinaryOp:
							    	if parameter=='':
									parameter =expressionCreator_C(param)
								else:
					        			parameter += ","+expressionCreator_C(param)
                                                        else:
                                                            if type(param) is c_ast.ArrayRef:
                                                            #parameter_list.append('int')
                                                                degree=0
                                                                stmt,degree=createArrayList_C(param,degree)
                                                                if parameter=='':
                                                                    parameter = str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
                                                                else:
                                                                    parameter += ","+str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
					var="['"+statement.name.name+"',"+parameter+"]"
		
                                
				if expression.getIsPrime()==False:
                                    if programsstart=="":
                                        programsstart="['-1','seq',['-1','=',"+str(var)+","+str(expressionCreator_C(expression.getExpression().rvalue))+"]"
                                        programsend="]"
				    else:
					programsstart+=",['-1','seq',['-1','=',"+str(var)+","+str(expressionCreator_C(expression.getExpression().rvalue))+"]"
					programsend+="]"
				else:
                                    if programsstart=="":
                                        programsstart="['-1','=',"+str(var)+","+str(expressionCreator_C(expression.getExpression().rvalue))+"]"+programsend
                                    else:
                                        programsstart+=",['-1','=',"+str(var)+","+str(expressionCreator_C(expression.getExpression().rvalue))+"]"+programsend

                        elif type(expression.getExpression()) is c_ast.FuncCall:
                        	parameter=''
                        	statement=expression.getExpression()
				if statement.args is not None:
			    		for param in statement.args.exprs:
			    			if type(param) is c_ast.ID:
			    				if parameter=='':
					        		parameter = str(eval("expres('"+param.name+"')"))
					        	else:
					        		parameter += ","+str(eval("expres('"+param.name+"')"))
			    			elif type(param) is c_ast.Constant:
			    		    		if parameter=='':
								parameter = str(eval("expres('"+param.value+"')"))
							else:
					        		parameter += ","+str(eval("expres('"+param.value+"')"))
						elif type(param) is c_ast.BinaryOp:
			    		    		if parameter=='':
								parameter =expressionCreator_C(param)
							else:
					        		parameter += ","+expressionCreator_C(param)
                                                else:
                                                    if type(param) is c_ast.ArrayRef:
                                                        #parameter_list.append('int')
                                                        degree=0
                                                        stmt,degree=createArrayList_C(param,degree)
                                                        if parameter=='':
                                                            parameter = str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
                                                        else:
                                                            parameter += ","+str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
					
                                        if expression.getIsPrime()==False:
						if programsstart=="":
							programsstart="['-1','seq',"+"['"+statement.name.name+"',"+parameter+"]"
					                programsend="]"
						else:
							programsstart+=","+"['-1','seq',"+"['"+statement.name.name+"',"+parameter+"]"
							programsend+="]"
					else:
						if programsstart=="":
					        	programsstart="['-1','seq',"+"['"+statement.name.name+"',"+parameter+"]"+programsend
					        else:
                                        		programsstart+=","+"['-1','seq',"+"['"+statement.name.name+"',"+parameter+"]"+programsend
				else:
  					if expression.getIsPrime()==False:
						if programsstart=="":
							programsstart="['-1','seq',"+str(eval("expres('"+statement.name.name+"'"+")"))
							programsend="]"
						else:
							programsstart+=","+"['-1','seq',"+str(eval("expres('"+statement.name.name+"'"+")"))
							programsend+="]"
					else:
						if programsstart=="":
							programsstart="['-1','seq',"+str(eval("expres('"+statement.name.name+"'"+")"))+programsend
						else:
                                        		programsstart+=","+"['-1','seq',"+str(eval("expres('"+statement.name.name+"'"+")"))+programsend
		elif type(expression) is blockclass:
			predicatestmt="['-1','while',"+expressionCreator_C(expression.predicate)+","+programToinductiveDefination_C( expression.getExpression(), allvariable)+"]"
			if expression.getIsPrime()==False:
				if programsstart=="":
					programsstart="['-1','seq',"+predicatestmt
					programsend="]"
				else:
					programsstart+=",['-1','seq',"+predicatestmt
					programsend+="]"
			else:
				programsstart+=","+predicatestmt+programsend
		elif type(expression) is Ifclass:
			condition=expressionCreator_C(expression.predicate)
			expressionif=None
			expressionelse=None
			predicatestmt=""
			if expression.getExpressionif() is not None:
				expressionif=programToinductiveDefination_C( expression.getExpressionif(), allvariable)
			if expression.getExpressionelse() is not None:
				if type(expression.getExpressionelse()) is Ifclass:
					#expressionelse=programToinductiveDefination( expression.getExpressionelse().getExpressionif(), allvariable)
					expressionelse=programToinductiveDefinationIfElse_C( expression.getExpressionelse(), allvariable)
				else:
					expressionelse=programToinductiveDefination_C( expression.getExpressionelse(), allvariable)
			if expressionif is not None and expressionelse is not None:
                          	predicatestmt="['-1','if2',"+condition+","+expressionif+","+expressionelse+"]"
			elif expressionif is not None and expressionelse is None:
				predicatestmt="['-1','if1',"+condition+","+expressionif+"]"
			if expression.getIsPrime()==False:
				if programsstart=="":
					programsstart="['-1','seq',"+predicatestmt
					programsend="]"
				else:
					programsstart+=",['-1','seq',"+predicatestmt
					programsend+="]"
			else:
				if programsstart=="":
					programsstart=predicatestmt+programsend
				else:
					programsstart+=","+predicatestmt+programsend
	if programsstart[0]==',':
		programsstart=programsstart[1:]	
	return programsstart





"""

IfElse Block Statement to Array of Statement Compatible to Translator Program 

"""
def programToinductiveDefinationIfElse_C(expression, allvariable):
	programsstart=""
	programsend=""
	statements=""
	if type(expression) is expressionclass:
		if type(expression.getExpression()) is c_ast.Assignment:
                        var=None
                        if type(expression.getExpression().lvalue) is c_ast.ID:
                            var=str(eval("expres('"+str(expression.getExpression().lvalue.name)+"')"))
                        elif type(expression.getExpression().lvalue) is c_ast.Constant:
                            var=str(eval("expres('"+str(expression.getExpression().lvalue.value)+"')"))
                        elif type(expression.getExpression().lvalue) is c_ast.ArrayRef:
			    	degree=0
			       	stmt,degree=createArrayList_C(expression.getExpression().lvalue,degree)
    				var=str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
			if expression.getIsPrime()==False:
                            if programsstart=="":
                                programsstart="['-1','seq',['-1','=',"+str(var)+","+str(expressionCreator(expression.getExpression().rhs))+"]"
                                programsend="]"
			    else:
                                programsstart+=",['-1','seq',['-1','=',"+str(var)+","+str(expressionCreator(expression.getExpression().rhs))+"]"
                                programsend+="]"
                        else:
                            if programsstart=="":
                                programsstart+="['-1','=',"+str(var)+","+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
                            else:
                                programsstart+=",['-1','=',"+str(var)+","+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend

	elif type(expression) is blockclass:
		predicatestmt="['-1','while',"+expressionCreator_C(expression.predicate)+","+programToinductiveDefination_C( expression.getExpression(), allvariable)+"]"
		if expression.getIsPrime()==False:
			if programsstart=="":
				programsstart="['-1','seq',"+predicatestmt
				programsend="]"
			else:
				programsstart+=",['-1','seq',"+predicatestmt
				programsend+="]"
		else:
			if programsstart=="":
				programsstart+=","+predicatestmt+programsend
			
	elif type(expression) is Ifclass:
		condition=expressionCreator_C(expression.predicate)
		expressionif=None
		expressionelse=None
		predicatestmt=""
		if expression.getExpressionif() is not None:
			expressionif=programToinductiveDefination_C( expression.getExpressionif(), allvariable)
		if expression.getExpressionelse() is not None:
			if type(expression.getExpressionelse()) is Ifclass:
				#expressionelse=programToinductiveDefination( expression.getExpressionelse().getExpressionif(), allvariable)
				expressionelse=programToinductiveDefinationIfElse_C( expression.getExpressionelse(), allvariable)
			else:
				expressionelse=programToinductiveDefination_C( expression.getExpressionelse(), allvariable)
		if expressionif is not None and expressionelse is not None:
                	predicatestmt="['-1','if2',"+condition+","+expressionif+","+expressionelse+"]"
		elif expressionif is not None and expressionelse is None:
			predicatestmt="['-1','if1',"+condition+","+expressionif+"]"
		if expression.getIsPrime()==False:
			if programsstart=="":
				programsstart="['-1','seq',"+predicatestmt
				programsend="]"
			else:
				programsstart+=",['-1','seq',"+predicatestmt
				programsend+="]"
		else:
			if programsstart=="":
				programsstart=predicatestmt+programsend
			else:
				programsstart+=","+predicatestmt+programsend
 	return programsstart


"""

Program Expression to a Array of Statement Compatible to Translator Program 

"""

fun_call_map={}
current_fun_call=None


def expressionCreator_C(statement):
    expression=""
    global defineMap
    global defineDetaillist
    global fun_call_map
    global current_fun_call
    if type(statement) is c_ast.ID:
    	if statement.name in defineMap.keys():
    		value = defineMap[statement.name]
    		return str(eval("expres('"+value+"')"))
        else:
        	return str(eval("expres('"+statement.name+"')"))
    elif type(statement) is c_ast.Constant:
    	if statement.type=='char':
                if str(statement.value)==str("'\\0'"):
                    return str(eval("expres('0')"))
                else:
                    return "['char',expres("+statement.value+")]"
    	elif statement.type=='float':
    		if statement.value[-1]=='f':
    			#return "expres('"+str(round(float(statement.value[:-1]), 7))+"')"
                        return str(eval("expres('"+str(statement.value[:-1])+"')"))
	        #return "expres('"+str(float(statement.value))+"')"
                return str(eval("expres('"+str(statement.value)+"')"))
	elif statement.type=='double':
                #return "expres('"+str(float(statement.value))+"')"
                return str(eval("expres('"+str(statement.value)+"')"))
    	else:
        	if is_hex(statement.value) is not None:
        		return str(eval("expres('"+is_hex(statement.value)+"')"))
        	else:
        		return str(eval("expres('"+statement.value+"')"))
    elif type(statement) is c_ast.FuncCall:
    	parameter=''
    	parameter_list=[]
    	defineDetaillist=[]
    	defineDetailtemp=[]
    	parameter_list.append('int')
	if statement.args is not None:
    		for param in statement.args.exprs:
    			if type(param) is c_ast.ID:
    				parameter_list.append('int')
    				if param.name in defineMap.keys():
    					param.name = defineMap[param.name]
    				if parameter=='':
		        		parameter = str(eval("expres('"+param.name+"')"))
		        	else:
		        		parameter += ","+str(eval("expres('"+param.name+"')"))
    			elif type(param) is c_ast.Constant:
    				parameter_list.append('int')
    		    		if parameter=='':
					if is_hex(param.value) is not None:
						parameter = str(eval("expres('"+is_hex(param.value)+"')"))
					else:
						parameter = str(eval("expres('"+param.value+"')"))
				else:
		        		if is_hex(param.value) is not None:
		        			parameter += ","+str(eval("expres('"+is_hex(param.value)+"')"))
		        		else:
		        			parameter += ","+str(eval("expres('"+param.value+"')"))
		        elif type(param) is c_ast.UnaryOp:
				if parameter=='':
                                    
			        	parameter = str(eval("expres('"+param.op+"',["+expressionCreator_C(param.expr)+"])"))
			        else:
                                	parameter +=','+str(eval("expres('"+param.op+"',["+expressionCreator_C(param.expr)+"])"))
		        
		        elif type(param) is c_ast.BinaryOp:
				if parameter=='':
			        	parameter =expressionCreator_C(param)
			        else:
                                	parameter +=','+expressionCreator_C(param)
                        elif type(param) is c_ast.FuncCall:
            
				if parameter=='':
                                        #param.show()
			        	parameter =expressionCreator_C(param)
			        else:
                                        #param.show()
                                	parameter +=','+expressionCreator_C(param)
			else:
				if type(param) is c_ast.ArrayRef:
					parameter_list.append('int')
				    	degree=0
				       	stmt,degree=createArrayList_C(param,degree)
    					if parameter=='':
						parameter = str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
					else:
		        			parameter += ","+str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
				
				#print '@@@@@@@@@@@RamRam'
				#print param.show()
				#print '@@@@@@@@@@@'
		defineDetailtemp.append(statement.name.name)
		defineDetailtemp.append(len(parameter_list)-1)
		defineDetailtemp.append(parameter_list)
		defineDetaillist.append(defineDetailtemp)
                
                #if statement.name.name in fun_call_map.keys() and statement.name.name != current_fun_call and '__VERIFIER_nondet_' not in statement.name.name:
                #    fc_count=fun_call_map[statement.name.name]
                #    fc_count+=1
                #    fun_call_map[statement.name.name]=fc_count
                #    return "['"+statement.name.name+"_"+str(fc_count)+"',"+parameter+"]"
                #else:
                #    fun_call_map[statement.name.name]=0
                return "['"+statement.name.name+"',"+parameter+"]"
	else:
		if '__VERIFIER_nondet_' not in statement.name.name:
                    defineDetailtemp.append(statement.name.name)
                    defineDetailtemp.append(len(parameter_list)-1)
                    defineDetailtemp.append(parameter_list)
                    defineDetaillist.append(defineDetailtemp)
		#if statement.name.name in fun_call_map.keys() and statement.name.name != current_fun_call and '__VERIFIER_nondet_' not in statement.name.name:
                #    fc_count=fun_call_map[statement.name.name]
                #    fc_count+=1
                #    fun_call_map[statement.name.name]=fc_count
                #    return str(eval("expres('"+statement.name.name+"_"+str(fc_count)+"'"+")"))
                #else:
                #    fun_call_map[statement.name.name]=0
                return str(eval("expres('"+statement.name.name+"'"+")"))
                    
    elif type(statement) is c_ast.ArrayRef:
    	degree=0
       	stmt,degree=createArrayList_C(statement,degree)
    	return str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
    else:
        if type(statement) is c_ast.Cast:
            if statement.to_type.type.type.names[0]=='float':
                return "['"+"_ToReal"+"',"+expressionCreator_C(statement.expr)+"]"
            elif statement.to_type.type.type.names[0]=='double':
                return "['"+"_ToReal"+"',"+expressionCreator_C(statement.expr)+"]"
            elif statement.to_type.type.type.names[0]=='int':
                return "['"+"_ToInt"+"',"+expressionCreator_C(statement.expr)+"]"
        else:
            
            if statement.op in ['+','-','*','/','%']:
                expression="expres('"
                expression+=statement.op
                if type(statement) is c_ast.BinaryOp:
                    expression+="',["+expressionCreator_C(statement.left)
                    expression+=','+expressionCreator_C(statement.right)
                else:
                    expression+="',["+expressionCreator_C(statement.expr)
                expression+='])'
                expression=str(eval(expression))
                return expression
            else:
                #if statement.op == '!=':
                #    statement=c_ast.UnaryOp(op='!', expr=c_ast.BinaryOp(op='==',left=statement.left, right=statement.right))

                expression="['"
                if statement.op == '&&':
                    expression+='and'
                elif statement.op == '||':
                    expression+='or'
                elif statement.op == '!':
                    expression+='not'
                else:
                    expression+=statement.op
                if type(statement) is c_ast.BinaryOp:
                    expression+="',"+expressionCreator_C(statement.left)

                    expression+=','+expressionCreator_C(statement.right)
                    expression+=']'
                else:
                    expression="expres('"
                    if statement.op == '!':
                            expression+='not'
                    else:
                            expression+=statement.op
                    expression+="',["+expressionCreator_C(statement.expr)+"]"
                    expression+=')'
                    expression=str(eval(expression))
                return expression




"""

Construct Array List

"""
def createArrayList_C(statement,degree):
	if type(statement) is c_ast.ArrayRef:
		degree=degree+1
		stmt=''
		if type(statement.name) is c_ast.ArrayRef:
			stmt,degree=createArrayList_C(statement.name,degree)
			if type(statement.subscript) is c_ast.ID:
				stmt+=",expres('"+statement.subscript.name+"')"
                        elif type(statement.subscript) is c_ast.BinaryOp:
                                stmt+=","+expressionCreator_C(statement.subscript)
			else:
				stmt+=",expres('"+statement.subscript.value+"')"
			return stmt,degree
		else:
			if type(statement.name) is c_ast.ID:
				if type(statement.subscript) is c_ast.ID:
					stmt+="expres('"+statement.name.name+"')"+",expres('"+statement.subscript.name+"')"
					return stmt,degree
				elif type(statement.subscript) is c_ast.BinaryOp:
					stmt+="expres('"+statement.name.name+"')"+","+expressionCreator_C(statement.subscript)
					return stmt,degree
				else:
                                        if type(statement.subscript) is c_ast.ArrayRef:
                                            temp_degree=0
                                            temp_stmt,temp_degree=createArrayList_C(statement.subscript,temp_degree)
                                            stmt+="expres('"+statement.name.name+"')"+","+"expres('d"+str(temp_degree)+'array'+"',["+temp_stmt+"])"
                                            return stmt,degree 
                                        else:
                                            stmt+="expres('"+statement.name.name+"')"+",expres('"+statement.subscript.value+"')"
                                            return stmt,degree
			else:
				if type(statement.name) is c_ast.FuncCall:
					if type(statement.subscript) is c_ast.FuncCall:
						stmt+=expressionCreator_C(statement.name)+","+expressionCreator_C(statement.subscript)
					elif type(statement.subscript) is c_ast.BinaryOp:
						stmt+=expressionCreator_C(statement.name)+","+expressionCreator_C(statement.subscript)
					else:
						stmt+=expressionCreator_C(statement.name)+",expres('"+statement.subscript.value+"')"
				else:
					stmt+="expres('"+statement.name.value+"')"+",expres('"+statement.subscript.value+"')"
				return stmt,degree
	else:
		return "expres('"+statement.name+"')",degree




#Find Intersection of Two lists


def intersect3(c1,c2,c3):
	return list(set(list(set(c1) & set(c2)))-set(c3))

def intersect2(c1,c2):
	return list(set(c1) & set(c2))
        
def merge_two_dicts(x,y):
    z=x.copy()
    z.update(y)
    return z


config = ConfigParser.RawConfigParser()
config.read(currentdirectory+'/config.properties')
timeout=config.get('ConfigurationSection', 'timeout');
app_id=config.get('ConfigurationSection', 'app_id');



#Time Out 
if timeout.strip()!='' and timeout.strip()!='None' and is_number(timeout.strip())!=False:
	TIMEOUT=timeout.strip()
else:
	TIMEOUT=40000

if app_id.strip()!='' and app_id.strip()!='None':
	Mathematica_id=app_id.strip()
else:
	Mathematica_id=None


# base language (non dynamic, not changed by the program)
# do not use name with number in the end
# these names are not supposed to be used as prorgam variables

_base = ['=','==','!=','<','<=','>','>=','*','**','!','+','-','/', '%', 'ite', 'and', 'or', 'not', 'implies', 'all', 'some', 'null','>>','<<','&','|','^']
_infix_op = ['=','==','!=','<','<=','>','>=','*','**','+','-','/', '%', 'implies','<<','>>','&','|','^']
_relation_op = ['==','!=','<','<=','>','>=']

# variables introduced in the translation

def isvariable(x):
    if x.startswith('_x') or  x.startswith('_y') or  x.startswith('_n') or  x.startswith('_s'):
        return True
    else:
        return False



# program variables and temporary program variables and big N

def is_program_var(x,v):
    if x.startswith('_N'):
        return True
    for y in v:
        if x==y or x.startswith(y+OUT) or (x.startswith(y+TEMP) and 
                                           x[len(y+TEMP):].isdigit()) or x.startswith(y+LABEL):
            return True
    return False


current_milli_time = lambda: int(round(time.time() * 1000))

"""
#Get timestap
"""

def getTimeStamp():
	ts = time.time()
	st = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
	return "\n***********************\n"+str(st)+"\n***********************\n"


"""
RET for return value of a function
Temporary function names are constructed as: 
variable-name + TEMP + TC
Output function names are: 
variable-name + LABEL
for those with label, or
variable-name + OUT
for those without label.
 TC: TempCount, a global counter for naming temporary variables
 LC: LoopCount, a global counter for naming loop constants and variables
"""

RET='RET'
#OUT='Z' #so don't name variables xZ, yZ...
OUT='1' #so don't name variables x1, y1...
#TEMP = 'T' #so if x is a variable, then don't name variables xT, 
TEMP = '' #so if x is a variable, then don't name variables x2,x3,... (temp starts at 2)
LABEL = '_' #so if x is a variable, then don't name variables x_1,x_2, 
TC = 1  # for generating temporary functions to yield xt1,xt2,...
LC = 0  # for generating smallest macro constants in a loop _N1, _N2,... as well as
               # natural number variables _n1,_n2,...
"""
 Expressions: (f e1 ... ek) is represented as [f,e1,...,ek].
 Example: a+1 is ['+', ['a'],['1']]; constant a is ['a']; 
 sum(i+1,j) is ['sum', ['+', ['i'], ['1']], ['j']]
"""


#constructor: functor - a string like '+', '*', 'and', 
# or constants like '1', 'x'; args - a list of exprs
def expres(functor,args=[]):
    return [functor]+args

#accessor
def expr_op(e):
    return e[0]
def expr_args(e):
    return e[1:]

#prefix printing
def expr2string(e):
    if len(e)==1:
        return e[0]
    else:
        return '(' + e[0] +' '+ ' '.join(list(expr2string(x) for x in e[1:]))+ ')'

#normal infix printing
def expr2string1(e):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2string1(args[0])
            else:
                return '('+(' '+op+' ').join(list(expr2string1(x) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2string1(args[0])
        elif op=='implies' and len(args)==2:
            return expr2string1(args[0])+ ' -> '+expr2string1(args[1])
        elif op in _infix_op and len(args)==2:
            return '(' + expr2string1(args[0])+ op+expr2string1(args[1])+')'
        else:
            return op +'('+ ','.join(list(expr2string1(x) for x in args))+ ')'



def expr2stringvfact(e,var_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2stringvfact(args[0],var_map)
            else:
                return '('+(' '+op+' ').join(list(expr2stringvfact(x,var_map) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2stringvfact(args[0],var_map)
        elif op=='implies' and len(args)==2:
            return expr2stringvfact(args[0],var_map)+ ' -> '+expr2stringvfact(args[1],var_map)
        elif op in _infix_op and len(args)==2:
            t1=args[0][0]
            if t1 not in _base and is_number(t1)==False:
            	parameter=[]
            	
            	for x in range(0, len(args[0])):
            		parameter.append('int')
            	var_map[t1]=parameter
            t2=args[1][0]
            if t2 not in _base and is_number(t2)==False:
            	parameter=[]
            	
            	for x in range(0, len(args[1])):
            		parameter.append('int')
            		
            	var_map[t2]=parameter
            return '(' + expr2stringvfact(args[0],var_map)+ op+expr2stringvfact(args[1],var_map)+')'
        else:
            if isArrayFunction(op)==True:
            	count=0
            	for parameter in args:
            	
            		if len(parameter)==1:
            			name=expr2stringvfact(parameter,var_map)
            			if is_number(name)==False:
            				type_list=[]
            				if count==0:
            					type_list.append('array')
            				else:
            					type_list.append('int')
            				count=count+1
            			
            				var_map[name]=type_list
            			
            return op +'('+ ','.join(list(expr2stringvfact(x,var_map) for x in args))+ ')'





def expr2stringvfact2(e,var_map,allvariablelist,constraints):
    args=expr_args(e)
    op=expr_op(e)
    constraint=None
    if len(args)==0:
    	if op not in var_map.keys() and is_number(op)==False and is_hex(op)==None and op not in _base:
    		element=[]
    		element.append(op)
        	element.append(0)
        	element_para=[]
        	element.append(element_para)
        	typename=getVariableType(op,allvariablelist)
		if typename is None:
                        if '__VERIFIER_nondet_double' in op:
                            element_para.append('double')
                        elif '__VERIFIER_nondet_float' in op:
                            element_para.append('float')
                        else:
                            element_para.append('int')
		else:
			if isVariableArray(op,allvariablelist) is not None:
        			element_para.append('array')
        		else:
        			if typename=='unsigned':
                                        constraint=e
        				element_para.append('int')
        			elif typename=='long':
        				element_para.append('int')
        			else:
        				element_para.append(typename)
        	#print '----------'
                #print op
                #print element
                #print '----------'
        	var_map[op]=element
                if constraint is not None or '__VERIFIER_nondet_uint' in op:
                    con_equ=[]
                    con_equ.append('c1')
                    con_equ1=[]
                    con_equ1.append('>=')
                    con_equ1.append(e)
                    con_equ1.append(eval("['0']"))
                    con_equ.append(con_equ1)
                    constraints.append(wff2z3_update_postCond(con_equ))
                constraint=None  
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2stringvfact2(args[0],var_map,allvariablelist,constraints)
            else:
                return '('+(' '+op+' ').join(list(expr2stringvfact2(x,var_map,allvariablelist,constraints) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2stringvfact2(args[0],var_map,allvariablelist,constraints)
        elif op=='implies' and len(args)==2:
            return expr2stringvfact2(args[0],var_map,allvariablelist,constraints)+ ' -> '+expr2stringvfact2(args[1],var_map,allvariablelist,constraints)
        elif op in _infix_op and len(args)==2:
            return '(' + expr2stringvfact2(args[0],var_map,allvariablelist,constraints)+ op+expr2stringvfact2(args[1],var_map,allvariablelist,constraints)+')'
        else:
            if isArrayFunction(op)==True:
            	count=0
            	element=[]
            	element.append(op)
            	element.append(len(args))
            	element_para=[]
            	array_type=None
            	for parameter in args:
            		if count==0:
            			element_para.append('array')
            			element_in=[]
            			para_value=expr2stringvfact2(parameter,var_map,allvariablelist,constraints)
            			element_in.append(para_value)
            			element_in.append(0)
            			element_para_in=[]
            			element_para_in.append('array')
            			element_in.append(element_para_in)
            			var_map[para_value]=element_in
            			array_type=getVariableType(parameter,allvariablelist)
            		else:
            			expr2stringvfact2(parameter,var_map,allvariablelist,constraints)
            			typename=getVariableType(parameter,allvariablelist)
            			if typename is None:
            				element_para.append('int')
            			else:
            				if typename=='unsigned':
            					element_para.append('int')
            				elif typename=='long':
            					element_para.append('int')
            				else:
            					element_para.append(typename)
 			count=count+1
 		if array_type is None:
			element_para.append('int')
		else:
            		if typename=='unsigned':
                                constraint=e
            			element_para.append('int')
            		elif typename=='long':
                                constraint=e
            			element_para.append('int')
            		else:
            			element_para.append(array_type)
            	element.append(element_para)
            	var_map[op]=element
                if constraint is not None or '__VERIFIER_nondet_uint' in op:
                    con_equ=[]
                    con_equ.append('c1')
                    con_equ1=[]
                    con_equ1.append('>=')
                    con_equ1.append(e)
                    con_equ1.append(eval("['0']"))
                    con_equ.append(con_equ1)
                    constraints.append(wff2z3_update_postCond(con_equ))
                constraint=None  
            else:
            	if op not in var_map.keys() and op is not 'ite' and op not in _base:
            		element=[]
            		element.append(op)
            		element.append(len(args))
            		element_para=[]
            		if len(args)>0:
            			for x in args:
            				typename=getVariableType(expr2stringvfact2(x,var_map,allvariablelist,constraints),allvariablelist)
            				if typename is None:
            					element_para.append('int')
            				else:
            					element_para.append(typename)
            		       	typename=getVariableType(op,allvariablelist)
			        if typename is None:
                                    if '__VERIFIER_nondet_double' in op:
                                        element_para.append('double')
                                    elif '__VERIFIER_nondet_float' in op:
                                        element_para.append('float')
                                    else:
			        	element_para.append('int')
			        else:
            				if typename=='unsigned':
                                                constraint=e
            					element_para.append('int')
            				elif typename=='long':
            					element_para.append('int')
            				else:
            					element_para.append(typename)
            		else:
            			typename=getVariableType(op,allvariablelist)
            			if typename is None:
                                    if '__VERIFIER_nondet_double' in op:
                                        element_para.append('double')
                                    elif '__VERIFIER_nondet_float' in op:
                                        element_para.append('float')
                                    else:
            				element_para.append('int')
            			else:
            				if typename=='unsigned':
                                                constraint=e
            					element_para.append('int')
            				elif typename=='long':
            					element_para.append('int')
            				else:
            					element_para.append(typename)
            		element.append(element_para)
            		var_map[op]=element
                        if constraint is not None or '__VERIFIER_nondet_uint' in op:
                            con_equ=[]
                            con_equ.append('c1')
                            con_equ1=[]
                            con_equ1.append('>=')
                            con_equ1.append(e)
                            con_equ1.append(eval("['0']"))
                            con_equ.append(con_equ1)
                            constraints.append(wff2z3_update_postCond(con_equ))
                        constraint=None           	            			
            return op +'('+ ','.join(list(expr2stringvfact2(x,var_map,allvariablelist,constraints) for x in args))+ ')'



# Rearrage expression
def getRidOfDiv(e):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return e
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return e[:1]+list(getRidOfDiv(args[0]))
            else:
                return e[:1]+list(getRidOfDiv(x) for x in expr_args(e))
        elif op=='not' and len(args)==1:
            return e[:1]+list(getRidOfDiv(args[0]))
        elif op=='implies' and len(args)==2:
            return e[:1]+[getRidOfDiv(args[0])]+[getRidOfDiv(args[1])]
        elif op in _relation_op and len(args)==2:
            if len(args[0])>1 and len(args[1])>1 and '/'==args[0][0] and '/'==args[1][0]:
                list_vales=[]
                list_vales_temp1=[]
                list_vales_temp1.append('*')
                list_vales_temp1.append(list(args[0][1]))
                list_vales_temp1.append(list(args[1][2]))
                
                list_vales_temp2=[]
                list_vales_temp2.append('*')
                list_vales_temp2.append(list(args[1][1]))
                list_vales_temp2.append(list(args[0][2]))

        
                list_vales.append(list_vales_temp1)
                list_vales.append(list_vales_temp2)
                
                return e[:1]+list_vales
            elif len(args[0])>1 and '/'==args[0][0]:
                list_vales=[]
                list_vales_temp=[]
                list_vales_temp.append('*')
                list_vales_temp.append(list(args[1]))
                list_vales_temp.append(list(args[0][2]))
                args[1]=list_vales_temp
                list_vales.append(args[0][1])
                list_vales.append(args[1])
                return e[:1]+list_vales
            elif len(args[1])>1 and '/'==args[1][0]:
                list_vales=[]
                list_vales_temp=[]
                list_vales_temp.append('*')
                list_vales_temp.append(list(args[0]))
                list_vales_temp.append(list(args[1][2]))
                args[0]=list_vales_temp
                list_vales.append(args[0])
                list_vales.append(args[1][1])
                return e[:1]+list_vales
            else:
                return e[:1]+list(getRidOfDiv(x) for x in expr_args(e))
        elif op in _infix_op and len(args)==2:
            return e[:1]+list(getRidOfDiv(x) for x in expr_args(e))
        else:
            return e[:1]+list(getRidOfDiv(x) for x in expr_args(e))




#normal infix printing
def expr2stringSimplify(e):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2stringSimplify(args[0])
            else:
                return '('+(' '+op+' ').join(list(expr2stringSimplify(x) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2stringSimplify(args[0])
        elif op=='implies' and len(args)==2:
            return expr2stringSimplify(args[0])+ ' -> '+expr2stringSimplify(args[1])
        elif op in _infix_op and len(args)==2:
            return '(' + expr2stringSimplify(args[0])+ op+expr2stringSimplify(args[1])+')'
        else:
            if op is 'ite':
            	expresion1 = expr2stringSimplify(args[1])
            	expresion2 =  expr2stringSimplify(args[2])
            	if ('and' not in expresion1 and 'or' not in expresion1 and 'ite' not in expresion1) and ('and' not in expresion2 and 'or' not in expresion2 and 'ite' not in expresion2) and simplify(expresion1+'=='+expresion2)==True:
            		
            		return expresion1
		else:
			return op +'('+ ','.join(list(expr2stringSimplify(x) for x in args))+ ')'
            else:
            	return op +'('+ ','.join(list(expr2stringSimplify(x) for x in args))+ ')'


#Function to Simplify equation using Array Map

#e=['i1', 3, '_n1', ['d2array3', ['_x1'], ['_x2'], ['_x3'], ['+', ['_n1'], ['1']],['_n2'], ['_n3']], ['ite', ['and', ['=', ['_x1'], ['C']], ['=', ['_x2'], ['+', ['_n3'], ['0']]], ['=', ['_x3'], ['+', ['_n1'], ['0']]]], ['+', ['ite', ['and', ['=', ['C'], ['C']], ['=', ['+', ['_n3'], ['0']], ['+', ['_n3'], ['0']]], ['=', ['+', ['_n1'], ['0']], ['+', ['_n1'], ['0']]]], ['0'], ['d2array3', ['C'], ['+',['_n3'], ['0']], ['+', ['_n1'], ['0']], ['_n1'], ['_n2'], ['_n3']]], ['*', ['ite', ['and', ['=', ['A'], ['C']], ['=', ['+', ['_n3'], ['0']], ['+', ['_n3'], ['0']]], ['=', ['+', ['_n2'], ['0']], ['+', ['_n1'], ['0']]]], ['0'], ['d2array3', ['A'], ['+', ['_n3'], ['0']], ['+', ['_n2'], ['0']], ['_n1'], ['_n2'], ['_n3']]], ['ite', ['and', ['=', ['B'], ['C']], ['=', ['+', ['_n2'], ['0']], ['+', ['_n3'], ['0']]], ['=', ['+', ['_n1'], ['0']], ['+', ['_n1'], ['0']]]], ['0'], ['d2array3', ['B'], ['+', ['_n2'], ['0']], ['+', ['_n1'], ['0']], ['_n1'], ['_n2'], ['_n3']]]]], ['ite', ['and', ['=', ['_x1'], ['C']], ['=', ['_x2'], ['+', ['_n3'], ['0']]], ['=', ['_x3'], ['+', ['_n1'], ['0']]]], ['0'], ['d2array3', ['_x1'], ['_x2'], ['_x3'], ['_n1'], ['_n2'], ['_n3']]]]]
#array_list=['A','B','C']

def simplify_ind_equation(e,array_list):
        if e[:1]==['ite']:
        	temp=[]
        	count=0
        	ifcase=None
        	elsecase=None
        	status=None
        	for x in expr_args(e):
        		parameter=simplify_ind_equation(x,array_list)
        		if count==0:
        			status=evaluateCondition(parameter,array_list)
                                if status == 'Unknown':
                                    parameter = evaluateConditionModify(parameter,array_list)
        		elif count==1:
        			ifcase=parameter
        		elif count==2:
        			elsecase=parameter
        		temp.append(parameter)
        		count=count+1
        	if status=='True':
        		return ifcase
        	elif status=='False':
        		return elsecase
        	else:
        		return e[:1]+temp
        else:
        	return e[:1]+list(simplify_ind_equation(x,array_list) for x in expr_args(e))




def simplify_ind_equation_array(e,array_list):
        if e[:1]==['ite']:
        	temp=[]
        	count=0
        	ifcase=None
        	elsecase=None
        	status=None
        	for x in expr_args(e):
        		parameter=simplify_ind_equation_array(x,array_list)
        		if count==0:
        			status=evaluateConditionArray(parameter,array_list)
                                if status is not None:
                                    parameter=status
        		elif count==1:
        			ifcase=parameter
        		elif count==2:
        			elsecase=parameter
        		temp.append(parameter)
        		count=count+1
        	if status is None:
        		return ifcase
        	else:
        		return e[:1]+temp
        else:
        	return e[:1]+list(simplify_ind_equation_array(x,array_list) for x in expr_args(e))


def evaluateConditionArray(e,array_list):
	if e[:1]==['and']:
		status=None
                temp=[]
		for x in expr_args(e):
			parameter=simplify_ind_equation(x,array_list)
                        left=expr2string1(parameter[1])
                        right=expr2string1(parameter[2])
			expression=expr2string1(parameter)
			if  parameter[0]== '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression and left in array_list and right in array_list:
                                    c_status=simplify(left)==simplify(right)
                                    if c_status==False :
                                        return 
                        else:
                            temp.append(x)
                if len(temp)>0:
                    return e[:1]+temp
                else:
                    return None
        else:
            return e







#def evaluateCondition(e,array_list):
#	if e[:1]==['and']:
#		status=None
#		for x in expr_args(e):
#			parameter=simplify_ind_equation(x,array_list)
#			expression=expr2string1(parameter)
#			if  parameter[0]== '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression:
#				left=expr2string1(parameter[1])
#				right=expr2string1(parameter[2])
#				c_status=simplify(left)==simplify(right)
#				if c_status==True:
#					if status==None:
#						status='True'
#					elif status=='Unknown':
#						status='Unknown'
#					elif status=='False':
#						status='False'
#					elif status=='True':
#						status='True'
#					else:
#						status='Unknown'
#				elif c_status==False and left in array_list and right in array_list:
#					status='False'
#                                elif c_status==False and status==None:
#                                        status='False'
#				else:
#					if status=='False':
#                                                #status_ieq1=simplify(left)>=simplify(right)
#                                                #status_ieq2=simplify(left)<=simplify(right)
#                                                #if status_ieq1==False
#						status='False'
#					else:
#						status_ieq2=simplify(simplify(left)<=simplify(right))
#						status_ieq1=simplify(simplify(left)>=simplify(right))
#                                                if status_ieq1==True and status_ieq2==False:
#                                                    status='False'
#                                                elif status_ieq1==False and status_ieq2==True:
#                                                    status='False'
#                                                else:
#                                                    status='Unknown'
#			else:
#				if status=='False':
#					status='False'
#				else:
#					status='Unknown'
#		return status
#	elif e[:1]==['or']:
#		status=None
#		for x in expr_args(e):
#			parameter=simplify_ind_equation(x,array_list)
#			expression=expr2string1(parameter)
#			if  parameter[0] is '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression:
#				left=expr2string1(expr2string1(parameter[1]))
#				right=expr2string1(expr2string1(parameter[2]))
#				c_status=simplify(left)==simplify(right)
#				if c_status==True:
#					if status==None:
#						status='True'
#					elif status=='Unknown':
#						status='True'
#					elif status=='False':
#						status='True'
#					elif status=='True':
#						status='True'
#					else:
#						status='Unknown'
#				elif c_status==False and left in array_list and right in array_list:
#					status='False'
#				else:
#					if status=='True':
#						status='True'
#					else:
#						status='Unknown'
#			else:
#				if status=='True':
#					status='True'
#				else:
#					status='Unknown'
#		return status




#def evaluateConditionModify(e,array_list):
#        modify_parameter=[]
#	if e[:1]==['and']:
#		status=None
#		for x in expr_args(e):
#			parameter=simplify_ind_equation(x,array_list)
#			expression=expr2string1(parameter)
#			if  parameter[0]== '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression:
#				left=expr2string1(parameter[1])
#				right=expr2string1(parameter[2])
#				c_status=simplify(left)==simplify(right)
#				if c_status!=True:
#                                    modify_parameter.append(x)
#			else:
#                                modify_parameter.append(x)
#		if len(modify_parameter)==1:
#                    return modify_parameter[0]
#                else:
#                    return e[:1]+modify_parameter
#	elif e[:1]==['or']:
#		status=None
#		for x in expr_args(e):
#			parameter=simplify_ind_equation(x,array_list)
#			expression=expr2string1(parameter)
#			if  parameter[0] is '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression:
#				left=expr2string1(expr2string1(parameter[1]))
#				right=expr2string1(expr2string1(parameter[2]))
#				c_status=simplify(left)==simplify(right)
#				if c_status!=True:
#                                    modify_parameter.append(x)
#                        else:
#                            modify_parameter.append(x)
#		if len(modify_parameter)==1:
#                    return modify_parameter[0]
#                else:
#                    return e[:1]+modify_parameter



def evaluateCondition(e,array_list):
	if e[:1]==['and']:
		status=None
		for x in expr_args(e):
			parameter=simplify_ind_equation(x,array_list)
			expression=expr2string1(parameter)
			if  parameter[0]== '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression:
				left=expr2string1(parameter[1])
				right=expr2string1(parameter[2])
				c_status=simplify(left)==simplify(right)
				if c_status==True:
					if status==None:
						status='True'
					elif status=='Unknown':
						status='Unknown'
					elif status=='False':
						status='False'
					elif status=='True':
						status='True'
					else:
						status='Unknown'
				elif c_status==False and left in array_list and right in array_list:
					status='False'
                                elif c_status==False and status==None:
                                        status='False'
				else:
					if status=='False':
                                                #status_ieq1=simplify(left)>=simplify(right)
                                                #status_ieq2=simplify(left)<=simplify(right)
                                                #if status_ieq1==False
						status='False'
					else:
						status_ieq2=simplify(simplify(left)<=simplify(right))
						status_ieq1=simplify(simplify(left)>=simplify(right))
                                                if status_ieq1==True and status_ieq2==False:
                                                    status='False'
                                                elif status_ieq1==False and status_ieq2==True:
                                                    status='False'
                                                else:
                                                    status='Unknown'
			else:
				if status=='False':
					status='False'
				else:
					status='Unknown'
		return status
	elif e[:1]==['or']:
		status=None
		for x in expr_args(e):
			parameter=simplify_ind_equation(x,array_list)
			expression=expr2string1(parameter)
			if  parameter[0] is '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression:
				left=expr2string1(expr2string1(parameter[1]))
				right=expr2string1(expr2string1(parameter[2]))
				c_status=simplify(left)==simplify(right)
				if c_status==True:
					if status==None:
						status='True'
					elif status=='Unknown':
						status='True'
					elif status=='False':
						status='True'
					elif status=='True':
						status='True'
					else:
						status='Unknown'
				elif c_status==False and left in array_list and right in array_list:
					status='False'
				else:
					if status=='True':
						status='True'
					else:
						status='Unknown'
			else:
				if status=='True':
					status='True'
				else:
					status='Unknown'
		return status
        elif e[:1]==['='] and e[1][0] in array_list and  e[1][0] in array_list and e[1][0]!=e[2][0]:
            status='False'
            return status
        elif e[:1]==['='] and e[1][0] in array_list and  e[1][0] in array_list and e[1][0]==e[2][0]:
            status='True'
            return status
            


def evaluateConditionModify(e,array_list):
        modify_parameter=[]
	if e[:1]==['and']:
		status=None
		for x in expr_args(e):
			parameter=simplify_ind_equation(x,array_list)
			expression=expr2string1(parameter)
			if  parameter[0]== '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression:
				left=expr2string1(parameter[1])
				right=expr2string1(parameter[2])
				c_status=simplify(left)==simplify(right)
				if c_status!=True:
                                    modify_parameter.append(x)
			else:
                                modify_parameter.append(x)
		if len(modify_parameter)==1:
                    return modify_parameter[0]
                else:
                    return e[:1]+modify_parameter
	elif e[:1]==['or']:
		status=None
		for x in expr_args(e):
			parameter=simplify_ind_equation(x,array_list)
			expression=expr2string1(parameter)
			if  parameter[0] is '=' and 'and' not in expression and 'or' not in expression and 'implies' not in expression and 'ite' not in expression:
				left=expr2string1(expr2string1(parameter[1]))
				right=expr2string1(expr2string1(parameter[2]))
				c_status=simplify(left)==simplify(right)
				if c_status!=True:
                                    modify_parameter.append(x)
                        else:
                            modify_parameter.append(x)
		if len(modify_parameter)==1:
                    return modify_parameter[0]
                else:
                    return e[:1]+modify_parameter
















def expr2python(e,tab):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2python(args[0],tab)
            else:
                return '('+(' '+op+' ').join(list(expr2python(x,tab) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2python(args[0],tab)
        elif op=='implies' and len(args)==2:
            return expr2python(args[0],tab)+ ' -> '+expr2python(args[1],tab)
        elif op in _infix_op and len(args)==2:
            return '(' + expr2python(args[0],tab)+ op+expr2python(args[1],tab)+')'
        else:
            if op is 'ite':
            	cond = expr2python(args[0],tab+'\t')
            	expresion1 = expr2python(args[1],tab+'\t')
            	expresion2 =  expr2python(args[2],tab+'\t')
            	return '\n'+tab+'if '+cond+' : \n'+tab+'\treturn '+expresion1+'\n'+tab+'else : \n'+tab+'\treturn '+expresion2+'\n'
            else:
            	return op +'('+ ','.join(list(expr2python(x,tab) for x in args))+ ')'









#Get Variable Type

def getVariableType(variable,allvariablelist):
	for var in allvariablelist.keys():
		if var in variable and variable[0] is not '_':
                        if var+var in variable:
                            #print '$$$$$$$$$$$$$$'
                            variableType=allvariablelist[var+var]
                            #print allvariablelist['bb'].
                            #print allvariablelist
                            #print variableType.getVariableType()
                            #print '$$$$$$$$$$$$$$'
                            return variableType.getVariableType()
                        else:
                            variableType=allvariablelist[var]
                            return variableType.getVariableType()
                elif '__VERIFIER_nondet_double' in variable:
                        return 'double'
                elif '__VERIFIER_nondet_float' in variable:
                        return 'float'
                elif '__VERIFIER_nondet_int' in variable:
                        return 'int'
                elif '__VERIFIER_nondet_uint' in variable:
                        return 'int'
	return None


#Is Variable a Array

def isVariableArray(variable,allvariablelist):
    
	for var in allvariablelist.keys():
		#if var in variable:                    
                if isTempVar(variable,var)==True or variable==var:
                        if isTempVar(variable,var+var)==True:
                            variableType=allvariablelist[var+var]
                            return variableType.getDimensions()
                        else:
                            variableType=allvariablelist[var]
                            return variableType.getDimensions()
	return None

#variable='maker1'
#pattern='maker'
#isTempVar( 'maker1', 'maker')
def isTempVar( variable, pattern):
	status=False
        reg_expreesion=""+pattern+"\d"
        find=regex.compile(reg_expreesion)
	group = find.search(variable)
        find1=regex.compile(""+pattern+"\d[_]")
	group1 = find1.search(variable)
	if group is not None:
		status=True
        if group1 is not None:
		status=False
	return status



#expression to z3 constraint
def expr2z3(e,var_cstr_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        if isvariable(op)==True:
    		var_cstr_map[op]=op+">=0"
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2z3(args[0],var_cstr_map)
            else:
                parameter1=None
                parameter2=None
                for x in args:
                    if parameter1==None:
                    	parameter1=expr2z3(x,var_cstr_map)
                    else:
                    	parameter2=expr2z3(x,var_cstr_map)
                if op=='or':
                	return 'Or('+parameter1+','+parameter2+')'
                else:
                	if op=='and':
                		return 'And('+parameter1+','+parameter2+')'
                #return '('+(' '+op+' ').join(list(expr2z3(x,var_cstr_map) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'Not('+expr2z3(args[0],var_cstr_map)+')'
        elif op=='implies' and len(args)==2:
            
            if len(var_cstr_map)==0:
            	return 'Implies('+expr2z3(args[0],var_cstr_map)+ ','+expr2z3(args[1],var_cstr_map)+')'
            else:
            	list_constrn=""
                for x in var_cstr_map:
            		if list_constrn=="":
            			list_constrn="And("+expr2z3(args[0],var_cstr_map)+","+var_cstr_map[x]+")"
            		else:
            			list_constrn="And("+list_constrn+","+var_cstr_map[x]+")"
            	return 'Implies('+list_constrn+ ','+expr2z3(args[1],var_cstr_map)+')'
        elif op in _infix_op and len(args)==2:
            return '((' + expr2z3(args[0],var_cstr_map)+')'+ op+'('+expr2z3(args[1],var_cstr_map)+'))'
        else:
            return op +'('+ ','.join(list(trim_p(expr2z3(x,var_cstr_map)) for x in args))+ ')'





#expression to z3 constraint

#e=['or', ['or', ['or', ['<=', ['B'], ['0']], ['<=', ['A'], ['0']]], ['<=', ['+', ['A'], ['B']], ['B']]], ['<=', ['+',['A'], ['B']], ['A']]]

#e=['+', ['*', ['*', ['/', ['B'], ['']], ['/', ['A'], ['C']]], ['+', ['+', ['A'], ['B']], ['B']]], ['-', ['+',['A'], ['B']], ['A']]]

#e=['Y3', ['+', ['_n1'], ['1']], ['A'], ['B']], ['ite', ['>', ['A'], ['B']], ['Y3', ['_n1'], ['A'], ['B']], ['+', ['A'], ['*', ['2'], ['B']]]]

#e=['ite', ['>', ['A'], ['B']], ['Y3', ['_n1'], ['A'], ['B']], ['+', ['A'], ['*', ['2'], ['B']]]]

#e=['==', ['d1array3', ['a'], ['+', ['+', ['_k1'], ['1']], ['0']], ['+', ['+', ['_k1'], ['1']], ['1']]], ['d1array3', ['b'], ['+', ['*', ['9'], ['+', ['_k1'], ['1']]], ['1']], ['+', ['_k1'], ['1']]]]

#var_cstr_map={}

def expr2z3_update(e,var_cstr_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        if isvariable(op)==True:
    		var_cstr_map[op]=op+">=0"
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
            	expression=expr2z3_update(args[0],var_cstr_map)
            	if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'If' not in expression and 'Implies' not in expression:
            		expression=simplify_expand_sympy(expression)
                return expression
            else:
                e_array=[]
                for x in args:
                	parameter1=expr2z3_update(x,var_cstr_map)
                    	if '/' not in parameter1 and 'Or' not in parameter1 and '==' not in parameter1 and 'And' not in parameter1 and 'If' not in parameter1 and 'Implies' not in parameter1:                    		
                    		parameter1=convert_pow_op_fun(simplify_expand_sympy(parameter1))
                                
                    	elif 'Or' not in parameter1 and 'And' not in parameter1 and 'If' not in parameter1 and 'Implies' not in parameter1:
                    		parameter1=convert_pow_op_fun(parameter1)
                    	e_array.append(parameter1)
                if op=='or':
                	#return 'Or('+parameter1+','+parameter2+')'
                	return constructAndOr(e_array,'Or')
                else:
                	if op=='and':
                		#return 'And('+parameter1+','+parameter2+')'
                		return constructAndOr(e_array,'And')
        elif op=='not' and len(args)==1:
            expression=expr2z3_update(args[0],var_cstr_map)
            if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'If' not in expression and 'Implies' not in expression:
            	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            elif 'Or' not in expression and 'And' not in expression and 'If' not in expression and 'Implies' not in expression:
            	expression=convert_pow_op_fun(expression)
            return 'Not('+expression+')'
        elif op=='implies' and len(args)==2:
            if len(var_cstr_map)==0:
            	expression1=expr2z3_update(args[0],var_cstr_map)
            	expression2=expr2z3_update(args[1],var_cstr_map)
            	if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
            		expression1=convert_pow_op_fun(simplify_expand_sympy(expression1))
            	elif 'Or' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
			expression1=convert_pow_op_fun(expression1)
            	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
            		expression2=convert_pow_op_fun(simplify_expand_sympy(expression2))
            	elif 'Or' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
			expression2=convert_pow_op_fun(expression2)
            	return 'Implies('+expression1+ ','+expression2+')'
            else:
            	list_constrn=""
                for x in var_cstr_map:
            		if list_constrn=="":
            			expression1=expr2z3_update(args[0],var_cstr_map)
            			if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
            				expression1=convert_pow_op_fun(simplify_expand_sympy(expression1))
            			elif 'Or' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
					expression1=convert_pow_op_fun(expression1)
            			list_constrn="And("+expression1+","+var_cstr_map[x]+")"
            		else:
            			list_constrn="And("+list_constrn+","+var_cstr_map[x]+")"
            	expression2=expr2z3_update(args[1],var_cstr_map)
            	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
            		expression1=simplify_expand_sympy(expression2)
            	elif 'Or' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
			expression2=convert_pow_op_fun(expression2)
            	return 'Implies('+list_constrn+ ','+expression2+')'
        elif op in _infix_op and len(args)==2:
        	expression1=expr2z3_update(args[0],var_cstr_map)
        	expression2=expr2z3_update(args[1],var_cstr_map)
        	if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
        		expression1=simplify_expand_sympy(expression1)
        	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
        		expression2=simplify_expand_sympy(expression2)
        	if op=='/':
        		return '((' + expression1+')'+op+'('+expression2+'))'
                elif op=='**':
                        if expression2=='2':
                            return expression1+'*'+expression1
                        else:
                            return 'power((' + expression1+')'+','+'('+expression2+'))'
        	elif op=='=':
                    
        		return '((' + expression1+ ')==('+expression2+'))'
        	else:
        		if op=='*':
                            expression='((' + expression1+')'+ op+'('+expression2+'))'
                        else:
                            expression='((' + expression1+')'+ op+'('+expression2+'))'
        		if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and '.' not in expression:
        			return simplify_expand_sympy(expression)
        		else:
        			return expression
        else:
            if op=='ite':
            	return 'If('+ ','.join(list(conditionSimplifyPower(expr2z3_update(x,var_cstr_map)) for x in args))+ ')'
            else:
            	if isArrayFunction(op)==True:
            		parameter_list=[]
            		defineDetailtemp=[]
            		defineDetailtemp.append(op)
            		parameter_list.append('array')
            		for x in range(0, len(args)):
            			parameter_list.append('int')
            		defineDetailtemp.append(len(args))
            		defineDetailtemp.append(parameter_list)
            		defineDetaillist.append(defineDetailtemp)
            	return op +'('+ ','.join(list(expr2z3_update(x,var_cstr_map) for x in args))+ ')'





def expr2z3_update1(e,var_cstr_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        if isvariable(op)==True:
    		var_cstr_map[op]=op+">=0"
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
            	expression=expr2z3_update1(args[0],var_cstr_map)
                return expression
            else:
                e_array=[]
                for x in args:
                	parameter1=expr2z3_update1(x,var_cstr_map)
                    	e_array.append(parameter1)
                if op=='or':
                	#return 'Or('+parameter1+','+parameter2+')'
                	return constructAndOr(e_array,'Or')
                else:
                	if op=='and':
                		#return 'And('+parameter1+','+parameter2+')'
                		return constructAndOr(e_array,'And')
        elif op=='not' and len(args)==1:
            expression=expr2z3_update1(args[0],var_cstr_map)
            return 'Not('+expression+')'
        elif op=='implies' and len(args)==2:
            if len(var_cstr_map)==0:
            	expression1=expr2z3_update1(args[0],var_cstr_map)
            	expression2=expr2z3_update1(args[1],var_cstr_map)
            	return 'Implies('+expression1+ ','+expression2+')'
            else:
            	list_constrn=""
                for x in var_cstr_map:
            		if list_constrn=="":
            			expression1=expr2z3_update1(args[0],var_cstr_map)
            			list_constrn="And("+expression1+","+var_cstr_map[x]+")"
            		else:
            			list_constrn="And("+list_constrn+","+var_cstr_map[x]+")"
            	expression2=expr2z3_update1(args[1],var_cstr_map)
            	return 'Implies('+list_constrn+ ','+expression2+')'
        elif op in _infix_op and len(args)==2:
        	expression1=expr2z3_update1(args[0],var_cstr_map)
        	expression2=expr2z3_update1(args[1],var_cstr_map)
        	if op=='/':
        		return '((' + expression1+')'+op+'('+expression2+'))'
                elif op=='**':
                        if expression2=='2':
                            return expression1+'*'+expression1
                        else:
                            return 'power((' + expression1+')'+','+'('+expression2+'))'
        	elif op=='=':
                    
        		return '((' + expression1+ ')==('+expression2+'))'
        	else:
        		if op=='*':
                            expression='((' + expression1+')'+ op+'('+expression2+'))'
                        else:
                            expression='((' + expression1+')'+ op+'('+expression2+'))'
                        return expression
        else:
            if op=='ite':
            	return 'If('+ ','.join(list(expr2z3_update1(x,var_cstr_map) for x in args))+ ')'
            else:
            	if isArrayFunction(op)==True:
            		parameter_list=[]
            		defineDetailtemp=[]
            		defineDetailtemp.append(op)
            		parameter_list.append('array')
            		for x in range(0, len(args)):
            			parameter_list.append('int')
            		defineDetailtemp.append(len(args))
            		defineDetailtemp.append(parameter_list)
            		defineDetaillist.append(defineDetailtemp)
            	return op +'('+ ','.join(list(expr2z3_update1(x,var_cstr_map) for x in args))+ ')'














def constructAndOr(e_array,operator):
	if len(e_array)>2:
		return operator+'('+e_array[0]+','+constructAndOr(e_array[1:],operator)+')'
	if len(e_array)==2:
		return operator+'('+e_array[0]+','+e_array[1]+')'
	else:
		return e_array[0]
                
                
def constructAndOrArray(e_array,operator):
	if len(e_array)>2:
		return eval("['"+operator+"',"+str(e_array[0])+','+str(constructAndOrArray(e_array[1:],operator))+']')
	if len(e_array)==2:
		return eval("['"+operator+"',"+str(e_array[0])+','+str(e_array[1])+']')
	else:
		return e_array[0]





def expr2z3_update_postCond(e,var_cstr_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        if isvariable(op)==True:
    		var_cstr_map[op]=op+">=0"
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
            	expression=expr2z3_update_postCond(args[0],var_cstr_map)
            	if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'Implies' not in expression and 'If' not in expression:
            		expression=simplify_expand_sympy(expression)
                return expression
            else:
                parameter1=None
                parameter2=None
                for x in args:
                    if parameter1==None:
                    	parameter1=expr2z3_update_postCond(x,var_cstr_map)
                    	if '/' not in parameter1 and 'Or' not in parameter1 and '==' not in parameter1 and 'And' not in parameter1 and 'Implies' not in parameter1 and 'If' not in parameter1:
                    		parameter1=convert_pow_op_fun(simplify_expand_sympy(parameter1))
                    	elif 'Or' not in parameter1 and 'And' not in parameter1 and 'If' not in parameter1 and 'Implies' not in parameter1 and 'If' not in parameter1:
                    		parameter1=convert_pow_op_fun(parameter1)
                    else:
                    	parameter2=expr2z3_update_postCond(x,var_cstr_map)
                    	if '/' not in parameter2 and 'Or' not in parameter2 and '==' not in parameter2 and 'And' not in parameter2 and 'Implies' not in parameter2 and 'If' not in parameter2:
                    		parameter2=convert_pow_op_fun(simplify_expand_sympy(parameter2))
                    	elif 'Or' not in parameter2 and 'And' not in parameter2 and 'If' not in parameter2 and 'Implies' not in parameter2 and 'If' not in parameter2:
                    		parameter2=convert_pow_op_fun(parameter2)
                if op=='or':
                	return 'Or('+parameter1+','+parameter2+')'
                else:
                	if op=='and':
                		return 'And('+parameter1+','+parameter2+')'
        elif op=='not' and len(args)==1:
            expression=expr2z3_update_postCond(args[0],var_cstr_map)
            if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'Implies' not in expression and 'If' not in expression:
            	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            elif 'Or' not in expression and 'And' not in expression and 'Implies' not in expression and 'If' not in expression:
            	expression=convert_pow_op_fun(expression)
            return 'Not('+expression+')'
        elif op=='implies' and len(args)==2:
            if len(var_cstr_map)==0:
            	expression1=expr2z3_update_postCond(args[0],var_cstr_map)
            	expression2=expr2z3_update_postCond(args[1],var_cstr_map)
            	if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
            		expression1=convert_pow_op_fun(simplify_expand_sympy(expression1))
            	elif 'Or' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
			expression1=convert_pow_op_fun(expression1)
            	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
            		expression2=convert_pow_op_fun(simplify_expand_sympy(expression2))
            	elif 'Or' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
			expression2=convert_pow_op_fun(expression2)
            	return 'Implies('+expression1+ ','+expression2+')'
            else:
            	list_constrn=""
                for x in var_cstr_map:
            		if list_constrn=="":
            			expression1=expr2z3_update_postCond(args[0],var_cstr_map)
            			if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
            				expression1=convert_pow_op_fun(simplify_expand_sympy(expression1))
            			elif 'Or' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
					expression1=convert_pow_op_fun(expression1)
            			list_constrn="And("+expression1+","+var_cstr_map[x]+")"
            		else:
            			list_constrn="And("+list_constrn+","+var_cstr_map[x]+")"
            	expression2=expr2z3_update_postCond(args[1],var_cstr_map)
            	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
            		expression1=simplify_expand_sympy(expression2)
            	elif 'Or' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
			expression2=convert_pow_op_fun(expression2)
            	return 'Implies('+list_constrn+ ','+expression2+')'
        elif op in _infix_op and len(args)==2:
        	expression1=expr2z3_update_postCond(args[0],var_cstr_map)
        	expression2=expr2z3_update_postCond(args[1],var_cstr_map)
        	if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
        		expression1=simplify_expand_sympy(expression1)
        	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
        		expression2=simplify_expand_sympy(expression2)
        	if op=='/':
        		return '(' + expression1+ op+expression2+')'
                elif op=='**':
                    if is_number(expression1)==True and is_number(expression2)==True:
                        return str(simplify(expression1+"**"+expression2))
                    else:
                        return 'power((' + expression1+')'+','+'('+expression2+'))'
        	elif op=='=':
        		return '((' + expression1+ ')==('+expression2+'))'
        	else:
        		expression='((' + expression1+')'+ op+'('+expression2+'))'
        		if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'Implies' not in expression and 'If' not in expression:
        			return simplify_expand_sympy(expression)
        		else:
        			return expression
        else:
            if op=='ite':
            	stmt_list=[]
            	final_stmt=''
            	for x in args:
            		stmt=conditionSimplifyPower(expr2z3_update_postCond(x,var_cstr_map))
            		if str(stmt)!='0':
            			stmt_list.append(stmt)
                        elif str(stmt)=='0' and '>' not in args[1] and '<' not in args[1] :
                                stmt_list.append(stmt)
            	if len(stmt_list)==2:
            		final_stmt='Implies('+final_stmt+','.join(stmt_list)+')'
            	else:
            		final_stmt='If('+final_stmt+','.join(stmt_list)+')'
            	return final_stmt
            else:
                if isArrayFunction(op)==True:
	        	parameter_list=[]
	                defineDetailtemp=[]
	                defineDetailtemp.append(op)
	                parameter_list.append('array')
	                for x in range(0, len(args)):
	                	parameter_list.append('int')
	                defineDetailtemp.append(len(args))
	                defineDetailtemp.append(parameter_list)
            		defineDetaillist.append(defineDetailtemp)
            	return op +'('+ ','.join(list(expr2z3_update_postCond(x,var_cstr_map) for x in args))+ ')'









def conditionSimplifyPower(expression):
	if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'If' not in expression and 'char(' not in expression and 'Implies' not in expression:
		return convert_pow_op_fun(simplify_expand_sympy(expression))
	elif 'Or' not in expression and 'And' not in expression and 'If' not in expression and 'char(' not in expression and 'Implies' not in expression:
		return convert_pow_op_fun(expression)
	else:
		return expression

#get variable
def expr2varlist(e,variable_list):
    args=expr_args(e)    
    op=expr_op(e)
    if len(args)==0:
    	if '_n' not in op and is_number(op)==False:
    		variable_list.append(op)
    else:
        if op=='and' or op=='or':
            if len(args)==1:
               expr2varlist(args[0],variable_list)
            else:
                for x in args:
                    expr2varlist(x,variable_list)
        elif op=='not' and len(args)==1:
            expr2varlist(args[0],variable_list)
        elif op=='implies' and len(args)==2:
        	expr2varlist(args[0],variable_list)
        	expr2varlist(args[1],variable_list)
        elif op in _infix_op and len(args)==2:
        	expr2varlist(args[0],variable_list)
        	expr2varlist(args[1],variable_list)
        else:
            for x in args:
        	expr2varlist(x,variable_list)


#return the list of program variables in an expression 

def expr_func(e,v): #e - expr
    ret = []
    f = expr_op(e)
    if is_program_var(f,v) or '__VERIFIER_nondet' in f:
        ret.append(f)
    for e1 in expr_args(e):
        ret = ret + expr_func(e1,v)
    return ret
    

#substitution of functors: in e, replace functor n1 by n2
def expr_sub(e,n1,n2): # e - expr; n1,n2 - strings
    e1=list(expr_sub(x,n1,n2) for x in e[1:])
    if e[0]==n1:
        return [n2]+e1
    else:
        return e[:1]+e1
        

#substitution of functors in a set: in e, for all x in v1 but not in v2, replace x+n1 by x+n2
def expr_sub_set(e,n1,n2,v1,v2): #e - expr; n1,n2 - strings, v1, v2 - sets of strings
    e1 = list(expr_sub_set(e2,n1,n2,v1,v2) for e2 in e[1:])
    if e[0].endswith(n1):
        x = e[0][:len(e[0])-len(n1)]
        if (x in v1) and (not x in v2):
            return [x+n2]+e1
        else:
            return e[:1]+e1
    else:
        return e[:1]+e1
        
        

# expr_replace(e,e1,e2): replace all subterm e1 in e by e2

def expr_replace(e,e1,e2): #e,e1,e2: expr
    if e==e1:
        return e2
    else:
        return e[:1]+list(expr_replace(x,e1,e2) for x in expr_args(e))
        
        

# expr_sub_dict(e,d): d is a dictonary of substitutions: functor 'f' to e1=d['f'] so that in e, each f term f(t1,...,tk) is replaced by e1(_x1/t1,...,_xk/tk)

def expr_sub_dict(e,d):
    args = expr_args(e)
    args1 = list(expr_sub_dict(x,d) for x in args)
    if expr_op(e) in d:
        return expr_sub_var_list(d[expr_op(e)],list(expres('_x'+str(i+1)) for i in range(len(args))),args1)
    else:
        return expres(expr_op(e),args1)
        

# expr_sub_var_list(e,l1,l2): in e, replace all terms in l1 by the corresponding terms in l2

def expr_sub_var_list(e,l1,l2): #e: expr, l1,l2: lists of the same length of exprs
    for i,x in enumerate(l1):
        if e==x:
            return l2[i]
    return e[:1]+list(expr_sub_var_list(y,l1,l2) for y in expr_args(e))


# compute E[n] extend(e,n,excl,v). n is an expr like ['_n1'], excl is a container of strings that are not to be extended
def extend(e,n,excl,v):
    op = expr_op(e)
    x = [n] if (is_program_var(op,v) and not (op in excl)) or '__VERIFIER_nondet' in op else []
    return expres(op, list(extend(e1,n,excl,v) for e1 in expr_args(e)) + x)


#A dictionary of dependencies para is such that, if x is an input variable, then para[x] is a list whose first element is 1 and the second element is the variable's parameter name; otherwise, para[x] is the list of input variables that x is depended on. 
#example: para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'], ['X','Y']],...} meaning 'X' is an input variable parameterized as '_y1' and 'X11' is a function depending on X and Y whose corresponding parameters are '_y1' and '_y2', respectively.
#So after parameterization, X11(a,X) will become X11(a,_y1,_y1,_y2)

def parameterize_expres(e,para): 
    if e[0] in para:
        if para[e[0]][0] == 1:
            return para[e[0]][1]+list(parameterize_expres(x,para) for x in e[1:])
        else:
            return e[:1]+list(parameterize_expres(x,para) for x in e[1:])+para[e[0]][1]
    else:
        return e[:1]+list(parameterize_expres(x,para) for x in e[1:])


#parameterize non-input functions then restore the input variables to its name
#given above para, X11(a,X) will become X11(a,X,X,Y), assuming that _y2 corresponds to Y

def parameterize_expr_sub(e,para): 
    if e[0] in para:
        if para[e[0]][0] == 1:
            return [e[0]]+list(parameterize_expr_sub(x,para) for x in e[1:])
        else:
            return e[:1]+list(parameterize_expr_sub(x,para) for x in e[1:])+para[e[0]][2]
    else:
        return e[:1]+list(parameterize_expr_sub(x,para) for x in e[1:])




        


"""
 Formulas:
 1. equations f(x) = e: ['e',e1,e2], 
    where e1 is expression for f(x) and e2 for e
 2. inductive definition:
 - base case f(x1,...,xk,0,...,xm)=e: ['i0',k,e1,e2] 
   where e1 is Expr for f(x1,...,xk,0,...,xm) and e2 the Expr for e
 - inductive case f(x1,...,xk,n+1,...,xm)=e: ['i1',k,'n',e1,e2] 
    where e1 is Expr for f(x1,...,xk,n+1,...,xm) and e2 the Expr for e
 3. inductive definition for functions that return natural numbers 
    (like N in smallest macro):
 - base case f(x) = 0 iff C: ['d0',e,c] 
   where e is the Expr for f(x) and c an expression for condition C
 - inductive case f(x) = n+1 iff C(n): ['d1','n',e,c] 
   where e is the Expr for f(x) and c an Expr for condition C
 4. any other axioms: A: ['a',e], where e is the Expr for A
 5. constraints from smallest macro smallest(N,n,e):
    ['s0', e(N)] 
    ['s1', forall n<N -> not e]

 Examples: a' = a+1: ['e', ['a\''], ['+',['a'],['1']]]
 N(x) = 0 if x<I else N(x-1)+1 is divided into two axioms:
 N(x) = 0 iff x<I:  
 ['d0', ['N',['x']], ['<', ['x'],['I']]] and
 N(x) = n+1 iff n=N(x-1): 
 ['d1','n', ['N',['x']], ['=',['n'], ['N', ['-', ['x'],['1']]]]]
"""


# constructors
def wff_e(e1,e2): #e1,e2: expr
    return ['e',e1,e2]

def wff_i0(k,e1,e2): #k: int; e1,e2: expr
    return ['i0',k,e1,e2]

def wff_i1(k,v,e1,e2): #k: int; v: string; e1,e2: expr
    return ['i1',k,v,e1,e2]

def wff_d0(e,c): #e: expr; c: expr
    return ['d0',e,c]

def wff_d1(v,e,c): #v: string, e and c: expr
    return ['d1',v,e,c]

def wff_a(e): #e: expr
    return ['a',e]

def wff_s0(e):
    return ['s0',e]
def wff_s1(e):
    return ['s1',e]
    
def wff_c1(e):
    return ['c1',e]

    
    
#print in prefix notation
def wff2string(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1' or w[0] == 'R':
            return '(= '+expr2string(w[-2])+' '+expr2string(w[-1]) +')'
        elif w[0] == 'd0':
            return '(iff (= '+expr2string(w[1])+' 0) '+ expr2string(w[2])+')'
        elif w[0] == 'd1':
            return '(iff (= '+expr2string(w[2])+' (+ '+w[1]+' 1)) '+expr2string(w[3])+')'
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1' or w[0]=='c1' or w[0] == 'R':
            return expr2string(w[1])

#print in normal infix notation
def wff2string1(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1' or w[0] == 'i2' or w[0] == 'R':
            return expr2string1(w[-2])+' = '+ expr2string1(w[-1])
        elif w[0] == 'd0':
            return expr2string1(w[1])+'=0 <=> '+ expr2string1(w[2])
        elif w[0] == 'd1':
            return expr2string1(w[2])+'='+w[1]+'+1 <=> '+expr2string1(w[3])
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1' or w[0]=='c1':
            return expr2string1(w[1])

            
#print in normal infix notation
def wff2stringvfact(w,var_map):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1' or w[0] == 'R':
            return expr2stringvfact(w[-2],var_map)+' = '+ expr2stringvfact(w[-1],var_map)
        elif w[0] == 'd0':
            return expr2stringvfact(w[1],var_map)+'=0 <=> '+ expr2stringvfact(w[2],var_map)
        elif w[0] == 'd1':
            return expr2stringvfact(w[2],var_map)+'='+w[1]+'+1 <=> '+expr2stringvfact(w[3],var_map)
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1' or w[0]=='c1':
            return expr2stringvfact(w[1],var_map)



#print in normal infix notation
def wff2stringvfact2(w,var_map,allvariablelist,constraints):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1' or w[0] == 'R':
            return expr2stringvfact2(w[-2],var_map,allvariablelist,constraints)+' = '+ expr2stringvfact2(w[-1],var_map,allvariablelist,constraints)
        elif w[0] == 'd0':
            return expr2stringvfact2(w[1],var_map,allvariablelist,constraints)+'=0 <=> '+ expr2stringvfact2(w[2],var_map,allvariablelist,constraints)
        elif w[0] == 'd1':
            return expr2stringvfact2(w[2],var_map,allvariablelist,constraints)+'='+w[1]+'+1 <=> '+expr2stringvfact2(w[3],var_map,allvariablelist,constraints)
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1' or w[0]=='c1' :
            return expr2stringvfact2(w[1],var_map,allvariablelist,constraints)



def getConstraints_Eq(w,allvariablelist,constraints):
    if w[0] == 'i1':
        temp_eq=copy.deepcopy(w[3])
        temp_eq=expr_replace(temp_eq,eval("['+',['"+w[2]+"'],['1']]"),eval("['"+w[2]+"']"))
        if isArrayFunction(w[3][0])==False:
            typename=getVariableType(w[3][0],allvariablelist)
            if typename=='unsigned':
                con_equ=[]
                con_equ.append('c1')
                con_equ1=[]
                con_equ1.append('>=')
                con_equ1.append(temp_eq)
                con_equ1.append(eval("['0']"))
                con_equ.append(con_equ1)
                return wff2z3_update_postCond(con_equ)
    return None

    




#strip '(' at the beginning and matching ')' in the end of a string
def trim_p(s):
    if s.startswith('(') and s.endswith(')'):
        return trim_p(s[1:-1])
    else:
        return s


#convert wff to z3 constraint
def wff2z3(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            lhs=expr2z3(w[-2],var_cstr_map)
            rhs=expr2z3(w[-1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	#return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
                else:
                	return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[1],var_cstr_map)
            rhs=expr2z3(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+'=0 == '+ rhs+"))"
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[2],var_cstr_map)
            rhs=expr2z3(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(w[1]+'+1'))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+rhs+"))"
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())
                    old_arg_list=arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        #equations.append('ForAll(['+str(list_var_str_new)+'],Implies('+str(list_cstr_str_new)+','+arg_list[1]+'))')
                        #return equations
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        #equations.append(arg_list[1])
                        #return equations
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
        elif w[0] == 'R':
            var_cstr_map={}
            lhs=expr2z3(w[2],var_cstr_map)
            rhs=expr2z3(w[3],var_cstr_map)
            list_var_str=qualifier_list(w[1])
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs

        else:
            return expression







#convert wff to z3 constraint
def wff2z3_update(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            flag_constr=False
            lhs=expr2z3_update(w[-2],var_cstr_map)
            rhs=expr2z3_update(w[-1],var_cstr_map) 
            list_var_str=qualifier_list(var_cstr_map.keys())
            if isArrayFunction(w[-2][0])==True:
            	if '_x1' in var_cstr_map.keys():
            		del var_cstr_map['_x1']
            	flag_constr=True
            if '_s1' in var_cstr_map.keys():
                del var_cstr_map['_s1']
            	flag_constr=True
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if w[-1][0] in ['==','<=','>=','>','<','!=','or','and']:
                rhs='If(('+rhs+')==0,0,1)'
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                else:
                	if flag_constr==True:
                		return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	else:
                		return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[1],var_cstr_map)
            rhs=expr2z3_update(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=w[1]+'+1'
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3_update(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())

                    new_w = copy.deepcopy(w)
                    for element in var_cstr_map.keys():
                    	fun=[]
                    	fun.append('_f')
                    	parameter=[]
                    	parameter.append(element)
                    	fun.append(parameter)
                    	sub=[]
                    	sub.append(element)
                    	new_w[1]=expr_replace(new_w[1],sub,fun) #expr_replace_const(new_w[1],element,fun)
		    new_expression=expr2z3_update(new_w[1],var_cstr_map)
		    new_arg_list=extract_args(new_expression)
                    
                    #old_arg_list=arg_list[1]
                    old_arg_list=new_arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'

        elif w[0]=='c1':
         	var_cstr_map={}
	      	equations=[]
	    	expression=expr2z3_update(w[1],var_cstr_map)
	    	list_var_str=qualifier_list(var_cstr_map.keys())
	    	list_cstr_str=cstr_list(var_cstr_map.values())
	    	if list_var_str is not None and list_cstr_str is not None:
        		 return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
        	else:
        		 return expression
        elif w[0]=='L1':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update(w[-2],var_cstr_map)
            	rhs=expr2z3_update(w[-1],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())
            	if isArrayFunction(w[-2][0])==True:
            		if '_x1' in var_cstr_map.keys():
            			del var_cstr_map['_x1']
            		flag_constr=True
                if '_s1' in var_cstr_map.keys():
                    del var_cstr_map['_s1']
                    flag_constr=True
            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())
            	if list_cstr_str is not None:
            		constant=w[2].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[2]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str2+','+w[2]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		if w[0] == 'i1':
                		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                	else:
                		if flag_constr==True:
                			return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                		else:
                			return "Implies("+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+","+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+")"
            	else:
                	return "Implies("+lhs+' == '+ rhs+","+lhs+' == '+ rhs+")"
        elif w[0]=='L2':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update(w[2],var_cstr_map)
            	rhs=expr2z3_update(w[3],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())

            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())

            	if list_cstr_str is not None:
            		constant=w[1].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[1]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str+','+w[1]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+rhs+"))"+")"
            	else:
                	return "Implies("+lhs+","+rhs+")"
        elif w[0] == 'R':
            var_cstr_map={}
            lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'RE':
            var_cstr_map={}
            if len(w[2])==0:
                lhs=None
            else:
                lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            if len(w[1])==0:
                list_var_str=None
            else:
                list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                if lhs!='' and lhs is not None:
                    return 'ForAll(['+list_var_str+'],Implies('+lhs+','+rhs+"))"
                else:
                    return 'ForAll(['+list_var_str+'],'+rhs+")"
            elif lhs!='' and lhs is not None:
                return 'Implies('+lhs+','+rhs+")"
            else:
                return rhs

        else:
            return expression





def wff2z3_update_power(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            flag_constr=False
            lhs=expr2z3_update(w[-2],var_cstr_map)
            rhs=expr2z3_update(w[-1],var_cstr_map) 
            list_var_str=qualifier_list(var_cstr_map.keys())
            if isArrayFunction(w[-2][0])==True:
            	if '_x1' in var_cstr_map.keys():
            		del var_cstr_map['_x1']
            	flag_constr=True
            if '_s1' in var_cstr_map.keys():
                del var_cstr_map['_s1']
            	flag_constr=True
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if w[-1][0] in ['==','<=','>=','>','<','!=','or','and']:
                rhs='If(('+rhs+')==0,0,1)'
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                else:
                	if flag_constr==True:
                		return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	else:
                		return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[1],var_cstr_map)
            rhs=expr2z3_update(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=w[1]+'+1'
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3_update(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())

                    new_w = copy.deepcopy(w)
		    new_expression=expr2z3_update(new_w[1],var_cstr_map)
		    new_arg_list=extract_args(new_expression)
                    
                    #old_arg_list=arg_list[1]
                    old_arg_list=new_arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'

        elif w[0]=='c1':
         	var_cstr_map={}
	      	equations=[]
	    	expression=expr2z3_update(w[1],var_cstr_map)
	    	list_var_str=qualifier_list(var_cstr_map.keys())
	    	list_cstr_str=cstr_list(var_cstr_map.values())
	    	if list_var_str is not None and list_cstr_str is not None:
        		 return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
        	else:
        		 return expression
        elif w[0]=='L1':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update(w[-2],var_cstr_map)
            	rhs=expr2z3_update(w[-1],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())
            	if isArrayFunction(w[-2][0])==True:
            		if '_x1' in var_cstr_map.keys():
            			del var_cstr_map['_x1']
            		flag_constr=True
                if '_s1' in var_cstr_map.keys():
                    del var_cstr_map['_s1']
                    flag_constr=True
            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())
            	if list_cstr_str is not None:
            		constant=w[2].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[2]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str2+','+w[2]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		if w[0] == 'i1':
                		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                	else:
                		if flag_constr==True:
                			return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                		else:
                			return "Implies("+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+","+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+")"
            	else:
                	return "Implies("+lhs+' == '+ rhs+","+lhs+' == '+ rhs+")"
        elif w[0]=='L2':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update(w[2],var_cstr_map)
            	rhs=expr2z3_update(w[3],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())

            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())

            	if list_cstr_str is not None:
            		constant=w[1].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[1]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str+','+w[1]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+rhs+"))"+")"
            	else:
                	return "Implies("+lhs+","+rhs+")"
        elif w[0] == 'R':
            var_cstr_map={}
            lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'RE':
            var_cstr_map={}
            if len(w[2])==0:
                lhs=None
            else:
                lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            if len(w[1])==0:
                list_var_str=None
            else:
                list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                if lhs!='' and lhs is not None:
                    return 'ForAll(['+list_var_str+'],Implies('+lhs+','+rhs+"))"
                else:
                    return 'ForAll(['+list_var_str+'],'+rhs+")"
            elif lhs!='' and lhs is not None:
                return 'Implies('+lhs+','+rhs+")"
            else:
                return rhs

        else:
            return expression










#convert wff to z3 constraint
def wff2z3_update1(w,const_var_map):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            flag_constr=False
            lhs=expr2z3_update(w[-2],var_cstr_map)
            rhs=expr2z3_update(w[-1],var_cstr_map) 
            list_var_str=qualifier_list(var_cstr_map.keys())
            #print '----------------------'
            #print list_var_str
            #print '----------------------'
            if isArrayFunction(w[-2][0])==True:
            	if '_x1' in var_cstr_map.keys():
            		del var_cstr_map['_x1']
            	flag_constr=True
            if '_s1' in var_cstr_map.keys():
                del var_cstr_map['_s1']
                flag_constr=True
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if w[-1][0] in ['==','<=','>=','>','<','!=','or','and']:
                rhs='If(('+rhs+')==0,0,1)'
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+",("+lhs+') == ('+ rhs+")))"
                else:
                	if flag_constr==True:
                		return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+",("+lhs+') == ('+ rhs+"))"
                	else:
                		return 'ForAll(['+list_var_str+'],('+lhs+') == ('+ rhs+"))"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[1],var_cstr_map)
            rhs=expr2z3_update(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return 'ForAll(['+list_var_str+'],('+lhs+'=0) == ('+ rhs+"))"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            lhs=w[1]+'+1'
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3_update(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    if '<' in arg_list[0]:
                        constr=simplify(arg_list[0])
                        axms=str(constr).split('<')
                        axms[0]=axms[0].strip()
                        axms[1]=axms[1].strip()
                        arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                        if list_var_str is not None and list_cstr_str is not None:
                            return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                        else:
                            return arg_list[1]
                    else:
                        return expression
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())

                    new_w = copy.deepcopy(w)
                    for element in var_cstr_map.keys():
                    	fun=[]
                    	fun.append('_f')
                    	parameter=[]
                    	parameter.append(element)
                    	fun.append(parameter)
                    	sub=[]
                    	sub.append(element)
                    	new_w[1]=expr_replace(new_w[1],sub,fun) #expr_replace_const(new_w[1],element,fun)
		    new_expression=expr2z3_update(new_w[1],var_cstr_map)
		    new_arg_list=extract_args(new_expression)
                    
                    #old_arg_list=arg_list[1]
                    old_arg_list=new_arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'

        elif w[0]=='c1':
         	var_cstr_map={}
	      	equations=[]
	    	expression=expr2z3_update(w[1],var_cstr_map)
	    	list_var_str=qualifier_list(var_cstr_map.keys())
	    	list_cstr_str=cstr_list(var_cstr_map.values())
                #add by pritom 30/08/2017
                list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
	    	if list_var_str is not None and list_cstr_str is not None:
        		 return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
        	else:
        		 return expression
        elif w[0]=='L1':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update(w[-2],var_cstr_map)
            	rhs=expr2z3_update(w[-1],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())
            	if isArrayFunction(w[-2][0])==True:
            		if '_x1' in var_cstr_map.keys():
            			del var_cstr_map['_x1']
            		flag_constr=True
                if '_s1' in var_cstr_map.keys():
                    del var_cstr_map['_s1']
                    flag_constr=True
            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())
                #add by pritom 30/08/2017
            	if list_cstr_str is not None:
            		constant=w[2].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[2]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str2+','+w[2]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		if w[0] == 'i1':
                		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                	else:
                		if flag_constr==True:
                			return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                		else:
                			return "Implies("+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+","+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+")"
            	else:
                	return "Implies("+lhs+' == '+ rhs+","+lhs+' == '+ rhs+")"
        elif w[0]=='L2':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update(w[2],var_cstr_map)
            	rhs=expr2z3_update(w[3],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())

            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())

            	if list_cstr_str is not None:
            		constant=w[1].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[1]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str+','+w[1]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+rhs+"))"+")"
            	else:
                	return "Implies("+lhs+","+rhs+")"
        elif w[0] == 'R':
            var_cstr_map={}
            lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'RE':
            var_cstr_map={}
            if len(w[2])==0:
                lhs=None
            else:
                lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            if len(w[1])==0:
                list_var_str=None
            else:
                list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                if lhs!='' and lhs is not None:
                    return 'ForAll(['+list_var_str+'],Implies('+lhs+','+rhs+"))"
                else:
                    return 'ForAll(['+list_var_str+'],'+rhs+")"
            elif lhs!='' and lhs is not None:
                return 'Implies('+lhs+','+rhs+")"
            else:
                return rhs
        else:
            return expression







#convert wff to z3 constraint
def wff2z3_update4(w,var_dim_map,const_var_map):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            flag_constr=False
            lhs=expr2z3_update(w[-2],var_cstr_map)
            rhs=expr2z3_update(w[-1],var_cstr_map) 
            list_var_str=qualifier_list(var_cstr_map.keys())
            #print '----------------------'
            #print list_var_str
            #print '----------------------'
            if isArrayFunction(w[-2][0])==True:
            	if '_x1' in var_cstr_map.keys():
            		del var_cstr_map['_x1']
            	flag_constr=True
            if '_s1' in var_cstr_map.keys():
                del var_cstr_map['_s1']
                flag_constr=True
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            if flag_constr==True:
                if  w[-2][1][0] in var_dim_map.keys():
                    list_cstr_str_temp=None
                    list_cstr_str_temp=cstr_list_additional1(list_cstr_str_temp,var_cstr_map.keys(),var_dim_map[w[-2][1][0]].getDimensions().keys(),var_dim_map[w[-2][1][0]].getDimensions())
                    if list_cstr_str_temp is not None:
                        if list_cstr_str is None:
                            list_cstr_str = list_cstr_str_temp
                        else:
                            list_cstr_str = "And("+list_cstr_str +','+ list_cstr_str_temp+")"
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if w[-1][0] in ['==','<=','>=','>','<','!=','or','and']:
                rhs='If(('+rhs+')==0,0,1)'
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                else:
                	if flag_constr==True:
                		return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	else:
                		return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[1],var_cstr_map)
            rhs=expr2z3_update(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            lhs=w[1]+'+1'
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3_update(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            #print '----------------------'
            #print list_var_str
            #print '----------------------'
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())

                    new_w = copy.deepcopy(w)
                    for element in var_cstr_map.keys():
                    	fun=[]
                    	fun.append('_f')
                    	parameter=[]
                    	parameter.append(element)
                    	fun.append(parameter)
                    	sub=[]
                    	sub.append(element)
                    	new_w[1]=expr_replace(new_w[1],sub,fun) #expr_replace_const(new_w[1],element,fun)
		    new_expression=expr2z3_update(new_w[1],var_cstr_map)
		    new_arg_list=extract_args(new_expression)
                    
                    #old_arg_list=arg_list[1]
                    old_arg_list=new_arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'

        elif w[0]=='c1':
         	var_cstr_map={}
	      	equations=[]
	    	expression=expr2z3_update(w[1],var_cstr_map)
	    	list_var_str=qualifier_list(var_cstr_map.keys())
	    	list_cstr_str=cstr_list(var_cstr_map.values())
                #add by pritom 30/08/2017
                list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
	    	if list_var_str is not None and list_cstr_str is not None:
        		 return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
        	else:
        		 return expression
        elif w[0]=='L1':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update(w[-2],var_cstr_map)
            	rhs=expr2z3_update(w[-1],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())
            	if isArrayFunction(w[-2][0])==True:
            		if '_x1' in var_cstr_map.keys():
            			del var_cstr_map['_x1']
            		flag_constr=True
            	
            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())
                #add by pritom 30/08/2017
            	if list_cstr_str is not None:
            		constant=w[2].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[2]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str2+','+w[2]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		if w[0] == 'i1':
                		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                	else:
                		if flag_constr==True:
                			return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                		else:
                			return "Implies("+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+","+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+")"
            	else:
                	return "Implies("+lhs+' == '+ rhs+","+lhs+' == '+ rhs+")"
        elif w[0]=='L2':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update(w[2],var_cstr_map)
            	rhs=expr2z3_update(w[3],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())

            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())

            	if list_cstr_str is not None:
            		constant=w[1].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[1]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str+','+w[1]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+rhs+"))"+")"
            	else:
                	return "Implies("+lhs+","+rhs+")"
        elif w[0] == 'R':
            var_cstr_map={}
            lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'RE':
            var_cstr_map={}
            if len(w[2])==0:
                lhs=None
            else:
                lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            if len(w[1])==0:
                list_var_str=None
            else:
                list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                if lhs!='' and lhs is not None:
                    return 'ForAll(['+list_var_str+'],Implies('+lhs+','+rhs+"))"
                else:
                    return 'ForAll(['+list_var_str+'],'+rhs+")"
            elif lhs!='' and lhs is not None:
                return 'Implies('+lhs+','+rhs+")"
            else:
                return rhs
        else:
            return expression





#convert wff to z3 constraint for array tilling
def wff2z3_update5(w,var_dim_map,const_var_map):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            flag_constr=False
            lhs=expr2z3_update1(w[-2],var_cstr_map)
            rhs=expr2z3_update1(w[-1],var_cstr_map) 
            list_var_str=qualifier_list(var_cstr_map.keys())
            #print list_var_str
            if isArrayFunction(w[-2][0])==True:
            	if '_x1' in var_cstr_map.keys():
            		del var_cstr_map['_x1']
            	flag_constr=True
            if '_s1' in var_cstr_map.keys():
                del var_cstr_map['_s1']
                flag_constr=True
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            if flag_constr==True:
                if  w[-2][1][0] in var_dim_map.keys():
                    list_cstr_str_temp=None
                    list_cstr_str_temp=cstr_list_additional1(list_cstr_str_temp,var_cstr_map.keys(),var_dim_map[w[-2][1][0]].getDimensions().keys(),var_dim_map[w[-2][1][0]].getDimensions())
                    if list_cstr_str_temp is not None:
                        if list_cstr_str is None:
                            list_cstr_str = list_cstr_str_temp
                        else:
                            list_cstr_str = "And("+list_cstr_str +','+ list_cstr_str_temp+")"
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if w[-1][0] in ['==','<=','>=','>','<','!=','or','and']:
                rhs='If(('+rhs+')==0,0,1)'
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                else:
                	if flag_constr==True:
                		return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	else:
                		return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update1(w[1],var_cstr_map)
            rhs=expr2z3_update1(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update1(w[2],var_cstr_map)
            rhs=expr2z3_update1(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            lhs=w[1]+'+1'
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3_update1(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #add by pritom 30/08/2017
            list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
            #print '----------------------'
            #print list_var_str
            #print '----------------------'
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update1(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())

                    new_w = copy.deepcopy(w)
                    for element in var_cstr_map.keys():
                    	fun=[]
                    	fun.append('_f')
                    	parameter=[]
                    	parameter.append(element)
                    	fun.append(parameter)
                    	sub=[]
                    	sub.append(element)
                    	new_w[1]=expr_replace(new_w[1],sub,fun) #expr_replace_const(new_w[1],element,fun)
		    new_expression=expr2z3_update1(new_w[1],var_cstr_map)
		    new_arg_list=extract_args(new_expression)
                    
                    #old_arg_list=arg_list[1]
                    old_arg_list=new_arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'

        elif w[0]=='c1':
         	var_cstr_map={}
	      	equations=[]
	    	expression=expr2z3_update1(w[1],var_cstr_map)
	    	list_var_str=qualifier_list(var_cstr_map.keys())
	    	list_cstr_str=cstr_list(var_cstr_map.values())
                #add by pritom 30/08/2017
                list_cstr_str=cstr_list_additional(list_cstr_str,var_cstr_map.keys(),const_var_map)
	    	if list_var_str is not None and list_cstr_str is not None:
        		 return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
        	else:
        		 return expression
        elif w[0]=='L1':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update1(w[-2],var_cstr_map)
            	rhs=expr2z3_update1(w[-1],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())
            	if isArrayFunction(w[-2][0])==True:
            		if '_x1' in var_cstr_map.keys():
            			del var_cstr_map['_x1']
            		flag_constr=True
            	
            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())
                #add by pritom 30/08/2017
            	if list_cstr_str is not None:
            		constant=w[2].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[2]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str2+','+w[2]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		if w[0] == 'i1':
                		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                	else:
                		if flag_constr==True:
                			return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+lhs+' == '+ rhs+"))"+")"
                		else:
                			return "Implies("+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+","+'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"+")"
            	else:
                	return "Implies("+lhs+' == '+ rhs+","+lhs+' == '+ rhs+")"
        elif w[0]=='L2':
        	var_cstr_map={}
        	flag_constr=False
            	lhs=expr2z3_update1(w[2],var_cstr_map)
            	rhs=expr2z3_update1(w[3],var_cstr_map)           
            	list_var_str=qualifier_list(var_cstr_map.keys())

            	list_cstr_str=cstr_list(var_cstr_map.values())
            	list_cstr_str2=cstr_list(var_cstr_map.values())

            	if list_cstr_str is not None:
            		constant=w[1].replace('n','L')
            		list_cstr_str='And(And('+list_cstr_str+','+w[1]+'<'+constant+'),'+constant+'>0'+')'
            		list_cstr_str2='And(And('+list_cstr_str+','+w[1]+'<'+constant+'+1),'+constant+'>0'+')'
            	if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            		lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            	if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            		rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            	if list_var_str is not None and list_cstr_str is not None:
            		return "Implies("+"ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+"))"+","+"ForAll(["+list_var_str+"],Implies("+list_cstr_str2+","+rhs+"))"+")"
            	else:
                	return "Implies("+lhs+","+rhs+")"
        elif w[0] == 'R':
            var_cstr_map={}
            lhs=expr2z3_update1(w[2],var_cstr_map)
            rhs=expr2z3_update1(w[3],var_cstr_map)
            list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'RE':
            var_cstr_map={}
            if len(w[2])==0:
                lhs=None
            else:
                lhs=expr2z3_update1(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            if len(w[1])==0:
                list_var_str=None
            else:
                list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                if lhs!='' and lhs is not None:
                    return 'ForAll(['+list_var_str+'],Implies('+lhs+','+rhs+"))"
                else:
                    return 'ForAll(['+list_var_str+'],'+rhs+")"
            elif lhs!='' and lhs is not None:
                return 'Implies('+lhs+','+rhs+")"
            else:
                return rhs
        else:
            return expression















#convert wff to z3 constraint
def wff2z3_update_postCond(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            flag_constr=False
            lhs=expr2z3_update_postCond(w[-2],var_cstr_map)
            rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
            
            list_var_str=qualifier_list(var_cstr_map.keys())
            
            if isArrayFunction(w[-2][0])==True:
	    	del var_cstr_map['_x1']
            	flag_constr=True
            if '_s1' in var_cstr_map.keys():
                del var_cstr_map['_s1']
                flag_constr=True
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
                    
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                else:
                	if flag_constr==True:
                		return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update_postCond(w[1],var_cstr_map)
            rhs=expr2z3_update_postCond(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update_postCond(w[2],var_cstr_map)
            rhs=expr2z3_update_postCond(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=w[1]+'+1'
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3_update_postCond(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update_postCond(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())
                    old_arg_list=arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'

        elif w[0]=='c1':
         	var_cstr_map={}
	      	equations=[]
	    	expression=expr2z3_update(w[1],var_cstr_map)
	    	list_var_str=qualifier_list(var_cstr_map.keys())
	    	list_cstr_str=cstr_list(var_cstr_map.values())
	    	if list_var_str is not None and list_cstr_str is not None:
        		 return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
        	else:
        		 return expression     
        elif w[0] == 'R':
            var_cstr_map={}
            lhs=expr2z3_update_postCond(w[2],var_cstr_map)
            rhs=expr2z3_update_postCond(w[3],var_cstr_map)
            list_var_str=qualifier_list(w[1])
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'RE':
            var_cstr_map={}
            lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(w[1])
            if list_var_str is not None:
                if lhs!='' and lhs is not None:
                    return 'ForAll(['+list_var_str+'],Implies('+lhs+','+rhs+"))"
                else:
                    return 'ForAll(['+list_var_str+'],'+lhs+")"
            else:
                return lhs
        else:
            return expression






#convert wff to z3 constraint(Special Case N=0 V E(n/(N-1)))
def wff2z3SC_update(w):
	if w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression and 'Implies' not in expression:
	    	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())
                    old_arg_list=arg_list[1]
                    
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                        return 'ForAll(['+str(list_var_str_new)+'],Implies('+str(list_cstr_str_new)+','+arg_list[1]+'))'
                        #return equations
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        return arg_list[1]
                        #return equations
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
                    
                    
                    
#convert wff to z3 constraint(Special Case N=0 V E(n/(N-1)))
def wff2z3SC(w):
	if w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())
                    old_arg_list=arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                        return 'ForAll(['+str(list_var_str_new)+'],Implies('+str(list_cstr_str_new)+','+arg_list[1]+'))'
                        #return equations
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        return arg_list[1]
                        #return equations
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'



#Function Collect Condition From All Recursive  Formulas

def getAllCondtion(w,condition_map):
	if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
		var_cstr_map={}
	        lhs=expr2z3(w[-2],var_cstr_map)
	        rhs=expr2z3(w[-1],var_cstr_map)
	        if 'ite' not in str(rhs):
	        	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
	        extract_conditions(rhs,condition_map)
        

def extract_conditions(expression,condition_map):
	if 'If' in expression:
		axioms=extract_args(expression)
	        condition_map[axioms[0]]=axioms[0]
	        if 'If' in axioms[1]:
			extract_conditions(axioms[1],condition_map)
		if 'If' in axioms[2]:
			extract_conditions(axioms[2],condition_map)









#print in normal infix notation
def wff2subslist(w):
        if w[0] == 'e':
            return expr2string1(w[-2]),expr2string1(w[-1])
 


#construct constraints for qualified variables
        
def qualifier_list(list_var):
    if len(list_var)==0:
        return None;
    else:
        var=list_var[-1]
        del list_var[-1]
        list_var_str=qualifier_list(list_var)
        if list_var_str is None:
            return var
        else:
            return var+","+list_var_str


#construct map of all array functions

def array_element_list(e,array_map): #e,e1,e2: expr
	if isArrayFunction(e[:1][0])==True:
            array_map[e[:1][0]]=e[:1][0]
            for x in expr_args(e):
                array_element_list(x,array_map)
        else:
            for x in expr_args(e):
                array_element_list(x,array_map)

#construct constraints for qualified variables

def cstr_list(list_cstr):
    if len(list_cstr)==0:
        return None;
    else:
        var=list_cstr[-1]
        del list_cstr[-1]
        list_cstr_str=cstr_list(list_cstr)
        if list_cstr_str is None:
            return var
        else:
            return "And("+var+","+list_cstr_str+")"
        
        
        
#construct constraints for qualified variables

def cstr_list_additional(list_cstr_str,list_cstr,const_var_map):
    if len(list_cstr)==0:
        return list_cstr_str;
    else:
        var=list_cstr[-1]
        del list_cstr[-1]
        if list_cstr_str is None:
            list_cstr_str=cstr_list_additional(list_cstr_str,list_cstr,const_var_map)
        else:
            list_cstr_str = cstr_list_additional(list_cstr_str,list_cstr,const_var_map)
        if var in const_var_map.keys():
            if list_cstr_str is None:
                return var+"<"+const_var_map[var]
            else:
                return "And("+var+"<"+const_var_map[var]+","+list_cstr_str+")"
        else:
            return list_cstr_str;


def cstr_list_additional1(list_cstr_str,variable_list,list_cstr,const_var_map):
    if len(list_cstr)==0:
        return list_cstr_str;
    else:
        var=list_cstr[-1]
        del list_cstr[-1]
        if list_cstr_str is None:
            list_cstr_str = cstr_list_additional1(list_cstr_str,variable_list,list_cstr,const_var_map)
        else:
            result = cstr_list_additional1(list_cstr_str,variable_list,list_cstr,const_var_map)
            if result is not None:
                list_cstr_str="And("+result+","+list_cstr_str+")"
        if var in const_var_map.keys() and var in variable_list:
            if list_cstr_str is None:
                return var+"<"+const_var_map[var]
            else:
                return "And("+var+"<"+const_var_map[var]+","+list_cstr_str+")"
        else:
            return list_cstr_str;




#strip '(' at the beginning and matching ')' in the end of a string
def trim_p(s):
    if s.startswith('(') and s.endswith(')'):
        return trim_p(s[1:-1])
    else:
        return s



#for a formula w, compute w[n]
def wff_extend(w,n,excl,v): #w: wff, n: expr, excl: container of strings
    if w[0]=='e': #['e',e1,e2]
        return ['e',extend(w[1],n,excl,v),extend(w[2],n,excl,v)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],extend(w[2],n,excl,v),extend(w[3],n,excl,v)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],extend(w[3],n,excl,v),extend(w[4],n,excl,v)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',extend(w[1],n,excl,v),extend(w[2],n,excl,v)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],extend(w[2],n,excl,v),extend(w[3],n,excl,v)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': 
        return [w[0], extend(w[1],n,excl,v)]
    else:
        print('Not a wff')
        return
        

#for a formula w, replace functor old by new
def wff_sub(w,old,new): #w - wff; old, new - string
    if w[0]=='e': #['e',e1,e2]
        return ['e',expr_sub(w[1],old,new),expr_sub(w[2],old,new)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],expr_sub(w[2],old,new),expr_sub(w[3],old,new)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],expr_sub(w[3],old,new),expr_sub(w[4],old,new)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',expr_sub(w[1],old,new),expr_sub(w[2],old,new)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],expr_sub(w[2],old,new),expr_sub(w[3],old,new)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub(w[1],old,new)]
    else:
        print('Not a wff')
        return
        

#for a formula w, replace functor x+old by x+new for those in v1 but not in v2
def wff_sub_set(w,old,new,v1,v2): #w - wff; old, new - string; v1,v2: sets
    if w[0]=='e': #['e',e1,e2]
        return ['e',expr_sub_set(w[1],old,new,v1,v2),expr_sub_set(w[2],old,new,v1,v2)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],expr_sub_set(w[2],old,new,v1,v2),expr_sub_set(w[3],old,new,v1,v2)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],expr_sub_set(w[3],old,new,v1,v2),expr_sub_set(w[4],old,new,v1,v2)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',expr_sub_set(w[1],old,new,v1,v2),expr_sub_set(w[2],old,new,v1,v2)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],expr_sub_set(w[2],old,new,v1,v2),expr_sub_set(w[3],old,new,v1,v2)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub_set(w[1],old,new,v1,v2)]
    else:
        print('Not a wff')
        return

#like expr_sub_dict(e,d) but on wffs

def wff_sub_dict(w,d): #w - wff; d - a dictionary as in expr_sub_dict(e,d)
    if w[0]=='e': #['e',e1,e2]
        return w[:2]+[expr_sub_dict(w[2],d)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return w[:3]+[expr_sub_dict(w[3],d)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return w[:4]+[expr_sub_dict(w[4],d)]
    elif w[0]=='d0': #['d0',e,c]
        return w[:2]+[expr_sub_dict(w[2],d)]
    elif w[0]=='d1': #['d1',v,e,c]
        return w[:3]+[expr_sub_dict(w[3],d)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub_dict(w[1],d)]
    else:
        print('Not a wff')
        return

#parameterize a set of axioms by making program functions as input variables
#para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'],['X','Y']],...} meaning 'X' is an input variable parameterized as '_y1' and 'X11' is a function taking two new parameters '_y1','_y2'
#X11(a,X)=X11(a+b,1) will become X11(a,_y1,_y1,_y2)=X11(a+b,1,_y1,_y2)
 
def parameterize_wff(ax,para):
    if not (ax[0] == 'a' or ax[0]=='s0' or ax[0]=='s1'):
        e1 = parameterize_expres(ax[-2],para)
        e2 = parameterize_expres(ax[-1],para)
        return ax[:-2]+[e1,e2]
    else:
        e2 = parameterize_expres(ax[-1],para)
        return [ax[0],e2]
        

#for all x in dep_set, add dep_set[x] as arguments, except when x is RET+OUT,
#replace it by foo()

def parameterize_axioms_fun(axioms,dep_set):
    for x in axioms:
        parameterize_wff_fun(x,dep_set)

def parameterize_wff_fun(ax,dep_set):
    if not (ax[0] == 'a' or ax[0]=='s0' or ax[0]=='s1'):
        e1 = parameterize_expres_fun(ax[-2],dep_set)
        e2 = parameterize_expres_fun(ax[-1],dep_set)
        return ax[:-2]+[e1,e2]
    else:
        e2 = parameterize_expres_fun(ax[-1],dep_set)
        return [ax[0],e2]

def parameterize_expres_fun(e,dep_set): 
    if e[0]==RET+OUT:
        if len(e) != 1:
            print 'Something is wrong '+RET+OUT+' should not have arguments'
            return
        else:
            return dep_set[RET+OUT]
    elif e[0] in dep_set:
        return expres(e[0],list(parameterize_expres_fun(x,dep_set) for x in e[1:])+dep_set[e[0]])
    else:
        return expres(e[0],list(parameterize_expres_fun(x,dep_set) for x in e[1:]))
        
        
    

def eqset2string(d):
    for x in d:
        print wff2string(d[x])
def eqset2string1(d):
    for x in d:
        print wff2string1(d[x])
 
def eqset2stringvfact(d,var_map):
    for x in d:
        wff2stringvfact(d[x],var_map)
        
def eqset2constraintlist(d):
    equation_list=[]
    for x in d:
        equation_list.append(wff2z3(d[x]))
    return equation_list
    

def eqset2constraintlist_update(d):
    equation_list=[]
    for x in d:
        equation_list.append(wff2z3_update(d[x]))
    return equation_list    
    


def eqset2constraintlist4_update(d,var_dim_map,const_var_map):
    equation_list=[]
    for x in d:
        equation_list.append(wff2z3_update4(d[x],var_dim_map,const_var_map))
    return equation_list 
    
    
    
    
def eqset2subs_list(d):
    subs_list={}
    for x in d:
        lhs,rhs=wff2subslist(d[x])
        if 'ite' not in rhs and 'E' not in str(lhs) and 'e' not in str(lhs):
        	subs_list[simplify(lhs)]=simplify_sympy(rhs)
        elif 'E' not in str(lhs) and 'e' not in str(lhs):
                subs_list[lhs]=rhs
    return subs_list
def eqset2subs_list_ind(d):
    subs_list={}
    for x in d:
        if x[0]=='i1':
            lhs=expr2string1(x[-2])
            rhs=expr2string1(x[-1])
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            subs_list[lhs]=rhs
    return subs_list
    
"""
 A program variable has the attributes: its name, its type, 
 and its corresponding logical variable when parameterized. 
 A set of program variables is represented by a dictionary 
 with variable names as keys.
 examples: { 'X':['_y1','init','int','char'], 'I':['_y2','int'] }
 This set contains two program variables: 
 constant I of int value and function X from int*int to char
 Notice that the arity of a variable x in a set d is len(d[x])-2
 We assume no local function definitions, so the p in 'if b then p else p'
 'while b do p', 'foo(x,...,y) {b}' is a normal body of program statements.

 Program representations:
1. an assignment (l is the label, l='-1' means no label)
 l: left = right
 by [l,'=',e1,e2], 
 where e1,e2 are expressions representing left and right, respectively
2. a sequence
 p1; p2
 by ['-1','seq',p1,p2]
 where p1 and p2 are programs
3. if-then:
 l: if C then P
by [l,'if1', c,p], where c is the expression for C and p a program for P
4. if-then-else
 l: if c then p1 else p2
by [l,'if2', c,p1,p2], 
where c is Expr, p1 and p2 are Prog
5. while loop
 l: while c {b} by
[l,'while', c,b], 
where c is Expr, b is Prog
6. function definition
 foo(x,...,y) { B }
['-1','fun',['foo','x',..,'y'], b]
where 'foo' is the name of the function, 'x',...,'y' parameters, and
b the Prog representing B. We assume that B has no local function, i.e.
a normal body of statements. 
We assume a unique string 'RET' representing return
value because we do not have a special return statement.
Instead, a return statement
 l: return E
is represented as a normal assignment
 l: RET = e
We expect this will be the last statement of the body b
7. sequence of functions
 foo1(...) {B1}, ..., fook(...) {Bk}
['-1', 'prog', [f1,...,fk]]
where fi is the program representation of fooi(...) {Bi}. For this, the list
of variables v needs to be a dictionary indexed by the function names 
'foo1',...,'fook' whose value v['foo'] is the list of variables used in the function

"""



# for testing flag=1 (original translation), flag=2 (inductive definition for smallest N)
def translate1(p,v,flag):
    global TC
    global LC
    TC=0
    LC=0
    if p[1]=='prog':
        f_map={}
        a_map={}
        o_map={}
        cm_map={}
        assert_list_map={}
        assume_list_map={}
        assert_key_map={}
        res = translate0(p,v,flag)
        for fn in res:
            x,f,o,a,l = res[fn]
            #print f
	    #print o
            #print('Output for '+fn+':')
            

            
            f,o,a,cm = rec_solver(f,o,a)
            #cm=[]          
            #print f
            #print o
            #print a

            
            organizeFreeVariable(f,o,a,v)
            
            
            f,o,a,cm = getDummyFunction(f,o,a,cm)
            #f,o,a,cm = update__VERIFIER_nondet(f,o,a,cm)
            
            f,o,a,assert_list,assume_list,assert_key=getAssertAssume(f,o,a,cm)
            
            #assert_list=[]
            
            #assume_list=[]
            
            #assert_key=[]
            
            #assert_key_map={}
            
            
            f_map[fn]=f
	    o_map[fn]=o
	    a_map[fn]=a
            cm_map[fn]=cm
            
            assert_list_map[fn]=assert_list
            assume_list_map[fn]=assume_list
            assert_key_map[fn]=assert_key
            
            f,o,a=organizeOutput(f,o,a,v)
            
            
            f_map[fn]=f
	    o_map[fn]=o
	    a_map[fn]=a
            cm_map[fn]=cm
            
            output_axioms_fn(f,o,a)
            print('\n4. Assumption :')
            for x in assume_list:
            	if x[0]=='i1':
	     		print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
	    	else:
	     		if x[0]!='i0':
                    		print wff2string1(x)
            print('\n5. Assertion :')
            for x in assert_list:
                if x[0]=='i1':
                    print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
                else:
                	if x[0]!='i0':
                    		print wff2string1(x)
        return f_map,o_map,a_map,cm_map,assert_list_map,assume_list_map,assert_key_map
        
    elif p[1]=='fun':
        fn,f,o,a,l = translate0(p,v,flag)
        print('Output for ')
        print(fn)
        f,o,a,cm = rec_solver(f,o,a)
        f,o,a,cm = getDummyFunction(f,o,a,cm)
        f,o,a,assert_list,assume_list,assert_key=getAssertAssume(f,o,a,cm)
        f,o,a=organizeOutput(f,o,a,v)
        output_axioms_fn(f,o,a)
    	print('\n4. Assumption :')
	for x in assume_list:
        	if x[0]=='i1':
			print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
		else:
			if x[0]!='i0':
                    		print wff2string1(x)
    	print('\n5. Assertion :')
	for x in assert_list:
                if x[0]=='i1':
                    print 'ForAll '+x[2]+' ( '+ expr2string1(x[4]) +' ) '
                else:
                	if x[0]!='i0':
                    		print wff2string1(x)
        return f,o,a,cm,assert_list,assume_list,assert_key
    else:
        f,o,a,l = translate0(p,v,flag)
        #Add by Pritom Rajkhowa 10 June 2016
    	f,o,a,cm = rec_solver(f,o,a)
    	f,o,a,cm = getDummyFunction(f,o,a,cm)
    	f,o,a,assert_list,assume_list,assert_key=getAssertAssume(f,o,a,cm)
        f,o,a=organizeOutput(f,o,a,v)
    	output_axioms_fn(f,o,a)
    	print('\n4. Assumption :')
	for x in assume_list:
	         if x[0]=='i1':
	         	print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
	         else:
	                if x[0]!='i0':
                    		print wff2string1(x)
    	print('\n5. Assertion :')
	for x in assert_list:
                if x[0]=='i1':
                    print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
                else:
                	if x[0]!='i0':
                    		print wff2string1(x)
    
    	return f,o,a,cm,assert_list,assume_list,assert_key




def output_axioms_fn(f,o,a):
    #print('Output in prefix notation:')
    #print('1. Frame axioms:')
    #eqset2string(f)
    #print('\n2. Output equations:')
    #eqset2string(o)
    #print('\n3. Other axioms:')
    #for x in a: 
    #    print wff2string(x)
    print('\nOutput in normal notation:')
    print('1. Frame axioms:')
    eqset2string1(f)
    print('\n2. Output equations:')
    eqset2string1(o)
    print('\n3. Other axioms:')
    for x in a: 
        print wff2string1(x)


def organizeOutput(f,o,a,vfacts):
    array_list=[]
    new_f={}
    duplicate_map={}
    new_f={}
    new_o={}
    new_a=[]
    for vfact in vfacts.keys():
        info_list=vfacts[vfact]
        if type(info_list) is dict:
            for info in info_list:
                element_list=info_list[info]
                if type(element_list) is list:
                    if element_list[1]=='array' and '_PROVE' not in info and '_ASSUME' not in info and len(element_list)==2:
                        array_list.append(info)
        else:
            if info_list[1]=='array' and '_PROVE' not in vfact and '_ASSUME' not in vfact and len(element_list)==2:
                array_list.append(vfact)
    

    for e in f:
        if isArrayFunction(e)==True:
            if len(array_list)>0:
                new_f[e]=f[e]
        else:
            new_f[e]=f[e]
    for e in o:
        if isArrayFunction(e)==True:
            if len(array_list)>0:
                new_o[e]=o[e]
        else:
            new_o[e]=o[e]
    for e in a:
        if e[0]=='i1':
            if isArrayFunction(e[3][0])==True:
                if len(array_list)>0:
                    new_a.append(e)
            else:
                new_a.append(e)
        elif e[0]=='i0':
            if isArrayFunction(e[2][0])==True:
                if len(array_list)>0:
                    new_a.append(e)
            else:
                new_a.append(e)
        else:
            new_a.append(e)
    
    return new_f,new_o,new_a


def organizeFreeVariable(f,o,a,vfacts):
    struct_type_list=[]
    for vfact in vfacts.keys():
        info_list=vfacts[vfact]
        for info in info_list:
            if info_list[info][1] not in ['int','short','unsigned','long','char','float','double','array']:
                struct_type_list.append(info)
    
    for x in o:
        e=o[x]
        if  e[0]=='e':
            if is_Stuct(e[-2][0],struct_type_list):
                e[-1] = expr_replace(e[-1],eval("['_x1']"),eval("['_s1']"))
                e[-2] = expr_replace(e[-2],eval("['_x1']"),eval("['_s1']"))
    
    for e in a:
        if e[0]=='i1' or e[0]=='i0':
            if is_Stuct(e[-2][0],struct_type_list):
                e[-1] = expr_replace(e[-1],eval("['_x1']"),eval("['_s1']"))
                e[-2] = expr_replace(e[-2],eval("['_x1']"),eval("['_s1']"))

            



def is_Stuct(var,struct_type_list):
    status=False
    for x in struct_type_list:
        temp=var.replace(x,'').strip()
        if is_number(temp)==True:
            status=True
    return status
        
        



# translate0(program,set of program variables) returns a dictionary of frame axioms, output equations, a list of other axioms and a label

def translate0(p,v,flag):
    if p[1]=='while':
        return translateWhile(p,v,flag)
    if p[1]=='seq':
        return translateSeq(p,v,flag)
    if p[1]=='if1':
        return translateIf1(p,v,flag)
    if p[1]=='if2':
        return translateIf2(p,v,flag)
    if p[1]=='=':
        return translateAssign(p,v,flag)
    if p[1]=='fun':
        return translateFun(p,v,flag)
    if p[1]=='prog':
        return translateProgram(p,v,flag)
     
     
# function definition
def translateFun(p,v,flag): #p=['-1','fun',['foo','x',..,'y'], b]
    #global TC
    #global LC
    #TC=0
    #LC=0
    f,o,a,l = translate0(p[-1],v,flag)
    axioms=a
    for x in f:
        axioms=axioms+[f[x]]
    for x in o:
        axioms=axioms+[o[x]]
    g = graph(axioms,v) #construct dependency graph
    param = list(expres(a) for a in p[-2][1:]) #parameters of the function
    dep_set = {} #dependency set for each variables in the axiom
    dep_set[RET+OUT]=expres(p[-2][0],param) #initialize it to the return function
    for (x,y) in g:
        if (not x in dep_set) and (not expres(x) in param):
            dep = []
            for x1 in reach_set([x],g):
                if (expres(x1) in param) and not (expres(x1) in dep):
                    dep.append(expres(x1))
            dep_set[x] = dep
    
    
    for x in f:
        f[x]=parameterize_wff_fun(f[x],dep_set)
    for x in o:
        o[x]=parameterize_wff_fun(o[x],dep_set)
    for i,ax in enumerate(a):
        a[i]=parameterize_wff_fun(ax,dep_set)
    return [dep_set[RET+OUT],f,o,a,l]
    
      
    
    
# program: a set of functions   
#p=['-1','prog',[f1,...,fk]] 
#for each fi, v[fi] is the list of variables used in the function fi
def translateProgram(p,v,flag): 
    result = {}
    for x in p[-1]:
        funcName = x[2][0]
        result[funcName] = translate0(x,v[funcName],flag)
    return result


# assignment translation: p a program and v a set of program variables

map___VERIFIER_nondet={}

def translateAssign(p,v,flag): #p=[l,'=',left,right]
    global map___VERIFIER_nondet
    if p[1] != '=':
        print('Not an assignment')
        return
    left = p[2] #left side of the assigment
    op = left[0] #the functor in left
    arity = len(left)-1 #arity of op
    right = p[3] #right side of the assignment
    right = update__VERIFIER_nondet_stmt(right,map___VERIFIER_nondet)
    out=OUT if p[0] == '-1' else LABEL+p[0]
    out_axioms = {}
    frame_axioms = {}
    for x in v:
        if x == op:
            args = list(expres('_x'+str(i+1)) for i in range(arity))
            cond = expres('=',[expres('_x1'),left[1]]) if arity==1 else \
                   expres('and', list(expres('=', [expres('_x'+str(i2+1)),y]) for \
                                    i2,y in zip(range(arity),left[1:])))
            if arity == 0:
                out_axioms[x]=wff_e(expres(op+out),right)
            else:
                out_axioms[x]=wff_e(expres(op+out,args), expres('ite',[cond,right,expres(op,args)]))
        else:
            args = list(expres('_x'+str(i+1)) for i in range(len(v[x])-2))
            frame_axioms[x]=wff_e(expres(x+out,args), expres(x,args))
    return frame_axioms, out_axioms, [], p[0]
    
    
    

def translateIf1(p,v,flag): # p=[l,'if1',c,e]
    global map___VERIFIER_nondet
    if p[1] != 'if1':
        print('Not an if-then')
        return
    global TC
    frame_axioms,out_axioms,axioms,llabel = translate0(p[3],v,flag)
    old_out = OUT if llabel=='-1' else LABEL+llabel
    out=OUT if p[0] == '-1' else LABEL+p[0]
    if llabel=='-1': # body has no final label
        TC += 1
    body_out = TEMP+str(TC) if llabel=='-1' else LABEL+llabel
    
    p[2] = update__VERIFIER_nondet_stmt(p[2],map___VERIFIER_nondet)
    
    for x in v:
        if x in frame_axioms: 
            ax = frame_axioms[x] #ax = ['e',e1,e2]
            if llabel != '-1': #body has label: keep axioms about it
                axioms.append(ax)
            #generate the new frame axiom
            frame_axioms[x] = wff_e(expr_sub(ax[1],x+old_out,x+out), ax[2])
        else:
            ax = out_axioms[x] #ax = ['e',e1,e2]
            if llabel != '-1': #body has label: keep axioms about it
                axioms.append(ax)
            out_axioms[x] = wff_e(expres(x+out, ax[1][1:]),
                                  expres('ite', [p[2], ax[2], expres(x,ax[1][1:])]))
    return frame_axioms, out_axioms, axioms, p[0]
    
            
def translateIf2(p,v,flag): # p=[l,'if2',c,e1,e2]
    global map___VERIFIER_nondet
    if p[1] != 'if2':
        print('Not an if-then-else')
        return
    global TC
    frame_axioms0,out_axioms0,axioms0,llabel0 = translate0(p[3],v,flag)
    frame_axioms1,out_axioms1,axioms1,llabel1 = translate0(p[4],v,flag)
    axioms = axioms0+axioms1
    old_out0 = OUT if llabel0=='-1' else LABEL+llabel0
    old_out1 = OUT if llabel1=='-1' else LABEL+llabel1
    out=OUT if p[0] == '-1' else LABEL+p[0]
    if llabel0=='-1': # if body has no final label
        TC += 1
    body_out0 = TEMP+str(TC) if llabel0=='-1' else LABEL+llabel0 # if body new out
    if llabel1=='-1': # else body has no final label
        TC += 1
    body_out1 = TEMP+str(TC) if llabel1=='-1' else LABEL+llabel1 # else body new out
    frame_axioms = {}
    out_axioms = {}
    
    p[2] = update__VERIFIER_nondet_stmt(p[2],map___VERIFIER_nondet)
    
    for x in v:
        if x in frame_axioms0 and x in frame_axioms1: 
            ax0 = frame_axioms0[x] #ax0 = ['e',e1,e2]
            ax1 = frame_axioms1[x] #ax1 = ['e',e1,e2]
            if llabel0 != '-1': #if body has label: keep axioms about it
                axioms.append(ax0)
            if llabel1 != '-1': #else body has label: keep axioms about it
                axioms.append(ax1)
            #generate the new frame axiom
            frame_axioms[x] = wff_e(expr_sub(ax0[1],x+old_out0,x+out), ax0[2])
        else:
            if x in frame_axioms0:
                ax0=frame_axioms0[x]
            else:
                ax0=out_axioms0[x]
            if x in frame_axioms1:
                ax1=frame_axioms1[x]
            else:
                ax1=out_axioms1[x]
            if llabel0 != '-1': #if body has label: keep axioms about it
                axioms.append(ax0)
            if llabel1 != '-1': #else body has label: keep axioms about it
                axioms.append(ax1)
            out_axioms[x] = wff_e(expres(x+out, ax0[1][1:]),
                                  expres('ite', [p[2], ax0[2], ax1[2]]))
    return frame_axioms, out_axioms, axioms, p[0]
    
            
def translateSeq(p,v,flag): # p=['-1','seq',p1,p2]
    if p[1] != 'seq':
        print('Not a sequence')
        return
    global TC
    frame_axioms0,out_axioms0,axioms0,llabel0 = translate0(p[2],v,flag)
    frame_axioms1,out_axioms1,axioms1,llabel1 = translate0(p[3],v,flag)
    old_out0 = OUT if llabel0=='-1' else LABEL+llabel0
    if llabel0=='-1': # if p1 has no final label
        TC += 1
    new_out0 = TEMP+str(TC) if llabel0=='-1' else LABEL+llabel0 # p1 new out
    frame_axioms = {}
    out_axioms = {}
    para = {} #a dictonary of substitution: para[x] is the expression to replace x(t) in p2's axioms
    for x in v:
        if x in frame_axioms0 and x in frame_axioms1:
            if llabel0 !='-1': #p1 has label, keep its axioms
                axioms0.append(frame_axioms0[x])
            frame_axioms[x]=frame_axioms1[x]
        else:
            if x in frame_axioms0:
                ax0=frame_axioms0[x] #ax0=['e',e1,e2]
            else:
                ax0=out_axioms0[x]
            if llabel0 != '-1': #p1 has label: keep equations about it
                axioms0.append(ax0)
            para[x]=ax0[2]
    for i,ax in enumerate(axioms1): #substituting p1's output into p2's input in p2's axioms
        axioms1[i] = wff_sub_dict(ax,para)
    for x in v: #do the same for the p2's output equations and frame axioms
        if not x in frame_axioms:
            if x in frame_axioms1:
                out_axioms[x] = frame_axioms1[x][:2]+[expr_sub_dict(frame_axioms1[x][2],para)]
            else:
                out_axioms[x] = out_axioms1[x][:2]+[expr_sub_dict(out_axioms1[x][2],para)]
    
    return frame_axioms, out_axioms, axioms0+axioms1, llabel1
    


def translateWhile(p,v,flag): #p=[l, 'while', c, b]
    global map___VERIFIER_nondet
    if p[1] != 'while':
        print('Not a while statement')
        return
    global LC
    global TC
    frame_axioms, out_axioms0, axioms,llabel = translate0(p[3],v,flag) # axioms and output labels for the body of the loop
    LC += 1
    if llabel=='-1': # if body has no final label
        if TC==0:
            TC += 2
        else:
            TC += 1
        
    loop_var = expres('_n'+str(LC)) #a new natural number variable for the loop
    smallest = expres('_N'+str(LC)) #a new natural number variable for the loop
    init=TEMP+str(TC) if llabel=='-1' else LABEL+llabel #iterating functions
    old_out=OUT if llabel=='-1' else LABEL+llabel #original output functions in body
    out=OUT if p[0]=='-1' else LABEL+p[0] #new output functions for the loop

    for i0, ax0 in enumerate(axioms): #extend the axioms with [n]
        ax0 = wff_sub_set(ax0,'',init,v,frame_axioms)
        axioms[i0]=wff_extend(ax0, loop_var, frame_axioms,v)

    for x in frame_axioms:
        ax = frame_axioms[x] #ax = ['e',e1,e2]
        if llabel != '-1': #body has label: keep axioms about it
            axioms.append(ax)
        #generate the new frame axiom
        frame_axioms[x] = wff_e(expr_sub(ax[1],x+old_out,x+out), ax[2])
    out_axioms00={}
    for x in out_axioms0: 
        ax = out_axioms0[x] #ax = ['e',e1,e2]
        #change output and input variable names to loop and extend e2[loop_var]
        ax = wff_sub_set(ax,old_out,init,v,frame_axioms)
        ax = wff_sub_set(ax,'',init,v,frame_axioms)
        out_axioms00[x]=ax[:2]+[extend(ax[2],loop_var,frame_axioms,v)]

    # using Pritom's solve_rec() to try to get closed-form solution
    found_solution=True
    variable=None
    while found_solution:
        found1=False
        for x in out_axioms00.keys():
            ax=out_axioms00[x]
            if expr_func(ax[2],v)==[]:
                found1=True
                e=extend(ax[1],loop_var,frame_axioms,v)
                axioms.append(wff_e(e,ax[2]))
                del out_axioms00[x]
                for y in out_axioms00:
                    ax1= out_axioms00[y]
                    out_axioms00[y]=ax1[:2]+[expr_sub_dict(ax1[2],{expr_op(ax[1]):ax[2]})]
            else:
                e1=wff_i1(0,expr_op(loop_var),extend(ax[1],expres('+',[loop_var,['1']]),frame_axioms,v),ax[2])
                e2=wff_i0(0,extend(ax[1],expres('0'),frame_axioms,v),expres(x,expr_args(ax[1])))
                res=solve_rec(e1,e2)
                if res != None: #res = ['i2',k,n,e1,e2]
                    found1=True
                    variable=res[2] # Variable add by Pritom Rajkhowa
                    axioms.append(wff_e(res[3],res[4]))
                    del out_axioms00[x]
                    for y in out_axioms00:
                        ax1= out_axioms00[y]
                        out_axioms00[y]=ax1[:2]+[expr_sub_dict(ax1[2],{expr_op(res[3]):res[4]})]
        if not found1:
            found_solution=False
    for x in out_axioms00:
        ax = out_axioms00[x] #ax = ['e',e1,e2]
        e1=extend(ax[1],expres('+',[loop_var,['1']]),frame_axioms,v)
        e2=ax[2]
        axioms.append(wff_i1(len(expr_args(e1))-1,expr_op(loop_var),e1,e2))
    
    #base case
    for x in out_axioms00:
        arity = len(v[x])-2
        args = list(expres('_x'+str(i+1)) for i in range(arity))
        axioms.append(wff_i0(arity,expres(x+init,args+[expres('0')]), expres(x,args)))
    c=p[2] #loop condition
    c = update__VERIFIER_nondet_stmt(c,map___VERIFIER_nondet)
    c=expr_sub_set(c,'',init,v,frame_axioms)
    c = extend(c,loop_var,frame_axioms,v) #add the smallest macro
     #Add by pritom
    cc = copy.deepcopy(c)
    axioms.append(wff_s0(expr_sub(expr_complement(cc),expr_op(loop_var),expr_op(smallest))))  
    #axioms.append(wff_s0(expres('not',[expr_sub(c,expr_op(loop_var),expr_op(smallest))])))
    axioms.append(wff_s1(expres('implies',
                             [expres('<', [loop_var, smallest]),c])))
    out_axioms = {}
    for x in v: # generate out_axioms
        if not x in frame_axioms:
            args = list(expres('_x'+str(i+1)) for i in range(len(v[x])-2))
            e1=expres(x+out,args)
            args.append(smallest)
            e2=expres(x+init,args)
            out_axioms[x]=wff_e(e1,e2)
    #substitution of closed form solution by pritom rajkhowa
    constant='_N'+str(LC)
    variable='_n'+str(LC)
    update_axioms=[]
    equations=[]

    for ax in axioms:
    	if ax[0]=='e':
    		equations.append(ax)
    	else:
    		update_axioms.append(ax)
    
    for equation in equations:
    	equation1=copy.deepcopy(equation)
    	update_axioms=solnsubstitution(update_axioms,equation[1],equation[2])
    	equation1[1]=expr_replace_const(equation1[1],variable,constant)
    	equation1[2]=expr_replace_const(equation1[2],variable,constant)
    	update_axioms=solnsubstitution(update_axioms,equation1[1],equation1[2])
    	for x in out_axioms:
		stmt=out_axioms[x]
    		stmt[2]=expr_replace(stmt[2],equation1[1],equation1[2])
    axioms=update_axioms
    updated_axioms=[]
    for ax in axioms:
    	if ax[0]=='s0':
        	expression=expr2string1(ax[1])
        	if '->' not in expression and constant in expression:
        		if '>=' in expression and 'and' not in expression and 'or' not in expression:
                                if '**' not in expression:
                                    expression=normal_form_constant(expression, constant) 
                                    #pp = getParser()
                                    #tree = pp.parse_expression(str(expression))
                                    if '**' not in str(expression):
                                        parser = c_parser.CParser()
                                        ast = parser.parse("void test(){"+str(expression)+";}")
                                        statement_temp=ast.ext[0].body.block_items[0]
                                        axupdate = construct_expression_normalC(eval(expressionCreator_C(statement_temp)))
                                        #axupdate=construct_expression_normal(tree)
                                        if axupdate is not None:
                                                updated_axioms.append(axupdate)
                                        else:
                                                updated_axioms.append(ax)
                                    else:
                                        updated_axioms.append(ax)
                                else:
                                    updated_axioms.append(ax)
        		elif '<=' in expression and 'and' not in expression and 'or' not in expression:
    				if '**' not in expression:
                                    expression=normal_form_constant(expression, constant)
                                    #pp = getParser()
                                    if '**' not in str(expression):
                                        parser = c_parser.CParser()
                                        ast = parser.parse("void test(){"+str(expression)+";}")
                                        statement_temp=ast.ext[0].body.block_items[0]
                                        #tree = pp.parse_expression(str(expression))		 
                                        #axupdate=construct_expression_normal(tree)
                                        axupdate = construct_expression_normalC(eval(expressionCreator_C(statement_temp)))
                                        if axupdate is not None:
                                                updated_axioms.append(axupdate)
                                        else:
                                                updated_axioms.append(ax)
                                    else:
                                        updated_axioms.append(ax)
                                else:
                                    updated_axioms.append(ax)
    			else:
    				updated_axioms.append(ax)
    		else:
    			updated_axioms.append(ax)
    		
    	else:
     		updated_axioms.append(ax)
    axioms=[]
    for ax in updated_axioms:
    	axioms.append(ax)

    #substitution of closed form solution by pritom rajkhowa  
    if flag==2:
        g = graph(axioms,v) #construct dependency graph
        for x in expr_func(p[2],v):
            if not ['_N'+str(LC), x] in g:
                g.append(['_N'+str(LC), x])
                g.append(['_N'+str(LC), x+init])
        for x in out_axioms00:
            if not [x+init,x] in g:
                g.append([x+init,x])
            if not [x,x+init] in g:
                g.append([x,x+init])
            for y in expr_func(out_axioms00[x][2],v):
                if not [x,y] in g:
                    g.append([x,y])
        #build a dictionary para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'],['X','Y'],...} 
        #meaning 'X' is an input variable parameterized as '_y1' and 
        #'X11' is a function taking two new parameters '_y1' and '_y2' which correspond 
        # to 'X' and 'Y', respectively
        para={} 
        for [x,x1] in g: #compute the dependency sets
            if x in v and not x in frame_axioms:
                para[x] = [1,[v[x][0]]]
            else:
                if not x in para and not x in frame_axioms:
                    t=[]
                    t1=[]
                    for y in reach_set([x],g):
                        if y in v and (not expres(y) in t1) and (not y in frame_axioms):
                            t.append(expres(v[y][0]))
                            t1.append(expres(y))
                    if t != []:
                        para[x] = [0,t,t1]
        #parameterize input variables that N depends on and all associated functions
        for i,ax in enumerate(axioms):
            axioms[i] = parameterize_wff(ax,para)
        #construct inductive definition for N
        s_args = para['_N'+str(LC)][1]
        smallest1=expres('_N'+str(LC), s_args)
        next_args=[]
        for i,y in enumerate(s_args):
            x=expr_op(para['_N'+str(LC)][2][i])
            next_args.append(parameterize_expres(out_axioms0[x][2],para))
        axioms.append(['d0',smallest1, parameterize_expres(expres('not',[p[2]]),para)])
        axioms.append(['d1','_n'+str(LC), smallest1, 
                       expres('=',[loop_var,expres('_N'+str(LC),next_args)])])
        #parameterize output axioms
        for x in out_axioms:
            out_axioms[x]=out_axioms[x][:2]+[parameterize_expr_sub(out_axioms[x][2],para)]
        new_axioms = [] #for creating new inductive definitions
        for ax in axioms:
            if ax[0]=='i1':
                x=expr_op(ax[3])
                if x.endswith(init) and x[:len(x)-len(init)] in v:
                    next_args=[]
                    for k,arg in enumerate(expr_args(ax[3])):
                        if k==ax[1]:
                            next_args.append(expres(ax[2]))
                        else:
                            a=expr_op(arg)
                            if a.startswith('_y'):
                                for b in v:
                                    if v[b][0]==a:
                                        next_args.append(parameterize_expres(out_axioms0[b][2],para))
                            else:
                                next_args.append(arg)
                    new_axioms.append(ax[0:4]+[expres(x,next_args)])
        axioms=axioms+new_axioms

    return frame_axioms, out_axioms, axioms, p[0]






#construct a graph of dependency relation in a set of equations axioms 
def graph(axioms,v):
    ret = []
    for ax in axioms:
        if ax[0]=='e' or ax[0]=='i0' or ax[0]=='i1' or ax[0]=='d0' or ax[0]=='d1':
            op=expr_op(ax[-2])
            for x in expr_func(ax[-1],v):
                if not [op,x] in ret:
                    ret.append([op,x])
        elif ax[0]=='s1':
            op=expr_op(expr_args(expr_args(ax[1])[0])[1])
            for x in expr_func(expr_args(ax[1])[1],v):
                if not [op,x] in ret:
                    ret.append([op,x])
    return ret

#given a list s of nodes, return the list of nodes that are reachable from the nodes in s
def reach_set(s,g):
    s1=[]
    for [n1,n2] in g:
        if (n1 in s) and not (n2 in s):
            s1.append(n2)
    if s1==[]:
        return s
    else:
        return reach_set(s+s1,g)

                            
# testing examples. 
x=expres('x')
y=expres('y')
ex1 = ['-1','=',x, expres('+',[y,['1']])] #x=y+1
ex2 = ['-1','=',y, ['+',y,['1']]] #y=y+1
ex21 = ['1','=',y, ['+',y,['1']]] #1: y=y+1
ex22 = ['-1','if1',['>', y,['1']],ex2] # if y>1 then y=y+1
ex23 = ['-1','if1',['>', y,['1']],ex21] # if y>1 then l: y=y+1
ex24 = ['-1','if2',['>', y,['1']],ex21,ex1] # if y>1 then l: y=y+1 else x=y+1
ex3 = ['-1','seq',ex1,ex2]  #x=y+1; y=y+1
v1 = {'x':['_y1','int'], 'y':['_y2','int']}
ex4 = ['-1', '=', ['t',x], ['+', ['+', ['z', x, ['t', x]], ['1']], x]]
ex42 = ['-1', '=', ['z',x,y], ['+', ['+', ['z', x, ['t', x]], ['1']], x]]
v2 = {'x':['_y1','int'], 'y':['_y2','int'], 't':['_y3','int','int'], 'z':['_y4','int','int','int']}
ex41 = ['-1','if1',['>', y,['1']],ex4] # if y>1 then ex4

ex25 = ['-1','if2',['>', y,['1']],ex1,ex4] 

ex5 = ['-1','if2',expres('and', [expres('=', [expres('x'),expres('t',[expres('1')])]), expres('<', [expres('y'), expres('z',[expres('x'),expres('y')])])]), ex1, ex4]

ex6 = ['-1','while',expres('<',[expres('x'),expres('y')]),ex4]

#translate1(ex3,v1,1)
#translate1(ex4,v2,1)
#translate1(ex5,v2,1)

# factorial function
"""
i=1;
F=1;
while(i <= X) {
 F=F*i;
 i=i+1;
}
"""
i=expres('i')
F=expres('F')
X=expres('X')
fact0 = ['-1','seq',['-1','=',i,['1']],['-1','=',F,['1']]]
fact1 = ['-1','seq',['-1','=',F,['*',F,i]],['-1','=',i,['+',i,['1']]]]
fact2 = ['-1','while', ['<=',i,X], fact1]
fact = ['-1','seq',fact0,fact2]
vfact = {'i':['_y1','int'], 'X':['_y2','int'], 'F':['_y3','int'],RET:['_y0','int']}
#translate1(fact,vfact)

#factorial as a function: return F
fact3 = ['-1','=',expres(RET),F]
funfact = ['-1','fun',['factorial', 'X'],['-1','seq',fact,fact3]]
#a main() that uses factorial
# main1() { X=factorial(2) }
main1 = ['-1','fun',['main1'],['-1','=',X,expres('factorial',[expres('2')])]]
# variable list for main1()
man1v = {'X':['_y1','int']}
# variable lists for main1p, one for each function
main1pv = {'main1':man1v,'factorial':vfact}
main1p = ['-1','prog',[funfact,main1]]
# translate1(main1p, main1pv,1)

# in-place list reversing - see Lin and Yang 2015
"""
J = null;
while I != null do {
    K = next(I);
    next(I) = J;
    J=I;
    I=K;
}
I=J;
"""

lr6 = ['-1','=',['I'],['K']]
lr5 = ['-1','seq',['-1','=',['J'],['I']], lr6]
lr4 = ['-1','seq',['-1','=', ['next', ['I']],['J']], lr5]
lr3 = ['-1','seq',['-1','=',['K'],['next',['I']]], lr4]
lr2 = ['-1','while',['!=', ['I'], ['null']], lr3]
lr1 = ['-1','seq',lr2,['-1','=',['I'],['J']]]
lr = ['-1','seq',['-1','=',['J'],['null']], lr1]
vlr = {'J':['_y1','list'],'I':['_y2','list'],'K':['_y3','list'],'next':['_y4','list','list']}

#Cohen's division algorithm
"""
//XandYaretwoinputintegers;Y>0 
Q=0; // quotient
R=X; // remainder
while (R >= Y) do {
    A=1; // A and B are some that at any time for
    B=Y; // some n, A=2^n and B=2^n*Y
    while (R >= 2*B) do {
       A = 2*A;
       B = 2*B; }
    R = R-B;
    Q = Q+A }
//
return Q = X/Y;
"""

A=expres('A')
B=expres('B')
R=expres('R')
Q=expres('Q')
Y=expres('Y')
A2=expres('*',[expres('2'),A]) #2*A
B2=expres('*',[expres('2'),B]) #2*B
RB=expres('-',[R,B]) #R-B
QA=expres('+',[Q,A]) #Q+A
c1=expres('>=',[R,B2]) #R>=2*B
c2=expres('>=',[R,Y]) #R >= Y

cohen9=['-1','seq',['-1','=',A,A2],['-1','=',B,B2]]
cohen8=['-1','seq',['-1','=',R,RB],['-1','=',Q,QA]]
cohen7=['-1','while',c1, cohen9]
cohen6=['-1','seq',cohen7,cohen8]
cohen1=['-1','=',Q,['0']]
cohen5=['-1','seq',['-1','=',B,Y],cohen6]
cohen4=['-1','seq',['-1','=',A,['1']],cohen5]
cohen3=['-1','while',c2, cohen4]
cohen2=['-1','seq',['-1','=',R,X],cohen3]
cohen = ['-1', 'seq', cohen1,cohen2]
vcohen={'X':['_y1','int'],'Y':['_y2','int'],'Q':['_y3','int'],'R':['_y4','int'],'A':['_y5','int'],'B':['_y6','int']}

#product of two integers
"""
Z = 0;
while( Y!=0 ) {
 if ( Y % 2 ==1 ) {
     Z = Z+X;
     Y =(Y-1);
  }
  X = 2*X;
  Y = Y/2;
}
"""
Z=expres('Z')
prod1=['-1','seq',['-1','=',Z,expres('+',[Z,X])],['-1','=',Y,expres('-',[Y,['1']])]]
prod2=['-1','seq',['-1','=',X,expres('*',[['2'],X])],['-1','=',Y,expres('/',[Y,['2']])]]
prod3=['-1', 'if1', expres('=',[expres('%',[Y,['2']]), ['1']]), prod1]
prod4=['-1','seq',prod3,prod2]
prod5=['-1','while',expres('!=',[Y,['0']]),prod4]
prod = ['-1','seq',['-1','=',Z,['0']],prod5]
vprod = {'X':['_y1','int'],'Y':['_y2','int'],'Z':['_y3','int']}

#array sum array represented as a reference, and element represented by at predicate
"""
i=0;
sum=0;
while (i<size(A)) {
 sum=at(A,i)+sum
 i=i+1
}
"""
sum3=['-1','while',expres('<',[i,expres('size',[A])]),['-1','seq',['-1','=',['sum'],expres('+',[expres('at',[A,i]),['sum']])],['-1','=',i,expres('+',[i,['1']])]]]
sum2=['-1','seq',['-1','=',['sum'],['0']],sum3]
sum1=['-1','seq',['-1','=',i,['0']],sum2]
vsum = {'i':['_y1','int'],'sum':['_y2','int'],'size':['_y3','array','int'],'A':['_y4','array'],'at':['_y5','array','int','int']}

#Dijkstra's LCM algorithm
"""
X=A;  Y=B;  U=B;  V=A;
while (X!=Y) { 
  if (X>Y) {X=X-Y; V=V+U;} 
      else {Y=Y-X; U=U+V;}
}
"""

A=expres('A')
B=expres('B')
X=expres('X')
V=expres('V')
U=expres('U')
XY=expres('-',[X,Y])
YX=expres('-',[Y,X])
UV=expres('+',[U,V])
lcm1=['-1','seq',['-1','=',X,A],['-1','=',Y,B]]
lcm2=['-1','seq',lcm1,['-1','=',U,B]]
lcm3=['-1','seq',lcm2,['-1','=',V,A]]
lcm4=['-1','seq',['-1','=',X,XY],['-1','=',V,UV]]
lcm5=['-1','seq',['-1','=',Y,YX],['-1','=',U,UV]]
c1=expres('>',[X,Y])
lcm6=['-1', 'if2', c1, lcm4,lcm5]
c2=expres('!=',[X,Y])
lcm7=['-1','while',c2,lcm6]
lcm = ['-1','seq',lcm3,lcm7]
vlcm={'A':['_y1','int'],'B':['_y2','int'],'X':['_y3','int'],'Y':['_y4','int'],'U':['_y5','int'],'V':['_y6','int']}

"""
matrix multiplication from verifythis-2016 competition

int[][] matrixMultiply(int[][] A, int[][] B) {
	int n = A.length;

	// initialise C
	int[][] C = new int[n][n];

	for (int i = 0; i < n; i++) {
   		for (int k = 0; k < n; k++) {
       			for (int j = 0; j < n; j++) {
           			C[i][j] += A[i][k] * B[k][j];
       			}
   		}
	}
	return C;
 }
"""
def less(x,y):
    return expres('<',[x,y])
def passign(l,le,ri):
    return [l,'=',le,ri]
def initialize_array2(x,i,j,m,n):
    a=passign('-1',expres('d2array',[x,i,j]),expres('0')) #d2array(x,i,j)=0
    a1=passign('-1',i,expres('+',[i,expres('1')])) #i++
    a2=passign('-1',j,expres('+',[j,expres('1')])) #j++
    while1 = ['-1','while', less(j,n), ['-1','seq',a,a2]]
    body1 = ['-1','seq',while1,a1]
    body2 = ['-1','seq',passign('-1',j,expres('0')),body1]
    while2 = ['-1','while', less(i,m), body2]
    return ['-1','seq',passign('-1',i,expres('0')),while2]

mM1 = ['-1','seq',passign('-1',expres('n'),expres('length',[expres('a')])),
       initialize_array2(expres('c'),expres('i'),expres('j'),expres('n'),expres('n'))]
mM = ['-1','seq',mM1,passign('-1',expres(RET),expres('c'))]
# for now matrixMuliply only initializes C
matrixMultipy = ['-1','fun', ['matrixMultiply','a','b'],mM]
mMv = {'a':['_y1','array'],'b':['_y2','array'],'c':['_y3','array'],RET:['_y0','array'],'i':['_y4','int'],'j':['_y5','int'],'k':['_y6','int'],'n':['_y7','int'],'d2array':['_y7','array','int','int','int']}

# translate1(matrixMultipy,mMv,1)

"""

#Add by Pritom 

"""


#Function Get list of parameters 

def find_between( s, first, last ):
    try:
        start = s.index( first ) + len( first )
        end = s.index( last, start )
        return s[start:end]
    except ValueError:
        return ""
        
#Get the parameter 

def getParameter( parameterlist ):
	try:
	 	parameters=parameterlist.split(',')
		for index, parameter  in enumerate(parameters):
			if '+1' in parameter:
				return parameter.replace("\n","").strip()
	except ValueError:
        	return ""





"""
Function to Take care of the parentheses During 

#substitutor='(X2(_N1(B,A),A,B)'
#left=None
#right=None

"""
def parenthesesOrganizer( substitutor ,left ,right):
	if left is None:
		left=""
	if right is None:
		right=""
	if substitutor[0]=="(":
		left=left+"("
		substitutor=substitutor[1:len(substitutor)]
		if substitutor[len(substitutor)-1]==")":
			right=right+")"
			substitutor=substitutor[0:len(substitutor)-1]
			leftin=None
			rightin=None
			leftin,rightin,substitutor_update=parenthesesOrganizer(substitutor,leftin ,rightin)
			if leftin is not None and rightin is not None:
				substitutor=leftin+substitutor_update+rightin
		else:
			substitutor="("+substitutor
			left=left[0:len(left)-1]
	return left,right,substitutor


"""

#Get Function Name 
#This can be done using Regular expression ...Need to update
"""
def getFunctionName(function,parameters ):
	for parameter in parameters:
		function=function.replace(parameter,"")
	blanklist=find_between( function,'(',')')
	function=function.replace("("+str(blanklist)+")","")
	return function


"""

axiomes to Z3 statements

"""


"""
#Test Case 1
#variable="n1"

#Test Case 2
#variable="_n1"

"""


def isConstant( variable ):
	status=False
	find=regex.compile(r'[_]N\d')
	group = find.search(variable)
	if group is not None:
		status=True
	return status


def isFunCallbyRef( variable ):
	status=False
	find=regex.compile(r'f\d[_]\d[_]RET')
	group = find.search(variable)
	if group is not None:
		status=True
	return status


#fun_name="ackermann_2"

#fun_list=['ackermann']

def isRecurrenceFun( fun_name, fun_list ):
	status=False
        for fun in fun_list:
            if fun_name.startswith(fun+'_')==True:
                digit=fun_name.replace(fun+'_', '')
                if is_number(digit)==True:
                    return fun
	return None




"""
#Test Case 1
#variable="n1"

#Test Case 2
#variable="_n1"

"""


def isLoopvariable( variable ):
	status=False
	find=regex.compile(r'[_]n\d')
	group = find.search(variable)
	if group is not None:
		status=True
	return status


"""
#Test Case 1
#variable="C1"

#Test Case 2
#variable="C0"

"""


def isConstInResult( variable ):
	status=False
	find=regex.compile(r'C\d')
	group = find.search(variable)
	if group is not None:
		status=True
	return status


#Test Case 1
#variable="d1array4"

#Test Case 2
#variable="d1ar4"	
	
def isArrayFunction( variable ):
	status=False
	find=regex.compile(r'([d]\d[a][r][r][a][y]\d|[d]\d[a][r][r][a][y])')
	group = find.search(variable)
	if group is not None:
		status=True
	return status


#Is Boolean Variable

#Test Case 1
#variable="bool_go_error1"

#Test Case 2
#variable="bool_go_error2"	
	
def isBoolVariable( variable ):
	status=False
	find=regex.compile(r'([b][o][o][l][_][g][o][_])')
	group = find.search(variable)
	if group is not None:
		status=True
	return status




#expression='n+1'

def replaceAddOperator(expression):
	p = regex.compile(r'[A-Za-z|\d|\)|\]][+][A-Za-z|\d|\(|\]]')
	result=(p.sub(lambda m: m.group().replace("+", " + "), expression))
	result=replaceAddOperator1(result)
	return result

def replaceAddOperator1(expression):
	p = regex.compile(r'[A-Za-z|\d|\s][+][A-Za-z|\d]')
	result=(p.sub(lambda m: m.group().replace("+", "+ "), expression))
	return result
	



#Is Varible is Substitution Variable
# variable = 'f1_1_i'
def isSubsVar( variable ):
	status=False
	find=regex.compile(r'f\d[_]\d')
	group = find.search(variable)
	if group is not None:
		status=True
	return status



"""
#Extract arguments from smallest function

#Example 1: expr="smallest(n,_N1,su(n)>X(n))"
#extract_args(expr):

"""
def extract_args(expr):
    paren = 0
    start = 0
    ret = []
    for i, c in enumerate(expr):
        if c=='(':
            paren+=1
            if paren==1:
                start=i+1
        elif c==')':
            if paren==1 and start:
                ret.append(expr[start: i]) 
            paren-=1
        elif c==',' and paren==1:
            ret.append(expr[start:i])
            start=i+1
    return ret


# expr_replace(e,e1,e2): replace all subterm e1 in e by e2

#e=['a', ['implies', ['<', ['_n1'], ['_N1']], ['<', ['x2', ['_n1']], ['y2', ['_n1']]]]]

#e=['a', ['<', ['x2', ['_N1']], ['y2', ['_N1']]]]

def expr_complement(e): #e,e1,e2: expres
    if e[:1]==['<']:
    	e[:1]=['>=']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['>']:
    	e[:1]=['<=']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['>=']:
        e[:1]=['<']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['<=']:
        e[:1]=['>']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['==']:
        e[:1]=['!=']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['!=']:
        e[:1]=['==']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['&&']:
        e[:1]=['||']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['||']:
        e[:1]=['&&']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['and']:
        e[:1]=['or']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['or']:
        e[:1]=['and']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    else:
        return e[:1]+list(expr_complement(x) for x in expr_args(e))



""" 
#Function to replace variable by constant
#Test Case
#e=['a', ['<', ['x2', ['_n1']], ['y2', ['_n1']]]]
#variable='_n1'
#constant='_N1'
#expr_replace_const(e,variable,constant)
"""

def expr_replace_const(e,variable,constant):
	if e[:1]==expres(variable):
		e[:1]=expres(constant)
	return e[:1]+list(expr_replace_const(x,variable,constant) for x in expr_args(e))


def get_All_Var(e,var_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
    	if is_number(op)==False and is_hex(op)==None and op not in _base:
        	var_map.append(op)
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                get_All_Var(args[0],var_map)
            else:
            	for x in args:
            		get_All_Var(x,var_map)
        elif op=='not' and len(args)==1:
            get_All_Var(args[0],var_map)
        elif op=='implies' and len(args)==2:
            get_All_Var(args[0],var_map)
            get_All_Var(args[1],var_map)
        elif op in _infix_op and len(args)==2:
            get_All_Var(args[0],var_map)
            get_All_Var(args[1],var_map)
        else:
        	if is_number(op)==False and is_hex(op)==None and op not in _base:
        		var_map.append(op)
        	for x in args:
        		get_All_Var(x,var_map)




#substituting close form solution in rest of the axiomes
def solnsubstitution(axioms,key,substituter):
	update_axioms=[]
    	for axiom in axioms:
    		if axiom[0]!='i0' and axiom[0]!='i1':
               		update_axioms.append(expr_replace(axiom,key,substituter))
    		else:
                        if axiom[0]=='i1':
                            axiom[4]=expr_replace(axiom[4],key,substituter)
                            update_axioms.append(axiom)
                        elif axiom[0]=='i0':
                            axiom[3]=expr_replace(axiom[3],key,substituter)
                            update_axioms.append(axiom)
                        else:
                            update_axioms.append(axiom)
    	return update_axioms



    
def solnsubstitution_Array(axioms,key,substituter):
	update_axioms=[]
    	for axiom in axioms:
    		if axiom[0]!='i0' and axiom[0]!='i1':
               		update_axioms.append(expr_array_replace(axiom,key,substituter))
    		else:
                        if axiom[0]=='i1':
                            axiom[4]=expr_array_replace(axiom[4],key,substituter)
                            update_axioms.append(axiom)
                        elif axiom[0]=='i0':
                            axiom[3]=expr_array_replace(axiom[3],key,substituter)
                            update_axioms.append(axiom)
                        else:
                            update_axioms.append(axiom)
    	return update_axioms






"""
Reading the contain of the file 
"""
def readingFile( filename ):
	content=None
	with open(currentdirectory+"/"+filename) as f:
    		content = f.readlines()
    	return content
 
"""
Wrtitting the contain on file 
"""
def writtingFile( filename , content ):
	file = open(currentdirectory+"/"+filename, "w")
	file.write(str(content))
	file.close()
        #if '.graphml' in filename:
        #    st = os.stat(currentdirectory+"/"+filename)
        #    print st.st_size

"""
Appending the contain on file 
"""
def appendingFile( filename , content ):
	file = open(currentdirectory+"/"+filename, "a")
	file.write(str(content))
	file.close()

"""

write logs

"""

def writeLogFile(filename , content):
	if os.path.isfile(currentdirectory+"/"+filename):
    		appendingFile( filename , content )
	else:
    		writtingFile( filename , content )
                

"""
Wrtitting the contain on file 
"""
def writtingWittness( filename , content ):
	if os.path.isfile(filename):
    		writtingFile( filename , content )
	else:
    		writtingFile( filename , content )


"""
Convert Inequality to Normal Form

"""


def normal_form_constant(expression, constant):
    #print "*************"
    #print expression
    #print "*************"
    mult_by_minus_one_map = {
    	None: '==',
    	'>=': '<=',
    	'<=': '>=',
    	'>': '<',
    	'<': '>',
	}
    ineq=simplify(expression)
    l = ineq.lhs
    r = ineq.rhs
    op = ineq.rel_op
    all_on_left = l - r
    coeff_dict = all_on_left.as_coefficients_dict()
    var_types = coeff_dict.keys()
    new_rhs = sympify(0)
    for s in var_types:
    	if s != simplify(constant):
    		factor=s.coeff(simplify(constant))
        	if factor==0:
            		all_on_left = (all_on_left - (coeff_dict[s]*s))
            		new_rhs = (new_rhs - (coeff_dict[s]*s))
    all_on_left=all_on_left.expand(basic=True)
    coeff_dict = all_on_left.as_coefficients_dict()
    var_types = coeff_dict.keys()
    if len(var_types)==1:
    	for s in var_types:
    		if coeff_dict[s]<0:
    			all_on_left = all_on_left * -1
        		new_rhs = new_rhs * -1
        		op = mult_by_minus_one_map[op]	
    	factor=all_on_left.coeff(simplify(constant))
    	if factor!=0:
		all_on_left=all_on_left/factor
    		new_rhs=new_rhs/factor
    else:
    	all_on_left=simplify(all_on_left)
    	new_rhs=simplify(new_rhs)
    	coeff_dict = all_on_left.as_coefficients_dict()
    	var_types = coeff_dict.keys()
    	if len(var_types)==1:
	 	for s in var_types:
	 		if coeff_dict[s]<0:
	    			all_on_left = all_on_left * -1
	        		new_rhs = new_rhs * -1
        			op = mult_by_minus_one_map[op]	
    
    #print "*************"
    #print all_on_left
    #print new_rhs
    #print "*************"
    return Relational(all_on_left,new_rhs,op)



def solve_for_constant(expression, constant):
    #print "*************"
    #print expression
    #print "*************"
    mult_by_minus_one_map = {
    	None: '==',
    	'>=': '<=',
    	'<=': '>=',
    	'>': '<',
    	'<': '>',
	}
    all_on_left=simplify(expression)
    coeff_dict = all_on_left.as_coefficients_dict()
    var_types = coeff_dict.keys()
    new_rhs = sympify(0)
    for s in var_types:
    	if s != simplify(constant):
    		factor=s.coeff(simplify(constant))
        	if factor==0:
            		all_on_left = (all_on_left - (coeff_dict[s]*s))
            		new_rhs = (new_rhs - (coeff_dict[s]*s))
    all_on_left=all_on_left.expand(basic=True)
    coeff_dict = all_on_left.as_coefficients_dict()
    var_types = coeff_dict.keys()
    if len(var_types)==1:
    	for s in var_types:
    		if coeff_dict[s]<0:
    			all_on_left = all_on_left * -1
        		new_rhs = new_rhs * -1
        		op = mult_by_minus_one_map[op]	
    	factor=all_on_left.coeff(simplify(constant))
    	if factor!=0:
            if new_rhs is not None:
                if '**' not in str(new_rhs):
                    parser = c_parser.CParser()
                    ast = parser.parse("void test(){"+str(new_rhs)+";}")
                    statement_temp=ast.ext[0].body.block_items[0]
                    axupdate = construct_expression_normalC(eval(expressionCreator_C(statement_temp)))
                    new_rhs=eval("['/',"+str(axupdate[1])+",['"+str(factor)+"']]")
                    return new_rhs
                else:
                    return None
        else:
            if new_rhs is not None:
                if '**' not in str(new_rhs):
                    parser = c_parser.CParser()
                    ast = parser.parse("void test(){"+str(new_rhs)+";}")
                    statement_temp=ast.ext[0].body.block_items[0]
                    axupdate = construct_expression_normalC(eval(expressionCreator_C(statement_temp)))
                    return axupdate[1]
                else:
                    return None
    else:
    	all_on_left=simplify(all_on_left)
    	new_rhs=simplify(new_rhs)
    	coeff_dict = all_on_left.as_coefficients_dict()
    	var_types = coeff_dict.keys()
    	if len(var_types)==1:
	 	for s in var_types:
	 		if coeff_dict[s]<0:
	    			all_on_left = all_on_left * -1
	        		new_rhs = new_rhs * -1
        			op = mult_by_minus_one_map[op]	
    
    return None








#To construct vfact
def wff2fvact(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            return expr2string1(w[-2])
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1':
            return expr2string1(w[1])
            
"""
Construct vfact by analysis translated equation equation 
"""

def getVariFunDetails(f,o,a,variableMapIp,variableMapOp):
	constaints=[]
	loopvariablesMap={}
	functionMap={}
	vfacts=""
	for variable in variableMapIp:
            values=variableMapIp[variable]
            if values.getDimensions()>0:
            	vfact="['"+variable+"',0,['array']]"
	    else:
	    	if values.getVariableType()=='int':	
		        vfact="['"+variable+"',0,['int']]"
                elif values.getVariableType()=='long':	
		        vfact="['"+variable+"',0,['int']]"
		elif values.getVariableType()=='unsigned':	
		        vfact="['"+variable+"',0,['int']]"
		elif values.getVariableType()=='float':
		        vfact="['"+variable+"',0,['float']]"
		elif values.getVariableType()=='double':
			vfact="['"+variable+"',0,['double']]"
                elif values.getVariableType()=='_Bool':
			vfact="['"+variable+"',0,['Bool']]"
		elif values.getVariableType()=='array':
			vfact="['"+variable+"',0,['array']]"
            if vfacts=="":
            	#vfact=''
                vfacts=vfact
            else:
                if vfact!="":
                    vfacts+=","+vfact
	
	
	for variable in variableMapOp:
            values=variableMapOp[variable]
	    if values[1]=='int':	
                vfact="['"+variable+"',0,['int']]"
	    elif values[1]=='unsigned':	
		vfact="['"+variable+"',0,['int']]"
	    elif values[1]=='long':	
		vfact="['"+variable+"',0,['int']]"
	    elif values[1]=='float':
                vfact="['"+variable+"',0,['float']]"
	    elif values[1]=='double':
		vfact="['"+variable+"',0,['double']]"
	    elif values[1]=='array':
	    	vfact="['"+variable+"',0,['array']]"
	    elif values[1]=='unsigned':
	    	vfact="['"+variable+"',0,['int']]"
            elif values[1]=='_Bool':
	    	vfact="['"+variable+"',0,['Bool']]"
	    elif values[1]=='array':
	    	vfact="['"+variable+"',0,['array']]"
            if vfacts=="":
                vfacts=vfact
            else:
                if vfact!="":
                    vfacts+=","+vfact
	
	equations=[]
        for x in a: 
        	equations.append(wff2fvact(x))
            
	for equation in equations:
		if equation is not None and '->' not in equation and '>' not in equation and '<' not in equation and '=' not in equation :
			loopvariables=extract_args(equation)
			equation=equation.strip()
			vfact=""
			if len(loopvariables)==0:	
				if equation not in variableMapOp.keys():
					if equation in variableMapIp.keys():
						values=variableMapIp[equation]
						if values[1]=='int':	
							vfact="['"+equation+"',0,['int']]"
						elif values[1]=='unsigned':	
							vfact="['"+equation+"',0,['int']]"
						elif values[1]=='float':
							vfact="['"+equation+"',0,['float']]"
						elif values[1]=='double':
							vfact="['"+equation+"',0,['double']]"
                                                elif values[1]=='_Bool':
							vfact="['"+equation+"',0,['Bool']]"
					else:
						vfact="['"+equation+"',0,['int']]"
				
			else:
				function_name=getFunctionName(str(equation),loopvariables )
				if function_name not in functionMap.keys() and isArrayFunction(function_name)==False:
					functionMap[function_name]=function_name
					fact="['int'"
					for x in xrange(len(loopvariables)):
						fact+=",'int'"
					fact+="]"
					vfact="['"+function_name+"',"+str(len(loopvariables))+","+fact+"]"	
			if vfacts=="":
				vfacts=vfact
			else:
				if vfact!="":
					vfacts+=","+vfact
		elif equation is not None and '->' in equation:
			axiomes=equation.split('->')
			axiomes[0]=simplify(str(axiomes[0]))
			variables=str(axiomes[0]).split('<')
			variables[0]=variables[0].strip()
			variables[1]=variables[1].strip()
			loopvariables=extract_args(variables[1])
			loopvariablesMap[variables[0]]=variables[0]
			parameter=""
			for variable in  loopvariables:
				variable=variable.strip()
				if parameter=="":
                                        if '__VERIFIER_nondet' in variable:
                                            tem_var_list = extract_args(variable)
                                            for tem_var in tem_var_list:
                                                if parameter=="":
                                                    parameter="["+tem_var
                                                else:
                                                    parameter+=" ,"+tem_var
                                        else:
                                            parameter="["+variable
				else:
					parameter+=" ,"+variable
					loopvariablesMap[variable]=variable
			if parameter=="":
				constaint=variables[1]+">=0"
			else:
				parameter+="]"
				constaint="ForAll("+parameter+","+variables[1]+">=0)"
			constaints.append(constaint)
			vfact=""
			if len(loopvariables)==0:	
				vfact="['"+variables[1]+"',0,['int']]"			
			else:
				fact="['int'"
				for x in xrange(len(loopvariables)):
					fact+=",'int'"
				fact+="]"
				function_name=getFunctionName(str(variables[1]),loopvariables )
				if isArrayFunction(function_name)==False:
					vfact="['"+getFunctionName(str(variables[1]),loopvariables )+"',"+str(len(loopvariables))+","+fact+"]"	
			if vfacts=="":
				vfacts=vfact
			else:
				if vfact!="":
					vfacts+=","+vfact
	
	for loopvariable in loopvariablesMap:

		if vfacts=="":
			vfacts="['"+loopvariable+"',0,['int']]"
		else:
		 	vfacts+=","+"['"+loopvariable+"',0,['int']]"
	vfacts=eval("["+vfacts+"]")
	return vfacts,constaints


#Collect all Function and Variable defination for Translation 2

def getVariFunDetails2(f,o,a,allvariablelist,constraints,assert_list,assume_list):
	var_map={}
	for x in f:
            wff2stringvfact2(f[x],var_map,allvariablelist,constraints)
	for x in o:
            wff2stringvfact2(o[x],var_map,allvariablelist,constraints)
        for x in a:
            wff2stringvfact2(x,var_map,allvariablelist,constraints)
        for x in assert_list:
            wff2stringvfact2(x,var_map,allvariablelist,constraints)
        for x in assume_list:
            wff2stringvfact2(x,var_map,allvariablelist,constraints)
        return var_map



"""
Expanding algebraic powers
"""

def pow_to_mul(expression):
    """
    Convert integer powers in an expression to Muls, like a**2 => a*a(Only for Squre).
    """
    #expression=simplify(expression).expand(basic=True)
    #expression=simplify(expression)
    pows=list(expression.atoms(Pow))
    if any(not e.is_Integer for b, e in (i.as_base_exp() for i in pows)):
    	#A power contains a non-integer exponent
    	return expression
    repl=None
    for b,e in (i.as_base_exp() for i in pows):
    	if e==2:
    		repl = zip(pows,((Mul(*[b]*e,evaluate=False)) for b,e in (i.as_base_exp() for i in pows)))
    if repl is not None:
    	return expression.subs(repl)
    else:
    	return expression



"""
#Function to Simplify and Expand an expression using sympy
"""
def simplify_expand_sympy(expression):
    if 'If' in str(expression) or '%' in str(expression):
    	return expression
    if 'Implies' not in expression and 'ite' not in expression and '==' not in  expression and '!=' not in  expression and 'And' not in  expression and 'Or' not in  expression and 'Not' not in  expression and 'ForAll' and 'Exists' not in  expression and 'Implies' not in expression:
    	return str(simplify_sympy(expression))
    elif 'Implies' in expression :
        axioms=extract_args(expression)
        if len(axioms)==2:
            #return 'Implies('+simplify_expand_sympy(axioms[0])+','+simplify_expand_sympy(axioms[1])+')'
            return 'Implies('+axioms[0]+','+simplify_expand_sympy(axioms[1])+')'
        else:
            return expression
    elif 'ite' in expression and 'And' not in  expression and 'Or' not in  expression and 'Not' not in  expression and 'ForAll' and 'Exists' not in  expression and 'Implies' not in expression:
        axioms=extract_args(expression)
        if len(axioms)==3:
            return 'If('+simplify_expand_sympy(axioms[0])+','+simplify_expand_sympy(axioms[1])+','+simplify_expand_sympy(axioms[2])+')'
        else:
            return expression
    elif '==' in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression and 'And' not in  expression and 'Or' not in  expression and 'Not' not in  expression and 'ForAll' and 'Exists' not in  expression and 'Implies' not in expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('==')
        if len(axioms)!=2:
            return expression
        if left is not None and right is not None:
        	if '%' in axioms[0]:
        		leftin =None
			rightin =None
        		leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
        		axm=axioms[0].split('%')
        		if left is not None and right is not None:
        			expression="("+left+leftin+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+rightin+')==('+str(simplify_sympy(axioms[1]))+right+")"
        		else:
        			expression="("+left+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+')==('+str(simplify_sympy(axioms[1]))+right+")"
        	
        	else:
        		expression="("+left+str(simplify_sympy(axioms[0]))+')==('+str(simplify_sympy(axioms[1]))+right+")"
        		#expression=left+str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(powsimp(pow_to_mul(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	if '%' in axioms[0]:
			leftin =None
			rightin =None
			leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
			axm=axioms[0].split('%')
			if left is not None and right is not None:
				expression=left+leftin+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+rightin+'=='+str(simplify_sympy(axioms[1]))+right
			else:
				expression=left+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+'=='+str(simplify_sympy(axioms[1]))+right
		        	
        	else:
        		expression=str(simplify_sympy(axioms[0]))+'=='+str(simplify_sympy(axioms[1]))
        		#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    elif '!=' in  expression and 'and' not in  expression and 'or' not in  expression and 'And' not in  expression and 'Or' not in  expression and 'Not' not in  expression and 'ForAll' and 'Exists' not in  expression and 'Implies' not in expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('!=')
        if len(axioms)!=2:
            return expression
        if left is not None and right is not None:
              	if '%' in axioms[0]:
	        	leftin =None
			rightin =None
	        	leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
	        	axm=axioms[0].split('%')
	        	if leftin is not None and rightin is not None:
	        		expression=left+leftin+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+rightin+'=='+str(simplify_sympy(axioms[1]))+right
	        	else:
        			expression=left+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+'=='+str(simplify_sympy(axioms[1]))+right
        	else:
        		expression=left+str(simplify_sympy(axioms[0]))+'!='+str(simplify_sympy(axioms[1]))+right
        		#expression=left+str(powsimp(pow_to_mul(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	 if '%' in axioms[0]:
		 	leftin =None
			rightin =None
			leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
			axm=axioms[0].split('%')
			if leftin is not None and rightin is not None:
				expression=left+leftin+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+rightin+'=='+str(simplify_sympy(axioms[1]))+right
			else:
		        	expression=left+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+'=='+str(simplify_sympy(axioms[1]))+right

        	 else:
        		expression=str(simplify_sympy(axioms[0]))+'!='+str(simplify_sympy(axioms[1]))
        		#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    else:
        return  expression

"""
#convert all power operator to power function
"""
def convert_pow_op_fun(expression):
    return expression


def convert_pow_op_fun1(expression):
    if 'Implies' not in expression and 'ite' not in expression and 'If' not in expression and '==' not in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
        return  translatepowerToFun(expression)
    elif 'Implies' in expression:
        axioms=extract_args(expression)
        return 'Implies('+convert_pow_op_fun(axioms[0])+','+convert_pow_op_fun(axioms[1])+')'
    elif 'ite' in expression:
        axioms=extract_args(expression)
        return 'If('+convert_pow_op_fun(axioms[0])+','+convert_pow_op_fun(axioms[1])+','+convert_pow_op_fun(axioms[2])+')'
    elif 'If' in expression:
        axioms=extract_args(expression)
        return 'If('+convert_pow_op_fun(axioms[0])+','+convert_pow_op_fun(axioms[1])+','+convert_pow_op_fun(axioms[2])+')'
    elif '==' in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
        expression=translatepowerToFun(expression)
        return expression
    elif '!=' in  expression and 'and' not in  expression and 'or' not in  expression:
        expression=translatepowerToFun(expression)
        return expression
    else:
        return  translatepowerToFun(expression)


def simplify_sympy(expression):
        #if '/' in str(expression) and '>' not in str(expression) and '<' not in str(expression) and '=' not in str(expression):  
        if '<<' in str(expression) or '>>' in str(expression) or 'ite' in str(expression) or 'and' in str(expression) or '&' in  str(expression) or '|' in str(expression) or '^' in str(expression):
		return expression 
        try:
            sympify(expression)
        except Exception as e:
            return expression
        
        if sympify(expression)==True or sympify(expression)==False:
		return expression        
        if '/' in str(expression):
        	expression,flag=expressionChecking(expression)
        	if flag==True:
        		expression_mod=expression 
        	else:
        		expression_mod=powsimp(expression)
        else:
            if 'array' not in str(expression):
                expression_mod=powsimp(expression)
            else:
                expression_mod=expression 
    
	if '/' not in str(expression_mod) and 'E' not in str(expression_mod) and 'e' not in str(expression_mod):
		expression=expression_mod
	if '/' in str(expression):
		no,deno=fraction(together(expression))
		no=sympify(no).expand(basic=True)
		deno=sympify(deno).expand(basic=True)
		if deno==1:
			expression,flag=expressionChecking(expression)
			if flag==True:
				return expression
				#return pow_to_mul(powsimp(expression))
			else:
				return pow_to_mul(powsimp(expression))
			#return pow_to_mul(powsimp(no))
		else:
                 	return Mul(pow_to_mul(powsimp(no)), Pow(pow_to_mul(powsimp(deno)), -1), evaluate=False)
	
	else:
		#return str(sympify(expression).expand(basic=True))
		if type(expression) is str:
                    return expression
                else:
                    expressiontemp=sympify(expression).expand(basic=True)
                    if '/' in str(expressiontemp):
                            return pow_to_mul(powsimp(sympify(expression)))
                    else:
                            return pow_to_mul(powsimp(sympify(expression).expand(basic=True)))
	

def substituteValue(expression,key,value):
	if '/' in str(expression):
		#no,deno=fraction(together(expression))
		no,deno=fraction(expression)
		no=sympify(no).expand(basic=True)
		no=no.subs(simplify(key),simplify(value))
		deno=deno.subs(simplify(key),simplify(value))
		if deno==1:
			return powsimp(no)
		else:
                 	return Mul(powsimp(no), Pow(powsimp(deno), -1), evaluate=False)
	
	else:
		return simplify(expression).subs(simplify(key),simplify(value))




"""
#Function to Simplify and Expand an expression using sympy
"""
def sub_ind_def(expression,variable,constant):
    if 'Implies' not in expression and 'ite' not in expression and '==' not in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
    	return expression.replace(variable,constant)
    elif 'Implies' in expression :
        axioms=extract_args(expression)
        #return 'Implies('+simplify_expand_sympy(axioms[0])+','+simplify_expand_sympy(axioms[1])+')'
        return 'Implies('+axioms[0]+','+sub_ind_def(axioms[1],variable,constant)+')'
    elif 'ite' in expression:
        axioms=extract_args(expression)
        return 'If('+sub_ind_def(axioms[0],variable,constant)+','+sub_ind_def(axioms[1],variable,constant)+','+sub_ind_def(axioms[2],variable,constant)+')'
    elif '==' in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('==')
        if left is not None and right is not None:
        	if '%' in axioms[0]:
        		leftin =None
			rightin =None
        		leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
        		axm=axioms[0].split('%')
        		if left is not None and right is not None:
        			expression=left+leftin+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+rightin+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
        		else:
        			expression=left+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
        	
        	else:
        		expression=left+str(sub_ind_def(axioms[0]))+'=='+str(sub_ind_def(axioms[1]))+right
        		#expression=left+str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(powsimp(pow_to_mul(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	if '%' in axioms[0]:
			leftin =None
			rightin =None
			leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
			axm=axioms[0].split('%')
			if left is not None and right is not None:
				expression=left+leftin+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+rightin+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
			else:
				expression=left+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
		        	
        	else:
        		expression=str(simplify_sympy(axioms[0]))+'=='+str(simplify_sympy(axioms[1]))
        		#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    elif '!=' in  expression and 'and' not in  expression and 'or' not in  expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('!=')
        if left is not None and right is not None:
              	if '%' in axioms[0]:
	        	leftin =None
			rightin =None
	        	leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
	        	axm=axioms[0].split('%')
	        	if leftin is not None and rightin is not None:
	        		expression=left+leftin+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+rightin+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
	        	else:
        			expression=left+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
        	else:
        		expression=left+str(sub_ind_def(axioms[0],variable,constant))+'!='+str(sub_ind_def(axioms[1],variable,constant))+right
        		#expression=left+str(powsimp(pow_to_mul(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	 if '%' in axioms[0]:
		 	leftin =None
			rightin =None
			leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
			axm=axioms[0].split('%')
			if leftin is not None and rightin is not None:
				expression=left+leftin+str(sub_ind_def(axm[0],variable,constant))+'%'+str(simplify_sympy(axm[1],variable,constant))+rightin+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
			else:
		        	expression=left+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+'=='+str(sub_ind_def(axioms[1],variable,constant))+right

        	 else:
        		expression=str(sub_ind_def(axioms[0],variable,constant))+'!='+str(sub_ind_def(axioms[1],variable,constant))
        		#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    else:
        return  expression





"""
Recurrences Solving Module
#Add by Pritom Rajkhowa
#June 8

Test cases

Test Case 1

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['+', ['a3', ['_n1']], ['1']]]
#e2=['i0', 0, ['a3', ['0']], ['0']]

Test Case 2

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['*', ['a3', ['_n1']], ['+', ['_n1'], ['1']]]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

Test Case 3

#e1=['i1', 2, '_n1', ['t3', ['+', ['_n1'], ['1']]], ['+', ['t3', ['_n1']], ['2']]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

Test Case 4

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['*', ['a3', ['_n1']], ['2']]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

"""
def solve_rec(e1,e2):
        global fun_call_map
	lefthandstmt=None
	righthandstmt=None
	righthandstmt_d=None
	lefthandstmt_base=None
	righthandstmt_base=None
	righthandstmt_base_d=None
	variable=None
	closed_form_soln=None
	if e1[0]=='i1':
		lefthandstmt=expr2string1(e1[3])
		righthandstmt=expr2string1(e1[4])
		lefthandstmt=lefthandstmt.strip()
		righthandstmt=righthandstmt.strip()
		variable=e1[2]
		if lefthandstmt.find('_PROVE')>0:
			return None
		elif lefthandstmt.find('_ASSUME')>0:
        		return None
		if 'ite' not in righthandstmt and '>' not in righthandstmt and '<' not in righthandstmt and '==' not in righthandstmt and '|' not in righthandstmt and '&' not in righthandstmt: 
		    	lefthandstmt=simplify(lefthandstmt)
		    	righthandstmt=simplify(righthandstmt)
		    	variable=simplify(variable)
		else:
			if '|' not in righthandstmt and '&' not in righthandstmt and '<<' not in righthandstmt and '>>' not in righthandstmt:
                            righthandstmt=expr2stringSimplify(e1[4])
			righthandstmt=righthandstmt.strip()
			if 'ite' not in righthandstmt and '>' not in righthandstmt and '<' not in righthandstmt and '==' not in righthandstmt and '<' not in righthandstmt and '==' not in righthandstmt and '|' not in righthandstmt and '&' not in righthandstmt: 
				lefthandstmt=simplify(lefthandstmt)
				righthandstmt=simplify(righthandstmt)
		    		variable=simplify(variable)
			else:
				lefthandstmt=None
				righthandstmt=None
				variable=None
	if e2[0]=='i0':
		lefthandstmt_base=expr2string1(e2[2])
		righthandstmt_base=expr2string1(e2[3])
		variable_list=[]
		expr2varlist(e2[3],variable_list)
		lefthandstmt_base=lefthandstmt_base.strip()
		righthandstmt_base=righthandstmt_base.strip()
		if 'ite' in righthandstmt_base or '|' in righthandstmt_base or '&' in righthandstmt_base or '<<' in righthandstmt_base or '>>' in righthandstmt_base: 
			return None
		lefthandstmt_base=simplify(lefthandstmt_base)
		righthandstmt_base=simplify(righthandstmt_base)

	if variable is not None and lefthandstmt is not None and righthandstmt is not None and lefthandstmt_base is not None and righthandstmt_base is not None:
		righthandstmt_d=righthandstmt
		righthandstmt_base_d=righthandstmt_base
		term1=lefthandstmt.subs(simplify(str(variable)+"+1"),0)
		term2=lefthandstmt.subs(simplify(str(variable)+"+1"),simplify(variable))
		if term1==lefthandstmt_base and  str(term2) in str(righthandstmt):
			righthandstmt=simplify(righthandstmt).subs({simplify(term2):simplify('T(n)'),simplify(variable):simplify('n')})
			result=None
			#Try to solve recurrences
			try:
				
				result = getSympyCache(righthandstmt,righthandstmt_base)
                                
                                if result is None:
                                    #result=recurreSolver_wolframalpha(righthandstmt,righthandstmt_base,variable_list)
                                    result=recurreSolver_sympy(righthandstmt,righthandstmt_base)
				#if result is None:
					#result=recurreSolver_sympy(righthandstmt,righthandstmt_base)
					#result=recurreSolver_wolframalpha(righthandstmt,righthandstmt_base,variable_list)
			except ValueError:
				result=None
			if result is not None:
				result=substituteValue(simplify_sympy(result),simplify('n'),simplify(variable))
				writeLogFile( "j2llogs.logs" , "\nOriginal Axoims \n"+str(lefthandstmt)+"="+str(righthandstmt_d)+","+str(lefthandstmt_base)+"="+str(righthandstmt_base_d)+"\n Closed Form Solution\n"+str(result)+"\n" )
				if "**" in str(result):
					result=translatepowerToFun(str(result))
                                        
				expression=str(str(term2)+"="+str(result))
				fun_call_map={}
				parser = c_parser.CParser()
                                ast = parser.parse("void test(){"+expression+";}")
                                statement_temp=ast.ext[0].body.block_items[0]
                                
                                closed_form_soln = construct_expressionC(e1[1],e1[2],expr_replace_power(eval(expressionCreator_C(statement_temp.lvalue))),expr_replace_power(eval(expressionCreator_C(statement_temp.rvalue))))
				#tree = p.parse_expression(expression)
				#closed_form_soln=construct_expression(tree,e1[1],e1[2])
                                
			
	#return None
        return closed_form_soln



# expr_replace(e,e1,e2): replace all subterm e1 in e by e2


def expr_replace_power(e): #e,e1,e2: expr
    args=expr_args(e)
    op=expr_op(e)
    if len(args)>0:
        if op=='power' or 'power_' in op :
            return eval("['**']")+list(expr_replace_power(x) for x in expr_args(e))
        else:
            return e[:1]+list(expr_replace_power(x) for x in expr_args(e))
    else:
        return e





"""

Simplification Of Conditional Statements 

"""
def simplifyIteStatement(statement):
	print '############################'
	print expr2stringSimplify(statement[4])
	print '*************************'


"""
#Code Add by Pritom Rajkhowa
#Following Code will Translate Java Program to a Array of Statements 
"""
"""
Recurrence Solver After Translation
"""
def rec_solver(f,o,a):
    global fun_call_map
    constant_fun_map={}
    
    #return f,o,a,constant_fun_map

    equation_map={}
    base_map={}
    for axiom in a:
        if axiom[0]=='i1':
             lefthandstmt=expr2string1(axiom[3])
	     lefthandstmt=lefthandstmt.strip()
             equation_map[str(simplify(lefthandstmt))]=axiom
	if axiom[0]=='i0':
	     lefthandstmt=expr2string1(axiom[2])
	     lefthandstmt=lefthandstmt.strip()
	     base_map[str(simplify(lefthandstmt))]=axiom
	if axiom[0]=='s1':
	     equ=expr2string1(axiom[1])
	     if '->' in equ:
                 axiomes=equ.split('->')
		 axiomes[0]=simplify(str(axiomes[0]))
		 variables=str(axiomes[0]).split('<')
		 variables[0]=variables[0].strip()
		 variables[1]=variables[1].strip()
		 constant_fun_map[variables[0]]=variables[1]
    while True:
        solution_map={} 
	for equation in equation_map:
            e1=equation_map[equation]
	    equation_base=str(simplify(equation).subs(simplify(str(e1[2])+"+1"),0))
	    if equation_base in base_map.keys():
                e2=base_map[equation_base]
                result=solve_rec(e1,e2)
                if result is not None:
                    a.remove(base_map[equation_base])
                    del base_map[equation_base]
                    solution_map[equation]=result
    
	for equation in solution_map:
            a.remove(equation_map[equation])
	    del equation_map[equation]
	    e=solution_map[equation]
	    e1=copy.deepcopy(e)
	    variable=e[2]
	    a=solnsubstitution(a,e[3],e[4])
	    constant=constant_fun_map[variable]
	    #p = getParser()
	    #tree = p.parse_expression(constant)
	    #constant=eval(expressionCreator(tree))
            fun_call_map={}
            parser = c_parser.CParser()
            ast = parser.parse("void test(){"+str(constant)+";}")
            statement_temp=ast.ext[0].body.block_items[0]
            constant=eval(expressionCreator_C(statement_temp))
	    variable_list=eval("expres('"+variable+"')")
	    e1[3]=expr_replace(e1[3],variable_list,constant)
	    e1[4]=expr_replace(e1[4],variable_list,constant)
	    a=solnsubstitution(a,e1[3],e1[4])
	    for x in o:
                stmt=o[x]
		stmt[2]=expr_replace(stmt[2],e1[3],e1[4])
	if len(equation_map)==0 or len(solution_map)==0:
            break
    return f,o,a,constant_fun_map



def update__VERIFIER_nondet_stmt(e,var_map):
    args=expr_args(e)
    if '__VERIFIER_nondet' in e[0] and len(args)==0:
        if e[0] in var_map.keys():
            VC=var_map[e[0]]
            VC=VC+1
            key=e[0]
            var_map[key]=VC
            e[0] = e[0]+str(VC)
            return e
        else:
            key=e[0]
            var_map[key]=2
            e[0] = e[0]+str(2)
            return e
    else:
        return e[:1]+list(update__VERIFIER_nondet_stmt(x,var_map) for x in expr_args(e))




#Get all typedefination

typedef_map={}

def getAllTypeDef(ast):
	global typedef_map
	typedef_map={}
	generator = c_generator.CGenerator()
	for element in ast.ext:
		if type(element) is c_ast.Typedef: 
			if type(element.type.type) is c_ast.Struct:
				program_temp="struct "+ast.ext[0].type.type.name+";"
				temp_ast = parser.parse(program_temp)
				typedef_map[element.name]=generator.visit(temp_ast.ext[0])
			else:
				typedef_map[element.name]=generator.visit(element.type)	
				
				
				
				
				
def updateTypeDef(statement):
	global typedef_map
	parser = c_parser.CParser()
	pointer=None
	array=None
	if type(statement) is c_ast.Decl:
		if type(statement.type) is c_ast.PtrDecl:
			degree=0
    			type_stmt,degree,structType=getArrayDetails(statement,degree)
    			#if degree==1:
    			#	if type_stmt in typedef_map.keys():
    			#		type_stmt=typedef_map[type_stmt]
    			#	program_temp=type_stmt+' '+ statement.name
    			#	pointer=statement.name
    			#else:
    			#    	if type_stmt in typedef_map.keys():
			#    		type_stmt=typedef_map[type_stmt]
			#    	program_temp=type_stmt+' '+ statement.name
			#    	for x in range(0,degree):
    			#		program_temp+='[]'
    			#	pointer=statement.name
    			# commented on 16/11/2016
    			if type_stmt in typedef_map.keys():
				type_stmt=typedef_map[type_stmt]
			program_temp=type_stmt+' '+ statement.name
			for x in range(0,degree):
			    	program_temp+='[]'
    			pointer=statement.name
    			
    			program_temp+=';'
    			temp_ast = parser.parse(program_temp)
    			return temp_ast.ext[0],pointer,array
    		elif type(statement.type) is c_ast.ArrayDecl:
			degree=0
                        dimensionmap={}
    			type_stmt,degree,structType=getArrayDetails(statement,degree,dimensionmap)
			if type_stmt in typedef_map.keys():
				type_stmt=typedef_map[type_stmt]
			program_temp=type_stmt+' '+statement.name
			for x in range(0,degree):
				program_temp+='[]'
			program_temp+=';'
			array=statement.name
			temp_ast = parser.parse(program_temp)
    			#return temp_ast.ext[0],pointer,array
                        return statement,pointer,array
    		else:
    			type_stmt= statement.type.type.names[0]
    			if type_stmt in typedef_map.keys():
				type_stmt=typedef_map[type_stmt]
			program_temp=type_stmt+' '+ statement.name
			generator = c_generator.CGenerator()
			if statement.init is not None:
				value=generator.visit(statement.init)
				if value is not None:
					program_temp+='='+value
			program_temp+=';'
			temp_ast = parser.parse(program_temp)
    			return temp_ast.ext[0],pointer,array
	return None,pointer,array


def pointerHandlingParameter(ast):

	if type(ast) is c_ast.FuncDef:
		pointer_list=[]
		array_list=[]
		new_stmts=[]
		new_parameters=''
		generator = c_generator.CGenerator()
		parser = c_parser.CParser()
		if ast.decl.type.args is not None:
			parameters=ast.decl.type.args.params
			if parameters is not None:
				for parameter in parameters:
					if new_parameters=='':
						type_decl,pointer,array=updateTypeDef(parameter)
						if pointer is not None:
							pointer_list.append(pointer)
						if array is not None:
							array_list.append(array)
						new_parameters=generator.visit(type_decl)
					else:
						type_decl,pointer,array=updateTypeDef(parameter)
						if pointer is not None:
							pointer_list.append(pointer)
						if array is not None:
							array_list.append(array)
						new_parameters+=','+generator.visit(type_decl)
		return_type=generator.visit(ast.decl.type.type)
		function_name=ast.decl.name
    		new_fun=return_type+' '+ function_name+'('+ new_parameters +'){}'
    		new_fun=parser.parse(new_fun)
    		return new_fun.ext[0].decl,pointer_list,array_list
	else:
		return None,[],[]


def pointerHandlingDecl(function_body,pointer_list,array_list):
	update_statements=[]
	statements=function_body.block_items
	for statement in statements:
		if type(statement) is c_ast.Decl:
			new_statement,pointer,array=updateTypeDef(statement)
			new_stmt=None
			if pointer is not None:
				if statement.init is not None:
					if type(statement.init) is c_ast.InitList:
						new_statement=None
						new_stmt=None
					else:
						new_stmt=c_ast.Assignment(op='=', lvalue=c_ast.ID(name=pointer), rvalue=ref2function(statement.init))
				pointer_list.append(pointer)
			if array is not None:
				array_list.append(array)
			if new_statement is not None:
				update_statements.append(new_statement)
				if new_stmt is not None:
					update_statements.append(new_stmt)
			else:
				update_statements.append(statement)
		else:
			update_statements.append(statement)
	fun_body=c_ast.Compound(block_items=update_statements)
	return fun_body
	




def pointerHandling(statements,pointer_list,array_list):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Decl:
			new_statement,pointer,array=updateTypeDef(statement)
			if pointer is not None:
				pointer_list.append(pointer)
			if array is not None:
				array_list.append(array)
			if new_statement is not None:
				update_statements.append(new_statement)
			else:
				update_statements.append(statement)
		elif type(statement) is c_ast.If:
			update_statements.append(pointerHandlingIf(statement,pointer_list,array_list))
		elif type(statement) is c_ast.While:
			if statement.stmt.block_items is not None:
                		update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=pointerHandling(statement.stmt.block_items,pointer_list,array_list))))
		elif type(statement) is c_ast.Assignment:
			update_statements.append(c_ast.Assignment(op=statement.op,lvalue=defref2function(statement.lvalue,pointer_list,array_list),rvalue=defref2function(statement.rvalue,pointer_list,array_list)))
		else:
			update_statements.append(statement)
	return update_statements
	


	
def pointerHandlingIf(statement,pointer_list,array_list):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.Assignment:
        	new_iftrue=c_ast.Assignment(op=statement.iftrue.op,lvalue=defref2function(statement.iftrue.lvalue,pointer_list,array_list),rvalue=defref2function(statement.iftrue.rvalue,pointer_list,array_list))
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=pointerHandling(statement.iftrue.block_items,pointer_list,array_list)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
       
       
        if type(statement.iffalse) is c_ast.Assignment:
		new_iftrue=c_ast.Assignment(op=statement.iffalse.op,lvalue=defref2function(statement.iffalse.lvalue,pointer_list,array_list),rvalue=defref2function(statement.iffalse.rvalue,pointer_list,array_list))
	elif type(statement.iffalse) is c_ast.Compound:
		if statement.iffalse.block_items is not None:
	        	new_block_items=pointerHandling(statement.iffalse.block_items,pointer_list,array_list)
	                new_iffalse=c_ast.Compound(block_items=new_block_items)
	        else:
	                new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.If:
		new_iffalse=pointerHandlingIf(statement.iffalse,pointer_list,array_list)
	else:
        	new_iffalse=statement.iffalse
        	
    return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
    
    
#def defref2function(statement,pointer_list,array_list):
#	if type(statement) is c_ast.UnaryOp:
#		parameter=[]
#		if statement.op=='*' and statement.expr.name in pointer_list:
#			parameter.append(statement.expr)
#			return c_ast.FuncCall(name=c_ast.ID(name='_data'), args=c_ast.ExprList(exprs=parameter))
#		elif statement.op=='*' and statement.expr.name in array_list:
#
#			return c_ast.ArrayRef(name=statement.expr, subscript=c_ast.Constant(type='int', value='0'))
#			#return c_ast.FuncCall(name=c_ast.ID(name='_data'), args=c_ast.ExprList(exprs=parameter))
#		elif statement.op=='&' and statement.expr.name in pointer_list:
#			parameter.append(statement.expr)
#			return c_ast.FuncCall(name=c_ast.ID(name='_address'), args=c_ast.ExprList(exprs=parameter))
#		else:
#			return c_ast.UnaryOp(op=statement.op, expr=defref2function(statement.expr,pointer_list,array_list))
#	elif type(statement) is c_ast.BinaryOp:
#		return c_ast.BinaryOp(op=statement.op,left=defref2function(statement.left,pointer_list,array_list),right=defref2function(statement.right,pointer_list,array_list))
#	else:
#		return statement





def defref2function(statement,pointer_list,array_list):
	if type(statement) is c_ast.UnaryOp:
		parameter=[]
		if statement.op=='*':
			stmt=defref2array(statement,pointer_list,array_list)
			if stmt is not None:
				return stmt
			else:
				return statement
		elif statement.op=='&' and statement.expr.name in pointer_list:
			parameter.append(statement.expr)
			return c_ast.FuncCall(name=c_ast.ID(name='_address'), args=c_ast.ExprList(exprs=parameter))
		else:
			return c_ast.UnaryOp(op=statement.op, expr=defref2function(statement.expr,pointer_list,array_list))
	elif type(statement) is c_ast.BinaryOp:
		return c_ast.BinaryOp(op=statement.op,left=defref2function(statement.left,pointer_list,array_list),right=defref2function(statement.right,pointer_list,array_list))
	else:
		return statement





		
		
def ref2function(statement):
	if type(statement) is c_ast.UnaryOp:
		parameter=[]
		if statement.op=='&':
			parameter.append(statement.expr)
			return c_ast.FuncCall(name=c_ast.ID(name='_address'), args=c_ast.ExprList(exprs=parameter))
		else:
			return c_ast.UnaryOp(op=statement.op, expr=ref2function(statement.expr))
	elif type(statement) is c_ast.BinaryOp:
		return c_ast.BinaryOp(op=statement.op,left=ref2function(statement.left),right=ref2function(statement.right))
	else:
		return statement


def defref2array(statement,pointer_list,array_list):
	if statement.op=='*' and type(statement.expr) is c_ast.UnaryOp :
		stmt=defref2array(statement.expr,pointer_list,array_list)
		if stmt is not None:
			return c_ast.ArrayRef(name=stmt, subscript=c_ast.Constant(type='int', value='0'))
		else:
			return None
	elif statement.op=='*' and type(statement.expr) is c_ast.BinaryOp :
            if type(statement.expr.left) is c_ast.ID and type(statement.expr.right) is c_ast.UnaryOp:
                stmt=defref2array(statement.expr.right,pointer_list,array_list)
                if stmt is not None:
			return c_ast.ArrayRef(name=stmt, subscript=statement.expr.left)
		else:
			return None
            elif type(statement.expr.right) is c_ast.ID and type(statement.expr.left) is c_ast.UnaryOp:
                stmt=defref2array(statement.expr.left,pointer_list,array_list)
                if stmt is not None:
			return c_ast.ArrayRef(name=stmt, subscript=statement.expr.right)
		else:
			return None
            elif type(statement.expr.left) is c_ast.Constant and type(statement.expr.right) is c_ast.UnaryOp:
                stmt=defref2array(statement.expr.right,pointer_list,array_list)
                if stmt is not None:
			return c_ast.ArrayRef(name=stmt, subscript=statement.expr.left)
		else:
			return None
            elif type(statement.expr.right) is c_ast.Constant and type(statement.expr.left) is c_ast.UnaryOp:
                stmt=defref2array(statement.expr.left,pointer_list,array_list)
                if stmt is not None:
			return c_ast.ArrayRef(name=stmt, subscript=statement.expr.right)
		else:
			return None
            elif type(statement.expr.left) is c_ast.ID and type(statement.expr.right) is c_ast.ID and statement.expr.right.name in pointer_list:
                return c_ast.ArrayRef(name=statement.expr.right, subscript=statement.expr.left)
            elif type(statement.expr.right) is c_ast.ID and type(statement.expr.left) is c_ast.ID and statement.expr.left.name in pointer_list:
                return c_ast.ArrayRef(name=statement.expr.left, subscript=statement.expr.right)
            elif type(statement.expr.left) is c_ast.ID and type(statement.expr.right) is c_ast.ID and statement.expr.right.name in array_list:
                return c_ast.ArrayRef(name=statement.expr.right, subscript=statement.expr.left)
            elif type(statement.expr.right) is c_ast.ID and type(statement.expr.left) is c_ast.ID and statement.expr.left.name in array_list:
                return c_ast.ArrayRef(name=statement.expr.left, subscript=statement.expr.right)
            #if type(statement.expr.left) is c_ast.ID and statement.expr.left.name in pointer_list:
             #   return c_ast.ArrayRef(name=stmt, subscript=statement.expr.right)
            #elif type(statement.expr.left) is c_ast.ID and statement.expr.left.name in array_list:
             #   return c_ast.ArrayRef(name=stmt, subscript=statement.expr.right)
            #if type(statement.expr.right) is c_ast.ID and statement.expr.right.name in pointer_list:
             #   return c_ast.ArrayRef(name=stmt, subscript=statement.expr.left)
            #elif type(statement.expr.right) is c_ast.ID and statement.expr.right.name in array_list:
             #   return c_ast.ArrayRef(name=stmt, subscript=statement.expr.left)
	elif statement.op=='*' and statement.expr.name in pointer_list:
		return c_ast.ArrayRef(name=statement.expr, subscript=c_ast.Constant(type='int', value='0'))
	elif statement.op=='*' and statement.expr.name in array_list:
		return c_ast.ArrayRef(name=statement.expr, subscript=c_ast.Constant(type='int', value='0'))
	
	else:
		return None


def getAssertAssume(f,o,a,cm):
	new_o={}
	new_a=[]
	new_f={}
	assert_list=[]
	assume_list=[]
        key_value=None
        assert_key_map={}
	for x in f:
		if x.find('_PROVE')<0 and x.find('_ASSUME')<0:
			new_f[x]=f[x]
	for x in o:
		if x.find('_PROVE')>0:
                        key_value=x
                        if key_value is not None:
                            assert_key_map[key_value]=o[x]
        		assert_list.append(o[x])
                elif x.find('_ASSUME')>0:
                        if o[x][-1][0]=='ite':
                            if o[x][-1][-1]==['0']:
                                new_e=eval("['implies',"+str(o[x][-1][1])+","+str(o[x][-1][2])+"]")
                                o[x][-1]=new_e

        		assume_list.append(o[x])
                elif x.find('_FAILED')>0:
                    #assert_list.append(o[x])

                    key_value=x
                    new_assert=[]
                    arg_list=expr_args(o[x][1])
                    if len(arg_list)>0:
                        new_assert.append('R')
                        parameterlist=[]
                        for para in arg_list:
                            parameterlist.append(para[0])
                        new_assert.append(parameterlist)
                        new_assert.append(o[x][1])
                        new_assert.append('0')
                        assert_list.append(new_assert)
                        if key_value is not None:
                            assert_key_map[key_value]=new_assert
                    else:
                        new_assert.append('c1')
                        new_assert.append(['==',o[x][1],['0']])
                        assert_list.append(new_assert)
                        if key_value is not None:
                            assert_key_map[key_value]=new_assert
                    new_o[x]=o[x]
        	else:
        		new_o[x]=o[x]
        
        update_new_a=[]
        for x in a:
                if x[0]=='i1':
                    if x[3][0].find('array')>0:
                        map_var={}
                        getAll_PROVE_ASSUME(x[4],map_var)
                        if len(map_var.keys())>0:
                            for e_array in map_var.keys():
                                new_e1 = copy.deepcopy(x)
                                var_array=eval("['"+e_array+"']")
                                var_e1=eval("['_x1']")
                                new_e1[3]=expr_replace(new_e1[3],var_e1,var_array)
                                new_e1[4]=expr_replace(new_e1[4],var_e1,var_array)
                                new_e1[4]=simplify_ind_equation(new_e1[4],map_var.keys())
                                update_new_a.append(new_e1)
                            x[4]=x[4][3]
                            x[4]=getEndElse(x[4])
                            update_new_a.append(x)
                        else:
                            update_new_a.append(x)
                    else:
                        if x[3][1][0]=='_s1':
                            map_var={}
                            getAll_PROVE_ASSUME(x[4],map_var)
                            x[4]=simplify_ind_equation(x[4],map_var.keys())
                            update_new_a.append(x) 
                        else:
                            update_new_a.append(x) 
                else:
                   update_new_a.append(x) 
        
        
        
        
        
        
        
        #for x in a:
        
        for x in update_new_a:
        	if x[0]=='i1':
        		if x[3][0].find('array')>0:
        			if '_PROVE' in expr2string1(x[4]):
                                        key_value=x[3][1][0]
                                        
                                        #new_word,const_var=getPrimeAssert(a,cm,x[2],cm[x[2]])
                                        new_word,const_var=getPrimeAssert(update_new_a,cm,x[2],cm[x[2]])

                                        if new_word is not None and const_var is not None:
                                            new_word=copy.deepcopy(new_word)
                                            new_word[-1]=eval("['"+const_var+"']")
                                        #list_conditin=getConditions(o,a,new_word)

                                        list_conditin=getConditions(o,update_new_a,new_word)
                                        print 
                                        con_stmt=None
                                        if list_conditin is not None:
                                            con_stmt=constructAndOrlist(list_conditin,'and')
                                        new_x = copy.deepcopy(x)
                                        #print '----------------------'
                                        #print expr2string1(x[4])
                                        #print '----------------------'
                                        x[4]=assert_filter1(x[4])
                                        var_e1=eval("['_x1']")
                                        x[3][1]=var_e1
                                        x[4]=assert_filter(x[4],x[3],new_word,cm)
                                        #x[4][2]=assert_filter(x[4][2],x[3],new_word,cm)  
                                        if  con_stmt is not None:
                                            new_stmt=[]
                                            new_stmt.append('implies')
                                            new_stmt.append(con_stmt)
                                            #new_stmt.append(x[4][2])
                                            #print '----------------------'
                                            #print expr2string1(con_stmt)
                                            #print expr2string1(x[4])
                                            #print '----------------------'
                                            new_stmt.append(x[4])
                                            #x[4][2]=new_stmt
                                            x[4]=new_stmt
        				assert_list.append(x)
                                        if key_value is not None:
                                            assert_key_map[key_value]=x
        				new_w = copy.deepcopy(new_x)
        				new_w[4]=copy.deepcopy(new_x[4][3])
                                        #new_w[4]=copy.deepcopy(x[4])
        				#new_a.append(new_w)
        			elif '_ASSUME' in expr2string1(x[4]):
                                        #new_word,const_var=getPrimeAssert(a,cm,x[2],cm[x[2]])
                                        
                                        print '--------==============='
                                        print x[4]
                                        print '--------==============='
                                        
                                        new_word,const_var=getPrimeAssert(update_new_a,cm,x[2],cm[x[2]])
                                        if new_word is not None and const_var is not None:
                                            new_word=copy.deepcopy(new_word)
                                            new_word[-1]=eval("['"+const_var+"']")
                                        #list_conditin=getConditions(o,a,new_word)
                                        list_conditin=getConditions(o,update_new_a,new_word)
                                        con_stmt=None
                                        if list_conditin is not None:
                                            con_stmt=constructAndOrlist(list_conditin,'and')
                                        new_x = copy.deepcopy(x)
                                        x[4]=assert_filter1(x[4])
                                        var_e1=eval("['_x1']")
                                        x[3][1]=var_e1
                                        x[4]=assert_filter(x[4],x[3],new_word,cm)
                                        #x[4][2]=assert_filter(x[4][2],x[3],new_word,cm)  
                                        if  con_stmt is not None:
                                            new_stmt=[]
                                            new_stmt.append('implies')
                                            new_stmt.append(con_stmt)
                                            #new_stmt.append(x[4][2])
                                            new_stmt.append(x[4])
                                            #x[4][2]=new_stmt
                                            x[4]=new_stmt
        				assume_list.append(x)
        				new_w = copy.deepcopy(new_x)
        				new_w[4]=copy.deepcopy(new_x[4][3])
                                        #new_w[4]=copy.deepcopy(x[4])
        				#new_a.append(new_w)
        			else:
        				new_a.append(x)
        		
        		elif x[3][0].find('_PROVE')>0:
        			#for var in cm.keys():
        			#	x[4]=expr_sub(x[4],cm[var],var)
                                if x[4][0].find('_PROVE')<0:
                                    assert_list.append(x)
        		elif x[3][0].find('_ASSUME')>0:
                                print '--------===============2'
                                print x[4]
                                print '--------===============2'

                                assume_list.append(x)
        		else:
        			new_a.append(x)
        	elif x[0]=='i0':
        		if x[2][0].find('_PROVE')>0:
                                if x[3][0].find('_PROVE')<0:
                                    assert_list.append(x)
        		elif x[2][0].find('_ASSUME')>0:
                                print '--------===============3'
                                print x[4]
                                print '--------===============3'

                                assume_list.append(x)
        		else:
        			new_a.append(x)
        	else:
			new_a.append(x)
        return new_f,new_o,new_a,extractAssert(assert_list,cm),extractAssume(assume_list,cm),extractAssertMap(assert_key_map,cm)
        

def getPrimeAssert(a,cm,var,constant):
    pime_eq=None
    constant_var=None
    for x in a:
        if x[0]=='i1':
            if x[3][0].find('array')>0:
                if x[2]==var:
                    pime_eq=x[3]
                    constant_var=cm[x[2]]
                else :
                    if x[2] in constant:
                        pime_eq=x[3]
                        constant_var=cm[x[2]]
    return pime_eq,constant_var
            




        
def extractAssert(assert_list,cm):
	update_assert_stmts=[]
	for stmt in assert_list:
		if stmt[0]=='e':
			update_stmt=[]
			update_stmt.append('s0')
			update_stmt.append(stmt[2])
			key=wff2string1(update_stmt)
			for iteam in cm:
				key=key.replace(cm[iteam],iteam+'+1')
			flag=False
			for temp_stmt in assert_list:
				if temp_stmt[0]=='i1':
					lefthandstmt=expr2string1(temp_stmt[3])
					if 'and' not in str(key) and 'or' not in str(key):
						if simplify(key)==simplify(lefthandstmt):
							flag=True
			if flag==False:
				if update_stmt[0]=='s0':
					temp=expr2string1(update_stmt[1])
					if '_PROVE' not in temp:
						if '<' in temp or '>' in temp or '=' in temp:
							update_assert_stmts.append(update_stmt)
				else:
					update_assert_stmts.append(update_stmt)
		else:
			if stmt[0]=='s0':
				temp=expr2string1(stmt[1])
				if '<' in temp or '>' in temp or '=' in temp:
					update_assert_stmts.append(stmt)
			else:
				if stmt[0]=='i1':
					stmt_assert=[]
					stmt_assert.append('c1')
					#stmt_assert.append(stmt[4][2])
                                        if stmt[4][0]=='ite':
                                            stmt[4] = assert_filter1(stmt[4])
                                        stmt_assert.append(stmt[4])
					update_assert_stmts.append(stmt_assert)
				else:
					update_assert_stmts.append(stmt)
			
	return update_assert_stmts
    

def extractAssertMap(assert_list_map,cm):
	update_assert_stmts_map={}
	for key_val in assert_list_map.keys():
                stmt=assert_list_map[key_val]
		if stmt[0]=='e':
			update_stmt=[]
			update_stmt.append('s0')
			update_stmt.append(stmt[2])
			key=wff2string1(update_stmt)
			for iteam in cm:
				key=key.replace(cm[iteam],iteam+'+1')
			flag=False
			for temp_stmt in assert_list_map.keys():
				if temp_stmt[0]=='i1':
					lefthandstmt=expr2string1(temp_stmt[3])
					if 'and' not in str(key) and 'or' not in str(key):
						if simplify(key)==simplify(lefthandstmt):
							flag=True
			if flag==False:
				if update_stmt[0]=='s0':
					temp=expr2string1(update_stmt[1])
					if '_PROVE' not in temp:
						if '<' in temp or '>' in temp or '=' in temp:
							update_assert_stmts_map[key_val]=update_stmt
				else:
					update_assert_stmts_map[key_val]=update_stmt
		else:
			if stmt[0]=='s0':
				temp=expr2string1(stmt[1])
				if '<' in temp or '>' in temp or '=' in temp:
					update_assert_stmts_map[key_val]=stmt
			else:
				if stmt[0]=='i1':
					stmt_assert=[]
					stmt_assert.append('c1')
					#stmt_assert.append(stmt[4][2])
                                        if stmt[4][0]=='ite':
                                            stmt[4] = assert_filter1(stmt[4])
                                        stmt_assert.append(stmt[4])
					update_assert_stmts_map[key_val]=stmt_assert
				else:
					update_assert_stmts_map[key_val]=stmt	
	return update_assert_stmts_map



def extractAssume(assume_list,cm):
	update_assume_stmts=[]
	for stmt in assume_list:
		if stmt[0]=='e':
			update_stmt=[]
			update_stmt.append('s0')
			update_stmt.append(stmt[2])
			key=wff2string1(update_stmt)
			for iteam in cm:
				key=key.replace(cm[iteam],iteam+'+1')
			flag=False
			for temp_stmt in assume_list:
				if temp_stmt[0]=='i1':
					lefthandstmt=expr2string1(temp_stmt[3])
					if 'and' not in str(key) and 'or' not in str(key):
						if simplify(key)==simplify(lefthandstmt):
							flag=True
			if flag==False:
				if update_stmt[0]=='s0':
					temp=expr2string1(update_stmt[1])
					if '_PROVE' not in temp:
						if '<' in temp or '>' in temp or '=' in temp:
							update_assume_stmts.append(update_stmt)
				else:
					update_assume_stmts.append(update_stmt)
		else:
			if stmt[0]=='s0':
				temp=expr2string1(stmt[1])
				if '<' in temp or '>' in temp or '=' in temp:
					update_assume_stmts.append(stmt)
			else:

				if stmt[0]=='i1':
					stmt_assume=[]
					stmt_assume.append('c1')
					#stmt_assert.append(stmt[4][2])
                                        stmt_assume.append(stmt[4])
					update_assume_stmts.append(stmt_assume)
				else:
					update_assume_stmts.append(stmt)
			
	return update_assume_stmts






	


def assert_filter1(e):
    if e[:1]==['ite']:
        arg_list=expr_args(e)
        #print '---------@@@@@@@@@@@@@@@1'
        #print arg_list[0]
        #print '---------@@@@@@@@@@@@@@@1'
        new_cond=conditionFilter(arg_list[0])
        #print '---------@@@@@@@@@@@@@@@2'
        #print new_cond
        #print '---------@@@@@@@@@@@@@@@2'
        if new_cond==None:
            return arg_list[1]
        else:
            new_stmt1=assert_filter1(arg_list[1])
            new_cond1=conditionFilter(arg_list[1])
            new_stmt2=assert_filter1(arg_list[2])
            new_cond2=conditionFilter(arg_list[2])
            if new_cond==None:
                return e
            else:
                if isArrayFunction(new_cond1[0])==True and '_PROVE' in new_cond1[1][0]:
                    if isArrayFunction(new_cond2[0])==True and '_PROVE' in new_cond2[1][0]:
                        return new_cond 
                    else:
                        new_stmt=[]
                        new_stmt.append('implies')
                        new_stmt.append(expr_complement(new_cond))
                        new_stmt.append(new_cond2)
                        return new_stmt
                else:
                    if '_PROVE' in new_cond1[0]:
                        new_stmt=[]
                        new_stmt.append('implies')
                        new_stmt.append(expr_complement(new_cond))
                        new_stmt.append(new_cond2)
                        return new_stmt
                    else:
                        new_stmt=[]
                        new_stmt.append('implies')
                        new_stmt.append(new_cond)
                        new_stmt.append(new_cond1)
                        return new_stmt
                
                



def getEndElse(e):
    if e[:1]==['ite']:
        arg_list=expr_args(e)
        if arg_list[2][:1]==['ite']:
            return getEndElse(arg_list[2])
        else:
            return arg_list[2]
    else:
        return e


def getAll_PROVE_ASSUME(e,map_var):
    arg_list=expr_args(e)
    op=expr_op(e)
    if len(arg_list)==0:
        if op.find('_PROVE')>0 or op.find('_ASSUME')>0:
            map_var[op]=op
    elif op=='ite':
        for x in arg_list:
            getAll_PROVE_ASSUME(x,map_var)
    elif op=='and':
        for x in arg_list:
            getAll_PROVE_ASSUME(x,map_var)
    else:
        for x in arg_list:
            getAll_PROVE_ASSUME(x,map_var)




def conditionFilter(e):
    if e[0]=='and':
        arg_list=expr_args(e)
        temp=[]
        for i in range(1,len(arg_list)):
            if conditionFilter(arg_list[i]) is not None:
                temp.append(arg_list[i])
        if len(temp)==0:
            return None
        elif len(temp)==1:
            return  temp[0]
        else:
            return e2[0]+temp
    elif e[0]=='=':
        if '_x1' in e[1][0]:
            return None
    elif e[0]=='ite':
        arg_list=expr_args(e)
        new_cond=conditionFilter(arg_list[1])
        if new_cond==None:
            return None
        else:
            return new_cond
    else:
        return e







def assert_filter(e,e1,e2,cm): #e,e1,e2: expr
	if isArrayFunction(e[:1][0])==True:
		if e1[0][1]==e[:1][0][1]:
			temp=[]
			count=0
                        arg_list=expr_args(e)
        		for x in expr_args(e2):
                            if count<len(expr_args(e2))-1:
                                temp.append(arg_list[count])
                            else:
                                temp.append(x)
                            count=count+1
			return e2[:1]+temp
		else:
			return e
	else:
		return e[:1]+list(assert_filter(x,e1,e2,cm) for x in expr_args(e))


def getConditions(o,a,e):
    for x in o:
        list_condition=[]
        get_conditions(o[x],e,list_condition)
        if len(list_condition) >0:
            return list_condition
    for x in a:
        if x[0]=='i0':
            list_condition=[]
            get_conditions(x[3],e,list_condition)
            if len(list_condition) >0:
                return list_condition
    return None

        
def get_conditions(e,e_el,list_condition):
        if e[:1]==['ite']:
        	temp=[]
        	count=0
        	cond=None
        	for x in expr_args(e):
                        get_conditions(x,e_el,list_condition)
        		if count==0:
        			cond=x
        		elif count==1:
        			if x==e_el and cond is not None:
                                    list_condition.append(cond) 
        		elif count==2:
                                if x==e_el and cond is not None:
                                    con=[]
                                    con.append('not')
                                    con.append(cond)
                                    list_condition.append(cond) 
        		count=count+1
        else:
        	for x in expr_args(e):
                    get_conditions(x,e_el,list_condition)       


def constructAndOrlist(e_array,operator):
	if len(e_array)>2:
                cond=[]
                cond.append(operator)
                cond.append(e_array[0])
                cond.append(constructAndOrlist(e_array[1:],operator))
		return cond
	if len(e_array)==2:
                cond=[]
                cond.append(operator)
                cond.append(e_array[0])
                cond.append(constructAndOrlist(e_array[1:],operator))
		return cond
	else:
		return e_array[0]

