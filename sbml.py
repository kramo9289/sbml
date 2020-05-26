#Kevin Ramos
#111019436

#References
#TTgrammer.py @author Professor Christopher Kane
#Lecture 07 @author Professor Christopher Kane
import sys

import ply.lex as lex

#A dictionary of variable names
var_names = {}
#Dictionary for functions
fun_names = {}
#stack array
stack = []

#AST NODES
class Node():
    def __init__(self):
        self.parent = None
        
    def eval(self):
        return 0
    
    def parentCount(self):
        count = 0
        current = self.parent
        while current is not None:
            count +=  1
            current = current.parent
        return count

class Binary(Node):
    def __init__(self, left, operator, right):
        super().__init__()
        self.left = left
        self.right = right
        self.left.parent = self
        self.right.parent = self
        self.operator = operator

    def evaluate(self):
        #Evaluate both sides first
        lefteval = self.left.evaluate()
        righteval = self.right.evaluate()


        #get the variable names
        if(type(self.left) == AST_varname and var_names.get(lefteval) != None):
           lefteval = var_names[lefteval]
        if(type(self.right) == AST_varname and var_names.get(righteval) != None):
           righteval = var_names[righteval]
        
        #Check the type of each side
        lefttype = type(lefteval)
        righttype = type(righteval)
        
        #Perform the evaluation and checking for semantics
        if(self.operator == "+" ):
            if(lefttype == str and righttype == str):
                return lefteval[0] + lefteval[1:-1] + righteval[1:-1] + lefteval[0]
            
            if(lefttype == float or lefttype == int):
                if(righttype == float or righttype == int):
                    return lefteval + righteval

            if(lefttype == list and righttype == list):
                return lefteval + righteval
        if(self.operator == "-" and (lefttype == int or lefttype == float) and (righttype == int or righttype == float)):
            return lefteval - righteval
        if(self.operator == "/" and (lefttype == int or lefttype == float) and (righttype == int or righttype == float) and righteval != 0):
            return lefteval/righteval
        if(self.operator == "*" and (lefttype == int or lefttype == float) and (righttype == int or righttype == float)):
            return lefteval * righteval
        if(self.operator == "div" and lefttype == int and righttype == int and righteval != 0):
            return lefteval // righteval
        if(self.operator == "mod" and lefttype == int and righttype == int and righteval != 0):
            return lefteval % righteval
        if(self.operator == "**" and (lefttype == int or lefttype == float) and (righttype == int or righttype == float)):
            return lefteval ** righteval
        if(self.operator == "andalso" and lefttype == bool and righttype == bool):
            return lefteval and righteval
        if(self.operator == "orelse" and lefttype == bool and righttype == bool):
            return lefteval or righteval
        if(self.operator == "<" and (lefttype == int or lefttype == str) and (righttype == int or righttype == str)):
            return lefteval < righteval
        if(self.operator == "<=" and (lefttype == int or lefttype == str) and (righttype == int or righttype == str)):
            return lefteval <= righteval
        if(self.operator == "==" and (lefttype == int or lefttype == str) and (righttype == int or righttype == str)):
            return lefteval == righteval
        if(self.operator == "<>" and (lefttype == int or lefttype == str) and (righttype == int or righttype == str)):
            return lefteval != righteval
        if(self.operator == ">=" and (lefttype == int or lefttype == str) and (righttype == int or righttype == str)):
            return lefteval >= righteval
        if(self.operator == ">" and (lefttype == int or lefttype == str) and (righttype == int or righttype == str)):
            return lefteval > righteval
        if(self.operator == "in" and lefttype == str and righttype == str):
            return lefteval in righteval
        if(self.operator == "in" and righttype == list):
            return lefteval in righteval
        if(self.operator == "::" and (lefttype == str or lefttype == int or lefttype == float or lefttype == bool or lefttype == tuple or lefttype == list) and righttype == list):
            return [lefteval] + righteval
        
        #If it reaches this point then there is a semantic error
        print("SEMANTIC ERROR")
        exit()
        
class Unary(Node):
    def __init__(self, operator, value):
        super().__init__()
        self.value = value
        self.operator = operator

    #Checks to see if the value is a bool/int/float and if the corresponding operator is correct, else it is a semantic error
    def evaluate(self):
        operator = self.operator
        value = self.value.evaluate()
        
        #get the variable names
        if(type(self.value) == AST_varname and var_names.get(value) != None):
           value = var_names[value]
        
        if(type(value) == bool and operator == 'not'):
            return not value
        if(type(value) == int and operator == '-'):
            return - value
        if(type(value) == float and operator == '-'):
            return - value

        #If it is not then it is a semantic error
        print("SEMANTIC ERROR")
        exit()

    
class Tuple(Node):
    def __init__(self, values):
        super().__init__()
        self.values = [values]
        
    def evaluate(self):
        if(len(tuple(self.values)) ==0):
            print("SYNTAX ERROR")
            exit()
        else:
            tupleeval = []
            for i in self.values:
                ieval = i.evaluate()
                if(type(i) == AST_varname and var_names.get(ieval) != None):
                   ieval = var_names[ieval]
                tupleeval.append(ieval)
            return tuple(tupleeval)


class TupleIndex(Node):
    def __init__(self, index, child):
        super().__init__()
        self.child = child
        self.child.parent = self
        self.index = index
        self.index.parent = self

    def evaluate(self):
        tupleeval = self.child.evaluate()
        indexeval = self.index.evaluate()

        if(type(self.child) == AST_varname and var_names.get(tupleeval) != None):
            tupleeval = var_names[tupleeval]
        if(type(self.index) == AST_varname and var_names.get(indexeval) != None):
            indexeval = var_names[indexeval]
                   
        if(type(indexeval) == int and type(tupleeval) == tuple):
            if(len(tupleeval) >= indexeval and indexeval >= 1):
                return tupleeval[indexeval-1]
        else:
            print("SEMANTIC ERROR")
            exit()

class List(Node):
    def __init__(self, values):
        super().__init__()
        if(values == None):
            self.values = []
        else:
            self.values = [values]

    def evaluate(self):
        listeval = []
        if(self.values == None):
            return listeval
        for i in self.values:
            ieval = i.evaluate()
            if(type(i) == AST_varname and var_names.get(ieval) != None):
                ieval = var_names[ieval]
            listeval.append(ieval)
        return listeval
    
class ListIndex(Node):
    def __init__(self, expr, index):
        super().__init__()
        self.expr = expr
        self.index = index
        
    def evaluate(self):
        indexeval = self.index.evaluate()
        expreval = self.expr.evaluate()
        exprtype = type(expreval)
        indextype = type(indexeval)

        if(type(self.expr) == AST_varname and var_names.get(expreval) != None):
            expreval = var_names[expreval]
            exprtype = type(expreval)
        if(type(self.index) == AST_varname and var_names.get(indexeval) != None):
            indexeval = var_names[indexeval]
            indextype = type(indexeval)

        if(exprtype == list or str):
            if(indextype == int):
                if(indexeval < len(expreval)):
                    return expreval[indexeval]

        print("SEMANTIC ERROR")
        exit()

            
class AST_True(Node):
    def __init__(self):
        super().__init__()
        self.value = True

    def evaluate(self):
        return self.value
    
class AST_False(Node):
    def __init__(self):
        super().__init__()
        self.value = False

    def evaluate(self):
        return self.value

class AST_int(Node):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def evaluate(self):
        return self.value

class AST_real(Node):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def evaluate(self):
        return self.value

class AST_String(Node):
    def __init__(self, value):
        super().__init__()
        self.value = value
    def evaluate(self):
        return self.value

class AST_varname(Node):
    def __init__(self, value):
        super().__init__()
        self.value = value
    def evaluate(self):
        return self.value

class AST_variable(Node):
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right

    def evaluate(self):
        lefteval = self.left.evaluate()
        righteval = self.right.evaluate()
        
        if(type(self.right) == AST_varname and var_names.get(righteval) != None):
            righteval = var_names[righteval]
        
        if(type(self.left) == AST_varname):
            var_names[lefteval] = righteval
            return righteval
        elif(type(self.left) == ListIndex and type(self.left.expr) == AST_varname):
            index = False
            if(type(self.left.index) == AST_varname):
                index = var_names[self.left.index.evaluate()]
            elif(type(self.left.index) == AST_int):
                index = self.left.index.evaluate()
            if(type(index) != int and type(righteval) != index):
                print("SEMANTIC ERROR")
                exit()
            else:
                expr =self.left.expr.evaluate()
                expr = var_names[expr]
                expr[index] = righteval
                return righteval
        else:
            print("SYNTAX ERROR")
            exit()
               

class AST_Block(Node):
    def __init__(self, statements):
        super().__init__()
        self.statement_list = statements
        
    def evaluate(self):
        if(self.statement_list != None):
            for statement in self.statement_list:
                statement.evaluate()

class AST_print(Node):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def evaluate(self):
        toPrint = self.value.evaluate()
        if(type(self.value) == AST_varname and var_names.get(toPrint) != None):
            toPrint = var_names[toPrint]
            print(toPrint)
        else:
            print(toPrint)

class AST_if(Node):
    def __init__(self, expr, block):
        super().__init__()
        self.expr = expr
        self.block = block

    def evaluate(self):
        boolean = self.expr.evaluate()
        if(type(self.expr) == AST_varname and var_names.get(boolean) != None):
            boolean = var_names[boolean]
        if(type(boolean) != bool):
            print("SEMANTIC ERROR")
            exit()
        if(boolean):
            return self.block.evaluate()
        
class AST_if_else(Node):
    def __init__(self, expr, block1, block2):
        super().__init__()
        self.expr = expr
        self.block1 = block1
        self.block2 = block2

    def evaluate(self):
        boolean = self.expr.evaluate()
        if(type(self.expr) == AST_varname and var_names.get(boolean) != None):
            boolean = var_names[boolean]
        if(type(boolean) != bool):
            print("SEMANTIC ERROR")
            exit()
        if(boolean):
            return self.block1.evaluate()
        else:
            return self.block2.evaluate()

class AST_while(Node):
    def __init__(self, expr, block):
        self.expr = expr
        self.block = block

    def evaluate(self):
        boolean = self.expr.evaluate()
        if(type(self.expr) == AST_varname and var_names.get(boolean) != None):
            boolean = var_names[boolean]
        if(type(boolean) != bool):
            print("SEMANTIC ERROR")
            exit()
        while(self.update_boolean()):
            self.block.evaluate()

    def update_boolean(self):
        boolean = self.expr.evaluate()
        if(type(self.expr) == AST_varname and var_names.get(boolean) != None):
            boolean = var_names[boolean]
        return boolean

class AST_program(Node):
    def __init__(self, functions, block):
        self.functions = functions 
        self.block = block

    def evaluate(self):
        if(self.functions != None):
            for fun in self.functions:
                fun_names[fun.function_name.evaluate()] = fun
            return self.block.evaluate()

class AST_function(Node):
    def __init__(self, function_name, arguments, block, to_return):
        self.function_name = function_name
        self.arguments = arguments
        self.block = block
        self.to_return = to_return

    def evaluate(self):
        self.block.evaluate()

class AST_function_call(Node):
    def __init__(self, function_name, arguments):
        self.function_name = function_name
        self.arguments = arguments

    def evaluate(self):
        #referenced before assignment
        global var_names
        global stack
        global fun_names
        #check if it is a name
        function = fun_names.get(self.function_name.evaluate())

        if(function == None):
            print("SEMANTIC ERROR")
            exit()

        #create a new referencing environment before evaluating the function block
        parameter_list = {}

        #check to see if the argument lengths are equal to eachother            
        if(len(self.arguments) != len(function.arguments)):
            print("SEMANTIC ERROR")
            exit()

        #checks all parameters and put everythign into name array after evaluating 
        for r in range(len(function.arguments)):
            argseval = self.arguments[r].evaluate()
            if(type(self.arguments[r]) == AST_varname and var_names.get(argseval) != None):
                argseval = var_names[argseval]
            parameter_list[function.arguments[r].evaluate()] = argseval
        
        #add the previous variable names to the stack
        stack.append(var_names)
        #set the variable names to the parameters so the function block can be evaluated with the correct variables
        var_names = {}
        for key in parameter_list:
            var_names[key] = parameter_list[key]
        #Evaluate the function block
        function.evaluate()
        #Evaluate the return variable
        to_return_eval = function.to_return.evaluate()
        if(type(function.to_return) == AST_varname and var_names.get(to_return_eval) != None):
                to_return_eval = var_names[to_return_eval]
        #set the reference enviornment to the one that was set before the function was called
        var_names = stack.pop()
        return to_return_eval
        

#Any keywords that arent strings
reserved = {
    'div' : 'DIV',
    'mod' : 'MOD',
    'in' : 'IN',
    'not' : 'NOT',
    'andalso' : 'ANDALSO',
    'orelse' : 'ORELSE',
    'True' : 'TRUE',
    'False' : 'FALSE',
    'while' : 'WHILE',
    'print' : 'PRINT',
    'if' : 'IF',
    'else' : 'ELSE',
    'fun' : 'FUN'
    }
    
#Tokens for the program to recognize
tokens = [   
    'INTEGER',
    'REAL',
    'STRING',
    'LPAREN',
    'RPAREN',
    'LBRACK',
    'RBRACK',
    'HASHINDEX',
    'EXPONENT',
    'MULTIPLICATION',
    'OVERLOAD_DIVISION',
    'PLUS',
    'MINUS',
    'CONS',
    'LESS_THAN',
    'LESS_EQUAL',
    'EQUAL',
    'NOT_EQUAL',
    'GREATER_THAN',
    'GREATER_EQUAL',
    'COMMA',
    'SEMI_COLON',
    'ASSIGNMENT',
    'LCURLY',
    'RCURLY',
    'VARIABLE'
] + list(reserved.values())

#Regex representation of the tokens for the program to recognize
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACK = r'\['
t_RBRACK = r'\]'
t_HASHINDEX = r'\#'
t_EXPONENT = r'\*\*'
t_MULTIPLICATION = r'\*'
t_OVERLOAD_DIVISION = r'\/'
t_PLUS = r'\+'
t_MINUS = r'-'
t_CONS = r'::'
t_LESS_THAN = r'<'
t_LESS_EQUAL = r'<='
t_EQUAL = r'=='
t_NOT_EQUAL = r'<>'
t_GREATER_THAN = r'>'
t_GREATER_EQUAL = r'>='
t_COMMA = r','
t_SEMI_COLON = r';'
t_ASSIGNMENT = r'='
t_LCURLY = r'{'
t_RCURLY = r'}'

#Real token function
def t_REAL(t):
    r'\d*(\d\.|\.\d)\d*(e*)(-?\d)*'
    try:
        t.value = float(t.value)
    except ValueError:
        print("Float value too large %d", t.value)
        t.value = 0
    return t

#Integer token function
def t_INTEGER(t):
    r'\d+'
    try:
        t.value = int(t.value)
    except ValueError:
        print("Integer value too large %d", t.value)
        t.value = 0
    return t

#String token function
def t_STRING(t):
    r'(\"[^\"]*\")|(\'[^\']*\')'
    return t

#Variable token function
def t_VARIABLE(t):
    r'[a-zA-Z][a-zA-Z0-9_]*'
    if t.value in reserved:
        t.type = reserved[t.value]
    return t   

#tokens to be ignored
t_ignore = " \t"

#TO CHANGE
def t_error(t):
    sys.stdout.write("SYNTAX ERROR")
    exit()

#Build lexer
lexer = lex.lex(debug = False)

#The following are SBML Operator Precendence
precedence = (('left', 'ORELSE'),
        ('left', 'ANDALSO'),
        ('left', 'NOT'),
        ('left', 'LESS_THAN', 'LESS_EQUAL', 'EQUAL', 'NOT_EQUAL', 'GREATER_THAN', 'GREATER_EQUAL'),
        ('right', 'CONS'),
        ('left', 'IN'),
        ('left', 'PLUS', 'MINUS'),
        ('left', 'MULTIPLICATION', 'OVERLOAD_DIVISION', 'DIV', 'MOD'),
        ('right', 'UMINUS'),
        ('right', 'EXPONENT'),
        ('left', 'LBRACK', 'RBRACK'),
        ('left', 'HASHINDEX'),
        ('left', 'LPAREN', 'RPAREN')
)

#The following are production functions
def p_inputs(p):
    'program : function_list block'
    p[0] = AST_program(p[1], p[2])

def p_inputs_only_blocks(p):
    'program : block'
    p[0] = AST_program(None, p[2])
    
def p_negation(p):
    '''expr : MINUS expr %prec UMINUS
            | NOT expr'''
    p[0] = Unary(p[1], p[2])
    
def p_binaryoperation(p):
    '''expr : expr PLUS expr
            | expr MINUS expr
            | expr OVERLOAD_DIVISION expr
            | expr MULTIPLICATION expr
            | expr DIV expr
            | expr MOD expr
            | expr EXPONENT expr
            | expr ANDALSO expr
            | expr ORELSE expr
            | expr LESS_THAN expr
            | expr LESS_EQUAL expr
            | expr EQUAL expr
            | expr NOT_EQUAL expr
            | expr GREATER_EQUAL expr
            | expr GREATER_THAN expr
            | expr IN expr
            | expr CONS expr'''
    p[0] = Binary(p[1], p[2], p[3])


def p_paren(p):
    'expr : LPAREN expr RPAREN'
    p[0] = p[2]
            
def p_list(p):
    'expr : LBRACK listelements RBRACK'
    p[0] = p[2]

def p_emptylist(p):
    'expr : LBRACK RBRACK'
    p[0] = List(None)

def p_listelements(p):
    'listelements : listelements COMMA expr'
    p[1].values.append(p[3])
    p[0] = p[1]

def p_endlistelements(p):
    'listelements : expr'
    p[0] = List(p[1])

def p_listindex(p):
    'expr : expr LBRACK expr RBRACK'
    p[0] = ListIndex(p[1], p[3])

def p_tuple(p):
    '''expr : LPAREN tupleelements RPAREN
            | LPAREN tupleelements COMMA RPAREN'''
    p[0] = p[2]

def p_tupleelements(p):
    'tupleelements : tupleelements COMMA expr'
    p[1].values.append(p[3])
    p[0] = p[1]

def p_endtupleelements(p):
    'tupleelements : expr'
    p[0] = Tuple(p[1])

def p_tupleindex(p):
    'expr : HASHINDEX expr expr'
    p[0] = TupleIndex(p[2], p[3])

def p_item(p):
    'expr : item'
    p[0] = p[1]
    
def p_string(p):
    'item : STRING'
    p[0] = AST_String(p[1])

def p_true(p):
    'item : TRUE'
    p[0] = AST_True()

def p_false(p):
    'item : FALSE'
    p[0] = AST_False()

def p_int(p):
    'item : INTEGER'
    p[0] = AST_int(p[1])

def p_real(p):
    'item : REAL'
    p[0] = AST_real(p[1])

def p_variable(p):
    'item : VARIABLE'
    p[0] = AST_varname(p[1])

def p_function_call(p):
    'item : expr LPAREN argument_list RPAREN'
    p[0] = AST_function_call(p[1], p[3])

def p_block(p):
    'block : LCURLY statement_list RCURLY'
    p[0] = AST_Block(p[2])
    
def p_empty_block(p):
    'block : LCURLY RCURLY'
    p[0] = AST_Block(None)
    
def p_statement_list(p):
    'statement_list : statement_list statement'
    p[0] = p[1] + [p[2]]

def p_statement_list_end(p):
    'statement_list : statement'
    p[0] = [p[1]]

def p_statement(p):
    '''statement : expr SEMI_COLON
                | assignment_statement SEMI_COLON
                | print_statement SEMI_COLON
                | if_statement 
                | if_else_statement
                | while_statement
                | block'''
    p[0] = p[1]

def p_function_list(p):
    'function_list : function_list function'
    p[0] = p[1] + [p[2]]

def p_function_list_end(p):
    'function_list : function'
    p[0] = [p[1]]

def p_function(p):
    'function : FUN expr LPAREN argument_list RPAREN ASSIGNMENT block expr SEMI_COLON'
    p[0] = AST_function(p[2], p[4], p[7], p[8])

def p_argument_list(p):
    'argument_list : argument_list COMMA expr'
    p[0] = p[1] + [p[3]]

def p_argument_list_end(p):
    'argument_list : expr'
    p[0] = [p[1]]

def p_assignment_statement(p):
    'assignment_statement : expr ASSIGNMENT expr'
    p[0] = AST_variable(p[1], p[3])

def p_print_statement(p):
    'print_statement : PRINT LPAREN expr RPAREN'
    p[0] =  AST_print(p[3])

def p_if_statement(p):
    'if_statement : IF LPAREN expr RPAREN block'
    p[0] = AST_if(p[3], p[5])

def p_if_else_statement(p):
    'if_else_statement : IF LPAREN expr RPAREN block ELSE block'
    p[0] = AST_if_else(p[3], p[5], p[7])
    
def p_while_statement(p):
    'while_statement : WHILE LPAREN expr RPAREN block'
    p[0] = AST_while(p[3], p[5])

def p_error(p):
    print("SYNTAX ERROR")
    exit()

def tokenize(inp):
    lexer.input(inp)
    while True:
        tok = lexer.token()
        if not tok:
            break
        print(tok)

import ply.yacc as yacc
parser = yacc.yacc(debug = False)

def  parse(inp):
    result = parser.parse(inp, debug = 0)
    return result

def main():
    '''
    while True:
        inp = input("Enter an expression: ")
        result = parse(inp)
        if result is not None and result.evaluate() is not None:
            print(result.evaluate())
    '''
    f = open(sys.argv[1],'r')
    lines = f.read().replace('\n', '')
    result = parse(lines)
    result.evaluate()
    f.close()
    '''
    f = open(sys.argv[1],'r')
    lines = f.read().replace('\n', '')
    print(lines)
    '''
if __name__ == "__main__":
    main()
