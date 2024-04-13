from AST import *
from Visitor import *
from Utils import Utils
from StaticError import *
from functools import reduce
from abc import ABC,abstractmethod,ABCMeta


class Type(ABC):
    __metaclass__ = ABCMeta
    pass

class ScalarType(Type):
    __metaclass__ = ABCMeta

class NumberType(ScalarType):
    def __init__(self):
        return
    def __repr__(self):
        return "Number"

class StringType(ScalarType):
    def __init__(self):
        return
    def __repr__(self):
        return "String"

class BoolType(ScalarType):
    def __init__(self):
        return
    def __repr__(self):
        return "Boolean"

class VoidType(ScalarType):
    def __init__(self):
        return
    def __repr__(self):
        return "Void"



class NoType(Type):
    def __init__(self):
        return
    def __repr__(self):
        return "NoType"


class Symbol:
    pass

class VarSymbol(Symbol):
    def __init__(self, name, type):
        self.name = name
        self.type = type

class FuncSymbol(Symbol):
    def __init__(self, name, param, returnType):
        self.name = name
        self.param = param
        self.returnType = returnType

class StaticChecker(BaseVisitor, Utils):
    def __init__(self,ast):
        self.ast = ast
        self.global_env = [[
            FuncSymbol("readNumber",[],NumberType()),
            FuncSymbol("writeNumber",[VarSymbol("",NumberType())],VoidType()),
            FuncSymbol("readBool",[],BoolType()),
            FuncSymbol("writeBool",[VarSymbol("",BoolType())],VoidType()),
            FuncSymbol("readString",[],StringType()),
            FuncSymbol("writeString",[VarSymbol("",StringType())],VoidType()),
        ]]
    
    def check(self):
        self.visit(self.ast, self.global_env)
    
    def checkNoEntryPoint(self,o):
        for symbol in o:
            for subsymbol in symbol:
                if type(subsymbol) is FunctionSymbol and subsymbol.name == 'main':
                    return
        raise NoEntryPoint()
    
    def visitStringLiteral(self,ast:StringLiteral,o):
        


        
        
