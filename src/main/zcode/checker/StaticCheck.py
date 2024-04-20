from AST import *
from Visitor import *
from Utils import Utils
from StaticError import *
from functools import reduce
from abc import ABC,abstractmethod,ABCMeta
from typing import List


class NoType(Type):
    def __init__(self):
        return
    def __repr__(self):
        return "NoType"



        
        


class Symbol:
    pass

class VarSymbol(Symbol):
    def __init__(self, name:str, type:Type):
        self.name = name
        self.type = type

class FuncSymbol(Symbol):
    def __init__(self, name:str, param:List[VarSymbol], returnType:Type,body: Stmt):
        self.name = name
        self.param = param
        self.returnType = returnType
        self.body = body

class StaticChecker(BaseVisitor, Utils):
    def __init__(self,ast):
        self.ast = ast
        self.nameVarDeclaring = None
        self.temp_list_ast = []
        self.prototypeFunction = []
        self.canInfer = True
        self.global_env = [[
            FuncSymbol("readNumber",[],NumberType()),
            FuncSymbol("writeNumber",[VarSymbol("",NumberType())],VoidType()),
            FuncSymbol("readBool",[],BoolType()),
            FuncSymbol("writeBool",[VarSymbol("",BoolType())],VoidType()),
            FuncSymbol("readString",[],StringType()),
            FuncSymbol("writeString",[VarSymbol("",StringType())],VoidType()),
        ]]
        # infer function
        def infer(self,expr: Id | CallExpr | CallStmt | ArrayLiteral, typ:Type, o):
            if type(expr) is Id:
                for symbol in o:
                    for subSymbol in symbol:
                        if type(subSymbol) is VarSymbol and subSymbol.name == expr.name:
                            subSymbol.type = typ
                            return typ
                raise Undeclared(Identifier(),expr.name)
            elif type(expr) in [CallStmt,CallExpr]:
                for symbol in o:
                    for subSymbol in symbol:
                        if type(subSymbol) is FuncSymbol and subSymbol.name == expr.name:
                            subSymbol.returnType = typ
                            return typ
                raise Undeclared(Function(),expr.name) 
            else:
                if type(typ) is not ArrayType:
                    self.canInfer = False
                else:
                    for exp in expr.value:
                        self.infer(exp, typ.eleType if len(typ.size) ==1 else ArrayType(typ.size[1:],typ.eleType),o)
            
                 
    
    def check(self):
        self.visit(self.ast, self.global_env)

    
    def visitStringLiteral(self, ast:StringLiteral,o):
        return StringType()

    def visitBooleanLiteral(self, ast:BooleanLiteral,o):
        return BoolType()

    def visitNumberLiteral(self, ast:NumberLiteral,o):
        return NumberType()

    def visitStringType(self, ast:StringType,o):
        return StringType()

    def visitBooleanType(self, ast:BoolType,o):
        return BoolType()

    def visitNumberType(self, ast:NumberType,o):
        return NumberType() 
    # return type of Id ,if not have type return NoType()
    def visitId(self, ast:Id, o):
        if self.nameVarDeclaring is not None and ast.name == self.nameVarDeclaring:
            raise Undeclared(Identifier(),ast.name)
        for sym in o:
            for subSym in sym:
                    if subSym.name == ast.name and type(subSym) is VarSymbol:
                        return subSym.typ
        raise Undeclared(Identifier(),ast.name)
    
    def visitUnaryOp(self, ast:UnaryOp,o):
        operandType = self.visit(ast.operand,o)
        if ast.op in ['-']:
            if type(operandType) is NoType:
                if type(ast.operand) in [Id, CallExpr]:
                    operandType = self.infer(ast.operand,NumberType(),o)
            if type(operandType) is NumberType:
                return NumberType()
            raise TypeMismatchInExpression(ast)
        
        if ast.op in ['not']:
            if type(operandType) is NoType:
                if type(ast.operand) in [Id, CallExpr]:
                    operandType = self.infer(ast.operand,BoolType(),o)
            if type(operandType) is BoolType:
                return BoolType()
            raise TypeMismatchInExpression(ast)
            
    def visitBinaryOp(self, ast:BinaryOp, o):
        leftType = self.visit(ast.left,o)
        rightType = self.visit(ast.right,o)
        if ast.op in ['+','-','*','/','%']:
            if type(leftType) is NoType:
                if type(ast.left) in [Id, CallExpr]:
                    leftType = self.infer(ast.left,NumberType(),o)
            if type(rightType) is NoType:
                if type(ast.right) in [Id, CallExpr]:
                    rightType = self.infer(ast.right,NumberType(),o)

            if type(leftType) is NumberType and type(rightType) is NumberType:
                return NumberType()
            raise TypeMismatchInExpression(ast)
        
        if ast.op in ['=','!=','<','>','<=','>=']:
            if type(leftType) is NoType:
                if type(ast.left) in [Id, CallExpr]:
                    leftType = self.infer(ast.left,NumberType(),o)
                    
            if type(rightType) is NoType:
                if type(ast.right) is [Id, CallExpr]:
                    rightType = self.infer(ast.right,NumberType(),o)

            if type(leftType) is NumberType and type(rightType) is NumberType:
                return BoolType()
            raise TypeMismatchInExpression(ast)

        if ast.op in ['or','and']:
            if type(leftType) is NoType:
                if type(ast.left) in [Id, CallExpr]:
                    leftType = self.infer(ast.left,BoolType(),o)
                
            if type(rightType) is NoType:
                if type(ast.right) in [Id, CallExpr]:
                    rightType = self.infer(ast.right,BoolType(),o)
            
            if type(leftType) is BoolType and type(rightType) is BoolType:
                return BoolType()
            raise TypeMismatchInExpression(ast)
        
        if ast.op in ['...']:
            if type(leftType) is NoType:
                if type(ast.left) in [Id, CallExpr]:
                    leftType = self.infer(ast.left,StringType(),o)                    
            if type(rightType) is NoType:
                if type(ast.right) in [Id, CallExpr]:
                    rightType = self.infer(ast.right,StringType(), o)

            if type(leftType) is StringType and type(rightType) is StringType:
                return StringType()
            raise TypeMismatchInExpression(ast)
    def visitArrayCell(self, ast: ArrayCell, o):
        nType = self.visit(ast.arr,o)
        if type (nType) is NoType:
            return NoType()
        else:
            if type (nType) is not ArrayType:
                raise TypeMismatchInExpression(ast)
            else:
                if len(nType.size) < len(ast.idx):
                    raise TypeMismatchInExpression(ast)
                else:
                    for exp in ast.idx:
                        expType =  self.visit(exp,o)
                        if type(expType) is NoType:
                            if type(exp) in [Id, CallExpr]:
                                if type(exp) is Id:
                                    expType = self.infer(exp,NumberType(),o)
                                else:
                                    expType = self.infer(exp,NumberType(),o)
                            return NoType()
                        if type(expType) is not NumberType:
                            raise TypeMismatchInExpression(ast)
                    if len (nType.size) == len(ast.idx):
                        return nType.eleType
                    return ArrayType(nType.size[len(ast.idx):] ,nType.eleType) 
                                    
    def visitArrayLiteral(self, ast:ArrayLiteral,o):
        if ast not in self.temp_list_ast:
            self.temp_list_ast += [ast]
        # find the first expr have type in [Expr]    
        tmpType = NoType()
        for exp in ast.value:
            tmpType = self.visit(exp,o)
            if type(tmpType) is  NoType:
                pass
            else: 
                break
        # after loop through [Expr]
            
        if type(tmpType) is not NoType:
            for expr in ast.value:
                exprType = self.visit(expr,o)
                if type(exprType) is NoType:
                    if type(expr) in [Id, CallExpr, ArrayLiteral]:
                        self.infer(expr,tmpType,o)
                        if self.canInfer: 
                            exprType = tmpType
                        else:
                            return NoType()
        
                    else:
                        return NoType()
                if type(exprType) is not type(tmpType):
                        raise TypeMismatchInExpression(self.temp_list_ast[0])
                else:
                    if type(exprType) is ArrayType:
                        if exprType.size[:len(tmpType.size)] != tmpType.size:
                            raise TypeMismatchInExpression(self.temp_list_ast[0])
                        else:
                            if type(exprType.eleType) is NoType:
                                if type(ast.value) in [Id, CallExpr, ArrayLiteral]:
                                    self.infer(ast.value,tmpType,o)
                                    if self.canInfer: 
                                         exprType = tmpType
                                    else:
                                        return NoType()
                                else:
                                    return NoType()
                            
                            if type(exprType.eleType) is not type(tmpType.eleType) or exprType.size != tmpType.size:
                                raise TypeMismatchInExpression(self.temp_list_ast[0])
        
            self.temp_list_ast = self.temp_list_ast[0:-1]
            if type(tmpType) is not ArrayType:
                return ArrayType([len(ast.value)],tmpType)  
            else:
                return ArrayType([len(ast.value)] + tmpType.size,tmpType.eleType)  
                                                             
        else:
            return NoType()
        
    def visitProgram(self, ast:Program,o):
        haveEntryPoint = False
        for decl in ast.decl:
            self.visit(decl,o)
        
        for decl in o[-1]:
            if type(decl) is FuncSymbol and type(decl.returnType) is VoidType and decl.param == []:
                haveEntryPoint = True
                break
        
        if not haveEntryPoint:
            raise NoEntryPoint()
        
        if self.prototypeFunction != []:
            raise NoDefinition(self.prototypeFunction[0])

    def visitVarDecl(self,ast:VarDecl,o):
        #check redeclare
        for sym in o[0]:
            for subSym in sym:
                if type(subSym) is VarSymbol and subSym.name is ast.name:
                    raise Redeclared(Variable(),ast.name.name)
        
        self.nameVarDeclaring = ast.name.name
        
        
        
        if ast.varInit is not None and ast.varType is not None: # both left and right have type
            rightType = self.visit(ast.varInit) # type of initValue
            leftType = ast.varType
            
            if type(rightType) is NoType:
                if type(ast.varInit) in [Id, CallExpr, ArrayLiteral]:
                    self.infer(ast.varInit,leftType,o)
                    if self.canInfer:
                        rightType = leftType
                    else:
                        return NoType()
                else:
                    return NoType()
            
            if type(rightType) is not type (leftType): # left and right difference type => Raise error            
                raise TypeMismatchInStatement(ast)
            else: # same type
                if type(rightType) is ArrayType:
                    if leftType.size[:len(rightType.size)] != rightType.size:
                        raise TypeMismatchInStatement(ast)
                    else:
                        if rightType.eleType is NoType:
                            self.infer(ast.varInit,leftType,o)
                            if not self.canInfer:
                                raise TypeCannotBeInferred(ast)
                            o[0] += [VarSymbol(ast.name.name, leftType)]
                        else:
                            if type(rightType.eleType) is not type(leftType.eleType):
                                raise TypeMismatchInStatement(ast)
                o[0] += [VarSymbol(ast.name.name,leftType)]
        elif ast.varInit is None and type(ast.varType) is NoType():
                o[0] += [VarSymbol(ast.name.name, NoType())]
                
        elif ast.varInit is None:
            if type(leftType) is NoType:
                o[0] += [VarSymbol(ast.name.name, NoType())]            
            else: 
                o[0] += [VarSymbol(ast.name.name,leftType)]
        else:
            if type(rightType) is NoType:
                raise TypeCannotBeInferred(ast)
            else:
                o[0] += [VarSymbol(ast.name.name, rightType)]
                
    def visitFuncDecl(self, ast:FuncDecl, o):
        pass