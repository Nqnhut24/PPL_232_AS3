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
        self.contain_return = False
        self.tmp_return_type = None
        self.canInfer = True
        self.tmp_return_list = []
        self.inLoop = []
        self.current_funcName = None
        
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
                
        self.nameVarDeclaring = None
                
    def visitFuncDecl(self, ast:FuncDecl, o):    
    # name: Id
    # param: List[VarDecl]  # empty list if there is no parameter
    # body: Stmt = None  # None if this is just a declaration-part

        
        funcName = ast.name.name # name of function
        self.current_funcName = funcName
        
        if ast.body is None: #only declare part
            for decl in o[0]:
                if type(decl) is FuncSymbol and decl.name == funcName:
                    raise Redeclared(Function(), funcName)
            
            self.prototypeFunction += [funcName]

            param = [] # store parameters of function
            
            for parameter in ast.param:
                for para in param:
                    if para.name == parameter.name.name:
                        raise Redeclared(Parameter(),parameter.name.name)
                param += [VarSymbol(parameter.name.name, parameter.varType,o)]
            
            o[0] += [FuncSymbol(funcName,param,None,None)]
        else: # full function
            exist = False
            for decl in o[0]:
                if type(decl) is FuncSymbol and decl.name == funcName:
                    exist = True
                    if decl.body is not None:
                        raise Redeclared(Function(), funcName)
                    
                    if len(decl.param) != len(ast.param):
                        raise Redeclared(Function(), funcName)
                    
                    else:
                        for i in range(len(decl.param)):
                            if decl.param[i].type is not ast.param[i].varType:
                                raise Redeclared(Function(), funcName)
                            
                    idx = self.prototypeFunction.index(funcName)
                    self.prototypeFunction.pop(idx)
                    
                    param = [] # store parameters of function
            
                    for parameter in ast.param:
                        for para in param:
                            if para.name == parameter.name.name:
                                raise Redeclared(Parameter(),parameter.name.name)
                        param += [VarSymbol(parameter.name.name, parameter.varType,o)]
                    
                    o = [param] + o
                    self.visit(ast.body,o)
                    if  not self.contain_return:
                        decl.returnType = VoidType()
                        decl.body = ast.body
                    else:
                        decl.returnType = self.tmp_return_type
                        decl.body = ast.body
                    self.contain_return = False
                    self.tmp_return_type = None
                    o = o[1:]
                    break
            
            if not exist:
                param = [] # store parameters of function
            
                for parameter in ast.param:
                    for para in param:
                        if para.name == parameter.name.name:
                            raise Redeclared(Parameter(),parameter.name.name)
                    param += [VarSymbol(parameter.name.name, parameter.varType,o)]
                
                o = [param] + o
                self.visit(ast.body,o)
                o = o[1:]
                if  not self.contain_return:
                    o[0]+= [FuncSymbol(funcName,param,VoidType())]
                else:
                    o[0]+= [FuncSymbol(funcName,param,self.tmp_return_type)]
                self.contain_return = False
                self.tmp_return_type = None
                self.current_funcName = None
                
    def visitReturn(self, ast:Return, o):
        if self.contain_return:
            return
        
        self.contain_return = True
        
        hasParent = False
        for function in o[1]:
            if type(function) is FuncSymbol and function.name == self.current_funcName: # find parent function of return statement
                if ast.expr is None: # return not have statement
                    self.tmp_return_type = VoidType()
                    if type(function.returnType) is NoType:
                        function.returnType = VoidType()
                    else:
                        raise TypeMismatchInStatement(ast)
    
                else: # return have expression
                    rType = self.visit(ast.expr,o)    #type of expression
                    if type(rType) is NoType():
                        if type(function.returnType) is NoType():
                            raise TypeCannotBeInferred(ast)
                        else:
                            self.tmp_return_type = function.returnType
                            #infer to for expr of return
                            if type(ast.expr) in [Id, CallExpr, ArrayLiteral]:
                                self.infer(ast.expr,self.tmp_return_type,o)
                                if not self.canInfer:
                                    raise TypeCannotBeInferred(ast)
                            else:
                                TypeCannotBeInferred(ast)
                        self.tmp_return_type = None
                    else:
                        
                        if type(function.returnType) is NoType:
                            function.returnType = rType
                        else:
                            if type(function.returnType) is not type(rType):
                                raise TypeMismatchInStatement(ast)    
                            else:
                                if type(rType) is ArrayType:
                                    if function.returnType.size[:len(rType.size)] != rType.size:
                                        raise TypeMismatchInStatement(ast)
                                    
                                    if type(rType.eleType) is NoType:
                                        if type (ast.expr) in [Id, CallExpr, ArrayLiteral]:
                                            self.infer(ast.expr,function.returnType,o)
                                            if not self.canInfer:
                                                raise TypeCannotBeInferred(ast)
                                            rType = function.returnType
                                        else:
                                            raise TypeCannotBeInferred(ast)
                                    if type(function.returnType.eleType) is not type(rType.eleType) or function.returnType.size != rType.size:
                                        raise TypeMismatchInStatement(ast)
                                self.tmp_return_type = function.returnType

                            
                                     
                hasParent = True
                break

        if not hasParent:
            raise TypeMismatchInStatement(ast)
        self.temp_list_ast = []
                

            
    def visitBreak(self, ast:Break, o):
        if self.inLoop == []:
            raise MustInLoop(ast)

    def visitContinue(self, ast:Continue, o):
            if self.inLoop == []:
                raise MustInLoop(ast)
            
    def visitBlock(self, ast:Block,o):
        o = [[]] + o
        for stmt in ast.stmt:
            self.visit(stmt,o)
        
        self.contain_return = False
        o = o[1:]
        
        
    def visitCallExpr(self, ast: CallExpr, o):
        
        if self.nameVarDeclaring is not None and self.nameVarDeclaring == ast.name.name:
            raise TypeMismatchInExpression(ast)
        
        self.canInfer = True
        
        no_last = o[:-1]
        
        for sym in no_last:
            for subSym in sym:
                if type(subSym) is VarSymbol and subSym.name == ast.name.name:
                    raise TypeMismatchInExpression(ast)
        has_declared = False
        for sym in o:
            for subSym in sym:
                if type(subSym) is FuncSymbol and subSym.name == ast.name.name:
                    if len(ast.args) != len(subSym.param):
                        raise TypeMismatchInExpression(ast)
                    
                    for i in range(len(ast.args)):
                        argType = self.visit(ast.args[i],o)
                        if type(argType) is NoType:
                            if type(ast.args[i]) in [Id, CallExpr, ArrayLiteral]:
                                self.infer(ast.args[i],subSym.param[i],o)
                                if not self.canInfer:
                                    return NoType()
                            else:
                                return NoType()
                            
                        if type(argType) is NoType:
                            self.canInfer = False
                            raise TypeMismatchInExpression(ast)
                        
                        if type(ast.args[i]) is not type (subSym.param[i]):
                            raise TypeMismatchInExpression(ast)
                        else:
                            if type (ast.args[i]) is ArrayType:
                                if ast.arg[i].size[:len(subSym.size)] != subSym.size:
                                    raise TypeMismatchInExpression(ast)
                                
                                if type(ast.args[i].eleType) is NoType:
                                    if type(ast.args[i]) in [Id, CallExpr, ArrayLiteral]:
                                        self.infer(ast.args[i],subSym.eleType,o)
                                        if not self.canInfer:
                                            return NoType()
                                        
                                    
                                    else:
                                        return NoType()
                                
                                if len(ast.arg[i].size) != len(subSym.size) or ast.args[i].size != subSym.size:
                                    raise TypeMismatchInExpression(ast)
                                
                        
                                if type(subSym.returnType) is VoidType:
                                    raise TypeMismatchInExpression(ast)
                                
                                return subSym.returnType
                    
                    has_declared = True
                    break
                
            
        
        if not has_declared:
            raise Undeclared(Function(),ast.name.name) 
        
    def visitCallStmt(self, ast: CallStmt, o):
        
        if self.nameVarDeclaring is not None and self.nameVarDeclaring == ast.name.name:
            raise TypeMismatchInStatement(ast)
        
        self.canInfer = True
        
        no_last = o[:-1]
        
        for sym in no_last:
            for subSym in sym:
                if type(subSym) is VarSymbol and subSym.name == ast.name.name:
                    raise TypeMismatchInStatement(ast)
                
        has_declared = False
        for sym in o:
            for subSym in sym:
                if type(subSym) is FuncSymbol and subSym.name == ast.name.name:
                    if len(ast.args) != len(subSym.param):
                        raise TypeMismatchInStatement(ast)
                    
                    for i in range(len(ast.args)):
                        argType = self.visit(ast.args[i],o)
                        if type(argType) is NoType:
                            if type(ast.args[i]) in [Id, CallExpr, ArrayLiteral]:
                                self.infer(ast.args[i],subSym.param[i],o)
                                if not self.canInfer:
                                    return NoType()
                            else:
                                return NoType()
                            
                        if type(argType) is NoType:
                            self.canInfer = False
                            raise TypeMismatchInStatement(ast)
                        
                        if type(ast.args[i]) is not type (subSym.param[i]):
                            raise TypeMismatchInStatement(ast)
                        else:
                            if type (ast.args[i]) is ArrayType:
                                if ast.arg[i].size[:len(subSym.size)] != subSym.size:
                                    raise TypeMismatchInStatement(ast)
                                
                                if type(ast.args[i].eleType) is NoType:
                                    if type(ast.args[i]) in [Id, CallExpr, ArrayLiteral]:
                                        self.infer(ast.args[i],subSym.eleType,o)
                                        if not self.canInfer:
                                            return NoType()
                                    
                                    else:
                                        return NoType()
                                
                                if len(ast.arg[i].size) != len(subSym.size) or ast.args[i].size != subSym.size:
                                    raise TypeMismatchInStatement(ast)
                                
                if type(subSym.returnType) is NoType:
                    self.infer(ast,VoidType(),o)
                                
                has_declared = True
                break
                
            
        
        if not has_declared:
            raise Undeclared(Function(),ast.name.name)  
          
    def visitAssign(self, ast: Assign, o):
        rType = self.visit(ast.exp,o)
        lType = self.visit(ast.lhs,o)
        if type(rType) is NoType and type(lType) is NoType:
            raise TypeCannotBeInferred(ast)
        
        if type(lType) is NoType and type(rType) is not None:
            if type(ast.lhs) is Id:
                lType = self.infer(ast.lhs, rType,o)
                
            else:
                raise TypeCannotBeInferred(ast)
        
        elif type(lType) is not None and type(rType) is None:
            if type(ast.exp) in [Id, CallExpr, ArrayLiteral]:
                self.infer(ast.exp,lType,o)
                if not self.canInfer:
                    raise TypeCannotBeInferred(ast)
            else:
                raise TypeCannotBeInferred(ast)
            
        else:
            
            if type(lType) is VoidType:
                raise TypeMismatchInStatement(ast)
            
            if type(lType) is not type(rType):
                raise TypeMismatchInStatement(ast)
            
            else:
                if type(lType) is ArrayType:
                    if lType.size[:len(rType.size)] != rType.size:
                        raise TypeMismatchInStatement(ast)
                    
                    else:
                        if type(rType.eleType) is NoType:
                            if type(ast.exp) in [Id, CallExpr, ArrayLiteral]:
                                self.infer(ast.exp,o)
                                
                                if not self.canInfer:
                                    raise TypeCannotBeInferred(ast)

                                rType = lType
                            
                            else:
                                raise TypeCannotBeInferred(ast)
                            
                        
                        if type(lType.eleType) is not type(rType.eleType) or lType.size != rType.size:
                            raise TypeMismatchInStatement(ast)
                        
                    
    def visitIf(self, ast: If, o):
    # expr: Expr
    # thenStmt: Stmt
    # elifStmt: List[Tuple[Expr, Stmt]] # empty list if there is no elif statement
    # elseStmt: Stmt = None  # None if there is no else branch
        conType = self.visit(ast.expr,o)
        if type(conType) is not BoolType:
            raise TypeMismatchInStatement(ast)
        
        if type(conType) is NoType:
            if type(ast.expr) in [Id, CallExpr, ArrayLiteral]:
                self.infer(ast.expr, BoolType(),o)
                if not self.canInfer:
                    raise TypeCannotBeInferred(ast)
                
                conType = BoolType()
            
            else:
                raise TypeCannotBeInferred(ast)
        
        
        self.visit(self.thenStmt)
        self.contain_return = False
        for elifCon, elifStmt in ast.elifStmt:
            condType = self.visit(elifCon,o)
            if (condType) is None:
                if type(elifCon) in [Id, CallExpr]:
                    self.infer(elifCon,BoolType(),o):
                    if not self.canInfer:
                        raise TypeCannotBeInferred(ast)
                    elifCon = BoolType()
                else:
                    raise TypeCannotBeInferred(ast)
            
            
            if type(condType) is not BoolType:
                raise TypeMismatchInStatement(ast)
            
            self.visit(elifStmt,o)
            self.contain_return = False
        
        if ast.elifStmt:
            self.visit(ast.elseStmt,o)
            
            
    def visitFor(self, ast:For, o):
        
                    
                    
                    
                        
                