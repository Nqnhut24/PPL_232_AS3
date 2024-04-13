# Generated from c:/Users/Admin/Documents/HK232/PPL/Assignment3/assignment3-initial/src/main/zcode/parser/ZCode.g4 by ANTLR 4.13.1
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
    from typing import TextIO
else:
    from typing.io import TextIO


from lexererr import *


def serializedATN():
    return [
        4,0,6,41,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,1,
        0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,5,1,23,8,1,10,1,12,1,26,9,1,1,
        2,4,2,29,8,2,11,2,12,2,30,1,2,1,2,1,3,1,3,1,3,1,4,1,4,1,5,1,5,0,
        0,6,1,1,3,2,5,3,7,4,9,5,11,6,1,0,3,1,0,97,122,2,0,48,57,97,122,3,
        0,9,10,13,13,32,32,42,0,1,1,0,0,0,0,3,1,0,0,0,0,5,1,0,0,0,0,7,1,
        0,0,0,0,9,1,0,0,0,0,11,1,0,0,0,1,13,1,0,0,0,3,20,1,0,0,0,5,28,1,
        0,0,0,7,34,1,0,0,0,9,37,1,0,0,0,11,39,1,0,0,0,13,14,5,110,0,0,14,
        15,5,117,0,0,15,16,5,109,0,0,16,17,5,98,0,0,17,18,5,101,0,0,18,19,
        5,114,0,0,19,2,1,0,0,0,20,24,7,0,0,0,21,23,7,1,0,0,22,21,1,0,0,0,
        23,26,1,0,0,0,24,22,1,0,0,0,24,25,1,0,0,0,25,4,1,0,0,0,26,24,1,0,
        0,0,27,29,7,2,0,0,28,27,1,0,0,0,29,30,1,0,0,0,30,28,1,0,0,0,30,31,
        1,0,0,0,31,32,1,0,0,0,32,33,6,2,0,0,33,6,1,0,0,0,34,35,9,0,0,0,35,
        36,6,3,1,0,36,8,1,0,0,0,37,38,9,0,0,0,38,10,1,0,0,0,39,40,9,0,0,
        0,40,12,1,0,0,0,3,0,24,30,2,6,0,0,1,3,0
    ]

class ZCodeLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    NUMBER = 1
    IDENTIFIER = 2
    WS = 3
    ERROR_CHAR = 4
    UNCLOSE_STRING = 5
    ILLEGAL_ESCAPE = 6

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'number'" ]

    symbolicNames = [ "<INVALID>",
            "NUMBER", "IDENTIFIER", "WS", "ERROR_CHAR", "UNCLOSE_STRING", 
            "ILLEGAL_ESCAPE" ]

    ruleNames = [ "NUMBER", "IDENTIFIER", "WS", "ERROR_CHAR", "UNCLOSE_STRING", 
                  "ILLEGAL_ESCAPE" ]

    grammarFileName = "ZCode.g4"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.1")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None


    def action(self, localctx:RuleContext, ruleIndex:int, actionIndex:int):
        if self._actions is None:
            actions = dict()
            actions[3] = self.ERROR_CHAR_action 
            self._actions = actions
        action = self._actions.get(ruleIndex, None)
        if action is not None:
            action(localctx, actionIndex)
        else:
            raise Exception("No registered action for:" + str(ruleIndex))


    def ERROR_CHAR_action(self, localctx:RuleContext , actionIndex:int):
        if actionIndex == 0:
            raise ErrorToken(self.text)
     


