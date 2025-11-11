package sutd.compiler.simp


import scala.language.adhocExtensions
import org.scalatest.funsuite 
import org.scalatest.matchers
import sutd.compiler.simp.syntax.Lexer.*
import sutd.compiler.simp.syntax.Parsec.*
import sutd.compiler.simp.syntax.Parser.*
import sutd.compiler.simp.syntax.*
import sutd.compiler.simp.syntax.AST.*


class TestParser extends funsuite.AnyFunSuite {
    import LToken.*
    import Progress.*
    import Result.*
    import SrcLoc.*
    import Stmt.* 
    import Exp.*
    import Const.*



    test("test p_spaces: parsing 0 spaces") {
        val input = List()
        val expected = List() 
        Parsec.run(p_spaces)(PEnv(input)) match {
            case Empty(Ok((exp, penv))) if done(penv) => {
                assert(exp == expected)
            }
            case others => {
                println(others)
                assert(false)
            }
        }
    }


    test("test p_spaces: parsing 3 spaces") {
        val input = List(
            WhiteSpace(SrcLoc(1,1), ' '), 
            WhiteSpace(SrcLoc(1,2), ' '), 
            WhiteSpace(SrcLoc(1,3), ' ') 
        )
        val expected = input
        Parsec.run(p_spaces)(PEnv(input)) match {
            case Consumed(Ok((exp, penv))) if done(penv) => {
                assert(exp == expected)
            }
            case others => {
                println(others)
                assert(false)
            }
        }
    }

    test("test p_spaces: parsing 3 tabs") {
        val input = List(
            WhiteSpace(SrcLoc(1,1), '\t'), 
            WhiteSpace(SrcLoc(1,2), '\t'), 
            WhiteSpace(SrcLoc(1,3), '\t') 
        )
        val expected = input
        Parsec.run(p_spaces)(PEnv(input)) match {
            case Consumed(Ok((exp, penv))) if done(penv) => {
                assert(exp == expected)
            }
            case others => {
                println(others)
                assert(false)
            }
        }
    }

    test("test p_spaces: should not parse id") {
        val input = List(
            IdTok(SrcLoc(1,1),"x"), WhiteSpace(SrcLoc(1,2), ' ') 
        )
        val expected = input
        Parsec.run(p_spaces)(PEnv(input)) match {
            case Consumed(Ok((exp, penv))) if done(penv) => {
                // assert(exp == expected)
                assert(false)
            }
            case others => {
                assert(true)
            }
        }
    }

    test("test p_exp: parsing x + 1") {
        val input = List(
            IdTok(SrcLoc(1,1),"x"), WhiteSpace(SrcLoc(1,2), ' '), 
            PlusSign(SrcLoc(1,3)), WhiteSpace(SrcLoc(1,4),' ' ), IntTok(SrcLoc(1,5),1)
        )
        val expected = Plus(VarExp(Var("x")),ConstExp(IntConst(1)))
        Parsec.run(p_exp)(PEnv(input)) match {
            case Consumed(Ok((exp, penv))) if done(penv) => {
                assert(exp == expected)
            }
            case others => {
                assert(false)
            }
        }
    }

    test("test p_exp: parsing x - (1 + (y * 2))") {
        val input = List(
            IdTok(SrcLoc(1,1),"x"), WhiteSpace(SrcLoc(1,2), ' '), 
            MinusSign(SrcLoc(1,3)), WhiteSpace(SrcLoc(1,4), ' '), 
            LParen(SrcLoc(1,5)), IntTok(SrcLoc(1,6),1),  WhiteSpace(SrcLoc(1,7), ' '), 
            PlusSign(SrcLoc(1,8)),  WhiteSpace(SrcLoc(1,9), ' '), 
            LParen(SrcLoc(1,10)), IdTok(SrcLoc(1,11),"y"),  WhiteSpace(SrcLoc(1,12), ' '),
            AsterixSign(SrcLoc(1,13)),  WhiteSpace(SrcLoc(1,14), ' '), 
            IntTok(SrcLoc(1,15),2), RParen(SrcLoc(1,16)), RParen(SrcLoc(1,17))
        )
        val expected = Minus(VarExp(Var("x")),ParenExp(Plus(ConstExp(IntConst(1)),ParenExp(Mult(VarExp(Var("y")),ConstExp(IntConst(2)))))))
        Parsec.run(p_exp)(PEnv(input)) match {
            case Consumed(Ok((exp, penv))) if done(penv) => {
                assert(exp == expected)
            }
            case others => {
                assert(false)
            }
        }
    }

    test("test parser: parsing y = 1; x = x + 1;") {
        // y = 1; x = x + 1;
        val input = List(            
            IdTok(SrcLoc(1,2),"y"), WhiteSpace(SrcLoc(1,3),' '), 
            EqSign(SrcLoc(1,4)), WhiteSpace(SrcLoc(1,5),' '), IntTok(SrcLoc(1,6),1), 
            SemiColon(SrcLoc(1,7)), WhiteSpace(SrcLoc(1,8), ' '),
            IdTok(SrcLoc(1,9),"x"), WhiteSpace(SrcLoc(1,10), ' '), 
            EqSign(SrcLoc(1,11)), WhiteSpace(SrcLoc(1,12), ' '), IdTok(SrcLoc(1,13),"x"), WhiteSpace(SrcLoc(1,14), ' '), 
            PlusSign(SrcLoc(1,15)), WhiteSpace(SrcLoc(1,16),' ' ), IntTok(SrcLoc(1,17),1), SemiColon(SrcLoc(1,18))) 
        val expected =  List(Assign(Var("y"),ConstExp(IntConst(1))), Assign(Var("x"),Plus(VarExp(Var("x")),ConstExp(IntConst(1)))))
        Parsec.run(parse)(PEnv(input)) match {
            case Consumed(Ok((stmts, penv))) if done(penv) => {
                assert(stmts == expected)
            }
            case others => {
                assert(false)
            }
        }
    }


    test("test parser: parsing" + """ 
x = input;
s = 0;
c = 0;
while c < x {
    s = c + s;
    c = c + 1;
}
return s;
        """) {
        val input = List(
            WhiteSpace(SrcLoc(2,1),'\n'), IdTok(SrcLoc(2,2),"x"), WhiteSpace(SrcLoc(2,3),' '), EqSign(SrcLoc(2,4)), WhiteSpace(SrcLoc(2,5),' '), IdTok(SrcLoc(2,10),"input"), SemiColon(SrcLoc(2,11)), 
            WhiteSpace(SrcLoc(3,1),'\n'), IdTok(SrcLoc(3,2),"s"), WhiteSpace(SrcLoc(3,3),' '), EqSign(SrcLoc(3,4)), WhiteSpace(SrcLoc(3,5),' '), IntTok(SrcLoc(3,6),0), SemiColon(SrcLoc(3,7)), 
            WhiteSpace(SrcLoc(4,1),'\n'), IdTok(SrcLoc(4,2),"c"), WhiteSpace(SrcLoc(4,3),' '), EqSign(SrcLoc(4,4)), WhiteSpace(SrcLoc(4,5),' '), IntTok(SrcLoc(4,6),0), SemiColon(SrcLoc(4,7)), 
            WhiteSpace(SrcLoc(5,1),'\n'), WhileKW(SrcLoc(5,6)), WhiteSpace(SrcLoc(5,7),' '), IdTok(SrcLoc(5,8),"c"), WhiteSpace(SrcLoc(5,9),' '), LThanSign(SrcLoc(5,10)), WhiteSpace(SrcLoc(5,11),' '), IdTok(SrcLoc(5,12),"x"), WhiteSpace(SrcLoc(5,13),' '), LBrace(SrcLoc(5,14)), 
            WhiteSpace(SrcLoc(6,1),'\n'), WhiteSpace(SrcLoc(6,2),' '), WhiteSpace(SrcLoc(6,3),' '), WhiteSpace(SrcLoc(6,4),' '), WhiteSpace(SrcLoc(6,5),' '), IdTok(SrcLoc(6,6),"s"), WhiteSpace(SrcLoc(6,7),' '), EqSign(SrcLoc(6,8)), WhiteSpace(SrcLoc(6,9),' '), IdTok(SrcLoc(6,10),"c"), WhiteSpace(SrcLoc(6,11),' '), PlusSign(SrcLoc(6,12)), WhiteSpace(SrcLoc(6,13),' '), IdTok(SrcLoc(6,14),"s"), SemiColon(SrcLoc(6,15)), 
            WhiteSpace(SrcLoc(7,1),'\n'), WhiteSpace(SrcLoc(7,2),' '), WhiteSpace(SrcLoc(7,3),' '), WhiteSpace(SrcLoc(7,4),' '), WhiteSpace(SrcLoc(7,5),' '), IdTok(SrcLoc(7,6),"c"), WhiteSpace(SrcLoc(7,7),' '), EqSign(SrcLoc(7,8)), WhiteSpace(SrcLoc(7,9),' '), IdTok(SrcLoc(7,10),"c"), WhiteSpace(SrcLoc(7,11),' '), PlusSign(SrcLoc(7,12)), WhiteSpace(SrcLoc(7,13),' '), IntTok(SrcLoc(7,14),1), SemiColon(SrcLoc(7,15)), 
            WhiteSpace(SrcLoc(8,1),'\n'), RBrace(SrcLoc(8,2)), 
            WhiteSpace(SrcLoc(9,1),'\n'), RetKW(SrcLoc(9,7)), WhiteSpace(SrcLoc(9,8),' '), IdTok(SrcLoc(9,9),"s"), SemiColon(SrcLoc(9,10)), 
            WhiteSpace(SrcLoc(10,1),'\n'), WhiteSpace(SrcLoc(10,2),' '), WhiteSpace(SrcLoc(10,3),' '), WhiteSpace(SrcLoc(10,4),' '), WhiteSpace(SrcLoc(10,5),' '), WhiteSpace(SrcLoc(10,6),' '), WhiteSpace(SrcLoc(10,7),' '), WhiteSpace(SrcLoc(10,8),' '), WhiteSpace(SrcLoc(10,9),' ')
        ) 
        val expected =  List(
            Assign(Var("x"),VarExp(Var("input"))), 
            Assign(Var("s"),ConstExp(IntConst(0))), 
            Assign(Var("c"),ConstExp(IntConst(0))), 
            While(LThan(VarExp(Var("c")),VarExp(Var("x"))),
                List(
                    Assign(Var("s"),Plus(VarExp(Var("c")),VarExp(Var("s")))), 
                    Assign(Var("c"),Plus(VarExp(Var("c")),ConstExp(IntConst(1)))))), 
            Ret(Var("s")))
        Parsec.run(parse)(PEnv(input)) match {
            case Consumed(Ok((stmts, penv))) if done(penv) => {
                assert(stmts == expected, s"Expected: $expected\nGot: $stmts\n")
            }
            case others => {
                assert(false)
            }
        }
    }
}