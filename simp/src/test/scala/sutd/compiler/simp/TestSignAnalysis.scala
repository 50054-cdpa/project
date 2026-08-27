package sutd.compiler.simp

import scala.language.adhocExtensions
import org.scalatest.funsuite 
import org.scalatest.matchers
import sutd.compiler.simp.ir.PseudoAssembly.*
import sutd.compiler.simp.semantic.SignAnalysis.*
import sutd.compiler.simp.lattice.SignLattice.*
import scala.collection.immutable.HashMap

class TestSignAnalysis extends funsuite.AnyFunSuite {
    import Instr.* 
    import Opr.*
    import SignAbsVal.*
    /*
    1: x <- input
    2: s <- 0
    3: c <- 0
    4: b <- c < x
    5: ifn b goto 9
    6: s <- c + s
    7: c <- c + 1
    8: goto 4
    9: _ret_r <- s
    10: ret
    */
    test("test Sign Analysis with sum()"){
        val input = Temp(AVar("input"))
        val x = Temp(AVar("x"))
        val s = Temp(AVar("s"))
        val c = Temp(AVar("c"))
        val b = Temp(AVar("b"))
        val r_ret = Regstr("_r_ret")
        val pa = List(
            (1, IMove(x, input)),
            (2, IMove(s, IntLit(0))),
            (3, IMove(c, IntLit(0))),
            (4, ILThan(b, c, x)),
            (5, IIfNot(b, 9)),
            (6, IPlus(s, c, s)),
            (7, IPlus(c, c, IntLit(1))),
            (8, IGoto(4)),
            (9, IMove(r_ret, s)),
            (10, IRet)
        )
        val expected = HashMap(
            1 -> HashMap("b" -> Bot, "c" -> Bot, "input" -> Top, "s" -> Bot, "x" -> Top), 
            2 -> HashMap("b" -> Bot, "c" -> Bot, "input" -> Top, "s" -> Zero, "x" -> Top), 
            3 -> HashMap("b" -> Bot, "c" -> Zero, "input" -> Top, "s" -> Zero, "x" -> Top), 
            4 -> HashMap("b" -> Top, "c" -> Top, "input" -> Top, "s" -> Top, "x" -> Top),
            5 -> HashMap("b" -> Top, "c" -> Top, "input" -> Top, "s" -> Top, "x" -> Top), 
            6 -> HashMap("b" -> Top, "c" -> Top, "input" -> Top, "s" -> Top, "x" -> Top), 
            7 -> HashMap("b" -> Top, "c" -> Top, "input" -> Top, "s" -> Top, "x" -> Top), 
            8 -> HashMap("b" -> Top, "c" -> Top, "input" -> Top, "s" -> Top, "x" -> Top), 
            9 -> HashMap("b" -> Top, "c" -> Top, "input" -> Top, "s" -> Top, "x" -> Top), 
            10 -> HashMap("b" -> Top, "c" -> Top, "input" -> Top, "s" -> Top, "x" -> Top)
        ) 
        analyze(pa) match {
            case Left(err) => { 
                println(err)
                assert(false)
            }
            case Right(res) => assert(res == expected) 
        }
    }



    /*
    This test case shows that this sign analysis is not accurate enough to detect the negativity of x of return statement
    // SIMP1
    x = input;
    while (x >= 0) {
        x = x - 1;
    }
    return x; // x must be -

    1: x <- input
    2: a <- 0 == x
    3: b <- 0 < x
    4: c <- a + b   // b || c
    5: ifn c goto 8
    6: x <- x - 1
    7: goto 2
    8: _ret_r <- x
    9: ret
    */
    test("test Sign Analysis with descending subtraction"){
        val input = Temp(AVar("input"))
        val x = Temp(AVar("x"))
        val a = Temp(AVar("a"))
        val c = Temp(AVar("c"))
        val b = Temp(AVar("b"))
        val r_ret = Regstr("_r_ret")
        val pa = List(
            (1, IMove(x, input)),
            (2, IDEqual(a, IntLit(0), x)),
            (3, ILThan(b, IntLit(0), x)),
            (4, ILThan(c, a, b)),
            (5, IIfNot(c, 8)),
            (6, IMinus(x, x, IntLit(1))),
            (7, IGoto(2)),
            (8, IMove(r_ret, x)),
            (9, IRet)
        )
        val expected = HashMap(
            1 -> HashMap("x" -> Top, "a" -> Bot, "b" -> Bot, "c" -> Bot, "input" -> Top), 
            2 -> HashMap("x" -> Top, "a" -> Top, "b" -> Top, "c" -> Top, "input" -> Top), 
            3 -> HashMap("x" -> Top, "a" -> Top, "b" -> Top, "c" -> Top, "input" -> Top), 
            4 -> HashMap("x" -> Top, "a" -> Top, "b" -> Top, "c" -> Top, "input" -> Top),
            5 -> HashMap("x" -> Top, "a" -> Top, "b" -> Top, "c" -> Top, "input" -> Top), 
            6 -> HashMap("x" -> Top, "a" -> Top, "b" -> Top, "c" -> Top, "input" -> Top), 
            7 -> HashMap("x" -> Top, "a" -> Top, "b" -> Top, "c" -> Top, "input" -> Top), 
            8 -> HashMap("x" -> Top, "a" -> Top, "b" -> Top, "c" -> Top, "input" -> Top), 
            9 -> HashMap("x" -> Top, "a" -> Top, "b" -> Top, "c" -> Top, "input" -> Top) 
            ) 

        analyze(pa) match {
            case Left(err) => { 
                println(err)
                assert(false)
            }
            case Right(res) => assert(res == expected) 
        }
    }

}
