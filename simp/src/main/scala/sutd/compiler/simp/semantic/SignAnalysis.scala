package sutd.compiler.simp.semantic

import sutd.compiler.simp.monad.Monad.*
import sutd.compiler.simp.lattice.CompleteLattice.{*, given}
import sutd.compiler.simp.lattice.SignLattice.{*, given}
import sutd.compiler.simp.ir.PseudoAssembly.* 
import sutd.compiler.simp.ir.CFG.*
import sutd.compiler.simp.semantic.Util.*


object SignAnalysis {
    import Instr.* 
    import Opr.* 
    import AVar.* 
    
    type AbstractState = Map[String, SignAbsVal]

    import SignAbsVal.* 


    /**
      * lookup the sign of a name from an abstract state, if not found, bot is returned
      *
      * @param m
      * @param n
      * @return
      */
    def getSign(m:AbstractState, n:String):SignAbsVal = m.get(n) match {
        case None => Bot
        case Some(v) => v
    }


    /**
      * lookup the sign of a operand from an abstract state.
      *
      * @param m
      * @param o
      * @return
      */
    def getOprSign(m:AbstractState, o:Opr):Either[String, SignAbsVal] = o match {
        case IntLit(v) if v > 0 => Right(Plus)
        case IntLit(v) if v == 0 => Right(Zero)
        case IntLit(v) => Right(Minus)
        case Regstr(name) => Left(s"getOprSign failed. Trying to retrieve the sign from an register ${name}.")
        case Temp(AVar(n)) => Right(getSign(m, n))
    } 


    /**
      * Mapping label to abstract state, each entry in this map is an s_i where i is the label.
      * 
      * Note htis is also a map lattice
      */
    type AbstractEnv = Map[Label, AbstractState]


    /**
      * join(s) = \sqbigcup_{t \in pred(s)} t
      *
      * @param ss
      * @return
      */
    // Cohort Problem Exercise 2
    def join(preds:List[AbstractState]):AbstractState = // TODO: Fixme
        Map()

    type MonotoneFunction = AbstractEnv => Either[String, AbstractEnv]


    /**
      * Generate the monotone function from a PA program p
      *
      * @param p
      * @return
      */
    def genMonotoneFunction(p:List[LabeledInstr]):MonotoneFunction = {
        val cfg = buildCFG(p)
        val vars = allVars(p)
        val s0 = vars.map( v => if (v == "input") (v, Top) else (v, Bot)).toMap // set everything to bottom except for input
        def joinPredStates(label:Label, env:AbstractEnv):AbstractState = {
            val preds = predecessors(cfg, label)
            val preds_states = preds match { 
              case Nil => List(s0)  // label is the first label
              case _ => preds.flatMap( pred => env.get(pred) ) }
            join(preds_states)
        }

        (absEnv:AbstractEnv) => {
          /**
            * iterate through all the labeled instructions in p
            */
          foldM(
            (acc:AbstractEnv, li:LabeledInstr) => li match {
              /**
                * case l:t <- src:   s_l = join(s_l)[t -> join(s_l)(src)]
                */
              case (label, IMove(Temp(AVar(t)), src)) => {
                val joined_preds_states = joinPredStates(label, acc)
                getOprSign(joined_preds_states, src) match {
                  case Left(err) => Left(err)
                  case Right(sign) => Right(acc + (label -> (joined_preds_states + (t -> sign) )))
                }
              }
              // Cohort Problem Exercise 3
              // TODO
              /**
                * case l: t <- src1 op src2:  s_l = join(s_l)[t -> join(s_l)(src1) abs(op) join(s_l)(src1)]
                */
              // YOUR CODE HERE 
              /**
                * other cases: s_l = join(s_l)
                */
              case (label, _) => {
                val joined_preds_states = joinPredStates(label, acc)
                Right(acc + (label -> joined_preds_states))
              }
            })(absEnv)(p)
        }
    }

    /**
      * | ++ | $\top$ | + | - | 0 | $\bot$ | 
        |---|---|---|---|---|---|
        | $\top$| $\top$| $\top$| $\top$| $\top$| $\bot$| 
        | + | $\top$ | + | $\top$ | + | $\bot$| 
        | - | $\top$ | $\top$ | - | - | $\bot$ |
        | 0 | $\top$ | + | - | 0 | $\bot$ |
        | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | 
      *
      * @param s1
      * @param s2
      * @return
      */
    def absPlus(s1:SignAbsVal, s2:SignAbsVal):SignAbsVal = (s1, s2) match {
      case (Top, Bot)     => Bot
      case (Top, _)       => Top 
      case (Plus, Bot)    => Bot
      case (Plus, Zero)   => Plus
      case (Plus, Plus)   => Plus
      case (Plus, Top)    => Top
      case (Plus, Minus)  => Top 
      case (Minus, Bot)   => Bot 
      case (Minus, Top)   => Top 
      case (Minus, Plus)  => Top 
      case (Minus, Minus) => Minus
      case (Minus, Zero)  => Minus 
      case (Zero, s2)     => s2
      case (Bot, _)       => Bot 
    }

    /**
      * | -- | $\top$ | + | - | 0 | $\bot$ | 
        |---|---|---|---|---|---|
        | $\top$| $\top$| $\top$| $\top$| $\top$| $\bot$| 
        | + | $\top$ | $\top$ | + | + | $\bot$| 
        | - | $\top$ | - | $\top$ | - | $\bot$ |
        | 0 | $\top$ | - | + | 0 | $\bot$ |
        | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | 
      * 
      */

    def absMinus(s1:SignAbsVal, s2:SignAbsVal):SignAbsVal = (s1, s2) match {
      case (Top, Bot)     => Bot
      case (Top, _)       => Top 
      case (Plus, Bot)    => Bot
      case (Plus, Zero)   => Plus
      case (Plus, Minus)  => Plus 
      case (Plus, Plus)   => Top 
      case (Plus, Top)    => Top 
      case (Minus, Bot)   => Bot 
      case (Minus, Zero)  => Minus
      case (Minus, Minus) => Top
      case (Minus, Plus)  => Minus
      case (Minus, Top)   => Top
      case (Zero, Bot)    => Bot
      case (Zero, Zero)   => Zero
      case (Zero, Minus)  => Plus
      case (Zero, Plus)   => Minus
      case (Zero, Top)    => Top 
      case (Bot, _)       => Bot
    }

    /**
      * | ** | $\top$ | + | - | 0 | $\bot$ | 
        |---|---|---|---|---|---|
        | $\top$| $\top$| $\top$| $\top$| 0 | $\bot$| 
        | + | $\top$ | + | - | 0 | $\bot$| 
        | - | $\top$ | - | + | 0 | $\bot$ |
        | 0 | 0 | 0 | 0 | 0 | $\bot$ |
        | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | 
      */
    
    def absMult(s1:SignAbsVal, s2:SignAbsVal):SignAbsVal = (s1, s2) match {
      case (Top, Bot)     => Bot
      case (Top, Zero)    => Zero
      case (Top, _)       => Top
      case (Plus, Bot)    => Bot
      case (Plus, Zero)   => Zero
      case (Plus, Minus)  => Minus
      case (Plus, Plus)   => Plus
      case (Plus, Top)    => Top
      case (Minus, Bot)   => Bot 
      case (Minus, Zero)  => Zero
      case (Minus, Minus) => Plus
      case (Minus, Plus)  => Minus
      case (Minus, Top)   => Top 
      case (Zero, Bot)    => Bot
      case (Zero, _)      => Zero 
      case (Bot, _)       => Bot 
    }

    /**
      * | === | $\top$ | + | - | 0 | $\bot$ | 
        |---|---|---|---|---|---|
        | $\top$| $\top$| $\top$| $\top$| $\top$ | $\bot$| 
        | + | $\top$ | $\top$ | 0 | 0 | $\bot$| 
        | - | $\top$ | 0 | $\top$ | 0 | $\bot$ |
        | 0 | $\top$ | 0 | 0 | + | $\bot$ |
        | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | 
      */

    def absDEqual(s1:SignAbsVal, s2:SignAbsVal):SignAbsVal = (s1, s2) match {
      case (Top, Bot)     => Bot
      case (Top, _)       => Top
      case (Plus, Bot)    => Bot
      case (Plus, Zero)   => Zero
      case (Plus, Minus)  => Zero
      case (Plus, Plus)   => Top 
      case (Plus, Top)    => Top
      case (Minus, Bot)   => Bot 
      case (Minus, Zero)  => Zero
      case (Minus, Minus) => Top 
      case (Minus, Plus)  => Zero
      case (Minus, Top)   => Top 
      case (Zero, Bot)    => Bot
      case (Zero, Zero)   => Plus
      case (Zero, Minus)  => Zero 
      case (Zero, Plus)   => Zero
      case (Zero, Top)    => Top 
      case (Bot, _)       => Bot 
    }

    /**
      * 
      * | << | $\top$ | + | - | 0 | $\bot$ | 
        |---|---|---|---|---|---|
        | $\top$| $\top$| $\top$| $\top$| $\top$ | $\bot$| 
        | + | $\top$ | $\top$ | 0 | 0 | $\bot$| 
        | - | $\top$ | + | $\top$ | + | $\bot$ |
        | 0 | $\top$ | + | 0 | 0 | $\bot$ |
        | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | 
      * 
      */

    def absLThan(s1:SignAbsVal, s2:SignAbsVal):SignAbsVal = (s1, s2) match {
      case (Top, Bot)     => Bot
      case (Top, _)       => Top
      case (Plus, Bot)    => Bot
      case (Plus, Zero)   => Zero
      case (Plus, Minus)  => Zero
      case (Plus, Plus)   => Top 
      case (Plus, Top)    => Top
      case (Minus, Bot)   => Bot 
      case (Minus, Zero)  => Plus
      case (Minus, Minus) => Top 
      case (Minus, Plus)  => Plus
      case (Minus, Top)   => Top 
      case (Zero, Bot)    => Bot
      case (Zero, Zero)   => Zero
      case (Zero, Minus)  => Zero 
      case (Zero, Plus)   => Plus
      case (Zero, Top)    => Top 
      case (Bot, _)       => Bot 
    }



    /**
      * Top level function for sign analysis 
      * Peform sign analysis over a PA program `p` return an abstract environment mapping label to abstract states
      *   Each abstract state is mapping variable names to sign abstract value.
      *
      * @param p
      * @param i
      * @return
      */
    def analyze(p:List[LabeledInstr])(using i:CompleteLattice[AbstractEnv]):Either[String, AbstractEnv] = {
      val f = genMonotoneFunction(p)
      val vars = allVars(p)
      val labels = p.map( li => li match {case (l,_) => l})
      val init_abstract_state:AbstractState = vars.map( x => (x,Top)).toMap
      val init_abstract_env:AbstractEnv = labels.map( l => (l, init_abstract_state)).toMap
      i.naiveFP(f)(init_abstract_env)
    }
}