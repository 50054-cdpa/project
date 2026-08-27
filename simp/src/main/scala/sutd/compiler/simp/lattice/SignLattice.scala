package sutd.compiler.simp.lattice

import sutd.compiler.simp.lattice.CompleteLattice.{given, *} 

object SignLattice {
    import CompleteLattice.* 
    enum SignAbsVal {
        case Bot    // _|_
        case Minus  // -
        case Plus   // + 
        case Top    // T
        case Zero   // 0
    }

    import SignAbsVal.*
    // Cohort Problem Exercise 2
    given signLattice:CompleteLattice[SignAbsVal] = new CompleteLattice[SignAbsVal] {
        def sqSubSetEq(a: SignAbsVal, b: SignAbsVal): Option[Boolean] = None // TODO: FixMe  
        def lub(a:SignAbsVal, b:SignAbsVal):SignAbsVal = // Top // TODO: FixMe
            (a, b) match {
                case (Bot, _) => b 
                case (_, Bot) => a
                case (Top, _) => Top 
                case (_, Top) => Top
                case (Zero, Zero) => Zero 
                case (Plus, Plus) => Plus
                case (Minus, Minus) => Minus
                case (_ , _ ) => Top 
            }
    }
}