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
        def sqSubSetEq(a: SignAbsVal, b: SignAbsVal): Option[Boolean] = (a, b) match {
            case (Bot, _) => Some(true)           // Bot is bottom
            case (_, Top) => Some(true)           // Top is top
            case (x, y) if x == y => Some(true)   // reflexive
            case (Minus, Minus) => Some(true)
            case (Zero, Zero) => Some(true)
            case (Plus, Plus) => Some(true)
            case (Minus, Zero) => Some(false)     // incomparable
            case (Minus, Plus) => Some(false)     // incomparable
            case (Zero, Minus) => Some(false)     // incomparable
            case (Zero, Plus) => Some(false)      // incomparable
            case (Plus, Minus) => Some(false)     // incomparable
            case (Plus, Zero) => Some(false)      // incomparable
            case (Top, _) => Some(false)          // Top is only ⊑ Top
            case (_, Bot) => Some(false)          // only Bot is ⊑ Bot
        }

        def lub(a:SignAbsVal, b:SignAbsVal):SignAbsVal = (a, b) match {
            case (Bot, x) => x
            case (x, Bot) => x
            case (Top, _) => Top
            case (_, Top) => Top
            case (x, y) if x == y => x
            case (Minus, Zero) => Top
            case (Minus, Plus) => Top
            case (Zero, Minus) => Top
            case (Zero, Plus) => Top
            case (Plus, Minus) => Top
            case (Plus, Zero) => Top
        }
    }
}