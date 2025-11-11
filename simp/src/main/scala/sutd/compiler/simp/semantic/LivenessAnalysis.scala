package sutd.compiler.simp.semantic


import sutd.compiler.simp.monad.Monad.{given, *}
import sutd.compiler.simp.lattice.CompleteLattice.{*, given}
import sutd.compiler.simp.ir.PseudoAssembly.* 
import sutd.compiler.simp.ir.CFG.*
import sutd.compiler.simp.semantic.Util.*

object LivenessAnalysis {
    import Instr.* 
    import Opr.* 
    import AVar.* 
    

    /**
      * abstract state is a set of variable names
      */
    type AbstractState = Set[String] 

    
    /**
      * AbstractEnv is a mapping from label to abstract state
      */
    type AbstractEnv = Map[Label, AbstractState]


    /**
      * join(s) = \sqbigcup_{t \in succ(s)} t
      *
      * @param succs, abstract states coming from the successors
      * @return
      */
    // Task 2.1
    def join(succs:List[AbstractState]):AbstractState = {
        // For power set lattice, join (⊔) is union (∪)
        // Liveness analysis is backward, so we merge states from successors
        succs.foldLeft(Set():AbstractState)((acc, s) => acc union s)
    }

    
    type MonotoneFunction = AbstractEnv => Either[String, AbstractEnv]


    /**
      * Generate the monotone function from a PA program p
      *
      * @param p
      * @return
      */
    def genMonotoneFunction(p:List[LabeledInstr]):MonotoneFunction = {
        val cfg = buildCFG(p)
        val top = allVars(p)
        def joinSuccStates(label:Label, env:AbstractEnv):AbstractState = {
            val succs = successors(cfg, label)
            val succs_states:List[AbstractState] = succs.flatMap( 
                succ => env.get(succ) match {
                case None => List(Set()) 
                case Some(value) => List(value)
              })
            join(succs_states)
        }

        (absEnv:AbstractEnv) => {
          /**
            * iterate through all the labeled instructions in p
            */

          foldM(
            (acc:AbstractEnv, li:LabeledInstr) => li match {
              /**
                * case l:t <- src:   s_l = join(s_l) - {t} \cup vars(src)
                */
              case (label, IMove(Temp(AVar(t)), src)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states - t union vars(src).toSet)))
              }
              /**
                * case l: t <- src1 op src2:  s_l = join(s_l) - {t} \cup vars(src1) \cup vars(src2)
                */
              // Task 2.2
              case (label, IPlus(Temp(AVar(t)), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states - t union vars(src1).toSet union vars(src2).toSet)))
              }

              case (label, IMinus(Temp(AVar(t)), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states - t union vars(src1).toSet union vars(src2).toSet)))
              }

              case (label, IMult(Temp(AVar(t)), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states - t union vars(src1).toSet union vars(src2).toSet)))
              }

              case (label, IDEqual(Temp(AVar(t)), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states - t union vars(src1).toSet union vars(src2).toSet)))
              }

              case (label, ILThan(Temp(AVar(t)), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states - t union vars(src1).toSet union vars(src2).toSet)))
              }

              /**
                * case l:r <- src:   s_l = join(s_l) \cup vars(src)
                */
              case (label, IMove(Regstr(n), src)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states union vars(src).toSet)))
              }              
              /**
                * case l: r <- src1 op src2:  s_l = join(s_l) \cup vars(src1) \cup vars(src2)
                */
              case (label, IPlus(Regstr(n), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states union vars(src1).toSet union vars(src2).toSet)))
              }

              case (label, IMinus(Regstr(n), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states union vars(src1).toSet union vars(src2).toSet)))
              }

              case (label, IMult(Regstr(n), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states union vars(src1).toSet union vars(src2).toSet)))
              }

              case (label, IDEqual(Regstr(n), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states union vars(src1).toSet union vars(src2).toSet)))
              }
              
              case (label, ILThan(Regstr(n), src1, src2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states union vars(src1).toSet union vars(src2).toSet)))
              }
              /**
                * case l: ifn t goto l':  s_l = join(s_l) \cup {t}
                */
              case (label, IIfNot(Temp(AVar(t)), label2)) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> (joined_succs_states + t)))
              }
              /**
                * other cases: s_l = join(s_l)
                */
              case (label, _) => {
                val joined_succs_states = joinSuccStates(label, acc)
                Right(acc + (label -> joined_succs_states)):Either[String, AbstractEnv]
              }
            })(absEnv)(p)
        }
    }


    /**
      * Top level function for liveness analysis 
      * Peform liveness analysis over a PA program `p` return an abstract environment mapping label to abstract states
      *   Each abstract state is set of variable names
      *
      * @param p
      * @param i
      * @return
      */
    def analyze(p:List[LabeledInstr])(using i:CompleteLattice[AbstractEnv]):Either[String, AbstractEnv] = {
      val f = genMonotoneFunction(p)
      val labels = p.map( li => li match {case (l,_) => l})
      val init_abstract_state:AbstractState = Set()
      val init_abstract_env:AbstractEnv = labels.map( l => (l, init_abstract_state)).toMap
      i.naiveFP(f)(init_abstract_env)
    }

}