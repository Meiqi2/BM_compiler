package sutd.compiler.simp.backend

import org.objectweb.asm.ClassWriter
import org.objectweb.asm.Opcodes
import java.io.FileOutputStream
import org.objectweb.asm.MethodVisitor

import sutd.compiler.simp.ir.PseudoAssembly.*
import sutd.compiler.simp.monad.Monad.{given, *}
import sutd.compiler.simp.monad.StateT.{given, *}
import sutd.compiler.simp.monad.error.StateTMonadError.{given, *}
import sutd.compiler.simp.semantic.Util.* 

import org.objectweb.asm.ClassVisitor
import org.objectweb.asm.Opcodes


/**
  * implementation of the JVM code generator
  * 
  * It defers from the notes in the following. 
  * 
  * Due to the api limitation of the org.objectweb.asm.ClassVisitor being a JAVA object
  * we need to implement the code generator as a function with effect, i.e. return MVStateMonad[Unit] 
  * instead of return a list of JVM instructions. 
  * 
  * In this implementation, each call to convert function return MVStateMonad[Unit] must be strictly 
  * ordered in order to ensure the correct sequence of JVM instructions being generated.
  */

object JVM {

    import Instr.* 
    import Opr.*

    /**
      * MethodVisitor state object
      */
    case class MVStateInfo(ended:Boolean, mv:MethodVisitor, cw:ClassWriter)

    /**
      * initialize the class writer and method visitor to main() method
      *
      * @return
      */
    def init_mv_stateInfo():MVStateInfo = {
        val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES) // cOMPUTE_MAXS automatically compute stack size, COMPUTE_FRAMES automatically compute the stackmap
        // val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS) // cOMPUTE_MAXS automatically compute stack size, COMPUTE_FRAMES automatically compute the stackmap
        cw.visit(Opcodes.V1_8, Opcodes.ACC_PUBLIC, "GeneratedClass", null, "java/lang/Object", null)   
        val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_STATIC, "main", "([Ljava/lang/String;)V", null, null)
        mv.visitCode()
        // int input = parseInt(argv[0])
        mv.visitVarInsn(Opcodes.ALOAD, 0) // load 0 param, i.e. this
        mv.visitInsn(Opcodes.ICONST_0)    // load  argv 0
        mv.visitInsn(Opcodes.AALOAD)
        mv.visitMethodInsn(Opcodes.INVOKESTATIC, "java/lang/Integer", "parseInt", "(Ljava/lang/String;)I", false)
        mv.visitVarInsn(Opcodes.ISTORE, 1) // store it at local var 1, i.e input
        MVStateInfo(false, mv, cw)
    }

    trait StateMVMonadError[S] extends StateMonadError[S] {

    }

    given stateMVMonadError[S]:StateMVMonadError[S] = new StateMVMonadError[S]{}


    /**
      * MethodVisitor State Case class (with the run function etc.)
      */
    type MVState[A] = StateT[MVStateInfo, EitherM[String], A]

    def get: StateT[MVStateInfo, EitherM[String], MVStateInfo] = StateT{ st => Right(st, st) }
    def put(st:MVStateInfo): StateT[MVStateInfo, EitherM[String], Unit] = StateT{ _ => Right(st, ())}
    
    /** 
     * end the method visitor and close the class writer
     * */
    def end:MVState[Unit] = for {
        st <- get
        _  <- st match {
                case MVStateInfo(ended, mv, cw) => {
                    mv.visitMaxs(0, 0)
                    mv.visitEnd()
                    cw.visitEnd()
                    put(st.copy(ended=true, mv=mv, cw=cw))
                }
            }
    } yield ()
    
    /**
      * retrieve the method visitor from the state info object
      *
      * @return
      */
    def getMV: StateT[MVStateInfo, EitherM[String], MethodVisitor] = StateT{ st => st match {
        case MVStateInfo(true, mv, cw) => Left("getMV failed. Method Visitor has been ended.")
        case MVStateInfo(ended, mv, cw) => Right((st, mv))
    }}

    /**
      * the L environment.
      * It differs from the note as follows.
      *   1. It is not a set of PA labels
      *   2. It is a mapping from PA labels to JVM Labels 
      */
    type L = Map[Label, org.objectweb.asm.Label]

    // the mapping from temporary variable names to JVM local variable slot 1,...n
    type M = Map[String, Int]


    /**
      * convert a PA label `lbl`
      * 
      *
      * @param lenv
      * @param lbl
      * @param m
      * @return
      */
    def convertLabel(lenv:L, lbl:Label)(using m:StateMVMonadError[MVStateInfo]):MVState[Unit] = lenv.get(lbl) match {
        /**
          *            l \not \in L 
          * (jLabel1) ---------------
          *            L |- l => []
          */
        case None => m.pure(())
        /**
          *            (l, jvm_l) \in L   
          * (jLabel2) ---------------------
          *           L |- l => [ilabel jvm_l]  
          * 
          */
        case Some(jvm_lbl) =>
            for {
                mv <- getMV
                _  <- m.pure({
                    mv.visitLabel(jvm_lbl)
                })
            } yield ()
    }

    /**
      * covert a PA operand
      *
      * @param menv
      * @param opr
      * @param m
      * @return
      */
    def convertOpr(menv:M, opr:Opr)(using m:StateMVMonadError[MVStateInfo]):MVState[Unit] = opr match {
        /**
          * 
          * (jConst) M |- c => [sipush c]
          *           
          */
        case IntLit(c) => for {
            mv <- getMV
            _  <- m.pure({
                mv.visitIntInsn(Opcodes.SIPUSH, c)
            })
        } yield()
        /**
          * (jVar) M |- t => [iload M(t)]
          */
        case Temp(AVar(t)) => menv.get(t) match  {
            case None => m.raiseError(s"convertOpr failed: temp variable ${t} is allocated to any local variable slot.")
            case Some(jvar) => for {
                mv <- getMV 
                _ <- m.pure({
                    mv.visitVarInsn(Opcodes.ILOAD, jvar)
                })
            } yield ()
        } 
        case Regstr(name) => m.raiseError(s"convertOpr failed: register ${name} should not appear as an operands in Pseudo Assembly.")
    }

    /**
      * converting a sequence of PA labeled instructions
      *
      * @param menv
      * @param lenv
      * @param lis
      * @param m
      * @return
      */
    def convertInstr(menv:M, lenv:L, lis:List[LabeledInstr])(using m:StateMVMonadError[MVStateInfo]):MVState[Unit] = lis match {
        /**
            * 
            *           L |- l1 => jis0    M |- s => jis1    
            * (jReturn) --------------------------------------------------------------------
            *           M, L |- l1 : rret <- s;  l2 : ret  => jis0 + jis1 + [print s; return]
            */
        case ((l1, IMove(Regstr("_r_ret"), src))::(l2, IRet)::Nil) => for {
            _  <- convertLabel(lenv, l1)
            _  <- convertOpr(menv, src)
            mv <- getMV
            // the original (jReturn) in the note
            // _  <- m.pure(mv.visitInsn(Opcodes.RETURN))
            // the updated (jReturn) 
            _  <- src match {
              case Temp(AVar(t)) => menv.get(t) match {
                case Some(js) => m.pure({
                  // println(s);
                  mv.visitFieldInsn(Opcodes.GETSTATIC, "java/lang/System", "out", "Ljava/io/PrintStream;")
                  mv.visitVarInsn(Opcodes.ILOAD, js) 
                  mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/io/PrintStream", "println", "(I)V", false)
                  // return;
                  mv.visitInsn(Opcodes.RETURN)
                })
                case None => m.raiseError(s"convertInstr failed: temp variable ${t} is not mapped to any jvm local variable.")
              }
              case Regstr(name) => m.raiseError(s"convertOpr failed: register ${name} should not appear as an operands in Pseudo Assembly.")
              case IntLit(v) => m.raiseError(s"convertOpr failed: integer constant ${v} should not appear as an operands of return in Pseudo Assembly.")
            }
            _  <- end // must end
        } yield ()
        /**
            * 
            *          L |- l => jis0      M |- s => jis1       M,L |- lis => jis2
            * (jMove)  -----------------------------------------------------------------
            *          M, L |- l : t <- s ; lis  => jis0 + jis1 + [istore M(t)] + jis2
            * 
            */
        case ((l, IMove(Temp(AVar(t)), src))::lis) => menv.get(t) match  {
            case None => m.raiseError(s"convertInstr failed: temp variable ${t} is not mapped to any jvm local variable.")
            case Some(j_var) => for {
            _  <- convertLabel(lenv, l)
            _  <- convertOpr(menv, src)
            mv <- getMV 
            _  <- m.pure(mv.visitVarInsn(Opcodes.ISTORE, j_var))
            _  <- convertInstr(menv, lenv, lis)
            } yield ()
        }

        /**
            * 
            *         L |- l => jis0    M |- s1 => jis1  M |- s2 => jis2   M,L |- lis => jis3
            * (jAdd)  -----------------------------------------------------------------------
            *         M, L |- l : t <- s1 + s2; lis => jis0 + jis1 + jis2 + [iadd, istore M(t)] + jis3
            * 
            */
        case ((l, IPlus(Temp(AVar(t)), src1, src2))::lis) => menv.get(t) match  {
            case None => m.raiseError(s"convertInstr failed: temp variable ${t} is not mapped to any jvm local variable.")
            case Some(jvar) => for {
                _  <- convertLabel(lenv, l)
                _  <- convertOpr(menv, src1)
                _  <- convertOpr(menv, src2)
                mv <- getMV
                _  <- m.pure(mv.visitInsn(Opcodes.IADD))
                _  <- m.pure(mv.visitVarInsn(Opcodes.ISTORE, jvar))
                _  <- convertInstr(menv, lenv, lis)
            } yield ()
        }
        
        // TODO Task 3
        // TODO this case is missing
        /**
            *
            *         L |- l => jis0    M |- s1 => jis1  M |- s2 => jis2   M,L |- lis => jis3
            * (jSub) -----------------------------------------------------------------------
            *         M, L |- l : t <- s1 - s2; lis => jis0 + jis1 + jis2 + [isub, istore M(t)] + jis3
            *
            */
        case ((l, IMinus(Temp(AVar(t)), src1, src2))::lis) => menv.get(t) match  {
            case None => m.raiseError(s"convertInstr failed: temp variable ${t} is not mapped to any jvm local variable.")
            case Some(jvar) => for {
                _  <- convertLabel(lenv, l)
                _  <- convertOpr(menv, src1)
                _  <- convertOpr(menv, src2)
                mv <- getMV
                _  <- m.pure(mv.visitInsn(Opcodes.ISUB))
                _  <- m.pure(mv.visitVarInsn(Opcodes.ISTORE, jvar))
                _  <- convertInstr(menv, lenv, lis)
            } yield ()
        }

        // TODO Task 3
        // TODO this case is missing
        /**
            *
            *         L |- l => jis0    M |- s1 => jis1  M |- s2 => jis2   M,L |- lis => jis3
            * (jMult) -----------------------------------------------------------------------
            *         M, L |- l : t <- s1 *s2; lis => jis0 + jis1 + jis2 + [imul, istore M(t)] + jis3
            *
            */
        case ((l, IMult(Temp(AVar(t)), src1, src2))::lis) => menv.get(t) match  {
            case None => m.raiseError(s"convertInstr failed: temp variable ${t} is not mapped to any jvm local variable.")
            case Some(jvar) => for {
                _  <- convertLabel(lenv, l)
                _  <- convertOpr(menv, src1)
                _  <- convertOpr(menv, src2)
                mv <- getMV
                _  <- m.pure(mv.visitInsn(Opcodes.IMUL))
                _  <- m.pure(mv.visitVarInsn(Opcodes.ISTORE, jvar))
                _  <- convertInstr(menv, lenv, lis)
            } yield ()
        }
        
        /**
            * 
            *         L |- l1 => jis0    M |- s1 => jis1  M |- s2 => jis2   M,L |- lis => jis3
            * (jEq) ----------------------------------------------------------------------------------------------------
            *         M, L |- l1:t <- s1 == s2; l2: ifn t got l3; lis => jis0 + jis1 + jis2 + [if_icmpne L(l3)] + jis3
            * 
            */
        case ((l1, IDEqual(Temp(AVar(t)), src1, src2))::(l2, IIfNot(Temp(AVar(t2)), l3))::lis) if t == t2 => lenv.get(l3) match {
            case None => m.raiseError(s"")
            case Some(jl3) => for {
                _  <- convertLabel(lenv, l1)
                _  <- convertOpr(menv, src1)
                _  <- convertOpr(menv, src2)
                mv <- getMV
                _  <- m.pure(mv.visitJumpInsn(Opcodes.IF_ICMPNE, jl3))
                _  <- convertInstr(menv, lenv, lis)
            } yield ()
        } 

        // TODO Task 3
        // TODO this case is missing
        /**
            *
            *         L |- l1 => jis0    M |- s1 => jis1  M |- s2 => jis2   M,L |- lis => jis3
            * (jLThan) ----------------------------------------------------------------------------------------------------
            *         M, L |- l1:t <- s1 < s2; l2: ifn t got l3; lis => jis0 + jis1 + jis2 + [if_icmpge L(l3)] + jis3
            *
            */
        case ((l1, ILThan(Temp(AVar(t)), src1, src2))::(l2, IIfNot(Temp(AVar(t2)), l3))::lis) if t == t2 => lenv.get(l3) match {
            case None => m.raiseError(s"convertInstr failed: label ${l3} is not mapped to jvm label.")
            case Some(jl3) => for {
                _  <- convertLabel(lenv, l1)
                _  <- convertOpr(menv, src1)
                _  <- convertOpr(menv, src2)
                mv <- getMV
                _  <- m.pure(mv.visitJumpInsn(Opcodes.IF_ICMPGE, jl3))
                _  <- convertInstr(menv, lenv, lis)
            } yield ()
        }

        /**
            * 
            *          L |- i1 => jis0     M, L |- lis => jis1
            * (jGoto) ----------------------------------------------------------
            *          M, L |- l1: goto l2; lis => jis0 + [igoto L(l2)] + jis1
            * 
            */
        case ((l1, IGoto(l2))::lis) => lenv.get(l2) match {
            case None => m.raiseError(s"convertInstr failed: label ${l2} is not mapped to jvm label.")
            case Some(jl2) => for {
                _  <- convertLabel(lenv, l1)
                mv <- getMV
                _  <- m.pure(mv.visitJumpInsn(Opcodes.GOTO, jl2))
                _  <- convertInstr(menv, lenv, lis)
            } yield ()
        }

        case other => m.raiseError(
            s"convertInstr failed: unsupported instruction ${other}"
        )
    
    }

    /**
      * generate the list of useful labels and mapping them to JVM labels
      *
      * @param lis
      * @return
      */
    def generateLEnv(lis:List[LabeledInstr]):L = {
        def getGotoLabels(lis:List[LabeledInstr]):List[Label] = lis.flatMap( li => li match {
            case (_,instr) => instr match {
            case IRet => List() 
            case IDEqual(dest, src1, src2) => List() 
            case IGoto(dest) => List(dest)
            case IIfNot(cond, dest) => List(dest) 
            case ILThan(dest, src1, src2) => List()
            case IMinus(dest, src1, src2) => List()
            case IMove(dest, src) => List()
            case IMult(dest, src1, src2) => List()
            case IPlus(dest, src1, src2) => List()
            }
        }).toSet.toList.sorted 
        val paLabels = getGotoLabels(lis)
        paLabels.map( plbl => (plbl, new org.objectweb.asm.Label())).toMap
    }

    /**
      * generate the PA variables to JVM variables
      *
      * @param lis
      * @return
      */
    def generateMEnv(lis:List[LabeledInstr]):M = {
        val vars_exclude_input = allVars(lis).filter( x => x != "input")
        // place "input" as the first local vars so that it is always mapped to 1
        val vars = List("input") ++ vars_exclude_input 
        // local vars start from 1, 0 is reserved for this.
        vars.zip((1 to vars.length)).toMap
    }


    /**
      * Top level functoin to generate the target code
      *
      * @param lis
      * @return either an unit () or an error message.
      */
    def genTargetCode(lis:List[LabeledInstr]):Either[String, Unit] = {
        val menv = generateMEnv(lis)
        val lenv = generateLEnv(lis)
        val init = init_mv_stateInfo()
        convertInstr(menv,lenv, lis) match {
          case StateT(run) => run(init) match {
            case Left(err) => Left(err) 
            case Right((mvstinfo, ())) => mvstinfo match {
              case MVStateInfo(ended, mv, cw) if ended => {
                val bytes = cw.toByteArray()
                try {
                    val stream = new FileOutputStream("GeneratedClass.class")
                    stream.write(bytes)
                    Right(())
                } catch { 
                    case (e:Exception) => {
                        e.printStackTrace()
                        Left(s"genTargetCode failed: ${e.toString()}")
                    }
                }
              }
              case MVStateInfo(ended, mv, cw) => {
                Left(s"genTargetCode failed: the method visitor is still open.")
              }
            } 
          }
        }
    }


}