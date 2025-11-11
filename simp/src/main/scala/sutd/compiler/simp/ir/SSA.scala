package sutd.compiler.simp.ir



import sutd.compiler.simp.ir.PseudoAssembly.*
import sutd.compiler.simp.ir.CFG.*
import sutd.compiler.simp.ir.DF.*
import sutd.compiler.simp.monad.Monad.*

// unstructured SSA
object SSA {

    type SSALabeledInstr = (Label, List[PhiAssignment], Instr)
    import Instr.*
    import Opr.*

    case class PhiAssignment(dest:Opr, operands:List[(Label,AVar)], stem:Opr)

    // SSA construction using Cytron's algorithm
    // In the notes the SSA construction is divided into two steps, 1. inserting phi assignment 2. renaming  variable.
    // 

    def buildSSA(pa:List[LabeledInstr]):Either[String, List[SSALabeledInstr]] = { 
        val cfg  = buildCFG(pa)
        for {        
            dt   <- buildDomTree(cfg, 1)
            dft  = buildDFT(dt, cfg)
            // for each Labeled Instr convert it to SSA Labeled Instr by adding empty phi assignments
            p    = insertPhis(pa, dft, cfg)
            q    <- convDTree(Map(), dt, p, cfg)
        } yield { 
            q.toList
            .sortBy( p => p match { case (l, ssali) => l })
            .map( p => p match { case (l, ssali) => ssali })
        }
    }

    // Part 1 insert Phi assignments
    // E environment, mapping a label l  to a list of variables that should have phi-assignments in l
    type E = Map[Label, List[String]]
    // P Enivronment, mapping a label l to a ssa labeled instruction
    type P = Map[Label, SSALabeledInstr]

    /** 
      * generate a raw SSA program from a Pseudo Assembly program pa, variables are yet to be renamed
      *
      * @param pa
      * @param dft
      * @param g
      * @return
      */
    def insertPhis(pa:List[LabeledInstr], dft:DFTable, g:CFG):P = {
        // A list of pairs. Each pair consists of a label l and the set of variables that are modified in l
        val labels_modded_vars:List[(Label, List[String])] = pa.map( li => modVars(li))
        // Task 1.2 TODO
        // Build E environment: for each variable v modified at label l, add v to all labels in DF+(l)
        val e:E = labels_modded_vars.foldLeft(Map():E)((acc, pair) => pair match {
            case (label, vars) => vars.foldLeft(acc)((acc2, v) => {
                val df_plus = dfPlus(dft, List(label))
                df_plus.foldLeft(acc2)((acc3, l) => {
                    val existing = acc3.getOrElse(l, Nil)
                    acc3 + (l -> (existing ++ List(v)).distinct)
                })
            })
        })

        // Build pa_with_phis: for each label instruction, add phi assignments for variables in E
        val pa_with_phis:List[SSALabeledInstr] = pa.map(li => li match {
            case (label, instr) => {
                val vars_need_phi = e.getOrElse(label, Nil)
                val phis = vars_need_phi.map(v => {
                    val preds = predecessors(g, label)
                    val operands = preds.map(pred => (pred, AVar(v)))
                    PhiAssignment(Temp(AVar(v)), operands, Temp(AVar(v)))
                })
                (label, phis, instr)
            }
        })

        val p = pa_with_phis.foldLeft(Map():P)((acc:P, li:SSALabeledInstr) => li match {
            case (l, phis, i) =>  acc + (l -> li)
        })
        p
    }

    def modVars(li:LabeledInstr):(Label, List[String]) = li match {
        case (label, IMove(Temp(AVar(n)),_)) => (label, List(n)) 
        case (label, IPlus(Temp(AVar(n)),_,_)) => (label, List(n)) 
        case (label, IMinus(Temp(AVar(n)),_,_)) =>  (label, List(n))  
        case (label, IMult(Temp(AVar(n)),_,_)) =>  (label, List(n)) 
        case (label, IDEqual(Temp(AVar(n)),_,_)) =>  (label, List(n)) 
        case (label, ILThan(Temp(AVar(n)),_,_)) =>  (label, List(n)) 
        case (label, _) => (label, Nil) 
    }
     

    // Part 2 variable renaming 

    // As we are using FP for the implementation, the 2nd step of cytron's algorithm presented in the notes an be 
    // simplified w/o using explicit (user defined) stacks.
    // The differeces are summarized as
    //
    //      notes                                                   FP implementation 
    //-----|------------------------------------------------------|-------------------------------------------
    // K   | mapping from var to stack of numbers                 | mapping from var to latest number 
    // vars| local set of varables to be popped at the end of     | local set of variables (no need to pop)


    /**
     * K - as above
     * P - the PA SSA program (mapping from label to label instructions)
     * G - the CFG
     * 
     * K, P(l) |- K', li          P^0 = P oplus (l, li)
     * for i in [0,n], (l, succ_i) in G, we have  K', P^i(succ_i) |-phi_rhs li_i, P^{i+1} = P^i oplus (succ_i, li_i)
     * for j in [0,k], ch_j in chs, we have  K', ch_j, P^{n+j}, G |- P^{n+j+1}
     * -------------------------------------------------------------------------------------------- (DTree)
     * K, Node(l,chs), P, G |- P^{n+k} 
    */

    type K = Map[String, Int]
    type Vars = Set[AVar]

    // type G = CFG
    
    import DomTree.*
    def convDTree(k:K, dt:DomTree, p:P, g:CFG):Either[String,P] = dt match {
        case Empty => Right(p)
        case Node(l, children) => p.get(l) match {
            case None => Left(s"buildSSA failed. Label ${l} is not found.")
            case Some(li) => for {
                (k_p, li_p) <- convInstr(k, li)
                p0 = p + (l -> li_p)
                succs = successors(g, l)
                pnj   <- foldM((acc:P, succ:Label) => acc.get(succ) match {
                        case None => Left(s"convDTree failed: node ${l}'s child ${succ} does not exists.") // this should not happen
                        case Some(li) => for { 
                            li_p <- convPhiRhs(k_p, li, l)
                            acc_next = acc + (succ -> li_p)
                        } yield acc_next
                    })(p0)(succs)
                pnm   <- foldM((acc:P, child:DomTree) => convDTree(k_p, child, acc, g))(pnj)(children)
            } yield pnm
        } 
    }
    
    /**
      * converting a labeled instruction  
      *
      * @param k
      * @param i
      * @return
      */
    import Opr.*
    def convInstr(k:K, i:SSALabeledInstr):Either[String, (K, SSALabeledInstr)] = i match {
        case (label, phis, IMove(IntLit(v), s)) => Left(s"convInstr failed. Int literal appears as the LHS of the IMove.")
        case (label, phis, IPlus(IntLit(v), s1, s2)) => Left(s"convInstr failed. Int literal appears as the LHS of the IPlus.")
        case (label, phis, IMinus(IntLit(v), s1, s2)) => Left(s"convInstr failed. Int literal appears as the LHS of the IMinus.")
        case (label, phis, IMult(IntLit(v), s1, s2)) => Left(s"convInstr failed. Int literal appears as the LHS of the IMult.")
        case (label, phis, IDEqual(IntLit(v), s1, s2)) => Left(s"convInstr failed. Int literal appears as the LHS of the IDEqual.")
        case (label, phis, ILThan(IntLit(v), s1, s2)) => Left(s"convInstr failed. Int literal appears as the LHS of the ILThan.")

        /**
          * K, phis |-phi_lhs K', phis'   s' = ren(K', s)
          * ---------------------------------------- (reg1)
          * K, l:phis r <-s |- K', l:phis' r <- s'
          */
        case (label, phis, IMove(Regstr(r), s)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s_p <- ren(k_p, s)
        } yield (k_p, (label, phis_p, IMove(Regstr(r), s_p)))

        /**
          * K, phis |-phi_lhs K', phis'   s1' = ren(K',s1) s2' = ren(K', s2)
          * -------------------------------------------------------------- (reg2)
          * K, l:phis r <-s1 op s2 |- K', l:phis' r <- s1' op s2'
          */
        case (label, phis, IPlus(Regstr(r), s1, s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
        } yield (k_p, (label, phis_p, IPlus(Regstr(r), s1_p, s2_p)))

        case (label, phis, IMinus(Regstr(r), s1, s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
        } yield (k_p, (label, phis_p, IMinus(Regstr(r), s1_p, s2_p)))
        
        case (label, phis, IMult(Regstr(r), s1, s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
        } yield (k_p, (label, phis_p, IMult(Regstr(r), s1_p, s2_p)))
        
        case (label, phis, IDEqual(Regstr(r), s1, s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
        } yield (k_p, (label, phis_p, IDEqual(Regstr(r), s1_p, s2_p)))

        case (label, phis, ILThan(Regstr(r), s1, s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
        } yield (k_p, (label, phis_p, ILThan(Regstr(r), s1_p, s2_p)))        
        /**
          * K, phis |-phi_lhs K', phis'   s' = ren(K', s)
          * K'' = K' oplus (t, K(t)+1)    t_i = ren(K'', t)
          * ---------------------------------------- (TVar1)
          * K, l:phis t <-s |- K'', l:phis' t_i <- s'
          */
        case (label, phis, IMove(Temp(AVar(n)), s)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s_p <- ren(k_p, s)
            k_pp <- incr(k_p, n)
            t_i <- ren(k_pp, Temp(AVar(n)))
        } yield (k_pp, (label, phis_p, IMove(t_i, s_p)))
        /**
          * K, phis |-phi_lhs K', phis'   s1' = ren(K', s1)   s2' = ren(K', s2)
          * K'' = K' oplus (t, K(t)+1)    t_i = ren(K'', t)
          * ---------------------------------------- (TVar2)
          * K, l:phis t <-s1 op s2 |- K'', l:phis' t_i <- s1' op s2'
          */
        case (label, phis, IPlus(Temp(AVar(n)), s1 , s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
            k_pp <- incr(k_p, n)
            t_i <- ren(k_pp, Temp(AVar(n)))
        } yield (k_pp, (label, phis_p, IPlus(t_i, s1_p, s2_p)))

        case (label, phis, IMinus(Temp(AVar(n)), s1 , s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
            k_pp <- incr(k_p, n)
            t_i <- ren(k_pp, Temp(AVar(n)))
        } yield (k_pp, (label, phis_p, IMinus(t_i, s1_p, s2_p)))      

        case (label, phis, IMult(Temp(AVar(n)), s1 , s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
            k_pp <- incr(k_p, n)
            t_i <- ren(k_pp, Temp(AVar(n)))
        } yield (k_pp, (label, phis_p, IMult(t_i, s1_p, s2_p)))    

        case (label, phis, IDEqual(Temp(AVar(n)), s1 , s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
            k_pp <- incr(k_p, n)
            t_i <- ren(k_pp, Temp(AVar(n)))
        } yield (k_pp, (label, phis_p, IDEqual(t_i, s1_p, s2_p)))    

        case (label, phis, ILThan(Temp(AVar(n)), s1 , s2)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            s1_p <- ren(k_p, s1)
            s2_p <- ren(k_p, s2)
            k_pp <- incr(k_p, n)
            t_i <- ren(k_pp, Temp(AVar(n)))
        } yield (k_pp, (label, phis_p, ILThan(t_i, s1_p, s2_p)))

        /**
          * K, phis |-phi_lhs K', phis' 
          * ----------------------------------------- (Goto)
          * K, l: phis goto l' |- K', l:phis' goto l'
          */

        case (label, phis, IGoto(m)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
        } yield (k_p, (label, phis_p, IGoto(m)))

        /**
          * K, phis |-phi_lhs K', phis'    t' = ren(K', t)
          * ----------------------------------------------- (IfNGoto)
          * K, l: phis ifn t goto l' |- K', l:phis' goto l'
          */

        case (label, phis, IIfNot(t, m)) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
            t_p <- ren(k_p, t)
        } yield (k_p, (label, phis_p, IIfNot(t_p, m)))

        /**
          * K, phis |-phi_lhs K', phis' 
          * ----------------------------------------- (Ret)
          * K, l: phis ret |- K', l:phis' ret
          */

        case (label, phis, IRet) => for {
            (k_p, phis_p) <- convPhiLhs(k, phis)
        } yield (k_p, (label, phis_p, IRet))
        
        
    }


    /**
      * increment the counter under name in k by 1
      *
      * @param k
      * @param name
      * @return
      */
    def incr(k:K, name:String):Either[String, K] = k.get(name) match {
        case None =>  Right(k + (name -> 1))
        case Some(i) => Right(k + (name -> (i + 1)))
    }


    /**
      * convert the LHS of the phi assignments
      *  
      * ---------------------------------(PLhsPhi1)
      * K, [] |-  K, []
      * 
      * K' = K oplus (x -> K(x) + 1)
      * K', phis |- K'', phis'
      * ---------------------------------------------------------------------------(PLhsPhi2)
      * K, x = phi(l1:x1, l2:x2); phis |-  K'', x_i = phi(l1:x1, l2:x2); phis'
      * 
      * Note that we do not rename the RHS operands of the phi assignments, which is handled in the PRhs rules.
      * 
      * @param k
      * @param phis
      * @return
      */
    def convPhiLhs(k:K, phis:List[PhiAssignment]):Either[String, (K, List[PhiAssignment])] = {
        val acc0 = (k, Nil)
        foldM((acc:(K,List[PhiAssignment]), phi:PhiAssignment) => acc match {
            case (k1, phis1) => phi match {
                case PhiAssignment(x, operands, stem) => x match {
                    case IntLit(v) => Left(s"convPhis failed. Integer literal appears in the LHS of the phi assignment.")
                    case Regstr(name) => Left(s"convPhis failed. Register ${name} appears in the LHS of the phi assignment.")
                    case Temp(AVar(name)) => for {
                            k2 <- incr(k1, name)
                            x_i <- ren(k2, x)
                    } yield (k2, phis1 ++ List(PhiAssignment(x_i, operands, stem))) 
                }
            }
        })(acc0)(phis) match {
            case Left(err) => Left(err)
            case Right((k2,phis2)) => Right((k2, phis2.sortBy(phi => phi match {
                case PhiAssignment(dest, operands, stem) => stem
            })))
        }
    }

    /**
      * convert the RHS of the phi assignments in labeled instruction li
      * 
      * K, phis, l |-phi_rhs phis'
      * ------------------------------------------(PRhs)
      * K, l: phis i, l' |-phi_rhs l: phis' i
      *
      * @param k - K environment
      * @param li - SSA labeled instruction
      * @param l - predecesor's label
      * @return
      */
    def convPhiRhs(k:K, li:SSALabeledInstr, l:Label):Either[String, SSALabeledInstr] = li match {
        case (label, phis, instr) => for  {
            /**
              * --------------------------------- (PPhiRhs1)
              * K, [] |- K, []
              * 
              * K, phis, l1 |- phis'   x1' = ren(K,x1)
              * ---------------------------------------------------------------------- (PPhiRhs2)
              * K, x = phi(l1:x1, l2:x2); phis, l1 |- x = phi(l1:x1', l2:x2); phis'
              * 
              * 
              * K, phis, l2 |- phis'   x2' = ren(K,x2)
              * ---------------------------------------------------------------------- (PPhiRhs3)
              * K, x = phi(l1:x1, l2:x2); phis, l2 |- x = phi(l1:x1, l2:x2'); phis'
              * 
              * stem(x) \not in dom(K)
              * ---------------------------------------------------------------------- (PPhiRhs4)
              * K, x = phi(l1:x1, l2:x2); phis, l3 |- x = phi(l1:x1, l2:x2'); phis'
              * 
              */
            phis_p <- foldM((acc_phis:List[PhiAssignment], phi:PhiAssignment) => phi match {
                case PhiAssignment(_, operands, Temp(AVar(n))) if !k.keySet.contains(n) => {
                    Right(acc_phis) // (PPhiRhs4) case 
                }
                case PhiAssignment(x, operands, stem) => for {
                    operands_p <- foldM((acc_operands:List[(Label,AVar)], p:(Label,AVar)) =>  p match {
                        case (m, avar) if m == l => for {
                            avar_p <- ren(k, avar)
                        } yield acc_operands ++ List((m, avar_p))
                        case (m, avar) => Right(acc_operands ++ List((m, avar)))
                    })(Nil)(operands)
                } yield { 
                    val operands_p_sorted = operands_p.sortBy( operand => operand match {
                        case (label, avar) => label
                    })
                    (acc_phis ++ List(PhiAssignment(x, operands_p_sorted, stem)))
                }                
            })(Nil)(phis)
        } yield (label, phis_p, instr)
    }



    /**
      * rename an operand
      *
      * @param k
      * @param s
      * @return
      */
    def ren(k:K, s:Opr):Either[String, Opr] = s match {
        case IntLit(v) => Right(IntLit(v))
        case Regstr(name) => Right(Regstr(name))
        case Temp(avar) => for {
            avar_p <- ren(k, avar)
        } yield Temp(avar_p)
    }

    def ren(k:K, av:AVar):Either[String, AVar] = av match {
        case AVar("input") => Right(av)
        case AVar(n) => k.get(n) match {
            case None => Left(s"renaming failed. temp variable ${n} is not found in the K environment ${k}.")
            case Some(i) => Right(AVar(s"${n}_${i}"))
        }
    }



    
    // SSA destruction

    def destructSSA(p:List[SSALabeledInstr]):Either[String, List[LabeledInstr]] = {
        val q = phiMigrate(p)
        label(q)
    }

    // phi migration

    def phiMigrate(p:List[SSALabeledInstr]):List[LabeledInstr] = {
        // for each l: phis i in P, append l: i to Q
        val q:List[LabeledInstr] = p.map(li => li match {
            case (l, phis, i) => (l,i)
        })
        // for each l: phis i in P
            // for each x = phi(l1:x1, l2:x2) in phis, append l1: x = x1 and l2: x = x2 to q
        val q1:List[LabeledInstr] = p.foldLeft(q)( (acc, li) => li match {
            case (l, phis, i) => phis.foldLeft(acc)( (acc1, phi:PhiAssignment) => phi match {
                case PhiAssignment(d, oprs, stem) => acc1 ++ (oprs.map( lv => lv match {
                    case (label, avar) => (label, IMove(d, Temp(avar)))
                }))
            })
        })
        // scala list sortBy is stable
        q1.sortBy(li => li match { case (label, i) => label})
    }

    // relabeling
    // precondition, p is sorted according to label
    //               labels in p might not be unique
    def label(p:List[LabeledInstr]):Either[String, List[LabeledInstr]] = {
        
        // new labels
        val newLabels = (1 to p.length).toList
        val oldLabels = p.map( li => li match { case (l, i) => l})
        // generate mapping from old label to new label
        val m:Map[Label, Label] = newLabels.zip(oldLabels).toMap

        def go(li:LabeledInstr):Either[String, LabeledInstr] = li match {
            case (label, i) => m.get(label) match {
                case None => Left(s"relabelling error: ${label} not found.")
                case Some(newLabel) => label_instr(i, m) match {
                    case Left(err) => Left(err)
                    case Right(j) => Right((newLabel, j))
                }
            }  
        }
        foldM((acc:List[LabeledInstr], li:LabeledInstr) => for {
            li1 <- go(li)
            } yield acc ++ List(li1))(Nil)(p)
    }

    def label_instr(i:Instr, m:Map[Label,Label]):Either[String, Instr] = i match {
        case IGoto(dest) => m.get(dest) match {
            case None => Left(s"relabelling error: ${dest} not found.")
            case Some(dest1) => Right(IGoto(dest1))
        }
        case IIfNot(cond, dest) => m.get(dest) match {
            case None => Left(s"relabelling error: ${dest} not found.")
            case Some(dest1) => Right(IIfNot(cond, dest1))
        }
        case _ => Right(i)
    }


    given oprOrdering(using so:Ordering[String]):Ordering[Opr] = new Ordering[Opr] {
        def compare(x: Opr, y: Opr): Int = (x, y) match {
            case (Temp(AVar(t1)), Temp(AVar(t2))) => so.compare(t1,t2)
            case (Regstr(r1), Regstr(r2)) => so.compare(r1,r2)
            case (IntLit(i1), IntLit(i2)) => i1 - i2
            case (IntLit(_), _) => -1 
            case (Regstr(_), IntLit(_)) => 1
            case (Regstr(_), _) => -1
            case (Temp(_), _) => 1
        }
    }
}