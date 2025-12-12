package sutd.compiler.simp

import scala.io.Source
import sutd.compiler.simp.syntax.Lexer.{given, *}
import sutd.compiler.simp.syntax.Parser.*
import sutd.compiler.simp.syntax.Parsec.*
import sutd.compiler.simp.syntax.Parsec
import sutd.compiler.simp.syntax.Parsec.Progress
import sutd.compiler.simp.syntax.AST.*
import sutd.compiler.simp.semantic.TypeInf.{given, *}
import sutd.compiler.simp.interpreter.SimpInt.*
import sutd.compiler.simp.ir.MMUpDown.*
import sutd.compiler.simp.ir.Util.StateInfo
import sutd.compiler.simp.backend.JVM.*
import sutd.compiler.simp.monad.Monad.*
import sutd.compiler.simp.monad.StateT.*

object Main {
    def main(args:Array[String]):Unit = {
        if (args.length < 2) {
            println("""
            USAGE: scala run -cp simp.jar -M sutd.compiler.Main <mode> source.simp [inputs]
              e.g. scala run -cp simp.jar -M sutd.compiler.Main -i fib.simp 2
            """)
        } else {
            val flag = args(0)
            val simpfile = args(1)
            if (flag == "-c") {
                compile(simpfile) match {
                    case Left(error) => {
                        println("Error:")
                        println(error)
                    } 
                    case Right(result) => {
                        println("Compilation done.")
                    }
                }
            } else {
                if ((flag == "-i") && (args.length >= 3)) {
                    val input = args(2).toInt
                    exec(simpfile, input) match {
                        case Left(error) => {
                            println("Error:")
                            println(error)
                        } 
                        case Right(result) => {
                            println(result)
                        }
                    }
                } else {
                    println(args.length)
                    for (i <- (0 to args.length - 1)) {
                        println(args(i))
                    }
                    println("""
                    USAGE1: interpreter 
                        scala run -cp simp_all.jar -M sutd.compiler.simp.Main -- -i source.simp <input>
                    e.g. scala run simp_all.jar -M sutd.compiler.simp.Main -- -i fib.simp 2
                    USAGE2: compiler
                        scala jar simp_all.jar -M sutd.compiler.simp.Main -- -c source.simp
                    e.g. scala jar simp_all.jar -M sutd.compiler.simp.Main --  -c fib.simp
                    """)
                }
            }
        }
    }
    import Progress.*
    import Result.*
    import Const.*
    def exec(filename:String, input:Int):Either[String, String] = {
        try {
            val lines = Source.fromFile(filename).getLines.toList.mkString("\n")
            Parsec.run(lex)(LEnv(lines.toList, 1, 1)) match {
                case Consumed(Ok((toks, lenv))) if eof(lenv) => {
                    Parsec.run(parse)(PEnv(toks)) match {
                        case Consumed(Ok((stmts, penv))) if done(penv) => {
                            typeInf(stmts) match {
                                case Left(errorMessage) => {
                                    Left(errorMessage)
                                }
                                case Right(typeenv) => {
                                    interpret(stmts,input) match {
                                        case Left(err) => Left(err)
                                        case Right(IntConst(result)) => Right(result.toString())
                                        case Right(BoolConst(result)) => Right(result.toString())
                                    }
                                }
                            }
                        }
                        case Consumed(Ok((stmts, penv)))  => {
                            Left(s"Parser terminated prematurely at ${penv._1}")
                        }
                        case Consumed(Failed(msg)) => 
                            Left(msg)
                        case Empty(Ok((stmts, penv))) if done(penv) => {
                            Left("An empty file is given.")
                        }
                        case Empty(Ok((stmts, penv)))  => {
                            Left(s"Parser terminated prematurely at ${penv._1}")
                        }
                        case Empty(Failed(msg)) => 
                            Left(msg)
                    }
                }
                case Consumed(Ok((toks, lenv))) => {
                    Left(s"Lexer terminated prematurely at ${lenv._1.mkString("")}")
                }
                case Consumed(Failed(msg)) => Left(msg)
                case Empty(Ok((toks, lenv))) if eof(lenv) => {
                    Left("An empty file is given.")
                }
                case Empty(Ok((toks, lenv))) => {
                    Left(s"Lexer terminated prematurely at ${lenv._1.mkString("")}")
                }
                case Empty(Failed(msg)) => Left(msg)
            }
            
        } catch {
            case e: java.io.FileNotFoundException => Left(s"File ${filename} does not exists.")
        }
    }

    def compile(filename:String):Either[String, Unit] = {
        try {
            val lines = Source.fromFile(filename).getLines.toList.mkString("\n")
            Parsec.run(lex)(LEnv(lines.toList, 1, 1)) match {
                case Consumed(Ok((toks, lenv))) if eof(lenv) => {
                    Parsec.run(parse)(PEnv(toks)) match {
                        case Consumed(Ok((stmts, penv))) if done(penv) => {
                            typeInf(stmts) match {
                                case Left(errorMessage) => {
                                    Left(errorMessage)
                                }
                                case Right(typeenv) => {
                                    cogen(stmts).run(StateInfo(1,"var", 1)) match {
                                        case Identity((st_, instrs)) => {
                                            // TODO liveness analysis here?
                                            genTargetCode(instrs) 
                                        }
                                    }

                                }
                            }
                        }
                        case Consumed(Ok((stmts, penv)))  => {
                            Left(s"Parser terminated prematurely at ${penv._1}")
                        }
                        case Consumed(Failed(msg)) => 
                            Left(msg)
                        case Empty(Ok((stmts, penv))) if done(penv) => {
                            Left("An empty file is given.")
                        }
                        case Empty(Ok((stmts, penv)))  => {
                            Left(s"Parser terminated prematurely at ${penv._1}")
                        }
                        case Empty(Failed(msg)) => 
                            Left(msg)
                    }
                }
                case Consumed(Ok((toks, lenv))) => {
                    Left(s"Lexer terminated prematurely at ${lenv._1.mkString("")}")
                }
                case Consumed(Failed(msg)) => Left(msg)
                case Empty(Ok((toks, lenv))) if eof(lenv) => {
                    Left("An empty file is given.")
                }
                case Empty(Ok((toks, lenv))) => {
                    Left(s"Lexer terminated prematurely at ${lenv._1.mkString("")}")
                }
                case Empty(Failed(msg)) => Left(msg)
            }
            
        } catch {
            case e: java.io.FileNotFoundException => Left(s"File ${filename} does not exists.")
        }
    }}


/*

import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes
import java.io.FileOutputStream
import org.objectweb.asm.Label



object Main {
    def hellowworld():ClassWriter = {
        val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS)
        cw.visit(Opcodes.V1_8, Opcodes.ACC_PUBLIC, "GeneratedClass", null, "java/lang/Object", null)
        
        val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_STATIC, "main", "([Ljava/lang/String;)V", null, null)
        mv.visitCode()
        mv.visitFieldInsn(Opcodes.GETSTATIC, "java/lang/System", "out", "Ljava/io/PrintStream;")
        mv.visitLdcInsn("Hello world!")
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/io/PrintStream", "println", "(Ljava/lang/String;)V", false)
        mv.visitInsn(Opcodes.RETURN)
        mv.visitMaxs(0, 0)
        mv.visitEnd()
        cw.visitEnd()
        return cw
    }

    def print_argv0():ClassWriter = {
        val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS)
        cw.visit(Opcodes.V1_8, Opcodes.ACC_PUBLIC, "GeneratedClass", null, "java/lang/Object", null)
        
        val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_STATIC, "main", "([Ljava/lang/String;)V", null, null)
        mv.visitCode()
        mv.visitFieldInsn(Opcodes.GETSTATIC, "java/lang/System", "out", "Ljava/io/PrintStream;");
        mv.visitVarInsn(Opcodes.ALOAD, 0) // load 0 param, i.e. this
        mv.visitInsn(Opcodes.ICONST_0)    // load  argv 0
        mv.visitInsn(Opcodes.AALOAD)
        // mv.visitVarInsn(Opcodes.AALOAD, 0) // this won't work
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/io/PrintStream", "println", "(Ljava/lang/String;)V", false)
        mv.visitInsn(Opcodes.RETURN)
        mv.visitMaxs(0, 0)
        mv.visitEnd()
        cw.visitEnd()
        return cw
    }

    def print_argv0_as_int():ClassWriter = {
        val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS)
        cw.visit(Opcodes.V1_8, Opcodes.ACC_PUBLIC, "GeneratedClass", null, "java/lang/Object", null)
        
        val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_STATIC, "main", "([Ljava/lang/String;)V", null, null)
        mv.visitCode()
        mv.visitVarInsn(Opcodes.ALOAD, 0) // load 0 param, i.e. this
        mv.visitInsn(Opcodes.ICONST_0)    // load  argv 0
        mv.visitInsn(Opcodes.AALOAD)
        mv.visitMethodInsn(Opcodes.INVOKESTATIC, "java/lang/Integer", "parseInt", "(Ljava/lang/String;)I", false)
        mv.visitVarInsn(Opcodes.ISTORE, 1) // store it at local var 1
        mv.visitFieldInsn(Opcodes.GETSTATIC, "java/lang/System", "out", "Ljava/io/PrintStream;")
        mv.visitVarInsn(Opcodes.ILOAD, 1) 
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/io/PrintStream", "println", "(I)V", false)
        mv.visitInsn(Opcodes.RETURN)
        mv.visitMaxs(0, 0)
        mv.visitEnd()
        cw.visitEnd()
        return cw
    }


    def print_argv0_plus_1():ClassWriter = {
        val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS)
        cw.visit(Opcodes.V1_8, Opcodes.ACC_PUBLIC, "GeneratedClass", null, "java/lang/Object", null)        
        val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_STATIC, "main", "([Ljava/lang/String;)V", null, null)
        mv.visitCode()
        mv.visitVarInsn(Opcodes.ALOAD, 0) // load 0 param, i.e. this
        mv.visitInsn(Opcodes.ICONST_0)    // load  argv 0
        mv.visitInsn(Opcodes.AALOAD)
        mv.visitMethodInsn(Opcodes.INVOKESTATIC, "java/lang/Integer", "parseInt", "(Ljava/lang/String;)I", false)
        mv.visitVarInsn(Opcodes.ISTORE, 1) // store it at local var 1
        mv.visitVarInsn(Opcodes.ILOAD, 1) // load local var 1 to the operand stack
        mv.visitInsn(Opcodes.ICONST_1) // load const 1 to the 2nd opreand stack
        mv.visitInsn(Opcodes.IADD)
        mv.visitVarInsn(Opcodes.ISTORE, 1) // store the result back to local var 1
        mv.visitFieldInsn(Opcodes.GETSTATIC, "java/lang/System", "out", "Ljava/io/PrintStream;")
        mv.visitVarInsn(Opcodes.ILOAD, 1) 
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/io/PrintStream", "println", "(I)V", false)
        mv.visitInsn(Opcodes.RETURN)
        mv.visitMaxs(0, 0)
        mv.visitEnd()
        cw.visitEnd()
        return cw
    }




    def print_argv0_countdown():ClassWriter = {
        val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES) // cOMPUTE_MAXS automatically compute stack size, COMPUTE_FRAMES automatically compute the stackmap
        cw.visit(Opcodes.V1_8, Opcodes.ACC_PUBLIC, "GeneratedClass", null, "java/lang/Object", null)        
        val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_STATIC, "main", "([Ljava/lang/String;)V", null, null)
        val endWhile = new Label()
        val beginWhile = new Label()
        mv.visitCode()
        // int x = parseInt(argv[0])
        mv.visitVarInsn(Opcodes.ALOAD, 0) // load 0 param, i.e. this
        mv.visitInsn(Opcodes.ICONST_0)    // load  argv 0
        mv.visitInsn(Opcodes.AALOAD)
        mv.visitMethodInsn(Opcodes.INVOKESTATIC, "java/lang/Integer", "parseInt", "(Ljava/lang/String;)I", false)
        mv.visitVarInsn(Opcodes.ISTORE, 1) // store it at local var 1
        // while (x > 0) {
        mv.visitLabel(beginWhile)
        mv.visitVarInsn(Opcodes.ILOAD, 1) // load local var 1 to the operand stack
        // mv.visitInsn(Opcodes.ICONST_0) // load const 1 to the 2nd opereand stack
        // mv.visitJumpInsn(Opcodes.IF_ICMPLE, endWhile);
        mv.visitJumpInsn(Opcodes.IFLE, endWhile);
        // x = x - 1;
        mv.visitVarInsn(Opcodes.ILOAD, 1) // load local var 1 to the operand stack
        mv.visitInsn(Opcodes.ICONST_1) //
        mv.visitInsn(Opcodes.ISUB) // 
        mv.visitVarInsn(Opcodes.ISTORE, 1) // store the result back to local var 1
        // }
        mv.visitJumpInsn(Opcodes.GOTO, beginWhile)
        mv.visitLabel(endWhile)
        // println(x);
        mv.visitFieldInsn(Opcodes.GETSTATIC, "java/lang/System", "out", "Ljava/io/PrintStream;")
        mv.visitVarInsn(Opcodes.ILOAD, 1) 
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/io/PrintStream", "println", "(I)V", false)
        // return;
        mv.visitInsn(Opcodes.RETURN)
        mv.visitMaxs(0, 0)
        mv.visitEnd()
        cw.visitEnd()
        return cw
    }

    def main(args:Array[String]):Unit = {
        val cw = print_argv0_countdown()
        val bytes = cw.toByteArray()
        try {
            val stream = new FileOutputStream("GeneratedClass.class")
            stream.write(bytes)
        } catch { 
            case (e:Exception) => {
                e.printStackTrace()
            }
        }
    }
}

*/