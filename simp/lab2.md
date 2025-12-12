# 50.054 Project Lab 2 (10%)

In the previous lab, we completed the parser and ir code generation.

If you have trouble completing lab 1, you can send the instructor an email to ask for the sample solution. 

In this lab, we look into the dynamic and static semantics of the SIMP language.

## Tasks for this Lab

The two main tasks for this lab include

1. Implementing an interpreter of SIMP programs.
1. Implementing a type inference for SIMP programs

There is no obvious dependency between the two tasks, hence you can divide the task among your team members if you wish to.

## Task 1 - SIMP interpreter

An interperter takes an ir of a program (AST, or Pseudo Assembly) and the input and runs the program ir form and returns the result.

Typically an interpreter implementation can derived based on the operational semantics. 

In `src/main/scala/sutd/compiler/simp/interpreter/PAInt.scala`, we implemented an interpreter of Pseudo Assembly in Small Step Operational Semantics. We recommend you to study the code in `PAInt.scala` and `src/test/scala/sutd/compiler/simp/TestPAInt` to understand how the algorithm was implemented. There is no modification required to these two files.

As a backup and for practice purposes, we would like to implement an interpreter of SIMP (from SIMP AST). 

In `src/main/scala/sutd/compiler/simp/interpreter/SIMPInt.scala`, we find the partially implemented interpreter using Big Step Operational Semantics of SIMP. 

### Sub Task 1.1

The `evalExp` function evaluates a SIMP expression to a constant by implementing the 
$\Delta \vdash E \Downarrow c$ rules introduced in the notes.

The function is nearly complete except that there are a few cases missing. 

Your task is to complete the implementation.

Upon completion, you should be able to pass the two test cases for `evalExp`.

```bash
sbt compile "testOnly sutd.compiler.simp.TestSimpInt -- -z evalExp" 
```
### Sub Task 1.2

The `eval` function evaluates a SIMP statement to a value environment by implementing the  $(\Delta, S) \Downarrow \Delta'$ rules.

Due to the definition of the statement AST, we need to overload `eval` for single statement and multiple statments.

Your task is to complete the implementation of the type class instances `evalMany` and `evalOne`.


##### Testing the SIMP interpreter implementation 

Now you should be able to pass all test cases in `src/test/scala/sutd/compiler/simp/TestSimpInt.scala`


## Task 2 - SIMP Type Inference

In this task we look into the static semantics of the SIMP programming language.


The codes of concern in this task are in `src/main/scala/sutd/compiler/simp/semantics/TypeInf.scala`

Recall the typing constructs for SIMP

$$
\begin{array}{rccl}
 {\tt (Variable)} & X & ::= & a \mid b \mid c \mid d \mid ... \\ 
 {\tt (Types)} & T & ::= & int \mid bool  \\ 
 {\tt (Extended\ Types)} & \hat{T} & ::=  &\alpha \mid T \\ 
 {\tt (Type\ Environments)} & \Gamma & \subseteq & (X \times T) \\ 
 {\tt (Constraints)} & \kappa & \subseteq & (\hat{T} \times \hat{T}) \\ 
 {\tt (Type\ Substitution)} & \Psi & ::= & [\hat{T}/\alpha] \mid [] \mid \Psi \circ \Psi 
\end{array}
$$

We encode the simple (non-extended) type as

```scala
enum Type {
    case IntTy
    case BoolTy
}
```

We encode the extended type as 

```scala
enum ExType {
    case MonoType(t:Type)
    case TypeVar(n:String)
}
```

then the type environment can be modelled via a dictionary mapping from variable to type.

```scala
type TypeEnv = Map[Var, Type]
```

The type constraints can be modelled as a set of pairs of extended types.

```scala
type TypeConstrs = Set[(ExType, ExType)]
```

Lastly the type substitution is a sequence of mapping type variable name to extended type.

```scala
enum TypeSubst {
    case Empty // [] 
    case RevComp(s:(String, ExType), psi:TypeSubst) //  psi compose s
}
```

As per mentioned in the notes, during the type inference, we create skolem type variable $\alpha_x$ for (data value) variable $x$. In the implementation, we have `TypeVar("x")` as the skolem type variable for variable `Var("x")`, i.e. they share the same name.

### Sub Task 2.1 - Substitution

In this task, you need to implement the type substitution

$$
\begin{array}{rcll}
[]\hat{T} & = & \hat{T} \\ 
[\hat{T}/\alpha]\alpha & = & \hat{T} \\  
[\hat{T}/\alpha]\beta & = & \beta & if\ \alpha \neq \beta \\
[\hat{T}/\alpha]T & = & T
\end{array}
$$

Type substiution can be *compositional*.

$$
\begin{array}{rcll}
 (\Psi_1 \circ \Psi_2) \hat{T} & = & \Psi_1(\Psi_2(\hat{T}))
\end{array}
$$

To do that, we define a type class `Substitutable[A]` which allows us to overload the `applySubst` function to different parameter types.

Your task here is to complete the implementation of type class instance `exTypeSubstitutable`.

Upon completion, you should be able to pass the four test cases for `substitution`.

```bash
sbt compile "testOnly sutd.compiler.simp.TestTypeInf -- -z substitution" 
```

### Sub Task 2.2 - Unification

The output of the type inference algorithm is a set of type constraints.

Solving the set of type constraint via unification produces the type substitution that grounds all the skolem type variables.

$$
\begin{array}{rcl}
mgu(int, int) & = & [] \\ 
mgu(bool, bool) & = & [] \\ 
mgu(\alpha, \hat{T}) & = & [\hat{T}/\alpha] \\ 
mgu(\hat{T}, \alpha) & = & [\hat{T}/\alpha] \\
\end{array}
$$

and

$$
\begin{array}{rcl}
mgu(\{\}) & = & [] \\ 
mgu(\{(\hat{T_1}, \hat{T_2})\} \cup \kappa ) & = & let\ \Psi_1 = mgu(\hat{T_1}, \hat{T_2}) \\ 
& & \ \ \ \ \ \ \kappa'  = \Psi_1(\kappa) \\ 
& & \ \ \ \ \ \ \Psi_2   = mgu(\kappa') \\ 
& & in\  \Psi_2 \circ \Psi_1  
\end{array}
$$

Since `mgu` needs to be overloaded, we define a type class `Unifiable[A]`. 

Your task is to complete the type class instances `extypesUnifiable` and `listUnifiable`.

Upon completion, you should be able to pass the four test cases for `unification`.

```bash
sbt compile "testOnly sutd.compiler.simp.TestTypeInf -- -z unification" 
```

### Sub Task 2.3 - Inference

The type class instance method `infStmt.infer` implements the $S \vDash \kappa$ rules.

Type function `infExp` implements the $E \vDash \hat{T}, \kappa$ rules.

Your task is to complete the above two by implementing the missing cases.


#### Testing the Type Inference Implementation

Now you should be able to pass all test cases in `src/test/scala/sutd/compiler/simp/TestTypeInf.scala`


## Everything So far

We should now be able to build an interpreter. 
Check out the code at `src/main/scala/Main.scala`.

To build it

```bash
sbt package
```

Let's make a simple simp program called `fib.simp`

```java
x = input;
f = 0;
s = 1;
c = 0;
t = 0;
while c < x {
    t = f;
    f = s;
    s = t + f;
    c = c + 1;
}
return s;
```


Running with scala version >= 3.7.2

```bash
scala run -cp target/scala-3.7.2/simp_3-0.0.1.jar -M sutd.compiler.simp.Main -- -i fib.simp 5
```

should produce `8` as output.


