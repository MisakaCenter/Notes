
# Static Program Analysis, Part 1

南京大学《软件分析》课程笔记 (Lec 1, 2)


## Programming Language:

 - Theory
   - Language design
   - Type system
   - Semantics and logics 
 - Environment
   - Compilers
   - Runtime system
 - Application
   - Program analysis
   - Program verification
   - Program synthesis

## Soundness & Completeness

 - Soundness: overapproximate, false positives
 - Completeness: underapproximate, false negatives

## Rice's Theorem

 - all non-trivial, semantic properties of programs are undecidable
 - There is no perfect static analysis (Sound & Complete)
   - Compromise soundness/completeness

## Compiler

1. Source Code -> Scanner (Lexical Analysis) -> Tokens

2. Tokens -> Parser (Syntax Analysis) -> AST
   1. Context-Free Grammar
   
3. AST -> Type Checker (Semantic Analysis) -> Decorated AST
   1. Attribute Grammar

4. Decorated AST -> Translator -> IR (Intermediate Representation)

5. IR -> Code Generator -> Machine Code

* Static Analysis -> IR
  * (1~4): frontend (trivial)
  * (5): backend

## AST & IR

- AST
  - closed to targeted language
  - suitable for fast type checking
  - lack of control flow information

- IR **basic for static analysis**
  - ("3-address" form), closed to machine code
  - compact and uniform
  - contain control flow information

## 3-Address Code (3AC)

 - at most **one** operator on the right of an instruction
 - contains at most **three** addresses
   - address can be one of the following:
     - Name: a,b
     - Constant: 3
     - Compiler-generated temporary: t1, t2
 - Common 3AC Forms
   - x = y *bop* z (binary operation)
   - x = *uop* y (unary operation)
   - x = y
   - *goto* L (unconditional jump)
   - *if* x *goto* L (conditional jump)
   - if x *rop* y goto L (relational operator)
 - Soot and Jimple
   - Soot: SA framework for Java
   - Jimple (IR of Soot): typed 3AC

## Static Single Assignment (SSA)

 - All assignments in SSA are to variables with **distinct** names
   - Give each definition a fresh name
   - Every variable has exactly one definition
     - phi-function: to select the values at merge nodes (phi(x0, x1) has the value x0 if the control flow passes through ... )
 - Flow information indirectly incorporated into the unique variable names
   - flow-insensitive analysis gains partial precision of flow-sensitive analysis via SSA
 - Define-and-Use pairs are explicit
 - May introduce too many variables and phi-functions
 - Inefficiency problem when translating to machine code (due to copy operations)

## Control Flow Analysis

 - Usually refer to building Control Flow Graph (CFG)
 - The node in CFG can be an individual 3AC, or a Basic Block (BB)

### Basic Block

 - maximal sequences of consecutive 3AC with properties that
   - it can be entered only at the beginning
   - it can be exited only at the end
 - Build BBs
   - determine the leaders
     - the first instruction
     - any target instruction of a jump
     - any instruction that immediately follows a jump
   - a BB consists of a leader and all its subsequent instructions until the next leader

### Control Flow Graph

 - The nodes of CFG are BBs
 - There is an edge from block A to block B iff.
   - there is a jump from the end of A to the beginning of B
   - B immediately follows A in the original order of instructions and A does not end in an **unconditional** jump
 - replace the jumps to instruction labels by jumps to BBs
 - Usually add two nodes, **Entry** and **Exit**
   - do not correspond to executable IR