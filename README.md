# Curry-Howard isomorphism between IPC and STLC

Explicitly written out isomorphism between intuitionistic propositional logic and
simply typed lambda calculus.

It is implemented as a program consisting of two parts:

  * Interactive proof assistant that can be used to construct proofs in IPC;
  * The actual isomorphism that translates proofs in IPC into STLC.


The only purpose of this program is to illustrate the 
Curry-Howard isomorphism between natural deduction proofs in IPC on one 
hand and simply typed lambda calculus on the other hand.

It allows the user to formulate theorems in IPC, and then to prove those 
theorems in atomic steps using a few built-in deduction rules (like e.g.
implication elimination `impl_elim` or conjunction introduction `conj_intr`),
as well as the previously proved theorems.

In each step, the assistant prints the proof in tree-form, the corresponding
piece of code, the current list of assumptions, and the current goal 
(somewhat similar in spirit to 
  [Coq](https://coq.inria.fr/), but much simpler).
The final output of the program is valid Scala-code that can be 
type-checked by the Scala compiler. Thus, the Scala type-checker is 
used as a proof-checker.

### Quickstart

To run the program, we will need the Scala compiler / command line tool `scala`.

A script with the proofs of few classical theorems of IPC is provided (`commands.txt`), so one
can simply run

    scala ipc_stlc_curry_howard.scala < commands.txt

and just enjoy the spectacle: the console will be filled with weirdly shaped proof trees and
code snippets.

Here is what the output will look like (excerpt):


    /*
                                                                                                                                                                                                                                                                                                                                                       
                                                                       ------------------------------------------------------------(A)  -----------------------------------------------------(A)               ------------------------------------------------------------(A)  -----------------------------------------------------(A)               
                                                                       [Neg[(C \/ D)], (A => C), (B => D), A, (A \/ B)] |- (A => C)     [Neg[(C \/ D)], (A => C), (B => D), A, (A \/ B)] |- A                  [Neg[(C \/ D)], (A => C), (B => D), B, (A \/ B)] |- (B => D)     [Neg[(C \/ D)], (A => C), (B => D), B, (A \/ B)] |- B                  
                                                                       -------------------------------------------------------------------------------------------------------------------------(-I)           -------------------------------------------------------------------------------------------------------------------------(-I)           
                                                                                                         [Neg[(C \/ D)], (A => C), (B => D), A, (A \/ B)] |- C                                                                                   [Neg[(C \/ D)], (A => C), (B => D), B, (A \/ B)] |- D                                                 
                                                                       -----------------------------------------------------------------------------------------------------------------------------(+D2)      -----------------------------------------------------------------------------------------------------------------------------(+D1)      
                                                                                                       [Neg[(C \/ D)], (A => C), (B => D), A, (A \/ B)] |- (C \/ D)                                                                            [Neg[(C \/ D)], (A => C), (B => D), B, (A \/ B)] |- (C \/ D)                                            
                                                                       ----------------------------------------------------------------------------------------------------------------------------------(+I)  ----------------------------------------------------------------------------------------------------------------------------------(+I)  ---------------------------------------------------------(A)
                                                                                                        [(A => C), (B => D), Neg[(C \/ D)], (A \/ B)] |- (A => (C \/ D))                                                                        [(A => C), (B => D), Neg[(C \/ D)], (A \/ B)] |- (B => (C \/ D))                                       [(A => C), (B => D), Neg[(C \/ D)], (A \/ B)] |- (A \/ B)
    --------------------------------------------------------------(A)  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------(-D)
    [(A => C), (B => D), Neg[(C \/ D)], (A \/ B)] |- Neg[(C \/ D)]                                                                                                                                              [(A => C), (B => D), Neg[(C \/ D)], (A \/ B)] |- (C \/ D)                                                                                                                                          
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------(-I)
                                                                                                                                                                                 [(A => C), (B => D), Neg[(C \/ D)], (A \/ B)] |- Nothing                                                                                                                                                                              
    -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------(+I)
                                                                                                                                                                                     [(A => C), (B => D), Neg[(C \/ D)]] |- Neg[(A \/ B)]                                                                                                                                                                                  
    */
    def destructiveDilemma[A,B,C,D](Iac:(A => C),Ibd:(B => D),IDcdF:Neg[(C \/ D)]):Neg[(A \/ B)] = { Dab => {
        val _g0:Neg[(C \/ D)] = IDcdF
        val _g1:(C \/ D) = {
          val _g0:(A => (C \/ D)) = { a => {
              val _g0:C = {
                val _g0:(A => C) = Iac
                val _g1:A = a
                impl_elim(_g0,_g1)
              }
              disj_intr_1(_g0)
            }
          }
          val _g1:(B => (C \/ D)) = { b => {
              val _g0:D = {
                val _g0:(B => D) = Ibd
                val _g1:B = b
                impl_elim(_g0,_g1)
              }
              disj_intr_2(_g0)
            }
          }
          val _g2:(A \/ B) = Dab
          disj_elim(_g0,_g1,_g2)
        }
        impl_elim(_g0,_g1)
      }
    }
    
    
    /*
                                                                                      
    ------------------------------------(A)  ------------------------------------(A)  --------------------------------------(A)
    [Neg[A], Neg[B], (A \/ B)] |- Neg[A]     [Neg[A], Neg[B], (A \/ B)] |- Neg[B]     [Neg[A], Neg[B], (A \/ B)] |- (A \/ B)
    ---------------------------------------------------------------------------------------------------------------------------(-D)
                                               [Neg[A], Neg[B], (A \/ B)] |- Nothing                                           
    -------------------------------------------------------------------------------------------------------------------------------(+I)
                                                   [Neg[A], Neg[B]] |- Neg[(A \/ B)]                                               
    */
    def deMorgan[A,B](IaF:Neg[A],IbF:Neg[B]):Neg[(A \/ B)] = { Cab => {
        val _g0:Neg[A] = IaF
        val _g1:Neg[B] = IbF
        val _g2:(A \/ B) = Cab
        disj_elim(_g0,_g1,_g2)
      }
    }
    
    
    /*
                                                                                                                                        
    -----------------------(A)                                                                 -----------------------(A)               
    [Neg[(A \/ B)], A] |- A                                                                    [Neg[(A \/ B)], B] |- B                  
    ------------------------------(+D2)                                                        ------------------------------(+D1)      
    [Neg[(A \/ B)], A] |- (A \/ B)                                                             [Neg[(A \/ B)], B] |- (A \/ B)           
    -----------------------------------(+I)  --------------------------------(A)               -----------------------------------(+I)  --------------------------------(A)
    [Neg[(A \/ B)]] |- (A => (A \/ B))       [Neg[(A \/ B)]] |- Neg[(A \/ B)]                  [Neg[(A \/ B)]] |- (B => (A \/ B))       [Neg[(A \/ B)]] |- Neg[(A \/ B)]
    ----------------------------------------------------------------------------(hypotSyllog)  ----------------------------------------------------------------------------(hypotSyllog)
                             [Neg[(A \/ B)]] |- Neg[A]                                                                  [Neg[(A \/ B)]] |- Neg[B]                          
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------(+C)
                                                                           [Neg[(A \/ B)]] |- (Neg[A] /\ Neg[B])                                                                        
    */
    def deMorgan_2[A,B](IDabF:Neg[(A \/ B)]):(Neg[A] /\ Neg[B]) = {
      val _g0:Neg[A] = {
        val _g0:(A => (A \/ B)) = { a => {
            val _g0:A = a
            disj_intr_1(_g0)
          }
        }
        val _g1:Neg[(A \/ B)] = IDabF
        hypotSyllog(_g0,_g1)
      }
      val _g1:Neg[B] = {
        val _g0:(B => (A \/ B)) = { b => {
            val _g0:B = b
            disj_intr_2(_g0)
          }
        }
        val _g1:Neg[(A \/ B)] = IDabF
        hypotSyllog(_g0,_g1)
      }
      conj_intr(_g0,_g1)
    }
    
The output will be a valid Scala program, with IPC proof trees in the comments, and corresponding code snippets as the actual compilable code.

The next few sections describe what all those IPC terms and proofs even are. Then the example sections explain how this tool could be used to prove some really simple theorems.


### IPC-Terms

The object language (IPC) is defined as follows:

  * Atoms are strings that match the regex `[A-Z]+` (e.g. `P`, `Q`, `R`)
  * The bottom term `Nothing` is in IPC.
  * If `a`, `b` are some meta-variables that represent terms of IPC, 
    then `(a /\ b)`, `(a \/ b)`, `(a => b)` are also in IPC.
    These connectives stand for conjunction, disjunction and implication.
  * There is "syntactic sugar" for negation: `Neg[A]` is shorthand for
    `A => Nothing`.

The parentheses can be omitted sometimes, the precedence order is as follows:
`=>`, `\/`, `/\`, `Neg`. 

Here are few examples of valid IPC terms:

  * `P => Q /\ (R \/ X)`
  * `(A => (B => C)) => ((A => B) => A => C)`.

### Proofs

The basic workflow is as follows: 

  1. The user creates a new theorem
  2. The user enters rules with variable names and type-hints (one at a time),
     until the theorem is proved. Then the new theorem becomes available 
     as a new rule, and the user either continues with (1) or exits.
  3. In the very end, all proofs are translated into STLC and printed as one
     big Scala program.

To create a new theorem, enter:

    > theorem myThmName [ <Assumption_1>; ...; <Assumption_N> ] => <Conclusion>

Here, all `<Assumption_i>` and `<Conclusion>` must be valid IPC terms.
An expression like `[A; B; C] => X` is essentially equivalent to
`A => B => C => X`, however, there is a little difference: when we will
try to apply our theorem later, the proof assistant will try to unify
our goal with `X`. In case of success, additional goals will be 
created, one goal for each assumption `A`, `B`, `C`.

Thus, for example, two theorems
with statements `[A ; B] => B /\ A` and `[A] => (B => B /\ A)` 
are essentially equivalent, but the conclusion of the former will be 
unifiable with the goal
`X /\ (Y \/ Z)` and not unifiable with `X => X /\ (Y \/ Z)`, whereas
the conclusion of the latter will not be unifiable with `X /\ (Y \/ Z)` but
with `X => X /\ (Y \/ Z)`.

To prove a theorem, repeatedly apply rules to the current goal
(backward-reasoning). Currently available rules can be listed by issuing the 
`list_rules` command.

Initially, there are only 10 rules:

    Assumption                           (`assumption`)
    Implication introduction             (`impl_intr`)
    Implication elimination              (`impl_elim`)
    Conjunction introduction             (`conj_intr`)
    Conjunction elimination (left)       (`conj_elim_1`)
    Conjunction elimination (right)      (`conj_elim_2`)
    Disjunction introduction (left)      (`disj_intr_1`)
    Disjunction introduction (right)     (`disj_intr_2`)
    Disjunction elimination              (`disj_elim`)
    Explosion principle                  (`explosion`)

Some of the rules require extra parameters: either variable names, or
valid IPC-formulas. For example, if the list of assumptions contains
a proof `x` of formula `X`, and our goal is to show `X`, we have to
explicitly specify the name of the assumption that we want to use: 

    > assumption(x)

Sometimes, we have to specify extra formulas when applying a rule.
For example, if our current goal is `G`, and we want to show that it is
a result of disjunction elimination, we have to specify two extra formulas
as hints. For example, if we want to show `G` by showing three formulas

  * `(X => Z) \/ Y`,
  * `(X => Z) => G`, and 
  * `Y => G`, 

we would have to invoke the `disj_elim` rule as follows:

    > disj_elim{X => Z, Y}

Compare this with the output of `list_rules`:

    disj_elim[(A => Z);(B => Z);(A \/ B)] => Z   needs hints for: A,B

We obtain the required hints by unifying the output of `list_rules` with
what we want to obtain:

    G                 unifies with goal            Z
    (X => Z) => G     unifies with                 A => Z
    Y => G            unifies with                 B => Z
    (X => Z) \/ Y     unifies with                 A \/ B

and therefore,

    X => Z            unifies with                 A
    Y                 unifies with                 B

and those two formulas are exactly the hints that we must provide to the `disj_elim` rule.

Notice that *curly* braces are used to specify formulas, while *round* 
parentheses are used to specify variable names. We can always list 
all available rules using the `list_rules` command. It will also 
tell us what hints each rule requires.

### Help, Undo, Exit

Enter `help` to get a brief reminder of how the interface works.

Enter `undo` to revert the last action.

We can exit the interactive session by typing `exit`. If we started the program using `cat` or `tee`, we might have to press `Ctrl+D` additionally.

After the program terminates, it will print all the proven theorems to the
stdout. 

We can save the output of the program to some file with ending ".scala", and
run it with the scala interpreter. If the type checker does not find any
errors, then our proofs are indeed sound.

### Hello-World example

Let's start with a really trivial example: given `A` and `B`, we want to
show that the conjunction `A /\ B` also holds.

Start the program with

    scala ipc_stlc_curry_howard.scala

and enter:

    > theorem trivial [A; B] => A /\ B

The name of the theorem is `trivial`. In the square brackets, we listed our assumptions `A` and `B`. Then we claimed that `A /\ B` follows.

The proof assistant will respond with

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Code ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    def trivial[A,B](a:A,b:B):(A /\ B) = ???
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~ Natural deduction proof ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    ???
    ------------------(?)
    [A, B] |- (A /\ B)
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Assumptions & Goals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
       a : A
       b : B
    ============================================================
    Goal: (A /\ B)

We see that, by the Curry-Howard isomorphism, stating our theorem was equivalent 
to the declaration of a generic scala method. 
This method takes two type arguments `A` and `B`, then two "assumptions" `a: A` and `b: B`,
and produces a result of type `A /\ B`
(which is an alias for the ordinary `(A, B)` pair type).

To prove our theorem, we have to get to the goal `(A /\ B)`. Since we have no idea,
let's list the available rules:

    > list_rules
    assumption(<nameOfAssumptionToUse>)
    conj_elim_1[(A /\ B)] => A   needs hints for: B
    conj_elim_2[(A /\ B)] => B   needs hints for: A
    conj_intr[A;B] => (A /\ B)
    disj_elim[(A => Z);(B => Z);(A \/ B)] => Z   needs hints for: A,B
    disj_intr_1[A] => (A \/ B)
    disj_intr_2[B] => (A \/ B)
    explosion[Nothing] => A
    impl_elim[(A => B);A] => B   needs hints for: A
    impl_intr(<nameOfIntroducedAssumption>)

The rule `conj_intr` has `(A /\ B)` as conclusion. This is literally what we need, so
this looks promising. We enter:

    > conj_intr

and the proof assistant responds with an updated state:

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Code ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    def trivial[A,B](a:A,b:B):(A /\ B) = {
      val _g0:A = ???
      val _g1:B = ???
      conj_intr(_g0,_g1)
    }
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~ Natural deduction proof ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    ???             ???
    -----------(?)  -----------(?)
    [A, B] |- A     [A, B] |- B
    ------------------------------(+C)
          [A, B] |- (A /\ B)      
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Assumptions & Goals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
       a : A
       b : B
    ============================================================
    Goal: A
      There are 1 more goal(s):
      (1)  (a : A, b : B) |- B

Our new goal is `A`. In the list of assumptions, we already have a proof `a` of the
formula `A`, so we use this assumption:

    > assumption(a)

and the response is:

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Code ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    def trivial[A,B](a:A,b:B):(A /\ B) = {
      val _g0:A = a
      val _g1:B = ???
      conj_intr(_g0,_g1)
    }
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~ Natural deduction proof ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
                    ???
    -----------(A)  -----------(?)
    [A, B] |- A     [A, B] |- B
    ------------------------------(+C)
          [A, B] |- (A /\ B)      
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Assumptions & Goals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
       a : A
       b : B
    ============================================================
    Goal: B

Now, we repeat the same for `B`:

    > assumption(b)

and we are actually done:


    'trivial' QED
    Currently nothing to show.
    Start new theorem with:  'theorem <name> [<A1>;...;<An>] => <C>'

We can from now on use this theorem to build more complex theorems. The command
`list_rules` displays the updated list of available rules 
(note the new `trivial[A;B] => (A /\ B)` line):

    > list_rules
    assumption(<nameOfAssumptionToUse>)
    conj_elim_1[(A /\ B)] => A   needs hints for: B
    conj_elim_2[(A /\ B)] => B   needs hints for: A
    conj_intr[A;B] => (A /\ B)
    disj_elim[(A => Z);(B => Z);(A \/ B)] => Z   needs hints for: A,B
    disj_intr_1[A] => (A \/ B)
    disj_intr_2[B] => (A \/ B)
    explosion[Nothing] => A
    impl_elim[(A => B);A] => B   needs hints for: A
    impl_intr(<nameOfIntroducedAssumption>)
    trivial[A;B] => (A /\ B)
    Currently nothing to show.
    Start new theorem with:  'theorem <name> [<A1>;...;<An>] => <C>'

If we now exit the proof assistant, a Scala program corresponding to the
above proof will be displayed:

    > exit
    
    // (...some predefined code here; omitted...)

    -----------(A)  -----------(A)
    [A, B] |- A     [A, B] |- B
    ------------------------------(+C)
          [A, B] |- (A /\ B)      
    */
    def trivial[A,B](a:A,b:B):(A /\ B) = {
      val _g0:A = a
      val _g1:B = b
      conj_intr(_g0,_g1)
    }

### A more interesting example

Suppose that we want to show that the triple negation elimination holds
in intuitionistic logic. Unlike the previous trivial "theorem", this
might be not immediately obvious. Again, start the proof assistant
with 

    scala ipc_stlc_curry_howard.scala

and write down the theorem that we want to show:

    theorem tripleNegation [ Neg[Neg[Neg[A]]] ] => Neg[A]

Recall that `Neg[A]` is just an abbreviation for `A => Nothing`.
In order to prove `A => B`, it is sufficient to *assume* `A` and then, with
this assumption, prove `B`. This is done by the `impl_intr` rule (last in the list):

    > list_rules
    assumption(<nameOfAssumptionToUse>)
    conj_elim_1[(A /\ B)] => A   needs hints for: B
    conj_elim_2[(A /\ B)] => B   needs hints for: A
    conj_intr[A;B] => (A /\ B)
    disj_elim[(A => Z);(B => Z);(A \/ B)] => Z   needs hints for: A,B
    disj_intr_1[A] => (A \/ B)
    disj_intr_2[B] => (A \/ B)
    explosion[Nothing] => A
    impl_elim[(A => B);A] => B   needs hints for: A
    impl_intr(<nameOfIntroducedAssumption>)

This rule requires a name for the assumption. Since we are assuming `A`, let's call
the assumption `a`:

    > impl_intr(a)

Take a look at the updated list of assumptions, it now contains the introduced
assumption `a: A`:

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Code ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    def tripleNegation[A](IIIaFFF:Neg[Neg[Neg[A]]]):Neg[A] = { a => ???
    }
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~ Natural deduction proof ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    ???
    --------------------------------(?)
    [Neg[Neg[Neg[A]]], A] |- Nothing
    -----------------------------------(+I)
       [Neg[Neg[Neg[A]]]] |- Neg[A]    
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Assumptions & Goals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    IIIaFFF : Neg[Neg[Neg[A]]]
       a : A
    ============================================================
    Goal: Nothing

Our new goal is to somehow show `Nothing` (absurdity), given the assumptions
`IIIaFFF: Neg[Neg[A]] => Nothing` and `a: A`. We want `Nothing` and we already
have `Neg[Neg[A]] => Nothing`.
We do not have a `Neg[Neg[A]]` yet, but still, it looks as if `impl_elim` could help:

    > impl_elim{Neg[Neg[A]]}

This is the response:

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Code ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    def tripleNegation[A](IIIaFFF:Neg[Neg[Neg[A]]]):Neg[A] = { a => {
        val _g0:Neg[Neg[Neg[A]]] = ???
        val _g1:Neg[Neg[A]] = ???
        impl_elim(_g0,_g1)
      }
    }
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~ Natural deduction proof ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    ???                                           ???
    -----------------------------------------(?)  ------------------------------------(?)
    [Neg[Neg[Neg[A]]], A] |- Neg[Neg[Neg[A]]]     [Neg[Neg[Neg[A]]], A] |- Neg[Neg[A]]
    -------------------------------------------------------------------------------------(-I)
                              [Neg[Neg[Neg[A]]], A] |- Nothing                           
    -----------------------------------------------------------------------------------------(+I)
                                  [Neg[Neg[Neg[A]]]] |- Neg[A]                               
    
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Assumptions & Goals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    IIIaFFF : Neg[Neg[Neg[A]]]
       a : A
    ============================================================
    Goal: Neg[Neg[Neg[A]]]
      There are 1 more goal(s):
      (1)  (IIIaFFF : Neg[Neg[Neg[A]]], a : A) |- Neg[Neg[A]]

This is the part that we already have, nothing interesting here:

    > assumption(IIIaFFF)

The new goal is a bit more interesting:

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Assumptions & Goals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    IIIaFFF : Neg[Neg[Neg[A]]]
       a : A
    ============================================================
    Goal: Neg[Neg[A]]

The `Neg[Neg[A]]`, which is the same as `(A => Nothing) => Nothing` is somehow
reminiscent of a continuation / yoneda embedding of `A`, so this looks promising.
Let's first break down the outermost `=>` in the goal by using `impl_intr`:

    > impl_intr(notA)

The response is:

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Assumptions & Goals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    IIIaFFF : Neg[Neg[Neg[A]]]
       a : A
    notA : Neg[A]
    ============================================================
    Goal: Nothing

Now we are almost done: `A` and `Neg[A]` trivially lead to absurdity:

    > impl_elim{A}

Now just use the assumptions:

    > assumption(notA)
    > assumption(a)

and we are done:

    'tripleNegation' QED

Again, the new theorem appears in the updated list of rules as:

    tripleNegation[Neg[Neg[Neg[A]]]] => Neg[A]

If we now `exit` the program, we see that our proof corresponds to the
following Scala program:

    def tripleNegation[A](IIIaFFF:Neg[Neg[Neg[A]]]):Neg[A] = { a => {
        val _g0:Neg[Neg[Neg[A]]] = IIIaFFF
        val _g1:Neg[Neg[A]] = { notA => {
            val _g0:Neg[A] = notA
            val _g1:A = a
            impl_elim(_g0,_g1)
          }
        }
        impl_elim(_g0,_g1)
      }
    }

We can clearly see the introductions of `a` and `notA` (with `impl_intr`)
that have been transformed into local anonymous function literals. We can
also see the multiple uses of `impl_elim`, which, as Scala function,
simply applies its first argument to the second argument:

    def impl_elim[A, B](f: A => B, x: A) : B = f(x)

The assignments of local variables `_gK` to a fixed value `v` correspond to
the invocation of `assumption(v)` during the proof.

The final result is a Scala method that builds a `A => Nothing` from a
`((A => Nothing) => Nothing) => Nothing`.

### Managing sessions

If one wants to write longer IPC proofs, one might want to save some
partial results, and then continue a session later.

The program does not provide any built-in facilities for saving the
current session, or loading previous sessions. However, it is easy 
to simulate saving/loading sessions on Unix/Linux.

The user input is read from STDIN.
Everything that is printed in interactive mode goes to STDERR.
When the program terminates, the resulting theory is printed to STDOUT.

The most basic way to run the program is:

    scala ipl_prover.scala

If we start the program this way, we will have to type in all the 
commands manually, and the resulting theory will be printed to the console.

If we want to save everything we type to a file, we can use `tee`:

    tee myCommands.txt | scala ipl_prover.scala

If we want to save the resulting scala code to a file, we can use stream
redirection:

    scala ipl_prover.scala > myTheory.scala

We can also re-run our commands, again, using stream redirection:

    scala ipl_prover.scala  < myCommands.txt   > myTheory.scala

We can also "load" and then continue with a previously saved session.
Remove the last `exit` command from our previously saved `myCommands.txt`
file, and start the interpreter as follows (note the `-`):

   cat myCommands.txt - | scala ipl_prover.scala

It will then re-run all the commands in `myCommands.txt` and go into 
interactive mode again.

Of course, we can combine all of the above, for example:

    cat myPreviousSession.txt - | tee myNewSession.txt | \
      scala ipl_prover.scala > myTheory.scala

will re-run all commands from `myPreviousSession.txt` and switch into 
interactive mode, saving all commands (old and new) to `myNewSession.txt`,
and saving the final output to `myTheory.scala`.