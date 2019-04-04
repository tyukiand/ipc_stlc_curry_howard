/*
 * PROOF ASSISTANT FOR INTUITIONISTIC PROPOSITIONAL LOGIC
 *
 * DESCRIPTION
 * ===========
 * 
 * This is a minimalistic proof assistant for intuitionistic propositional
 * logic. The only purpose of this program is to illustrate the 
 * Curry-Howard isomorphism between natural deduction proofs in IPC on one 
 * hand, and simply typed lambda calculus on the other hand.
 *
 * It allows the user to formulate theorems in IPC, and then to prove those 
 * theorems in atomic steps using a few built-in deduction rules (like e.g.
 * implication elimination `impl_elim` or conjunction introduction `conj_intr`),
 * as well as the previously proved theorems.
 * 
 * In each step, the assistant prints the proof in tree-form, the corresponding
 * piece of code, the current list of assumptions, and the current goal.
 * The final output of the program is valid Scala-code that can be 
 * type-checked by the Scala compiler. Thus, the Scala type-checker is 
 * used as a proof-checker.
 * 
 * RUNNING THE PROGRAM
 * ===================
 *
 * To run the program, you will need the Scala interpreter.
 *
 * The program does not provide any built-in facilities for saving the
 * current session, or loading previous sessions. However, it is easy 
 * to simulate saving/loading sessions on unix/linux
 * (in the following, `$` denotes the command line prompt).
 *
 * The user input is read from STDIN.
 * Everything that is printed in interactive mode goes to STDERR.
 * When the program terminates, the resulting theory is printed to STDOUT.
 *
 * The most basic way to run the program is:
 * $ scala ipl_prover.scala
 * If you start the program this way, you will have to type in all the 
 * commands manually, and the resulting theory will be printed to the console.
 * 
 * If you want to save everything you type to a file, use `tee`:
 * $ tee myCommands.txt | scala ipl_prover.scala
 *
 * If you want to save the resulting scala code to a file, use stream
 * redirection:
 * $ scala ipl_prover.scala  > myTheory.scala
 *
 * You can also re-run your commands, again, using stream redirection:
 * $ scala ipl_prover.scala  < myCommands.txt   > myTheory.scala
 *
 * You can also "load" a previously saved session with a little more effort.
 * Remove the last `exit` command from your previously saved `myCommands.txt`
 * file, and start the interpreter this way:
 * $ cat myCommands.txt - | scala ipl_prover.scala
 * It will then re-run all the commands in `myCommands.txt` and go into 
 * interactive mode again.
 *
 * Of course, you can combine all of the above, for example:
 * $ cat myPreviousSession.txt - | tee myNewSession.txt | \
 *   scala ipl_prover.scala > myTheory.scala
 * will re-run all commands from `myPreviousSession.txt` and switch into 
 * interactive mode, saving all commands (old and new) to `myNewSession.txt`,
 * and saving the final output to `myTheory.scala`.
 *
 * IPC-Terms
 * =========
 *
 * The object language (IPC) is defined as follows:
 *   - Atoms are strings that match the regex `[A-Z]+` (e.g. `P`, `Q`, `R`)
 *   - The bottom term `Nothing` is in IPC.
 *   - If a, b are some meta-variables that represent terms of IPC, 
 *     then `(a /\ b)`, `(a \/ b)`, `(a => b)` are also in IPC.
 *     These connectives stand for conjunction, disjunction and implication. 
 *   - There is "syntactic sugar" for negation: `Neg[A]` is shorthand for
 *     `A => Nothing`.
 * The parentheses can be omitted sometimes, the precedence order is as follows:
 * `=>`, `\/`, `/\`, `Neg`. Here are few examples of varid IPC terms:
 * `P => Q /\ (R \/ X)`, `(A => (B => C)) => ((A => B) => A => C)`.
 *
 * PROVING
 * =======
 * 
 * The basic workflow is as follows: 
 * (1) You create a new theorem
 * (2) You enter rules with variable names and type-hints (one at a time),
 *    until the theorem is proved. Then the new theorem becomes available 
 *    as a new rule, and you either continue with (1) or exit.
 * 
 * To create a new theorem, enter:
 * > theorem myThmName [ <Assumption_1>; ...; <Assumption_N> ] => <Conclusion> 
 * Here, all <Assumption_i> and <Conclusion> must be valid IPC terms.
 * An expression like `[A; B; C] => X` is essentially equivalent to
 * `A => B => C => X`, however, there is a little difference: when you will
 * try to apply your theorem later, the proof assistant will try to unify
 * your goal with `X`. In case of success, additional goals will be 
 * created, one goal for each assumption `A`, `B`, `C`. 
 * Thus, for example two theorems
 * with statements `[A ; B] => B /\ A` and `[A] => (B => B /\ A)` 
 * are essentially equivalent, but the conclusion of the former will be 
 * unifiable with the goal
 * `X /\ (Y \/ Z)` and not unifiable with `X => X /\ (Y \/ Z)`, whereas
 * the conclusion of the latter will not be unifiable with `X /\ (Y \/ Z)` but
 * with `X => X /\ (Y \/ Z)`.
 *
 * To prove a theorem, repeatedly apply rules to the current goal 
 * (backward-reasoning). Currently available rules can be listed by issuing the 
 * command `list_rules`. 
 * Initially, there are only 10 rules:
 *
 *   Assumption                           (`assumption`)
 *   Implication introduction             (`impl_intr`)
 *   Implication elimination              (`impl_elim`)
 *   Conjunction introduction             (`conj_intr`)
 *   Conjunction elimination (left)       (`conj_elim_1`)
 *   Conjunction elimination (right)      (`conj_elim_2`)
 *   Disjunction introduction (left)      (`disj_intr_1`)
 *   Disjunction introduction (right)     (`disj_intr_2`)
 *   Disjunction elimination              (`disj_elim`)
 *   Explosion principle                  (`explosion`)
 *
 * Some of the rules require extra parameters: either variable names, or
 * valid IPC-Formulas. For example, if the list of assumptions contains
 * a proof `x` of formula `X`, and your goal is to show `X`, you have to 
 * explicitly specify the name of the assumption that you want to use: 
 *
 * > assumption(x)
 *
 * Sometimes, you have to specify extra formulas when applying a rule.
 * For example, if your current goal is `G`, and you want to show that it is
 * a result of disjunction elimination, you have to specify two extra formulas
 * as hints. For example, if you want to show `G` by showing three formulas
 * `(X => Z) \/ Y`, `(X => Z) => G`, and `Y => G`, 
 * you would have to invoke the `disj_elim` rule as follows:
 * 
 * > disj_elim[X => Z, Y]
 * 
 * Notice that curly braces are used to specify formulas, while round 
 * parentheses are used to specify variable names. You can always list 
 * all available rules using the `list_rules` command. It will also 
 * tell you what hints each rule requires.
 *
 * TERMINATING THE PROGRAM
 * =======================
 * You can exit the program by typing `exit`. If you started the program 
 * using `cat` or `tee`, you might have to press `Ctrl+D` additionally.
 * 
 * TYPE-CHECKING
 * =============
 * 
 * Save the output of the program to some file with ending ".scala", and
 * run it with the scala interpreter. If the type checker does not find any
 * errors, then our proofs are indeed sound.
 *
 * @author: Andrey Tyukin
 * @date: 2015-11-06
 * 
 *
 * GPLv3 Licence
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
/*##############################################################################
              Logical formulas (grafting, unification)
##############################################################################*/

sealed trait Formula {
  def graft(f: String => Formula): Formula
  def unify(target: Formula): Option[Map[String, Formula]]
  def atoms: Set[Proposition]
}

object Formula {

  /** Merges two unification results, if at all possible */
  private def merge(x: Map[String, Formula], y: Map[String, Formula]): 
    Option[Map[String, Formula]] = {
    val keys = x.keySet ++ y.keySet
    var res = new scala.collection.mutable.HashMap[String, Formula]
    for (k <- keys) {
      if (x.contains(k)) {
        if (y.contains(k)) {
          val xv = x(k)
          val yv = y(k)
          if (xv == yv) {
            res(k) = xv
          } else {
            // two incompatible values, that's bad
            return None
          }
        } else {
          res(k) = x(k)
        }
      } else if (y.contains(k)) {
        res(k) = y(k)
      } else {
        throw new Error("Either `Map.keySet` or the merging algo has a bug")
      }
    }
    return Some(res.toMap)
  }

  def unifyTwo(aPat: Formula, aTrg: Formula, bPat: Formula, bTrg: Formula):
    Option[Map[String, Formula]] = {
    for {
      left <- aPat.unify(aTrg)
      right <- bPat.unify(bTrg)
      combination <- merge(left, right)
    } yield combination
  }
}

case object Bottom extends Formula {
  override def toString = "Nothing"
  def graft(f: String => Formula) = this
  def unify(target: Formula) = target match {
    case Bottom => Some(Map.empty)
    case sthElse => None
  }
  def atoms = Set.empty
}

case class Proposition(name: String) extends Formula {
  override def toString = name
  def graft(f: String => Formula) = f(name)
  def unify(target: Formula) = Some(Map(name -> target))
  def atoms = Set(this)
}

case class Implication(condition: Formula, conclusion: Formula) extends Formula{
  /** Implication with negation as special case */
  override def toString = {
    conclusion match {
      case Bottom => "Neg[%s]".format(condition)
      case _ => "(%s => %s)".format(condition, conclusion)
    }
  }
  def graft(f: String => Formula) = Implication(
    condition graft f,
    conclusion graft f
  )
  def unify(target: Formula) = target match {
    case Implication(aTrg, bTrg) => 
      Formula.unifyTwo(condition, aTrg, conclusion, bTrg)
    case sthElse => None
  }
  def atoms = condition.atoms ++ conclusion.atoms
}

case class Conjunction(a: Formula, b: Formula) extends Formula {
  override def toString = "(%s /\\ %s)".format(a, b)
  def graft(f: String => Formula) = Conjunction(a graft f, b graft f)
  def unify(target: Formula) = target match {
    case Conjunction(aTrg, bTrg) => Formula.unifyTwo(a, aTrg, b, bTrg)
    case _ => None
  }
  def atoms = a.atoms ++ b.atoms
}

case class Disjunction(a: Formula, b: Formula) extends Formula {
  override def toString = "(%s \\/ %s)".format(a, b)
  def graft(f: String => Formula) = Disjunction(a graft f, b graft f)
  def unify(target: Formula) = target match {
    case Disjunction(aTrg, bTrg) => Formula.unifyTwo(a, aTrg, b, bTrg)
    case _ => None
  }
  def atoms = a.atoms ++ b.atoms
}

/*##############################################################################
                           Contexts and Entailments
##############################################################################*/
case class Context(map: Map[String, Formula]) {
  def toString(pref: String, fmt: String, sep: String, suff: String): String = {
    val keys = map.keySet
    (for (k <- keys.toList.sorted) yield {
      fmt.format(k, map(k).toString)
    }).mkString(pref, sep, suff)
  }
  override def toString: String = toString("(", "%s : %s", ", ", ")")
  def apply(name: String) = map(name)
  def updated(name: String, value: Formula) = 
    new Context(map.updated(name, value))
  def contains(name: String) = map.contains(name)
}

/** Entailments
 * "(p_1: Formula_1, ..., p_n: Formula_n) |- Formula"
 */
case class Entailment(context: Context, formula: Formula) {
  override def toString = context.toString + " |- " + formula
  def toMultilineString = 
    context.toString("", "%4s : %s", "\n", "") + 
    "\n" + ("=" * 60) + "\n" + "Goal: " + formula
  def toShortString = {
    val shortCtx = context.map.toList.map(_._2).mkString("[",", ","]")
    shortCtx + " |- " + formula
  }
}

/*##############################################################################
                              Inference rules
##############################################################################*/
import scala.util.{Either, Left, Right}

trait InferenceRule {
  def shortName: String 
  /** 
   * In the backward reasoning mode, the rule is applied to the goal.
   * 
   * Some inference rules (e.g. Assumption, ImplicationIntroduction) require 
   * a name of a context elements as input, the `names` array is for those 
   * cases.
   *
   * Since the propositions in the upper half cannot always be 
   * inferred from the lower half of inference rule, additional hints 
   * might be necessary. 
   *
   * Example: if we want to apply the modus ponens 
   * (from `A, A => B` infer `B`) to the entailment `|- X`, then we can unify
   * `B` to be `X`, but we cannot automatically figure out what `A` is supposed
   * to be. Thus, the modus ponens requires a single hint-formula to unify `A`
   * with it.
   *
   * The rule returns a list of new goals in the
   * case of successful application (`Right`), 
   * or a human-readable error message in the case that this rule is not
   * applicable to the current goal (`Left`).
   * 
   * The reason why the `Right`-return type is a list rather than a single new 
   * `Entailment` is that lot of rules have multiple prerequisites on the top,
   * for example, the disjunction elimination rule 
   * (from `A => Z, B => Z, A \/ B` infer `Z`) splits a single goal into three
   * separate goals.
   */
  def backwardReasoning(
    goal: Entailment,
    names: List[String], 
    hints: List[Formula]
  ): Either[String, List[Entailment]]

  /**
   * Creates a label that captures some variable names
   * and can be used to label transitions between entailments,
   * that is, it captures with which arguments this inference rule 
   * has been invoked.
   */
  def createLabel(names: List[String], hints: List[Formula]): InferenceRuleLabel
}

/** 
 * Implication introduction is somewhat unusual among all the other rules, 
 * because it modifies the context.
 */
object ImplicationIntroduction extends InferenceRule {
  val shortName = "impl_intr"
  private val pattern = IpcParser.forceParseFormula("A => B")
  
  def backwardReasoning(
    goal: Entailment, 
    names: List[String], 
    hints: List[Formula]
  ): Either[String, List[Entailment]] = {
    if (names.size != 1) 
      return Left("need a single variable name")
    if (!hints.isEmpty) {
      return Left("received to many hints, expected: 0, got = " + hints.size)
    }
    val newVarName = names(0)
    if (!newVarName.matches("[a-zA-Z0-9_]+")) 
      return Left("invalid variable name: " + newVarName)
    pattern.unify(goal.formula) match {
      case None => Left("Unification failed: goal is not of shape " + pattern)
      case Some(binding) => {
        val modified = Entailment(
          goal.context.updated(newVarName, binding("A")),
          binding("B")
        )
        Right(List(modified))
      }
    }
  }

  def createLabel(names: List[String], hints: List[Formula]) = 
    ImplIntro(names.head)

  override def toString = {
    "impl_intr(<nameOfIntroducedAssumption>)"
  }
}

/** 
 * Assumption is another example of a rather irregular rule that looks at
 * the context.
 */
object Assumption extends InferenceRule {
  val shortName = "assumption"
  def backwardReasoning(
    goal: Entailment, 
    names: List[String], 
    hints: List[Formula]
  ): Either[String, List[Entailment]] = {

    if (names.size != 1) 
      return Left("need a single variable name")
    val varName = names(0)
    if (!varName.matches("[a-zA-Z0-9_]+")) 
      return Left("invalid variable name: " + varName)
    if (!goal.context.contains(varName)) 
      return Left("no assumption named '" + varName + "'")
    if (!hints.isEmpty) 
      return Left("received to many hints, expected: 0, got = " + hints.size)
    
    if(goal.formula == goal.context(varName)) {
      Right(List()) // no more goals, done
    } else {
      Left("The assumption '" + varName + "' is not the same as the goal")
    }
  }

  def createLabel(names: List[String], hints: List[Formula]) = 
    Assump(names.head)

  override def toString = {
    "assumption(<nameOfAssumptionToUse>)"
  }
}

/** 
 * A generic rule that does not look at the context.
 */
class ContextInvariantRule(
  val shortName: String,
  val antecedents: List[Formula], 
  val consequence: Formula,
  val shortLabel: String
) extends InferenceRule {
  // Alphabetically sorted list of variables that cannot be inferred from
  // the goal, and therefore need a hint.
  val propositionsNeedingHint: List[String] = {
    val inferableVariables = consequence.atoms
    val antecedentVariables = 
      antecedents.map{_.atoms}.foldLeft(Set.empty[Proposition]){ _ ++ _ }
    val resProps = 
      antecedentVariables.filterNot{ inferableVariables.contains }
    val res = resProps.toList.map{_.name}.sorted
    res
  }

  def backwardReasoning(
    goal: Entailment, 
    names: List[String], 
    hints: List[Formula]
  ): Either[String, List[Entailment]] = {
    if (!names.isEmpty) 
      return Left("no variable names required, but found " + names.size)  
    if (hints.size != propositionsNeedingHint.size) 
      return Left("wrong number of hints: need " + 
        propositionsNeedingHint.size + " hints for " +
        propositionsNeedingHint.mkString(", ") + " (in this order)")
    consequence.unify(goal.formula) match {
      case None => Left("unification failed: goal not of shape " + consequence)
      case Some(binding) => {
        val hintBinding = (propositionsNeedingHint zip hints).toMap
        val fullBinding = binding ++ hintBinding
        val newGoalList = for (a <- antecedents) yield {
          Entailment(goal.context, a.graft(fullBinding))
        }
        Right(newGoalList)
      }
    }
  }

  def createLabel(names: List[String], hints: List[Formula]) = 
    Regular(shortName, shortLabel)

  override def toString = {
    shortName + 
    antecedents.mkString("[",";","]") + " => " + consequence + 
    (if (propositionsNeedingHint.isEmpty) "" else {
    "   needs hints for: " + propositionsNeedingHint.mkString(",")
    })
  }
}

/*##############################################################################
                       Parser for logical formulas
##############################################################################*/
import scala.util.parsing.combinator._

trait IpcParsers extends JavaTokenParsers {
  def bottomConstant: Parser[Formula] = "Nothing" ^^^ Bottom
  def propId: Parser[String] = 
    "[a_zA-Z][_a-zA-Z0-9]*".r |
    failure("expected proposition id")
  def propVariable: Parser[Proposition] = propId ^^ {
    case x => Proposition(x)
  }
  // remember: `Neg` looks like proposition variable, so it has to go before
  // `propVariable`, otherwise we get dangling left-paren errors.
  def conjunct: Parser[Formula] = 
    bottomConstant |
    ("Neg[" ~> formula <~ "]") ^^ { case x => Implication(x, Bottom) } |
    propVariable | "(" ~> formula <~ ")"
  def disjunct: Parser[Formula] = rep1sep(conjunct, "/\\") ^^ {
    case conjuncts => conjuncts.reduceLeft[Formula] { 
      case (a, b) => Conjunction(a, b) 
    }
  }
  def implicant: Parser[Formula] = rep1sep(disjunct, "\\/") ^^ {
    case disjuncts => disjuncts.reduceLeft[Formula] { 
      case (a, b) => Disjunction(a, b) 
    }
  }
  def formula: Parser[Formula] = rep1sep(implicant, "=>") ^^ {
    case implicants => implicants.reduceRight[Formula] {
      case (a, b) => Implication(a, b)
    }
  }

  def ruleFormula: Parser[(List[Formula], Formula)] = 
    ("[" ~> repsep(formula, ";") <~ "]" <~ "=>") ~ formula ^^ {
      case premises~conclusion => (premises, conclusion)
    }

  def parseFormula(s: String): Either[String, Formula] = 
  parseAll(formula, s) match {
    case Success(t, _) => Right(t)
    case f => Left(f.toString)
  }
  /** unsafe parse-method unsuitable for user interaction */
  def forceParseFormula(s: String): Formula = parseFormula(s) match {
    case scala.util.Right(t) => t
    case _ => throw new Exception("could not parse formula")
  }
}

object IpcParser extends IpcParsers

/*
// little parser example
for (example <- List(
  """A /\ B""", 
  """A /\ B \/ C /\ D""",
  """A /\ B /\ C \/ D /\ (E => F /\ H) => G \/ A /\ B \/ (C \/ D => A)""",
  """Neg[X]""",
  """Neg[Neg[A => B]]""",
  """Neg[Neg[Neg[X]]] => Neg[X]""",
  """(A => B /\ C) => (Neg[B /\ C] => Neg[A])"""
)) {
  System.err.println(IpcParser.parseFormula(example))
}

// little unification example
val pat = IpcParser.forceParseFormula(""" (A \/ B) /\ (B \/ A) => C """)
val trg = IpcParser.forceParseFormula(
  """ ((Q /\ R => Z) \/ P /\ Q) /\ (P /\ Q \/ (Q /\ R => Z)) => Y /\ E /\ S""")
System.err.println(pat.unify(trg))
*/

/*##############################################################################
                Inference rules of intuitionistic propositional logic
##############################################################################*/
def rule(name: String, shortLabel: String, formulas: String*): 
ContextInvariantRule = {
  require(!formulas.isEmpty)
  val consequence = IpcParser.forceParseFormula(formulas.last)
  val antecedents = formulas.toList.dropRight(1).map{ 
    IpcParser.forceParseFormula 
  }
  new ContextInvariantRule(name, antecedents, consequence, shortLabel)
}

val IpcRules = List(
  Assumption,
  ImplicationIntroduction,
  rule("impl_elim", "-I", "A => B", "A", "B"),
  rule("explosion", "F!", "Nothing", "A"),
  rule("conj_intr", "+C", "A", "B", "A /\\ B"),
  rule("conj_elim_1", "-C1", "A /\\ B", "A"),
  rule("conj_elim_2", "-C2", "A /\\ B", "B"),
  rule("disj_intr_1", "+D2", "A", "A \\/ B"),
  rule("disj_intr_2", "+D1", "B", "A \\/ B"),
  rule("disj_elim", "-D", "A => Z", "B => Z", "A \\/ B", "Z")
)

/*##############################################################################
                               CLI-Parser
##############################################################################*/
sealed trait Command

case class NewTheoremCommand(
  name: String, 
  assumes: List[Formula], 
  shows: Formula
) extends Command

case class RuleCommand(cmd: String, names: List[String], hints: List[Formula])
extends Command

case object Undo extends Command
case object Terminate extends Command
case object Help extends Command
case object ListRules extends Command

trait CommandParsers extends IpcParsers {
  def hints: Parser[List[Formula]] = 
    ("{" ~> repsep(formula, ",") <~ "}") |
    ("") ^^^ Nil
  def name: Parser[String] = "[a-zA-Z][a-zA-Z0-9_]*".r
  def names: Parser[List[String]] = 
    "(" ~> repsep(name, ",") <~ ")" |
    "" ^^^ Nil
  def ruleCommand: Parser[Command] = name ~ names ~ hints ^^ {
    case c~ns~hs => RuleCommand(c, ns, hs)
  }
  def newThmCommand: Parser[Command] = 
    ("(theorem)|(lemma)".r ~> name) ~ ruleFormula ^^ {
      case n~((ps, c)) => NewTheoremCommand(n, ps, c)
    }
  def undoCommand: Parser[Command] = "undo" ^^^ Undo
  def terminateCommand: Parser[Command] = "(end)|(quit)|(exit)".r ^^^ Terminate
  def listRules : Parser[Command] = "list_rules" ^^^ ListRules
  def help: Parser[Command] = "(help)|(Help)|(\\?+)".r ^^^ Help
  def command = help | listRules | undoCommand | 
    terminateCommand | newThmCommand | ruleCommand
  def parseCommand(s: String): Either[String, Command] = {
    parseAll(command, s) match {
      case Success(t, _) => Right(t)
      case f => Left(f.toString)
    }
  }
}

object CommandParser extends CommandParsers

/*##############################################################################
                                  Utils
##############################################################################*/
// generation of reasonable assumption names from formulas
def generateReasonableName(f: Formula, blackList: Set[String]): String = {
  def canonicalName(f: Formula): String = f match {
    case Bottom => "F"
    case Proposition(x) => x.toLowerCase
    case Implication(l, r) => "I" + canonicalName(l) + canonicalName(r)
    case Disjunction(l, r) => "D" + canonicalName(l) + canonicalName(r) 
    case Conjunction(l, r) => "C" + canonicalName(l) + canonicalName(r)
  }
  val prefix = canonicalName(f)
  var res = prefix
  if (blackList.contains(prefix)) {
    var idx = 2
    var res = prefix + "_" + idx
    while(blackList.contains(res)) {
      idx += 1
    }
  }
  res
}

/** Assigns more or less reasonable names to formulas */
def nameAssumptions(assumptions: List[Formula]): List[(String, Formula)] = {
  assumptions match {
    case Nil => Nil
    case h :: t => {
      val smallerCtx = nameAssumptions(t)
      val blackList = smallerCtx.map(_._1).toSet
      val newName = generateReasonableName(h, blackList)
      (newName, h) :: smallerCtx
    }
  }
}

// little helper method to write two pieces of text near each other,
// similar to what `diff` usually does.
def diff(a: String, b: String, separator: String = " "): String = {
  val as = a.split("\n").toList
  val bs = b.split("\n").toList
  val (pas, pbs) = if (as.size < bs.size) {
    (List.fill(bs.size - as.size){""} ++ as, bs)
  } else {
    (as, List.fill(as.size - bs.size){""} ++ bs)
  }
  val w = as.map{_.size}.max
  val hpas = pas.map{_.padTo(w, ' ')} // horizontally padded a-lines
  val ls = for ((al, bl) <- hpas zip pbs) yield (al + separator + bl)
  ls.mkString("\n")
}

def maxLineWidth(a: String): Int = a.split("\n").map{_.size}.max
def centerString(s: String, length: Int, pad: Char = ' '): String = {
  val halfLen = (length - s.size) / 2
  val rHalf = length - s.size - halfLen
  (("" + pad) * halfLen) + s + (("" + pad) * rHalf)
}

def hline(msg: String): Unit = {
  System.err.println("\n" + centerString(msg, 80, '~') + "\n")
}
/*##############################################################################
                             visitors with state
##############################################################################*/

/**
 * immutable proof-rewriting 
 * visitor with "state" modeled by explicitly returned new
 * instances of visitor.
 */
sealed trait Visitor

trait ActiveVisitor extends Visitor {
  def apply(p: ProofTodo): (Proof, Visitor)
}
trait SuccessfulVisitor extends Visitor
trait FailedVisitor extends Visitor

/*##############################################################################
                          Proof-state data structure
##############################################################################*/

// The `InferenceRule` trait defined earlier is good at modifying the state 
// of the prover, but as a mere label for a transition between two entailments,
// it's overkill. We use more lightweight rule-labels instead
sealed trait InferenceRuleLabel {
  def toShortString: String
}

case class Assump(varName: String) extends InferenceRuleLabel {
  override def toString = "asmp:" + varName
  def toShortString = "A"
}
case class ImplIntro(varName: String) extends InferenceRuleLabel {
  override def toString = varName
  def toShortString = "+I"
}
case class Regular(
  ruleName: String,
  toShortString: String
) extends InferenceRuleLabel {
  override def toString = ruleName
}

/** 
 * piece of proof that knows what it proves, and also allows a stateful
 * visitor to modify todo-leafs.
 */
sealed trait Proof {
  def goal: Entailment // what does this proof prove?
  def visit(v: Visitor): (Proof, Visitor) 
  def hasTodos: Boolean
  def allTodos: List[ProofTodo]
}

/** 
 * A proof can be seen as a rooted tree.
 * A single entailment, together with an inference rule that
 * breaks the entailment up into subgoals constitutes a single node label.
 * Edges are unlabeled.
 * Each node has a list of its children (subgoals generated by backward 
 * inference rule application).
 */
case class ProofRuleApplication(
  goal: Entailment, 
  rule: InferenceRuleLabel,
  children: List[Proof]
) extends Proof {

  private def helpVisit(list: List[Proof], v: Visitor): 
    (List[Proof], Visitor) = {
    
    v match {
      case _ : SuccessfulVisitor => (list, v)
      case _ : FailedVisitor => (list, v)
      case _ : ActiveVisitor => {
        list match {
          case Nil => (list, v)
          case h :: t => {
            val (hh, vv) = h.visit(v)
            val (tt, vvv) = helpVisit(t, vv)
            (hh :: tt, vvv)
          }
        }
      }
    }
  }

  def visit(visitor: Visitor) = {
    val (cs, vv) = helpVisit(children, visitor)
    (this.copy(children = cs), vv)
  } 

  def hasTodos = children.exists{ _.hasTodos }
  def allTodos = children.flatMap{ _.allTodos }
  override def toString = {
    val cs = children.map{_.toString}
    val cs_glued = 
      if (cs.isEmpty) "" 
      else cs.reduce[String]{ case (x, y) => diff(x, y, "  ") }
    val goalStr = goal.toShortString
    val barLength = Math.max(maxLineWidth(cs_glued), goalStr.size)
    val bar = "-" * barLength
    val centerGoalStr = centerString(goalStr, barLength)
    cs_glued + "\n" +
    bar + "(" + rule.toShortString + ")" + "\n" +
    centerGoalStr
  }
}

/** Unfinished piece of proof that is still in the todo-list */
case class ProofTodo(goal: Entailment) extends Proof {
  def visit(visitor: Visitor) = {
    visitor match {
      case v: ActiveVisitor => {
        val (j, nextV) = v(this)
        (j, nextV)
      }
      case _ => (this, visitor)
    }
  }
  def hasTodos = true
  def allTodos = List(this)
  override def toString = { 
    // TODO: code duplication, bit rot...
    val cs = "???"
    val goalStr = goal.toShortString
    val barLength = Math.max(maxLineWidth(cs), goalStr.size)
    val bar = "-" * barLength
    val centerGoalStr = centerString(goalStr, barLength)
    cs + "\n" +
    bar + "(?)" + "\n" +
    centerGoalStr
  }
}

/** 
 * Named theorems are just proofs with a name.
 */
case class NamedTheorem(
  name: String, 
  orderedNamedAssumptions: List[(String, Formula)],
  proof: Proof
)

/*##############################################################################
                      Very restricted subset of Scala
##############################################################################*/

/** 
 * Represents pieces of Scala-code that can be used for proofs of
 * propositional logic formulas. Concrete implementations of `ScalaProof`
 * do essentially nothing except pretty-printing code that can be 
 * type-checked by the Scala-compiler.
 */
sealed trait ScalaProof {
  def toString(indentation: Int): String
  def typ: Formula
}

/** Introduces a variable */
case class ScalaLambda(
  varName: String, 
  typ: Formula,
  child: ScalaProof
) extends ScalaProof {
  def toString(indentation: Int): String = {
    "{ " + varName + " => " + child.toString(indentation + 2) + "\n" +
    (" " * indentation) + "}"
  }
}

/** Uses a variable */
case class ScalaUseVariable(
  varName: String,
  typ: Formula
) extends ScalaProof {
  def toString(indentation: Int) = varName
}

/** Applies a regular rule */
case class ScalaRegular(
  ruleName: String, 
  typ: Formula,
  children: List[ScalaProof]
) extends ScalaProof {
  def toString(indentation: Int) = {
    val whitespace = " " * indentation

    "{\n" + 
    (for((idx, chld) <- Stream.from(0).zip(children)) yield {
      whitespace + "  val _g" + idx + ":" + chld.typ + " = " + 
      chld.toString(indentation + 2)
    }).mkString("\n") + "\n" + 
    whitespace + "  " + ruleName + "(" + 
    ((0 until children.size).map{ i => "_g" + i }).mkString(",") + ")\n" +
    whitespace + "}"
  }
}

/** Special "non-proof" for unfinished proof states */
case class ScalaTodo(typ: Formula) extends ScalaProof {
  def toString(indentation: Int) = "???"
}

/** 
 * Top-level function that represents named theorems.
 * Corresponds to `NamedTheorem` above.
 */
case class ScalaNamedTheorem(
  theoremName: String,
  proof: ScalaProof,
  genericParams: List[String],
  assumptions: List[(String, Formula)], // It's not a context! It's ordered.
  returnType: Formula
) {

  def toString(indentation: Int) = {
    val whitespace = " " * indentation
    val genParamsStr = if (genericParams.isEmpty) "" else { 
      genericParams.mkString("[", ",", "]") 
    }

    val args = if (assumptions.isEmpty) "" else {
      (assumptions.map { case (n, t) => n + ":" + t }).mkString("(", ",", ")")
    }

    whitespace + "def " + theoremName + genParamsStr + args + ":" + 
    returnType + " = " + 
    proof.toString(indentation)
  }
}

/*##############################################################################
            The Curry-Howard Isomorphism: (Proof -> Code)-direction
##############################################################################*/

def curryHowardIsomorphism(p: Proof): ScalaProof = p match {
  case ProofRuleApplication(g, Assump(v), _) => ScalaUseVariable(v, g.formula)
  case ProofRuleApplication(g, ImplIntro(v), cs) => 
    ScalaLambda(v, g.formula, curryHowardIsomorphism(cs.head))
  case ProofRuleApplication(g, Regular(r, _), cs) => 
    ScalaRegular(r, g.formula, cs map curryHowardIsomorphism)
  case ProofTodo(g) => ScalaTodo(g.formula)
}

def curryHowardIsomorphism(thm: NamedTheorem): ScalaNamedTheorem = {
  val NamedTheorem(name, assumptions, proof) = thm
  val goalFormula = proof.goal.formula
  val allFormulas = goalFormula :: assumptions.map(_._2)
  val genericParams = 
    allFormulas.flatMap{_.atoms}.map{_.name}.toSet.toList.sorted
  ScalaNamedTheorem(
    name,
    curryHowardIsomorphism(proof),
    genericParams,
    assumptions,
    goalFormula
  )
}

/*##############################################################################
                    Persistent state of the prover
##############################################################################*/
case class ProverState(
  previousState: Option[ProverState],
  rules: Map[String, InferenceRule],
  provedTheorems: List[NamedTheorem],
  activeTheorem: Option[NamedTheorem],
  terminated: Boolean
) {

  def terminate: ProverState = this.copy(terminated = true)

  def showCurrentGoal() {
    if (activeTheorem.isEmpty) {
      System.err.println("Currently nothing to show.\n" +
       "Start new theorem with:  'theorem <name> [<A1>;...;<An>] => <C>'")
    } else { 
      val todos = activeTheorem.get.proof.allTodos
      hline(" Assumptions & Goals ")
      System.err.println(todos.head.goal.toMultilineString)
      if (todos.size > 1) {
        val moreGoals = todos.tail.map{_.goal}
        System.err.println("  There are %d more goal(s):".format(moreGoals.size))
        val maxGoals = 5
        for ((i, g) <- (Stream.from(1).zip(moreGoals.take(maxGoals)))) {
          System.err.println("  (" + i + ")  " + g)
        }
        if (moreGoals.size > maxGoals) System.err.println("...")
      }
    }
  }

  def showRules() {
    for (r <- rules.toList.sortBy(_._1).map{_._2}) {
      System.err.println(r)
    }
  }

  def showIsomorphism() {
    if (activeTheorem.isEmpty) {
      // do nothing 
    } else {
      val thm = activeTheorem.get
      val scalaCode = curryHowardIsomorphism(thm).toString(indentation = 0)
      hline(" Code ")
      System.err.println(scalaCode)
      hline(" Natural deduction proof ")
      System.err.println(thm.proof)
    }
  }

  def undo: ProverState = 
    if (previousState.isEmpty) this else previousState.get

  def newTheorem(ntc: NewTheoremCommand): ProverState = {
    val NewTheoremCommand(name, premises, conclusion) = ntc
    if (activeTheorem.isEmpty) {
      if (!rules.contains(name)) {
        val assumptionList = nameAssumptions(ntc.assumes)
        val initialContext = new Context(assumptionList.toMap)
        val topLevelGoal = Entailment(initialContext, ntc.shows)
        val thm = NamedTheorem(name, assumptionList, ProofTodo(topLevelGoal))
        val nextState = ProverState(
          previousState = Some(this),
          rules = this.rules,
          provedTheorems = provedTheorems,
          activeTheorem = Some(thm),
          terminated = false
        )
        nextState
      } else {
        System.err.println(
          "Error: a rule / theorem / lemma with name '" + name + 
          "' already exists"
        )
        this
      }
    } else {
      System.err.println(
        "Error: the current theorem " + activeTheorem.get.name + 
        " is not complete yet."
      )
      this
    }
  }

  /* Tries to apply an inference rule to the leftmost ProofTodo */
  private class InferenceRuleVisitor(
    rule: InferenceRule,
    varNames: List[String],
    hints: List[Formula]
  ) extends ActiveVisitor {
    def apply(p: ProofTodo): (Proof, Visitor) = {
      val goal = p.goal
      rule.backwardReasoning(goal, varNames, hints) match {
        case Right(newGoals) => {
          val packagedSubgoals = newGoals.map{ g => ProofTodo(g) }
          val expandedProof = ProofRuleApplication(
            goal,
            rule.createLabel(varNames, hints),
            packagedSubgoals
          )
          val successfulVisitor = new SuccessfulVisitor() {}
          (expandedProof, successfulVisitor)
        }
        case Left(errMsg) => {
          System.err.println("Error: " + errMsg)
          val failedVisitor = new FailedVisitor() {}
          (p, failedVisitor)
        }
      }
    }
  }

  /** 
   * Looks for the leftmost todo-subgoal, tries to apply the 
   * inference rule to it, and to build a new proof tree.
   */
  def applyInferenceRule(rc: RuleCommand): ProverState = {
    val RuleCommand(ruleName, varNames, hints) = rc
    if (!activeTheorem.isEmpty) {
      if (rules.contains(ruleName)) {
        val rule = rules(ruleName)
        val visitor = new InferenceRuleVisitor(rule, varNames, hints)
        activeTheorem.get.proof.visit(visitor) match {
          case (_, _: FailedVisitor) => {
            this
          }
          case (_, _: ActiveVisitor) => {
            throw new Error("Visited a proof that has no todo-nodes")
          }
          case (newProof, _: SuccessfulVisitor) => {
            if (newProof.hasTodos) {
              ProverState(
                previousState = Some(this),
                rules = this.rules,
                provedTheorems = this.provedTheorems,
                activeTheorem = 
                  Some(this.activeTheorem.get.copy(proof = newProof)),
                terminated = false
              )
            } else {
              val newThm = new NamedTheorem (
                this.activeTheorem.get.name,
                this.activeTheorem.get.orderedNamedAssumptions,
                newProof
              )
              // If the statement is know to be correct, we can use
              // it without the proof details. Extract the relevant
              // details from theorem, add it to the list of usable
              // rules.
              val newRule = new ContextInvariantRule(
                newThm.name,
                newThm.orderedNamedAssumptions.map{_._2},
                newProof.goal.formula,
                newThm.name
              )
              val newRules = this.rules.updated(newThm.name, newRule)
              val newProvedTheorems = newThm :: provedTheorems
              System.err.println("'" + newThm.name + "' QED")
              ProverState(
                previousState = Some(this),
                rules = newRules,
                provedTheorems = newProvedTheorems,
                activeTheorem = None,
                terminated = false
              )
            }
          }
        }
      } else {
        System.err.println("Error: rule '" + ruleName + "' not found.")
        this
      }
    } else {
      System.err.println("Error: no goals in queue, " + 
        "cannot apply any rules to anything")
      this
    }
  }
}

/*##############################################################################
          Piece of Scala code that implements all predefined 
                   natural deduction rules 
##############################################################################*/
val predef = """
// <BEGIN PREDEF>

// Types that represent disjunctions and conjunctions,
// essentially the same as `Either` and pair-types
sealed trait \/[A, B]
case class Inl[A, B](a: A) extends (A \/ B)
case class Inr[A, B](b: B) extends (A \/ B)

case class /\[A, B](a: A, b: B)

// Modus ponens is the implication elimination rule.
// modus ponens is just function application: A, A => B creates B
// The implication introduction is also not a method or axiom,
// but is rather modeled by Scala's anonymous function literals.

// Modus Ponens = function application
// Implication introduction = lambda abstraction

// however, for the purpose of theorem prover, it's actually 
// quite handy to have it as a rule that accepts two arguments
def impl_elim[A, B](f: A => B, x: A) : B = f(x)

// Disjunction introduction and elimination
def disj_intr_1[A, B](a: A) : A \/ B = Inl(a)
def disj_intr_2[A, B](b: B) : A \/ B = Inr(b)
def disj_elim[A, B, Z](az: A => Z, bz: B => Z, ab: A \/ B) :  Z = {
  ab match {
    case Inl(a) => az(a)
    case Inr(b) => bz(b)
  }
}

// Conjunction introduction and elimination
def conj_intr[A, B](a: A, b: B): A /\ B = /\(a, b)
def conj_elim_1[A, B](ab: A /\ B): A = ab.a
def conj_elim_2[A, B](ab: A /\ B): B = ab.b

// Nothing implies everything (explosion principle)
def explosion[X]: Nothing => X = { 
  unobtanium => throw new Exception("Gratz, you broke the world")
}

// Shorter notation for negation
type Neg[X] = (X => Nothing)
type Equiv[A, B] = (A => B) /\ (B => A)

// </END PREDEF>
"""

def printPredef() = println(predef)
/*##############################################################################
                                    Help
##############################################################################*/
val helpText = 
"""
To show this help message, enter `help`:
  > help

To show list of available rules, type `list_rules`:
  > list_rules

To undo the last action:
  > undo

To exit and print the proofs as terms:
  > exit

Creating new theorem: 

  General: 
    > theorem <thmName> [<Asump_1>; ... <Asump_n>] => <Consequence>
  Example:
    > theorem hypotSyllog [A => B; B => C] =>  A => C

Using a rule with specified variable names (e.g. 'assumption' or 'impl_intr'):

  General:
    > assumption(<nameOfUsedAssumption>)
    > impl_intr(<nameOfIntroducedVariable>)
  Example:
    > assumption(x)
    > impl_intr(foo)

Using a rule that requires hints (e.g. 'disj_elim', 'conj_elim_1')

  General: 
    > disj_elim{<firstEliminatedFormula>, <secondEliminatedFormula>}
    > conj_elim_1{<theEliminatedFormula>}
  Example:
    > disj_elim{A, B}
    > conj_elim_1{X}
"""

def printHelp() = System.err.println(helpText)
/*##############################################################################
                                  Main loop
##############################################################################*/
import scala.io.StdIn
val startRules = IpcRules.map{ r => (r.shortName, r) }.toMap
var proverState = ProverState(
  previousState = None,
  rules = startRules,
  provedTheorems = Nil,
  activeTheorem = None,
  terminated = false
)

while (!proverState.terminated) {
  System.err.print("\n" * 4 + "> ")
  val line = StdIn.readLine
  CommandParser.parseCommand(line) match {
    case Left(f) => System.err.println("Error: " + f)
    case Right(cmd) => {
      proverState = cmd match {
        case Help => { printHelp(); proverState }
        case ListRules => { proverState.showRules(); proverState }
        case Undo => proverState.undo
        case Terminate => proverState.terminate
        case ntc: NewTheoremCommand => proverState.newTheorem(ntc)
        case rc: RuleCommand => proverState.applyInferenceRule(rc)
      }
      if (!proverState.terminated) {
        proverState.showIsomorphism()
        proverState.showCurrentGoal()
      } else {
        // generate Scala-checkable code:
        // print predef and all proven theorems to stdout
        printPredef()
        for (thm <- proverState.provedTheorems.reverse) {
          println("\n")
          val scalaCode = curryHowardIsomorphism(thm).toString(indentation = 0)
          println("/" + "*")
          println(thm.proof)
          println("*" + "/")
          println(scalaCode)
        }
      }
    }
  }
}

/*##############################################################################
                              Proof tactics
##############################################################################*/

// THIS IS CRUFT
// This section contains a failed attempt to introduce automated proof tactics.
// The overall design turned out to be not flexible enough for this.
// Reason: application of atomic inference rules is way too intertwined with
// the prover-state, cutting this method out of the `ProverState` does not 
// seem possible without breaking everything else. 
//
// However, now I know how not to do it, and have a rough idea how to do it
// better.

/*
/** 
 * Tries to eliminate the rightmost todo-subgoal in the `proof` using
 * only the `availableRules` and additional arguments passed in `args`.
 * 
 * Returns a modified proof if it succeeds, or `None` otherwise.
 */
trait ProofTactic {
  def name: String

  
  def apply(
    proof: Proof, 
    availableRules: Map[String, InferenceRule], 
    args: Array[String]
  ): Option[Proof]
}

/**
 * Tries to apply assumption, conjunction introduction and
 * implication introduction as long as possible.
 * The `assumption` is always tried first, 
 * in order to get rid of as many subgoals as possible.
 * 
 * Succeeds as soon as it finds a `ProofTodo` node, even if it does 
 * nothing.
 */
case object Intros extends ProofTactic {
  def name = "intros"
  def apply(
    proof: Proof,
    availableRules: Map[String, InferenceRule],
    ignored_args: Array[String]
  ): Option[Proof] = {
    val assump = availableRules.get("assumption")
    val conjI = availableRules.get("conj_intr")
    val implI = availableRules.get("impl_intr")
    // there are two kinds of visitors: the first one only finds 
    // the (a _single_) first ProofTodo node, and then launches another visitor, 
    // which in turn hits _all_ ProofTodo nodes as long as possible.
    val singleSubgoalVisitor = new ActiveVisitor {
      def apply(todo: ProofTodo): (Proof, Visitor) = {
        val (modifiedSubproof, _) = todo.visit(recursiveVisitor)
        (modifiedSubproof, new SuccessfulVisitor() {})
      }
    }
    // this visitor is weird, it relaunches itself on the proofs it produces!
    def recursiveVisitor = new ActiveVisitor {
      def apply(todo: ProofTodo): (Proof, Visitor) = {
        val ent = todo.goal
        val Entailment(ctx, conclusion) = ent
        // use assumptions if possible
        val withoutAssumptions = (for (a <- assump) yield {
          if (ctx.exitst{ case (name, formula) => formula == conclusion }) {
            // can apply assumption, that's nice!
            val newEnts = a.backwardReasoning(ent, List(name), Nil)
            Nil
          } else {
            // return the entailment unchanged
            List(ent)
          }
        }).getOrElse(ent)
        // introduce as many variables as possible
        val withoutImplications = (for (i <- implI) yield {
          
        }).getOrElse(withoutAssumptions)
      }
    }
    proof.visit(singleSubgoalVisitor)
    
  }
}
*/
