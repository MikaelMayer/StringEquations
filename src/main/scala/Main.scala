import scala.collection.mutable.ListBuffer

object Main extends App {
  var mapping = Map[String, Var]()
  
  object ConcatVar {
    def apply(vars: Var*): ConcatVar = ConcatVar(vars.toList)
  }
  case class ConcatVar(vars: List[Var]) {
    def isEmpty = vars.isEmpty
    def head = vars.head
    def last = vars.last
    def take(i: Int) = ConcatVar(vars.take(i))
    def drop(i: Int) = ConcatVar(vars.drop(i))
    def length = vars.length
    def ++(other: ConcatVar) = ConcatVar(vars ++ other.vars)
    override def toString = if(isEmpty) "\"\"" else vars.map(_.toString).reduceLeft(_ + "+"+ _)
    
    private var origin: Option[ConcatVar] = None
    private var originExplained: Option[String] = None //Some(Thread.currentThread.getStackTrace.drop(1).take(5).mkString("\n"))
    def withOrigin(c: ConcatVar, reason: String): this.type = {
      origin = Some(c)
      originExplained = Some(reason)
      this
    }
    def toStringWithOrigin: String = this.toString + originExplained.map(o => s", and because of ${o} it comes from:\n").getOrElse("") + origin.map(_.toStringWithOrigin).getOrElse("")
    
    def copyFrom(other: ConcatVar): this.type = {
      if (origin == None) origin = other.origin
      if (originExplained == None) originExplained = other.originExplained
      this
    }
  }
  
  class Var(val name: String) extends Ordered[Var] {
    override def toString = name
    def length = Length(this)
    def compare(other: Var) = name.compare(other.name)
  }
  object Var {
    def apply(name: String) = mapping.get(name) match {
    case None =>
       val res = new Var(name)
       mapping += (name -> res)
       res
    case Some(v) => v
    }
    def fresh: Var = {
      def letter(i: Int) = 
        if(i <= 25) ('a'.toInt + i).toChar.toString
        else if(i < 51) ('A'.toInt + (i-26)).toChar.toString
        else ("a" + i)
      (Stream.from(10) find (i => !(mapping contains (letter(i))))) match {
        case Some(i) => Var(letter(i))
        case None => Var("$")
      }
    }
  }
  //implicit def listVarToConcatVar(i: List[Var]): ConcatVar = ConcatVar(i)
  
  case class Equation(left: ConcatVar, right: ConcatVar) {
    override def toString = {
      left + " = " +
      right
    }
    def expressions = List(left, right)
    /*var reason: String = "by hypothesis"
    def withReason(r: String): this.type = {
      reason = r
      this
    }*/
  }
  
  case class Problem(eqs: List[Equation]) {
    def &&(other: Equation): Problem = &&(Problem(List(other)))
    def &&(other: Problem): Problem = Problem(eqs ++ other.eqs) 
    override def toString = {
      val ls = eqs.map(_.toString)
      if(ls.isEmpty) "" else
        "/ " + ls.init.mkString("\n| ") + "\n\\ " + ls.last
    }
    def expressions: List[ConcatVar] = eqs.flatMap(_.expressions)
  }
  object Problem {
    def apply(s: String): Problem = {
      val equations = s.split("&&").toList.flatMap{t =>
        val eq = t.trim
        val same = eq.split("=").map(cv => cv.trim.split("").map(Var.apply).toList).toList
        assert(same.length >= 2, "Not enough number of equation terms in " + s + " for " + t)
        (((ListBuffer[Equation](), same.head) /: same.tail) {
          case ((l, a), b) => (l += Equation(ConcatVar(a), ConcatVar(b)), b)
        })._1.toList
      }
      Problem(equations)
    }
  }
  implicit def AugmentedString(s: String) {
    def ===(other: String): Problem = {
      Problem(List(Equation(ConcatVar(s.split("").map(Var.apply).toList),
                            ConcatVar(other.split("").map(Var.apply).toList))))
    }
  }
  
  implicit class ProblemConverter(val sc: StringContext) extends AnyVal {
    def p(args: Any*): Problem = Problem(sc.s(args: _*))
  }
  
  val proof = true
  
  /*val init = p"""
  ACB = aCb && AACBB = aaCbb
  """
  val a = Var("a")
  val A = Var("A")
  val b = Var("b")
  val B = Var("B")*/
  
  /*val init = p"""
  ADBDC = aDbDc &&
  AADBDCBDC = aaDbDcbDc &&
  ADBADBDCC = aDbaDbDcc &&
  AADBDCBADBDCC = aaDbDcbaDbDcc &&
  AADBADBDCCBDC = aaDbaDbDccbDc
  """*/
  
  
  /*val init = p"""abcd=badc"""
  val toprove = p"ab=ba"*/
  //println(init)
  //println((Congruences(init) ++* toprove.expressions).closure.canProve(toprove)
  
  // Problem of caribes
  /*val init = p"""czxd = zxdc &&
madzzxd = zxdmadz &&
dma = adm &&
mdzzxdczx = zzxdczxdm &&
adzx = dzxa &&
mdc = cmd &&
zzxdzxdm  = mdzzxdzx = zxdmdzzx"""

  val toprove = p"""mdzzx = zzxdm"""*/
  
  val init = p"""chd == hdc &&
madBdh == hdmadB &&
dma == adm &&
mdBdch == Bdchdm &&
adh = dha &&
mdc == cmd &&
Bdhdm  = mdBdh = hdmdB"""
  val h = Var("h")
  val B = Var("B")
  val toprove = p"""Bdm = mdB"""
  println((Congruences(init) ++* toprove.expressions).suppose(h.length  >= B.length).closure.canProve(toprove))

  /*val init = p"""chd = hdc &&
  madBdh = hdmadB &&
  dma = adm &&
  mdBdch = Bdchdm &&
  adh = dha &&
  mdc = cmd &&
  Bdhdm  = mdBdh = hdmdB"""

  val h = Var("h")
  val B = Var("B")*/

/*.simplifiedAfterClosure)//.suppose(a.length < A.length).suppose(B.length < b.length))*/
  
  
  /*
    .suppose(h.length > B.length))*/

  object Congruences {
    def apply(): Congruences = new Congruences(List[Set[ConcatVar]](), (_: ConcatVar) => None, Nil)
    def apply(p: Problem): Congruences = Congruences() ++ p
    
    def computeReverseIndex(sets: List[Set[ConcatVar]]) = {
      val res = sets.zipWithIndex.flatMap{ case (set, i) => set.toList.map(cv => (cv, i))}
      res.toMap.get _
    }
  }
  
  def pairs(set: Set[ConcatVar]): Iterable[(ConcatVar, ConcatVar)] = {
    val l = set.toSeq.toArray
    val n = l.length
    for { i <- (0 until n).toSeq
          j <- (i+1) until n} yield (l(i), l(j))
  }
  
  class Congruences( val sets: List[Set[ConcatVar]], val reverseIndex: ConcatVar => Option[Int], val constraints: List[BoolExpr]) {
    //require(sets.forallWithIndex((set, i) => set.forall(e => reverseIndex(e) == Some(i))) and if not in sets, reverseIndex = None)
    def +(other: Equation) = assertEqual(other.left, other.right)
    
    def ++(other: Problem) = (this /: other.eqs)(_.+(_))
 
    
    override def toString = {
      val ls = sets.map(set => set.mkString(" = "))
      (if(ls.length == 0) "{}" else if(ls.length == 1) "{ " + ls.head + " }"
      else "{ \n  " + ls/*.sortBy(s => s.length)*/.mkString(",\n  ") + "\n}") + " " + constraints.mkString(",")
    }
    
    def areEqual(a: ConcatVar, b: ConcatVar): Option[Boolean] = {
      (reverseIndex(a), reverseIndex(b)) match {
        case (Some(i), Some(j)) =>
          if (i == j) Some(true) else None
        case _ => None
      }
    }
    
    def +*(a: ConcatVar): Congruences = {
      var ai = reverseIndex(a)
      ai match {
      case Some(i) => this
      case None => 
        val newIndex = sets.length
        val newSet = Set(a)
        val newSets = sets :+ newSet
        val newReverseIndex = (c: ConcatVar) => if(newSet(c)) Some(newIndex) else reverseIndex(c) 
        new Congruences(newSets, newReverseIndex, constraints)
      }
    }
    def ++*(other: List[ConcatVar]): Congruences = (this /: other)(_.+*(_))
    
    def canProve(e: Equation): String = {
      val ai = reverseIndex(e.left)
      val bi = reverseIndex(e.right)
      (ai, bi) match {
        case (Some(ai), Some(bi)) if ai == bi =>
          val s = sets(ai)
          println(s"index in set: $ai")
          val eleft = s.find(i => i == e.left).get
          val eright = s.find(i => i == e.right).get
          s"$e proven because on one hand:\n" + eleft.toStringWithOrigin + "\n and on the other hand:\n" + eright.toStringWithOrigin
        case _ => s"No proof found for $e"
      }
    }
    def canProve(p: Problem): String = 
      p.eqs.map{ eq => canProve(eq)}.mkString("\n")
  
    def assertEqual(a: ConcatVar, b: ConcatVar): Congruences = {
      //println(s"Asserting equality between $a and $b")
      val ai = reverseIndex(a)
      val bi = reverseIndex(b)
      (ai, bi) match {
        case (None, None) => 
          //println("Not in set, adding them")
          val newIndex = sets.length
          val newSet = Set(a, b)
          val newSets = sets :+ newSet
          val newReverseIndex = (c: ConcatVar) => if(newSet(c)) Some(newIndex) else reverseIndex(c) 
          new Congruences(newSets, newReverseIndex, constraints)
        case (Some(ai), None) =>
          //println(s"Adding $b to the congruence set of $a")
          val newSets = sets.updated(ai, sets(ai) + b)
          val newReverseIndex = (c: ConcatVar) => if(c == b) Some(ai) else reverseIndex(c)
          new Congruences(newSets, newReverseIndex, constraints)
        case (None, Some(bi)) =>
          //println(s"Adding $a to the congruence set of $b")
          val newSets = sets.updated(bi, sets(bi) + a)
          val newReverseIndex = (c: ConcatVar) => if(c == a) Some(bi) else reverseIndex(c)
          new Congruences(newSets, newReverseIndex, constraints)
        case (Some(ai), Some(bi)) =>
          // We merge the biggest into the smallest.
          if (ai == bi) {
            //println(s"Nothing to change, already equal")
            this
          } else {
            val aset = sets(ai)
            val bset = sets(bi)
            //println(s"Merging congruence sets $aset and $bset")
            //println(a.toStringWithOrigin)
            //println(b.toStringWithOrigin)
            //println(
            aset.collectFirst{ case sa if sa == a => sa }.get.copyFrom(a)
            //.toStringWithOrigin)
            //println(
            bset.collectFirst{ case sb if sb == b => sb }.get.copyFrom(b)
            //.toStringWithOrigin)
            
            val (i1, i2) = (if (ai < bi) (ai, bi) else (bi, ai))
            val newSetAi = sets(i1) ++ sets(i2)
            val tmpSets = sets.updated(i1, newSetAi)
            val newSets = tmpSets.take(i2) ++ tmpSets.drop(i2 + 1)
            val newReverseIndex = (c: ConcatVar) => {
              reverseIndex(c) match {
                case None => None
                case s@Some(i) if i < i2 => s
                case s@Some(i) if i == i2 => Some(i1)
                case s@Some(i) if i > i2 => Some(i - 1)
              }
            }
            new Congruences(newSets, newReverseIndex, constraints)
          }
      }
    }
    
    def simplifiedAfterClosure = {
      val new_equations = ListBuffer[Equation]()
      // Removes dummy equations
      def simplify(s: Set[ConcatVar]): Option[Set[ConcatVar]] = {
        if (s.size != 2) Some(s)
        else {
          if((s.flatMap(a => a.take(1).vars).toSet).size == 1 || 
            (s.flatMap(a => a.drop(a.length - 1).vars).toSet).size == 1) {
            None
          } else Some(s)
        }
      }
      val newSets = for{set <- this.sets
         newset <- simplify(set)
        } yield {
         newset
      }
      new Congruences(newSets, Congruences.computeReverseIndex(newSets), constraints)
    }
    
    def closure = {
      // AB = AC = D ==> B == C should be added
      // Separates shorter instances if they are equal
      // Finds places where to split.
      // Computes all possibles equalities by reusing other equations.
      val new_equations = ListBuffer[Equation]()
      var transformed = this
      do {
      if (proof) println("Taking the closure of " + transformed)
      new_equations.clear()
      for {set <- transformed.sets
           (a, b) <- pairs(set)} {
        var imax = Math.min(a.length, b.length)
        for (i <- 1 to (imax-1)) {
          val astarti = a.take(i)
          val bstarti = b.take(i)
          if (astarti.vars.sorted == bstarti.vars.sorted && astarti != bstarti) {
             if (!transformed.areEqual(astarti, bstarti).getOrElse(false)) {
               val newEquation = Equation(astarti.withOrigin(a, s"the first $i elements"), bstarti.withOrigin(b, s"the first $i elements"))
               val newEquation2 = Equation(a.drop(i).withOrigin(a, s"the elements after the first $i elements"), b.drop(i).withOrigin(b, s"the elements after the first $i elements"))
               val reason = s"Because the first $i elements of ${Equation(a, b)} are the same, it follows that \n" + newEquation + "\n"  + newEquation2
               if (proof) println(reason)
               new_equations += newEquation//.withReason(reason)
               new_equations += newEquation2//.withReason(reason)
             }
          }
          val aendi = a.drop(a.length - i) 
          val bendi = b.drop(b.length - i)
          if (aendi.vars.sorted == bendi.vars.sorted && aendi != bendi) {
             if (!transformed.areEqual(aendi, bendi).getOrElse(false)) {
               val newEquation = Equation(aendi.withOrigin(a, s"the last $i elements"), bendi.withOrigin(b, s"the last $i elements"))//.withReason(reason)
               val newEquation2 = Equation(a.take(a.length - i).withOrigin(a, s"the elements before the last $i elements"), b.take(b.length - i).withOrigin(b, s"The elements before the last $i elements"))//.withReason(reason)
               
               val reason = s"Because the last $i elements of ${Equation(a, b)} are the same, it follows that \n" + newEquation + "\n"  + newEquation2
               if (proof) println(reason)
               new_equations += newEquation
               new_equations += newEquation2
             }
          }
        }
      }
      for {set <- transformed.sets
           a <- set} {
        val n = a.length
        //println(s"$a, $n")
        for { i <- 0 until n
              j <- 1 until (n-i) } {
          val suba = a.drop(i).take(j)
          assert(suba.length == j, s"Wrong length, n=$n, i=$i, expected j=$j got ${suba.length} ($a, $suba)")
          val opti = transformed.reverseIndex(suba)
          opti match {
            case None =>
            case Some(k) =>
              val replacements = transformed.sets(k)
              assert(replacements contains suba, s"$replacements does not contain $suba")
              for {rep <- replacements
                   alternative = a.take(i) ++ rep ++ a.drop(i+j)
                   if alternative.length <= a.length
                   if !transformed.areEqual(alternative, a).getOrElse(false)
              } {
                //assert(alternative.length == a.length, s"From $a, wrong alternative length, i=$i, j=$j expected n=$n, got ${alternative.length} ($a, $rep, $alternative) among $replacements")
                val reason = s"Because ${Equation(suba, rep)}, it follows that \n"+Equation(a, alternative)
                if (proof) println(reason)
                new_equations += Equation(a, alternative.withOrigin(a, s"because ${Equation(suba, rep)}"))//.withReason(reason)
              }
          }
          
        }
      }
      if (new_equations.nonEmpty) {
        if(proof) println("Added equations " + new_equations.mkString("\n"))
        transformed = transformed ++ Problem(new_equations.toList)
      }
      } while (new_equations.nonEmpty)
      transformed
    }
    
    def replace(a: Var, replacement: ConcatVar): Congruences = {
      val newSets = sets.map(set =>
        set.map(cv => ConcatVar(cv.vars.flatMap(v => if(v == a) replacement.vars else List(v))))
      )
      val newReverseIndex = Congruences.computeReverseIndex(newSets)
      val newConstraints = constraints.map(BoolExprOps.replace(a, replacement))
      (new Congruences(newSets, newReverseIndex, newConstraints) + Equation(ConcatVar(List(a)), replacement)).closure
    }
    
    def addConstraint(constraint: BoolExpr): Congruences = {
      new Congruences(sets, reverseIndex, constraints :+ constraint)
    }
    
    def suppose(constraint: BoolExpr): Congruences = {
      constraint match {
        case LessOrEqualThan(Length(ConcatVar(List(a))), Length(ConcatVar(List(b)))) => 
          // We look for equalities of the for  ...+a == ...+b so that we can introduce a new variable by saying b = fresh + a
          val whereaends = (0 until sets.length).collect{ case i if sets(i).exists(c => c.last == a) => i
          }
          val wherebends = (0 until sets.length).collect{ case i if sets(i).exists(c => c.last == b) => i
          }
          val intersect = whereaends.toSet intersect wherebends.toSet
          if (intersect.nonEmpty) {
            val v = Var.fresh
            replace(b, ConcatVar(v, a))
          } else {
            val whereastarts = (0 until sets.length).collect{ case i if sets(i).exists(c => c.head == a) => i
            }
            val wherebstarts = (0 until sets.length).collect{ case i if sets(i).exists(c => c.head == b) => i
            }
            val intersect = whereastarts.toSet intersect wherebstarts.toSet
            if (intersect.nonEmpty) {
              val v = Var.fresh
              replace(b, ConcatVar(a, v))
            } else {
              addConstraint(constraint)
            }
          }
      }
    }
  }
  
  object LessOrEqualThan{
    def unapply(i: BoolExpr): Option[(IntExpr, IntExpr)] = {
      i match {
        case LessEqThan(a, b) => Some((a, b))
        case LessThan(a, b) => Some((a, b))
        case _ => None
      }
    
    }
  }
  
  object Length {
    def apply(v: Var): Length = Length(ConcatVar(List(v)))
  }
  
  abstract class IntExpr {
    def <=(other: IntExpr): BoolExpr = LessEqThan(this, other)
    def >=(other: IntExpr): BoolExpr = LessEqThan(other, this)
    def <(other: IntExpr): BoolExpr = LessThan(this, other)
    def >(other: IntExpr): BoolExpr = LessThan(other, this)
    def ===(other: IntExpr): BoolExpr = Equals(this, other)
  }
  case class Length(a: ConcatVar) extends IntExpr
  
  abstract class BoolExpr
  case class LessEqThan(a: IntExpr, b: IntExpr) extends BoolExpr
  case class LessThan(a: IntExpr, b: IntExpr) extends BoolExpr
  case class Equals(a: IntExpr, b: IntExpr) extends BoolExpr
  
  object IntExprOps {
    def replace(a: Var, replacement: ConcatVar)(in: IntExpr): IntExpr = in match {
      case Length(u) => Length(ConcatVar(u.vars.flatMap(v => if(v == a) replacement.vars else List(v))))
    }
  }
  
  
  object BoolExprOps {
    def replace(a: Var, replacement: ConcatVar)(in: BoolExpr): BoolExpr = in match {
      case LessEqThan(u, v) => LessEqThan(
        IntExprOps.replace(a, replacement)(u),
        IntExprOps.replace(a, replacement)(v))
      case Equals(u, v) => Equals(
        IntExprOps.replace(a, replacement)(u),
        IntExprOps.replace(a, replacement)(v))
    }
  }
  
  /*Need to prove that mdB == Bdm */
  
  


}