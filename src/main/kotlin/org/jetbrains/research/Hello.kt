package org.jetbrains.research

import org.jetbrains.research.LoopTracker.name
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Jar
import org.jetbrains.research.kfg.KfgConfig
import org.jetbrains.research.kfg.KfgConfigParser
import org.jetbrains.research.kfg.analysis.Loop
import org.jetbrains.research.kfg.analysis.LoopAnalysis
import org.jetbrains.research.kfg.analysis.LoopManager
import org.jetbrains.research.kfg.analysis.LoopSimplifier
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.*
import org.jetbrains.research.kfg.ir.value.instruction.*
import org.jetbrains.research.kfg.util.Flags
import org.jetbrains.research.kfg.visitor.MethodVisitor
import org.jetbrains.research.kfg.visitor.executePipeline
import ru.spbstu.*
import ru.spbstu.wheels.*

//sealed class Evolution {
//    object Unknown: Evolution()
//    object NotSupported: Evolution()
//    object NotCalculated: Evolution()
//}
//enum class Op { SUM, PRODUCT }
//data class Opaque(val symbolic: Symbolic): Evolution()
//data class ChRec(val lhv: Evolution, val rhv: Evolution, val op: Op, val loop: Loop): Evolution()
//data class Peeled(val lhv: Evolution, val rhv: Evolution, val loop: Loop): Evolution()

fun walkLoops(method: Method) = sequence<Loop> {
    val topLevel = LoopManager.getMethodLoopInfo(method)
    for (loop in topLevel) yieldAll(walkLoops(loop))
}

fun walkLoops(top: Loop): Sequence<Loop> = sequence {
    for (loop in top.subLoops) {
        yieldAll(walkLoops(loop))
    }
    yield(top)
}

object Undefined : Apply("\\undefined") {
    override fun toString(): String = "\\undefined"

    override fun copy(arguments: List<Symbolic>): Symbolic {
        require(arguments.isEmpty())
        return this
    }
}

class KFGBinary(val opcode: BinaryOpcode, lhv: Symbolic, rhv: Symbolic) :
    Apply("\\operator${opcode.name}", lhv, rhv) {

    override fun copy(arguments: List<Symbolic>): Symbolic {
        require(arguments.size == 2)
        return KFGBinary(opcode, arguments[0], arguments[1])
    }

    override fun toString(): String = "${this.function}(${this.arguments.joinToString(", ")})"
}

enum class EvoOpcode(val rep: String) {
    PLUS("+"), TIMES("*");

    override fun toString(): String = rep
}

class Evolution(val loop: Loop, val opcode: EvoOpcode, val lhv: Symbolic, val rhv: Symbolic) :
    Apply("\\evolution", lhv, rhv) {
    override fun copy(arguments: List<Symbolic>): Symbolic {
        require(arguments.size == 2)
        return Evolution(loop, opcode, arguments[0], arguments[1])
    }

    private fun argsToString(sb: StringBuilder) {
        sb.append(lhv)
        sb.append(", ")
        sb.append(opcode)
        sb.append(", ")
        if (rhv is Evolution && rhv.loop == loop) rhv.argsToString(sb)
        else sb.append(rhv)
    }

    override fun toString(): String {
        val sb = StringBuilder()
        sb.append("{")
        argsToString(sb)
        sb.append("}[${loop.name}]")
        return "$sb"
    }

}

fun evaluateEvolutions(s: Symbolic, iterations: Map<Loop, Var>): Symbolic = s.transform { sym ->
    when (sym) {
        is Evolution -> {
            val lhv = transform(sym.lhv)
            val rhv = transform(sym.rhv)
            val variable = iterations.getValue(sym.loop)
            when (sym.opcode) {
                EvoOpcode.PLUS -> lhv + RowSum.of(variable, Const(1), variable, rhv) - rhv
                EvoOpcode.TIMES -> TODO() // Needs RowProduct.of
            }
        }
        else -> transform(sym)
    }
}

fun Symbolic.hasVar(v: Var): Boolean = when (this) {
    is Const -> false
    is Var -> v == this
    is Apply -> arguments.any { it.hasVar(v) }
    is Product -> parts.any { it.key.hasVar(v) }
    is Sum -> parts.any { it.key.hasVar(v) }
}

inline fun Sum.partition(predicate: (Symbolic) -> Boolean): Pair<Symbolic, Symbolic> {
    val (c1, c2) = this.parts.partitionTo(mutableMapOf(), mutableMapOf()) { k, _ -> predicate(k) }
    return Sum(parts = c1).simplify() to Sum(parts = c2, constant = this.constant).simplify()
}

class TransformScope(val body: TransformScope.(Symbolic) -> Symbolic) {
    fun transform(s: Symbolic): Symbolic =
        when (s) {
            is Const, is Var -> s
            is Apply -> s.copy(arguments = s.arguments.map { body(it) })
            is Product -> Product.of(Const(s.constant), *s.parts.mapToArray { (s, c) -> body(s) pow c })
            is Sum -> Sum.of(Const(s.constant), *s.parts.mapToArray { (s, c) -> body(s) * c })
        }
}

fun Symbolic.transform(body: TransformScope.(Symbolic) -> Symbolic): Symbolic {
    return TransformScope(body).body(this)
}

object LoopTracker { // XXX: remove this)
    private val loops: MutableMap<Loop, Int> = mutableMapOf()
    private var currentIndex = 0

    val Loop.name
        get() = "%loop.${loops.getOrPut(this) { ++currentIndex }}"
}

class Evolutions(override val cm: ClassManager) : MethodVisitor {
    val inst2loop = mutableMapOf<Instruction, Loop>()
    val loopPhis = mutableMapOf<PhiInst, Loop>()
    val inst2var = mutableMapOf<Value, Var>()
    val var2inst = mutableMapOf<Var, Value>()

    val PhiInst.isLoopPhi: Boolean get() = this in loopPhis
    val PhiInst.loop get() = loopPhis.getValue(this)
    val PhiInst.loopValue get() = this.incomings.getValue(this.loop.latch)
    val PhiInst.baseValue get() = this.incomings.getValue(this.loop.preheader)

    fun Loop.phis() = header.takeWhile { it is PhiInst }.filterIsInstance<PhiInst>()

    private operator fun Loop.contains(inst: Instruction) = inst.parent in this

    val equations = mutableMapOf<Value, Symbolic?>()

    fun transform(v: Value): Symbolic = when (v) {
        in equations -> equations[v]!!
        is IntConstant -> Const(v.value)
        is LongConstant -> Const(v.value)
        is ShortConstant -> Const(v.value.toInt())
        is ByteConstant -> Const(v.value.toInt())
        is UnaryInst -> when (v.opcode) {
            UnaryOpcode.NEG -> -transform(v)
            UnaryOpcode.LENGTH -> Apply("\\length", transform(v))
        }
        is BinaryInst -> when (v.opcode) {
            is BinaryOpcode.Add -> transform(v.lhv) + transform(v.rhv)
            is BinaryOpcode.Sub -> transform(v.lhv) - transform(v.rhv)
            is BinaryOpcode.Mul -> transform(v.lhv) * transform(v.rhv)
            else -> KFGBinary(v.opcode, transform(v.lhv), transform(v.rhv))
        }
        else -> {
            if (v.isNameDefined) {
                val res = Var(v.name.toString())
                var2inst[res] = v
                inst2var[v] = res
                res
            } else Undefined
        }
    }.also { equations[v] = it }

    val phiEquations: MutableMap<PhiInst, Symbolic> = mutableMapOf()
    fun buildPhiEquation(v: PhiInst): Symbolic {
        if (v in phiEquations) return phiEquations[v]!!
        phiEquations[v] = Undefined
        phiEquations[v] = buildPhiEquationUncached(v)
        return phiEquations[v]!!
    }

    private fun buildPhiEquationUncached(v: PhiInst): Symbolic {
        val base = transform(v.baseValue)
        var recur = transform(v.loopValue)

        val deps = recur.vars()
        for (dep in deps) {
            val dvar = var2inst[dep]!!
            if (dvar != v && dvar is PhiInst && dvar in loopPhis && dvar.loop == v.loop) {
                recur = recur.subst(dep to buildPhiEquation(dvar))
            }
        }
        val me = transform(v) as Var

        when (recur) {
            is Const, is Var -> return recur
            is KFGBinary -> {
                val (lhv, rhv) = recur.arguments
                if (lhv != me) return Undefined

                when (recur.opcode) {
                    is BinaryOpcode.Div -> return KFGBinary(
                        BinaryOpcode.Div(),
                        base,
                        Evolution(v.loop, EvoOpcode.TIMES, Const.ONE, rhv)
                    )
                    is BinaryOpcode.Shl, is BinaryOpcode.Shr, is BinaryOpcode.Ushr ->
                        return KFGBinary(
                            recur.opcode,
                            base,
                            Evolution(v.loop, EvoOpcode.PLUS, Const.ZERO, rhv)
                        )
                }
            }
            is Apply -> return recur
            is Product -> {
                // decompose recur to (Alpha * me)
                val alpha = recur / me
                if (alpha.hasVar(me)) return Undefined

                return Evolution(v.loop, EvoOpcode.TIMES, base, alpha)
            }
            is Sum -> {
                // decompose recur to (Alpha * me + Beta)
                val (l, beta) = recur.partition { it.hasVar(me) }
                val alpha = l / me
                if (alpha.hasVar(me)) return Undefined
                when {
                    alpha == Const.ONE -> return Evolution(v.loop, EvoOpcode.PLUS, base, beta)
                    beta == Const.ZERO -> return Evolution(v.loop, EvoOpcode.TIMES, base, alpha)
                    // TODO: this is incorrect
                    // correct formula is in the lines of {{base, +, beta, *, (alpha ^ -1)}, *, alpha}
                    else -> return Evolution(
                        v.loop, EvoOpcode.PLUS,
                        Evolution(v.loop, EvoOpcode.TIMES, base, alpha),
                        Evolution(v.loop, EvoOpcode.TIMES, beta, alpha)
                    )
                }
            }
        }

        return Undefined
    }

    override fun visit(method: Method) {
        walkLoops(method).forEach { loop ->
            loop
                .header
                .takeWhile { it is PhiInst }
                .filterIsInstance<PhiInst>()
                .forEach {
                    loopPhis[it] = loop
                }
            loop.body.forEach {
                it.forEach {
                    inst2loop.getOrPut(it) { loop }
                }
            }
        }

        for (b in method) for (i in b) {
            val t = transform(i)
            if (t != Undefined) {
                println(i.print() + " -> " + t)
            }
        }

        val freshVars = loopPhis.values.toSet().map { it to Var.fresh("iteration") }.toMap()

        for ((phi) in loopPhis) {
            val eq = buildPhiEquation(phi)
            val evo = evaluateEvolutions(eq, freshVars)
            println(phi.print())
            println(eq)
            println(evo)
            (1..10).forEach { iter ->
                print("[$iter]")
                println(evo.subst(freshVars.values.first() to Const(iter)))
            }
        }
    }

    override fun cleanup() {}

}

fun main(args: Array<String>) {
    val cfg = KfgConfigParser(args)

    val jar = Jar(cfg.getStringValue("jar"), cfg.getStringValue("package", "*"))

    val classManager = ClassManager(KfgConfig(Flags.readAll, true))
    classManager.initialize(jar)
    executePipeline(classManager, jar.`package`) {
        //+MethodDisplayer(classManager)
        +LoopAnalysis(classManager)
        +LoopSimplifier(classManager)
        +Evolutions(classManager)
    }

}

