import «FbipDemos»

namespace StringlyIndexed

/- variables are strings / pointers / ... / some representation that does not need renaming upon rewriting. -/
abbrev Var := String

inductive Arg where
| var (var : Var) : Arg
| const (c : Int) : Arg

/-- LLVM Instruction. -/
inductive Inst where
| const (val : Int) : Inst
| add (v w : Arg) : Inst
| mul (v w : Arg) : Inst

/-- basic block: intrinsically well-typed sequence of variables -/
inductive BB where
| set (var : Var) (e : Inst) (rest : BB) : BB
| ret (v : Var) : BB

/-- An evaluation context to evaluate programs. -/
def EvalContext := Var → Int
def EvalContext.extend (e: EvalContext) (var : Var) (val : Int) : EvalContext :=
  fun needle => if needle == var then val else e needle

def Var.eval (ctx : EvalContext) (v : Var) : Int := ctx v
def Arg.eval (ctx : EvalContext) : Arg → Int
| .const v => v
| .var v => v.eval ctx

def Inst.eval (ctx : EvalContext) : Inst → Int
| .const c => c
| .add a b => a.eval ctx + b.eval ctx
| .mul a b => a.eval ctx * b.eval ctx

def BB.eval (ctx : EvalContext) : BB → Int
| .ret v => v.eval ctx
| .set var e rest => rest.eval (ctx.extend var (e.eval ctx))

set_option trace.compiler.ir.result true in
/- This will be FBIPd -/
def replaceAddWithMul : BB → BB
| .ret v => .ret v
| .set var (.mul (.var v) (.const 2)) rest =>
  .set var (.add (.var v) (.var v)) (replaceAddWithMul rest)
| .set var e rest => .set var e (replaceAddWithMul rest)
/-
[result]
def StringlyIndexed.replaceAddWithMul._closed_1 : obj :=
  let x_1 : obj := 0;
  let inst : obj := Int.ofNat x_1;
  ret inst
def StringlyIndexed.replaceAddWithMul (bb : obj) : obj :=
  case bb : obj of
  StringlyIndexed.BB.set →
    let inst : obj := proj[1] bb;
    inc inst;
    case inst : obj of
    StringlyIndexed.Inst.mul →
      let inst_arg0 : obj := proj[0] inst;
      inc inst_arg0;
      case inst_arg0 : obj of
      StringlyIndexed.Arg.var →
        let inst_arg1 : obj := proj[1] inst;
        inc inst_arg1;
        case inst_arg1 : obj of
        StringlyIndexed.Arg.var →
          dec inst_arg1;
          dec inst_arg0;
          case isShared bb of
          Bool.false → /- unshared code, mutate current bb (set bb[b]) -/
            let rest : obj := proj[2] bb;
            let inst' : obj := proj[1] bb;
            dec inst';
            let rest_processed : obj := StringlyIndexed.replaceAddWithMul rest;
            set bb[2] := rest_processed;
            ret bb
          Bool.true →
            let bb_tag : obj := proj[0] bb;
            let inst' : obj := proj[2] bb;
            inc inst';
            inc bb_tag;
            dec bb;
            let new_rest : obj := StringlyIndexed.replaceAddWithMul inst';
            let new_bb : obj := ctor_0[StringlyIndexed.BB.set] bb_tag inst new_rest;
            ret new_bb
        StringlyIndexed.Arg.const →
          let x_13 : u8 := isShared bb;
          case x_13 : u8 of
          Bool.false →
            let x_14 : obj := proj[2] bb;
            let x_15 : obj := proj[1] bb;
            dec x_15;
            let x_16 : obj := proj[0] inst_arg0;
            inc x_16;
            dec inst_arg0;
            let x_17 : u8 := isShared inst_arg1;
            case x_17 : u8 of
            Bool.false →
              let x_18 : obj := proj[0] inst_arg1;
              let x_19 : obj := StringlyIndexed.replaceAddWithMul._closed_1;
              let x_20 : u8 := Int.decLt x_18 x_19;
              dec x_19;
              case x_20 : u8 of
              Bool.false →
                let x_21 : obj := Int.natAbs x_18;
                dec x_18;
                let x_22 : obj := 2;
                let x_23 : u8 := Nat.decEq x_21 x_22;
                dec x_21;
                case x_23 : u8 of
                Bool.false →
                  del inst_arg1;
                  dec x_16;
                  let x_24 : obj := StringlyIndexed.replaceAddWithMul x_14;
                  set bb[2] := x_24;
                  ret x_1
                Bool.true →
                  let x_25 : u8 := isShared inst;
                  case x_25 : u8 of
                  Bool.false →
                    let x_26 : obj := proj[1] inst;
                    dec x_26;
                    let x_27 : obj := proj[0] inst;
                    dec x_27;
                    setTag inst_arg1 := 0;
                    set inst_arg1[0] := x_16;
                    inc inst_arg1;
                    setTag inst := 1;
                    set inst[0] := inst_arg1;
                    let x_28 : obj := StringlyIndexed.replaceAddWithMul x_14;
                    set x_1[2] := x_28;
                    ret x_1
                  Bool.true →
                    dec inst;
                    setTag inst_arg1 := 0;
                    set inst_arg1[0] := x_16;
                    inc inst_arg1;
                    let x_29 : obj := ctor_1[StringlyIndexed.Inst.add] inst_arg1 inst_arg1;
                    let x_30 : obj := StringlyIndexed.replaceAddWithMul x_14;
                    set x_1[2] := x_30;
                    set x_1[1] := x_29;
                    ret x_1
              Bool.true →
                del inst_arg1;
                dec x_18;
                dec x_16;
                let x_31 : obj := StringlyIndexed.replaceAddWithMul x_14;
                set x_1[2] := x_31;
                ret x_1
            Bool.true →
              let x_32 : obj := proj[0] inst_arg1;
              inc x_32;
              dec inst_arg1;
              let x_33 : obj := StringlyIndexed.replaceAddWithMul._closed_1;
              let x_34 : u8 := Int.decLt x_32 x_33;
              dec x_33;
              case x_34 : u8 of
              Bool.false →
                let x_35 : obj := Int.natAbs x_32;
                dec x_32;
                let x_36 : obj := 2;
                let x_37 : u8 := Nat.decEq x_35 x_36;
                dec x_35;
                case x_37 : u8 of
                Bool.false →
                  dec x_16;
                  let x_38 : obj := StringlyIndexed.replaceAddWithMul x_14;
                  set x_1[2] := x_38;
                  ret x_1
                Bool.true →
                  let x_39 : obj := reset[2] inst;
                  let x_40 : obj := ctor_0[StringlyIndexed.Arg.var] x_16;
                  inc x_40;
                  let x_41 : obj := reuse! x_39 in ctor_1[StringlyIndexed.Inst.add] x_40 x_40;
                  let x_42 : obj := StringlyIndexed.replaceAddWithMul x_14;
                  set x_1[2] := x_42;
                  set x_1[1] := x_41;
                  ret x_1
              Bool.true →
                dec x_32;
                dec x_16;
                let x_43 : obj := StringlyIndexed.replaceAddWithMul x_14;
                set x_1[2] := x_43;
                ret x_1
          Bool.true →
            let x_44 : obj := proj[0] x_1;
            let x_45 : obj := proj[2] x_1;
            inc x_45;
            inc x_44;
            dec x_1;
            let x_46 : obj := proj[0] inst_arg0;
            inc x_46;
            dec inst_arg0;
            let x_47 : obj := proj[0] inst_arg1;
            inc x_47;
            let x_48 : obj := reset[1] inst_arg1;
            let x_49 : obj := StringlyIndexed.replaceAddWithMul._closed_1;
            let x_50 : u8 := Int.decLt x_47 x_49;
            dec x_49;
            case x_50 : u8 of
            Bool.false →
              let x_51 : obj := Int.natAbs x_47;
              dec x_47;
              let x_52 : obj := 2;
              let x_53 : u8 := Nat.decEq x_51 x_52;
              dec x_51;
              case x_53 : u8 of
              Bool.false →
                dec x_48;
                dec x_46;
                let x_54 : obj := StringlyIndexed.replaceAddWithMul x_45;
                let x_55 : obj := ctor_0[StringlyIndexed.BB.set] x_44 inst x_54;
                ret x_55
              Bool.true →
                let x_56 : obj := reset[2] inst;
                let x_57 : obj := reuse! x_48 in ctor_0[StringlyIndexed.Arg.var] x_46;
                inc x_57;
                let x_58 : obj := reuse! x_56 in ctor_1[StringlyIndexed.Inst.add] x_57 x_57;
                let x_59 : obj := StringlyIndexed.replaceAddWithMul x_45;
                let x_60 : obj := ctor_0[StringlyIndexed.BB.set] x_44 x_58 x_59;
                ret x_60
            Bool.true →
              dec x_48;
              dec x_47;
              dec x_46;
              let x_61 : obj := StringlyIndexed.replaceAddWithMul x_45;
              let x_62 : obj := ctor_0[StringlyIndexed.BB.set] x_44 inst x_61;
              ret x_62
      StringlyIndexed.Arg.const →
        dec inst_arg0;
        let x_63 : u8 := isShared x_1;
        case x_63 : u8 of
        Bool.false →
          let x_64 : obj := proj[2] x_1;
          let x_65 : obj := proj[1] x_1;
          dec x_65;
          let x_66 : obj := StringlyIndexed.replaceAddWithMul x_64;
          set x_1[2] := x_66;
          ret x_1
        Bool.true →
          let x_67 : obj := proj[0] x_1;
          let x_68 : obj := proj[2] x_1;
          inc x_68;
          inc x_67;
          dec x_1;
          let x_69 : obj := StringlyIndexed.replaceAddWithMul x_68;
          let x_70 : obj := ctor_0[StringlyIndexed.BB.set] x_67 inst x_69;
          ret x_70
    default →
      let x_71 : u8 := isShared x_1;
      case x_71 : u8 of
      Bool.false →
        let x_72 : obj := proj[2] x_1;
        let x_73 : obj := proj[1] x_1;
        dec x_73;
        let x_74 : obj := StringlyIndexed.replaceAddWithMul x_72;
        set x_1[2] := x_74;
        ret x_1
      Bool.true →
        let x_75 : obj := proj[0] x_1;
        let x_76 : obj := proj[2] x_1;
        inc x_76;
        inc x_75;
        dec x_1;
        let x_77 : obj := StringlyIndexed.replaceAddWithMul x_76;
        let x_78 : obj := ctor_0[StringlyIndexed.BB.set] x_75 inst x_77;
        ret x_78
  StringlyIndexed.BB.ret →
    let x_79 : u8 := isShared x_1;
    case x_79 : u8 of
    Bool.false →
      ret x_1
    Bool.true →
      let x_80 : obj := proj[0] x_1;
      inc x_80;
      dec x_1;
      let x_81 : obj := ctor_1[StringlyIndexed.BB.ret] x_80;
      ret x_81
-/
end StringlyIndexed


namespace IntrinsicallyWellTyped

/-- Intrinsically well-typed variables, all of type `Int`.
newest : Var 1

newest : Var 2
older (newest Var 1): Var 2


newest : Var 3
older (newest : Var 2) : Var 3
older (older (newest : Var 1)) : Var 3


Variables are used to index based on de-bruijn indexes.
So the program:

let x = 42 in
let y = 100 in
x - y

=becomes=>

let 42 in
let 100 in
⟨older newest⟩ - ⟨new⟩
-/
inductive Var : Nat → Type where
| newest : Var n
| older : Var n → Var (n.succ)


/-- an Argument to an LLVM instruction. -/
inductive Arg (n : Nat) where
| var (v : Var n) : Arg n
| const (c : Int) : Arg n

/-- LLVM Instruction. -/
inductive Inst (n : Nat) where
| const (val : Int) : Inst n
| add (v w : Arg n) : Inst n
| mul (v w : Arg n) : Inst n

/-- basic block: intrinsically well-typed sequence of variables -/
inductive BB : Nat → Type
| set (e : Inst n) (rest : BB (.succ n)) : BB n
| ret (v : Var n) : BB n

/-- An evaluation context to evaluate programs. -/
def EvalContext (n : Nat) := Var n → Int
def EvalContext.extend (e: EvalContext n) (val : Int) : EvalContext (.succ n) :=
  fun var => match var with
  | .newest => val -- newest variable: return new bound value
  | .older var' => e var' -- older variable: query context.

def Var.eval (ctx : EvalContext n) (v : Var n) : Int := ctx v
def Arg.eval (ctx : EvalContext n) : Arg n → Int
| .const v => v
| .var v => v.eval ctx

def Inst.eval (ctx : EvalContext n) : Inst n → Int
| .const c => c
| .add a b => a.eval ctx + b.eval ctx
| .mul a b => a.eval ctx * b.eval ctx

def BB.eval (ctx : EvalContext n) : BB n → Int
| .ret v => v.eval ctx
| .set e rest => rest.eval (ctx.extend (e.eval ctx))

def replaceAddWithMul : BB n → BB n
| .ret v => .ret v
| .set (.mul (.var v) (.const 2)) rest =>
  .set (.add (.var v) (.var v)) (replaceAddWithMul rest)
| .set e rest => .set e (replaceAddWithMul rest)

end IntrinsicallyWellTyped

def main : IO Unit := IO.println s!"Hello, {hello}!"
