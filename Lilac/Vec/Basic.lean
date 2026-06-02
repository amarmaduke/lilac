
import Lilac.Vec.Encoding

namespace Lilac

inductive Vec (α : Sort u) : Nat -> Sort (imax u 1) where
| nil : Vec α 0
| cons {n} : α -> Vec α n -> Vec α (n + 1)

notation "#𝓋[]" => Vec.nil
infixr:67 (name := vec_cons) " :: " => Vec.cons

-- Syntax adapted from Lean Prelude
----------------------------------------------------------------------------------------------------

syntax (name := «term#𝓋[_,]») "#𝓋[" withoutPosition(term,*,?) "]" : term

open Lean in
macro_rules
  | `(#𝓋[ $elems,* ]) => do
    -- NOTE: we do not have `TSepArray.getElems` yet at this point
    let rec expandListLit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(Vec.cons $(⟨elems.elemsAndSeps.get!Internal i⟩) $result))
    let size := elems.elemsAndSeps.size
    if size < 64 then
      expandListLit size (size % 2 == 0) (← ``(Vec.nil))
    else
      `(%[ $elems,* | Vec.nil ])

@[app_unexpander Vec.nil]
meta def Vec.unexpand_nil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(#𝓋[])

@[app_unexpander Vec.cons]
meta def Vec.unexpand_cons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `([])      => `(#𝓋[$x])
  | `([$xs,*]) => `(#𝓋[$x, $xs,*])
  | `(⋯)       => `(#𝓋[$x, $tail])
  | _          => throw ()
| _ => throw ()

----------------------------------------------------------------------------------------------------

@[coe]
def Fun.Vec.to {α n} (v : Lilac.Fun.Vec α n) : Lilac.Vec α n :=
  @induction α (λ n _ => Lilac.Vec α n) Lilac.Vec.nil (λ hd _ tl => Lilac.Vec.cons hd tl) _ v

@[simp]
theorem Fun.Vec.to_nil {α} : to (nil : Vec α 0) = .nil := by rfl

@[simp]
theorem Fun.Vec.to_cons {α n hd} {tl : Vec α n} : to (cons hd tl) = .cons hd tl.to := by rfl

@[simp]
instance {α n} : Coe (Lilac.Fun.Vec α n) (Lilac.Vec α n) where
  coe := Fun.Vec.to

@[simp]
def Vec.to {α n} : Vec α n -> Fun.Vec α n
| nil => .nil
| cons hd tl => .cons hd tl.to

instance {α} : Inhabited (Vec α 0) where
  default := Vec.nil

@[simp]
def Vec.default {α} [Inhabited α] : {n : Nat} -> Vec α n
| 0 => .nil
| n + 1 => Inhabited.default :: Vec.default (n := n)

instance {α n} [Inhabited α] : Inhabited (Vec α n) where
  default := Vec.default

def Vec.has_dec_eq {α : Type u} {n} [DecidableEq α] : (a b : Vec α n) -> Decidable (Eq a b) := sorry

instance {α : Type u} {n} [DecidableEq α] : DecidableEq (Vec α n) := Vec.has_dec_eq

@[reducible]
def Vec.length {α n} (_ : Vec α n) : Nat := n

def Vec.get {α n} : Vec α n -> Fin n -> α
| cons x xs, i => Fin.cases x xs.get i

def Vec.set {α n} : Vec α n -> Fin n -> α -> Vec α n
| cons x xs, i, a => Fin.cases (cons a xs) (λ i => cons x (xs.set i a)) i

def Vec.foldl {α β n} (f : α -> β -> α) (init : α) : Vec β n -> α
| nil => init
| cons x xs => foldl f (f init x) xs

def Vec.concat {α n} : Vec α n -> α -> Vec α (n + 1)
| nil, a => cons a nil
| cons x xs, a => cons x (concat xs a)

def Vec.append {α n m} : Vec α n -> Vec α m -> Vec α (n + m)
| nil, ys => ys |> cast (by simp)
| cons x xs, ys => cons x (xs.append ys) |> cast (by grind)

def Vec.flatten {α n m} : Vec (Vec α n) m -> Vec α (n * m)
| nil => nil
| cons x xs => x.append xs.flatten |> cast (by grind)

def Vec.map {α β n} (f : α -> β) : Vec α n -> Vec β n
| nil => nil
| cons x xs => cons (f x) (xs.map f)

@[simp]
theorem Vec.length_nil {α} : length (Vec.nil : Vec α 0) = 0 := rfl

@[simp]
theorem Vec.length_singleton {α} {a : α} : length #𝓋[a] = 1 := rfl

@[simp]
theorem Vec.length_cons {α n} {x : α} {xs : Vec α n} : (cons x xs).length = xs.length + 1 := rfl

@[simp]
theorem Vec.length_set {α n} {xs : Vec α n} {i : Fin n} {a : α} : (xs.set i a).length = xs.length :=
  sorry

@[simp, grind =]
theorem Vec.foldl_nil {α β} {f : α -> β -> α} {b} : nil.foldl f b = b := rfl

@[simp, grind =]
theorem Vec.foldl_cons {α β n x} {f : α -> β -> α} {b : α} {xs : Vec β n}
  : (x::xs).foldl f b = xs.foldl f (f b x)
:= rfl

@[simp]
theorem Vec.length_concat {α n} {xs : Vec α n} {x} : (concat xs x).length = xs.length + 1 := sorry

@[grind ->]
theorem Vec.of_concat_eq_concat {α n} {xs ys : Vec α n} {x y} (h : xs.concat x = ys.concat y)
  : xs = ys ∧ x = y
:= sorry

def Vec.beq {α n m} [BEq α] : Vec α n -> Vec α m -> Bool
| nil, nil => true
| cons x xs, cons y ys => x == y && beq xs ys
| _, _ => false

@[simp]
theorem Vec.beq_nil_nil {α} [BEq α] : beq (nil : Vec α 0) (nil : Vec α 0) = true := rfl

@[simp]
theorem Vec.beq_cons_nil {α} [BEq α] {n x} {xs : Vec α n}
  : beq (cons x xs) (nil : Vec α 0) = false := rfl

@[simp]
theorem Vec.beq_nil_cons {α} [BEq α] {n x} {xs : Vec α n}
  : beq (nil : Vec α 0) (cons x xs) = false := rfl

@[simp]
theorem Vec.beq_cons_cons {α} [BEq α] {n m} {x y : α} {xs : Vec α n} {ys : Vec α m}
  : beq (cons x xs) (cons y ys) = (x == y && beq xs ys)
:= rfl

instance {α n} [BEq α] : BEq (Vec α n) := ⟨Vec.beq⟩

instance {α n} [BEq α] [ReflBEq α] : ReflBEq (Vec α n) where
  rfl := sorry

instance {α n} [BEq α] [LawfulBEq α] : LawfulBEq (Vec α n) where
  eq_of_beq := sorry

-- isEqv (skipped)

-- Lex (skipped)



end Lilac
