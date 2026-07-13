module

public import Lilac.Vec

@[expose] public section

namespace Lilac

/- # Tuple Design Decisions
  Why not a function, like mathlib? Functions are difficult to work with in an Agda-style proof
  setting, and they don't mesh well with modules---you can't hide the definiton unless you put
  it inside a structure defeating the purpose.

  Why not an inductive type? An inductive type would increase the universe hiearchy by one. This
  isn't the worst thing in the world, but it is undesirable.

  Why use a vector as an index instead of a list? It is not clear how to make Lean solve instance
  constraints of the form `[∀ (i : Fin l.length), Repr l[i]]`, but Lean doesn't seem to struggle
  with `[∀ (i : Fin n), Repr v[i]]`.

  Why a recursive definition? The chosen recursive definition does not bump the universe
  hierachy; it behaves well with existing machinery around Prod; and it enables Agda-style proofs
  by induction on the `Vec` inductive index---though this seem rarely necessary unless you're
  working with genuinely symbolic length tuples.
-/
@[coe, simp]
abbrev Tuple {n : Nat} : Vec (Type u) n -> Type u
| #() => ULift Unit
| #(x) => x
| x::xs => x × (Tuple xs)

@[simp]
theorem Tuple.cons_succ {a : Type u} : {n : Nat} -> {v : Vec (Type u) (n + 1)} -> (Tuple (a::v)) = (a × Tuple v)
| 0, #(_) => rfl
| n + 1, _::_ => rfl

instance : CoeSort (Vec (Type u) n) (Type u) where
  coe := Tuple

def Tuple.nil : Tuple #() := ULift.up Unit.unit

def Tuple.cons {α : Type u} (a : α) : {v : Vec (Type u) n} -> (t : Tuple v) -> Tuple (α::v)
| #(), t => a
| _::_, t => (a, t)

notation "#⟨⟩" => Tuple.nil
infixr:67 (name := Tuple_cons) " :: " => Tuple.cons

-- protected def Tuple.repr {n} {v : Vec (Type u) n} [∀ (i : Fin n), Repr v[i]] (t : Tuple v) (p : Nat) : Std.Format :=
--   "#⟨" ++ go t p ++ "⟩"
-- where
--   go : {n : Nat} -> {v : Vec (Type u) n} -> [∀ (i : Fin n), Repr v[i]] -> Tuple v -> Nat -> Std.Format
--   | 0, #(), _, _, _ => ""
--   | n + 1, .cons x xs, i, t, p =>
--     have i0 := i 0
--     match n, xs, t with
--     | 0, #(), t => @repr _ i0 t
--     | n + 1, .cons y xs, (a, t) =>
--       have i' := λ (k : Fin (n + 1)) => i k.succ
--       @repr _ i0 a ++ "," ++ @go _ _ i' t p

-- instance {n} {v : Vec (Type u) n} [∀ (i : Fin n), Repr v[i]] : Repr (Tuple v) where
--   reprPrec := Tuple.repr

end Lilac

end section
