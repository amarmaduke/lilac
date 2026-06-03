
import Lilac.Vec.Basic

namespace Lilac

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

end Lilac
