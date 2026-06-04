
import Lilac.Vec.Basic

namespace Lilac

/-!
  # Vec Lemmas
  TODO: Header
-/

/-! ## Fun.Vec.to -/

@[simp]
theorem Fun.Vec.to_nil {α} : to (nil : Vec α 0) = .nil := by rfl

@[simp]
theorem Fun.Vec.to_cons {α n hd} {tl : Vec α n} : to (cons hd tl) = .cons hd tl.to := by rfl

@[simp]
theorem Fun.Vec.to_iso {α n} {v : Fun.Vec α n} : v.to.to = v := sorry

/-! ## to -/

theorem Vec.to_iso {α n} {v : Vec α n} : v.to.to = v := sorry

/-! ## list -/

@[simp]
theorem Vec.list_tail {α n} [NeZero n] {v : Vec α n} : v.tail.list = v.list.tail := sorry

@[simp]
theorem Vec.list_set {α n i x} {v : Vec α n} : (v.set i x).list = v.list.set i x := sorry

@[simp]
theorem Vec.list_concat {α n x} {v : Vec α n} : (v.concat x).list = v.list.concat x := sorry

@[simp]
theorem Vec.list_append {α n m} {v1 : Vec α n} (v2 : Vec α m) : (v1 ++ v2).list = v1.list ++ v2.list := sorry

@[simp]
theorem Vec.list_flatten {α n m} {v : Vec (Vec α n) m} : v.flatten.list = (list <$> v.list).flatten := sorry

@[simp]
theorem Vec.list_map {α β n} {f : α -> β} {v : Vec α n} : (v.map f).list = v.list.map f := sorry

@[simp]
theorem Vec.list_replicate {α n} {x : Nat} {v : Vec α n} : (replicate n x).list = List.replicate n x := sorry

@[simp]
theorem Vec.list_reverse {α n} {v : Vec α n} : v.reverse.list = v.list.reverse := sorry

@[simp]
theorem Vec.list_take {α n h} {v : Vec α n} : (v.take n h).list = v.list.take n := sorry

@[simp]
theorem Vec.list_drop {α : Type u} {m}
  : {n : Nat} -> {v : Vec α m} -> {h : n ≤ m} -> (v.drop n h).list = v.list.drop n
| _, #(), h => by cases h; simp [Vec.drop]
| 0, x::xs, h => by simp [Vec.drop]
| n + 1, x::xs, h => sorry

@[simp]
theorem Vec.list_zipWith {α β γ n} {f : α -> β -> γ} {v1 : Vec α n} {v2 : Vec β n}
  : (zipWith f v1 v2).list = List.zipWith f v1.list v2.list
:= sorry

@[simp]
theorem Vec.list_zip {α β n} {v1 : Vec α n} {v2 : Vec β n} : (zip v1 v2).list = List.zip v1.list v2.list := sorry

@[simp]
theorem Vec.list_range {n k} : (range n k).list = List.range' 0 n k := sorry

@[simp]
theorem Vec.list_zipIdx {α n k} {v : Vec α n} : (v.zipIdx k).list = v.list.zipIdx k := sorry

@[grind .]
theorem Vec.list_of_at_least_one_nonempty {α n} {v : Vec α (n + 1)} : v.list ≠ [] := sorry

/-!
## length

Vec carries its own length, hence why length is marked reducible.
This also means that most operations on length are trivial and the simplifier will reject them.
-/

theorem Vec.length_to {α n} {v : Fun.Vec α n} : v.to.length = n := rfl

@[simp]
theorem Vec.length_tail {α n} [NeZero n] {v : Vec α n} : v.tail.length = n - 1 := rfl

theorem Vec.length_set {α n i x} {v : Vec α n} : (v.set i x).length = n := rfl

@[simp]
theorem Vec.length_concat {α n x} {v : Vec α n} : (v.concat x).length = n + 1 := rfl

@[simp]
theorem Vec.length_append {α n m} {v1 : Vec α n} {v2 : Vec α m} : (v1 ++ v2).length = n + m := sorry

@[simp]
theorem Vec.length_flatten {α n m} {v : Vec (Vec α n) m} : v.flatten.length = n * m := rfl

theorem Vec.length_map {α β n} {f : α -> β} {v : Vec α n} : (v.map f).length = n := rfl

theorem Vec.length_reverse {α n} {v : Vec α n} : v.reverse.length = n := rfl

theorem Vec.length_take {α m n h} {v : Vec α m} : (v.take n h).length = n := rfl

@[simp]
theorem Vec.length_drop {α m n h} {v : Vec α m} : (v.drop n h).length = m - n := rfl

theorem Vec.length_zipWith {α β γ n} {f : α -> β -> γ} {v1 : Vec α n} {v2 : Vec β n} : (zipWith f v1 v2).length = n := rfl

theorem Vec.length_zip {α β n} {v1 : Vec α n} {v2 : Vec β n} : (zip v1 v2).length = n := rfl

theorem Vec.length_range {n k} : (range n k).length = n := rfl

theorem Vec.length_zipIdx {α n k} {v : Vec α n} : (v.zipIdx k).length = n := rfl

/-! ## head -/

@[grind =]
theorem Vec.head_zeroth_index_agree {α n} [NeZero n] {v : Vec α n} : v.head = v[Fin.ofNat n 0] := sorry

@[simp]
theorem Vec.head_set_zero {α n x} [NeZero n] {v : Vec α n} : (v.set 0 x).head = x := sorry

@[simp]
theorem Vec.head_set_succ {α n i x} [NeZero n] {v : Vec α n} : (v.set (i + 1) x).head = v.head := sorry

@[simp]
theorem Vec.head_concat {α n x} [NeZero n] {v : Vec α n} : (v.concat x).head = v.head := sorry

@[simp]
theorem Vec.head_append {n α m} [NeZero n] {v1 : Vec α n} (v2 : Vec α m) : (v1 ++ v2).head = v1.head := sorry

@[simp]
theorem Vec.head_flatten {α n m} [NeZero n] [NeZero m] {v : Vec (Vec α n) m} : v.flatten.head = v.head.head := sorry

@[simp]
theorem Vec.head_map {α β n} {f : α -> β} [NeZero n] {v : Vec α n} : (v.map f).head = f v.head := sorry

@[simp]
theorem Vec.head_replicate {α n} {x : α} [NeZero n] {v : Vec α n} : (replicate n x).head = x := sorry

@[simp]
theorem Vec.head_zipWith {α β γ n} {f : α -> β -> γ} [NeZero n] {v1 : Vec α n} {v2 : Vec β n} : (zipWith f v1 v2).head = f v1.head v2.head := sorry

@[simp]
theorem Vec.head_zip {α β n} [NeZero n] {v1 : Vec α n} {v2 : Vec β n} : (zip v1 v2).head = (v1.head, v2.head) := sorry

@[simp]
theorem Vec.head_range {n k} [NeZero n] : (range n k).head = k := sorry

@[simp]
theorem Vec.head_zipIdx {α n k} [NeZero n] {v : Vec α n} : (v.zipIdx k).head = (v.head, k) := sorry

/-! ## tail -/

-- TODO

/-! ## get -/

@[simp]
theorem Vec.get_cons_zero {α n x} {xs : Vec α n} : (x::xs)[(0 : Fin (n + 1))] = x := sorry

@[simp]
theorem Vec.get_cons_succ {α n x} {xs : Vec α n} {i : Fin n} : (x::xs)[Fin.succ i] = xs[i] := sorry

@[grind =]
theorem Vec.get_set_neq {α n i j x} {v : Vec α n} (h : i ≠ j) : (v.set i x)[j] = v[j] := sorry

@[simp]
theorem Vec.get_set_eq {α n i x} {v : Vec α n} : (v.set i x)[i] = x := sorry

@[grind =]
theorem Vec.get_concat {α n x} {v : Vec α n} {i : Fin (n + 1)} (h : i ≠ 0) : (v.concat x)[i] = v[Fin.pred i h] := sorry

@[grind =]
theorem Vec.get_append_lt {α n m} {v1 : Vec α n} {v2 : Vec α m} {i : Fin (n + m)} (h : i < n) : (v1 ++ v2)[i] = v1[i.castLT h] := sorry

theorem Vec.get_append_ge {α n m} {v1 : Vec α n} {v2 : Vec α m} {i : Fin (n + m)} (h : i ≥ n)
  : (v1 ++ v2)[i] = v2[Fin.subNat n (i.cast (by grind) : Fin (m + n)) h]
:= sorry

@[simp]
theorem Vec.get_map {α β n} {f : α -> β} {v : Vec α n} {i : Fin n} : (v.map f)[i] = f v[i] := sorry

@[simp]
theorem Vec.get_replicate {α n} {x : α} {i : Fin n} : (replicate n x)[i] = x := sorry

@[simp]
theorem Vec.get_reverse {α n} {v : Vec α n} {i : Fin n} : v.reverse[i] = v[i.rev] := sorry

@[simp]
theorem Vec.get_zipWith {α β γ n} {f : α -> β -> γ} {v1 : Vec α n} {v2 : Vec β n} {i : Fin n} : (zipWith f v1 v2)[i] = f v1[i] v2[i] := sorry

@[simp]
theorem Vec.get_zip {α β n} {v1 : Vec α n} {v2 : Vec β n} {i : Fin n} : (zip v1 v2)[i] = (v1[i], v2[i]) := sorry

@[simp]
theorem Vec.get_range {n k} {i : Fin n} : (range n k)[i] = i + k := sorry

@[simp]
theorem Vec.get_zipIdx {α n k} {v : Vec α n} {i : Fin n} : (v.zipIdx k)[i] = (v[i], i + k) := sorry

/-! ## set -/

-- TODO

/-! ## foldl -/

-- TODO

/-! ## foldr -/

-- TODO

/-! ## concat -/

-- TODO

/-! ## append -/

-- TODO

/-! ## flatten -/

-- TODO

/-! ## map -/

-- TODO

/-! ## beq -/

-- TODO

/-! ## replicate -/

-- TODO

/-! ## reverse -/

-- TODO

/-! ## contains -/

-- TODO

/-! ## take -/

-- TODO

/-! ## drop -/

-- TODO

/-! ## any -/

-- TODO

/-! ## all -/

-- TODO

/-! ## zipWith -/

-- TODO

/-! ## zip -/

-- TODO

/-! ## unzip -/

-- TODO

/-! ## range -/

-- TODO

/-! ## zipIdx -/

-- TODO

/-! ## Mem -/

-- TODO

end Lilac
