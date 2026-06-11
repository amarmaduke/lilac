import Lilac.Vec.Basic

namespace Lilac

/-! ## Misc. -/

theorem zero_lt_imp_neZero {n} : [NeZero n] → 0 < n
| h => by simp [Nat.ne_zero_iff_zero_lt.mp, h.out]

theorem succ_castLT {n} {i : Fin (n + 1)} {_ : i ≠ n}
  : i.succ.castLT ((by grind) : i.succ < n + 1) = (i.castLT ((by omega) : i < n)).succ := by grind

theorem succ_castLT' {m n : Nat} {i : Fin (n + m)} {h : i < m}
  : (Fin.succ i).castLT ((by grind) : i.succ < m + 1) = Fin.succ (i.castLT ((by omega) : i < m)) := by grind

-- (x :: x' :: xs)[i'.castSucc.succ.rev] = (x' :: xs)[i'.succ.rev]
theorem castSucc_succ_rev {n : Nat} {i : Fin n} : i.castSucc.succ.rev = i.succ.rev.succ := by grind

/-!
  # Vec Lemmas
  TODO: Header
-/

/-! ## Fun.Vec.to -/

@[simp]
theorem Fun.Vec.to_nil {α} : to (nil : Vec α 0) = .nil := rfl

@[simp]
theorem Vec.to_nil {α} : (Vec.to (#() : Vec α 0)) = (.nil : Fun.Vec α 0) := rfl

@[simp]
theorem Fun.Vec.to_cons {α n hd} {tl : Vec α n} : to (cons hd tl) = .cons hd tl.to := rfl

@[simp]
theorem Fun.Vec.to_iso {α n} {v : Fun.Vec α n} : v.to.to = v := by
  induction v using Fun.Vec.induction
  case nil => rfl
  case cons ih => simp [ih]

/-! ## to -/

@[simp]
theorem Vec.to_iso {α n} : {v : Vec α n} -> v.to.to = v
| #() => rfl
| x::xs => by simp [to_iso]

/-! ## list -/

@[simp]
theorem Vec.list_tail {n α} : [NeZero n] → {v : Vec α n} → v.tail.list = v.list.tail
| nz, #() => False.elim (nz.out rfl)
| _, _::xs => rfl

@[simp]
theorem Vec.list_set {α a} : {n : Nat} → {i : Fin n} → {v : Vec α n} → (v.set i a).list = v.list.set i a
| 0, i, #() => by grind
| n + 1, i, (x::xs) =>
  @Fin.cases
    n
    (fun i ↦ ((x::xs).set i a).list = (x::xs).list.set i a) -- Motive
    (by simp [set])                                         -- 0 case
    (fun i' ↦ by simp [set, list_set])                      -- succ case
    i

@[simp]
theorem Vec.list_concat {α n x} : {v : Vec α n} → (v.concat x).list = v.list.concat x
| #() => rfl
| x::xs => by simp [list_concat]

-- Avoids needing to unfold HAppend.hAppend. Maybe there's a better way.
@[simp]
theorem Vec.nil_append {α n} : {v : Vec α n} → (#() : Vec α 0) ++ v = v := rfl

-- Avoids needing to unfold HAppend.hAppend. Maybe there's a better way.
@[simp]
theorem Vec.cons_append {α n m} {x : α} {xs : Vec α m} {v : Vec α n} : (x :: xs) ++ v = x :: (xs ++ v) := rfl

@[simp]
theorem Vec.append_nil {α n} : (v : Vec α n) → (v ++ (#() : Vec α 0)) = (cast (by simp) v)
| #() => rfl
| x::xs => by simp [append_nil xs] ; grind

-- Changed v2 to be implicit
@[simp]
theorem Vec.list_append {α n m} : {v1 : Vec α n} → {v2 : Vec α m} → (v1 ++ v2).list = v1.list ++ v2.list
| #(), v => rfl
| v, #() => by simp ; grind
| x::xs, v => by simp [list_append]

@[simp]
theorem Vec.list_flatten {α n m} : {v : Vec (Vec α n) m} → v.flatten.list = (list <$> v.list).flatten
| #() => rfl
| x::xs => by
  simp [flatten, list, Functor.map]
  conv => lhs ; apply list_append
  congr
  exact list_flatten

@[simp]
theorem Vec.list_map {α β n} {f : α -> β} : {v : Vec α n} → (v.map f).list = v.list.map f
| #() => rfl
| x::xs => by simp [map, list_map]

@[simp]
theorem Vec.list_replicate {x : Nat} : {n : Nat} → (replicate n x).list = List.replicate n x
| 0 => rfl
| n + 1 => by simp [replicate, List.replicate, list_replicate]

@[simp]
theorem Vec.list_reverse {α n} : {v : Vec α n} → v.reverse.list = v.list.reverse
| #() => rfl
| x::xs => by simp [reverse, list_reverse]

@[simp]
theorem Vec.list_take {α} : {n k : Nat} → {h : k ≤ n} → {v : Vec α n} → (v.take k h).list = v.list.take k
| 0, k, h, #() => by grind [take, list]
| n + 1, 0, h, x::xs => rfl
| n + 1, k + 1, h, x::xs => by simp [take, list_take]

@[simp]
theorem Vec.list_drop {α : Type u} : {m n : Nat} -> {v : Vec α m} -> {h : n ≤ m} -> (v.drop n h).list = v.list.drop n
| _, _, #(), h => by cases h; simp [drop]
| _, 0, v, _ => by cases v <;> simp [drop, List.drop]
| m + 1, n + 1, x::xs, h => by
  simp [list, drop, ← @list_drop _ _ n xs (by grind)]
  sorry

@[simp]
theorem Vec.list_zipWith {α β γ n} {f : α -> β -> γ}
  : {v1 : Vec α n} → {v2 : Vec β n} → (zipWith f v1 v2).list = List.zipWith f v1.list v2.list
| #(), #() => rfl
| x::xs, y::ys => by simp [zipWith, list_zipWith]

@[simp]
theorem Vec.list_zip {α β n} : {v1 : Vec α n} → {v2 : Vec β n} → (zip v1 v2).list = List.zip v1.list v2.list
| #(), #() => rfl
| x::xs, y::ys => by simp [zip, ← list_zip]

@[simp]
theorem Vec.list_zipIdx {α n k} : {v : Vec α n} → (v.zipIdx k).list = v.list.zipIdx k
| #() => rfl
| x::xs => by simp [zipIdx, list_zipIdx]

@[simp]
theorem Vec.list_range {k} : (n : Nat) → (range n k).list = List.range' k n 1
| 0 => by simp
| n + 1 => by simp [range, list_range, List.range']

@[grind .]
theorem Vec.list_of_at_least_one_nonempty {α n} : {v : Vec α (n + 1)} → v.list ≠ []
| x::xs => by simp

/-! ## length
Vec carries its own length, hence why length is marked reducible.
This also means that most operations on length are trivial and the simplifier will reject them.
-/

theorem Vec.length_to {α n} {v : Fun.Vec α n} : v.to.length = n := rfl

@[simp]
theorem Vec.length_tail {α n} [NeZero n] {v : Vec α n} : v.tail.length = n - 1 := rfl

theorem Vec.length_set {α n i x} {v : Vec α n} : (v.set i x).length = n := rfl

@[simp]
theorem Vec.length_concat {α n x} {v : Vec α n} : (v.concat x).length = n + 1 := rfl

-- Still want Agda style if this can be done in one grind call?
@[simp]
theorem Vec.length_append {α n m} {v1 : Vec α n} {v2 : Vec α m} : (v1 ++ v2).length = n + m := by grind

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
theorem Vec.get_cons_zero {α n x} {xs : Vec α n} : (x::xs)[(0 : Fin (n + 1))] = x := by simp [getElem, get]

@[simp]
theorem Vec.get_cons_succ {α n x} {xs : Vec α n} {i : Fin n} : (x::xs)[Fin.succ i] = xs[i] := by simp [getElem, get]

@[grind =]
theorem Vec.get_set_neq {α} : {n : Nat} → {i j : Fin n} → (h : i ≠ j) → {a : α} → {v : Vec α n} → (v.set i a)[j] = v[j]
| 0, _, _, _, _, #() => by omega
| n + 1, i, j, h, a, x::xs => by
  cases i using Fin.cases
  case zero => simp [set, getElem, get] ; cases j using Fin.cases <;> grind
  case succ i' =>
    cases j using Fin.cases
    case zero => simp [set, getElem, get]
    case succ j' =>
      simp [set, @get_set_neq _ n i' j' (by grind) a xs]

@[simp]
theorem Vec.get_set_eq {α a} : {n : Nat} → {i : Fin n} → {v : Vec α n} → (v.set i a)[i] = a
| n + 1, i, x::xs => by
  cases i using Fin.cases
  case zero => simp [set, getElem, get]
  case succ i' => simp [set, get_set_eq]


@[grind =]
theorem Vec.get_concat {α a}
  : {n : Nat} → {i : Fin (n + 1)} → (h : i ≠ n) → {v : Vec α n} → (v.concat a)[i] = v[i.castLT ((by grind) : i < n)]
| 0, _, _, #() => by grind
| n + 1, i, h, x::xs => by
  cases i using Fin.cases
  case zero => simp [Fin.castLT]
  case succ i' =>
    simp [@get_concat _ a n i' (by grind) xs]
    rw [succ_castLT]
    simp
    grind

@[grind =]
theorem Vec.get_concat' {α a n} : {i : Fin n} → {v : Vec α n} → (v.concat a)[i.castSucc] = v[i]
| i, #() => by grind
| i , x::xs => by
  simp
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [get_concat']

@[grind =]
theorem Vec.get_append_lt {α}
  : {n m : Nat} → {v1 : Vec α n} → {v2 : Vec α m} → {i : Fin (m + n)} → (h : i < n) → (v1 ++ v2)[i] = v1[i.castLT h]
| 0, _, #(), _, i, h => by grind
| n + 1, m, x::xs, ys, i, h => by
  cases i using Fin.cases
  case zero => simp [get, getElem, Fin.castLT]
  case succ i' => simp [@succ_castLT' n m i' (by grind), @get_append_lt _ _ _ _ _ i' (by grind)]

theorem Vec.get_append_ge {α n m} {v1 : Vec α n} {v2 : Vec α m} {i : Fin (m + n)} (h : i ≥ n)
  : (v1 ++ v2)[i] = v2[Fin.subNat n (i.cast (by grind) : Fin (m + n)) h] := sorry

@[simp]
theorem Vec.get_map {α β} {f : α -> β} : {n : Nat} → {v : Vec α n} → {i : Fin n} → (v.map f)[i] = f v[i]
| n + 1, x::xs, i => by
  cases i using Fin.cases
  case zero => simp [getElem, get]
  case succ i' => simp [@get_map _ _ f n xs i']

@[simp]
theorem Vec.get_replicate {α} {x : α} : {n : Nat} → {i : Fin n} → (replicate n x)[i] = x
| n + 1, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [get_replicate]

@[simp]
theorem Vec.cons_get_last {α n x} : {xs : Vec α (n + 1)} → xs[Fin.last n] = (x::xs)[Fin.last (n + 1)]
| x'::xs => by simp [Fin.last, getElem, get]

@[simp]
theorem Vec.concat_get_last {α} {n : Nat} {a : α} : {xs : Vec α n} → (xs.concat a)[Fin.last n] = a
| #() => rfl
| x::xs => by simp [concat, ← cons_get_last, concat_get_last]

@[simp]
theorem Vec.cons_get_0 {α} {x : α} {n : Nat} {xs : Vec α n} : (x :: xs)[Fin.ofNat (n + 1) 0] = x := rfl

@[simp]
theorem Vec.cons_get_1 {α} {x x' : α} {n : Nat} {xs : Vec α n} : (x :: x' :: xs)[Fin.ofNat (n + 2) 1] = x' := rfl

@[simp]
theorem Vec.cons_get_rev {α} {x : α} : {n : Nat} → {xs : Vec α n} → {i : Fin n} → (x::xs)[i.castSucc.rev] = xs[i.rev]
| _, #(), i => by grind
| n + 1, x'::xs, i => by
  cases i using Fin.cases
  case zero => simp [← @cons_get_last]
  case succ i' => simp [castSucc_succ_rev]

@[simp]
theorem Vec.get_reverse {α} : {n : Nat} → {v : Vec α n} → {i : Fin n} → v.reverse[i] = v[i.rev]
| 1, x::#(), 0 => rfl
| n + 1 + 1, x::xs, i => by
  induction i using Fin.reverseInduction
  case last => simp [reverse]
  case cast i' => simp [get_concat', get_reverse]

@[simp]
theorem Vec.get_zipWith {α β γ n} {f : α -> β -> γ}
  : {v1 : Vec α n} → {v2 : Vec β n} → {i : Fin n} → (zipWith f v1 v2)[i] = f v1[i] v2[i]
| x::xs, y::ys, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [zipWith, get_zipWith]

@[simp]
theorem Vec.get_zip {α β n} : {v1 : Vec α n} → {v2 : Vec β n} → {i : Fin n} → (zip v1 v2)[i] = (v1[i], v2[i])
| x::xs, y::ys, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [zip]

@[simp]
theorem Vec.get_range : {k n : Nat} → {i : Fin n} → (range n k)[i] = i + k
| 0, n + 1, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [range, get_range]
| k + 1, n + 1, i => by
  cases i using Fin.cases
  case zero => simp
  case succ i' => simp [range, get_range] ; omega

@[simp]
theorem Vec.get_zipIdx {α} : {k n : Nat} → {v : Vec α n} → {i : Fin n} → (v.zipIdx k)[i] = (v[i], i + k)
| 0, n + 1, x::xs, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [zipIdx, get_zipIdx]
| k + 1, n + 1, x::xs, i => by
  cases i using Fin.cases
  case zero => simp
  case succ i' => simp [get_zipIdx] ; omega

/-! ## set -/

-- TODO

/-! ## foldl -/

-- TODO

/-! ## foldr -/

-- TODO

/-! ## concat -/

-- TODO

/-! ## append -/

@[simp]
theorem Vec.append_nil_left {α n} {v : Vec α n} : (#() : Vec α 0) ++ v = v := rfl

@[simp]
theorem Vec.append_cons {α n1 n2 x} {v1 : Vec α n1} {v2 : Vec α n2} : (x::v1) ++ v2 = x::(v1 ++ v2) := rfl

@[simp, grind =]
theorem Vec.append_nil_right {α n} : {v : Vec α n} → v ++ (#() : Vec α 0) ≍ v
| #() => by simp
| x::xs => by simp ; grind

@[simp, grind =]
theorem Vec.append_assoc {α n1 n2 n3}
  : {v1 : Vec α n1} → {v2 : Vec α n2} → {v3 : Vec α n3} → (v1 ++ v2) ++ v3 ≍ v1 ++ (v2 ++ v3)
| #(), _, _ => by simp
| _, #(), _ => by simp ; grind
| _, _, #() => by simp ; grind
| x::xs, y::ys, z::zs => by
  simp
  -- Congruence for HEq?
  sorry

/-! ## flatten -/

-- TODO

/-! ## map
Why don't we use `Functor` / `LawfulFunctor`?
Because Lean's type inference is not capable of figuring out the right functor `f` when
using `Functor.map`.
Try it yourself: implement `Functor (Vec · n)` and notice how `(· + 2) <$> #(1, 2)` fails.
Solutions:
1. Try to fix Lean's type inference algorithm, unclear if Lean developers will be receptive
2. Use `Vec.map` directly (not horrible, `v.map f` is good ergonomics)
3. Define our own `IndexedFunctor` type that will resolve the index correctly:
```lean
class IndexedFunctor (I : Type u) (F : Type v -> I -> Type w) where
  imap {α β i} (f : α -> β) : F α i -> F β i

instance : IndexedFunctor Nat Vec where
  imap := Vec.map

#eval IndexedFunctor.imap (· + 2) #(1, 2)
```
**For now we choose 2**
-/

@[simp, grind =]
theorem Vec.map_id {α n} : {v : Vec α n} → v.map id = v
| #() => rfl
| x::xs => by simp [map_id]

@[simp, grind =]
theorem Vec.map_id_lambda {α n} : {v : Vec α n} → v.map (λ x => x) = v
| #() => rfl
| x::xs => by simp [map_id_lambda]

@[simp, grind =]
theorem Vec.map_tail {α β n} {f : α -> β} [NeZero n] {v : Vec α n} : v.tail.map f = (v.map f).tail := sorry

@[simp, grind =]
theorem Vec.map_set {α β n i x} {f : α -> β} {v : Vec α n} : (v.set i x).map f = (v.map f).set i (f x) := sorry

@[simp, grind =]
theorem Vec.map_concat {α β n x} {f : α -> β} {v : Vec α n} : (v.concat x).map f = (v.map f).concat (f x) := sorry

@[simp, grind =]
theorem Vec.map_append {α β n m} {f : α -> β} {v1 : Vec α n} {v2 : Vec α m} : (v1 ++ v2).map f = v1.map f ++ v2.map f := sorry

@[simp, grind =]
theorem Vec.map_flatten {α β n m} {f : α -> β} {v : Vec (Vec α n) m} : v.flatten.map f = (v.map (map f)).flatten := sorry

@[simp, grind =]
theorem Vec.map_map {α β γ n} {f : α -> β} {h : β -> γ} {v : Vec α n} : (v.map f).map h = v.map (h ∘ f) := sorry

@[simp, grind =]
theorem Vec.map_replicate {α β n} {a : α} {f : α -> β} : (replicate n a).map f = replicate n (f a) := sorry

@[simp, grind =]
theorem Vec.map_reverse {α β n} {f : α -> β} {v : Vec α n} : v.reverse.map f = (v.map f).reverse := sorry

@[simp, grind =]
theorem Vec.map_take {α β m n} {f : α -> β} {h} {v : Vec α m} : (v.take n h).map f = (v.map f).take n h := sorry

@[simp, grind =]
theorem Vec.map_drop {α β m n} {f : α -> β} {h} {v : Vec α m} : (v.drop n h).map f = (v.map f).drop n h := sorry

/-! ## beq -/

instance {α n} [BEq α] [ReflBEq α] : ReflBEq (Vec α n) where
  rfl := sorry

instance {α n} [BEq α] [LawfulBEq α] : LawfulBEq (Vec α n) where
  eq_of_beq := sorry

@[grind =]
theorem Vec.beq_head_tail {α n} [BEq α] [NeZero n] {v1 : Vec α n} {v2 : Vec α n} : v1.head == v2.head ∧ v1.tail == v2.tail <-> v1 == v2 := sorry

-- TODO: there is some funext automation thing that should be used here
@[grind <-]
theorem Vec.beq_get {α n} [BEq α] {v1 : Vec α n} {v2 : Vec α n} (h : ∀ (i : Fin n), v1[i] == v2[i]) : v1 == v2 := sorry

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

/-! ## find? -/

-- TODO

/-! ## findIdx? -/

-- TODO

/-! ## erase -/

-- TODO

/-! ## count -/

-- TODO

/-! ## traverse -/

-- TODO

/-! ## sequence -/

-- TODO

/-! ## sum -/

-- TODO

/-! ## Mem -/

-- TODO

end Lilac
