module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PCurry
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace CurryingSwaps

variable {α : Type*} {m k : ℕ}

theorem upd_castAdd (I : Fin m → α) (J : Fin k → α) (i : Fin m) (v : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) v = Fin.append (Function.update I i v) J := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Fin.append_left, Fin.append_left,
        Function.update_of_ne h]
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_right, Fin.append_right]

theorem upd_natAdd (I : Fin m → α) (J : Fin k → α) (j : Fin k) (v : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) v = Fin.append I (Function.update J j v) := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_left, Fin.append_left]
  · by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.natAdd_injective _ _ e)), Fin.append_right, Fin.append_right,
        Function.update_of_ne h]

theorem swap_castAdd (I : Fin m → α) (J : Fin k → α) (i i' : Fin m) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.castAdd k i') = Fin.append (I ∘ Equiv.swap i i') J := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · simp only [Function.comp_apply, Fin.append_left, Equiv.swap_apply_def, Fin.castAdd_inj]
    split_ifs <;> simp
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.natAdd m b ≠ Fin.castAdd k i' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right]

theorem swap_natAdd (I : Fin m → α) (J : Fin k → α) (j j' : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd m j) (Fin.natAdd m j') = Fin.append I (J ∘ Equiv.swap j j') := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h1 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.castAdd k a ≠ Fin.natAdd m j' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left]
  · simp only [Function.comp_apply, Fin.append_right, Equiv.swap_apply_def, Fin.natAdd_inj]
    split_ifs <;> simp

theorem swap_mixed (I : Fin m → α) (J : Fin k → α) (i : Fin m) (j : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.natAdd m j) =
      Fin.append (Function.update I i (J j)) (Function.update J j (I i)) := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h2 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : a = i
    · subst h; simp
    · have h1 : Fin.castAdd k a ≠ Fin.castAdd k i := fun e => h (Fin.castAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left,
        Function.update_of_ne h]
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : b = j
    · subst h; simp
    · have h2 : Fin.natAdd m b ≠ Fin.natAdd m j := fun e => h (Fin.natAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right,
        Function.update_of_ne h]

theorem iteApp {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (p : Prop) [Decidable p]
    (g : V →ₗ[ℂ] W) (x : V) : (if p then g else 0) x = if p then g x else 0 := by
  split_ifs <;> rfl

end CurryingSwaps

open CurryingSwaps in
theorem curry_holds : Curry := by
  intro n M _ _ E m k
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g h
    funext K
    have := congrFun (congrFun (congrArg (fun x => x) h) (fun j => K (Fin.natAdd m j))) (fun i => K (Fin.castAdd k i))
    simpa only [curF_apply, Fin.append_castAdd_natAdd] using this
  · intro g
    refine ⟨fun K => g (fun j => K (Fin.natAdd m j)) (fun i => K (Fin.castAdd k i)), ?_⟩
    funext J I
    simp only [curF_apply, Fin.append_left, Fin.append_right]
  · intro a b
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, tE_apply, Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, upd_castAdd, upd_natAdd, add_assoc]
  · intro i
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ b : Fin k, ¬ (Fin.natAdd m b < Fin.castAdd k i) := fun b h => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at h <;> omega
    have hc : ∀ x : Fin m, Fin.castAdd k x < Fin.castAdd k i ↔ x < i := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, lift_apply, curF_apply, Fin.append_left, upd_castAdd, Finset.sum_filter,
      Fin.sum_univ_add, swap_castAdd, hz, hc, if_false, Finset.sum_const_zero, add_zero]
  · intro j
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ x : Fin m, Fin.castAdd k x < Fin.natAdd m j := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    have hc : ∀ b : Fin k, Fin.natAdd m b < Fin.natAdd m j ↔ b < j := fun b => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, curF_apply, tE_apply, Fin.append_right, upd_natAdd, upd_castAdd,
      Finset.sum_filter, Fin.sum_univ_add, swap_natAdd, swap_mixed, hz, hc, if_true, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x p => if I p = x then
      f (Fin.append (Function.update I p (J j)) (Function.update J j x)) else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, add_assoc]
  · intro B
    rfl
  · intro i i'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, lift_apply, swap_castAdd]
  · intro j j'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, swap_natAdd]

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PJmComm
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace JMA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem comp_swap {P : Type} [DecidableEq P] (I : P → Fin n) (p j : P) (_h : p ≠ j) :
    I ∘ Equiv.swap p j = Function.update (Function.update I p (I j)) j (I p) := by
  funext q
  simp only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_def]
  split_ifs <;> subst_vars <;> simp_all

theorem pm_swap_eq {P : Type} [DecidableEq P] (p j : P) (h : p ≠ j) :
    (pm (Equiv.swap p j) : Module.End ℂ (TV n M P)) = ∑ a, ∑ b, eAt p a b * eAt j b a := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [pm_apply, comp_swap I p j h]
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, eAt_apply,
    Function.update_apply, if_neg (Ne.symm h)]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem xJ_eq {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) :
    xJ E j = ∑ a, ∑ b, tE (Finset.univ.filter (· < j)) E a b * eAt j b a := by
  have hs : ∀ i ∈ Finset.univ.filter (· < j),
      pm (Equiv.swap i j) = ∑ a, ∑ b, (eAt i a b * eAt j b a : Module.End ℂ (TV n M (Fin m))) :=
    fun i hi => pm_swap_eq i j (ne_of_lt (Finset.mem_filter.1 hi).2)
  show Om E j + ∑ i ∈ Finset.univ.filter (· < j), pm (Equiv.swap i j) = _
  rw [Finset.sum_congr rfl hs]
  simp only [tE, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem eAt_eq_sub {P : Type} [DecidableEq P] (S : Finset P) (j : P) (hj : j ∉ S)
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    (eAt j a b : Module.End ℂ (TV n M P)) = tE (insert j S) E a b - tE S E a b := by
  simp only [tE, Finset.sum_insert hj]
  abel

theorem comm_xJ {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) (X : Module.End ℂ (TV n M (Fin m)))
    (h1 : ∀ a b, Commute X (tE (Finset.univ.filter (· < j)) E a b))
    (h2 : ∀ a b, Commute X (tE (insert j (Finset.univ.filter (· < j))) E a b)) : Commute X (xJ E j) := by
  rw [xJ_eq]
  refine Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => (h1 a b).mul_right ?_
  rw [eAt_eq_sub (Finset.univ.filter (· < j)) j (by simp) E]
  exact (h2 b a).sub_right (h1 b a)

theorem swap_pres {P : Type} [DecidableEq P] (S : Finset P) (i j : P) (h : i ∈ S ↔ j ∈ S) (q : P) :
    Equiv.swap i j q ∈ S ↔ q ∈ S := by
  rcases eq_or_ne q i with rfl | hi
  · rw [Equiv.swap_apply_left]
    exact h.symm
  rcases eq_or_ne q j with rfl | hj
  · rw [Equiv.swap_apply_right]
    exact h
  · rw [Equiv.swap_apply_of_ne_of_ne hi hj]

theorem swap_comm_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (k i j : Fin m)
    (h1 : i < k ↔ j < k) (h2 : (i = k ∨ i < k) ↔ (j = k ∨ j < k)) :
    Commute (pm (Equiv.swap i j)) (xJ E k) :=
  comm_xJ E k _ (fun a b => (hT n M (Fin m) E hE _).2.2.1 _ (swap_pres _ i j (by simpa using h1)) a b)
    (fun a b => (hT n M (Fin m) E hE _).2.2.1 _ (swap_pres _ i j (by simpa using h2)) a b)

theorem om_comm_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (h : i < j) : Commute (Om E i) (xJ E j) :=
  comm_xJ E j _ (fun a b => (hT n M (Fin m) E hE _).2.1 i (by simpa using h) a b)
    (fun a b => (hT n M (Fin m) E hE _).2.1 i (by simp [h]) a b)

theorem xJ_comm_lt (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (h : i < j) : Commute (xJ E i) (xJ E j) := by
  show Commute (Om E i + ∑ l ∈ Finset.univ.filter (· < i), pm (Equiv.swap l i)) (xJ E j)
  refine (om_comm_xJ hT hE i j h).add_left (Commute.sum_left _ _ _ fun l hl => ?_)
  have hl' : l < i := (Finset.mem_filter.1 hl).2
  exact swap_comm_xJ hT hE j l i (iff_of_true (hl'.trans h) h)
    (iff_of_true (Or.inr (hl'.trans h)) (Or.inr h))

theorem xJ_comm (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m) :
    Commute (xJ E i) (xJ E j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact xJ_comm_lt hT hE i j h
  · exact Commute.refl _
  · exact (xJ_comm_lt hT hE j i h).symm

theorem pm_swap_sq {P : Type} (i j : P) [DecidableEq P] :
    (pm (Equiv.swap i j) : Module.End ℂ (TV n M P)) * pm (Equiv.swap i j) = 1 := by
  rw [← pm_mul, Equiv.swap_mul_self, pm_one]

theorem xJ_succ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) :
    xJ E j = pm (Equiv.swap i j) * xJ E i * pm (Equiv.swap i j) + pm (Equiv.swap i j) := by
  have hOm : pm (Equiv.swap i j) * Om E i * pm (Equiv.swap i j) = Om E j := by
    rw [(hT n M (Fin m) E hE (∅ : Finset (Fin m))).2.2.2, mul_assoc, pm_swap_sq, mul_one,
      Equiv.swap_apply_left]
  have hsum : ∀ l ∈ Finset.univ.filter (· < i),
      pm (Equiv.swap i j) * pm (Equiv.swap l i) * pm (Equiv.swap i j) =
        (pm (Equiv.swap l j) : Module.End ℂ (TV n M (Fin m))) := by
    intro l hl
    have hl' : (l : ℕ) < i := (Finset.mem_filter.1 hl).2
    rw [← pm_mul, ← pm_mul]
    congr 1
    refine Equiv.ext fun x => ?_
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have hset : Finset.univ.filter (· < j) = insert i (Finset.univ.filter (· < i)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega
  show Om E j + ∑ l ∈ Finset.univ.filter (· < j), pm (Equiv.swap l j) =
    pm (Equiv.swap i j) * (Om E i + ∑ l ∈ Finset.univ.filter (· < i), pm (Equiv.swap l i)) *
      pm (Equiv.swap i j) + pm (Equiv.swap i j)
  rw [hset, Finset.sum_insert (by simp), mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl hsum, hOm]
  abel

theorem xJ_mul_swap (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) : xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 := by
  rw [xJ_succ hT hE i j hij]
  simp only [add_mul, mul_assoc, pm_swap_sq, mul_one]

theorem swap_mul_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) : pm (Equiv.swap i j) * xJ E j = xJ E i * pm (Equiv.swap i j) + 1 := by
  rw [xJ_succ hT hE i j hij]
  simp only [mul_add, ← mul_assoc, pm_swap_sq, one_mul]

theorem list_prod_comm {A : Type} [Monoid A] (x : A) : ∀ (L : List A) (k : ℕ) (hk : k + 1 < L.length),
    (∀ t (ht : t < L.length), t ≠ k → t ≠ k + 1 → Commute L[t] x) → Commute (L[k] * L[k + 1]) x →
      Commute L.prod x := by
  intro L
  induction L with
  | nil =>
    intro k hk
    simp at hk
  | cons a L ih =>
    intro k hk h1 h2
    cases k with
    | zero =>
      cases L with
      | nil => simp at hk
      | cons b L =>
        rw [List.prod_cons, List.prod_cons, ← mul_assoc]
        change Commute (a * b) x at h2
        refine h2.mul_left (Commute.list_prod_left L x fun y hy => ?_)
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
        exact h1 (t + 2) (by simp; omega) (by omega) (by omega)
    | succ k =>
      rw [List.prod_cons]
      exact (h1 0 (by simp) (by omega) (by omega)).mul_left (ih k (by simpa using hk)
        (fun t ht h h' => h1 (t + 1) (by simpa using ht) (by omega) (by omega)) h2)

theorem pair_comm {A : Type} [Ring A] [Algebra ℂ A] (u : ℂ) (a b p : A) (hab : Commute a b)
    (h1 : b * p = p * a + 1) (h2 : p * b = a * p + 1) :
    Commute ((algebraMap ℂ A u + a) * (algebraMap ℂ A u + b)) p := by
  have hU : ∀ z : A, Commute (algebraMap ℂ A u) z := fun z => Algebra.commutes u z
  have hs : Commute (a + b) p := by
    show (a + b) * p = p * (a + b)
    rw [add_mul, mul_add, h1, h2]
    abel
  have hp : Commute (a * b) p := by
    show a * b * p = p * (a * b)
    calc a * b * p = a * (p * a + 1) := by rw [mul_assoc, h1]
      _ = (a * p + 1) * a := by noncomm_ring
      _ = p * b * a := by rw [h2]
      _ = p * (a * b) := by rw [mul_assoc, hab.eq]
  have he : (algebraMap ℂ A u + a) * (algebraMap ℂ A u + b) =
      algebraMap ℂ A u * algebraMap ℂ A u + algebraMap ℂ A u * (a + b) + a * b := by
    rw [add_mul, mul_add, mul_add, ← (hU a).eq, mul_add]
    abel
  rw [he]
  exact (((hU p).mul_left (hU p)).add_left ((hU p).mul_left hs)).add_left hp

theorem piJ_comm_adj (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (u : ℂ)
    (i : Fin m) : Commute (PiJ (m + 1) E u) (pm (Equiv.swap i.castSucc i.succ)) := by
  have hij : ((i.castSucc : Fin (m + 1)) : ℕ) + 1 = i.succ := by simp
  show Commute (List.ofFn fun j : Fin (m + 1) => algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) u + xJ E j).prod _
  apply list_prod_comm _ _ i (by simp)
  · intro t ht h1 h2
    rw [List.getElem_ofFn]
    refine Commute.add_left (Algebra.commutes u _) ?_
    refine (swap_comm_xJ hT hE ⟨t, by simpa using ht⟩ i.castSucc i.succ ?_ ?_).symm
    · simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ]
      omega
    · simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
      omega
  · simp only [List.getElem_ofFn]
    exact pair_comm u _ _ _ (xJ_comm hT hE _ _) (xJ_mul_swap hT hE _ _ hij) (swap_mul_xJ hT hE _ _ hij)

theorem piJ_comm (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) (m : ℕ) (u : ℂ)
    (σ : Equiv.Perm (Fin m)) : Commute (PiJ m E u) (pm σ) := by
  cases m with
  | zero =>
    rw [Subsingleton.elim σ 1, pm_one]
    exact Commute.one_right _
  | succ m =>
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hσ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact piJ_comm_adj hT hE u i
    | one =>
      rw [pm_one]
      exact Commute.one_right _
    | mul x y _ _ hx hy =>
      rw [pm_mul]
      exact hx.mul_right hy

end JMA

theorem jmComm_of : TensorGl → JMComm := by
  intro hT n M _ _ E hE m
  refine ⟨JMA.xJ_comm hT hE, fun i j h => ⟨JMA.xJ_mul_swap hT hE i j h, fun k hk1 hk2 => ?_⟩,
    fun u σ => JMA.piJ_comm hT hE m u σ⟩
  have e1 := Fin.val_ne_of_ne hk1
  have e2 := Fin.val_ne_of_ne hk2
  refine (JMA.swap_comm_xJ hT hE k i j ?_ ?_).symm
  · simp only [Fin.lt_iff_val_lt_val]
    omega
  · simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGKB
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem actT_fin {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (hfin : ∀ y, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y))) (y : TV n M P) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y)) := by
  classical
  haveI hS : ∀ J : P → Fin n, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ (y J))) :=
    fun J => hfin (y J)
  set T : Submodule ℂ M := ⨆ J : P → Fin n, Submodule.span ℂ (Set.range fun γ => ρ γ (y J)) with hT
  haveI : FiniteDimensional ℂ T := by rw [hT]; infer_instance
  let L : ((P → Fin n) → T) →ₗ[ℂ] TV n M P := LinearMap.pi fun I => T.subtype ∘ₗ LinearMap.proj I
  have hle : Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y) ≤ LinearMap.range L := by
    rw [Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    have hmem : ∀ I, actT lab κ ρ γ y I ∈ T := by
      intro I
      simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.proj_apply]
      refine Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ ?_
      exact Submodule.mem_iSup_of_mem J (Submodule.subset_span ⟨γ, rfl⟩)
    exact ⟨fun I => ⟨_, hmem I⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem actT_cont {ι Γ : Type} [TopologicalSpace Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ i j, Continuous fun γ => κ τ γ i j)
    (hc : ∀ y (lam : M →ₗ[ℂ] ℂ), Continuous fun γ => lam (ρ γ y)) (y : TV n M P) (lam : TV n M P →ₗ[ℂ] ℂ) :
    Continuous fun γ => lam (actT lab κ ρ γ y) := by
  classical
  have h1 : ∀ x : TV n M P, lam x = ∑ I : P → Fin n, (lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I) (x I) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have key : (fun γ => lam (actT lab κ ρ γ y)) = fun γ => ∑ I : P → Fin n, ∑ J : P → Fin n,
      (∏ p : P, κ (lab p) γ (I p) (J p)) * (lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I) (ρ γ (y J)) := by
    funext γ
    rw [h1]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
  rw [key]
  refine continuous_finsetSum _ fun I _ => continuous_finsetSum _ fun J _ => ?_
  exact (continuous_finsetProd _ fun p _ => hκ _ _ _).mul (hc (y J) _)

end PositivityTheory.Rg.Cz.TGK

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFinF
section
noncomputable section

namespace PositivityTheory.Rg.Cz

namespace TF

theorem monic_lprod (L : List ℂ) : (L.map fun c => Polynomial.X - Polynomial.C c).prod.Monic := by
  induction L with
  | nil => simp
  | cons c L ih =>
    rw [List.map_cons, List.prod_cons]
    exact (Polynomial.monic_X_sub_C c).mul ih

theorem fin_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [Finite ι] (x : ι → A)
    (hc : ∀ i j, Commute (x i) (x j)) (hL : ∀ i, ∃ L : List ℂ, (L.map fun c => x i - algebraMap ℂ A c).prod = 0) :
    FiniteDimensional ℂ (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range x))) := by
  classical
  have hcomm : (Set.range x).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hc i j
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range x)) := Algebra.isMulCommutative_adjoin ℂ hcomm
  letI : CommRing (Algebra.adjoin ℂ (Set.range x)) := by
    open scoped IsMulCommutative in
      exact inferInstance
  have hint : ∀ i, IsIntegral ℂ (x i) := by
    intro i
    obtain ⟨L, hL⟩ := hL i
    refine ⟨(L.map fun c => Polynomial.X - Polynomial.C c).prod, monic_lprod L, ?_⟩
    rw [← Polynomial.aeval_def, map_list_prod, List.map_map]
    have hf : (⇑(Polynomial.aeval (x i)) ∘ fun c => Polynomial.X - Polynomial.C c) =
        fun c => x i - algebraMap ℂ A c := by
      funext c
      simp [Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hf]
    exact hL
  let y : ι → Algebra.adjoin ℂ (Set.range x) := fun i => ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hyint : ∀ z ∈ Set.range y, IsIntegral ℂ z := by
    rintro _ ⟨i, rfl⟩
    exact (isIntegral_algHom_iff (Algebra.adjoin ℂ (Set.range x)).val Subtype.val_injective).1 (hint i)
  have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral (R := ℂ) (Set.finite_range y) hyint
  have hset : Set.range y = Subtype.val ⁻¹' (Set.range x) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have htop : Algebra.adjoin ℂ (Set.range y) = ⊤ := by
    rw [hset]
    exact Algebra.adjoin_adjoin_coe_preimage
  rw [htop] at hfin
  have hS : Module.Finite ℂ (Algebra.adjoin ℂ (Set.range x)) :=
    Module.Finite.equiv Subalgebra.topEquiv.toLinearEquiv
  exact Subalgebra.finiteDimensional_toSubmodule.2 hS

end TF

end PositivityTheory.Rg.Cz
end
end

