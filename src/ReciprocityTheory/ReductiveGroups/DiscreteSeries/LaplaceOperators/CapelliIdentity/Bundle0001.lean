module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.BasicCycleRangeLastCastSucc
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

def permIns {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + 1)) :=
  i.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, τ)

theorem permIns_zero {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) : permIns i τ 0 = i := by
  simp [permIns, Equiv.Perm.mul_apply]

theorem permIns_succ {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) (j : Fin p) :
    permIns i τ j.succ = i.succAbove (τ j) := by
  simp [permIns, Equiv.Perm.mul_apply]

theorem sign_permIns {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permIns i τ) : ℤˣ) : ℤ) = (-1) ^ (i : ℕ) * ((Equiv.Perm.sign τ : ℤˣ) : ℤ) := by
  simp [permIns, Equiv.Perm.sign_mul]

theorem permIns_bijective {p : ℕ} :
    Function.Bijective (fun q : Fin (p + 1) × Equiv.Perm (Fin p) => permIns q.1 q.2) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have h' : permIns i τ = permIns i' τ' := h
    have hi : i = i' := by
      have h0 := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => σ 0) h'
      simpa only [permIns_zero] using h0
    subst hi
    have hτ : τ = τ' := by
      refine Equiv.ext fun j => ?_
      have hj := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => σ j.succ) h'
      simp only [permIns_succ] at hj
      first
      | exact Fin.succAbove_right_injective hj
      | exact Fin.succAbove_right_inj.mp hj
    rw [hτ]
  · simp [Fintype.card_perm, Nat.factorial_succ]

theorem sum_perm_succ {M : Type*} [AddCommMonoid M] {p : ℕ} (F : Equiv.Perm (Fin (p + 1)) → M) :
    ∑ σ, F σ = ∑ i, ∑ τ, F (permIns i τ) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective _ (permIns_bijective (p := p))) F, Fintype.sum_prod_type]
  all_goals rfl

theorem basic_zsmul_sign {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] (i : ℕ) (s : ℤ) (a b : 𝒰) :
    ((-1 : ℤ) ^ i * s) • (a * b) = (-1 : ℂ) ^ i • (a * (s • b)) := by
  have h1 : ((-1 : ℂ) ^ i) = (((-1 : ℤ) ^ i : ℤ) : ℂ) := by simp
  rw [h1, Int.cast_smul_eq_zsmul ℂ, mul_smul_comm, mul_smul]
  all_goals rfl

theorem basic_sign_mul_sign {p : ℕ} (τ σ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign τ : ℤˣ) : ℤ) * ((Equiv.Perm.sign (τ * σ) : ℤˣ) : ℤ) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
  rw [← Units.val_mul, Equiv.Perm.sign_mul, ← mul_assoc, Int.units_mul_self, one_mul]

theorem basic_eq_zero_of_eq_neg {𝒰 : Type*} [AddCommGroup 𝒰] [Module ℂ 𝒰] (c : 𝒰)
    (h : c = ((-1 : ℤˣ) : ℤ) • c) : c = 0 := by
  have h' : c = -c := by
    first
    | (rw [Units.val_neg, Units.val_one, neg_one_smul] at h; exact h)
    | (simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h; exact h)
  have h2 : (2 : ℂ) • c = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h']
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem basic_swap_of_not_inj {α : Type*} {p : ℕ} (R : Fin p → α) (h : ¬ Function.Injective R) :
    ∃ i j : Fin p, i ≠ j ∧ R ∘ Equiv.swap i j = R := by
  have hex : ∃ i j, R i = R j ∧ i ≠ j := by
    by_contra hc
    push_neg at hc
    exact h fun a b hab => hc a b hab
  obtain ⟨i, j, hij, hne⟩ := hex
  refine ⟨i, j, hne, funext fun k => ?_⟩
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, hij]
  · rw [h2, hij]
  · rfl

section Ring

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem cminor_succ_col {p : ℕ} (R C : Fin (p + 1) → Fin n) (x : ℂ) :
    cminor E R C x = ∑ i : Fin (p + 1), ((-1 : ℂ) ^ (i : ℕ)) •
      (capEntry E x (R i) (C 0) * cminor E (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1)) := by
  have e : ∀ t : ℂ, x - (t + 1) = x - 1 - t := fun t => by ring
  unfold cminor
  refine (sum_perm_succ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [sign_permIns, List.ofFn_succ, List.prod_cons, permIns_zero, permIns_succ, Fin.val_zero,
    Fin.val_succ, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one, e, Function.comp_apply,
    basic_zsmul_sign]

theorem cminor_perm_rows {p : ℕ} (R C : Fin p → Fin n) (τ : Equiv.Perm (Fin p)) (x : ℂ) :
    cminor E (R ∘ τ) C x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C x := by
  unfold cminor
  rw [Finset.smul_sum]
  refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulLeft τ) _)
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, smul_smul, basic_sign_mul_sign, Function.comp_apply]

theorem cminor_rows_not_inj {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) (h : ¬ Function.Injective R) :
    cminor E R C x = 0 := by
  obtain ⟨i, j, hij, hR⟩ := basic_swap_of_not_inj R h
  have h1 := cminor_perm_rows E R C (Equiv.swap i j) x
  rw [hR, Equiv.Perm.sign_swap hij] at h1
  exact basic_eq_zero_of_eq_neg _ h1

theorem rminor_succ_row {p : ℕ} (R C : Fin (p + 1) → Fin n) (x : ℂ) :
    rminor E R C x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      (capEntry E (x - (p : ℂ)) (R 0) (C j) * rminor E (R ∘ Fin.succ) (C ∘ j.succAbove) x) := by
  have e1 : x - ((p : ℂ) + 1) + 1 = x - p := by ring
  have e2 : ∀ t : ℂ, x - (p : ℂ) + (t + 1) = x - p + 1 + t := fun t => by ring
  unfold rminor
  refine (sum_perm_succ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [sign_permIns, List.ofFn_succ, List.prod_cons, permIns_zero, permIns_succ, Fin.val_zero,
    Fin.val_succ, Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, e1, e2, Function.comp_apply,
    basic_zsmul_sign]

theorem glRelR_op (hE : GlRelR E) : GlRelR (fun a b => MulOpposite.op (E b a)) := by
  intro a b c d
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op, hE d c b a]
  split_ifs <;> simp_all

end Ring

section Module

theorem basic_prod_intertwine {M R' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R'] [Module ℂ R']
    (l : M →ₗ[ℂ] R') : ∀ {m : ℕ} (f : Fin m → Module.End ℂ M) (g : Fin m → Module.End ℂ R'),
    (∀ j, l ∘ₗ f j = g j ∘ₗ l) → l ∘ₗ (List.ofFn f).prod = (List.ofFn g).prod ∘ₗ l
  | 0, f, g, _ => by simp [Module.End.one_eq_id]
  | m + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      basic_prod_intertwine l _ _ (fun j => h j.succ), ← LinearMap.comp_assoc]

theorem cminor_intertwine {M R' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R'] [Module ℂ R']
    {n k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (D : Fin k → Fin k → Module.End ℂ R')
    (ι : Fin k → Fin n) (hι : Function.Injective ι) (l : M →ₗ[ℂ] R')
    (hl : ∀ i j, l ∘ₗ E (ι i) (ι j) = D i j ∘ₗ l) {p : ℕ} (Rw Cw : Fin p → Fin k) (x : ℂ) :
    l ∘ₗ cminor E (ι ∘ Rw) (ι ∘ Cw) x = cminor D Rw Cw x ∘ₗ l := by
  have hc : ∀ (y : ℂ) (a b : Fin k), l ∘ₗ capEntry E y (ι a) (ι b) = capEntry D y a b ∘ₗ l := by
    intro y a b
    have hv : ∀ v, l (E (ι a) (ι b) v) = D a b (l v) := fun v => LinearMap.congr_fun (hl a b) v
    unfold capEntry
    simp only [hι.eq_iff]
    ext v
    split_ifs <;> simp [hv]
  have key : ∀ σ : Equiv.Perm (Fin p),
      l ∘ₗ (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) ((ι ∘ Rw) (σ j)) ((ι ∘ Cw) j)).prod =
        (List.ofFn fun j : Fin p => capEntry D (x - ((j : ℕ) : ℂ)) (Rw (σ j)) (Cw j)).prod ∘ₗ l := by
    intro σ
    apply basic_prod_intertwine
    intro j
    exact hc _ _ _
  unfold cminor
  ext v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 := LinearMap.congr_fun (key σ) v
  simp only [LinearMap.comp_apply] at h1
  first
  | (rw [LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, h1])
  | simp [h1, map_zsmul]

end Module

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ProdOfFnUpdateEq
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

section SlopeTestRemainingChoices

variable {𝒰 : Type*} [Ring 𝒰]

theorem prod_ofFn_update_eq {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) :
    ∃ A B : 𝒰, ∀ v, (List.ofFn (Function.update f j v)).prod = A * v * B := by
  induction p with
  | zero => exact j.elim0
  | succ p ih =>
    refine Fin.cases ?_ (fun j' => ?_) j
    · refine ⟨1, (List.ofFn fun i : Fin p => f i.succ).prod, fun v => ?_⟩
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    · obtain ⟨A, B, h⟩ := ih (fun i => f i.succ) j'
      refine ⟨f 0 * A, B, fun v => ?_⟩
      have e1 : (fun i : Fin p => Function.update f j'.succ v i.succ) =
          Function.update (fun i => f i.succ) j' v := by
        funext i
        simp only [Function.update_apply, Fin.succ_inj]
      have e2 : Function.update f j'.succ v 0 = f 0 := by
        simp only [Function.update_apply, (Fin.succ_ne_zero j').symm, if_false]
      rw [List.ofFn_succ, List.prod_cons, e1, e2, h]
      simp only [mul_assoc]

theorem comm_prod_ofFn (y : 𝒰) {p : ℕ} (f : Fin p → 𝒰) :
    y * (List.ofFn f).prod - (List.ofFn f).prod * y =
      ∑ j, (List.ofFn (Function.update f j (y * f j - f j * y))).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h0 : (List.ofFn (Function.update f 0 (y * f 0 - f 0 * y))).prod =
        (y * f 0 - f 0 * y) * (List.ofFn fun i : Fin p => f i.succ).prod := by
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    have hs : ∀ j' : Fin p,
        (List.ofFn (Function.update f j'.succ (y * f j'.succ - f j'.succ * y))).prod =
          f 0 * (List.ofFn (Function.update (fun i : Fin p => f i.succ) j'
            (y * f j'.succ - f j'.succ * y))).prod := by
      intro j'
      have e1 : (fun i : Fin p => Function.update f j'.succ (y * f j'.succ - f j'.succ * y) i.succ) =
          Function.update (fun i => f i.succ) j' (y * f j'.succ - f j'.succ * y) := by
        funext i
        simp only [Function.update_apply, Fin.succ_inj]
      have e2 : Function.update f j'.succ (y * f j'.succ - f j'.succ * y) 0 = f 0 := by
        simp only [Function.update_apply, (Fin.succ_ne_zero j').symm, if_false]
      rw [List.ofFn_succ, List.prod_cons, e1, e2]
    have hih := ih (fun i => f i.succ)
    rw [Fin.sum_univ_succ, h0, Finset.sum_congr rfl (fun j' _ => hs j'), ← Finset.mul_sum, ← hih,
      List.ofFn_succ, List.prod_cons]
    noncomm_ring

end SlopeTestRemainingChoices

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem capEntry_comm (hE : GlRelR E) (a b c d : Fin n) (x : ℂ) :
    E a b * capEntry E x c d - capEntry E x c d * E a b =
      (if b = c then capEntry E x a d else 0) - (if d = a then capEntry E x c b else 0) := by
  have hz : ∀ s : 𝒰, (s = 0 ∨ ∃ z : ℂ, s = algebraMap ℂ 𝒰 z) → E a b * s - s * E a b = 0 := by
    rintro s (rfl | ⟨z, rfl⟩)
    · simp
    · rw [Algebra.commutes, sub_self]
  have key : E a b * capEntry E x c d - capEntry E x c d * E a b =
      (E a b * E c d - E c d * E a b) + (E a b * (if c = d then algebraMap ℂ 𝒰 x else 0) -
        (if c = d then algebraMap ℂ 𝒰 x else 0) * E a b) := by
    unfold capEntry
    noncomm_ring
  have hs : (if c = d then algebraMap ℂ 𝒰 x else 0) = 0 ∨
      ∃ z : ℂ, (if c = d then algebraMap ℂ 𝒰 x else 0) = algebraMap ℂ 𝒰 z := by
    split_ifs
    · exact Or.inr ⟨x, rfl⟩
    · exact Or.inl rfl
  rw [key, hz _ hs, add_zero, hE a b c d]
  unfold capEntry
  split_ifs <;> subst_vars <;> first | rfl | simp_all | abel

private theorem prod_ofFn_update_sub' {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) (u v : 𝒰) :
    (List.ofFn (Function.update f j (u - v))).prod =
      (List.ofFn (Function.update f j u)).prod - (List.ofFn (Function.update f j v)).prod := by
  obtain ⟨A, B, h⟩ := prod_ofFn_update_eq f j
  rw [h, h, h]
  noncomm_ring

private theorem prod_ofFn_update_ite' {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) (P : Prop) [Decidable P]
    (w : 𝒰) :
    (List.ofFn (Function.update f j (if P then w else 0))).prod =
      if P then (List.ofFn (Function.update f j w)).prod else 0 := by
  obtain ⟨A, B, h⟩ := prod_ofFn_update_eq f j
  split_ifs
  · rfl
  · rw [h, mul_zero, zero_mul]

private theorem sum_ite_sum_comm {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop)
    [DecidablePred P] (g : α → β → 𝒰) :
    (∑ t, if P t then ∑ σ, g t σ else 0) = ∑ σ, ∑ t, if P t then g t σ else 0 := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

private theorem sum_comp_perm_eq_sum {p : ℕ} (σ : Equiv.Perm (Fin p)) (g : Fin p → 𝒰) :
    ∑ t, g t = ∑ j, g (σ j) :=
  (Equiv.sum_comp σ g).symm

theorem cminor_comm (hE : GlRelR E) (a b : Fin n) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    E a b * cminor E R C x - cminor E R C x * E a b =
      (∑ t : Fin p, if R t = b then cminor E (Function.update R t a) C x else 0) -
        ∑ t : Fin p, if C t = a then cminor E R (Function.update C t b) x else 0 := by
  unfold cminor
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_smul_comm, smul_mul_assoc,
    ← smul_sub, comm_prod_ofFn, capEntry_comm E hE, prod_ofFn_update_sub', prod_ofFn_update_ite']
  simp only [Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [sum_ite_sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    conv_rhs => rw [sum_comp_perm_eq_sum σ]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : R (σ j) = b
    · rw [if_pos h.symm, if_pos h]
      congr 1
      congr 1
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_apply, hk, σ.injective.ne hk]
    · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
  · rw [sum_ite_sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : C j = a
    · rw [if_pos h, if_pos h]
      congr 1
      congr 1
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_apply, hk]
    · rw [if_neg h, if_neg h, smul_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

