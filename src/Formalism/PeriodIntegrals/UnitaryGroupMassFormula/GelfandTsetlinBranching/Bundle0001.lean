module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Mathlib
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionD
section
noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem natW_anti_D {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

theorem extremal_mem_D (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (natW_anti_D mu)

theorem extremal_ne_D (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl mu.natW

def sqLinD (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := sqAct ℂ N lam g
  map_add' x y := by simp only [sqAct, map_add (f := _), smul_add]
  map_smul' c x := by
    simp only [sqAct, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem sqLinD_apply (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqLinD N lam g f = sqAct ℂ N lam g f := rfl

theorem isEqv_zero_D {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N) :
    IsEqv h mu lam 0 := by
  refine ⟨fun s _ => by
    simp only [LinearMap.zero_apply]
    exact Submodule.zero_mem _, fun g s _ => ?_⟩
  simp only [LinearMap.zero_apply]
  rw [← sqLinD_apply, map_zero]

theorem isEqv_smul_D {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) (c : ℂ) :
    IsEqv h mu lam (c • φ) := by
  refine ⟨fun s hs => ?_, fun g s hs => ?_⟩
  · rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ c (hφ.1 s hs)
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ.2 g s hs, ← sqLinD_apply, ← sqLinD_apply, map_smul]

theorem eq_on_of_extremal_D (hI : PI.HwIrred) (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N)
    {mu : DomWeight n} {lam : DomWeight N}
    {φ ψ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ}
    (hφ : IsEqv h mu lam φ) (hψ : IsEqv h mu lam ψ)
    (hext : φ (extremal ℂ n mu) = ψ (extremal ℂ n mu)) : ∀ s ∈ nablaSq ℂ n mu, φ s = ψ s := by
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := nablaSq ℂ n mu ⊓ LinearMap.ker (φ - ψ)
  have hU : U ≤ nablaSq ℂ n mu := inf_le_left
  have hstab : ∀ (g : GL (Fin n) ℂ), ∀ f ∈ U, sqAct ℂ n mu g f ∈ U := by
    rintro g f ⟨hf1, hf2⟩
    refine ⟨(he n mu).2.2 g f hf1, ?_⟩
    have hf2' : φ f = ψ f := by
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf2
      exact hf2
    show sqAct ℂ n mu g f ∈ LinearMap.ker (φ - ψ)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hφ.2 g f hf1, hψ.2 g f hf1, hf2']
  rcases (hI n mu).2.1 U hU hstab with hbot | htop
  · exfalso
    have he_mem : extremal ℂ n mu ∈ U :=
      ⟨extremal_mem_D n mu, by
        show extremal ℂ n mu ∈ LinearMap.ker (φ - ψ)
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hext, sub_self]⟩
    rw [hbot] at he_mem
    exact extremal_ne_D n mu ((Submodule.mem_bot ℂ).mp he_mem)
  · intro s hs
    have hsU : s ∈ U := by rw [htop]; exact hs
    have h2 : s ∈ LinearMap.ker (φ - ψ) := hsU.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    exact h2

theorem fixed_of_eqv_D (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) :
    IsFixedW h lam mu (φ (extremal ℂ n mu)) := by
  have hmem := extremal_mem_D n mu
  refine ⟨fun g hg1 hg2 => ?_, fun t => ?_⟩
  · rw [← hφ.2 g _ hmem, (he n mu).1 g hg1 hg2]
  · rw [← hφ.2 _ _ hmem, (he n mu).2.1 t, map_smul]

theorem equivariant_map_interlacing_unique (hI : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) {n N : ℕ} (h : n + 1 = N)
    (lam : DomWeight N) (mu : DomWeight n)
    (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (hφ : IsEqv h mu lam φ) (hφ' : IsEqv h mu lam φ') (hne : ∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) :
    Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s := by
  have hmem := extremal_mem_D n mu
  have hne' : φ' (extremal ℂ n mu) ≠ 0 := by
    intro h0
    obtain ⟨s, hs, hs0⟩ := hne
    apply hs0
    have h3 := eq_on_of_extremal_D hI he h hφ' (isEqv_zero_D h mu lam) (by rw [h0, LinearMap.zero_apply]) s hs
    rw [h3, LinearMap.zero_apply]
  obtain ⟨⟨c, hc⟩, hint⟩ := ha n N h lam mu (φ (extremal ℂ n mu)) (φ' (extremal ℂ n mu)) (hφ.1 _ hmem)
    (hφ'.1 _ hmem) (fixed_of_eqv_D he h hφ) (fixed_of_eqv_D he h hφ') hne'
  refine ⟨hint, c, fun s hs => ?_⟩
  have h3 := eq_on_of_extremal_D hI he h hφ (isEqv_smul_D h hφ' c) (by rw [LinearMap.smul_apply, hc]) s hs
  rw [h3, LinearMap.smul_apply]

def brSupD {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ⨆ (mu : DomWeight n) (_ : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (_ : IsEqv h mu lam φ), (nablaSq ℂ n mu).map φ

theorem branching_rule_decomposition (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl) (hc : HighestVec) (hd : Realize)
    {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : nablaSq ℂ N lam = brSupD h lam := by
  have hmemS : ∀ (mu : DomWeight n) (hint : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ),
      (nablaSq ℂ n mu).map φ ≤ brSupD h lam :=
    fun mu hint φ hφ => le_iSup_of_le mu (le_iSup_of_le hint (le_iSup_of_le φ (le_iSup_of_le hφ le_rfl)))
  have hle : brSupD h lam ≤ nablaSq ℂ N lam := by
    refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hφ.1 s hs
  have hstab : IsStable h lam (brSupD h lam) := by
    intro g
    have key : brSupD h lam ≤ (brSupD h lam).comap (sqLinD N lam (embGL ℂ n N h g)) := by
      refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨s, hs, rfl⟩
      rw [Submodule.mem_comap, sqLinD_apply, ← hφ.2 g s hs]
      exact hmemS mu hint φ hφ ⟨_, (he n mu).2.2 g s hs, rfl⟩
    intro f hf
    exact key hf
  obtain ⟨W', hW'le, hW'st, hsup, hinf⟩ := hb n N h lam (brSupD h lam) hle hstab
  by_cases hW' : W' = ⊥
  · rw [hW', sup_bot_eq] at hsup
    exact hsup.symm
  · exfalso
    obtain ⟨f, hfW, hf0, mu, hfix⟩ := hc n N h lam W' hW'le hW'st hW'
    obtain ⟨φ, hφ, hφe⟩ := hd n N h lam mu f (hW'le hfW) hfix hf0
    have hint : Interlace h lam mu := (ha n N h lam mu f f (hW'le hfW) (hW'le hfW) hfix hfix hf0).2
    have hfS : f ∈ brSupD h lam := hmemS mu hint φ hφ ⟨_, extremal_mem_D n mu, hφe⟩
    have hfI : f ∈ brSupD h lam ⊓ W' := ⟨hfS, hfW⟩
    rw [hinf] at hfI
    exact hf0 ((Submodule.mem_bot ℂ).mp hfI)

theorem gTBranch_of_steps (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) (hd : Realize) : PI.GTBranch := by
  intro n N hnN lam
  refine ⟨fun mu φ φ' hψ hne => ?_, branching_rule_decomposition he ha hb hc hd hnN lam⟩
  have hφ : IsEqv hnN mu lam φ := hψ φ (by simp)
  have hφ' : IsEqv hnN mu lam φ' := hψ φ' (by simp)
  exact equivariant_map_interlacing_unique h he ha hnN lam mu φ φ' hφ hφ' hne

end PI.WGB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.StepACleared
section
noncomputable section

namespace PI.WGB

open Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

def RInvA (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) : Prop :=
  ∀ (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a b : Fin (n + 1)) (t : ℂ), a < b → b.val < n →
    φ (lhwline_rowOp a b t x) = φ x

theorem mrow_invA (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hφ : RInvA φ) (p : Fin (n + 1))
    (t : Fin (n + 1) → ℂ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (S : Finset (Fin (n + 1)))
    (hS : ∀ b ∈ S, p < b ∧ b.val < n) :
    φ (lhwline_mrow p S t x) = φ x := by
  induction S using Finset.induction_on with
  | empty =>
    congr 1
  | insert b S hb ih =>
    have hpS : p ∉ S := fun h => lt_irrefl p (hS p (Finset.mem_insert_of_mem h)).1
    have hpb := hS b (Finset.mem_insert_self b S)
    have heq : lhwline_mrow p (insert b S) t x = lhwline_rowOp p b (t b) (lhwline_mrow p S t x) := by
      funext v
      simp only [lhwline_mrow, lhwline_rowOp, Finset.mem_insert]
      by_cases hv : v.1 = b
      · simp [hv, hb, hpS]
      · simp [hv]
    rw [heq, hφ _ p b _ hpb.1 hpb.2, ih fun b' hb' => hS b' (Finset.mem_insert_of_mem hb')]

def stepA (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  let y := lhwline_mrow p (Finset.univ.filter fun b => p < b ∧ b.val < n) (fun b => -(x (b, q) / x (p, q))) x
  lhwline_mcol q (Finset.univ.filter fun j => q < j) (fun j => -(y (p, j) / y (p, q))) y

theorem stepA_inv (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hR : RInvA φ) (hC : lhwline_CInv φ)
    (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : φ (stepA p q x) = φ x := by
  unfold stepA
  simp only
  rw [lhwline_mcol_inv φ hC _ _ _ _ (fun j hj => (Finset.mem_filter.mp hj).2),
    mrow_invA φ hR _ _ _ _ (fun b hb => (Finset.mem_filter.mp hb).2)]

def elimA : ℕ → (Fin (n + 1) × Fin (n + 1) → ℂ) → (Fin (n + 1) × Fin (n + 1) → ℂ)
  | 0, x => x
  | k + 1, x =>
    if h : k < n then stepA ⟨k, by omega⟩ ⟨k, by omega⟩ (elimA k x) else elimA k x

theorem elimA_inv (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hR : RInvA φ) (hC : lhwline_CInv φ)
    (k : ℕ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : φ (elimA k x) = φ x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [elimA]
    split_ifs
    · rw [stepA_inv φ hR hC, ih]
    · exact ih

def clearedA (k : ℕ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Prop :=
  ∀ (a j : Fin (n + 1)), a.val < n → a.val ≠ j.val → (a.val < k ∨ j.val < k) → x (a, j) = 0

theorem stepA_apply (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a j : Fin (n + 1)) :
    stepA p q x (a, j) =
      (if p < a ∧ a.val < n then x (a, j) + -(x (a, q) / x (p, q)) * x (p, j) else x (a, j)) +
      (if q < j then -(x (p, j) / x (p, q)) *
        (if p < a ∧ a.val < n then x (a, q) + -(x (a, q) / x (p, q)) * x (p, q) else x (a, q)) else 0) := by
  simp only [stepA, lhwline_mcol, lhwline_mrow, Finset.mem_filter, Finset.mem_univ, true_and,
    lt_irrefl, false_and, if_false]
  split_ifs <;> ring

theorem stepA_cleared (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hp : y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0) :
    clearedA (k + 1) (stepA ⟨k, by omega⟩ ⟨k, by omega⟩ y) := by
  intro a j ha hne hlt
  rw [stepA_apply]
  simp only [Fin.lt_def]
  rcases lt_trichotomy j.val k with hj | hj | hj
  · have h1 : y (⟨k, by omega⟩, j) = 0 := hy _ _ (by show k < n; omega) (by show k ≠ j.val; omega) (Or.inr hj)
    have h2 : y (a, j) = 0 := hy _ _ ha hne (Or.inr hj)
    rw [if_neg (show ¬ k < j.val by omega)]
    split_ifs <;> simp [h1, h2]
  · have hjq : j = ⟨k, by omega⟩ := Fin.ext hj
    rw [hjq]
    simp only [Fin.val_mk, lt_irrefl, if_false, add_zero]
    split_ifs with ha'
    · rw [neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]
    · rw [← hjq]
      exact hy _ _ ha hne (Or.inl (by omega))
  · have ha2 : a.val ≤ k := by omega
    have hka : ¬ (k < a.val ∧ a.val < n) := by omega
    simp only [if_neg hka, if_pos hj]
    rcases lt_or_eq_of_le ha2 with ha2 | ha2
    · have h1 : y (a, j) = 0 := hy _ _ ha hne (Or.inl ha2)
      have h2 : y (a, ⟨k, by omega⟩) = 0 := hy _ _ ha (by show a.val ≠ k; omega) (Or.inl ha2)
      simp [h1, h2]
    · have hap : a = ⟨k, by omega⟩ := Fin.ext ha2
      rw [hap, neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]

theorem pivotA_ne (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hd : eval y (lpMinor ℂ (k + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0 := by
  unfold lpMinor at hd
  rw [RingHom.map_det] at hd
  have hM : (eval y).mapMatrix (Matrix.of fun p q : Fin (k + 1) =>
      (X (Fin.castLE (show k + 1 ≤ n + 1 by omega) p, Fin.castLE (show k + 1 ≤ n + 1 by omega) q) :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) =
      Matrix.diagonal (fun p => y (Fin.castLE (show k + 1 ≤ n + 1 by omega) p,
        Fin.castLE (show k + 1 ≤ n + 1 by omega) p)) := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X,
      Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · have hpq : p.val ≠ q.val := fun e => h (Fin.ext e)
      have := p.isLt
      have := q.isLt
      apply hy
      · simp only [Fin.val_castLE]; omega
      · simpa using hpq
      · simp only [Fin.val_castLE]; omega
  rw [hM, Matrix.det_diagonal] at hd
  have := Finset.prod_ne_zero_iff.mp hd (Fin.last k) (Finset.mem_univ _)
  convert this using 3 <;> ext <;> simp

theorem minorA_RInv (s : ℕ) (hr : s ≤ n + 1) :
    RInvA (fun x : Fin (n + 1) × Fin (n + 1) → ℂ => eval x (lpMinor ℂ s hr hr)) :=
  fun x a b t hab _ => lhwline_minor_RInv s hr hr x a b t hab

theorem elimA_cleared (x : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    ∀ k, k ≤ n → clearedA k (elimA k x) := by
  intro k
  induction k with
  | zero =>
    intro _ a j _ _ h
    omega
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hc := ih (by omega)
    simp only [elimA, dif_pos hkn]
    apply stepA_cleared k hkn _ hc
    apply pivotA_ne k hkn _ hc
    have hk1 : k + 1 ≤ n + 1 := by omega
    rw [elimA_inv (fun y => eval y (lpMinor ℂ (k + 1) hk1 hk1 :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ))
      (minorA_RInv _ _) (lhwline_minor_CInv _ _ _)]
    exact hx k hkn

theorem vanishA (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hR : RInvA (fun x => eval x g)) (hC : lhwline_CInv (fun x => eval x g))
    (hD : ∀ D : Fin (n + 1) × Fin (n + 1) → ℂ,
      (∀ a j : Fin (n + 1), a.val < n → a ≠ j → D (a, j) = 0) → eval D g = 0) :
    g = 0 := by
  set P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ := ∏ s : Fin n,
    lpMinor ℂ (s.val + 1) (by have := s.isLt; omega) (by have := s.isLt; omega) with hPdef
  have hP : P ≠ 0 := by
    intro h
    have := congrArg (eval (idPoint ℂ (n + 1) (n + 1))) h
    simp only [hPdef, map_prod, eval_idPoint_lpMinor, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hgP : g * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0
    · have h1 : eval x g = eval (elimA n x) g :=
        (elimA_inv (fun y => eval y g) hR hC n x).symm
      rw [h1, hD _ (fun a j ha h => elimA_cleared x hx n le_rfl a j ha
        (fun e => h (Fin.ext e)) (Or.inl ha)), zero_mul]
    · push Not at hx
      obtain ⟨s, hs, hs0⟩ := hx
      have : eval x P = 0 := by
        rw [hPdef, map_prod]
        exact Finset.prod_eq_zero (i := ⟨s, by omega⟩) (Finset.mem_univ _) hs0
      rw [this, mul_zero]
  rcases mul_eq_zero.mp hgP with h | h
  · exact h
  · exact absurd h hP

end PI.WGB
end
end

