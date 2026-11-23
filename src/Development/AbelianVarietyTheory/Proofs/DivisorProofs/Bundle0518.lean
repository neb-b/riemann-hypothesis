module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockSwap

variable {p q r s : ℕ}

theorem linePos_swap (l : Ln p q r s) : linePos (l.swap : Ln r s p q) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> rfl

theorem rename_lowB (l : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (lowB l P) = lowB (l.swap : Ln r s p q) (rename Prod.swap P) := by
  unfold lowB
  rw [linePos_swap]
  split_ifs
  · exact (pderiv_rename Prod.swap_injective l P).symm
  · simp

theorem rename_raiB (l : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (raiB l P) = raiB (l.swap : Ln r s p q) (rename Prod.swap P) := by
  unfold raiB
  rw [linePos_swap]
  split_ifs
  · simp
  · simp only [LinearMap.neg_apply, map_neg, neg_inj]
    exact (pderiv_rename Prod.swap_injective l P).symm

theorem rename_omE (l l' : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (omE l l' P) =
      omE (l.swap : Ln r s p q) l'.swap (rename Prod.swap P) := by
  unfold omE
  simp only [LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, rename_raiB, rename_lowB,
    Prod.swap_inj]
  congr 1
  split_ifs <;> simp

theorem rename_omAct (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    rename Prod.swap (omAct p q r s M P) =
      omAct r s p q (M.submatrix Prod.swap Prod.swap) (rename Prod.swap P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    rename_omE]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l' => ?_
  simp

theorem rename_fockAct1 (Z : Mat p q) (P : Pol p q r s) :
    rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct]
  congr 2
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, mul_comm]

theorem rename_fockAct2 (Z : Mat r s) (P : Pol p q r s) :
    rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct]
  congr 2
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, mul_comm]

theorem rename_minusPart {σ τ : Type} (e : σ ≃ τ) (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (h : ∀ P, rename e (A P) = B (rename e P))
    (P : MvPolynomial σ ℂ) : rename e (minusPart A P) = minusPart B (rename e P) := by
  unfold minusPart
  have := (renameEquiv ℂ e).toAddEquiv.map_finsum
    (fun d : ℕ => homogeneousComponent d (A (homogeneousComponent (d + 2) P)))
  refine this.trans (finsum_congr fun d => ?_)
  show rename e _ = _
  rw [rename_homogeneousComponent, h, rename_homogeneousComponent]

theorem minusPart_eq_zero_iff {σ τ : Type} (e : σ ≃ τ) (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (h : ∀ P, rename e (A P) = B (rename e P))
    (P : MvPolynomial σ ℂ) : minusPart A P = 0 ↔ minusPart B (rename e P) = 0 := by
  rw [← rename_minusPart e A B h, map_eq_zero_iff _ (rename_injective _ e.injective)]

theorem swap_symmetry : ∀ (p q r s : ℕ), (∀ (Z : Mat p q) (P : Pol p q r s), rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P)) ∧ (∀ (Z : Mat r s) (P : Pol p q r s), rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P)) ∧ (∀ P : Pol p q r s, (P ∈ harm1 p q r s ↔ rename Prod.swap P ∈ harm2 r s p q) ∧ (P ∈ harm2 p q r s ↔ rename Prod.swap P ∈ harm1 r s p q)) := by
  intro p q r s
  refine ⟨rename_fockAct1, rename_fockAct2, fun P => ⟨?_, ?_⟩⟩
  · exact forall₂_congr fun Z _ =>
      minusPart_eq_zero_iff (Equiv.prodComm _ _) _ _ (rename_fockAct2 Z) P
  · exact forall₂_congr fun Z _ =>
      minusPart_eq_zero_iff (Equiv.prodComm _ _) _ _ (rename_fockAct1 Z) P

end GlobalTheory.FockSwap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockNormBoundsMulXPderiv
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockNormBound

theorem norm_sum_sq_of_orth {κ H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : Finset κ) (v : κ → H) (h : ∀ a b, a ≠ b → inner ℂ (v a) (v b) = 0) :
    ‖∑ a ∈ s, v a‖ ^ 2 = ∑ a ∈ s, ‖v a‖ ^ 2 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [inner_sum, Finset.sum_eq_single a, inner_self_eq_norm_sq]
  · intro b _ hb; exact h a b (Ne.symm hb)
  · intro h'; exact absurd ha h'

def mfact {σ : Type} (α : σ →₀ ℕ) : ℝ := α.prod (fun _ k => (k.factorial : ℝ))

theorem mfact_nonneg {σ : Type} (α : σ →₀ ℕ) : 0 ≤ mfact α :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem mfact_add {σ : Type} [DecidableEq σ] (α : σ →₀ ℕ) (i : σ) :
    mfact (α + Finsupp.single i 1) = ((α i : ℝ) + 1) * mfact α := by
  unfold mfact
  rw [← Finsupp.mul_prod_erase' (α + Finsupp.single i 1) i _ (by simp),
    ← Finsupp.mul_prod_erase' α i _ (by simp)]
  have : Finsupp.erase i (α + Finsupp.single i 1) = Finsupp.erase i α := by
    ext j; by_cases hj : j = i
    · simp [hj]
    · simp [Finsupp.erase_ne hj, Finsupp.single_eq_of_ne hj]
  rw [this]
  simp [Nat.factorial_succ]
  ring

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem norm_mono (h : IsFockIP ι) (α : σ →₀ ℕ) : ‖ι (monomial α 1)‖ ^ 2 = mfact α := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h α α, if_pos rfl]
  have : α.prod (fun _ k => (k.factorial : ℂ)) = ((mfact α : ℝ) : ℂ) := by
    simp [mfact, Finsupp.prod]
  rw [this]; simp

theorem norm_comb (h : IsFockIP ι) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℂ)
    (g : (σ →₀ ℕ) → (σ →₀ ℕ)) (hg : ∀ a b, a ≠ b → c a ≠ 0 → c b ≠ 0 → g a ≠ g b) :
    ‖ι (∑ a ∈ s, monomial (g a) (c a))‖ ^ 2 = ∑ a ∈ s, ‖c a‖ ^ 2 * mfact (g a) := by
  have e : ∀ a, ι (monomial (g a) (c a)) = c a • ι (monomial (g a) 1) := by
    intro a; rw [← map_smul, smul_monomial]; simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, norm_sum_sq_of_orth]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [e, norm_smul, mul_pow, norm_mono h]
  · intro a b hab
    rw [e, e]
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    rw [inner_smul_left, inner_smul_right, h, if_neg (hg a b hab ha hb)]; simp

theorem fock_norm_bounds (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (h : IsFockIP ι) (i : σ) (d : ℕ)
    (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧
      ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  have hd : ∀ a ∈ P.support, (a i : ℝ) ≤ d := by
    intro a ha
    have h1 : a i ≤ P.degreeOf i := monomial_le_degreeOf i ha
    exact_mod_cast h1.trans ((degreeOf_le_totalDegree P i).trans hP)
  have h0 : ‖ι P‖ ^ 2 = ∑ a ∈ P.support, ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := by
    conv_lhs => rw [P.as_sum]
    exact norm_comb h _ _ id (fun a b hab _ _ => hab)
  have h1 : X i * P = ∑ a ∈ P.support, monomial (a + Finsupp.single i 1) (AddMonoidAlgebra.coeff P a) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [X, monomial_mul, add_comm, one_mul]
  have h2 : pderiv i P = ∑ a ∈ P.support, monomial (a - Finsupp.single i 1) (AddMonoidAlgebra.coeff P a * a i) := by
    conv_lhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pderiv_monomial]
  have hsub : ∀ a : σ →₀ ℕ, a i ≠ 0 → a - Finsupp.single i 1 + Finsupp.single i 1 = a := by
    intro a ha
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ha))
  constructor
  · rw [h1, norm_comb h _ _ _ (fun a b hab _ _ hh => hab (add_right_cancel hh)), h0,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [mfact_add]
    have := hd a ha
    have h3 : 0 ≤ ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
    nlinarith
  · rw [h2, norm_comb h, h0, Finset.mul_sum]
    · refine Finset.sum_le_sum fun a ha => ?_
      have h3 : 0 ≤ ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
      by_cases hz : a i = 0
      · simp only [hz, Nat.cast_zero, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, zero_mul]
        exact mul_nonneg (by positivity) h3
      have h4 := mfact_add (a - Finsupp.single i 1) i
      rw [hsub a hz] at h4
      have h5 : (((a - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : ℝ) + 1 = a i := by
        have := congrArg (fun f : σ →₀ ℕ => f i) (hsub a hz)
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
        exact_mod_cast this
      rw [h5] at h4
      rw [norm_mul, Complex.norm_natCast]
      calc (‖AddMonoidAlgebra.coeff P a‖ * a i) ^ 2 * mfact (a - Finsupp.single i 1)
          = a i * (‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a) := by rw [h4]; ring
        _ ≤ d * (‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a) := mul_le_mul_of_nonneg_right (hd a ha) h3
    · intro a b hab ha hb hh
      have ha' : a i ≠ 0 := fun z => ha (by simp [z])
      have hb' : b i ≠ 0 := fun z => hb (by simp [z])
      apply hab
      rw [← hsub a ha', hh, hsub b hb']

end GlobalTheory.FockNormBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockPolGK

theorem X_mul_pderiv_mem {σ : Type} (d : ℕ) (i j : σ) (P : MvPolynomial σ ℂ)
    (hP : P ∈ restrictTotalDegree σ ℂ d) :
    X i * pderiv j P ∈ restrictTotalDegree σ ℂ d := by
  classical
  rw [mem_restrictTotalDegree] at hP
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hd : (α.sum fun _ e => e) ≤ d := (le_totalDegree hα).trans hP
  rw [pderiv_monomial]
  by_cases h : α j = 0
  · simp [h]
  · rw [mem_restrictTotalDegree, X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have hα : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp; omega
      · simp [hk]
    conv_rhs => rw [hα]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
    rfl

theorem omE_mem {p q r s : ℕ} (d : ℕ) (l l' : Ln p q r s) (h : linePos l = linePos l')
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omE l l' P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  unfold omE
  rw [LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · have hl' : linePos l' = false := h ▸ hl
      simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false]
      change -(pderiv l ((X l' : Pol p q r s) * P)) ∈ _
      refine Submodule.neg_mem _ ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Submodule.add_mem _ (X_mul_pderiv_mem d _ _ P hP) ?_
      by_cases e : l' = l
      · subst e; rw [pderiv_X_self, mul_one]; exact hP
      · rw [pderiv_X_of_ne e, mul_zero]; exact Submodule.zero_mem _
    · have hl' : linePos l' = true := h ▸ hl
      simp only [raiB, lowB, hl, hl', if_true]
      exact X_mul_pderiv_mem d _ _ P hP
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

theorem omAct_mem {p q r s : ℕ} (d : ℕ) (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (hZ : ∀ l l', linePos l ≠ linePos l' → Z l l' = 0)
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omAct p q r s Z P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  rw [LinearMap.smul_apply]
  by_cases h : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (omE_mem d l l' h P hP)
  · rw [hZ l l' h, zero_smul]; exact Submodule.zero_mem _

theorem kStable1 (p q r s d : ℕ) :
    KStable (fockAct1 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change Z a b * (1 : Mat r s) c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hZ a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, mul_zero]

theorem kStable2 (p q r s d : ℕ) :
    KStable (fockAct2 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change (1 : Mat p q) a b * Z c e = 0
  by_cases hc : a = b
  · subst hc
    rw [hZ c e, mul_zero]
    rcases a with a | a <;> rcases c with c | c <;> rcases e with e | e <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, zero_mul]

def signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) : ℚ := if linePos (a, c) then 1 else -1

theorem cast_signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) :
    ((signQ a c : ℚ) : ℂ) = lineSign a c := by
  rcases a with a | a <;> rcases c with c | c <;> simp [signQ, linePos, lineSign]

theorem mem_of_monomials {σ : Type} (N : Submodule ℂ (MvPolynomial σ ℂ))
    (h : ∀ α, monomial α (1 : ℂ) ∈ N) (P : MvPolynomial σ ℂ) : P ∈ N := by
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  have := N.smul_mem (AddMonoidAlgebra.coeff P α) (h α)
  rwa [smul_monomial, smul_eq_mul, mul_one] at this

theorem monomial_mem_weightSpace_fockAction_first {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct1 p q r s)
      (fun a => ∑ c, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan1, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

theorem monomial_mem_weightSpace_fockAction_second {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct2 p q r s)
      (fun c => ∑ a, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan2, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

theorem pol_locFin_weights : ∀ (p q r s : ℕ), (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct1 p q r s) W) ∧ P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ) ∧ (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct2 p q r s) W) ∧ P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ) := by
  intro p q r s
  refine ⟨fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable1 _ _ _ _ _⟩, ?_⟩,
    fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable2 _ _ _ _ _⟩, ?_⟩⟩
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_first α)) P
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_second α)) P

end GlobalTheory.FockPolGK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracket
section
open Formalism.BasicNotions.TH

namespace GlobalTheory.FockLie

theorem weyl_comm {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [DecidableEq ι] (a b : ι → A)
    (h : ∀ l m, (b l * a m - a m * b l = if l = m then (1 : A) else 0) ∧
      b l * b m = b m * b l ∧ a l * a m = a m * a l) (i j k l : ι) :
    (a i * b j) * (a k * b l) - (a k * b l) * (a i * b j) =
      (if j = k then a i * b l else 0) - (if l = i then a k * b j else 0) := by
  have h1 : b j * a k = a k * b j + if j = k then (1 : A) else 0 := by
    rw [← (h j k).1]; abel
  have h2 : b l * a i = a i * b l + if l = i then (1 : A) else 0 := by
    rw [← (h l i).1]; abel
  have e1 : (a i * b j) * (a k * b l) = a i * (b j * a k) * b l := by simp only [mul_assoc]
  have e2 : (a k * b l) * (a i * b j) = a k * (b l * a i) * b j := by simp only [mul_assoc]
  have e3 : a i * (a k * b j) * b l = a k * (a i * b l) * b j := by
    calc a i * (a k * b j) * b l = (a i * a k) * (b j * b l) := by simp only [mul_assoc]
      _ = (a k * a i) * (b l * b j) := by rw [(h i k).2.2, (h j l).2.1]
      _ = _ := by simp only [mul_assoc]
  rw [e1, e2, h1, h2, mul_add, mul_add, add_mul, add_mul, e3]
  split_ifs <;> simp

theorem omE_comm {p q r s : ℕ} (i j k l : Ln p q r s) :
    omE i j * omE k l - omE k l * omE i j =
      (if j = k then omE i l else 0) - (if l = i then omE k j else 0) := by
  have h := weyl_comm (raiB : Ln p q r s → _) lowB (GlobalTheory.fock_letters_ccr p q r s) i j k l
  have e : omE i j * omE k l - omE k l * omE i j =
      (raiB i * lowB j) * (raiB k * lowB l) - (raiB k * lowB l) * (raiB i * lowB j) := by
    simp only [omE]
    split_ifs <;>
      simp only [add_zero, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] <;>
      module
  rw [e, h]
  simp only [omE]
  by_cases h1 : j = k <;> by_cases h2 : l = i
  · subst h1; subst h2; simp
  · have h3 : ¬ i = l := fun h => h2 h.symm
    simp [h1, h2, h3]
  · have h3 : ¬ k = j := fun h => h1 h.symm
    simp [h1, h2, h3]
  · simp [h1, h2]

theorem omAct_single {p q r s : ℕ} (i j : Ln p q r s) (x : ℂ) :
    omAct p q r s (Matrix.single i j x) = x • omE i j := by
  rw [omAct_apply]
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_smul]

theorem omAct_single_mul {p q r s : ℕ} (i j k l : Ln p q r s) (x y : ℂ) :
    omAct p q r s (Matrix.single i j x * Matrix.single k l y) =
      (x * y) • (if j = k then omE i l else 0) := by
  by_cases h : j = k
  · subst h
    rw [Matrix.single_mul_single_same, omAct_single, if_pos rfl]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, if_neg h, map_zero, smul_zero]

theorem omAct_lie (p q r s : ℕ) (Y Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s (Y * Z - Z * Y) =
      omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y := by
  induction Y using Matrix.induction_on' with
  | h_zero => simp
  | h_add Y Y' hY hY' =>
    have : (Y + Y') * Z - Z * (Y + Y') = (Y * Z - Z * Y) + (Y' * Z - Z * Y') := by
      rw [add_mul, mul_add]; abel
    rw [this, map_add (f := _), hY, hY', map_add (f := _), add_mul, mul_add]; abel
  | h_std_basis i j x =>
    induction Z using Matrix.induction_on' with
    | h_zero => simp
    | h_add Z Z' hZ hZ' =>
      have : Matrix.single i j x * (Z + Z') - (Z + Z') * Matrix.single i j x =
          (Matrix.single i j x * Z - Z * Matrix.single i j x) +
            (Matrix.single i j x * Z' - Z' * Matrix.single i j x) := by
        rw [add_mul, mul_add]; abel
      rw [this, map_add (f := _), hZ, hZ', map_add (f := _), add_mul, mul_add]; abel
    | h_std_basis k l y =>
      rw [map_sub, omAct_single_mul, omAct_single_mul, omAct_single, omAct_single,
        smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x, ← smul_sub, ← smul_sub, omE_comm]

end GlobalTheory.FockLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]

def ObjMap.comp {R : Type} [CommRing R] {D : Datum p} {b : Base D R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) :
    ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
    by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB m₁.φ₂) (pull_isLB o₃.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.P m₁.φ₂ m₁.φ₂ rfl)
      (chartPullSame o₃.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
      m₂.pol)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

end GlobalTheory.UPel.HT

namespace GlobalTheory.RelTan

end GlobalTheory.RelTan
end
end

