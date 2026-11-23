module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolEqOfDegNeZero
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem trace_eq_of_trace_mul_pow {n m : ℕ} (A S : Matrix (Fin n) (Fin n) ℂ) (B T : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det)
    (h : ∀ i : ℕ, 1 ≤ i → (S * A ^ i).trace = (T * B ^ i).trace) : S.trace = T.trace := by
  set P := A.charpoly * B.charpoly with hP
  have hPA : Polynomial.aeval A P = 0 := by
    rw [hP, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hPB : Polynomial.aeval B P = 0 := by
    rw [hP, map_mul, Matrix.aeval_self_charpoly, mul_zero]
  have eA := congrArg (fun M => (S * M).trace) hPA
  have eB := congrArg (fun M => (T * M).trace) hPB
  simp only [Polynomial.aeval_eq_sum_range, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, mul_zero, Matrix.trace_zero] at eA eB
  rw [Finset.sum_range_succ'] at eA eB
  have hs : ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1) * (S * A ^ (i + 1)).trace =
      ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1) * (T * B ^ (i + 1)).trace :=
    Finset.sum_congr rfl fun i _ => by rw [h (i + 1) (by omega)]
  rw [hs] at eA
  have e0 : P.coeff 0 * (S * A ^ 0).trace = P.coeff 0 * (T * B ^ 0).trace := by linear_combination eA - eB
  simp only [pow_zero, Matrix.mul_one] at e0
  have hc : P.coeff 0 ≠ 0 := by
    rw [hP, Polynomial.mul_coeff_zero]
    refine mul_ne_zero (fun h0 => hA.ne_zero ?_) (fun h0 => hB.ne_zero ?_)
    · rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
    · rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  exact mul_left_cancel₀ hc e0

end GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem charpoly_eq_toMatrix' {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    f.charpoly = (LinearMap.toMatrix' f).charpoly := by
  rw [← LinearMap.charpoly_toMatrix f (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']

theorem trace_eq_of_charpoly_eq {n : ℕ} {M M' : Matrix (Fin n) (Fin n) ℂ} (e : M.charpoly = M'.charpoly) :
    M.trace = M'.trace := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]

theorem charPol_eq_of_deg_ne_zero : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (x y : WD h), (∀ σ : Weil h, deg σ ≠ 0 → x.charPol σ = y.charPol σ) → ∀ σ : Weil h, x.charPol σ = y.charPol σ := by
  intro K Ω _ _ _ _ _ A v h x y hxy σ
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  simp only [WD.charPol_mk] at hxy ⊢
  have hnm : n = m := by
    have e := congrArg Polynomial.natDegree (hxy (frob h) (by rw [deg_frob]; exact one_ne_zero))
    rwa [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at e
  subst hnm
  by_cases hσ : deg σ = 0
  swap
  · exact hxy σ hσ

  have hMA : ∀ τ : Weil h, LinearMap.toMatrix' (a.ρ τ) = (a.toGL τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => (WDRep.coe_toGL a τ).symm
  have hMB : ∀ τ : Weil h, LinearMap.toMatrix' (b.ρ τ) = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => (WDRep.coe_toGL b τ).symm
  have hne : ∀ τ : Weil h, deg τ ≠ 0 →
      (a.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro τ hτ
    refine trace_eq_of_charpoly_eq ?_
    rw [← hMA, ← hMB, ← charpoly_eq_toMatrix', ← charpoly_eq_toMatrix']
    exact hxy τ hτ
  have hall : ∀ τ : Weil h,
      (a.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro τ
    by_cases hτ : deg τ = 0
    swap
    · exact hne τ hτ
    refine trace_eq_of_trace_mul_pow (a.toGL (frob h) : Matrix (Fin n) (Fin n) ℂ) _
      (b.toGL (frob h) : Matrix (Fin n) (Fin n) ℂ) _
      ((Matrix.isUnit_iff_isUnit_det _).1 (a.toGL (frob h)).isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).1 (b.toGL (frob h)).isUnit) fun i hi => ?_
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul,
      ← map_pow, ← map_pow, ← map_mul, ← map_mul]
    refine hne _ ?_
    rw [deg_mul, deg_pow, hτ, deg_frob]
    omega
  rw [charpoly_eq_toMatrix', charpoly_eq_toMatrix', hMA, hMB]
  refine GlobalTheory.QuadKernelConj.charpoly_eq_of_trace_pow _ _ fun j => ?_
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  exact hall _

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldProdEmbeddingsRegroupMaximalRealStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmField_prod_embeddings_regroup_maximalReal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : (E →+* ℂ) → ℤ), (∀ τ, k (ComplexEmbedding.conjugate τ) = k τ) → ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ, ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ = ∏ φ, g φ ^ (2 * n φ) := by
  first | exact @GlobalTheory.cm_prod_regroup_maximalReal | exact GlobalTheory.cm_prod_regroup_maximalReal | (intros; apply GlobalTheory.cm_prod_regroup_maximalReal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIntegralPreimageLeSumTransposeImage
section
open Matrix

namespace GlobalTheory.LatticeDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int_iff (a : L) : a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := Iff.rfl

theorem mulVec_int {m n : ℕ} (A : Matrix (Fin m) (Fin n) L) (u : Fin n → L)
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hu : ∀ i, u i ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ u) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hu j)

theorem one_dim (e z : L)
    (h : ∀ c : L, c ∈ Formalism.UG.intL L → e * c ∈ Formalism.UG.intL L → c * z ∈ Formalism.UG.intL L) :
    ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧ z = a + e * b := by
  by_cases he : e ∈ Formalism.UG.intL L
  · refine ⟨z, 0, ?_, Subring.zero_mem _, by simp⟩
    simpa using h 1 (Subring.one_mem _) (by simpa using he)
  · have he0 : e ≠ 0 := by
      rintro rfl
      exact he (Subring.zero_mem _)
    have hlt : 1 < Valued.v e := not_le.mp ((mem_int_iff e).not.mp he)
    have hinv : e⁻¹ ∈ Formalism.UG.intL L := by
      rw [mem_int_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hlt.le
    refine ⟨0, e⁻¹ * z, Subring.zero_mem _, h _ hinv ?_, ?_⟩
    · rw [mul_inv_cancel₀ he0]; exact Subring.one_mem _
    · field_simp
      simp

theorem diag_case {m n : ℕ} (d : Fin m → L) (z : Fin n → L)
    (h : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) →
      (∀ i, ((Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0)) *ᵥ u) i
        ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) :
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
      z = l + (Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0))ᵀ *ᵥ w := by
  have key : ∀ k : Fin n, ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧
      z k = a + (if hk : (k : ℕ) < m then d ⟨k, hk⟩ else 0) * b := by
    intro k
    apply one_dim
    intro c hc hec
    have := h (Pi.single k c) ?_ ?_
    · simpa [Pi.single_apply] using this
    · intro i
      by_cases hi : i = k
      · subst hi; simpa using hc
      · simp [hi]
    · intro j
      rw [Matrix.mulVec_single]
      by_cases hj : (k : ℕ) = (j : ℕ)
      · have hk : (k : ℕ) < m := hj ▸ j.2
        have : (⟨k, hk⟩ : Fin m) = j := Fin.ext hj
        rw [dite_eq_left hk, this] at hec
        simpa [hj] using hec
      · simp [hj]
  choose a b ha hb hz using key
  refine ⟨a, fun j => if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0, ha, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact hb _
    · exact Subring.zero_mem _
  · funext k
    rw [hz k, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hk : (k : ℕ) < m
    · rw [dite_eq_left hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
      · simp
      · intro j _ hj
        have : (k : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · rw [dite_eq_right hk, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (k : ℕ) ≠ (j : ℕ) := fun e => hk (e ▸ j.2)
      simp [this]

theorem dual_subset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  intro L _ _ m n x z h
  obtain ⟨P, P', Q, Q', d, hP, hP', hQ, hQ', hPP, hQQ, hx⟩ := _root_.GlobalTheory.SmithValued.smith_valued L m n x
  set D : Matrix (Fin m) (Fin n) L :=
    Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) with hD
  have hPP' : P' * P = 1 := mul_eq_one_comm.mp hPP
  have hQQ' : Q' * Q = 1 := mul_eq_one_comm.mp hQQ
  obtain ⟨l, w, hl, hw, hz⟩ := diag_case d (Q'ᵀ *ᵥ z) (by
    intro s hs hDs
    have h1 := h (Q' *ᵥ s) (mulVec_int _ _ hQ' hs) (by
      have : x *ᵥ (Q' *ᵥ s) = P *ᵥ (D *ᵥ s) := by
        rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P * D), hQQ, Matrix.mul_one]
      rw [this]
      exact mulVec_int _ _ hP hDs)
    have h2 : ∑ i, s i * (Q'ᵀ *ᵥ z) i = ∑ i, (Q' *ᵥ s) i * z i := by
      change s ⬝ᵥ (Q'ᵀ *ᵥ z) = (Q' *ᵥ s) ⬝ᵥ z
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h2]
    exact h1)
  refine ⟨Qᵀ *ᵥ l, P'ᵀ *ᵥ w, mulVec_int _ _ (fun i j => hQ j i) hl,
    mulVec_int _ _ (fun i j => hP' j i) hw, ?_⟩
  have h3 : z = Qᵀ *ᵥ (Q'ᵀ *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, Matrix.one_mulVec]
  have h4 : xᵀ *ᵥ (P'ᵀ *ᵥ w) = Qᵀ *ᵥ (Dᵀ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hx,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [h4, ← Matrix.mulVec_add, ← hz]
  exact h3

end GlobalTheory.LatticeDuality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteRepresentativesModUniformizerPow
section
open Matrix

noncomputable section

namespace GlobalTheory.UnramReps

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem le_ofAdd_neg_one_of_lt_one' {y : WithZero (Multiplicative ℤ)} (h : y < 1) :
    y ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction y using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

theorem exists_residue_reps' {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = q ^ 2) :
    ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ x ∈ Formalism.UG.intL L, ∃ r ∈ R,
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) (x - r) < 1 := by
  classical
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
  have hfin : Finite (v.integer ⧸ IsLocalRing.maximalIdeal v.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI : Finite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring) := hfin
  haveI := Fintype.ofFinite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring)
  let f : v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring → L :=
    fun c => ((Ideal.Quotient.mk_surjective c).choose : L)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    show _ ∈ v.integer
    rw [Valuation.mem_integer_iff]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (Ideal.Quotient.mk_surjective c).choose.2
  · intro x hx
    have hx' : x ∈ v.valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).2 ((Valuation.mem_integer_iff _ _).1 hx)
    let xs : v.valuationSubring := ⟨x, hx'⟩
    let c := Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring) xs
    refine ⟨f c, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
    have hspec := (Ideal.Quotient.mk_surjective c).choose_spec
    have hmem : xs - (Ideal.Quotient.mk_surjective c).choose ∈
        IsLocalRing.maximalIdeal v.valuationSubring :=
      Ideal.Quotient.eq.1 (hspec.symm)
    rw [Valuation.mem_maximalIdeal_iff] at hmem
    simpa [xs, f] using hmem

theorem exists_reps_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧
      ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K := by
  intro L _ _ ϖ σ q hU
  classical
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := hU
  obtain ⟨R, hRO, hR⟩ := exists_residue_reps' (L := L) hq hcard
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
  have h0 : v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  have hϖ1 : v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    norm_num
  have hϖO : ϖ ∈ Formalism.UG.intL L := (Valuation.mem_integer_iff _ _).2 hϖ1
  intro K
  induction K with
  | zero =>
    refine ⟨{0}, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_singleton.1 hr]; exact (Formalism.UG.intL L).zero_mem
    · intro x hx
      refine ⟨0, Finset.mem_singleton_self 0, ?_⟩
      rw [sub_zero, pow_zero]
      exact (Valuation.mem_integer_iff _ _).1 hx
  | succ N ih =>
    obtain ⟨T, hTO, hT⟩ := ih
    refine ⟨Finset.image₂ (fun r t => r + ϖ * t) R T, ?_, ?_⟩
    · intro z hz
      obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_image₂.1 hz
      exact (Formalism.UG.intL L).add_mem (hRO r hr) ((Formalism.UG.intL L).mul_mem hϖO (hTO t ht))
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := hR x hx
      have hle : v (x - r) ≤ v ϖ := hϖ ▸ le_ofAdd_neg_one_of_lt_one' hxr
      set y := (x - r) * ϖ⁻¹ with hy
      have hϖ0 : ϖ ≠ 0 := fun h => h0 (by rw [h, map_zero])
      have hyO : y ∈ Formalism.UG.intL L := by
        apply (Valuation.mem_integer_iff _ _).2
        rw [hy, map_mul, map_inv₀]
        calc v (x - r) * (v ϖ)⁻¹ ≤ v ϖ * (v ϖ)⁻¹ := mul_le_mul' hle le_rfl
          _ = 1 := mul_inv_cancel₀ h0
      obtain ⟨t, ht, hyt⟩ := hT y hyO
      refine ⟨r + ϖ * t, Finset.mem_image₂.2 ⟨r, hr, t, ht, rfl⟩, ?_⟩
      have he : x - (r + ϖ * t) = ϖ * (y - t) := by
        rw [hy]; field_simp; ring
      show v (x - (r + ϖ * t)) ≤ v ϖ ^ (N + 1)
      rw [he, map_mul, pow_succ']
      exact mul_le_mul' le_rfl hyt

end GlobalTheory.UnramReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepresentativesMulInvIntegral
section
open Matrix

namespace GlobalTheory.Hk3.HoweDuality.Reps

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eventually_pow_mul_le_one (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (e : L) : ∀ᶠ K : ℕ in Filter.atTop, Valued.v ϖ ^ K * Valued.v e ≤ 1 := by
  rcases eq_or_ne (Valued.v e) 0 with h0 | h0
  · exact Filter.Eventually.of_forall fun K => by rw [h0, mul_zero]; exact zero_le
  · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    refine Filter.eventually_atTop.2 ⟨(Multiplicative.toAdd m).toNat, fun K hK => ?_⟩
    rw [← hm, hϖ, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe,
      ← ofAdd_nsmul, ← Multiplicative.toAdd_le]
    simp only [toAdd_mul, toAdd_ofAdd, toAdd_one, nsmul_eq_mul, mul_neg, mul_one]
    have : Multiplicative.toAdd m ≤ (K : ℤ) := (Int.self_le_toNat _).trans (by exact_mod_cast hK)
    linarith

end GlobalTheory.Hk3.HoweDuality.Reps

open GlobalTheory.Hk3.HoweDuality.Reps in
theorem GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (n n' : ℕ) (a : GL (Fin n) L) (x : Matrix (Fin n') (Fin n) L),
  (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ y ∈ Y, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
  intro L _ _ ϖ hϖ hR n n' a x hx
  classical
  set ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hai
  have hinv : ai * (a : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [hai, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  obtain ⟨K, hK⟩ := (Filter.eventually_all.2 fun p : Fin n × Fin n =>
    eventually_pow_mul_le_one ϖ hϖ (ai p.1 p.2)).exists
  obtain ⟨R, hRint, hRapp⟩ := hR K
  have hv1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]; simp

  let S : Finset (Matrix (Fin n') (Fin n) L) :=
    Fintype.piFinset fun _ : Fin n' => Fintype.piFinset fun _ : Fin n => R
  have hSint : ∀ s ∈ S, ∀ i j, s i j ∈ Formalism.UG.intL L := by
    intro s hs i j
    exact hRint _ (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hs i) j)

  have hcong : ∀ d : Matrix (Fin n') (Fin n) L, (∀ i j, Valued.v (d i j) ≤ Valued.v ϖ ^ K) →
      d * ai ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
    intro d hd i j
    rw [Matrix.mul_apply]
    refine (Formalism.UG.intL L).sum_mem fun k _ => ?_
    change Valued.v (d i k * ai k j) ≤ 1
    rw [map_mul]
    calc Valued.v (d i k) * Valued.v (ai k j) ≤ Valued.v ϖ ^ K * Valued.v (ai k j) := by gcongr; exact hd i k
      _ ≤ 1 := hK (k, j)
  let T : Finset (Matrix (Fin n') (Fin n) L) := insert x (S.image fun s => s * ai)
  have hTint : ∀ t ∈ T, ∀ i j, (t * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hx
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
      rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
      exact hSint s hs
  let q : Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n :=
    QuotientAddGroup.mk
  let rep : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n → Matrix (Fin n') (Fin n) L :=
    fun c => if q x = c then x else if h : ∃ t ∈ T, q t = c then h.choose else 0
  have hrep : ∀ t ∈ T, rep (q t) ∈ T ∧ q (rep (q t)) = q t := by
    intro t ht
    by_cases hxt : q x = q t
    · have hr : rep (q t) = x := by simp [rep, hxt]
      rw [hr]; exact ⟨Finset.mem_insert_self _ _, hxt⟩
    · have h : ∃ t' ∈ T, q t' = q t := ⟨t, ht, rfl⟩
      simp only [rep, hxt, if_false, h, dif_pos]
      exact h.choose_spec
  refine ⟨T.image fun t => rep (q t), ?_, ?_, ?_, ?_⟩
  · refine Finset.mem_image.2 ⟨x, Finset.mem_insert_self _ _, ?_⟩
    simp [rep]
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact hTint _ (hrep t ht).1
  · intro y hy y' hy' hyy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hy'
    have e : q t = q t' := by
      rw [← (hrep t ht).2, ← (hrep t' ht').2]
      exact QuotientAddGroup.eq_iff_sub_mem.2 hyy
    rw [e]
  · intro u hu
    have hpick : ∀ i j, ∃ r ∈ R, Valued.v (u i j - r) ≤ Valued.v ϖ ^ K := fun i j => hRapp _ (hu i j)
    choose s hsR hsv using hpick
    have hsS : (Matrix.of fun i j => s i j) ∈ S := by
      refine Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => hsR i j
    have ht : (Matrix.of fun i j => s i j) * ai ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hsS)
    refine ⟨rep (q ((Matrix.of fun i j => s i j) * ai)), Finset.mem_image_of_mem _ ht, ?_⟩
    have h1 : u * ai - (Matrix.of fun i j => s i j) * ai ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
      rw [← Matrix.sub_mul]
      exact hcong _ fun i j => by simpa using hsv i j
    have h2 := (hrep _ ht).2
    rw [← QuotientAddGroup.eq_iff_sub_mem] at h1 ⊢
    exact h1.trans h2.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvectorStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  first | exact @GlobalTheory.TorusEigenform.main | exact GlobalTheory.TorusEigenform.main | (intros; apply GlobalTheory.TorusEigenform.main <;> assumption)
end

