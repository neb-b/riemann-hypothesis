module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ImagQuadraticDescentGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle0005
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    ∑ i, lieS E a i i z ψ = dchi ω z • ψ := by
  have e2 : lie E a (Central.scL a z) = ∑ i, lieS E a i i z := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lieS_apply, ← map_sum]
    exact congrArg (lie E a) (Matrix.sum_single_eq_diagonal (fun _ : Fin a => z)).symm
  rw [← LinearMap.sum_apply, ← e2]
  refine Subtype.ext (funext fun g => ?_)
  have h1 := Central.hasDerivAt_scalar z ψ g
  have h2 : (fun t : ℝ => ψ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    have h3 := congrFun (congrArg Subtype.val (hω (infId E (expU (t • z))) ψ hψ)) g
    have h4 := chiInf_expU ω (t • z)
    rw [map_smul, Complex.real_smul] at h4
    rw [← h4]
    exact h3
  rw [h2] at h1
  have h5 := (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)
  have h6 := h1.unique h5
  change lieD _ ψ.1 g = dchi ω z * ψ.1 g
  rw [h6]
  simp

private theorem expo_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : π.HasInfChar τ m) : expo ω τ = m.sum := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine smul_left_injective ℂ h0 ?_
  beta_reduce
  rw [← GlobalTheory.trace_Eop_of_hasInfChar E a π τ m hm φ hφ]
  have h1 := lie_central hω (atEmb τ 1) hφ
  have h2 := lie_central hω (atEmb τ Complex.I) hφ
  simp only [Eop, expo, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, ← Finset.smul_sum, Finset.sum_sub_distrib, h1, h2]
  module

private theorem det_algSat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = (q : ℂ) * ((x * y : ℂˣ) : ℂ) := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  have e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x,
      (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y} := by
    simp [algSat]
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, mul_mul_mul_comm, hq',
    Units.val_mul]

private theorem gap_of_sum {x y : ℂ} (hne : x ≠ y) {i j : ℤ} (hi : x = i + 1 / 2) (hj : y = j + 1 / 2) (hs : x + y = 1) :
    ∃ (c : ℂ) (k : ℕ), 2 ≤ k ∧ ({x, y} : Multiset ℂ) = {c, c + k} := by
  have h0 : i + j = 0 := by
    have : ((i + j : ℤ) : ℂ) = 0 := by push_cast; linear_combination hs - hi - hj
    exact_mod_cast this
  have h1 : i ≠ j := fun e => hne (by rw [hi, hj, e])
  rcases lt_or_gt_of_ne h1 with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨x, k, by omega, ?_⟩
    have : ((j - i : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show x + k = y by linear_combination hi - hj - this]
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨y, k, by omega, ?_⟩
    have : ((i - j : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show y + k = x by linear_combination hj - hi - this, Multiset.pair_comm]

end SlopeTestRemainingChoices
