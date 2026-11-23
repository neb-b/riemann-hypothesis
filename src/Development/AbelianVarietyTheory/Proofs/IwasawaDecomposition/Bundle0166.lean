module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquations
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

section General

variable {σ : Type} [DecidableEq σ] {F : Fock σ} {v : F.H} {E : MvPowerSeries σ ℂ}


omit [DecidableEq σ] in
theorem prod_factorial_add_single (α : σ →₀ ℕ) (l : σ) :
    (α + Finsupp.single l 1).prod (fun _ k => (k.factorial : ℂ)) =
      ((α l : ℂ) + 1) * α.prod (fun _ k => (k.factorial : ℂ)) := by
  classical
  rw [← FockSeq.mfact_cast, ← FockSeq.mfact_cast, Oscillator.mfact_add_single]
  push_cast
  ring

theorem inner_X_mul_monomial (h : HasCoeff F v E) (l : σ) (α : σ →₀ ℕ) :
    inner ℂ (F.ι (MvPolynomial.X l * MvPolynomial.monomial α 1)) v =
      α.prod (fun _ k => (k.factorial : ℂ)) *
        (((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E) := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm, h, prod_factorial_add_single]
  ring

theorem inner_pderiv_monomial (h : HasCoeff F v E) (m : σ) (α : σ →₀ ℕ) :
    inner ℂ (F.ι (MvPolynomial.pderiv m (MvPolynomial.monomial α 1))) v =
      α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (MvPowerSeries.X m * E) := by
  have e : ∀ (γ : σ →₀ ℕ) (c : ℂ), (MvPolynomial.monomial γ c : MvPolynomial σ ℂ) =
      c • MvPolynomial.monomial γ 1 := fun γ c => by simp [MvPolynomial.smul_monomial]
  rw [MvPolynomial.pderiv_monomial, e, map_smul, inner_smul_left, h, MvPowerSeries.X_def,
    MvPowerSeries.coeff_monomial_mul]
  by_cases h0 : α m = 0
  · have : ¬ Finsupp.single m 1 ≤ α := by rw [Finsupp.single_le_iff, h0]; omega
    simp [h0, this]
  · have hle : Finsupp.single m 1 ≤ α := Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero h0)
    obtain ⟨β, rfl⟩ := exists_add_of_le hle
    rw [if_pos hle, add_tsub_cancel_left, add_comm, prod_factorial_add_single]
    simp
    ring

theorem inner_X_mul_of_deriv {κ : Type} [Fintype κ] (h : HasCoeff F v E) (l : σ) (c : ℂ) (a : κ → ℂ) (m : κ → σ)
    (hE : ∀ α : σ →₀ ℕ, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E =
      MvPowerSeries.coeff α (((MvPolynomial.C c + ∑ k, MvPolynomial.C (a k) * MvPolynomial.X (m k) :
        MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * E)) (f : MvPolynomial σ ℂ) :
    inner ℂ (F.ι (MvPolynomial.X l * f)) v =
      c * inner ℂ (F.ι f) v + ∑ k, a k * inner ℂ (F.ι (MvPolynomial.pderiv (m k) f)) v := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [mul_add, map_add (f := _), inner_add_left, hf, hg, Finset.sum_add_distrib]
    ring
  | monomial α b =>
    have e : (MvPolynomial.monomial α b : MvPolynomial σ ℂ) = b • MvPolynomial.monomial α 1 := by
      simp [MvPolynomial.smul_monomial]
    have e2 : ((MvPolynomial.C c + ∑ k, MvPolynomial.C (a k) * MvPolynomial.X (m k) :
        MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
        MvPowerSeries.C c + ∑ k, MvPowerSeries.C (a k) * MvPowerSeries.X (m k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add (f := _), map_sum]
      simp
    rw [e, mul_smul_comm]
    simp only [Derivation.map_smul, map_smul, inner_smul_left]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [inner_X_mul_monomial h, inner_pderiv_monomial h, h α, hE, e2, add_mul, Finset.sum_mul, map_add (f := _),
      map_sum, mul_assoc, MvPowerSeries.coeff_C_mul, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring

end General

variable {P Q : ℕ}

theorem pderiv_inl_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (i : Fin P) :
    MvPolynomial.pderiv (Sum.inl i) (gaussPoly A x) =
      MvPolynomial.C (x (Sum.inl i)) + ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inr j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gaussPoly, map_add (f := _), map_sum, mul_assoc, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  rw [add_comm, Finset.sum_comm]
  simp

theorem pderiv_inr_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (j : Fin Q) :
    MvPolynomial.pderiv (Sum.inr j) (gaussPoly A x) =
      MvPolynomial.C (x (Sum.inr j)) + ∑ i, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inl i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gaussPoly, map_add (f := _), map_sum, mul_assoc, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  rw [add_comm]
  simp

theorem gauss_annihilator (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H)
    (h : HasCoeff F v (expPS (gaussPoly A x))) :
    (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v =
      x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) ∧
    (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v =
      x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) := by
  refine ⟨fun i f => ?_, fun j f => ?_⟩
  · refine inner_X_mul_of_deriv h _ _ (fun j => A i j) (fun j => Sum.inr j) (fun α => ?_) f
    rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x), pderiv_inl_gaussPoly]
  · refine inner_X_mul_of_deriv h _ _ (fun i => A i j) (fun i => Sum.inl i) (fun α => ?_) f
    rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x), pderiv_inr_gaussPoly]

end GlobalTheory.OscGauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.HeckeExp

variable {D : D7}


open Classical in
theorem exists_idele_at {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1,
      by rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := by
    rw [← sub_eq_zero]
    refine hσ.ext _ (by rw [RingHom.map_sub, RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul, sub_self]) fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one,
      sub_eq_zero]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem arg_ne_zero (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) :
    θ (infPart D (x : AE D)) / (‖θ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
  have h : θ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map θ).ne_zero
  exact div_ne_zero h (by exact_mod_cast norm_ne_zero_iff.2 h)

theorem eq_of_zpow_eq {n m : ℤ} (h : ∀ w : ℂ, ‖w‖ = 1 → w ^ n = w ^ m) : n = m := by
  by_contra hne
  have hd : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have h1 := h (Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I _)
  have h2 : Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I) ^ (n - m) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  have hd' : ((n - m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have e : ((n - m : ℤ) : ℂ) * (((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_intCast]; field_simp
  rw [← Complex.exp_int_mul, e, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem hasInfExp_unique {χ : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ τ a') :
    a = a' := by
  obtain ⟨n, hn, ⟨θ, hθ⟩, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  have e : n = m := eq_of_zpow_eq fun w hw => by
    obtain ⟨x, hx1, hx2⟩ := exists_idele_at hθ τ w (by rintro rfl; simp at hw)
    have ho : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' hτ => by rw [hx2, if_neg hτ]
    have e1 := h1 θ hθ x hx1 ho
    have e2 := h2 θ hθ x hx1 ho
    rw [hx2, if_pos rfl, hw, Complex.ofReal_one, div_one] at e1 e2
    exact e1.symm.trans e2
  subst e
  linarith

theorem hasInfExp_mul {χ χ' : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ' τ a') :
    HasInfExp D (χ * χ') τ (a + a') := by
  obtain ⟨n, hn, h0, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hτ, h2 θ hθ x hx hτ, zpow_add₀ (arg_ne_zero _ x)]

theorem hasInfExp_inv {χ : IdC D} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ τ a) : HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, h0, h1⟩ := h
  refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hτ, _root_.zpow_neg]

def hcSubgroup (D : D7) : Subgroup (IdC D) where
  carrier := {χ | IsHC D χ}
  one_mem' := isHC_one D
  mul_mem' := fun {χ χ'} h h' =>
    ⟨⟨h.1.1.mul h'.1.1, fun x => by rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => (h'.2 τ).elim fun _ ha' => ⟨_, hasInfExp_mul ha ha'⟩⟩
  inv_mem' := fun {χ} h =>
    ⟨⟨h.1.1.inv, fun x => by rw [MonoidHom.inv_apply, h.1.2, inv_one]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => ⟨_, hasInfExp_inv ha⟩⟩

theorem hecke_exp_laws : ∀ D : D7, (∃ C : Subgroup (IdC D), ∀ χ, χ ∈ C ↔ IsHC D χ) ∧
    (∀ (χ : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ τ a' → a = a') ∧
    ∀ (χ χ' : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ' τ a' → HasInfExp D (χ * χ') τ (a + a') :=
  fun D => ⟨⟨hcSubgroup D, fun _ => Iff.rfl⟩, fun _ _ _ _ => hasInfExp_unique, fun _ _ _ _ _ => hasInfExp_mul⟩

end GlobalTheory.Mem.HeckeExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions : ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → IsUnit (1 - Aᴴ * B).det := by
  first | exact @GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions | exact GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions | (intros; apply GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDvdOfAdicValuationLtOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelUnif

open GlobalTheory.LevelHecke

theorem le_exp_sub_one {x : WithZero (Multiplicative ℤ)} {n : ℤ} (h : x < WithZero.exp n) :
    x ≤ WithZero.exp (n - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem T_notMem_sq (D : D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 := by
  set v0 := A.eV.symm ⟨v, hv⟩ with hv0
  have hU := GlobalTheory.LevelUnram.unram D u A v0
  set P := RingHom.ker (A.res v0) with hP
  haveI hPp : P.IsPrime := RingHom.ker_isPrime _
  have hvP : ∀ x, x ∈ v.asIdeal → algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P := by
    intro x hx
    have h := (A.res_v v0 x).1 (by rw [hv0, Equiv.apply_symm_apply]; exact hx)
    exact h
  have hTP : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ P := hU.1
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hPbot : P ≠ ⊥ := fun h => hT0 (by rw [h] at hTP; exact (Ideal.mem_bot).1 hTP)
  have hlt : P ^ 2 < P ^ 1 := Ideal.pow_right_strictAnti P hPbot hPp.ne_top (by norm_num)
  rw [pow_one] at hlt
  obtain ⟨a, haP, ha2⟩ := SetLike.exists_of_lt hlt
  have hTE : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ P ^ 2 := by
    intro hT2
    obtain ⟨s, b, hs, hsab⟩ := hU.2 a haP
    have h1 : s * a ∈ P ^ 2 := by rw [hsab]; exact Ideal.mul_mem_right _ _ hT2
    rcases Ideal.IsPrime.mul_mem_pow P h1 with h | h
    · exact hs h
    · exact ha2 h
  intro hv2
  apply hTE
  have hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤ P :=
    Ideal.map_le_iff_le_comap.2 (fun x hx => hvP x hx)
  have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2
  rw [Ideal.map_pow] at h3
  have h4 := Ideal.pow_right_mono hle 2 h3
  simpa using h4

theorem dvd_of_val_lt_one : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (_ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal)
    (a : v.adicCompletionIntegers D.host.F) (_ : Valued.v (a : v.adicCompletion D.host.F) < 1),
    ∃ b : v.adicCompletionIntegers D.host.F, a = (((D.mem u).A.T : ℕ) : v.adicCompletionIntegers D.host.F) * b := by
  intro D u A v hv a ha
  have hT2 := T_notMem_sq D u A v hv
  have hval : v.intValuation (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1) := by
    apply le_antisymm
    · have h := (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)
      simpa using h
    · by_contra h
      push_neg at h
      have h2 := le_exp_sub_one h
      norm_num at h2
      exact hT2 ((v.intValuation_le_pow_iff_mem _ 2).1 (by simpa using h2))
  have hTv : Valued.v ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) = WithZero.exp (-1) := by
    have h := v.valuedAdicCompletion_eq_valuation (K := D.host.F) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F)
    rw [HeightOneSpectrum.valuation_of_algebraMap, hval] at h
    simpa using h
  have hc0 : ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) ≠ 0 := by
    intro h; rw [h, map_zero] at hTv; exact WithZero.zero_ne_coe hTv
  have hale : Valued.v (a : v.adicCompletion D.host.F) ≤ WithZero.exp (-1) := by
    have h := le_exp_sub_one (n := 0) (by simpa using ha)
    simpa using h
  set c : v.adicCompletion D.host.F := (((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F) with hc
  have hb : (a : v.adicCompletion D.host.F) / c ∈ v.adicCompletionIntegers D.host.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hTv]
    rw [div_le_one₀ (by simp)]
    exact hale
  refine ⟨⟨_, hb⟩, Subtype.ext ?_⟩
  push_cast
  rw [← hc, mul_div_cancel₀ _ hc0]

end GlobalTheory.LevelUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralOrthogonalComplementPairIndepGroupElemeStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → IsInvTup R σ J' m' → ∀ (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g k : HA R σ J), g • ratTup (F := F) R x = k • ratTup (F := F) R x → ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ y', f (pairOf R σ J B y g y') ∂m' = ∫⁻ y', f (pairOf R σ J B y k y') ∂m' := by
  first | exact @GlobalTheory.TwoStepIndep.lintegral_pairOf_eq | exact GlobalTheory.TwoStepIndep.lintegral_pairOf_eq | (intros; apply GlobalTheory.TwoStepIndep.lintegral_pairOf_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LrActScalar
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.Polar

theorem qR_scalar {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (r : R)
    (z : Fin M → R ⊗[F] E) :
    qR R σ J (algebraMap R (R ⊗[F] E) r • z) = r * r * qR R σ J z := by
  have hs : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  have h : hR R σ J (algebraMap R (R ⊗[F] E) r • z) (algebraMap R (R ⊗[F] E) r • z)
      = (r * r) • hR R σ J z z := by
    rw [Algebra.smul_def (r * r), map_mul]
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [qR, h, map_smul, smul_eq_mul]
  ring

theorem lrAct_scalar {S : Type} [CommRing S] {n M : ℕ} (c : S) (X : Fin n → Fin M → S) :
    lrAct (c • (1 : Matrix (Fin M) (Fin M) S)) 1 X = c • X := by
  funext a i
  simp [lrAct, Matrix.smul_mulVec, Matrix.one_apply]

theorem polar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J (tupMeas lam 1 M) ν β m → ∀ (W : Set R) (ρ : R → R), MeasurableSet W → (∀ b ∈ W, IsUnit (ρ b) ∧ ρ b * ρ b * β = b) → ∀ f : (Fin 1 → Fin M → R ⊗[F] E) → ℝ≥0∞, Measurable f → (∀ X, qR R σ J (X 0) ∉ W → f X = 0) → ∫⁻ X, f X ∂(tupMeas lam 1 M) = ∫⁻ b in W, ((modu (R ⊗[F] E) (algebraMap R (R ⊗[F] E) (ρ b) ^ M) * (modu R (ρ b * ρ b))⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ X, f (algebraMap R (R ⊗[F] E) (ρ b) • X) ∂m ∂ν := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hN M J lam ν β m hlam hν hβ hfib W ρ hW hρ f hf hf0
  obtain ⟨fib, hfam, hm⟩ := id hfib
  have h2 := hfam.2.1 f hf
  rw [Measure.restrict_univ] at h2
  rw [h2, ← lintegral_indicator hW]
  refine lintegral_congr fun b => ?_
  by_cases hb : b ∈ W
  · rw [Set.indicator_of_mem hb]
    obtain ⟨hr, hrb⟩ := hρ b hb
    set c : R ⊗[F] E := algebraMap R (R ⊗[F] E) (ρ b) with hc
    have hdet : (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))).det = c ^ M := by
      simp
    have hcu : IsUnit c := hr.map _
    have h1 := GlobalTheory.GaugeEx.fibAt_similitude F E σ R hN M J J lam ν β (ρ b * ρ b) m
      (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hlam hν (by rw [hdet]; exact hcu.pow M)
      (hr.mul hr) (fun z => by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact qR_scalar σ R J (ρ b) z) hfib
    rw [hrb, hdet] at h1
    have hbu : IsUnit b := hrb ▸ (hr.mul hr).mul hβ
    have h3 := (GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ R hN M J _ ν b _ hν hbu h1).2.2 (fib b)
      ⟨fib, hfam, rfl⟩
    have hl : lrAct (n := 1) (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) 1 = fun X => c • X :=
      funext fun X => lrAct_scalar c X
    have hcont : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => c • X := continuous_const_smul c
    rw [h3, hl, lintegral_smul_measure, lintegral_map hf hcont.measurable]
    rfl
  · rw [Set.indicator_of_notMem hb]
    have h1 := hfam.1 b
    have hae : f =ᵐ[fib b] 0 := by
      refine measure_mono_null (fun X hX => ?_) h1
      intro hX'
      apply hX
      apply hf0
      have : qR R σ J (X 0) = b := hX'.1
      rw [this]; exact hb
    rw [lintegral_congr_ae hae]
    simp

end GlobalTheory.GaugeEx.Polar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenNormCoeffOfFibre
section
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem mem_basicOpen_normCoeff_of_fibre {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    {V : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
    (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X) (hx : x ∈ V) (h : ∀ y : Y, f y = x → y ∈ Y.basicOpen τ) :
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  have hV' := hV.preimage f
  have sq := hV.SpecMap_appLE_fromSpec f hV' le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at sq
  have pt : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V),
      hV.fromSpec (PrimeSpectrum.comap (f.app V).hom q) = f (hV'.fromSpec q) := fun q => congr($(sq) q)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have e₁ : ∀ c : Γ(X, V), hV.fromSpec p ∈ X.basicOpen c ↔ c ∉ p.asIdeal := fun c => by
    rw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]; rfl
  have e₂ : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV'.fromSpec q ∈ Y.basicOpen τ ↔ τ ∉ q.asIdeal :=
    fun q : Spec Γ(Y, f ⁻¹ᵁ V) => by rw [← Scheme.Hom.mem_preimage, hV'.fromSpec_preimage_basicOpen]; rfl
  have inj := hV.fromSpec.isOpenEmbedding.injective
  have h0 : ∃ Q : Ideal Γ(Y, f ⁻¹ᵁ V), Q.IsPrime ∧ Q.comap (f.app V).hom = ⊥ := by
    let P0 : PrimeSpectrum Γ(X, V) := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨y, hy⟩ := f.surjective (hV.fromSpec P0)
    have hyV : f y ∈ V := by
      have hr : hV.fromSpec P0 ∈ Set.range hV.fromSpec := ⟨P0, rfl⟩
      rw [hV.range_fromSpec] at hr
      rw [hy]; exact hr
    obtain ⟨q, rfl⟩ : y ∈ Set.range hV'.fromSpec := by rw [hV'.range_fromSpec]; exact hyV
    exact ⟨q.asIdeal, q.isPrime, congrArg PrimeSpectrum.asIdeal (inj ((pt q).trans hy))⟩
  obtain ⟨k, hk, hc⟩ := GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime (f.app V).hom (f.finite_app V hV) τ h0 p.asIdeal p.isPrime
    (fun Q hQ hQp => by
      let q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V) := ⟨Q, hQ⟩
      have e : PrimeSpectrum.comap (f.app V).hom q = p := PrimeSpectrum.ext hQp
      exact (e₂ q).1 (h _ ((pt q).symm.trans (congrArg hV.fromSpec e))))
  exact ⟨k, hk, (e₁ _).2 hc⟩

end GlobalTheory.NormalDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDualStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_O1_iso_blowup_twist_dual : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (J : X.IdealSheafData) (L₀ : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L₀.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (D : GlobalTheory.EffCartierData W), L₀.IsLB →
    GlobalTheory.ProjBlowup.Generates J σ → GlobalTheory.ProjBlowup.Proportional σ g ψ → D.idealSheaf = J.comap g →
    LBIso ((GlobalTheory.ProjSpace.O1 R m).pull ψ) (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := by
  first | exact @GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional | exact GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional | (intros; apply GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional <;> assumption)
end

