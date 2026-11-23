module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0029
public import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneous
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.BlockHom

open MvPolynomial

theorem two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zpow, Complex.norm_ofNat] at h'
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h'

theorem eval_aeval_gen {σ κ : Type} (g : κ → ℂ) (φ : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    MvPolynomial.eval g (MvPolynomial.aeval φ Q) = MvPolynomial.eval (fun s => MvPolynomial.eval g (φ s)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p s hp => rw [map_mul, map_mul, aeval_X, map_mul, hp, eval_X]

open Classical in
theorem evFr_scale (D : D7) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (τ₀ : D.what₂.Tau) (t : ℂ) (ht : t ≠ 0) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    GL3Theta.evFr D Q (fun τ => if τ = τ₀ then t • y τ else y τ) = t ^ (∑ r, ν τ₀ r) * GL3Theta.evFr D Q y := by
  set β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ => if τ = τ₀ then t • (1 : Matrix (Fin n) (Fin n) ℂ) else 1 with hβ
  have hB : IsBor β := by
    intro τ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp only [hβ]; split_ifs <;> simp [Matrix.one_apply_ne (ne_of_lt hsr).symm]
    · simp only [hβ]; split_ifs <;> simp [ht]
  have h1 := congrArg (MvPolynomial.eval (fun k : GL3Theta.FrV D n => y k.1 k.2.1 k.2.2)) (hQ β hB)
  have hL : MvPolynomial.eval (fun k : GL3Theta.FrV D n => y k.1 k.2.1 k.2.2) (colSub β Q) =
      GL3Theta.evFr D Q (fun τ => if τ = τ₀ then t • y τ else y τ) := by
    unfold colSub GL3Theta.evFr
    rw [eval_aeval_gen]
    apply congrArg (fun F => MvPolynomial.eval F Q)
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_C, eval_X, hβ]
    by_cases hk : k.1 = τ₀
    · simp [hk, Matrix.one_apply, mul_comm]
    · simp [hk, Matrix.one_apply]
  rw [← hL, h1, MvPolynomial.smul_eval]
  unfold GL3Theta.evFr
  congr 1
  rw [Finset.prod_eq_single τ₀]
  · simp [hβ, Finset.prod_pow_eq_pow_sum]
  · intro τ _ hτ
    simp [hβ, hτ]
  · simp

open Classical in
theorem prod_scale {ι : Type} [Fintype ι] (τ₀ : ι) (A B : ι → ℂ) (k : ℂ)
    (hAB : ∀ τ, A τ = if τ = τ₀ then k * B τ else B τ) (e : ι → ℤ) :
    ∏ τ, A τ ^ e τ = k ^ e τ₀ * ∏ τ, B τ ^ e τ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀), ← Finset.mul_prod_erase (s := Finset.univ) (fun τ => B τ ^ e τ) (Finset.mem_univ τ₀)]
  rw [hAB τ₀, ite_eq_left rfl, mul_zpow, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro τ hτ
  rw [hAB τ, ite_eq_right (Finset.ne_of_mem_erase hτ)]

open Classical in
theorem zT_scale {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f f' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, IsUnit (f τ).det) (τ₀ : D.what₂.Tau) (c : ℂ) (hc : c ≠ 0)
    (hf' : ∀ τ, f' τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then c⁻¹ else c) • f τ else f τ) (τ : D.what₂.Tau) :
    zT X D pos f' τ = if τ = τ₀ then c • zT X D pos f τ else zT X D pos f τ := by
  unfold zT
  rw [hf' τ]
  by_cases hτ : τ = τ₀
  · subst hτ
    simp only [ite_true]
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [ho, ite_true]
      rw [show c⁻¹ • f τ = (Units.mk0 c⁻¹ (inv_ne_zero hc)) • f τ from rfl, Matrix.inv_smul' (k := Units.mk0 c⁻¹ (inv_ne_zero hc)) (h := hf τ)]
      ext a b
      simp [Matrix.submatrix_apply, Matrix.transpose_apply, Units.smul_def]
    · simp [ho]
  · simp [hτ]

def dg {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) (τ₀ : D.what₂.Tau)
    (m : Var (X.Pj i) →₀ ℕ) : ℕ :=
  ∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then m x else 0

open Classical in
theorem valZ_scale {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f f' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, IsUnit (f τ).det)
    (τ₀ : D.what₂.Tau) (hf' : ∀ τ, f' τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2) • f τ else f τ) :
    valZ X D pos i h R f' = valZ X D pos i h (∑ m ∈ R.support, monomial m (AddMonoidAlgebra.coeff R m * 2 ^ (dg X D pos i τ₀ m))) f := by
  have hg : ∀ x : Var (X.Pj i), zT X D pos f' (posJ X D pos i ⟨x.1, x.2.1⟩) (Fin.cast h x.2.2.1) (Fin.cast h x.2.2.2) =
      (2:ℂ) ^ (if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then 1 else 0) *
        zT X D pos f (posJ X D pos i ⟨x.1, x.2.1⟩) (Fin.cast h x.2.2.1) (Fin.cast h x.2.2.2) := by
    intro x
    rw [zT_scale X D pos f f' hf τ₀ 2 two_ne_zero hf']
    by_cases hb : (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀
    · simp [hb]
    · have e : posJ X D pos i ⟨x.1, x.2.1⟩ ≠ τ₀ := fun e => hb (by rw [← e]; simp)
      simp [e, hb]
  unfold valZ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.eval_eq, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hsum : (∑ x ∈ m.support, (if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then 1 else 0) * m x) = dg X D pos i τ₀ m := by
    unfold dg
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans ?_
    · intro x _ hx
      have hx0 : m x = 0 := by simpa using hx
      simp [hx0]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
  simp only [hg, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  rw [hsum, Finset.prod_subset (Finset.subset_univ m.support) (fun x _ hx => by
    have hx0 : m x = 0 := by simpa using hx
    simp [hx0])]
  ring

theorem realises_blockHom : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Q ∈ WtPol ℂ ν → Realises X D pos i h a Q R → ∀ m ∈ R.support, ∀ τ, (∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ then (m x : ℤ) else 0) = (if IsOddPos (pos.symm τ).2 then -1 else 1) * ((∑ r, (ν τ r : ℤ)) - n * a τ) - n * eT X D pos i τ := by
  intro p _ X D pos i n h a ν Q R hQ hR m hm τ₀
  classical
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = if IsOddPos (pos.symm τ₀).2 then -1 else 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2 := ⟨_, rfl⟩
  have htε : t = (2:ℂ) ^ ε := by
    rw [ht, hε]; split_ifs <;> simp
  have ht0 : t ≠ 0 := by rw [htε]; exact zpow_ne_zero _ two_ne_zero
  obtain ⟨R2, hR2⟩ : ∃ R2 : XR (X.Pj i) ℂ, R2 = ∑ m ∈ R.support, monomial m (AddMonoidAlgebra.coeff R m * 2 ^ (dg X D pos i τ₀ m)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (((2:ℂ) ^ n) ^ eT X D pos i τ₀)⁻¹ * ((t ^ n) ^ (-(a τ₀)) * t ^ (∑ r, ν τ₀ r)) := ⟨_, rfl⟩
  have key : ∀ f : Fr1 D n, ev1 X D pos i h R2 f = c * ev1 X D pos i h R f := by
    intro f
    have hfu : ∀ τ, IsUnit (f.1 τ).det := f.2
    let f' : Fr1 D n := ⟨fun τ => if τ = τ₀ then t • f.1 τ else f.1 τ, by
      intro τ
      by_cases hτ : τ = τ₀
      · simp only [hτ, ite_true, Matrix.det_smul]
        exact (IsUnit.mk0 _ (pow_ne_zero _ ht0)).mul (hfu τ₀)
      · simp only [hτ, ite_false]; exact hfu τ⟩
    have hf' : ∀ τ, f'.1 τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2) • f.1 τ else f.1 τ := by
      intro τ; rw [← ht]
    have e1 := _root_.GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ X D pos i h R2 f
    have e2 := _root_.GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ X D pos i h R f'
    have e3 := hR f'
    have e4 := hR f
    have hv : valZ X D pos i h R f'.1 = valZ X D pos i h R2 f.1 := by
      rw [hR2]; exact valZ_scale X D pos i h R f.1 f'.1 hfu τ₀ hf'
    have hdz : ∏ τ, (zT X D pos f'.1 τ).det ^ eT X D pos i τ =
        ((2:ℂ) ^ n) ^ eT X D pos i τ₀ * ∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ := by
      apply prod_scale
      intro τ
      rw [zT_scale X D pos f.1 f'.1 hfu τ₀ 2 two_ne_zero hf' τ]
      split_ifs <;> simp
    have hdf : ∏ τ, (f'.1 τ).det ^ (-(a τ)) = (t ^ n) ^ (-(a τ₀)) * ∏ τ, (f.1 τ).det ^ (-(a τ)) := by
      apply prod_scale
      intro τ
      show (if τ = τ₀ then t • f.1 τ else f.1 τ).det = _
      split_ifs <;> simp
    have hq : GL3Theta.evFr D Q f'.1 = t ^ (∑ r, ν τ₀ r) * GL3Theta.evFr D Q f.1 := evFr_scale D ν Q hQ τ₀ t ht0 f.1
    have hK : ((2:ℂ) ^ n) ^ eT X D pos i τ₀ ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ two_ne_zero)
    have hE := e2.symm.trans e3
    rw [hv, hdz, hdf, hq] at hE
    rw [e1, e4, hc]
    calc (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R2 f.1
        = (((2:ℂ) ^ n) ^ eT X D pos i τ₀)⁻¹ * (((2:ℂ) ^ n) ^ eT X D pos i τ₀ *
            (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R2 f.1) := by
          field_simp
      _ = _ := by rw [hE]; ring
  have hz : R2 - c • R = 0 := by
    apply _root_.GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames X D pos i h
    intro f
    rw [map_sub, map_smul]
    simp [key f]
  have hcoef : AddMonoidAlgebra.coeff R2 m = AddMonoidAlgebra.coeff R m * 2 ^ (dg X D pos i τ₀ m) := by
    rw [hR2, coeff_sum]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      rw [coeff_monomial, ite_eq_right hb]
    · intro hm'; exact absurd hm hm'
  have hm0 : AddMonoidAlgebra.coeff R m ≠ 0 := (mem_support_iff.mp hm)
  have h2 : (2:ℂ) ^ (dg X D pos i τ₀ m) = c := by
    have := congrArg (AddMonoidAlgebra.coeff · m) hz
    rw [coeff_sub, coeff_smul, hcoef, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, sub_eq_zero, smul_eq_mul] at this
    exact mul_left_cancel₀ hm0 (by rw [this]; ring)
  have hcz : c = (2:ℂ) ^ (-((n : ℤ) * eT X D pos i τ₀) + (ε * ((n : ℤ) * (-(a τ₀))) + ε * ((∑ r, ν τ₀ r : ℕ) : ℤ))) := by
    have a1 : ((2:ℂ) ^ n) ^ (eT X D pos i τ₀) = (2:ℂ) ^ ((n : ℤ) * eT X D pos i τ₀) := by rw [zpow_mul, zpow_natCast]
    have a2 : (((2:ℂ) ^ ε) ^ n) ^ (-(a τ₀)) = (2:ℂ) ^ (ε * ((n : ℤ) * (-(a τ₀)))) := by rw [zpow_mul, zpow_mul, zpow_natCast]
    have a3 : ((2:ℂ) ^ ε) ^ (∑ r, ν τ₀ r) = (2:ℂ) ^ (ε * ((∑ r, ν τ₀ r : ℕ) : ℤ)) := by rw [zpow_mul, zpow_natCast]
    rw [hc, htε, a1, a2, a3, zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_neg]
  have hfin : ((dg X D pos i τ₀ m : ℕ) : ℤ) = -((n : ℤ) * eT X D pos i τ₀) + (ε * ((n : ℤ) * (-(a τ₀))) + ε * ((∑ r, ν τ₀ r : ℕ) : ℤ)) :=
    two_zpow_inj (by rw [zpow_natCast, h2, hcz])
  unfold dg at hfin
  push_cast at hfin
  rw [hfin, hε]
  ring

end GlobalTheory.TwV.DelA.BlockHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLabelsWithStepZeroClassMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Port


set_option maxHeartbeats 4000000 in
theorem site_labels_with_stepZero_classMap : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), Fl.mm = D.R.m → SiteGood Z → (∀ j, j < D.R.m → (Tw.fm u μ).KRat j) → (D.chTw u μ).DGam ∣ (D.mem u).C.DGam → ∀ (one : OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y) (e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0), ∃ X : LabIn (Z.inTw Fl ht Gt), ∀ a (La : (D.gat u w hg).P.Tup), X.c0.cls a La = e0 (levelZeroClass one a La) := by
  intro D Gt c g u w hg Tw μ Z Fl ht hm G rat dgam one e0
  refine ⟨labOf ⟨fun _ _ => rfl, fun j hj => chX_stepInOf hj (Z.Fo j hj) (Z.loc Fl ht j hj) (Gt.gat_pos u w hg) (Z.sameU Fl ht j hj)
    (Z.frRat Fl ht j hj) (hypTJC_site Z Fl ht G.siteGood_prime_torsion j hj), fillOK_of_empty (Z.lv_empty Fl ht)⟩ ht hm
    (clsAt0Of one e0 (fun c => Formalism.L2.G.Triv.card_stab (g.herm.lev0 u) D.host.g_prime D.host.g_ne c) _) rat dgam, fun a La => rfl⟩

end GlobalTheory.Port
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLocalIdentificationsEqStepZero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Proof.LocOfSite

section Step

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  {cmp : Type} [hcmp : Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}

theorem iw_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (B0 : GL (Fin D.R.k) D.host.E) (v) :
    (locJ hi t B).iw v = (locAt X u w hg B0).iw v := rfl

theorem pl_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (B0 : GL (Fin D.R.k) D.host.E) (v) :
    (locJ hi t B).pl v = (locAt X u w hg B0).pl v := rfl

theorem B_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : (locJ hi t B).B = reGL (rankN D (i + 1) hi) _ B := rfl

theorem splAlg_locJ' (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : GlobalTheory.TwV.SplAlg (locJ hi t B) :=
  fun _ a => (X.g u w hg).spl_alg _ _ a

end Step

theorem splAlg_locAt {D : D7} (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B0 : GL (Fin D.R.k) D.host.E) :
    GlobalTheory.TwV.SplAlg (locAt X u w hg B0) :=
  fun _ a => (X.g u w hg).spl_alg _ _ a


set_option maxHeartbeats 4000000 in
theorem loc_eq_step0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).iw v = (lev0At g u w hg).A.iw v) ∧ (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).pl v = (lev0At g u w hg).A.pl v) ∧ (∀ j hj β β', (((Z.inTw Fl ht Gt).at' j hj).st.loc β).B = (((Z.inTw Fl ht Gt).at' j hj).st.loc β').B) ∧ (∀ j hj, ((Z.inTw Fl ht Gt).at' j hj).st.pos = Gt.gat_pos u w hg) ∧ (∀ j hj β, GlobalTheory.TwV.SplAlg (((Z.inTw Fl ht Gt).at' j hj).st.loc β)) ∧ GlobalTheory.TwV.SplAlg (lev0At g u w hg).A := by
  intro D Gt c g u w hg Tw μ Z Fl ht
  refine ⟨fun j hj β v => ?_, fun j hj β v => ?_, fun j hj β β' => ?_, fun j hj => rfl, fun j hj β => ?_,
    splAlg_locAt g.herm u w hg g.cmp.B⟩
  · exact iw_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B g.cmp.B v
  · exact pl_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B g.cmp.B v
  · exact (B_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B).trans
      (B_locJ (hcmp := (Z.loc Fl ht j hj).fin β') hj ((Z.loc Fl ht j hj).t β') (Z.loc Fl ht j hj).B).symm
  · exact splAlg_locJ' (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B

end GlobalTheory.Proof.LocOfSite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimes
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SitePrime


set_option maxHeartbeats 2000000 in
theorem resChar_not_mem_S : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), D.what₂.places.resChar w ∉ (t.O u μ).S := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ J hmem
  obtain ⟨-, -, -, hg'⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨-, -, -, -, -, hT'⟩ := id hg
  rw [t.O_S u μ] at hmem
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | (h | h) | h
  · exact hT' (h ▸ dvd_rfl)
  · exact hg' 0 h
  · exact hg' 1 h
  · exact J.away h

end GlobalTheory.TwV.SitePrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulDualSetLatAdMem
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem smul_dualSet_latAd_mem {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) (T : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)) (hT : 0 < T)
    (hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb)
    (hdual : ∀ z ∈ dualSet (sp.cm.sig : E →+* E) J Lb, (T : E) • z ∈ Lb)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    (z : Fin N → E) (hz : z ∈ dualSet (sp.cm.sig : E →+* E) J (latAd y Lb)) :
    (T : E) • z ∈ latAd y Lb := by
  have hlat : latAd y Lb = Formalism.UG.CS.globLat y Lb := Submodule.span_eq (Formalism.UG.CS.globLat y Lb)
  set a : 𝓞 E := (T : 𝓞 E) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact_mod_cast hT.ne'
  have hsm : ∀ w : Fin N → E, a • w = (T : E) • w := by
    intro w
    rw [← algebraMap_smul E a w, ha, map_natCast]

  have hdl : ∀ w ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb, a • w ∈ Lb := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => rw [hsm]; exact hdual w hw
    | zero => rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
    | smul c w _ hw => rw [smul_comm]; exact Lb.smul_mem c hw
  have hle : Ideal.span {a} • Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb ≤ Lb := by
    refine Submodule.smul_le.2 fun r hr w hw => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Lb.smul_mem c (hdl w hw)

  have hz' : z ∈ Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) := by
    rw [Formalism.L2.GlobalTheoryTheory.Comp.glob_dl sp.cm.sig J (GlobalTheory.isLat_dl_of_isOrthCo sp J hco) hLb y hy]
    rw [hlat] at hz
    exact Submodule.subset_span hz
  have h1 : a • z ∈ Ideal.span {a} • Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) :=
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hz'
  have h2 := Formalism.L2.GlobalTheoryTheory.Comp.glob_mono y hle
    (Formalism.L2.GlobalTheoryTheory.Comp.smul_glob_le _ a y h1)
  rw [hlat, ← hsm]
  exact h2

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalContragredientMonomial
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.WeakTheRep

theorem eq_of_mono0_charPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x y : WD h)
    (hx : x.mono0) (hy : y.mono0) (hc : ∀ g, x.charPol g = y.charPol g) : x = y := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hx hy
  obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n m a b
    (fun σ => by rw [← WD.charPol_mk, ← WD.charPol_mk]; exact hc σ)
  exact WD.sound ⟨e, he, fun v => by rw [hx, hy]; simp⟩

theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') {K : Subgroup G}
    (h : GlobalTheory.PRep.fixed ρ K ≠ ⊥) : GlobalTheory.PRep.fixed ρ' K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e v, ?_, fun h0 => hv0 ?_⟩
  · refine GlobalTheory.ContraRefl.mem_fix.2 fun g hg => ?_
    have h1 := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
    simp only [LinearMap.comp_apply] at h1
    rw [GlobalTheory.ContraRefl.mem_fix.1 hv g hg] at h1
    exact h1.symm
  · exact e.toLinearEquiv.injective (h0.trans (map_zero e.toLinearEquiv).symm)

end GlobalTheory.WeakTheRep

end
end

