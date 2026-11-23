module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0191
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSplitUnitVectorOrthComplement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

private theorem hform_eq_star_dotProduct (I : AutInst) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y = star x ⬝ᵥ (I.J *ᵥ y) := by
  change (∑ i, ∑ j, star (x i) * I.J i j * y j) = _
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem IsPerp.exists_split {I : AutInst} {D : Sib I} {s : Bool} {x : Fin I.n → I.E}
    {A : Matrix (Fin I.n) (Fin D.n) I.E} {xf : I.Gf} (h : IsPerp D s x A xf) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I (1, xf)) : ∃ a : 𝓞 I.E, ∃ w ∈ D.L, y = a • x + A *ᵥ w := by
  obtain ⟨hn, hβ, hxA, hAJ, hx, hL⟩ := h
  have hJ : I.Jᴴ = I.J := by
    rw [← (show Formalism.UG.cT (starRingEnd I.E) I.J = I.Jᴴ by ext i j; rfl)]
    exact I.J_herm
  have hsq : sgn I.E s * sgn I.E s = 1 := by cases s <;> simp [sgn]
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    intro h0
    rw [hβ] at h0
    rw [h0, zero_mul] at hsq
    exact zero_ne_one hsq
  obtain ⟨u, A', -, -, -, -, hres, -⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ

  have hdec : y = (u ⬝ᵥ y) • x + A *ᵥ (A' *ᵥ y) := by
    have h1 : (vecMulVec x u + A * A') *ᵥ y = y := by rw [hres, one_mulVec]
    rw [add_mulVec, ← mulVec_mulVec] at h1
    refine h1.symm.trans ?_
    congr 1
    ext i
    simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

  have hpair : ∀ (c : I.E) (w : Fin D.n → I.E), y = c • x + A *ᵥ w →
      star x ⬝ᵥ (I.J *ᵥ y) = c * sgn I.E s := by
    intro c w e
    rw [e, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hβ, mulVec_mulVec,
      dotProduct_mulVec, hxA, zero_dotProduct, add_zero]
  have hcoef : u ⬝ᵥ y = sgn I.E s * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
    rw [hform_eq_star_dotProduct, hpair _ _ hdec]
    linear_combination (-(u ⬝ᵥ y)) * hsq
  have hint : Formalism.UG.hform (starRingEnd I.E) I.J x y ∈ (algebraMap (𝓞 I.E) I.E).range :=
    (((GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.2.2.1 y).mp hy) x hx
  have hsgn : sgn I.E s ∈ (algebraMap (𝓞 I.E) I.E).range := by
    cases s
    · exact ⟨-1, by simp [sgn]⟩
    · exact ⟨1, by simp [sgn]⟩
  obtain ⟨a, ha⟩ := Subring.mul_mem _ hsgn hint
  have hca : (u ⬝ᵥ y) • x = a • x := by rw [hcoef, ← ha, algebraMap_smul]
  refine ⟨a, A' *ᵥ y, (hL _).mpr ?_, ?_⟩
  · have e : A *ᵥ (A' *ᵥ y) = y - a • x := by
      rw [← hca]
      exact eq_sub_of_add_eq' hdec.symm
    rw [e]
    exact Submodule.sub_mem _ hy (Submodule.smul_mem _ a hx)
  · rw [← hca]
    exact hdec

theorem afVec_mulVec_eq_afMat_mulVec (I : AutInst) {m k : ℕ} (A : Matrix (Fin m) (Fin k) I.E) (w : Fin k → I.E) :
    afVec I (A *ᵥ w) = afMat I A *ᵥ afVec I w := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [afVec, afMat, mulVec, dotProduct, map_sum]

private theorem mem_lf_iff_mem_latS (I : AutInst) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    v ∈ I.Lf ↔ v ∈ Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
  show v ∈ lamAf (F := I.F) I.L ↔ v ∈ Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L
  unfold lamAf Formalism.UG.latS
  constructor
  · refine fun hv => Submodule.span_mono ?_ hv
    rintro _ ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · refine fun hv => Submodule.span_mono ?_ hv
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem adelicLattice_split : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ z : Fin I.n → I.E ⊗[I.F] Af I.F, I.fmat xf⁻¹ *ᵥ z ∈ I.Lf ↔ ∃ a ∈ IntAf I.F I.E, ∃ w ∈ D.inst.Lf, z = a • afVec I x + afMat I A *ᵥ w := by
  intro I D s x A xf h z
  have hmem : ∀ y : Fin I.n → I.E, y ∈ lamX I (1, xf) → I.fmat xf⁻¹ *ᵥ afVec I y ∈ I.Lf :=
    fun y hy => ((GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).1 y).mp hy
  obtain ⟨-, -, -, -, hx, hL⟩ := id h
  constructor
  · intro hz
    have hspan := Formalism.UG.P.csSpan_back Formalism.UG.P.integral_adele_approximation_holds I.L
      (Module.Finite.iff_fg.mpr I.L_fg) I.L_span (xf : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) z
      ((mem_lf_iff_mem_latS I _).mp hz)
    clear hz
    induction hspan using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨y, hy, rfl⟩ := hv
      have hy' : y ∈ lamX I (1, xf) := by
        rw [GlobalTheory.PointLattice.lamX_eq_globLat]
        exact hy
      obtain ⟨a0, w0, hw0, e⟩ := IsPerp.exists_split h hy'
      refine ⟨Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a0), Formalism.UG.CS.incl_int a0,
        afVec I w0, Submodule.subset_span ⟨⟨w0, hw0⟩, rfl⟩, ?_⟩
      rw [← afVec_mulVec_eq_afMat_mulVec]
      funext i
      simp [afVec, e, Algebra.smul_def, map_add (f := _), map_mul]
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add v1 v2 _ _ h1 h2 =>
      obtain ⟨a1, ha1, w1, hw1, rfl⟩ := h1
      obtain ⟨a2, ha2, w2, hw2, rfl⟩ := h2
      refine ⟨a1 + a2, add_mem ha1 ha2, w1 + w2, add_mem hw1 hw2, ?_⟩
      rw [add_smul, mulVec_add]
      abel
    | smul c v _ h1 =>
      obtain ⟨a, ha, w, hw, rfl⟩ := h1
      refine ⟨(c : I.E ⊗[I.F] Af I.F) * a, mul_mem c.2 ha, (c : I.E ⊗[I.F] Af I.F) • w,
        Submodule.smul_mem _ c hw, ?_⟩
      show (c : I.E ⊗[I.F] Af I.F) • (a • afVec I x + afMat I A *ᵥ w) = _
      rw [smul_add, mul_smul, mulVec_smul]
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [mulVec_add, mulVec_smul]
    refine add_mem (Submodule.smul_mem I.Lf ⟨a, ha⟩ (hmem x hx)) ?_
    have hw' : w ∈ Submodule.span (IntAf I.F I.E)
        (Set.range fun y : D.L => afVec I (y : Fin D.n → I.E)) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hv
      show I.fmat xf⁻¹ *ᵥ (afMat I A *ᵥ afVec I y) ∈ I.Lf
      rw [← afVec_mulVec_eq_afMat_mulVec]
      exact hmem _ ((hL y).mp hy)
    | zero => simp
    | add v1 v2 _ _ h1 h2 =>
      rw [mulVec_add, mulVec_add]
      exact add_mem h1 h2
    | smul c v _ h1 =>
      show I.fmat xf⁻¹ *ᵥ (afMat I A *ᵥ ((c : I.E ⊗[I.F] Af I.F) • v)) ∈ I.Lf
      rw [mulVec_smul, mulVec_smul]
      exact Submodule.smul_mem I.Lf c h1

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutBallCount
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.AutBall

theorem pow_bound (s t R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (ht : 0 < t) (ht1 : t ≤ 1 / 2) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / (t * t)) ^ (2 * (m * f)) ≤
      (3 * s / t ^ 2) ^ (2 * (m * f)) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hE : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR hf'.le)
  have htt : 0 < t * t := mul_pos ht ht
  have h1 : 1 ≤ s * Real.exp (R / f) / (t * t) := by
    rw [le_div_iff₀ htt]; nlinarith
  have h2 : 1 + 2 * s * Real.exp (R / f) / (t * t) ≤ 3 * s / t ^ 2 * Real.exp (R / f) := by
    have e1 : 2 * s * Real.exp (R / f) / (t * t) = 2 * (s * Real.exp (R / f) / (t * t)) := by ring
    have e2 : 3 * s / t ^ 2 * Real.exp (R / f) = 3 * (s * Real.exp (R / f) / (t * t)) := by ring
    rw [e1, e2]; linarith
  have h3 : Real.exp (2 * (m : ℝ) * R) = Real.exp (R / f) ^ (2 * (m * f)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [h3, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 _

theorem autBallCount : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.AutBallCount := by
  intro I hn x r hr
  obtain ⟨hfin, hle⟩ := GlobalTheory.RationalCount.count_le I x x r hn hr
  have hsub : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.ballSet I x r ⊆
      {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * x).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * x).1 v)) ≤ r v} := by
    rintro a ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun v => le_trans ?_ (h3 v)⟩
    obtain ⟨h0, -, -, h4, -⟩ :=
      (GlobalTheory.Count.Cartan.cartan_distances I.n (I.ε v)).2.1 ((x⁻¹ * a * x).1 v) ((x⁻¹ * a * x).1 v) hn
    have h5 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    exact (le_mul_of_one_le_left h0 h5).trans h4
  refine ⟨hfin.subset hsub, ?_⟩
  have hc := Set.ncard_le_ncard hsub hfin
  have hf : 0 < I.f := Module.finrank_pos (R := ℚ) (M := I.F)
  have hs : 1 ≤ Real.sqrt (I.n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hb := pow_bound (Real.sqrt (I.n : ℝ)) (tau1 I x) (∑ v, r v) (I.n ^ 2) I.f hs
    (GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x) (min_le_left _ _) (Finset.sum_nonneg fun v _ => hr v) hf
  refine (Nat.cast_le.mpr hc).trans (hle.trans (hb.trans (le_of_eq ?_)))
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA
  push_cast
  rfl

end GlobalTheory.AutBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSide
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.KernelRe

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det := ((uHGroup _ _ hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r := ((uHGroup _ _ hpk_unit).2.2 a ha).2

def lmulEquiv (a : Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := lmulM a x
  invFun x := lmulM a⁻¹ x
  left_inv x := by
    show (a⁻¹ * (a * Matrix.of x) : Mat k r) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
  right_inv x := by
    show (a * (a⁻¹ * Matrix.of x) : Mat k r) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
  measurable_toFun := Continuous.measurable (α := Mt k r) (γ := Mt k r)
    (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  measurable_invFun := Continuous.measurable (α := Mt k r) (γ := Mt k r)
    (continuous_const.matrix_mul (continuous_id (X := Mat k r)))

theorem rconv_eq_translate {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    (μG : Measure (Mt k r)) (e : Mat k r → ℂ) (W : Mat k r → Wp) (hμ : IsHaarOn (GG k r) μG)
    {y : Mat k r} (hy : y ∈ GG k r) :
    rconv μG e W y = ∫ g, e (y⁻¹ * Matrix.of g) • W (Matrix.of g) ∂μG := by
  have hyu : IsUnit y⁻¹.det := GG_unit (GG_inv hy)
  have hmap : μG.map (lmulM y⁻¹) = μG := hμ.2.2.2 _ (GG_inv hy)
  have hme : MeasurableEmbedding (lmulM (k := k) (r := r) y⁻¹) :=
    (lmulEquiv y⁻¹ hyu).measurableEmbedding
  unfold rconv
  conv_lhs => rw [← hmap]
  rw [hme.integral_map]
  congr 1; funext g
  show e (Matrix.of (lmulM y⁻¹ g)) • W (y * Matrix.of (lmulM y⁻¹ g)) = _
  show e (y⁻¹ * Matrix.of g) • W (y * (y⁻¹ * Matrix.of g)) = _
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GG_unit hy), Matrix.one_mul]

theorem kernel_rconv : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g))) ν ∧ rconv μG (eFun μG σ w) W y = (d : ℂ) • ∫ g, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) ∂ν := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν W hWG hWν hW hL2 y hy
  obtain ⟨hz, hT, hπ, hμS, _⟩ := hSide
  have hcl := _root_.GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hun := (_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1 hμS
  have hμG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hWeil := _root_.GlobalTheory.SgInf.weil_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hμG hμS hun hν
  have hFint : Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG :=
    _root_.GlobalTheory.SgInf.AbsConv.integrable_coef_smul k r σ w a μG d z c π μS hStd ⟨hz, hT, hπ, hμS, inferInstance⟩ ν hν W hWG hWν hW hL2 y hy
  obtain ⟨hI, hEq⟩ := hWeil.2.2.2.1 Wp _ hFint
  have hae : ∀ᵐ x ∂ν, (∫ s, star (coef σ w w (y⁻¹ * Matrix.of (lmulM (Matrix.of s) x))) •
      W (Matrix.of (lmulM (Matrix.of s) x)) ∂μS) =
      be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
    have h0 : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
      rw [ae_iff]; simpa using hWeil.2.1
    filter_upwards [h0] with x hx
    exact _root_.GlobalTheory.SgInf.inner_integral_eq_be k r σ w a μG d z c π μS hStd ⟨hz, hT, hπ, hμS, inferInstance⟩ W hW y hy x hx
  have hfd : fdegH μG σ w = d :=
    GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality k r σ μG d w hStd.2.2.2.2.2.1 (by
      intro h0; have := hStd.2.2.2.1; rw [h0, norm_zero] at this; exact zero_ne_one this)
  refine ⟨hI.congr hae, ?_⟩
  rw [rconv_eq_translate μG _ W hμG hy]
  have hfun : (fun g : Mt k r => eFun μG σ w (y⁻¹ * Matrix.of g) • W (Matrix.of g)) =
      fun g => (d : ℂ) • (star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) := by
    funext g; simp only [eFun, hfd, coef, smul_smul]
  rw [hfun, integral_smul, hEq, integral_congr_ae hae]

end GlobalTheory.SgInf.KernelRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelMatrixSkewCoordinatesRationalAut
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovSkew

theorem herm_esI {k r : ℕ} (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  have ha := a.2
  have ht : WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
    have h1 : (esI k r a).val < r ∨ r + k < (esI k r a).val := Or.inr (by simp only [esI]; omega)
    apply Fin.ext; unfold WeylGroupFacts.tau; dsimp only; rw [if_pos h1]; simp only [esI, eI]; omega
  have hs : WeylGroupFacts.sgn k r (esI k r a) = 1 := if_neg (by simp only [esI]; omega)
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_one_dotProduct]
  simp only [mulVec, dotProduct, WeylGroupFacts.hpk_row, ht, hs]
  simp

theorem sum_eI_apply {k r : ℕ} (c : Fin r → ℂ) (a : Fin r) :
    (∑ b, c b • bvec (eI k r b)) (eI k r a) = c a := by
  simp [Finset.sum_apply, Rad.bvec_apply, Rad.eI_inj]

theorem coords_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → q.1 = 0 → q.2.1 = 0 → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') ∧ (∀ p : {p : UT r // N.j ≤ p.1.1.val}, q.2.2.1 p = ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ) * σ (H.B (s (N.ist p.1.1.2)) (N.ist p.1.1.1))) ∧ ∀ a : {a : Fin r // N.j ≤ a.val}, q.2.2.2 a = ρ ^ (2 * (r - a.1.val)) * (σ (H.B (s (N.ist a.1)) (N.ist a.1))).im := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq hq1 hq2
  obtain ⟨hr, -, -, -, -, he, hi, -⟩ := hF
  have he1 : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) := fun a => (he a).1
  have ht : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (pow_pos hρ n).ne'
  set S : Matrix (Fin r) (Fin r) ℂ := skewM (Swap.extS r N.j q.2.2).1 (Swap.extS r N.j q.2.2).2 with hSdef
  have hM : crd k r N.j β q = pEl k r 0 S := by
    rw [RefCovTop.crd_of_zero β q hq1, Swap.pTop_eq, pOf, hq2, map_zero]
  have hS0 : ∀ a b : Fin r, ¬ N.j ≤ a.val → S a b = 0 := fun a b ha => Swap.skew_ext_zero q.2.2 a b ha
  have hcol : ∀ b : Fin r, pEl k r 0 S *ᵥ bvec (esI k r b) = bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a) := by
    intro b
    rw [((Rad.radical k r).1 0 S).2.2.1 b]
    simp [herm]
  have hsb : ∀ b : Fin r, N.j ≤ b.val → Φ (s (N.ist b)) =
      (((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) • (bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a)) := by
    intro b hb; rw [← hq, hM, hi b hb, mulVec_smul, hcol]
  have hB : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → σ (H.B (s (N.ist b)) (N.ist a)) =
      (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) := by
    intro a b ha hb
    rw [← hr.2.2.1, hsb b hb, hi a ha, RealMat.herm_smul_right, herm_esI, Pi.smul_apply, Pi.add_apply, sum_eI_apply,
      Rad.bvec_apply, if_neg (Rad.eI_ne_esI a b), zero_add, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  refine ⟨fun b hb => ?_, fun p => ?_, fun a => ?_⟩
  · have hΦy : Φ (s (N.ist b) - N.ist b) = ∑ a, ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) • bvec (eI k r a) := by
      rw [RealMat.phi_sub hr, hsb b hb, hi b hb, smul_add, add_sub_cancel_left, Finset.smul_sum]
      simp_rw [smul_smul]
    have hproj : NFGeom.proj N (s (N.ist b) - N.ist b) = s (N.ist b) - N.ist b := by
      apply RealMat.phi_inj hr
      rw [NFGeom.proj_apply, RealMat.phi_sum hr, hΦy, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with ha
      · rw [hr.2.1, he1, ← hr.2.2.1, hΦy, hi a ha, RealMat.herm_smul_right, herm_esI, sum_eI_apply, smul_smul]
        congr 1
        rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv, mul_comm, ← mul_assoc,
          mul_inv_cancel₀ (ht _), one_mul]
      · rw [hS0 a b ha, mul_zero, zero_smul]
    rw [← hproj]; exact NFGeom.proj_mem N _
  · obtain ⟨⟨⟨a, b⟩, hab⟩, ha⟩ := p
    have hab' : a < b := hab
    have ha' : N.j ≤ a.val := ha
    have hb : N.j ≤ b.val := le_trans ha' (le_of_lt hab')
    simp only
    rw [hB a b ha' hb]
    have hSab : S a b = q.2.2.1 ⟨⟨(a, b), hab⟩, ha⟩ := by
      simp [hSdef, skewM, hab', Swap.extS, Swap.extZ, ha']
    rw [hSab, pow_add, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv]
    have h1 := ht (r - a.val)
    have h2 := ht (r - b.val)
    field_simp
  · obtain ⟨a, ha⟩ := a
    simp only
    rw [hB a a ha ha]
    have hSaa : S a a = ((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I := by
      simp [hSdef, skewM, Swap.extS, Swap.extZ, ha]
    rw [hSaa]
    have e : ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * (((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I))) =
        (((ρ ^ (r - a.val))⁻¹ * ((ρ ^ (r - a.val))⁻¹ * q.2.2.2 ⟨a, ha⟩) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.mul_I_im, Complex.ofReal_re, two_mul, pow_add]
    have h1 : ρ ^ (r - a.val) ≠ 0 := (pow_pos hρ _).ne'
    field_simp

end GlobalTheory.DegVol.RefCovSkew
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangularStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biorthogonal_block_frames_triangular : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ), Biorth r m T T' → Biorth r m U U' → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) → (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b, U' b * Y * U (b + c + 1) = (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  first | exact @GlobalTheory.RadCov.blockFrames_triangular | exact GlobalTheory.RadCov.blockFrames_triangular | (intros; apply GlobalTheory.RadCov.blockFrames_triangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangularStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnBlocksSpanFlag_of_block_triangular : ∀ (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ k i, i < k → p k i = 0 ∧ q k i = 0) → (∀ i, A i = ∑ k, B k * p k i) → (∀ i, B i = ∑ k, A k * q k i) → SpansFlag A W → SpansFlag B W := by
  first | exact @GlobalTheory.LeviIso.spansFlag_of_triangular | exact GlobalTheory.LeviIso.spansFlag_of_triangular | (intros; apply GlobalTheory.LeviIso.spansFlag_of_triangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexFlagAtEmbeddingFrameFinrankAndLowersStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFlagAtEmbeddingFrame_finrank_and_lowers : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), IsUnit P → (∀ b, Module.finrank ℂ (locFlag φ P F b) = Formalism.HN.rkK (F b)) ∧ ∀ c, ∀ T ∈ lowers F c, P⁻¹ * T.map φ * P ∈ lowers (locFlag φ P F) c := by
  first | exact @GlobalTheory.RadCov.finrank_locFlag_and_lowers | exact GlobalTheory.RadCov.finrank_locFlag_and_lowers | (intros; apply GlobalTheory.RadCov.finrank_locFlag_and_lowers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistance
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.Dec.BoundedDistance

theorem bound_le (s la R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (hla : 0 < la) (hla1 : la ≤ 1) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * (m * f)) ≤ (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have he : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR (Nat.cast_nonneg _))

  have hone : 1 ≤ s * Real.exp (R / f) / la := by
    rw [le_div_iff₀ hla]
    nlinarith
  have hbase0 : 0 ≤ 1 + 2 * s * Real.exp (R / f) / la := by positivity
  have hbase : 1 + 2 * s * Real.exp (R / f) / la ≤ 3 * s / la * Real.exp (R / f) := by
    have h3 : 3 * s / la * Real.exp (R / f) =
        s * Real.exp (R / f) / la + 2 * s * Real.exp (R / f) / la := by ring
    linarith
  have hk : 2 * (m * f) = 2 * m * f := by ring
  rw [hk]
  calc (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * m * f)
      ≤ (3 * s / la * Real.exp (R / f)) ^ (2 * m * f) := pow_le_pow_left₀ hbase0 hbase _
    _ = (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

theorem countRat : CountRat := by
  intro I x y r hn hr
  obtain ⟨hfin, hcard⟩ := GlobalTheory.RationalCount.count_le I x y r hn hr
  have hx := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x
  have hy := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y

  have hx2 : tau1 I x ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hy2 : tau1 I y ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hs : (1 : ℝ) ≤ Real.sqrt I.n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hf : 0 < I.f := Module.finrank_pos
  have hla1 : tau1 I x * tau1 I y ≤ 1 := by nlinarith
  have key := bound_le (Real.sqrt I.n) (tau1 I x * tau1 I y) (∑ v, r v) (I.n ^ 2) I.f hs
    (mul_pos hx hy) hla1 (Finset.sum_nonneg fun v _ => hr v) hf
  push_cast at key
  exact ⟨hfin, hcard.trans key⟩

end GlobalTheory.Dec.BoundedDistance
end

