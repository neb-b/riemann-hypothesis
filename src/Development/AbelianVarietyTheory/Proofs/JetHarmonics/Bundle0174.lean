module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0122
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelModuleFormEqIntegralOfCompactCoeff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0173
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PictureMemStableBounded
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlaneWaveBoundOfCompactPositivity
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftBoundOfCompactPositivity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseRepCapelliEigenDual
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal Matrix.Norms.Elementwise in
theorem _root_.GlobalTheory.CoefZero.continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {m : ℕ∞}
    {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (h : _root_.Formalism.FourierDecayAlt.B.CkOn m (_root_.Formalism.FourierDecayAlt.B.GV k r) f) : ContinuousOn f (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfeq⟩ := h g₀ hg₀
  have hc : ContinuousOn f' U := hf'.continuousOn
  have hcont : ContinuousAt f' g₀ := hc.continuousAt (hU.mem_nhds hgU)
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (hfeq g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (_root_.Formalism.FourierDecayAlt.B.GV k r) (hU.mem_nhds hgU)] with g hg
  exact hfeq g hg.2 hg.1

end GlobalTheory.CoefZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionOfBesselFunctionZero
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bigCellExpansion_of_besselFunction_zero : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ), 0 ≤ b → (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) → (∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ := by
  intro P Wp Wq _ _ _ _ _ _ p f b C₃ a₁ hb hm hV
  have hV' : ∀ c : Fin (P.r + 1) → ℂ, p.V f (TBB.bigPt P.r c) = 0 := by
    intro c
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · exact hV c hc.1 hc.2
    · exact Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ hc
  refine ⟨ℤ, inferInstance, fun _ => f, 0, fun _ => 0, fun _ => 0, 0, (P.r + 1) * a₁, 0, rfl, le_rfl,
    fun _ _ => le_rfl, fun _ _ => le_rfl, rfl, rfl, ?_, le_rfl, ?_, fun _ => le_rfl, fun _ => hm⟩
  · intro μ _
    refine ⟨0, ?_, ?_, ?_⟩
    · funext c
      simp [hV' c]
    · simp
    · simp
  · rw [zero_pow (Nat.succ_ne_zero _)]
    exact Real.rpow_nonneg hb _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionSmul
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem familyDerivativeExpansion_smul (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (t : ℂ)
    (h : Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁) :
    Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p (fun g => t • f g) b C₃ a₁ := by
  obtain ⟨Par, inst, fam, lam, n₁, ninf, c0, q0, Gam, hf, hGam, h1, h2, h3, h4, hstep, hrange, hGb,
    hnorm, hmeas⟩ := h
  refine ⟨Par, inst, fun μ g => t • fam μ g, lam, n₁, ninf, c0, q0, Gam, ?_, hGam, h1, h2, h3, h4, ?_,
    hrange, hGb, ?_, ?_⟩
  · subst hf; rfl
  · intro μ hμ
    obtain ⟨a, hE, hS, hsupp⟩ := hstep μ hμ
    refine ⟨a, ?_, hS, hsupp⟩
    funext c
    have hc := congrFun hE c
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply] at hc ⊢
    rw [Formalism.FourierDecayAlt.P.CutBP.V_csmul p (fam μ) t, smul_comm, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Formalism.FourierDecayAlt.P.CutBP.V_csmul p (fam (μ + ν)) t, smul_comm]
  · intro μ
    rw [Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p (fam μ) t, Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p f t]
    gcongr
    exact hnorm μ
  · intro μ
    have e : (fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => t • fam μ g) (P.r + 1) [] (TBB.bigPt P.r c))) =
        fun c => ENNReal.ofReal (‖t‖ ^ 2) *
          ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fam μ) (P.r + 1) [] (TBB.bigPt P.r c)) := by
      funext c
      rw [Formalism.FourierDecayAlt.P.CutBP.Ew_csmul p (fam μ) t, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [e]
    exact (hmeas μ).const_mul _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenGapCoef
section
open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory

theorem eigDec_of_isKFinCoefT : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro H k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := H.1.2.2.1
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.isCoef_ckOn_inCC H k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDS hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.T.capelli_eigenvalue_kFinite_discreteSeries_coeff hsm H.2.2.1 k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.T.centredCapelliOperator_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsCoefContinuousOn
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupMeas

theorem isDS_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDS ε μ) (v : R.H) : ContinuousOn (fun g => R.σ g v) (GG k r) := by
  obtain ⟨-, P, hP, -, -, ⟨-, -, hc⟩, -⟩ := h
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have := (hc v).comp h3.continuousOn hmaps
  simpa only [Function.comp_def, e] using this

theorem isCoef_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {l : R.H → Wp} {l' : R.H → Wq} {F : Mx k r → (Wq →L[ℂ] Wp)} {s : ℂ}
    (h : R.IsDS ε μ) (hF : IsCoef R l l' F s) : ContinuousOn F (GG k r) := by
  obtain ⟨m, x, y, X, -, hF, -⟩ := hF
  refine ContinuousOn.congr ?_ hF
  exact continuousOn_finsetSum _ fun i _ =>
    (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (isDS_continuousOn h (y i))).smul continuousOn_const

end GlobalTheory.SupMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormDiagonalBigCellImEqZero
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelFormsReal

theorem isLocPt_ofFn {j : ℕ} (c : Fin j → ℂ) (hc : ∀ l, c l ≠ 0) :
    D.IsLocPt (List.ofFn fun l => ((1 : ℕ), c l)) j := by
  refine ⟨fun b hb => ?_, ?_⟩
  · simp only [List.mem_ofFn] at hb
    obtain ⟨l, rfl⟩ := hb
    exact ⟨by simp, hc l⟩
  · simp [D.ptSize, List.map_ofFn, Function.comp_def]

theorem ofFn_snoc {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    (List.ofFn fun l => ((1 : ℕ), (Fin.snoc c t : Fin (j + 1) → ℂ) l))
      = (List.ofFn fun l => ((1 : ℕ), c l)) ++ [(1, t)] := by
  rw [List.ofFn_succ']
  simp

theorem integral_im_eq_zero {f : ℂ → ℂ} (hf : ∀ t, t ≠ 0 → (f t).im = 0) :
    (∫ t : ℂ, f t).im = 0 := by
  have h : f =ᵐ[volume] fun t => (((f t).re : ℝ) : ℂ) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with t ht
    exact Complex.ext (by simp) (by simp [hf t ht])
  rw [integral_congr_ae h, integral_complex_ofReal]
  simp

theorem levelZero_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w hD hH hw
  have key : ∀ (n j : ℕ), j + n = P.r + 1 → ∀ c : Fin j → ℂ, (∀ l, c l ≠ 0) →
      (p.RR H j w (List.ofFn fun l => ((1 : ℕ), c l)) (List.ofFn fun l => ((1 : ℕ), c l))).im = 0 := by
    intro n
    induction n with
    | zero =>
      intro j hj c hc
      obtain rfl : j = P.r + 1 := hj
      exact (_root_.GlobalTheory.TopDensity.topDensity_eq Wp Wq P p H w c hc).2.1
    | succ n ih =>
      intro j hj c hc
      rw [(_root_.GlobalTheory.LevelIntegralStep.levelForm_eq_integral hP Wp Wq P p Cb H w j _ hD hH hw (by omega) (isLocPt_ofFn c hc)).2]
      refine integral_im_eq_zero fun t ht => ?_
      have h := ih (j + 1) (by omega) (Fin.snoc c t) (fun l => by
        refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using ht
        · simpa using hc i)
      rw [ofFn_snoc] at h
      simp [Complex.mul_im, h]
  simpa using key (P.r + 1) 0 (by omega) (fun l => l.elim0) (fun l => l.elim0)

end GlobalTheory.LevelFormsReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormLeNormCOfEigenSum
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory


open scoped Matrix.Norms.Elementwise in
theorem ckOn_group_finset_sum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type}
    (s : Finset ι) (Fi : ι → B.Mat k r → E) (h : ∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, Fi i g) := by
  intro g₀ hg₀
  choose U f hU hgU hf hff using fun i => h i g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun g => ∑ i ∈ s, f i g, isOpen_biInter_finset fun i _ => hU i,
    Set.mem_iInter₂.2 fun i _ => hgU i, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi => (hf i).mono fun g hg => Set.mem_iInter₂.1 hg i hi
  · intro g hg hG
    exact Finset.sum_congr rfl fun i hi => hff i g (Set.mem_iInter₂.1 hg i hi) hG

theorem levelZero_form_le_normC_of_eigen_sum : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (d : ℕ) (A : ℝ) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.AB P.k P.r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * P.r + P.k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV P.k P.r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV P.k P.r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR F 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re := by
  intro hXi Wp Wq _ _ _ _ _ _ P p lam d A nn F Y N hA hF hnn w hw _
  have hsm : B.CkOn ⊤ (B.GV P.k P.r) F := by
    obtain ⟨N₀, Fi, ν, -, hc, -, hsum⟩ := hF
    exact (ckOn_inCC_congr_on_group P.k P.r _ A (fun g => ∑ i, Fi i g) F
      (fun g hg => (hsum g hg).symm)).1 (ckOn_group_finset_sum Finset.univ Fi fun i => (hc i).1)
  have hs : M.sgn P p.l0 = 1 ∨ M.sgn P p.l0 = -1 := by
    unfold M.sgn
    exact neg_one_pow_eq_or ℂ _
  unfold KB.Pl.RR TBB.normC
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw.1)]
  exact GlobalTheory.levelZero_energy_le_of_eigen_sum hXi P.k P.r Wp Wq p.T.base lam d A _ nn F hs hA hF hnn w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.N1AddEZLe
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SuppliedPieri

theorem n1_add_eZ_le {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : I.card = ∑ i : Fin n, (if i ∈ I then 1 else 0) := by
    rw [Finset.sum_boole]; simp
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, eZ]
  split_ifs <;> omega

theorem JF_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (g : B.Mat k r) :
    B.JF D 0 g = 0 := by
  simp [B.JF, Formalism.QuantumDeterminants.besselJ]

end GlobalTheory.SuppliedPieri
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveIsometryOfRadial
section
namespace GlobalTheory.PointwiseBound

noncomputable section

section Wave

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants

theorem uInv_eq_zero {Y Z : Type} [AddCommGroup Z] [Module ℂ Z] (s : ℂ) (g : Y) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → Y → Z) (e : Wd.Ix (Fin w.length)),
      (∀ a, x a g = 0) → KB.uInv s w x e g = 0
  | [], _, e, h => h e
  | l :: w, x, e, h => by
    have h0 := uInv_eq_zero s g w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ) (fun a => h _)
    have h1 := uInv_eq_zero s g w (fun e' => x (Fin.cons 1 e')) (fun a => e a.succ) (fun a => h _)
    simp only [KB.uInv]
    by_cases h : e 0 = 0
    · simp only [if_pos h]
      exact h0
    · simp only [if_neg h, Pi.add_apply, Pi.smul_apply]
      rw [h0, h1, smul_zero, add_zero]

theorem waveG_cptCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, KB.CptCoef Bs (x e))
    (e : Wd.Ix (Fin w.length)) : KB.CptCoef Bs (KB.waveG Bs s w x e) := by
  obtain ⟨ε, hε, hn⟩ := PBL.nv_of_cv (Bs := Bs) (x := x) hx
  have hw := PBFV.waveG_nice Bs ε s w x hn e
  refine ⟨hw.1, ?_, ε, hε, hw.2.2⟩
  choose R hR using fun a => (hx a).2.1
  refine ⟨∑ a, |R a|, fun g hg hne => ?_⟩
  by_cases h0 : ∀ a, x a g = 0
  · exact absurd (by simp only [KB.waveG]; rw [uInv_eq_zero s g w x e h0, smul_zero]) hne
  · push Not at h0
    obtain ⟨a, ha⟩ := h0
    exact ((hR a g hg ha).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun a => |R a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))

theorem waveIsometry_of_radial (hRad : JC.RadialModuleForm) : KB.VIsoCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' hx hx'
  refine ⟨waveG_cptCoef _ s w x hx, ?_⟩
  obtain ⟨ε, hε, a, b, -⟩ := PBL.exists_norm_bound_three_families (Bs := p.T.bs j) (x := x) (y := x') (z := x) hx hx' hx
  exact GlobalTheory.WaveIsometry.isometry_of_bounded hRad hP Wp Wq P p j hj w hw s x x' ε hε a b
    (fun e => (hx e).2.1) (fun e => (hx' e).2.1) (fun e => (waveG_cptCoef _ s w x' hx' e).2.1)

end Wave

section Extension

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem extension_at_zero (hXi : B.XiExists) (hP : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) : TBB.HeadContinuityAtZero p nn F Y N := by
  intro j hj h hh w hw hN
  obtain ⟨φ, hφc, hφi, hφ, -⟩ := PBO.pStd_cpt_of_parts hP (FormsFromXi.radHead hXi) head_top
    (FormsFromXi.form_const_one hXi) exists_zeta_normalized_haar Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  refine ⟨fun c => ((A / TBB.normC nn w : ℝ) : ℂ) * φ c, continuous_const.mul hφc, hφi.const_mul _, ?_⟩
  intro c hc
  simp only
  rw [hφ c hc]
  have hA : 0 ≤ A := Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.NP
  rw [hn]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      push_cast
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    push_cast
    ring

end Extension

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder

end

end GlobalTheory.PointwiseBound
end

