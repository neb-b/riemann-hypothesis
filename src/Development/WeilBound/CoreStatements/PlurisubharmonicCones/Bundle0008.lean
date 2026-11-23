module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
public import Development.WeilBound.CoreStatements.FlagImmersions.ArithmeticIntersectionDivisorSupport
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinear
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.AmpleGenericFibreOfCombination
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt.Ample

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem coneTangent {P : Ideal (MRing J)} {e : ℕ}
    {τ : (Fin e → ℂ) → (Σ k, J k) → ℂ} {y : Fin e → ℂ} (hτ : DifferentiableAt ℂ τ y)
    (hm : ∀ᶠ y' in 𝓝 y, τ y' ∈ mcPts P) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (τ y) (fderiv ℂ τ y w) := by
  intro f hf
  set F := MvPolynomial.map (Int.castRingHom ℂ) f
  have h0 : (fun y' => MvPolynomial.eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hm] with y' hy'
    exact hy'.2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => MvPolynomial.eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ : Fin 1 => f) y = 2 / Real.pi * levi f y (Pi.single 0 1) := by
  have hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have hne : (∅ : Finset (Fin 1)) ≠ {0} := by decide
  have key : (cxHessian f y 0 0).re = levi f y (Pi.single 0 1) := by
    simp only [cxHessian, levi]
    generalize fderiv ℝ (fderiv ℝ f) y = H
    generalize H (Pi.single 0 1) (Pi.single 0 1) + H (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1) = u
    simp
  have hm : mixedDisc (fun _ : Fin 1 => cxHessian f y) = cxHessian f y 0 0 := by
    unfold mixedDisc
    rw [hU, Finset.sum_pair hne]
    simp [Matrix.det_unique]
  unfold maDensity
  rw [hm, key]
  simp

theorem geomDeg_nonneg {P W : Ideal (MRing J)} {N : HermLine J} (hN : IsSemipositiveH P N) (hW : P ≤ W) :
    0 ≤ geomDeg W N 1 := by
  classical
  unfold geomDeg ptsIntegral
  split_ifs with hΨ
  · refine MeasureTheory.integral_nonneg fun y => finsum_nonneg fun w => finsum_nonneg fun _ => ?_
    unfold sheetDensity
    split_ifs with hg
    · have hev := hg.choose_spec.2
      set gm := hg.choose
      have hP : ∀ᶠ y' in 𝓝 y, gm y' ∈ mcPts P := hev.mono fun y' h => ⟨h.2.1.1, fun f hf => h.2.1.2 f (hW hf)⟩
      have hz := hP.self_of_nhds
      have han : AnalyticAt ℂ gm y :=
        GroundTheory.Heights₂.Heights.Inter.analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
      have hlog : ContDiffAt ℝ 2 (fun z => Real.log (N.h z)) (gm y) :=
        ((hN.1.contDiffAt (StokesStep.isOpen_multicone.mem_nhds hz.1)).of_le
          (WithTop.coe_le_coe.2 le_top)).log (N.pos _ hz.1).ne'
      have h1 := ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) han hlog
      have h2 := hN.2 _ hz _ (coneTangent han.differentiableAt hP (Pi.single 0 1))
      have h3 := maDensity_one ((fun z => Real.log (N.h z)) ∘ gm) y
      rw [h1] at h3
      rw [_root_.one_mul]
      exact le_of_le_of_eq (mul_nonneg (by positivity) h2) h3.symm
    · exact le_rfl
  · exact le_rfl

end LevelTowerAlt.Ample

theorem LevelTowerAlt.ample_generic_fibre_of_combination : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (N A : HermLine J) (a' : K → ℤ) (m p : ℕ), IsSemipositiveH P N → IsSmoothHerm A → (∀ k, 0 < a' k) → 1 ≤ m → 1 ≤ p → (m : ℤ) • A.a = N.a + (p : ℤ) • a' → AmpleOnGenericFibre P A := by
  intro hI II hII K _ J _ P N A a' m p hN hA ha' hm hp heq W d hd hW hPW
  classical
  have hK : Nonempty K := hW.1
  have hDG := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system ⟨II, hII⟩)
  have hF := GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K J
  have hPos := GroundTheory.Heights₂.Heights.Targets.Positivity.full ℚ J _ hF
  let fs : (K → ℤ) → HermLine J := fun b => HermLine.ofMetrics (fun k => fsMetric (J k)) b
  have hfs : ∀ b, IsSmoothHerm (fs b) := fun b => GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs b
  have hfsn : ∀ b : K → ℤ, (∀ k, 0 ≤ b k) → ∀ W', IsArithVar W' 2 → 0 ≤ geomDeg W' (fs b) 1 := by
    intro b hb W' hW'
    have h1 := hDG K J W' 1 (fun _ => fs b) hW' fun _ => hfs b
    have h2 := (hPos _ 1 (GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW')).1
      (fun _ => b) fun _ k => hb k
    show 0 ≤ ptsIntegral W' (pot fun _ : Fin 1 => fs b) (fun _ => 1)
    rw [h1]
    exact_mod_cast h2
  let ℓ : Fin 3 → HermLine J := ![N, fs ((p : ℤ) • a' - 1), fs 1]
  have hℓ : ∀ j, IsSmoothHerm (ℓ j) := fun j => by
    fin_cases j
    · exact hN.1
    · exact hfs _
    · exact hfs _
  have hnef : ∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (ℓ j) 1 := fun j W' h1 h2 => by
    fin_cases j
    · exact LevelTowerAlt.Ample.geomDeg_nonneg hN (hPW.trans h2)
    · refine hfsn _ (fun k => ?_) W' h1
      have h3 := ha' k
      have h4 : (1 : ℤ) ≤ p := by exact_mod_cast hp
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      nlinarith
    · exact hfsn _ (fun _ => zero_le_one) W' h1
  have e1 := (_root_.GlobalTheory.CompanionTheory.Ar.Top.geo_multilin II hII K J W d (Fin 3) ℓ (fun _ _ => 1) hW hℓ).1
  have e2 := (_root_.GlobalTheory.CompanionTheory.Ar.Top.geo_multilin II hII K J W d Unit (fun _ => A) (fun _ _ => (m : ℤ)) hW fun _ => hA).1
  have e3 := (_root_.GlobalTheory.CompanionTheory.Ar.Top.geo_multilin II hII K J W d Unit (fun _ => A) (fun _ _ => (m : ℤ)) hW fun _ => hA).2
    (fun _ => Top.combLine ℓ fun _ => 1) (fun _ => Top.combLine (fun _ : Unit => A) fun _ => (m : ℤ)) (Equiv.refl _)
    (fun _ => (_root_.GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj K J _ ℓ _).1 hℓ) (fun _ => (_root_.GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj K J _ _ _).1 fun _ => hA) fun _ => by
      show ∑ _ : Unit, (m : ℤ) • A.a = ∑ j, (1 : ℤ) • (ℓ j).a
      rw [Fin.sum_univ_three]
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, heq]
      show _ = N.a + ((p : ℤ) • a' - 1) + 1
      abel
  rw [e1, e2] at e3
  have hpos : 0 < ∑ w : Fin d → Fin 3, (∏ k : Fin d, ((1 : ℤ) : ℝ)) *
      ptsIntegral W (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) := by
    simp only [Int.cast_one, Finset.prod_const_one, _root_.one_mul]
    refine Finset.sum_pos' (fun w _ => ?_) ⟨fun _ => 2, Finset.mem_univ _, ?_⟩
    · exact _root_.GlobalTheory.CompanionTheory.Ar.Top.kleiman_generic_fibre_integral hI.kleimanNefF (fun K _ J _ => (PB.Known.fieldNumbers ℚ K J).1) PB.Known.divSuppArith II hII K J W d (fun k => ℓ (w k)) hW
        (fun k => hℓ _) fun k => hnef _
    · have h1 := hDG K J W d (fun _ => fs 1) hW fun _ => hfs _
      have h2 := (hPos _ d (GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW)).2
      show 0 < ptsIntegral W (pot fun _ : Fin d => fs 1) (fun _ => 1)
      rw [h1]
      exact_mod_cast h2
  rw [← e3, Fintype.sum_unique] at hpos
  have hc : (0 : ℝ) ≤ ∏ k : Fin d, ((m : ℤ) : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  exact (pos_iff_pos_of_mul_pos hpos).1 (lt_of_le_of_ne hc fun h => by
    rw [← h, zero_mul] at hpos
    exact lt_irrefl _ hpos)
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtLogH
section
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi levi_comp levi_congr levi_add_smul levi_re_analytic)

namespace LevelTowerAlt

theorem levi_disc {ι : Type} [Fintype ι] {φ : (ι → ℂ) → ℝ} {δ : ℂ → ι → ℂ} {z w : ι → ℂ} (hδ : AnalyticAt ℂ δ 0)
    (hd : HasDerivAt δ w 0) (h0 : δ 0 = z) (hφ : ContDiffAt ℝ 2 φ z) :
    levi φ z w = levi (fun s : Fin 1 → ℂ => φ (δ (s 0))) 0 (fun _ => 1) := by
  subst h0
  have hτ : AnalyticAt ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 :=
    AnalyticAt.comp (g := δ) (f := fun s : Fin 1 → ℂ => s 0) hδ
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)
  have h := HasFDerivAt.comp (0 : Fin 1 → ℂ) (g := δ) (f := fun s : Fin 1 → ℂ => s 0) hd.hasFDerivAt
    (hasFDerivAt_apply 0 0)
  have h2 : fderiv ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 (fun _ => 1) = w := by
    rw [show fderiv ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 = _ from h.fderiv]
    simp
  have h3 := levi_comp (φ := φ) (τ := fun s : Fin 1 → ℂ => δ (s 0)) (z := 0) (fun _ => 1) hτ hφ
  rw [h2] at h3
  exact h3.symm

theorem levi_add_re {ι : Type} [Fintype ι] {f g : (ι → ℂ) → ℝ} {G : (ι → ℂ) → ℂ} {z : ι → ℂ}
    (hg : ContDiffAt ℝ 2 g z) (hG : AnalyticAt ℂ G z) (h : ∀ᶠ y in 𝓝 z, f y = g y + (G y).re) (w : ι → ℂ) :
    levi f z w = levi g z w := by
  have hR : AnalyticAt ℝ G z := hG.restrictScalars
  have hre : ContDiffAt ℝ 2 (fun y => (G y).re) z := Complex.reCLM.contDiff.contDiffAt.comp z hR.contDiffAt
  have h' : f =ᶠ[𝓝 z] fun y => g y + 1 * (G y).re := h.mono fun y hy => by simp only [hy, one_mul]
  rw [levi_congr h', levi_add_smul 1 hg hre, levi_re_analytic hG, mul_zero, add_zero]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (A : HermLine J) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) :
    Real.log (A.h (torusSmul c z)) = Real.log (A.h z) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have hp : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  change Real.log (A.h fun p => c p.1 * z p) = _
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hp k) (A.pos z hz).ne',
    Real.log_prod fun k _ => hp k, add_comm]
  simp only [Real.log_zpow]

theorem contDiffAt_log_h {A : HermLine J} (hA : IsSmoothHerm A) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) z :=
  ((ContDiffOn.contDiffAt hA (HermExtend.isOpen_blocksNe.mem_nhds hz)).log (A.pos z hz).ne').of_le
    (WithTop.coe_le_coe.2 le_top)

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGenerator
section
open AlgebraicGeometry CategoryTheory Matrix
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

namespace N1

section

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem mat_unique {b₀ : Fin r → V} (h₀ : LinearIndependent Ω b₀) {T T' : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, ∑ k', T k' k • b₀ k' = ∑ k', T' k' k • b₀ k') : T = T' := by
  ext k' k
  exact (Fintype.linearIndependent_iffₛ.1 h₀) (fun a => T a k) (fun a => T' a k) (h k) k'

theorem mat_comp {b₀ b b' : Fin r → V} {T A : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (h' : ∀ k, b' k = ∑ k', A k' k • b k') (k : Fin r) :
    b' k = ∑ k', (T * A) k' k • b₀ k' := by
  rw [h' k]
  simp only [h, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem exists_mat (R : Subring Ω) {b b' : Fin r → V} (h : ∀ k, b' k ∈ Submodule.span R (Set.range b)) :
    ∃ A : Matrix (Fin r) (Fin r) Ω, (∀ k, b' k = ∑ k', A k' k • b k') ∧ A.det ∈ R := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (h k)
  refine ⟨R.subtype.mapMatrix (Matrix.of fun k' k => c k k'), fun k => ?_, ?_⟩
  · rw [← hc k]; rfl
  · rw [← RingHom.map_det]; exact SetLike.coe_mem _

theorem det_ne_zero {b₀ b : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') : T.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hT⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine hv (funext (Fintype.linearIndependent_iff.1 hb v ?_))
  simp only [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [← Finset.sum_smul]
  have := congrFun hT k'
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
  rw [show ∑ i, v i * T k' i = 0 from by rw [← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _, zero_smul]

end

end N1

open N1

theorem determinant_lattice_generator : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ b : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω b₀ → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • b₀ k') → (detLat L b₀).IsGenAt p T.det := by
  intro X Ω _ ξ V _ _ L r b₀ b T p h₀ hb hT
  refine ⟨det_ne_zero hb.1 hT, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b', T', hb', hT', rfl⟩
    obtain ⟨A, hA, hd⟩ := exists_mat (regAt ξ p) (b := b) (b' := b') fun k => by
      rw [← hb.2, hb'.2]; exact Submodule.subset_span ⟨k, rfl⟩
    have e : T' = T * A := mat_unique h₀ fun k => by rw [← hT' k, ← mat_comp hT hA k]
    rw [e, Matrix.det_mul, mul_comm]
    exact Submodule.mem_span_singleton.2 ⟨⟨A.det, hd⟩, rfl⟩
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (SncPiece.det_mem_detLat hb hT))

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsConjInvariantMollifier
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

theorem contDiff_star (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : Fin n → ℂ => star v) := (starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)).contDiff

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.IntValSmul
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights TensorProduct

noncomputable section
namespace LevelTowerAlt.Lin

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

theorem mem_eigSp {R W O : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing O]
    (ρ : O →+* Module.End R W) (σ : O →+* R) (x : W) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

def intVal (σ : 𝓞 E →+* L) (a : 𝓞 E) : 𝓞 L :=
  ⟨σ a, (NumberField.RingOfIntegers.isIntegral a).map σ.toIntAlgHom⟩

theorem intVal_coe (σ : 𝓞 E →+* L) (a : 𝓞 E) : ((intVal σ a : 𝓞 L) : L) = σ a := rfl

theorem intVal_smul (σ : 𝓞 E →+* L) (a : 𝓞 E) (x : V) : intVal σ a • x = σ a • x := by
  rw [← intVal_coe σ a]
  exact (algebraMap_smul L (intVal σ a) x).symm

structure Pre (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (V₀ : Type) [AddCommGroup V₀] [Module (𝓞 L) V₀]
    (B : HermitianBundle.{0} L) where
  ρ : 𝓞 E →+* Module.End L V
  σ : Ψ ⊕ Ψ → (𝓞 E →+* L)
  σ_bij : Function.Bijective σ
  σ_inj : ∀ s, Function.Injective (σ s)
  fin : Module.Finite (𝓞 L) V₀
  j : V₀ →ₗ[𝓞 L] V
  j_inj : Function.Injective j
  span : Submodule.span L (Set.range j) = ⊤
  ρ₀ : 𝓞 E → V₀ → V₀
  j_ρ : ∀ a x, j (ρ₀ a x) = ρ a (j x)
  r : ℕ
  ε : Fin r → V₀
  ε_li : LinearIndependent (𝓞 L) ε
  I_stable : ∀ a, ∀ x ∈ AddSubgroup.closure (Set.range fun i => j (ε i)),
    ρ a x ∈ AddSubgroup.closure (Set.range fun i => j (ε i))
  f : V₀ →ₗ[𝓞 L] B.carrier
  ker : LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε)
  full : ∀ y, ∃ (a : 𝓞 L) (x : V₀), a ≠ 0 ∧ f x = a • y
  ρ' : 𝓞 E → B.carrier → B.carrier
  f_ρ : ∀ a x, f (ρ₀ a x) = ρ' a (f x)
  bar : 𝓞 E → 𝓞 E
  bar_conj : ∀ (τ : 𝓞 E →+* ℂ), Function.Injective τ → ∀ a, τ (bar a) = starRingEnd ℂ (τ a)
  adj : ∀ (ι : L →+* ℂ) a x y, (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] ρ' a x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] y) =
    (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] ρ' (bar a) y)

variable {V₀ : Type} [AddCommGroup V₀] [Module (𝓞 L) V₀] {B : HermitianBundle.{0} L} (P : Pre E L Ψ V V₀ B)

theorem Pre.eig {s : Ψ ⊕ Ψ} {x : V₀} (hx : P.j x ∈ eigSp P.ρ (P.σ s)) (a : 𝓞 E) :
    P.ρ' a (P.f x) = intVal (P.σ s) a • P.f x := by
  have h1 : P.ρ₀ a x = intVal (P.σ s) a • x := by
    apply P.j_inj
    rw [P.j_ρ, map_smul, intVal_smul]
    exact (mem_eigSp _ _ _).1 hx a
  rw [← P.f_ρ, h1, map_smul]

theorem Pre.orth {s s' : Ψ ⊕ Ψ} (h : s ≠ s') (ι : L →+* ℂ) {x y : V₀} (hx : P.j x ∈ eigSp P.ρ (P.σ s))
    (hy : P.j y ∈ eigSp P.ρ (P.σ s')) :
    (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f y) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, P.σ s a ≠ P.σ s' a := by
    by_contra hc
    push_neg at hc
    exact h (P.σ_bij.1 (RingHom.ext hc))
  have key : ∀ (c : 𝓞 L) (u : B.carrier), ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] (c • u) : Fibre ι B.carrier) =
      (ι (c : L) : ℂ) • ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] u) := by
    intro c u
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
  have hτ : Function.Injective (ι.comp (P.σ s')) := ι.injective.comp (P.σ_inj s')
  have e := P.adj ι a (P.f x) (P.f y)
  rw [P.eig hx, P.eig hy, key, key, (B.metric.form ι).smul_left,
    InnerProductSpace.Core.inner_smul_right (c := (B.metric.form ι).toCore), intVal_coe, intVal_coe] at e
  have hb := P.bar_conj _ hτ a
  simp only [RingHom.comp_apply] at hb
  rw [hb] at e
  have hne : (starRingEnd ℂ) (ι (P.σ s a)) ≠ (starRingEnd ℂ) (ι (P.σ s' a)) := by
    intro heq
    exact ha (ι.injective ((starRingEnd ℂ).injective heq))
  have : ((starRingEnd ℂ) (ι (P.σ s a)) - (starRingEnd ℂ) (ι (P.σ s' a))) *
      (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f y) = 0 := by
    rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem Pre.li {ι : Type} {x : ι → V₀} (hx : LinearIndependent (𝓞 L) x) : LinearIndependent L fun i => P.j (x i) := by
  have h := hx.map' P.j (LinearMap.ker_eq_bot.2 P.j_inj)
  exact h.localization (Rₛ := L) (S := nonZeroDivisors (𝓞 L))

def Pre.inv : LinearMap.range P.j →ₗ[𝓞 L] V₀ := (LinearEquiv.ofInjective P.j P.j_inj).symm.toLinearMap

theorem Pre.j_inv (x : LinearMap.range P.j) : P.j (P.inv x) = x := by
  have := (LinearEquiv.ofInjective P.j P.j_inj).apply_symm_apply x
  exact congrArg Subtype.val this

theorem Pre.inv_j (x : V₀) : P.inv ⟨P.j x, x, rfl⟩ = x := P.j_inj (P.j_inv _)

def Pre.lin : LinPt E L Ψ V where
  ρ := P.ρ
  σ := P.σ
  σ_bij := P.σ_bij
  σ_inj := P.σ_inj
  Λ := LinearMap.range P.j
  fg := by
    haveI := P.fin
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  span := P.span
  stable := by
    rintro a _ ⟨x, rfl⟩
    exact ⟨_, P.j_ρ a x⟩
  I := AddSubgroup.closure (Set.range fun i => P.j (P.ε i))
  I_le := fun x hx => (AddSubgroup.closure_le (LinearMap.range P.j).toAddSubgroup).2
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hx
  I_stable := P.I_stable
  I_basis := ⟨P.r, _, P.li P.ε_li, rfl⟩
  Bq := B
  f := P.f.comp P.inv
  ker := fun x => by
    have e : Submodule.span (𝓞 L) (AddSubgroup.closure (Set.range fun i => P.j (P.ε i)) : Set V) =
        (Submodule.span (𝓞 L) (Set.range P.ε)).map P.j := by
      rw [Submodule.map_span, ← Set.range_comp]
      refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) (Submodule.span_mono AddSubgroup.subset_closure)
      exact (AddSubgroup.closure_le (Submodule.span (𝓞 L) (Set.range (P.j ∘ P.ε))).toAddSubgroup).2
        Submodule.subset_span hy
    rw [e, ← P.ker, LinearMap.comp_apply]
    constructor
    · intro h
      exact ⟨_, h, P.j_inv x⟩
    · rintro ⟨y, hy, hxy⟩
      have : P.inv x = y := P.j_inj ((P.j_inv x).trans hxy.symm)
      rw [this]
      exact hy
  full := fun y => by
    obtain ⟨a, x, ha, h⟩ := P.full y
    exact ⟨a, ⟨P.j x, x, rfl⟩, ha, by rw [LinearMap.comp_apply, P.inv_j, h]⟩
  orth := by
    rintro s s' h ι _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact P.orth h ι (by rw [P.j_inv]; exact hx) (by rw [P.j_inv]; exact hy)

include P in
theorem Pre.rank_le [Module.Finite L V] : Module.finrank (𝓞 L) B.carrier ≤ Module.finrank L V := by
  have h2 : Module.rank (𝓞 L) V₀ ≤ (Module.finrank L V : Cardinal) := by
    apply _root_.rank_le
    intro s hs
    have := (P.li hs).fintype_card_le_finrank
    simpa using this
  have hq : Module.rank (𝓞 L) (B.carrier ⧸ LinearMap.range P.f) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, x, ha, h⟩ := P.full y
    refine ⟨a, ha, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← h]
    exact ⟨x, rfl⟩
  have h1 : Module.rank (𝓞 L) B.carrier ≤ Module.rank (𝓞 L) V₀ := by
    rw [← rank_quotient_add_rank_of_isDomain (LinearMap.range P.f), hq, zero_add]
    exact rank_range_le P.f
  exact Module.finrank_le_of_rank_le (h1.trans h2)

end LevelTowerAlt.Lin
end
end

