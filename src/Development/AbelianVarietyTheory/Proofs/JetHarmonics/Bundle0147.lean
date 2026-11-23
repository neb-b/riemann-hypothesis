module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosed
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosedStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyLift_one_mono_mul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), PolyLift P Bs 0 0 1 ∧ (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → PolyLift P Bs o κ a → PolyLift P Bs o' κ' a) ∧ ∀ o₁ κ₁ o₂ κ₂ a b, PolyLift P Bs o₁ κ₁ a → PolyLift P Bs o₂ κ₂ b → PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  first | exact @GlobalTheory.HatNF.polyLift_closed | exact GlobalTheory.HatNF.polyLift_closed | (intros; apply GlobalTheory.HatNF.polyLift_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplier
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

theorem jf_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (φ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.JF Bs (mulG Bs φ f) g = ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • B.JF Bs f g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (mulG Bs φ f) g ∂Bs.μSS =
    ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • ∫ p, JF.xiP Bs p • B.rho Bs p f g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, mulG, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem cptCoef_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {f : B.Mat k r → (Wq →L[ℂ] Wp)} (hf : KB.CptCoef Bs f) :
    KB.CptCoef Bs (mulG Bs φ f) := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨δ, hδ, hG⟩⟩ := hf
  have hne : ∀ g, mulG Bs φ f g ≠ 0 → f g ≠ 0 := fun g h h0 => h (by simp [mulG, h0])
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))
  exact ⟨Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc hs, ⟨R, fun g hg h => hR g hg (hne g h)⟩,
    ⟨δ, hδ, fun g hg h => hG g hg (hne g h)⟩⟩

theorem radial_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs φ f
  refine ⟨fun hφ => ⟨hφ.comp Real.contDiff_exp, fun hf => cptCoef_mulG Bs hφ hf⟩, ?_⟩
  intro W Φ hW hΦ x hx
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hpos : 0 < gR P Bs x.1 x.2 := by
    have := hcell.1.2.1
    rw [hcell.2.2.2] at this
    exact this
  have hld : LE.ld 0 φ (gR P Bs x.1 x.2) = φ (gR P Bs x.1 x.2) := by
    simp only [LE.ld, iteratedDeriv_zero, Real.exp_log hpos]
  rw [hW 0 Φ x.1 x.2, hΦ x hx]
  simp only [Q.resG]
  rw [jf_mulG, hcell.2.2.2, hld, smul_comm]
  rfl

end

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLogPrimeDepthBoundsLeMulWeightSize
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.PtTie

theorem depth_sum_le_PN : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → (WeightAlgebra.DF w : ℝ) * (Real.log (WeightAlgebra.DF w) + 2.2) + (c2 D w * Real.log D.host.QS + cHalf w * Real.log D.host.q + cHalf w * Real.log D.host.d) + ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤ WeightAlgebra.PN D large₂ * w.size := by
  intro D large₂ j w _ hlog
  obtain ⟨-, -, hM, hG, hc, -⟩ := GlobalTheory.RunIn.pPow_size D j w
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log (WeightAlgebra.DF w : ℝ) := Real.log_natCast_nonneg _
  have hs : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size := by
    have e : ((WeightAlgebra.DF w : ℕ) : ℝ) = ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by
      simp [WeightAlgebra.DF, WeightAlgebra.degP, Nat.cast_sum]
    have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
    unfold WeightFamilies.Wt.size
    linarith
  have hg2 : ∀ i, (2 : ℝ) ≤ D.host.g i := fun i => by exact_mod_cast (D.host.g_prime i).two_le
  have hterm : ∀ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤
      (WeightAlgebra.DF w : ℝ) * Real.log (D.host.g i) := fun i =>
    mul_le_mul_of_nonneg_right (div_le_self hD (by linarith [hg2 i])) (Real.log_natCast_nonneg _)
  have hsum : ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤
      (WeightAlgebra.DF w : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rw [Fin.sum_univ_two, Real.log_mul (by linarith [hg2 0]) (by linarith [hg2 1])]
    linarith [hterm 0, hterm 1]
  have hP : 0 ≤ WeightAlgebra.PN D large₂ := by
    unfold WeightAlgebra.PN WeightAlgebra.lamStar
    linarith
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hs hP)
  have h1 := mul_le_mul_of_nonneg_left hlog hD
  unfold WeightAlgebra.PN WeightAlgebra.lamStar
  nlinarith

end GlobalTheory.PtTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaSpansIsLatIn
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K] {C : Type} [AddCommGroup C]
  [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C)

theorem spanK_fg_of_subset [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] (N : Submodule (𝓞 F) C) (hN : N.FG)
    (s : Set C) (hs : s ⊆ N) : (spanK z s).FG := by
  classical
  obtain ⟨t, ht⟩ := hN
  have hle : spanK z s ≤ spanK z (t : Set C) := by
    unfold spanK
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hf' : f ∈ Submodule.span (𝓞 F) (t : Set C) := ht ▸ hs hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : z.symm (1 ⊗ₜ[F] (a • x)) =
          (RingOfIntegers.mapRingHom (algebraMap F K) a) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F a x, TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul,
          ← algebraMap_smul K (RingOfIntegers.mapRingHom (algebraMap F K) a)]
        rfl
      beta_reduce
      rw [e]
      exact Submodule.smul_mem _ _ hx
  have hfg : (spanK z (t : Set C)).FG := Submodule.fg_span (t.finite_toSet.image _)
  exact hfg.of_le hle

theorem span_spanK_eq_top (s : Set C) (hs : Submodule.span F s = ⊤) :
    Submodule.span K (spanK z s : Set (Fin n → K)) = ⊤ := by
  have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z s : Set (Fin n → K)) := by
    intro f
    have hf : f ∈ Submodule.span F s := hs ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (h1 f)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem scalOfP_sK_ne_zero {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {j : ℕ} (p : ℕ) (hp : 0 < p) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (scalOfP B hinj EX p ka wL wF T).sK ≠ 0 := by
  obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
  have h1 := fun w => (GlobalTheory.log_norm_normaliser D B hinj EX j w σ).1
  have h2 := fun a b c => ((GlobalTheory.RunIn.pPow_size D j ka).2.2.2.2.2 a b c).1
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (h1 _))) (h1 _)) ?_
  · exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  · exact Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h2 _ _ _))

theorem theta_spans_isLatIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → 0 < p → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → Submodule.IsLattice B.KO (B.Mlat j ka) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt X ka → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v i) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v i) := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act ht hp hF hn hD hM hSp h2
  have hle := Formalism.MainNotions.Gaps.T0.theta_le_msup X _ h2 hF rfl hn hD
  refine ⟨⟨?_, ?_⟩, ht.ThK_fg, ?_⟩
  · rw [ht.Th_eq]
    refine spanK_fg_of_subset z (B.Mlat j ka) hM.fg _ fun f hf => ?_
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 (hle hf)
    exact X.inc_inj ka e ▸ hg
  · rw [ht.Th_eq]
    apply span_spanK_eq_top
    apply top_unique
    rw [← hSp]
    apply Submodule.span_le.2
    intro f hf
    let a : 𝓞 B.KO := (scalOfP B hinj EX p ka wL wF T).sK
    let b : 𝓞 B.KO := ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * ka.n)
    have ha : (a : B.KO) ≠ 0 := by
      exact_mod_cast scalOfP_sK_ne_zero B hinj EX p hp ka wL wF T
    have hb : (b : B.KO) ≠ 0 := by
      dsimp [b]
      exact_mod_cast pow_ne_zero (D.R.f * D.R.r * ka.n) (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hm : X.inc ka (a • (b • f)) ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T := by
      apply (le_sup_right : X.emb ka (X.Thc a ka) ≤ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T)
      apply Submodule.mem_map.2
      refine ⟨a • (b • f), ?_, rfl⟩
      exact Submodule.mem_map.2 ⟨b • f, Submodule.mem_map.2 ⟨f, hf, rfl⟩, rfl⟩
    have hs := Submodule.subset_span (R := B.KO) (s := {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}) hm
    have he : a • (b • f) = ((a : B.KO) * (b : B.KO)) • f := by
      rw [← algebraMap_smul B.KO a (b • f), ← algebraMap_smul B.KO b f, smul_smul]
    rw [he] at hs
    have := (Submodule.span B.KO {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}).smul_mem (((a : B.KO) * (b : B.KO))⁻¹) hs
    change f ∈ Submodule.span B.KO {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero ha hb), one_smul] using this
  · apply top_unique
    have hs : Submodule.span K (spanK z (X.shortTh ka : Set _) : Set (Fin (O.nZ i) → K)) = ⊤ := span_spanK_eq_top z _ hSp
    rw [← hs]
    apply Submodule.span_mono
    intro x hx
    apply ht.ThK_ge
    exact spanK_mono z (fun f hf => by
      change X.inc ka f ∈ thetaPlain X ka wL wF T
      apply (le_sup_right : X.emb ka (X.shortTh ka) ≤ thetaPlain X ka wL wF T)
      exact Submodule.mem_map.2 ⟨f, hf, rfl⟩) hx
end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficients
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

open Filter Topology MeasureTheory in
private lemma opApply_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (c : ℂ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply Θ (c • F) g = c • _root_.Formalism.FourierDecayAlt.B.opApply Θ F g := by
  unfold _root_.Formalism.FourierDecayAlt.B.opApply
  simp only [_root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, Pi.smul_apply, map_smul]
  rw [List.smul_sum, List.map_map]
  rfl

open Filter Topology MeasureTheory in
private lemma vecV_smul_jet_harmonics {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν : Fin (2 * r + k + 1) → ℂ) (m : _root_.Formalism.FourierDecayAlt.B.Mat k r) (c : ℂ)
    (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m (fun g => c • G g) q = c • _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m G q := by
  unfold _root_.Formalism.FourierDecayAlt.D.vecV
  split_ifs with h h'
  · apply _root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae
    refine MeasureTheory.ae_of_all _ fun x => ?_
    unfold _root_.Formalism.FourierDecayAlt.D.orbIntegrand _root_.Formalism.FourierDecayAlt.B.rho
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    exact smul_comm _ _ _
  · simp
  · simp

open Filter Topology MeasureTheory in
private lemma topLift_vecV_add_smul_lemma {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : _root_.Formalism.FourierDecayAlt.M.Par} (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    {Cb : ℝ} (a : ℂ) {H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List _root_.Formalism.FourierDecayAlt.C.Letter}
    (hdom : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hcut : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w)
    (h₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁) (h₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂) (i : _root_.Formalism.FourierDecayAlt.Wd.Ix (Fin w.length))
    (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    p.V (p.Θ.Θ w i (H₁ + a • H₂)) q = p.V (p.Θ.Θ w i H₁) q + a • p.V (p.Θ.Θ w i H₂) q := by
  obtain ⟨nf, fib, o, κ, D, -, hD, -, -, hΘ⟩ := hdom w hcut i
  have hlen : ∀ T ∈ D, T.word.length ≤ o := fun T hT => by
    obtain ⟨_, _, _, _, es, -, -, hl, -⟩ := hD.2.2 T hT
    omega
  have hpos : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GPos p.T.base, g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, by simp⟩
  have hc₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₁ hD.1
  have hc₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₂ hD.1
  have e₁ : p.V (p.Θ.Θ w i H₁) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₁ g (hpos g hg)
  have e₂ : p.V (p.Θ.Θ w i H₂) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₂ g (hpos g hg)
  have e₃ : p.V (p.Θ.Θ w i (H₁ + a • H₂)) q =
      p.V (fun g => _root_.Formalism.FourierDecayAlt.B.opApply D H₁ g - (fun g => (-a) • _root_.Formalism.FourierDecayAlt.B.opApply D H₂ g) g) q := by
    refine _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => ?_
    have hsum : H₁ + a • H₂ = H₁ - (-a) • H₂ := by rw [neg_smul, sub_neg_eq_add]
    rw [hΘ _ g (hpos g hg), hsum,
      _root_.Formalism.FourierDecayAlt.P.PBE.opApply_subGV D hlen (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₁.1 o) (_root_.Formalism.FourierDecayAlt.P.B4.ckOn_smul (-a) (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₂.1 o)) g hg.1, opApply_smul]
  have e₄ := _root_.Formalism.FourierDecayAlt.P.PBN.vecV_sub p.T.base p.ν' p.m₀ q hc₁ (_root_.Formalism.FourierDecayAlt.P.PBN.cpt_smul p.T.base (-a) hc₂)
  have e₅ := vecV_smul_jet_harmonics p.T.base p.ν' p.m₀ (-a) (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q
  rw [e₁, e₂, e₃]
  change _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q = _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q + a • _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q
  rw [e₄, e₅, neg_smul, sub_neg_eq_add]

open Filter Topology MeasureTheory in
private lemma hsVec_add_jet_harmonics {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (A B : Wq →L[ℂ] Wp) : _root_.Formalism.FourierDecayAlt.B.hsVec (A + B) = _root_.Formalism.FourierDecayAlt.B.hsVec A + _root_.Formalism.FourierDecayAlt.B.hsVec B := by
  unfold _root_.Formalism.FourierDecayAlt.B.hsVec
  rfl


open Filter Topology MeasureTheory in
theorem _root_.GlobalTheory.TopVec.tv_add_smul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (Cb : ℝ) (a : ℂ) (H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (c : Fin (P.r + 1) → ℂ), _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁ → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂ → _root_.GlobalTheory.TopVec.tv p (H₁ + a • H₂) w c = _root_.GlobalTheory.TopVec.tv p H₁ w c + a • _root_.GlobalTheory.TopVec.tv p H₂ w c := by
  intro Wp Wq _ _ _ _ _ _ P p Cb a H₁ H₂ w c hdom hcut h₁ h₂
  unfold _root_.GlobalTheory.TopVec.tv
  rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  funext x
  rw [topLift_vecV_add_smul_lemma p a hdom hcut h₁ h₂, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, hsVec_add_jet_harmonics, _root_.Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, smul_add, Pi.add_apply, Pi.smul_apply,
    smul_comm a]

end GlobalTheory.TopVec
end

