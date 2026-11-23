module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.DownLift.Sobolev₂

open GlobalTheory.Size GlobalTheory.Grow
open scoped ComplexOrder

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 1000000 in
theorem integrableOn_extV (R : RealDat D A Ks) (hm : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hc := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hK := hc.choose_spec.1
  have hKc := hc.choose_spec.2
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hFc : Continuous (R.extV i t y) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hlc : Continuous fun h => l (R.extV i t y h) := l.continuous_of_finiteDimensional.comp hFc
  have hH : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfd : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have : IsFiniteMeasure ((R.νV i t).restrict (R.fdV i t)) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol (Vc D i) (R.νV i t) (R.fdV i t)
      hH hfd).ne
  have hb := hK.exists_bound_of_continuousOn hlc.continuousOn
  have hbd : ∀ h, ‖l (R.extV i t y h)‖ ≤ hb.choose := by
    intro h
    obtain ⟨γ, hγ, c, hc, e⟩ := hKc h
    rw [e, hFi γ hγ c]
    exact hb.choose_spec c hc
  exact Integrable.of_bound hlc.aestronglyMeasurable hb.choose (.of_forall hbd)


set_option maxHeartbeats 1000000 in
theorem downInt_sobolev_cont : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y μ 𝓕 hμ f hf l g ε hε
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hG.core.thP.ωP i t
  have hψ := hω.std
  have hpt := hG.core.thP.pt_theta i t
  have hvP : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hpt 1
    rwa [RealDat.ptP, GlobalTheory.FiniteFock.pureTensorO_one] at this
  obtain ⟨U₀, hU₀, hl₀⟩ := isTheta_iff_level.1 hvP
  obtain ⟨U₁, hU₁, hl₁⟩ := isTheta_iff_level.1 hf
  have hUo : IsOpen ((U₁ ⊓ U₀ : AddSubgroup (WO (Vc D i) (Wc D i))) : Set (WO (Vc D i) (Wc D i))) := by
    rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₀
  have hptl : ∀ P, R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) U₀ := fun P =>
    ⟨hpt P, fun u hu h0 => by
      have e := ((GlobalTheory.FinTranslate.finite_translate D R.ψ R.θ _ _ hψ hθ _ hvP).2 u h0).2
      unfold RealDat.ptP
      rw [← e, hl₀.2 u hu h0]⟩
  have hfl : f ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := thetaLevel_anti inf_le_left hl₁
  have hpl : ∀ P, R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P =>
    thetaLevel_anti inf_le_right (hptl P)
  have hml : ∀ P, f - R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P => sub_mem hfl (hpl P)
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (Vc D i).rank (Wc D i).rank
  obtain ⟨C, hC0, hC⟩ := (H (Vc D i) (Wc D i) rfl rfl).real R.ψ hθ hUo
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  obtain ⟨HK, hHK⟩ := hK.exists_bound_of_continuousOn (continuous_height (Vc D i)).continuousOn
  have hHK0 : 0 ≤ HK := by
    obtain ⟨γ, -, c, hc, -⟩ := hKc 1
    exact (norm_nonneg _).trans (hHK c hc)
  have hg0 := height_pos (Wc D i) g
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (HK * height (Wc D i) g) ^ Ae := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ by positivity
  have hbound : ∀ φ ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀), ∀ h,
      ‖thetaKO (R.ωP i t) h g φ‖ ≤ B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by
    intro φ hφ h
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hKc h
    rw [GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hφ.1 γ hγ c g]
    have h1 := (hC _ _ (R.ωP i t) hω μ 𝓕 hμ φ hφ).2 c g
    have hc1 : height (Vc D i) c ≤ HK := (Real.le_norm_self _).trans (hHK c hc)
    have hc0 := height_pos (Vc D i) c
    have hs : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d φ).toReal := ENNReal.toReal_nonneg
    have h2 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (height (Vc D i) c * height (Wc D i) g) ^ Ae ≤
        C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hc0 hg0).le
        (mul_le_mul_of_nonneg_right hc1 hg0.le) Ae) (mul_nonneg hC0 hs)
    have h3 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae =
        B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by rw [hB]; ring
    exact h1.trans (h2.trans_eq h3)
  have hl1 : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := integrableOn_extV R hm i t y l
  have hint : ∀ φ ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀),
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g φ * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := fun φ hφ =>
    Integrable.bdd_mul hl1 ((hω.om_cont φ hφ.1 0).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (.of_forall (hbound φ hφ))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ h in R.fdV i t, ‖l (R.extV i t y h)‖ ∂(R.νV i t) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hMdef ▸ integral_nonneg fun _ => norm_nonneg _
  have hpos : 0 < B * M + 1 := by positivity
  refine ⟨d, ENNReal.ofReal (ε / (B * M + 1)), ENNReal.ofReal_pos.2 (by positivity), fun P hP => ?_⟩
  have hs := ENNReal.toReal_lt_of_lt_ofReal hP
  have hs0 : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := ENNReal.toReal_nonneg
  have e : downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g =
      ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h) ∂(R.νV i t) := by
    have i1 := hint f hfl
    have i2 := hint (R.ptP i t P) (hpl P)
    have e1 := integral_sub i1 i2
    refine e1.symm.trans (integral_congr_ae (.of_forall fun h => ?_))
    have e2 : R.ωP i t (h, g) (f - R.ptP i t P) = R.ωP i t (h, g) f - R.ωP i t (h, g) (R.ptP i t P) :=
      LinearMap.map_sub _ _ _
    show thetaKO (R.ωP i t) h g f * l (R.extV i t y h) - thetaKO (R.ωP i t) h g (R.ptP i t P) * l (R.extV i t y h) =
      thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h)
    refine (sub_mul _ _ _).symm.trans (congrArg (· * l (R.extV i t y h)) ?_)
    exact (congrFun e2 0).symm
  rw [e]
  have hle := norm_integral_le_of_norm_le (μ := (R.νV i t).restrict (R.fdV i t))
    (f := fun h => thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h))
    (hl1.norm.const_mul (B * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal))
    (.of_forall fun h => by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound _ (hml P) h) (norm_nonneg _)))
  rw [integral_const_mul, ← hMdef] at hle
  calc _ ≤ _ := hle
    _ ≤ (B * M + 1) * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := by nlinarith
    _ < (B * M + 1) * (ε / (B * M + 1)) := by gcongr
    _ = ε := by field_simp

end GlobalTheory.DownLift.Sobolev₂
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylModuleIntertwinesGLOfUnitaryGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section

namespace GlobalTheory.AlgWtHW

theorem eval_adjugate_mvPolynomialX {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2)
      ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate x y) = g.adjugate x y := by
  have h := RingHom.map_adjugate (MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2))
    (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)
  have h2 : (MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2)).mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) = g := by
    ext i j; simp [Matrix.mvPolynomialX]
  rw [h2] at h
  simpa using congrFun (congrFun h x) y

theorem eval_det_mvPolynomialX {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det = g.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem det_mul_inv_apply {n : ℕ} (B : GL (Fin n) ℂ) (x y : Fin n) :
    B.val.det * (B⁻¹).val x y = B.val.adjugate x y := by
  have h : B.val.adjugate = B.val.det • (B⁻¹).val := by
    calc B.val.adjugate = B.val.adjugate * (B.val * (B⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = (B.val.adjugate * B.val) * (B⁻¹).val := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h, Matrix.smul_apply, smul_eq_mul]

theorem exists_det_pow_mul_eq_poly {n : ℕ} (Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), ∀ B : GL (Fin n) ℂ,
      B.val.det ^ d * MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) Q =
        MvPolynomial.eval (fun p => B.val p.1 p.2) P := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, fun B => by simp⟩
  | add p q hp hq =>
    obtain ⟨d₁, P₁, h₁⟩ := hp
    obtain ⟨d₂, P₂, h₂⟩ := hq
    refine ⟨d₁ + d₂, P₁ * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det ^ d₂ +
      P₂ * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det ^ d₁, fun B => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, eval_det_mvPolynomialX, ← h₁ B, ← h₂ B]
    ring
  | mul_X p v hp =>
    obtain ⟨d, P, h⟩ := hp
    cases v with
    | inl x =>
      refine ⟨d, P * MvPolynomial.X x, fun B => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inl, ← h B]
      ring
    | inr x =>
      refine ⟨d + 1, P * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate x.1 x.2, fun B => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inr, eval_adjugate_mvPolynomialX, ← h B,
        ← det_mul_inv_apply]
      ring

theorem sqRep_intertwines_of_unitary : ∀ (n : ℕ) (lam : DomWeight n) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), GlobalTheory.AlgWtHW.IsPolyRep Φ → ∀ M : nablaSq ℂ n lam →ₗ[ℂ] (ι → ℂ), (∀ (u : Matrix.unitaryGroup (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n u) v) = Matrix.mulVec (Φ (GlobalTheory.Branching.unitaryIncl n u)) (M v)) → ∀ (B : GL (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam B v) = Matrix.mulVec (Φ B) (M v) := by
  classical
  intro n lam ι _ _ Φ hΦ M hU B v
  funext k
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (nablaSq ℂ n lam)
  let π := (nablaSq ℂ n lam).linearProjOfIsCompl C hC
  let l : Module.Dual ℂ (MvPolynomial (Fin n × Fin n) ℂ) := LinearMap.proj k ∘ₗ M ∘ₗ π
  have hl : ∀ B' : GL (Fin n) ℂ, M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k =
      detPow ℂ n B' lam.detShift * l (Formalism.GradedWeylDivisibility.rowAct ℂ (B'.val)ᵀ v.1) := by
    intro B'
    calc M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k = l (sqAct ℂ n lam B' v.1) := by
          simp only [l, π, LinearMap.comp_apply, LinearMap.proj_apply]
          have := Submodule.linearProjOfIsCompl_apply_left hC (GlobalTheory.Branching.sqRep ℂ n lam B' v)
          rw [← GlobalTheory.Branching.sqRep_coe]
          exact (congrArg (fun w => M w k) this).symm
      _ = _ := by rw [sqAct, map_smul, smul_eq_mul]
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef n n v.1 l
  let R₁ := MvPolynomial.rename Prod.swap P₁
  have hR₁ : ∀ g : Matrix (Fin n) (Fin n) ℂ,
      MvPolynomial.eval (fun x => g x.1 x.2) R₁ = l (Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ v.1) := by
    intro g
    rw [hP₁, MvPolynomial.eval_rename]
    rfl
  choose Q hQ using hΦ.poly
  let Qs := ∑ j, Q k j * MvPolynomial.C ((M v) j)
  have hQs : ∀ B' : GL (Fin n) ℂ,
      MvPolynomial.eval (Sum.elim (fun p => B'.val p.1 p.2) (fun p => (B'⁻¹).val p.1 p.2)) Qs = (Φ B' *ᵥ M v) k := by
    intro B'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Qs, map_sum, map_mul, MvPolynomial.eval_C, ← hQ, Matrix.mulVec, dotProduct]
  obtain ⟨d, P₂, hP₂⟩ := exists_det_pow_mul_eq_poly Qs
  set a := lam.detShift
  set m : ℕ := a.natAbs
  have ha : 0 ≤ a + (m : ℤ) := by omega
  have hdet : ∀ B' : GL (Fin n) ℂ, B'.val.det ≠ 0 := fun B' => (Matrix.isUnits_det_units B').ne_zero
  have hdp : ∀ B' : GL (Fin n) ℂ, detPow ℂ n B' a = B'.val.det ^ a := by
    intro B'
    simp [detPow, Units.val_zpow_eq_zpow_val]
  have key : ∀ B' : GL (Fin n) ℂ,
      B'.val.det ^ d * B'.val.det ^ (a + (m : ℤ)).toNat * l (Formalism.GradedWeylDivisibility.rowAct ℂ (B'.val)ᵀ v.1) -
        B'.val.det ^ m * MvPolynomial.eval (fun p => B'.val p.1 p.2) P₂ =
      B'.val.det ^ d * B'.val.det ^ m * (M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k - (Φ B' *ᵥ M v) k) := by
    intro B'
    have hx := hdet B'
    rw [hl, ← hQs, ← hP₂, hdp]
    have e1 : B'.val.det ^ (a + (m : ℤ)).toNat = B'.val.det ^ m * B'.val.det ^ a := by
      rw [← zpow_natCast (B'.val.det) (a + (m : ℤ)).toNat, Int.toNat_of_nonneg ha, zpow_add₀ hx, zpow_natCast]
      ring
    rw [e1]
    ring
  let Dp := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  let Qd := Dp ^ d * Dp ^ (a + (m : ℤ)).toNat * R₁ - Dp ^ m * P₂
  have hQd : ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (fun x => g x.1 x.2) Qd =
      g.det ^ d * g.det ^ (a + (m : ℤ)).toNat * l (Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ v.1) -
        g.det ^ m * MvPolynomial.eval (fun p => g p.1 p.2) P₂ := by
    intro g
    simp only [Qd, Dp, map_sub, map_mul, map_pow, eval_det_mvPolynomialX, hR₁]
  have Q0 : Qd = 0 := by
    refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup n Qd fun u hu => ?_
    have h1 := key (GlobalTheory.Branching.unitaryIncl n ⟨u, hu⟩)
    have h2 := congrFun (hU ⟨u, hu⟩ v) k
    rw [h2, sub_self, mul_zero] at h1
    rw [hQd]
    exact h1
  have h3 := key B
  rw [← hQd, Q0, map_zero] at h3
  have hx := hdet B
  have h4 : B.val.det ^ d * B.val.det ^ m ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hx)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3.symm).resolve_left h4)

end GlobalTheory.AlgWtHW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstantIntegralArcFrames
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts
  GlobalTheory.GoodTransfer

namespace GlobalTheory.ArcFrame

open Matrix GlobalTheory.LieEigen MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem iwasawa_lower {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
    [IsFractionRing V F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (L : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ (∀ i j, i < j → L i j = 0) ∧
      (∀ i, L i i ≠ 0) ∧ A = L * k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, e⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) Aᵀ (by rwa [det_transpose])
  refine ⟨kᵀ, Uᵀ, by rwa [det_transpose], fun i j h => hU h, hd, ?_⟩
  rw [← transpose_transpose A, e, transpose_mul, transpose_map]

section Lie

variable {R O : Type} [CommRing R] [IsLocalRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] (act : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

theorem eig_prodPts (hv : ∀ i, IsTangent (v i)) (x : O) (s : R)
    (he : ∀ i, (v i ≫ act.act x).left = spMap (epsScaleR s) ≫ (v i).left) (c : Fin n → R) :
    (prodPts c v ≫ act.act x).left = spMap (epsScaleR s) ≫ (prodPts c v).left := by
  have := act.hom x
  have e : prodPts c v ≫ act.act x = prodPts c fun i => v i ≫ act.act x := by
    refine (map_list_prod (IsMonHom.monoidHom (act.act x) _) _).trans ?_
    rw [prodPts, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Category.assoc _ (v i) (act.act x))
  have e₁ : ∀ i, v i ≫ act.act x = prodPts (s • Pi.single i 1) v := fun i => by
    rw [prodPts_smul, ← (Chart.isLieComb_iff _ _ _).1 (IntModelExists.isLieComb_single hv i)]
    exact Over.OverMorphism.ext (he i)
  have e₂ : ∑ i, c i • (s • Pi.single i (1 : R) : Fin n → R) = s • c := by
    ext j; simp [Pi.single_apply, mul_comm]
  rw [e, funext e₁, prodPts_prodPts hv, e₂, prodPts_smul]
  rfl


omit [IsLocalRing R] [Smooth G.hom] in
theorem existsUnique_change (hv : ∀ i, IsTangent (v i)) (k : Matrix (Fin n) (Fin n) R) (hk : IsUnit k.det)
    {w : epsR R ⟶ G} (h : ∃! cf : Fin n → R, IsLieComb cf v w) :
    ∃! cf : Fin n → R, IsLieComb cf (fun i => prodPts (k i) v) w := by
  have key : ∀ cf : Fin n → R, IsLieComb cf (fun i => prodPts (k i) v) w ↔ IsLieComb (cf ᵥ* k) v w := fun cf => by
    rw [Chart.isLieComb_iff, Chart.isLieComb_iff, vecMul_eq_sum]
    exact Eq.congr_right (prodPts_prodPts hv cf fun i => k i)
  obtain ⟨d, hd, hu⟩ := h
  refine ⟨d ᵥ* k⁻¹, (key _).2 ?_, fun cf hcf => ?_⟩
  · rwa [vecMul_vecMul, nonsing_inv_mul _ hk, vecMul_one]
  · rw [← hu _ ((key _).1 hcf), vecMul_vecMul, mul_nonsing_inv _ hk, vecMul_one]

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem arcBasis_change (hG : Out.GlobalFnsSt) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h : ArcBasis W ρ e) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)
    (hk : ∀ τ, IsUnit (k τ).det) (he : ∀ τ i, GtComb (k τ i) (e τ) (e' τ i)) :
    ArcBasis W ρ e' ∧ ∀ τ i, GtTanR (e' τ i) := by
  obtain ⟨v, hi, hb⟩ := h
  have := W.t.semi.smooth
  let k' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (PowerSeries A) :=
    fun τ => (k τ).map (PowerSeries.C (R := A))
  have hk' : ∀ τ, IsUnit (k' τ).det := fun τ => by
    have := (hk τ).map (PowerSeries.C (R := A))
    rwa [RingHom.map_det] at this
  have ht : ∀ τ i, IsTangent (v τ i) := fun τ i => ((hb τ).1 i).1
  have img : ∀ τ i, LieImg W (e' τ i) (prodPts (k' τ i) (v τ)) := fun τ i =>
    (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W _ _ (e τ) _ (v τ) _ (hi τ) (he τ i)).2
      ((Chart.isLieComb_iff _ _ _).2 rfl)
  refine ⟨⟨_, img, fun τ => ⟨fun i => ⟨isTangent_prodPts (ht τ) _, fun x => ?_⟩, fun w hw hw' => ?_⟩⟩, fun τ i =>
    ((_root_.GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y A b a χ W _).2 _ (img τ i)).2 (isTangent_prodPts (ht τ) _)⟩
  · exact eig_prodPts W.t.act (ht τ) x _ (fun j => ((hb τ).1 j).2 x) _
  · exact existsUnique_change (ht τ) (k' τ) (hk' τ) ((hb τ).2 w hw hw')

theorem exists_values (c : Coeff l) (V : ValuationSubring c.F) :
    ∃ r z : V, ((V.subtype r : c.F) : ℂ) = H.rt0 ∧ ((V.subtype z : c.F) : ℂ) = zeta l.A := by
  have key : ∀ (x : c.F) (n : ℕ), 0 < n → ∀ m : ℤ, x ^ n = m → x ∈ V := fun x n hn m h =>
    IntModelExists.mem_of_isIntegral _ (IsIntegral.of_pow hn (by
      rw [h]; simpa using isIntegral_algebraMap (R := ℤ) (A := c.F) (x := m)))
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, key _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, key _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one

theorem exists_arcFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ev : PowerSeries T.V →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c), PushInvertible Y.t.G Y.t.PP.L → (algebraMap T.V T.Fr).comp b = io.comp V.subtype → χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b → (∀ x, ev (PowerSeries.C x) = x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp ev) ≫ χ → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, z ≫ pullback.fst _ _ = y.x → ∃ (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V)) (th : a.D₀.P.L.Sec) (y₀ : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), ArcBasis W ρ e ∧ ThNZ th ∧ (∀ τ k, GtTanR (e τ k)) ∧ (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x)) ∧ IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y₀ ∧ FrBor t y₀ y := by
  intro E _ _ _ H Dw l Xo c V Y T io b a χ W ev z hP hb hχ hev hz hj
  letI := io.toAlgebra
  intro y hy
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG := hL.globalFns
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  let em : (E →+* ℂ) → (𝓞 E →+* V) := fun τ => (embK c τ).codRestrict V.toSubring fun x =>
    IntModelExists.mem_of_isIntegral _ ((RingOfIntegers.isIntegral x).map (embK c τ).toIntAlgHom)
  let ρ : (E →+* ℂ) → (𝓞 E →+* T.V) := fun τ => b.comp (em τ)
  have hρ : ∀ τ x, algebraMap T.V T.Fr (ρ τ x) = io (embK c τ x) := fun τ x => RingHom.congr_fun hb (em τ x)
  have hC : ((algebraMap T.V T.Fr).comp ev).comp (PowerSeries.C (R := T.V)) = algebraMap T.V T.Fr :=
    RingHom.ext fun x => congrArg (algebraMap T.V T.Fr) (hev x)
  have hm : Mono Y.j := by
    have : IsPreimmersion (spMap V.subtype) :=
      IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
    have := Y.jQ_open
    unfold Model.j
    infer_instance
  obtain ⟨e₁, -, he₁⟩ := GlobalTheory.ConstBasis.exists_arcBasis hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W ρ io hb.symm hρ
    (exists_values c V)
  obtain ⟨th, hth, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange a.D₀.P
  obtain ⟨y₁, hx₁, hy₁⟩ := GlobalTheory.ArcQ.exists_isArcFr hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W ρ e₁ th he₁ hth (Or.inr hP)
    T.Fr ((algebraMap T.V T.Fr).comp ev) z (by rw [hC]; exact IntModelExists.flat_of_injective _ hinj) hj
    (by rw [← Category.assoc, hy]; exact y.2)
    (fun τ x => ((RingHom.congr_fun hC (ρ τ x)).trans (hρ τ x)).symm)
  obtain ⟨g, s, hg⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr (fun _ => 1) 1 y₁).2.2.2 y (hx₁.trans hy).symm
  obtain ⟨hgu, hsu⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr g s y₁).2.2.1 y hg
  choose k L hk hL0 hLd hkL using fun τ => iwasawa_lower (V := T.V) (g τ) (hgu τ).ne_zero
  choose e he using fun τ i => ConstLie.exists_gtComb (k τ i) (e₁ τ)
  obtain ⟨hbe, hte⟩ := arcBasis_change hG W he₁ k hk he
  obtain ⟨y₀, hy₀⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr (fun τ => (k τ).map (algebraMap T.V T.Fr)) 1
    y₁).1 (fun τ => by
      have := (hk τ).map (algebraMap T.V T.Fr)
      rwa [RingHom.map_det] at this) isUnit_one
  obtain ⟨hcomp, -, -, hbor⟩ := frChg_calculus E H Dw l Xo c T.Fr
  refine ⟨ρ, e, th, y₀, fun i => match i with
    | none => hsu.unit
    | some p => Units.mk0 _ (hLd p.1 p.2), hbe, hth, hte, fun τ x => (hρ τ x).symm, ?_, ?_⟩
  · refine GlobalTheory.T.arcFrame_change_by_constants hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W e₁ e th th k 1 hth he (ThMul.refl th) T.Fr _ y₁ y₀
      hm hy₁ ?_
    rw [hC, map_one, map_one]
    exact hy₀
  · refine (hbor _ _ _).2 ⟨L, fun _ _ => rfl, hL0, (hcomp _ L _ _ y₁ y₀ y hy₀).2 ?_⟩
    rw [_root_.mul_one, ← funext hkL]
    exact hg

end GlobalTheory.ArcFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFderivRealLieChartEqSumKernelOperators
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem integral_fderiv_chart_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a,
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
        ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 :=
  fun E _ _ _ a X _ ν k γ hk φ hb g =>
    integral_fderiv_chart_eq_of ν k γ (fun p => _root_.GlobalTheory.JSW.isRapidInf_mul_adCoef E a X ν k γ hk p) φ hb g

end GlobalTheory.JSW
end

