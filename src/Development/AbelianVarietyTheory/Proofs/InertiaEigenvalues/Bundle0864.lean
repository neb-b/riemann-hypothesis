module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0854
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
section
noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.ThetaPoisson GroundTheory.Global GlobalTheory.RSThetaLow
open GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.RSResidue

theorem continuous_integral_of_compact {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] {K : Set Y} (hK : IsCompact K)
    {F : X → Y → ℂ} (hF : Continuous fun p : X × Y => F p.1 p.2) (h0 : ∀ x, ∀ y ∉ K, F x y = 0) :
    Continuous fun x => ∫ y, F x y ∂ν := by
  have hI : (fun x => ∫ y, F x y ∂ν) = fun x => ∫ y in K, F x y ∂ν :=
    funext fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
  rw [hI]
  have hc : ∀ x, Continuous (F x) := fun x => hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (F x) K ν := fun x => (hc x).continuousOn.integrableOn_compact hK
  set m : ℝ := ν.real K with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hδ : 0 < ε / (m + 1) := by positivity
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, dist (F x y) (F x₀ y) < ε / (m + 1) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 := Metric.tendsto_nhds.1 (hF.continuousAt (x := (x₀, y))) (ε / (m + 1) / 2) (by positivity)
    have h2 := Metric.tendsto_nhds.1 ((hc x₀).comp continuous_snd |>.continuousAt (x := (x₀, y)))
      (ε / (m + 1) / 2) (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    calc dist (F z.1 z.2) (F x₀ z.2) ≤ dist (F z.1 z.2) (F x₀ y) + dist (F x₀ z.2) (F x₀ y) :=
          dist_triangle_right _ _ _
      _ < ε / (m + 1) / 2 + ε / (m + 1) / 2 := add_lt_add hz1 hz2
      _ = ε / (m + 1) := by ring
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have h3 : ‖∫ y in K, (F x y - F x₀ y) ∂ν‖ ≤ ε / (m + 1) * m :=
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun y hy => by
      rw [← dist_eq_norm]; exact (hx y hy).le
  refine h3.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsHat_zero_eq {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) : ∃ c : ℂ, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 = (∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a) * c := by
  refine ⟨(finiteAdelicChar E (∑ i, η i * pFin E ((0 : Fin a → Ad E) i)) : ℂ) *
        (latt a (traceDualIdeal E J)).indicator 1 (fun i => pFin E ((0 : Fin a → Ad E) i)) *
        ((finiteMeasurePi E (latt a J)).toReal : ℂ), fun g => ?_⟩
  have h := rsHat_eq (ℓ := ℓ) J η F F' hΦ g 0
  have e : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have hF : infFourier (rsInf ℓ F.1 F'.1 Φ g) (fun i => pInf E ((0 : Fin a → Ad E) i)) =
      ∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a := by
    rw [e, infFourier]
    simp
  change rsHat ℓ F.1 F'.1 Φ J η g 0 = _
  rw [h, hF]
  ring

variable {ω : HChar E}

theorem rsHat_zero_props (hω : ω.IsUnitary) {φ φ' : Sm E a} (h : φ.1 ∈ bddForms E a ω) (h' : φ'.1 ∈ bddForms E a ω)
    {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) :
    Continuous (fun g : GA E a => adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0) ∧
    (∃ C : ℝ, ∀ g : GA E a, ‖adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0‖ ≤ C) ∧
    ∀ γ ∈ latticeGL E a, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g)) 0 = adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 := by
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hc]
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc, norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ hγ g
    have hL : ∀ x, φ.1 (γ * x) * conj (φ'.1 (γ * x)) = φ.1 x * conj (φ'.1 x) := fun x =>
      leftInv_mul_conj hω h h' γ hγ x
    have e : rsInf ℓ φ.1 φ'.1 Φ (γ * g) = rsInf ℓ φ.1 φ'.1 Φ g := funext fun u => by
      rw [rsInf, rsInf, mul_assoc γ g, hL]
    have e' : rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y => by
      rw [rsPsi, rsPsi, e]
    rw [e']

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

end GlobalTheory.RSResidue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentOverBaseComponentRationalIsometry
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrame

theorem comp_over_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  intro D T hT j hj σ hσ C hC k₂
  obtain ⟨h₀, rfl⟩ := _root_.GlobalTheory.CoverOnto.exists_dict₂_comp D T hT j hj σ hσ C hC k₂
  obtain ⟨γ, hΛ, hiso, hfr⟩ := _root_.GlobalTheory.CoverFrameMove.frames_differ D T hT j hj σ hσ C hC h₀
  refine ⟨(T.dict j σ h₀).1, γ, hΛ, hiso, fun h hh => _root_.GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hT j hj σ hσ C hC h h₀ hh,
    fun x x' hx hxx' => ?_⟩
  have hU := hT.unf j hj σ hσ
  have hU₂ := hC.2.2.2.1
  have hx' : x' ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom :=
    _root_.GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ γ ((hU.2.1 _).1.trans (hU₂.2.1 _).1.symm)
      (fun τ => ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm) hiso x x' hx hxx'
  exact ⟨hx', _root_.GlobalTheory.CoverFrameRead.rdU_cover_eq D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr x x' hx hx' hxx'⟩

end GlobalTheory.CoverFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFramedPointOverMovedBaseFrame
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameOver

open GlobalTheory.CoverFrameRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem un_over : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r) (hx : x ∈ (C.U₂.X (C.dict₂ h).1).dom) (hx' : x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom), (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).x : Sp ℂ ⟶ C.d.Xo₂.X) C.d.r = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).x : Sp ℂ ⟶ (T.Q.Xo j).X) ∧ ∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)), CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) C.d.m.φ = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left) := by
  intro D T hT j hj σ hσ C hC h γ hlat hiso hfr x x' hx hx' hxx
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, ⟨hEF₁, hper₁⟩, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, ⟨hEF₂, hper₂⟩, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  obtain ⟨-, hpq, -, hq⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hT.pins j hj
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, -, hm₂, hf₂⟩ := hd₂ h
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  obtain ⟨δ, hδf, hδm⟩ := move_mark (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ hL₁
  have hγδ : (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = δ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h).1).cmType _).2 h0)⟩
    have t₁ := (hΨ τ).2 t₂
    have a₂ := hf₂ ⟨τ, t₂⟩
    have a₁ := hf₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have a₃ := a₁.trans ((hδf τ _ (hth₁ _ ⟨τ, t₁⟩) _).trans (congrArg (_ * ·) a₂.symm))
    have a₄ := (hfr τ t₂ t₁).symm.trans a₃
    have hu : IsUnit (mat (C.dict₂ h).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h ⟨τ, t₂⟩).1)
    exact Matrix.map_injective τ.injective (hu.mul_right_cancel a₄)
  obtain ⟨f, hf⟩ := exists_latEquiv _ _ γ hlat
  let gam := (φ₂ (C.dict₂ h).1).trans (f.trans (φ₁ (T.dict j σ h).1).symm)
  have hgam : ∀ a, (φ₁ (T.dict j σ h).1 (gam a) : Fin D.R.r → D.host.E) =
      (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (φ₂ (C.dict₂ h).1 a : Fin D.R.r → D.host.E) := fun a =>
    (congrArg Subtype.val ((φ₁ (T.dict j σ h).1).apply_symm_apply _)).trans (hf _)
  obtain ⟨P₁, hP₁, hp₁, hu₁, hv₁⟩ := hper₁ _ ⟨x', hx'⟩
  obtain ⟨P₂, hP₂, hp₂, hu₂, hv₂⟩ := hper₂ _ ⟨x, hx⟩
  have hle : KA T.Q.l ≤ KA C.d.l₂ := by rw [KA, KA, hA, hA₂]
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  obtain ⟨k₁, k₂⟩ := point_over C.d hlev (by omega) hA hle
    (RingHom.ext fun a => (congrArg C.σ₂ (Subtype.ext rfl)).trans
      (RingHom.congr_fun hσ₂ ((IntermediateField.inclusion T.Q.c.le).toRingHom a)))
    e₁ e₂ F₁ F₂ _ _ hp₁ hp₂ gam
    (fun a b => by
      have := (hEF₁ _ (gam a) (gam b)).trans (Eq.trans (by rw [hgam, hgam, hiso, (hW₁ _).2, (hW₂ _).2])
        (hEF₂ _ a b).symm)
      exact_mod_cast this)
    (fun a ha => by
      have b₂ := hm₂ a ha
      rw [hlev.2.1] at b₂
      obtain ⟨u, hu, e⟩ := hδm T.Q.l.M C.d.pd (by have := T.Q.l.three_le; omega) _ _ _
        (hm₁ a (Submodule.smul_mono_left (Ideal.map_mono hlev.1.2.1) ha)) b₂
      refine ⟨(φ₁ _).symm ⟨u, hu⟩, (φ₁ (T.dict j σ h).1).injective (Subtype.ext ?_)⟩
      rw [hgam, hγδ, e, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
      rfl)
    (fun a i => by
      rw [hP₁, hP₂, hgam, Equiv.apply_symm_apply, hrel]
      exact perFr_move _ _ hΨ ((hU₁.2.1 _).1.trans (hU₂.2.1 _).1.symm) ((hW₁ _).1.trans (hW₂ _).1.symm) γ hiso x x'
        hxx _ _ _)
  exact ⟨by rw [hu₁, hu₂]; exact k₁, fun τ i => k₂ ⟨τ, i⟩ _ _ (hv₁ τ i) (hv₂ τ i)⟩

end GlobalTheory.CoverFrameOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralValuesEqualCharacteristic
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqCharCusp

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem exists_goodAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ∃ p : ℕ, p.Prime ∧ l.GoodAt p := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (l.M + 1)
  refine ⟨p, hp, ?_⟩
  have h3 := l.three_le
  have hM : ¬ p ∣ l.M := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  unfold Level.GoodAt
  rw [Nat.factorization_eq_zero_of_not_dvd hM]
  simpa using h3

theorem exists_place (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, -, hQ, hQl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int)]; exact bot_le)
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : ((p : ℤ)) ∈ Ideal.under ℤ Q := by
      rw [hQl]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hpQ⟩
  rw [h] at hQl
  change Ideal.comap (algebraMap ℤ (𝓞 K)) ⊥ = _ at hQl
  rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at hQl
  have : ((p : ℤ)) ∈ (⊥ : Ideal ℤ) := hQl ▸ Ideal.mem_span_singleton_self _
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 this))

theorem integral_of_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c r U hU a n f hd hf T hcnt io hint y
  obtain ⟨p, hp, hg⟩ := exists_goodAt l
  obtain ⟨la, hpl⟩ := exists_place c.F p hp
  let _ := io.toAlgebra
  obtain ⟨b, hb⟩ := exists_factor T (io.comp (la.valuation c.F).valuationSubring.subtype) (fun x => hint _)
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.1.x (spMap io) (y.1.x_over.trans (sp_comp _ _).symm)
  have hz₁ : z ≫ pullback.fst _ _ = y.1.x := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hA : ∀ Y : Model Xo c (la.valuation c.F).valuationSubring.subtype, PushInvertible Y.t.G Y.t.PP.L →
      ∀ y' : Sp T.V ⟶ Y.X, z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → Set.range y' ⊆ abLocus Y.t.G →
      evI y f ∈ (algebraMap T.V T.Fr).range := fun Y hP y' h3 hr =>
    GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T io hint y ⟨y', z, hz₁, hz₂, h3, hr⟩
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · obtain ⟨Y, hP⟩ := GlobalTheory.SupFinite.exists_model_rank_zero Xo c hD (la.valuation c.F).valuationSubring.subtype
    obtain ⟨⟨y', ⟨-, hz₃⟩, -⟩, -⟩ :=
      GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
    refine hA Y hP y' hz₃.symm ?_
    rw [GlobalTheory.DefiniteAbelian.abLocus_eq_univ (by omega) _ Y]
    exact Set.subset_univ _
  obtain ⟨Y, hP, hop, hS, h3, h4⟩ := exists_model (by omega) Xo c la p hp hpl hg
  obtain ⟨⟨y', ⟨hy', hz₃⟩, -⟩, -⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
  by_cases hr : Set.range y' ⊆ abLocus Y.t.G
  · exact hA Y hP y' hz₃.symm hr
  obtain ⟨T', g, ϖ, a₀, hg₁, hg₂, hϖ, hA'⟩ := _root_.GlobalTheory.ArcOfPoint.exists_arcIn_of_bad_reduction E H Dw l Xo c _ Y h3 hS T io b y' z hb hy' hz₂ hz₃.symm hr
  obtain ⟨i, ρ, hρ, hi, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' g hg₁ hg₂
  obtain ⟨y₁, φ, hφ, hy₁⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i ρ hρ
    (fun x _ => hv x)
  let _ := (i.comp io).toAlgebra
  have e₁ : (algebraMap T'.V T'.Fr).comp g = i.comp (algebraMap T.V T.Fr) := RingHom.ext fun x => (hi x).symm
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite c.F c.F.val.toRingHom T T' g hg₁ hg₂ hcnt (i.comp io)
  have hint' : ∀ k : c.F, (i.comp io) k ∈ (algebraMap T'.V T'.Fr).range := fun k => by
    obtain ⟨v, hv'⟩ := hint k
    exact ⟨g v, by rw [RingHom.comp_apply, ← hv', hi]⟩
  have key := GlobalTheory.T.cuspForm_integral_arc_section_equalChar E H Dw l Xo c r U hU la Y hP hop h4 a n f hd hf
    (fun T₁ io₁ h₁ y₂ hy₂ => GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T₁ io₁ h₁ y₂ hy₂)
    T' (i.comp io) hint' ⟨κ, hκ⟩ (g.comp b)
    (by rw [← RingHom.comp_assoc, e₁, RingHom.comp_assoc, hb]; rfl) ϖ hϖ a₀ (spMap g ≫ y')
    (by rw [Category.assoc, hy', sp_comp]) hA' y₁ (spMap i ≫ z)
    (by rw [Category.assoc, hz₁, hy₁.1, hφ]) (by rw [Category.assoc, hz₂, sp_comp])
    (by rw [Category.assoc, ← hz₃, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, e₁])
  have hE : GlobalTheory.Reg.EvLaws Xo c := by
    have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    obtain ⟨-, -, hwd, hwt, hint, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hB E H Dw l Xo c
    have hbc : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
      GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y
    exact ⟨hwd, _root_.GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c, hwt, hbc⟩
  have e₂ : evI y₁ f = φ (evI y f) :=
    (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf.1 T.Fr).1 _ φ _ _ hy₁
  have e₃ : φ (evI y f) = i (evI y f) := RingHom.congr_fun hφ _
  have key' : InV T' (i (evI y f)) := by rw [← e₃, ← e₂]; exact key
  rw [inV_iff, hv] at key'
  show InV T (evI y f)
  rw [inV_iff]
  exact nonneg_of_mul_nonneg_right key' (by exact_mod_cast hρ)

end GlobalTheory.EqCharCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSupSFinGL
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E]

open Classical

def idemOff (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E :=
  ⟨fun v => if v ∈ S then 0 else 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact zero_mem _
    · simp only [h, if_false]; exact one_mem _⟩

theorem pLoc_idemOff (S : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    pLoc E v (idemOff S) = if v ∈ S then 0 else 1 := rfl

theorem idemOff_mul_self (S : Finset (HeightOneSpectrum (𝓞 E))) : idemOff S * idemOff S = idemOff S :=
  FiniteAdeleRing.ext _ fun v => by
    change pLoc E v (idemOff S) * pLoc E v (idemOff S) = pLoc E v (idemOff S)
    rw [pLoc_idemOff]; split_ifs <;> simp

def cutS (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E →ₙ+* Af E where
  toFun x := idemOff S * x
  map_mul' x y := by
    calc idemOff S * (x * y) = (idemOff S * idemOff S) * (x * y) := by rw [idemOff_mul_self]
      _ = idemOff S * x * (idemOff S * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pLoc_cutS (S : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) (x : Af E) :
    pLoc E v (cutS S x) = (if v ∈ S then 0 else 1) * pLoc E v x := by
  change pLoc E v (idemOff S * x) = _
  rw [map_mul, pLoc_idemOff]

theorem map_pLoc_pFin_finGL {a : ℕ} (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a k) = Matrix.GeneralLinearGroup.map (pLoc E v) k := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun x : GL (Fin a) (Af E) => pLoc E v (x i j)) (pFin_finGL k)

theorem exists_mul_supS_finGL : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a),
    g ∈ GlobalTheory.CellDec.C0 E a S →
    ∃ u ∈ GlobalTheory.CellDec.NA E a, ∃ h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, ∃ k : GL (Fin a) (Af E),
      (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (n := a)) ∧ (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) ∧
      g = u * h * finGL E a k := by
  intro E _ _ a S g hg
  obtain ⟨u, hu, k₁, hk₁, rfl⟩ := hg
  set k : GL (Fin a) (Af E) := cornerGL a (cutS S) (Matrix.GeneralLinearGroup.map (pFin E) k₁) with hk
  have hkv : ∀ v, v ∉ S → Matrix.GeneralLinearGroup.map (pLoc E v) k =
      Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) k₁ := by
    intro v hv
    rw [hk, map_cornerGL_of_hom _ _ (pLoc E v) (fun x => by rw [pLoc_cutS, if_neg hv, one_mul])]
    exact Units.ext (Matrix.ext fun i j => rfl)
  have hkS : ∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1 := fun v hv =>
    map_cornerGL_of_zero _ _ (fun x => by rw [pLoc_cutS, if_pos hv, zero_mul]) _
  have hK : ∀ v, v ∉ S → Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) k₁ ∈ KGL v (n := a) := by
    intro v hv
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hk₁ v) hv
  refine ⟨u, hu, k₁ * (finGL E a k)⁻¹, ?_, k, fun v => ?_, hkS, ?_⟩
  · intro w hw
    rw [map_mul, map_inv, map_pLoc_pFin_finGL, hkv w hw, mul_inv_cancel]
  · by_cases hv : v ∈ S
    · rw [hkS v hv]; exact one_mem _
    · rw [hkv v hv]; exact hK v hv
  · group

end GlobalTheory.CellDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroDominantSectionEachComponent
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverNZ

theorem exists_sec_ne_zero_each_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ n : ℕ, Even n → ∃ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n ∧ ∀ k : (T.U j σ).Comp, ∃ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) f k x ≠ 0 := by
  intro D T hT j hj σ hσ n hn
  refine ⟨0, ⟨fun _ => antitone_const, hn⟩, fun k => ?_⟩
  have hU : IsUnf (T.U j σ) := hT.unf j hj σ hσ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  obtain ⟨x, hx⟩ : ((T.U j σ).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
  obtain ⟨x₀, hx₀, -⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU).1 k ⟨x, hx⟩
  obtain ⟨f, hf, h0⟩ := GlobalTheory.DictLevel.exists_sec_rdU_ne_zero (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU hr k n hn x₀ hx₀
  exact ⟨f, hf, x₀.1, x₀.2, h0⟩

end GlobalTheory.CoverNZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramifiedStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  first | exact @GlobalTheory.JR.gl_unimodular | exact GlobalTheory.JR.gl_unimodular | (intros; apply GlobalTheory.JR.gl_unimodular <;> assumption)
end

