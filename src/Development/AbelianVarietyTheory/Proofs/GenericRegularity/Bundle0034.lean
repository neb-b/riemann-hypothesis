module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnSmoothChart
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

theorem fn_continuousOn_good {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) (xR : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (hx : 0 < xR) (hfn : FnPin U xR fn)
    (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A]
    (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ))
    (y : X → FrPt Xo c (CAt σ)) (hφ : ∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W)
    (hy : ∀ x ∈ W, FrMap (φ x) yA (y x)) (i : Ix Dw) : ContinuousOn (fun x => |fn σ (y x) i|) W := by
  classical
  intro x₀ hx₀
  let ρ : X → (A →+* ℂ) := fun x => (φ x).toRingHom
  have hρ : ∀ x, (ρ x).comp (algebraMap c.F A) = σ := fun x => RingHom.ext fun a => (φ x).commutes a
  have hρc : ∀ a, ContinuousOn (fun x => ρ x a) W := hφ
  obtain ⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩ := _root_.GlobalTheory.SmoothPointFamily.exists_holomorphic_family c.F A σ (ρ x₀) (hρ x₀)
  let ψ' : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ) := fun b =>
    if h : b ∈ B then
      { (show A →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b h).1 a }
    else φ x₀
  have hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a := by
    intro b hb a
    simp only [ψ', dif_pos hb]
    rfl
  choose z hz using fun b => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c A (CAt σ) (ψ' b) yA
  have hcont := _root_.GlobalTheory.FrameNorm.fn_continuousOn_hol E H Dw l Xo c r U hU xR fn hx hfn σ hσ A yA m B ψ' z hB
    (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) i
  let p : X → (Fin m → ℂ) := fun x j => ρ x (s j)
  have hp : ContinuousWithinAt p W x₀ := continuousWithinAt_pi.2 fun j => hρc (s j) x₀ hx₀
  have hev : ∀ᶠ x in nhdsWithin x₀ W, ∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro a _
    have := Metric.tendsto_nhds.1 (hρc a x₀ hx₀) ε hε
    simpa only [dist_eq_norm] using this
  have key : ∀ x ∈ W, (∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε) → p x ∈ B ∧ y x = z (p x) := by
    intro x hxW h
    obtain ⟨h1, h2⟩ := hnear (ρ x) (hρ x) h
    refine ⟨h1, ?_⟩
    have e : ψ' (p x) = φ x := by
      refine AlgHom.ext fun a => ?_
      have := hψ' (p x) h1 a
      rw [show ψ (p x) = ρ x from h2] at this
      exact this
    have h3 := hz (p x)
    rw [e] at h3
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) (φ x) yA).1 _ _ (hy x hxW) h3
  have h0 := key x₀ hx₀ (fun a _ => by simpa using hε)
  have hc : ContinuousWithinAt (fun x => |fn σ (z (p x)) i|) W x₀ :=
    ContinuousAt.comp_continuousWithinAt (f := p) (g := fun b => |fn σ (z b) i|)
      (hcont.continuousAt (hB.mem_nhds h0.1)) hp
  refine hc.congr_of_eventuallyEq ?_ (by rw [h0.2])
  filter_upwards [hev, self_mem_nhdsWithin] with x h hxW
  rw [(key x hxW h).2]

theorem fn_continuousOn_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (σ : c.F →+* ℂ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ)) (y : X → FrPt Xo c (CAt σ)), (∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W) → (∀ x ∈ W, FrMap (φ x) yA (y x)) → ∀ i, ContinuousOn (fun x => |fn σ (y x) i|) W := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn σ A _ _ _ yA X _ W φ y hφ hy i
  by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
  · exact fn_continuousOn_good U hU xR fn hx hfn σ hσ A yA X W φ y hφ hy i
  · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
      have := Formalism.L2.PjFree.goodEmb_goodOf c σ
      unfold Formalism.L2.PjFree.goodOf at this
      rwa [if_neg hσ] at this
    choose z hz using fun x => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (conjAlg σ) (y x)
    have h := fn_continuousOn_good U hU xR fn hx hfn _ hσ' A yA X W (fun x => (conjAlg σ).comp (φ x)) z
      (fun a => Complex.continuous_conj.comp_continuousOn (hφ a))
      (fun x hxW => frMap_trans (Xo := Xo) (c := c) _ _ _ (φ x) (conjAlg σ) yA (y x) (z x) (hy x hxW) (hz x)) i
    exact h.congr fun x _ => (hfn.2 σ (y x) (z x) (hz x) i).symm

end GlobalTheory.FrameNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupBddAndSupREqSupN
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FrameNorm.RecSup

theorem supBdd_and_supR_eq_supN : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ), GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn → FnNe (T.Q.Xo j) T.Q.c fn ∧ (∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), SupBdd (T.Q.Xo j) T.Q.c fn (wtA w) w.n F.1 ∧ ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA w) w.n F.1 = (recB h.toLawsCore).supN j w sg F) ∧ ∀ (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)), SupRLeRec h j fn i η := by
  intro D T h j hj fn hfn
  have hx : 0 < xiR D := (GlobalTheory.PinNum.xiR_pos_le_one D T.Q h.pins.1).1
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ =>
    (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))
  have hmain : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      SupBdd (T.Q.Xo j) T.Q.c fn (wtA w) w.n F.1 ∧
        ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA w) w.n F.1 = (recB h.toLawsCore).supN j w sg F := by
    intro w F
    have hF : F.1 ∈ Formalism.L2.PjFree.cusp (T.Q.Xo j) T.Q.c (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (wtA w) w.n :=
      cutR_le T.C j w F.2
    obtain ⟨h1, h2⟩ := GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq _ _ _ _ _ _ _ _ hU _ fn hx hfn _ _ (dom_wtA w) _ hF
    refine ⟨h1, fun sg => (h2 sg).trans ?_⟩
    show _ = cutN T.C T.Ns j w sg F
    unfold cutN
    rw [if_pos hj]
    rfl
  exact ⟨(GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm _ _ _ _ _ _ _ _ hU _ fn hx hfn).1, hmain,
    fun i η sg => ((hmain _ η).2 sg).le⟩

end GlobalTheory.FrameNorm.RecSup
end

