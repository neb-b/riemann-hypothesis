module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0897

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionFamilyNoCommonZeroLargeWeight
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanFamily


set_option maxHeartbeats 1000000 in
theorem holSub0_le_span_cuspA_of_lastPos : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos (T.Q.Dw j) a →
    4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n →
    Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤
      Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j a n : Set (T.R j))) := by
  intro D T h j hj σ hσ a n hdom hlast hn
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    a n hdom hlast hn
    (fun k => h.chiTriv j hj σ hσ a n hdom k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hI
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let _ : Algebra K ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨κ.comp (Ideal.Quotient.mkₐ K M), fun x hx => ?_⟩
  show κ (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]

theorem evR_of_frMap {D : D7} (T : CoreJ D) (h : LawsJ T) {j : ℕ} (hj : Formalism.L2.Pj.InR D j) (f : T.R j)
    (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (p : TRing T.Q.c.F) (ψ : p.R →ₐ[T.Q.c.F] S)
    (y : FrPt (T.Q.Xo j) T.Q.c p.R) (z : FrPt (T.Q.Xo j) T.Q.c S) (hz : FrMap ψ y z) :
    evR (T.Q.Xo j) T.Q.c f z = ψ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) z :=
    ⟨p, ψ, y, hz⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact h.evalWD j hj f hf S _ p _ ψ _ y z hT.choose_spec.choose_spec.choose_spec hz


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem exists_family : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom b m ∧ (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) ∧ (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) ∧ ∀ P ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n), ∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  intro D T h j hj σ hσ a n hdom
  obtain ⟨b, m, hbm, hlast, hm, hnz⟩ := _root_.GlobalTheory.BpfUniform.exists_weight_noCommonZero D T h j hj σ hσ
  haveI : FiniteDimensional T.Q.c.F (T.cuspA j b m) := h.cuspFD j hj b m hbm
  haveI : Module.Free T.Q.c.F (T.cuspA j b m) := Module.Free.of_divisionRing _ _
  let B := Module.finBasis T.Q.c.F (T.cuspA j b m)
  have hsec : ∀ i, (B i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c b m := fun i => cusp_le_sec _ _ _ _ _ (B i).2
  refine ⟨b, m, _, fun i => (B i : T.R j), hbm, hsec, ?_, ?_⟩
  · intro p y
    by_contra hne
    have hL := (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1
    obtain ⟨ψ, hψ⟩ := exists_complex_point σ _ hne
    obtain ⟨z, hz⟩ := hL.bc p.R (CAt σ) ψ y
    have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (B i : T.R j) z = 0 := fun i => by
      rw [evR_of_frMap T h hj _ (hsec i).1 p ψ y z hz]
      exact hψ _ (Ideal.subset_span ⟨i, rfl⟩)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨k, x, t, ht⟩ := (h.unf j hj σ hσ).2.2.1 z
    have hx0 : ∀ i, rdU (T.U j σ) (B i : T.R j) k x.1 = 0 := fun i => by
      have hw := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hsec i) t _ z ht
      rw [hz0 i] at hw
      have hu : wchar (ex (T.Q.Dw j) b m) t ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (t c).ne_zero
      have h0 := (mul_eq_zero.1 hw.symm).resolve_left hu
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2]
      exact congrArg toC h0
    let ev : FDSec (T.U j σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k x.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hall : ∀ f ∈ T.cuspA j b m, rdU (T.U j σ) f k x.1 = 0 := by
      intro f hf
      have key : ∀ g : T.cuspA j b m, g ∈ Submodule.span T.Q.c.F (Set.range B) →
          rdU (T.U j σ) (g : T.R j) k x.1 = 0 := by
        intro g0 hg0
        induction hg0 using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨i, rfl⟩ := hg
          exact hx0 i
        | zero => rw [Submodule.coe_zero, map_zero]; rfl
        | add g g' _ _ hg hg' =>
          rw [Submodule.coe_add, map_add (f := _), Pi.add_apply, Pi.add_apply, hg, hg', add_zero]
        | smul c g _ hg =>
          rw [Submodule.coe_smul, map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hg, smul_zero]
      exact key ⟨f, hf⟩ (B.mem_span _)
    have hle : Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j b m : Set (T.R j))) ≤ LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hall f hf
    obtain ⟨P, hP, hPx⟩ := hnz k x.1 x.2
    exact hPx (hle (holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ b m hbm hlast hm hP))
  · intro P hP i
    have hrd : rdU (T.U j σ) (B i : T.R j) ∈ holSub (T.U j σ).X (laU (T.U j σ) b m) :=
      ((mem_cusp _ _ _ _ _ _).1 (B i).2).2 σ hσ
    have hdab : Dom (a + b) (n + m) := ⟨fun τ => (hdom.1 τ).add (hbm.1 τ), hdom.2.add hbm.2⟩
    have hprod : P * rdU (T.U j σ) (B i : T.R j) ∈
        Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (a + b) (n + m)) := by
      refine ⟨?_, fun k x hx => by simp [hP.2 k x hx]⟩
      have hP1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hP.1
      have hr1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hrd
      refine (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).2 fun k => ?_
      rw [show laU (T.U j σ) (a + b) (n + m) k = laU (T.U j σ) a n k + laU (T.U j σ) b m k from
        GlobalTheory.CuspProduct.laU_add (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) a b n m hdom.2 hbm.2 k]
      exact (siegelSpaceAlgebra_holds (E := D.host.E) D.R.r _ _ _ 0).2.1 _ (hP1 k) _ (hr1 k).1
    have hlast' : LastPos (T.Q.Dw j) (a + b) := fun τ hτ hm0 =>
      lt_of_lt_of_le (hlast τ hτ hm0) (by simp)
    have hs := holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ (a + b) (n + m) hdab hlast' (by omega) hprod
    exact Submodule.span_mono (Set.image_mono (cusp_le_sec _ _ _ _ _)) hs

end GlobalTheory.SpanFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitConstantCoverPullbackReading
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverConstAt


set_option maxHeartbeats 1600000 in
theorem rel_at : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h₀ : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h₀).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h₀).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h₀).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h₀).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ), mat (T.dict j σ h₀).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h₀).2 ⟨τ, h₂⟩) → ∀ (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp), (C.dict₂ h₀).1 = k₂ → (T.dict j σ h₀).1 = k → ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ((∀ τ i, ‖dmin (C.U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  intro D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr k₂ k hk₂ hk x x' hx hxx'
  subst hk₂ hk
  have hU := hT.unf j hj σ hσ
  have hU₂ := hC.2.2.2.1
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ :=
    fun τ => ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hx' : x' ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ γ ((hU.2.1 _).1.trans (hU₂.2.1 _).1.symm) hΨ hiso x x' hx hxx'
  obtain ⟨o₁, o₂⟩ := _root_.GlobalTheory.CoverFrameOver.un_over D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr x x' hx hx' hxx'
  obtain ⟨t, ht, hn, hr⟩ := GlobalTheory.CoverFrameMod.exists_scalar C hC.2.2.1 _ _ o₁ o₂
  refine ⟨hx', t, ht, fun hd => ?_, fun n a _ f hf f₂ _ hp => ?_⟩
  · have hd' : ∀ τ i, ‖dmin ((T.U j σ).X (T.dict j σ h₀).1).Gm x' τ i‖ = 1 := by
      rintro ⟨τ, h₁⟩ i
      rw [← hd ⟨τ, (hΨ τ).1 h₁⟩ i]
      unfold dmin
      rw [hxx' τ ((hΨ τ).1 h₁) h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso τ]
    obtain ⟨g, e, F, ik, φ, -, hP⟩ := hU.2.2.2.2.2
    obtain ⟨g₂, e₂, F₂, ik₂, φ₂, -, hP₂⟩ := hU₂.2.2.2.2.2
    obtain rfl : g₂ = g := Fin.equiv_iff_eq.1 ⟨e₂.trans e.symm⟩
    obtain ⟨P, -, p, u, -, N⟩ := hP _ ⟨x', hx'⟩
    obtain ⟨P₂, -, p₂, u₂, -, N₂⟩ := hP₂ _ ⟨x, hx⟩
    exact hn _ _ _ _ _ F F₂ _ _ P P₂ p p₂ u u₂ (N hd') (N₂ hd)
  · have e : rdU (T.U j σ) f (T.dict j σ h₀).1 x' =
        toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un (T.dict j σ h₀).1 ⟨x', hx'⟩)) := dif_pos hx'
    rw [e]
    exact (dif_pos hx).trans (hr n a f hf f₂ hp)

end GlobalTheory.CoverConstAt

namespace GlobalTheory.CoverConstAt


set_option maxHeartbeats 1600000 in
theorem const_of_rel : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∀ (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ((∀ τ i, ‖dmin (C.U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x') → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ k' : (T.U j σ).Comp, k = k' → ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k').Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k').Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k').dom ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k' x' := by
  intro D T hL j hj σ hσ C hC n k₂ k γ hx
  obtain ⟨hΨ, hla⟩ := GlobalTheory.CoverConst.psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ : Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ := by
    intro x τ h₂ h₁
    rfl
  have hGdom : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom := fun x hx' => (hx x (G x) hx' (hGrel x)).1
  have hGdiff : Differentiable ℂ G := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [G, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    fun_prop
  let ι := {p : ((D.host.E →+* ℂ) × ℕ → ℕ) × Rul (T.Q.Xo j) T.Q.c × Rul C.d.Xo₂ C.d.c₂ //
    Dom p.1 n ∧ p.2.1 ∈ sec (T.Q.Xo j) T.Q.c p.1 n ∧ p.2.2 ∈ sec C.d.Xo₂ C.d.c₂ p.1 n ∧ C.IsPull p.2.1 p.2.2}
  let P₂ : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i => rdU C.U₂ i.1.2.2 k₂
  let P : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i x => rdU (T.U j σ) i.1.2.1 k (G x)
  have hP₂d : ∀ i, DifferentiableOn ℂ (P₂ i) (C.U₂.X k₂).dom := fun i =>
    (hU₂.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.2 i.2.2.2.1 k₂).1
  have hPd : ∀ i, DifferentiableOn ℂ (P i) (C.U₂.X k₂).dom := fun i =>
    (hU₁.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.1 i.2.2.1 k).1.comp hGdiff.differentiableOn hGdom
  have hg : ∀ x ∈ (C.U₂.X k₂).dom, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i : ι, P₂ i x = c * P i x := by
    intro x hxd
    obtain ⟨b, hb, hyd, hyo⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_borel_orthonormal_move (C.U₂.X k₂) hxd
    obtain ⟨-, t, -, hmod, hrel⟩ := hx (rmul x b) (G (rmul x b)) hyd (hGrel _)
    have ht1 : ‖t‖ = 1 := hmod (fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_diagonal_minor_one _ hyo τ i)
    refine ⟨t ^ n, by rw [norm_pow, ht1, one_pow], ?_⟩
    rintro ⟨⟨a, f, f₂⟩, hDom, hf, hf₂, hP⟩
    let b₁ : Frame ((T.U j σ).X k).Ψ D.R.r := fun τ => b ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have hb₁ : b₁ ∈ Bor ((T.U j σ).X k).Ψ D.R.r := fun τ => hb ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have e1 := hrel n a hDom f hf f₂ hf₂ hP
    have e2 : rdU C.U₂ f₂ k₂ (rmul x b) = bchar (laU C.U₂ a n k₂) b * rdU C.U₂ f₂ k₂ x :=
      (hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂).2.1 x hxd b hb
    have e3 : G (rmul x b) = rmul (G x) b₁ := by
      funext τ
      simp only [G, rmul, b₁, mat]
      exact (Matrix.mul_assoc ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1) (mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩) (mat b ⟨τ.1, (hΨ τ.1).2 τ.2⟩)).symm
    have e4 : rdU (T.U j σ) f k (rmul (G x) b₁) = bchar (laU (T.U j σ) a n k) b₁ * rdU (T.U j σ) f k (G x) :=
      (hU₁.2.2.2.2.1 a n hDom f hf k).2.1 (G x) (hGdom x hxd) b₁ hb₁
    have e5 : bchar (laU C.U₂ a n k₂) b = bchar (laU (T.U j σ) a n k) b₁ := by
      unfold bchar
      refine Fintype.prod_equiv (Equiv.subtypeEquivRight (fun τ => hΨ τ)) _ _ (fun τ => ?_)
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hla a n τ.1 τ.2 ((hΨ τ.1).1 τ.2) i]
      rfl
    have e6 : bchar (laU C.U₂ a n k₂) b ≠ 0 := by
      unfold bchar
      refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
      have hdet : (mat b τ).det ≠ 0 := (hb τ).1
      rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)] at hdet
      simpa [mat] using Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    show rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k (G x)
    apply mul_left_cancel₀ e6
    rw [← e2, e1, e3, e4, ← e5]
    ring
  classical
  let g : Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun x => if h : x ∈ (C.U₂.X k₂).dom then (hg x h).choose else 1
  have hg1 : ∀ x ∈ (C.U₂.X k₂).dom, ‖g x‖ = 1 := fun x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.1
  have hgr : ∀ i, ∀ x ∈ (C.U₂.X k₂).dom, P₂ i x = g x * P i x := fun i x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.2 i
  obtain ⟨u, hu1, hu⟩ := GlobalTheory.CoverConst.eq_const_mul_of_norm_one (C.U₂.X k₂).dom (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected D.R.r (C.U₂.X k₂)).isPreconnected P₂ P g hP₂d hPd hg1 hgr
  refine ⟨u, hu1, ?_⟩
  rintro k' rfl x x' hxd hrel'
  refine ⟨(hx x x' hxd hrel').1, ?_⟩
  have hx' : x' = G x := by
    funext τ
    exact hrel' τ.1 ((hΨ τ.1).2 τ.2) τ.2
  intro a hDom f hf f₂ hf₂ hP
  rw [hx']
  exact hu ⟨(a, f, f₂), hDom, hf, hf₂, hP⟩ x hxd

end GlobalTheory.CoverConstAt

namespace GlobalTheory.CoverConstAt


set_option maxHeartbeats 1600000 in
theorem cover_read_const : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ u : C.U₂.Comp → ℂ, (∀ k, ‖u k‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ h : GA D (T.V j σ), rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = u (C.dict₂ h).1 * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  intro D T hL j hj σ hσ C hC n
  have hU := hL.unf j hj σ hσ
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  choose h₀ hh₀ using GlobalTheory.CoverOnto.exists_dict₂_comp D T hL j hj σ hσ C hC
  have hframes := fun k₂ : C.U₂.Comp => GlobalTheory.CoverFrameMove.frames_differ D T hL j hj σ hσ C hC (h₀ k₂)
  choose γ₀ hΛ hiso hfr using hframes
  have hconst := fun k₂ : C.U₂.Comp => const_of_rel D T hL j hj σ hσ C hC n k₂ (T.dict j σ (h₀ k₂)).1 (γ₀ k₂)
    (rel_at D T hL j hj σ hσ C hC (h₀ k₂) (γ₀ k₂) (hΛ k₂) (hiso k₂) (hfr k₂) k₂ _ (hh₀ k₂) rfl)
  choose u hu1 hu using hconst
  refine ⟨u, hu1, ?_⟩
  intro a hDom f hf f₂ hf₂ hP h
  have e₂ : (C.dict₂ h).1 = (C.dict₂ (h₀ (C.dict₂ h).1)).1 := (hh₀ _).symm
  have e₁ : (T.dict j σ (h₀ (C.dict₂ h).1)).1 = (T.dict j σ h).1 :=
    GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hL j hj σ hσ C hC _ h (hh₀ _)
  obtain ⟨δ, hδ, hδrel⟩ := _root_.GlobalTheory.CoverFrameArith.frame_move_arith D T hL j hj σ hσ C hC h (h₀ (C.dict₂ h).1) e₂ (γ₀ _) (hΛ _) (hiso _) (hfr _)
  have hΨ : ∀ τ, τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ ↔ τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ :=
    fun τ => ((hU₂.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm
  let x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r := fun τ =>
    ((γ₀ (C.dict₂ h).1 : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat (C.dict₂ h).2 ⟨τ.1, (hΨ τ.1).2 τ.2⟩ :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hxd : (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom := hC.2.2.2.2.1 h
  obtain ⟨hx'd, hr⟩ := hu (C.dict₂ h).1 _ e₁ (C.dict₂ h).2 x' hxd (fun τ h₂ h₁ => rfl)
  have hd : (T.dict j σ h).2 = lact δ x' := by
    funext τ
    exact hδrel τ.1 ((hΨ τ.1).2 τ.2) τ.2
  rw [hr a hDom f hf f₂ hf₂ hP, hd, (hU.2.2.2.2.1 a n hDom f hf _).2.2 δ hδ x' hx'd,
    hL.chiTriv j hj σ hσ a n hDom _ δ hδ, one_mul]

end GlobalTheory.CoverConstAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModIntStatement
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)), Irreducible lam → ∀ a : ℕ, Finite ↥(Xq ↥LL.1 lam a) := by
  first | exact @GlobalTheory.UseLoc.Cases.finite_Xq | exact GlobalTheory.UseLoc.Cases.finite_Xq | (intros; apply GlobalTheory.UseLoc.Cases.finite_Xq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialLieDerivativeEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.LieEquivFock

theorem lie_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (ψ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) → (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ' ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ' w'))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t τ Y hY ψ ψ' hψ hψ'
  obtain ⟨a, hL⟩ := _root_.GlobalTheory.FockDerivP.hasDerivAt_ptP D G Pl0 T A Ks R F hG hF i t τ Y hY
  have hinj : Function.Injective (R.ptP i t) := (GlobalTheory.CoefActIo.thetaVector_laws (i := i) hG.core t).2.2
  have hlin : ∀ (c : ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t (c • P) = c • R.ptP i t P := by
    intro c P
    unfold RealDat.ptP
    exact map_smul _ c P
  set Y' := (R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹
  set Lop : PolF D (Wc D i).rank (Vc D i).rank → PolF D (Wc D i).rank (Vc D i).rank :=
    fun P => fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ)) Y' P + a • P
    with hLop
  have hder : ∀ w, ψ' w = Lop (ψ w) := by
    intro w
    apply hinj
    funext z
    exact (hψ' w z).unique (hL (ψ w) z)
  intro u hu w'
  obtain ⟨c, g, hg⟩ := _root_.GlobalTheory.RealFockSubst.om_ptP_subst D G Pl0 T A Ks R F hG i t u hu
  have h1 : ψ ((R.cV i).ρ u w') = c • fockSubst (pS D i) g (ψ w') := by
    apply hinj
    rw [hψ u hu w', hg, hlin]
  have hcomm : ∀ Q, Lop (fockSubst (pS D i) g Q) = fockSubst (pS D i) g (Lop Q) := by
    intro Q
    simp only [hLop, map_add (f := _), map_smul]
    rw [GlobalTheory.T.fockPolynomialSubstitution_commute_targetGlAction]
  have hsm : ∀ x, Lop (c • x) = c • Lop x := by
    intro x
    simp only [hLop, map_smul, smul_add]
    rw [smul_comm a c]
  rw [hder, h1, hder, hg, ← hlin, hsm, hcomm]

end GlobalTheory.LieEquivFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPullbackUniformisedLevelCoverPlaces
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUpInt

theorem valuation_lt_one_iff {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    la.valuation K x < 1 ↔ 0 < vLa la x := by
  have h0 : la.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [vLa]
  omega

theorem overLa_comp {K K₂ : Type} [Field K] [NumberField K] [Field K₂] [NumberField K₂] (i : K →+* K₂)
    {la : HeightOneSpectrum (𝓞 K)} {la₂ : HeightOneSpectrum (𝓞 K₂)}
    (h : ∀ x : 𝓞 K, x ∈ la.asIdeal ↔ la₂.valuation K₂ (i x) < 1) {T : CDVR} {io₂ : K₂ →+* T.Fr} {e₂ : ℕ}
    (ho : OverLa la₂ T.V io₂ e₂) : ∃ e, OverLa la T.V (io₂.comp i) e := by
  obtain ⟨N, hN, hp⟩ := GlobalTheory.IntCoefExt.exists_nat_pos ho
  obtain ⟨la', e, ho'⟩ := GlobalTheory.IntCoefExt.exists_overLa (io₂.comp i) hN hp
  obtain rfl : la' = la := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp
    have hx' : (x : K) ≠ 0 := by simpa using hx
    have e1 := ho'.2 (x : K)
    rw [RingHom.comp_apply, ho.2] at e1
    rw [h, valuation_lt_one_iff la₂ ((map_ne_zero i).2 hx'), ← la'.valuation_lt_one_iff_mem (K := K)]
    refine (valuation_lt_one_iff la' hx').trans ?_
    have p1 : (0 : ℤ) < e := by exact_mod_cast ho'.1
    have p2 : (0 : ℤ) < e₂ := by exact_mod_cast ho.1
    rw [← mul_pos_iff_of_pos_left p1, ← e1, mul_pos_iff_of_pos_left p2]
  exact ⟨e, ho'⟩

theorem pull_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, (∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ la₂ ∈ S₂, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la₂, 0 ≤ v f₂ := by
  intro D T hT j hj σ _ C _ a n _ S S₂ hS f _ hint f₂ _ hP la₂ hla₂ v hv
  obtain ⟨⟨q, T', io₂, e₂, ho, y₂, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨la, hla, hl⟩ := hS la₂ hla₂
  obtain ⟨e, ho'⟩ := overLa_comp C.inc hl ho
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    intro e
    have h1 := GlobalTheory.Dict.sig_add_of_pins T.Q hT.pins hj
    obtain ⟨k, hk⟩ := r_odd D
    omega
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  have hO := GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA C.d
  have hK : KA T.Q.l ≤ KA C.d.l₂ := GlobalTheory.Models.RankZero.KA_le_of_eq_one hA _
  let io' : C.c'.F →+* T'.Fr := io₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)
  let io : T.Q.c.F →+* T'.Fr := io₂.comp C.inc
  have hio : ∀ x, io' (incF T.Q.c C.c' C.hle x) = io x := fun _ => rfl
  letI := io₂.toAlgebra
  letI := io'.toAlgebra
  letI := io.toAlgebra
  obtain ⟨y', hy'⟩ := GlobalTheory.CovPull.below_exists C.d hO hK (S := T'.Fr) (fun _ => rfl) y₂.1
  let y : IntFr (T.Q.Xo j) T.Q.c T' io := ⟨y'.res C.hle hio, GlobalTheory.TransferCompare.allTest_framed _ _ _ _,
    (GlobalTheory.IntCoefExt.integral_res_iff C.hle T' io' io hio _).1
      (GlobalTheory.CoverDown.integral_below C.d T' io' io₂ (fun _ => rfl) y' y₂.1 hy' y₂.2.2)⟩
  have e1 : evI y₂ f₂ = evI y f := hP T'.Fr hio (fun _ => rfl) y₂.1 y' hy'
  have key := hint la hla _ ⟨PtV.mk (PY := Unit) (lies := fun _ _ _ _ => True) la ho' y hy () trivial, rfl⟩
  refine (GlobalTheory.IntCoefExt.nval_nonneg_iff ho.1 _).2 ?_
  rw [e1]
  exact (GlobalTheory.IntCoefExt.nval_nonneg_iff ho'.1 _).1 key

end GlobalTheory.CoverUpInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCoboundaryReadOfTwistedCharacterCoboundaryStatement
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCoboundary_read_of_twistedCharacter_coboundary : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ)
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCob (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) := by
  first | exact @GlobalTheory.UseLoc.Cases.readC_cob | exact GlobalTheory.UseLoc.Cases.readC_cob | (intros; apply GlobalTheory.UseLoc.Cases.readC_cob <;> assumption)
end

