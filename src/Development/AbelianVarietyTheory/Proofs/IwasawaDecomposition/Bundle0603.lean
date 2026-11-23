module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadFromLocalization
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentClassifyingMapBijectiveOnGeometricPoints
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.ClsMap

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (Y' : Var F) (φ' : X.Fn →ₐ[F] Y'.Fn) (f' : Y'.X ⟶ X.X) (S' : Fr (ratOf Y') Dw.mult Dw.mult), Refines Eb S' φ' f' → ∃ h : C.Y.X ⟶ Y'.X, h ≫ f' = f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ C.Y.X => p ≫ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hjo hj f hπ f₀ Eb A₀ hT hL Y' φ' f' S' hR'

  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.FlagBundle.exists_isHom_base_of_lifts E H Dw l Xo c O β Z F e C X j hjo hj f hπ hL
  have hgen : genericPt C.Y ≫ f = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X := hφ
  have hx : genericPt C.Y ≫ C.π ≫ genι Z = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (φ : X.Fn →+* C.Y.Fn) inferInstance hst₀ hx hc).1 C.f0
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := fun τ =>
    (Mat.det_map A₀ (φ : X.Fn →+* C.Y.Fn) τ).trans_ne ((map_ne_zero _).2 (hA₀d τ))
  set A₁ : Mat Dw.mult C.Y.Fn := M * A₀.map φ with hA₁
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => by
    rw [hA₁, Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hMu M hM τ).ne_zero (hA₀φ τ)
  have hC : f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) := by
    rw [hA₁, mul_assoc, Mat.mul_inv hA₀φ, mul_one]; exact hM
  obtain ⟨E', hT', -⟩ := _root_.GlobalTheory.ShFam.FlagTie.exists_tied_isGraded E H Dw l Xo c O β Z F e C A₁ hA₁d
  have hsub := _root_.GlobalTheory.LieBase.FlagPull.frames_sub E H Dw l Xo c O β Z F e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hC
  have R₁ : Reps Eb E' φ f := ⟨hφ, hsub,
    _root_.GlobalTheory.ShFam.FieldLift.lifts_of_closed E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC hsub⟩
  have R₂ : Reps Eb S' φ' f' := hR'.reps

  obtain ⟨ψ, hψ, hG⟩ := GlobalTheory.T.exists_functionField_map_fullFlag_generic_point F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.ZH.RatModel.exists_isHom_of_map_O F Y'.Fn (ratOf Y') C.Y.Fn (ratOf C.Y) ψ
    (GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique hφ
  refine ⟨h, hf, fun K _ _ => _root_.GlobalTheory.FlagBundle.CoBear₂ F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ h hf
    (_root_.GlobalTheory.FlagBundle.coBear_comp_of_isHom F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ ψ hψ hG h hh) K⟩

end GlobalTheory.ShFam.ClsMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChart
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.ChartCoords

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem co_congr {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f f' g : EigFrame Z φ x}
    (h : ∀ τ i, f'.v τ i = f.v τ i) (τ : E →+* ℂ) : f'.co g τ = f.co g τ :=
  EigFrame.co_eq fun i => by rw [funext (h τ)]; exact f.co_spec g τ i

theorem v_of_isMap_trans {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {φ₁ : c.F →+* R₁} {x₁ : Sp R₁ ⟶ Z.X} {φ₂ : c.F →+* R₂} {x₂ : Sp R₂ ⟶ Z.X}
    {f : EigFrame Z φ x} {f₁ : EigFrame Z φ₁ x₁} {f₂ f₂' : EigFrame Z φ₂ x₂} {ψ₁ : R →+* R₁} {ψ₂ : R₁ →+* R₂}
    {ψ : R →+* R₂} (h₁ : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ₁ f₁) (h₂ : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f₁ embτ basisIdx) ψ₂ f₂) (h : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f₂') (hψ : ψ₂.comp ψ₁ = ψ)
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : f₂.v τ i = f₂'.v τ i := by
  rw [h₂ τ i, h₁ τ i, GlobalTheory.GradedPieces.dual_comp, hψ, h τ i]

end GlobalTheory.LieBase.ChartCoords

open GlobalTheory.ProjVar.Var GlobalTheory.LieBase.ChartCoords

theorem GlobalTheory.LieBase.coords_eq_ratVal_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ A : Mat Dw.mult X.Fn, ∃ M : Mat Dw.mult X.Fn, ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), A ∈ S.S (under z) → ∀ hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1, (∀ τ p q, RegAt (under z) (M τ p q)) ∧ (∃ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g) ∧ ∀ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g → ∀ f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hz) f → ∀ τ, f.co g τ = (M τ).map (fun r => ratVal r z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ e X j f₀ S A₀ hj _hoi hT V φ Φ hV A
  classical
  have hVa : IsAffineOpen V.1 := V.2
  haveI : Mono (LogKS.chart V) := inferInstanceAs (Mono hVa.fromSpec)
  have hmem : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 →
      under z ∈ j ⁻¹ᵁ V.1 := fun z hz => mem_ptsIn.1 hz
  by_cases hη : genericPoint X.X ∈ j ⁻¹ᵁ V.1
  swap
  · exact ⟨0, fun z _ hz => absurd (gen_mem (hmem z hz)) hη⟩
  have key : ∀ x : X.X, x ∈ j ⁻¹ᵁ V.1 → ∃ ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x,
      spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j := fun x hx =>
    TieBase.exists_affine_factor _ V.2 (by
      show j (X.X.fromSpecStalk x (IsLocalRing.closedPoint _)) ∈ V.1
      rw [Scheme.fromSpecStalk_closedPoint]; exact hx)
  have key' : ∀ (x : X.X) (ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x), spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j →
      spMap ((algebraMap (X.X.presheaf.stalk x) X.X.functionField).comp ψ) ≫ LogKS.chart V = genericPt X ≫ j :=
    fun x ψ h => by rw [TieBase.spMap_trans, Category.assoc, h, TieBase.genericPt_eq X x, Category.assoc]
  obtain ⟨ψη, hψη⟩ := key _ hη
  obtain ⟨ρ, h₀⟩ : ∃ ρ : Γ(gen Z, V.1) →+* X.X.functionField, spMap ρ ≫ LogKS.chart V = genericPt X ≫ j :=
    ⟨_, key' _ ψη hψη⟩
  have hφK : constF e X = ρ.comp φ := EigLoc.spMap_inj (by
    rw [← TieBase.genericPt_str e X j hj, ← h₀, Category.assoc, hV, ← TieBase.spMap_trans])
  obtain ⟨ΦK, hΦK⟩ := Φ.exists_isMap ρ hφK (x' := genericPt X ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← h₀, Category.assoc])
  refine ⟨fun τ => ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹, fun z hA hz => ?_⟩
  have hx := hmem z hz
  obtain ⟨φx, fz, hc⟩ := hT.2 (under z) A hA
  obtain ⟨ψx, hψx⟩ := key _ hx
  have hρx : (algebraMap _ X.X.functionField).comp ψx = ρ :=
    EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 ((key' _ ψx hψx).trans h₀.symm))
  have hφx : φx = ψx.comp φ := RingHom.ext fun a => IsFractionRing.injective (X.X.presheaf.stalk (under z))
    X.X.functionField (by
      have h1 := RingHom.congr_fun hc.2.1 a
      have h2 := RingHom.congr_fun hφK a
      rw [← hρx] at h2
      exact h1.symm.trans h2)
  obtain ⟨Φx, hΦx⟩ := Φ.exists_isMap ψx hφx (x' := stalkPt X (under z) ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← hψx, Category.assoc])
  have hM : ∀ fz' : EigFrame Z φx (stalkPt X (under z) ≫ j ≫ genι Z),
      fz'.Coord (algebraMap (X.X.presheaf.stalk (under z)) X.X.functionField) f₀ (A₀ * A⁻¹) → ∀ τ,
      ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := by
    intro fz' hc' τ
    obtain ⟨k, hk⟩ := fz'.exists_isMap _ hc'.2.1 hc'.1
    obtain ⟨Φk, hΦk⟩ := Φx.exists_isMap _ hc'.2.1 hc'.1
    have h1 : k.co f₀ τ = ((A₀ * A⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk τ)]; exact hc'.2.2 τ i
    have h3 : Φk.co k τ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := hΦk.co τ hk hc'.1
    have h4 : Φk.co f₀ τ = ΦK.co f₀ τ := co_congr (v_of_isMap_trans hΦx hΦk hΦK hρx) τ
    have h5 : f₀.co k τ = (k.co f₀ τ)⁻¹ := (Matrix.inv_eq_right_inv ((k.co_mul f₀ k τ).trans (k.co_self τ))).symm
    rw [← h3, ← Φk.co_mul f₀ k τ, h4, h5, h1]
  have hs : spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) = z.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1
  have hxz : (cxOf e σ hj z).1 ≫ genι Z = spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) ≫ j ≫ genι Z := by
    show (z.1 ≫ j) ≫ genι Z = _
    conv_lhs => rw [← hs]
    simp only [Category.assoc]
  refine ⟨fun τ p q => ?_, ?_, ?_⟩
  · beta_reduce
    rw [hM fz hc τ]
    exact ⟨Φx.co fz τ p q, rfl⟩
  · have hφ : σ = (Scheme.stalkClosedPointTo z.1).hom.comp φx := RingHom.ext fun a => by
      have h3 : φx a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
        ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under z)).commutes _).symm)
      show σ a = evStalk z (φx a)
      rw [h3]
      refine Eq.trans ?_ ((evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
      simp
    obtain ⟨g, hg⟩ := fz.exists_isMap _ hφ hxz
    exact ⟨g, φx, fz, _, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm, hc, hg⟩
  · rintro g ⟨φ', fz', ψ', hψ', hc', hm'⟩ f hf τ
    obtain rfl : ψ' = (Scheme.stalkClosedPointTo z.1).hom :=
      EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under z))).1
        (hψ'.symm.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm))
    obtain rfl : φ' = φx := RingHom.ext fun a => IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc'.2.1 a).symm.trans (RingHom.congr_fun hc.2.1 a))
    have hev : (Scheme.stalkClosedPointTo z.1).hom.comp ψx = evHom hz :=
      EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 (by
        rw [TieBase.spMap_trans, Category.assoc, hψx, LieMet.spMap_evHom hz, ← Category.assoc, hs]
        rfl))
    have hfx : Φx.IsMap (Scheme.stalkClosedPointTo z.1).hom f := fun τ i => by
      rw [hf τ i, hΦx τ i, GlobalTheory.GradedPieces.dual_comp, hev]
    beta_reduce
    rw [hfx.co τ hm' hxz, hM fz' hc' τ]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.map_apply]
    rw [GlobalTheory.TrueGeo.Res.ratVal_eq_valAt z ⟨_, rfl⟩, GlobalTheory.TrueGeo.Res.valAt_algebraMap]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphi
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem isHol_chart_framePt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _hσ hU X j hji hj c' k n W ψ hW hψW hψd
  classical
  haveI := hji
  have hU' : Formalism.L2.Pj.IsUnf U.toPj := (Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU
  by_cases hne : ((U.X k).dom).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom := fun x =>
      if h : x ∈ (U.X k).dom then ⟨x, h⟩ else ⟨x₀, hx₀⟩
    have hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
    have h1 := BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]
    have h2 := LocLift.isHolTo_comp_hom h1 T.Z.jQ
    have hψ : DifferentiableOn ℂ ψ W :=
      differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b
    have h3 := LocLift.isHolTo_comp h2 hW hψ hψW
    let P : V n → CxPts (genStr T.Z) σ := fun w => cxPt T.Z (U.un k (sf (ψ w)))
    have h4 : IsHolTo W fun w => (P w).1 := h3
    have hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w := fun w h => by
      simp only [P, hsf _ h]
    have hc : ContinuousOn P W := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4
    have hκ : Topology.IsOpenEmbedding (cxOf e σ hj) := isOpenEmbedding_cxOf e σ hj
    have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source) := by
      ext w
      constructor
      · rintro ⟨hw, h, y', hy', he⟩
        exact ⟨hw, y', hy', he.trans (hP w h)⟩
      · rintro ⟨hw, y', hy', he⟩
        exact ⟨hw, hψW w hw, y', hy', he.trans (hP w _).symm⟩
    let q : V n → CxPts X.str (σ.comp e.toRingHom) := fun w =>
      if h : ∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w then h.choose else c'.e.symm 0
    have hq : ∀ w, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w) →
        q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = P w := fun w h => by
      simp only [q, dif_pos h]
      exact h.choose_spec
    refine ⟨q, ?_, fun w _ h hex => ?_, ?_⟩
    · rw [hS]
      exact hc.isOpen_inter_preimage hW (hκ.isOpenMap _ c'.e.open_source)
    · rw [hP w h] at hex ⊢
      exact hq w hex
    · rw [hS, differentiableOn_euclidean]
      intro a
      have hd := (h4 (j ''ᵁ c'.U) ((j.appIso c'.U).inv.hom (c'.x a))).2
      refine (hd.mono fun w (hw : w ∈ W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source)) => ⟨hw.1, ?_⟩).congr fun w hw => ?_
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show ⊤ ≤ (P w).1 ⁻¹ᵁ _
        rw [← hq2]
        exact le_preimage_cxOf e σ hj c'.U (c'.source_subset hq1)
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show c'.e (q w) a = valAt' (P w).1 _ _
        rw [c'.apply_eq _ hq1 a, ev_eq_valAt'_cxOf e σ hj _ _ (c'.source_subset hq1), hq2]
  · have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun w hw => hne ⟨_, hw.2.1⟩
    refine ⟨fun _ => c'.e.symm 0, ?_, fun w _ h _ => absurd ⟨_, h⟩ hne, ?_⟩
    · rw [hS]
      exact isOpen_empty
    · rw [hS]
      exact differentiableOn_empty

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMonHomOfSquaredDegenerationDataFunctionalEquatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_of_squaredDegenerationData_functionalEquation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → (¬ ∀ j, (f 0).f j = 0) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  first | exact @GlobalTheory.PsiFourth.key | exact GlobalTheory.PsiFourth.key | (intros; apply GlobalTheory.PsiFourth.key <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperRelAmpleKTrivOfPull
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PolNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_generic_pull {S T : Type} [CommRing S] [IsDomain S] [CommRing T] [IsDomain T] (i : S →+* T)
    (hi : Function.Injective i) {t : SAB H (Sp S)} {t' : SAB H (Sp T)} (m : SABMap t' t (spMap i))
    (hg : GlobalTheory.LN.PolAt t (Out.jK S)) : GlobalTheory.LN.PolAt t' (Out.jK T) := by
  let ι : FractionRing S →+* FractionRing T :=
    IsLocalization.map (FractionRing T) i (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i hi)
  refine GlobalTheory.DatUniq.polAt_pull m hg (Out.jK T) (spMap ι) ?_
  simp only [spMap, Out.jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStarOfOfCover
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarCells

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem inCone_of_strict {m' n : ℕ} {σ : Fin m' → LinearMap.BilinForm ℤ X} (hσs : IsStrict bar φ σ)
    (hσl : φ.LinearOn σ) {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X)
    (hβp : ∀ i y, 0 ≤ β i y y) {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (σ j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • σ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hσs
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (σ j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β σ) (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (σ j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ σ).1 hσl b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he


omit [Module O X] [Module.Finite O X] in
theorem inRCone_of_nsmul {m : ℕ} {σ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    {d : Fin m → ℕ} (hk : 0 < k) (h : k • β = ∑ j, d j • σ j) : InRCone σ β := by
  refine ⟨fun j => (d j : ℝ) / k, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have e := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at e
  have e' : (k : ℝ) * (β a b : ℝ) = ∑ j, (d j : ℝ) * (σ j a b : ℝ) := by exact_mod_cast e
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ j, (d j : ℝ) * (σ j a b : ℝ)) / k by rw [← e']; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PolFan.StarCells

namespace GlobalTheory.PolFan.StarCells

theorem isStarOf_of_cover (hcover : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j))) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' := by
  intro E _ _ _ H q ψ w ψ' hψ hw h1 h2
  refine ⟨h1, h2, ?_⟩
  intro X _ _ _ _ hX n γ' hγ'
  set B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ j, (1 : ℝ) • toReal (γ' j) with hBdef
  have hB : B ∈ psdCone (bar := H.bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X n γ' _ hγ'.mem hγ'.nonneg fun _ => zero_le_one
  obtain ⟨S, -, hfin⟩ := (hψ X hX).finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hfin B hB
  set δ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hδdef
  have hδ : IsCell H.bar ψ δ := CarDim.isCell_pull_equiv hγ e.symm
  have hBδ : B = ∑ i, c i • toReal (δ i) := by
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simp only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hδdef, pull_apply,
      LinearEquiv.coe_coe]
    exact this
  have key : ∀ (k : ℕ) (σ : Fin k → LinearMap.BilinForm ℤ X), IsCell H.bar ψ' σ → B ∈ rcone σ →
      ∀ j, InRCone σ (γ' j) := by
    rintro k σ hσ ⟨t, ht, hBt⟩ j
    obtain ⟨kk, d, hk, hkd⟩ := inCone_of_strict hσ.strict hσ.linear hγ'.mem hγ'.nonneg (a := fun _ => 1) (b := t)
      (fun _ => zero_le_one) ht ((linearOn_iff ψ' γ').1 hγ'.linear _ fun _ => zero_le_one) hBt j one_ne_zero
    exact inRCone_of_nsmul hk hkd
  by_cases hc0 : ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ InRCone δ β ∧ w.evalZ β = 1
  · obtain ⟨β₀, hβ₀, hβ₀p, hin, hw1⟩ := hc0
    have hne : β₀ ≠ 0 := by
      intro h0
      have := (hw X hX).2.1 β₀ hβ₀ hβ₀p hw1 2 0 (by simp [h0])
      omega
    obtain ⟨m', s, h, hfc, hpos, hBc⟩ :=
      hcover X m δ β₀ B (fun i => (hδ.mem i).1) hδ.nonneg hne hin ⟨c, hc, hBδ⟩
    exact Or.inr ⟨m, δ, β₀, m', s, h, hδ, hβ₀, hβ₀p, hw1, hin, hfc, hpos,
      key _ _ (h2 X hX m δ hδ β₀ hβ₀ hβ₀p hw1 hin m' s h hfc hpos) hBc⟩
  · push_neg at hc0
    have h0 : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β = 0 := fun β hβ hp hi =>
      ((hw X hX).1 β hβ hp).resolve_right (hc0 β hβ hp hi)
    exact Or.inl ⟨m, δ, hδ, h0, key _ _ (h1 X hX m δ hδ h0) ⟨c, hc, hBδ⟩⟩

end GlobalTheory.PolFan.StarCells
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundBlocksOfBlockDiagonalStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_blocks_of_blockDiagonal : ∀ (n : ℕ) (S : Finset (Fin n)) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (G : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, (∀ a ∈ S, ‖v a‖ < 1 / 2) → (Matrix.blockDiagonal' fun τ => G τ v).det ≠ 0 → (∀ p q, ContDiffAt ℝ 2 (fun u => (Matrix.blockDiagonal' fun τ => G τ u) p q) v) → GlobalTheory.GoodMetric.GoodBound S c N (fun u => Matrix.blockDiagonal' fun τ => G τ u) v → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (G τ) v := by
  first | exact @GlobalTheory.GoodMetric.goodBound_of_blockDiagonal' | exact GlobalTheory.GoodMetric.goodBound_of_blockDiagonal' | (intros; apply GlobalTheory.GoodMetric.goodBound_of_blockDiagonal' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZeroStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab φ : InvFun O), IsCarrierDim bar q ψ lab → IsBaryStage bar q ψ lab φ 0 → SimpLab bar q φ lab := by
  first | exact @GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | exact GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | (intros; apply GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero <;> assumption)
end

