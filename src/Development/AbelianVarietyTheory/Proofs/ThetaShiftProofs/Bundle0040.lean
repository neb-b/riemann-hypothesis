module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsChartLoc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumThetaGeneratorChartRatio
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFrameChangeByConstantsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcFrame_change_by_constants : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th th' : a.D₀.P.L.Sec) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (r : A), ThNZ th → (∀ τ k, GtComb (g τ k) (e τ) (e' τ k)) → ThMul r th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y y' : FrPt Xo c S), Mono Y.j → IsArcFr W e th ι y → FrChg (fun τ => (g τ).map (ι.comp (PowerSeries.C (R := A)))) (ι (PowerSeries.C (R := A) r)) y y' → IsArcFr W e' th' ι y' := by
  exact GlobalTheory.ArcQ.isArcFr_of_frChg_const
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChainLevelPtOfSection
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem chain_levelPt_of_section (h1 : Out.Laws) (h2 : Out.Laws2) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ)
    (k : ℕ) [NeZero k] (p₀ : Out.QkPt a.D₀ (FractionRing ℂ) k) (ξ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G)
    (ξ₀ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : Λ.A.La)
    (hξ : ξ.left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ ξ₀.left)
    (hk : (k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ ξ = Y.oF.etaA v) ∨
      (k = l.M ∧ ∃ v ∈ idealPart D l, HEq p₀ (a.eta v) ∧ ξ = Y.oF.eta v))
    (hrep : Λ.Rep k p₀ la) : C.Φ.LevelPt k (toUnit _ ≫ ξ₀) la := by
  have hξw : ξ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w ξ
  have hY : (C.yF ≫ ξ.left ≫ Y.m.φ) ≫ Y.t.G.hom = gen ≫ χ := by
    have := Y.m.cart.1.w
    rw [Category.assoc, Category.assoc, this, ← Category.assoc ξ.left, hξw, Category.id_comp]
    exact C.yF_j
  let p : Over.mk gen ⟶ W.t.G :=
    Over.homMk (W.m.cart.1.lift (C.yF ≫ ξ.left ≫ Y.m.φ) gen hY) (W.m.cart.1.lift_snd _ _ _)
  have hp : p.left ≫ W.m.φ = C.yF ≫ ξ.left ≫ Y.m.φ := W.m.cart.1.lift_fst _ _ _
  let pY : Over.mk (gen ≫ χ) ⟶ Y.t.G := Over.homMk (C.yF ≫ ξ.left ≫ Y.m.φ) hY
  let pF : Over.mk C.yF ⟶ Y.oF.t.G := toUnit _ ≫ ξ
  have hpF : pF.left = C.yF ≫ ξ.left := rfl
  have hW := GlobalTheory.T.levelPoints_of_arc_eq_period_div_level h1 h2 E H D l Xo c O β Y (bF.comp β) a χ W Λ C.Ξ C.ΦW C.yF k p₀ ξ la p C.isGen C.yF_j
    hk hrep hp
  have h₂ := (_root_.GlobalTheory.LevelTransport.levelPt_isTan_iff E H _ _ Λ.A _ _ _ W.m C.w₂ _ _ C.ΦW C.ΦY C.rig₂.1 C.rel₂).1 k p pY la hp
  have h₁ := (_root_.GlobalTheory.LevelTransport.levelPt_isTan_iff E H _ _ Λ.A _ _ _ Y.m C.w₁ _ _ C.ΦF C.ΦY C.rig₁.1 C.rel₁).1 k pF pY la
    (by rw [hpF, Category.assoc]; rfl)
  have h₀ := (_root_.GlobalTheory.LevelTransport.levelPt_isTan_iff E H _ _ Λ.A _ _ _ Y.m0.toSABMap C.w₀ _ _ C.ΦF C.Φ C.rig₀.1 C.rel₀).1 k pF
    (toUnit _ ≫ ξ₀) la (by rw [hpF, Category.assoc, hξ, ← Category.assoc]; rfl)
  exact h₀.1 (h₁.2 (h₂.1 hW))

theorem chain_levels : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (laA laM : D.La → Λ.A.La), (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → (∀ v, C.Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) ∧ ∀ v ∈ idealPart D l, C.Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v) := by
  intro h1 h2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C laA laM hA hM
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.A (a.etaA v) (Y.oF.etaA v)
      (Xo.univ.etaA v) (laA v) (Y.m0.etaA v) (Or.inl ⟨rfl, v, HEq.rfl, rfl⟩) (hA v)
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.M (a.eta v) (Y.oF.eta v)
      (Xo.univ.eta v) (laM v) (Y.m0.eta v) (Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩) (hM v)

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GenericPointsConstantPointsFormalSumValues
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GenericPoints

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , ∃ Φ : GenPts Λ.A W.t gen, Ξ.IsGen Φ := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  have g := GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ
  have f := GlobalTheory.T.constantPointFrame_isFrame_with_rigidification h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ
  exact exists_genPts Λ.A W.t W.P.U.LG W.P.bundle Ξ.x Ξ.τ g.1 g.2 f.1 f.2
    (fun j _ α th hth => GlobalTheory.T.exists_section_values_formalThetaSum h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α th hth)
    (fun j _ σ => GlobalTheory.ConstSpan.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j σ)
    (fun k hk s => exists_clear W.P.U k hk s)

end GlobalTheory.GenericPoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumThetaGeneratorChartRatioStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_thetaGenerator_chart_ratio : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (φ : p.R →ₐ[c.F] ℂ⸨X⸩) (y₁ : FrPt Xo c ℂ⸨X⸩) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → OpenChart j y₀ → FrMap φ y₀ y₁ → FrChg G s y₁ y → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ yw : FrPt Xo c (CAt σ)) (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ), (∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.toC (ψ f))) → FrMap ψ y₀ yw₁ → yw.x = Fu.u Ha.i (Ha.Pw w) → AnGen Fu Ha.i (Ha.Pw w) yw (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) Θ.κ → FrChg Gw sw yw₁ yw → HasSum (fun m : ℤ => (s).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.toC sw) := by
  first | exact @GlobalTheory.ArcQ.hasSum_generator_ratio | exact GlobalTheory.ArcQ.hasSum_generator_ratio | (intros; apply GlobalTheory.ArcQ.hasSum_generator_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentConstantCoordsGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_constant_coords_generic_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback W.t.G.hom gen), Ξ.IsGen Φ → DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v.left → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → Φ.IsTan (h.symm z₀) νK := by
  first | exact @GlobalTheory.ConstTan.isTan_of_diffHyp | exact GlobalTheory.ConstTan.isTan_of_diffHyp | (intros; apply GlobalTheory.ConstTan.isTan_of_diffHyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointsFramesEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstRational

section Sums
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem fsum_mem (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (hth : th ∈ A.Theta j α) (v : A.V) :
    A.FSum j α th v ∈ Conv.convLaurent := by
  obtain ⟨T, hT⟩ := exists_formal_convergence O A
  obtain ⟨h, -⟩ := ((hT T le_rfl j).1 α th hth).1 v
  exact Conv.halfRing_le_convLaurent T h

theorem exists_shift_mem (k : ℕ) [NeZero k] (la : A.La) (hla : ∀ α, (k : ℤ) ∣ A.be la.y α) :
    ∃ ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩,
      ∀ i z, IsFShift A k i.1 i.2 la z (ψ i z) ∧ ψ i z ∈ Conv.convLaurent := by
  obtain ⟨cz, -, h⟩ := _root_.GlobalTheory.ArcPts.theta_sum_shift O A k la hla
  choose th' hth' _ h' using h
  refine ⟨fun i z => HahnSeries.single (A.be la.y i.1 / k) (cz z) *
    A.FSum k (i.1 + la.y) (th' i.1 i.2 i.2.2) z, fun i z => ⟨((h' i.1 i.2 i.2.2 z).1 _).2 rfl, ?_⟩⟩
  exact mul_mem (Conv.halfRing_le_convLaurent 0 (Conv.single_mem_halfRing 0 _ _))
    (fsum_mem A k _ _ (hth' _ _ _) z)

end Sums

theorem points_frames_eq (L₁ : Out.Laws) (L₂ : Out.Laws2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} [StarRing (𝓞 E)] {D : Datum H} {l : Level H} {Xo : Moduli D l} {A : AnArc (𝓞 E)}
    (σ : KA l →+* ℂ) {y : Sp ℂ⸨X⸩ ⟶ Xo.X} (Φ : GenPts A Xo.univ.t y) (laA laM : D.La → A.La) (hA : AnFin A)
    (hy : y ≫ Xo.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ))
    (levA : ∀ v, Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v))
    (levM : ∀ v ∈ idealPart D l, Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v))
    {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (f g : ℂ⸨X⸩ →+* F)
    (hfg : ∀ a ∈ Conv.convLaurent, f a = g a) (v : A.V) :
    spMap f ≫ (Φ.x v).left = spMap g ≫ (Φ.x v).left ∧
      ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → f (Φ.τ v j) = g (Φ.τ v j) := by
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  let φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F := fun j i v =>
    if h : j = 0 then 0 else haveI : NeZero j := ⟨h⟩; f (A.FSum j i.1 i.2 v)
  have hf : ∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v) := fun j _ i v =>
    dif_neg (NeZero.ne j)
  have hg : ∀ (j : ℕ) [NeZero j] i v, φ j i v = g (A.FSum j i.1 i.2 v) := fun j _ i v =>
    (hf j i v).trans (hfg _ (fsum_mem A j _ _ i.2.2 v))
  obtain ⟨Θ₁, x₁, l₁⟩ := GlobalTheory.T.exists_arcGenericFibrePoints_baseChange E H Xo.X A Xo.univ.t y Φ F f φ hA hf
  obtain ⟨Θ₂, x₂, l₂⟩ := GlobalTheory.T.exists_arcGenericFibrePoints_baseChange E H Xo.X A Xo.univ.t y Φ F g φ hA hg
  have lev : ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : A.La),
      Φ.LevelPt k (toUnit _ ≫ ξ) la → ∃ ψ, Θ₁.Lev k (toUnit _ ≫ ξ) ψ ∧ Θ₂.Lev k (toUnit _ ≫ ξ) ψ := by
    intro k _ ξ la h
    obtain ⟨ψ, hψ⟩ := exists_shift_mem A k la h.2.1.2
    refine ⟨fun i z => f (ψ i z), l₁ k ξ la ψ h fun i z => (hψ i z).1, ?_⟩
    have e : (fun i z => f (ψ i z)) = fun i z => g (ψ i z) :=
      funext fun i => funext fun z => hfg _ (hψ i z).2
    rw [e]
    exact l₂ k ξ la ψ h fun i z => (hψ i z).1
  have hs : (spMap f ≫ y) ≫ Xo.s = (spMap g ≫ y) ≫ Xo.s := by
    have e : f.comp ((algebraMap ℂ ℂ⸨X⸩).comp σ) = g.comp ((algebraMap ℂ ℂ⸨X⸩).comp σ) :=
      RingHom.ext fun a => hfg _ (Conv.convLaurent.algebraMap_mem (σ a))
    rw [Category.assoc, Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  obtain ⟨e₁, e₂⟩ := _root_.GlobalTheory.FamilyUnique.points_frames_eq L₁ L₂ E H D l Xo F A.V _ _ φ _ _ Θ₁ Θ₂ hs
    (fun v => lev _ _ _ (levA v)) (fun v hv => lev _ _ _ (levM v hv)) v
  refine ⟨(x₁ v).1.symm.trans (e₁.trans (x₂ v).1), fun j hj => ?_⟩
  rw [← (x₁ v).2 j hj, ← (x₂ v).2 j hj]
  refine e₂ j ?_
  rw [(x₁ v).1]
  exact fun p _ => hj (Set.mem_univ (spMap f p))

theorem rational : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) (σ : KA l →+* ℂ) (y : Sp ℂ⸨X⸩ ⟶ Xo.X) (Φ : GenPts A Xo.univ.t y) (laA laM : D.La → A.La), AnFin A → y ≫ Xo.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ) → (∀ v, Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) → (∀ v ∈ idealPart D l, Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v)) → Φ.Rational := by
  intro L₁ L₂ E _ _ _ H _ D l Xo A σ y Φ laA laM hA hy levA levM
  haveI : CharZero ℂ⸨X⸩ := algebraRat.charZero _
  haveI : CharZero Conv.convLaurent := algebraRat.charZero _
  have key := fun s : AlgebraicClosure ℂ⸨X⸩ ≃ₐ[Conv.convLaurent] AlgebraicClosure ℂ⸨X⸩ =>
    points_frames_eq L₁ L₂ σ Φ laA laM hA hy levA levM
      ((s : AlgebraicClosure ℂ⸨X⸩ →+* AlgebraicClosure ℂ⸨X⸩).comp (algebraMap ℂ⸨X⸩ _))
      (algebraMap ℂ⸨X⸩ (AlgebraicClosure ℂ⸨X⸩)) (fun a ha => s.commutes (⟨a, ha⟩ : Conv.convLaurent))
  refine ⟨fun v => ?_, fun v j hj => ?_⟩
  · refine (FixedPoint.existsUnique_factor (K₀ := Conv.convLaurent) (L := AlgebraicClosure ℂ⸨X⸩)
      (Φ.x v).left fun s => ?_).exists
    have h := (key s v).1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact h
  · obtain ⟨a, ha⟩ := FixedPoint.mem_range_of_algebraMap_fixed (K₀ := Conv.convLaurent)
      (L := AlgebraicClosure ℂ⸨X⸩) (Φ.τ v j) fun s => (key s v).2 j hj
    exact ha ▸ a.2

end GlobalTheory.ConstRational
end

