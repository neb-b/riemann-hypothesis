module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorsOfHodgeTateChartBou
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamily

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorsOfHodgeTateChartBouStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characters_boundedMinors_of_hodgeTateChartBound : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F) := by
  first | exact @GlobalTheory.ChartCharacter.characters_exist_of_chartBound | exact GlobalTheory.ChartCharacter.characters_exist_of_chartBound | (intros; apply GlobalTheory.ChartCharacter.characters_exist_of_chartBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.LevelCusp

theorem apply_of_cols {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ))
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (cf : ∀ τ, Fin (m τ) → Fin (m τ) → ℂ)
    (hcol : ∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ j, cf τ i j • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) (z : Fin g → ℂ) (τ : α) (i : Fin (m τ)) :
    h z (e.symm ⟨τ, i⟩) = ∑ j, cf τ j i * z (e.symm ⟨τ, j⟩) := by
  classical
  refine Pi.single_induction (p := fun z => h z (e.symm ⟨τ, i⟩) = ∑ j, cf τ j i * z (e.symm ⟨τ, j⟩)) z (by simp)
    (fun z w hz hw => by simp only [map_add (f := _), Pi.add_apply, hz, hw, mul_add, Finset.sum_add_distrib]) fun n a => ?_
  · beta_reduce
    obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective n
    have h1 : (Pi.single (e.symm ⟨τ', i'⟩) a : Fin g → ℂ) = a • (Pi.single (e.symm ⟨τ', i'⟩) 1 : Fin g → ℂ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [h1, map_smul, hcol]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases hτ : τ = τ'
    · subst hτ
      simp [mul_comm]
    · simp [hτ]


set_option maxHeartbeats 1000000 in
theorem exists_isometry_tri_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → ∃ (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i = ∑ j ∈ Finset.range (Dw.mult τ), A τ i j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (i : Fin (Dw.mult τ)), A τ i i = Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ hU ρ ν k k' x x' y' t hM hB
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k x
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p'
    (by rw [← hPx, ← hPx', ← hB.1]; exact hM.1.symm)
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P' p' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ i)
      (y'.u τ i)).1 (hPx' ▸ hcf3 τ i)
    have d0 := FibreDeriv.isDerivAt0_comp (hv τ i) ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    rw [hM.2.1] at d1
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  refine ⟨(φ k).symm ≪≫ₗ gam ≪≫ₗ φ k',
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun τ i j hji => ?_,
    fun τ i hi v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dite_eq_left ⟨hi, j.2⟩]
    rfl
  · beta_reduce
    rw [dite_eq_left ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.LevelCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_productData_copies_trivialisation_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → (∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q) ∧ ∀ n : ℕ, ∃ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G') (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_ : UnifPowOf3 pD pA pG U' P.U) (_ : Module (𝓞 E) D'.toPre.X) (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧ (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∀ (α : 𝓞 E) (N : ℕ), 0 < N → α * star α = (N : 𝓞 E) → ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' α 1 N θ θα := by
  first | exact @GlobalTheory.PowData.exists_powData | exact GlobalTheory.PowData.exists_powData | (intros; apply GlobalTheory.PowData.exists_powData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometryStatement
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_isometry_of_trace_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  first | exact @GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry | exact GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry | (intros; apply GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translated_normalisedPullback_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G), b ^ N = 1 → ∃ hh, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh := by
  first | exact @GlobalTheory.exists_isTransPull | exact GlobalTheory.exists_isTransPull | (intros; apply GlobalTheory.exists_isTransPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.MoveValues

open GlobalTheory.MoveCalc

noncomputable abbrev cpt : Sp ℂ := IsLocalRing.closedPoint ℂ

noncomputable def ev : (Sp ℂ).presheaf.stalk cpt →+* ℂ := (stalkClosedPointIso (CommRingCat.of ℂ)).hom.hom

theorem mem_iff {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) : f cpt ∈ U ↔ ⊤ ≤ f ⁻¹ᵁ U :=
  ⟨fun h p _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) p cpt]
    exact h, fun h => h trivial⟩

theorem ev_gs {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)) :
    ev (gs f cpt U a) = valAt' f U a := by
  have h' := (mem_iff f U).1 h
  rw [gs_eq f cpt U h, valAt', dite_eq_left h', valAt, ← germ_stalkClosedPointIso_hom (CommRingCat.of ℂ)]
  exact congrArg ev (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') cpt trivial _).symm

theorem ev_gm {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)ˣ) :
    ev (gm f cpt U a).val = valAt' f U a.val :=
  (congrArg ev (gs_unit f cpt U h a).symm).trans (ev_gs f U h _)

section General

variable {X Y Y' : Scheme.{0}} {L : LB X} {F : X ⟶ X}

theorem mem_div {p : Sp ℂ ⟶ X} {i j : L.ι} :
    ⊤ ≤ p ⁻¹ᵁ (LB.div (L.pull F) L).U ((fun _ => i), j) ↔ F (p cpt) ∈ L.U i ∧ p cpt ∈ L.U j :=
  (mem_iff p _).symm.trans (and_congr_left' (mem_pull (F := F) (J := fun _ => i)))

theorem ev_gw (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    ev (gw w p cpt i j).val =
      valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val :=
  ev_gm p _ (show p cpt ∈ (L.pull F).U (fun _ => i) ⊓ L.U j from ⟨mem_pull.2 hi, hj⟩) _

theorem val_ne (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val ≠ 0 := by
  rw [← ev_gw w p hi hj]
  exact ((gw w p cpt i j).isUnit.map ev).ne_zero

theorem val_pgen {w : LB.Iso L (L.pull F)} (h : PGen w) (p : Sp ℂ ⟶ X) {i j i' j' : L.ι}
    (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) (hi' : F (p cpt) ∈ L.U i') (hj' : p cpt ∈ L.U j') :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' p (L.U j ⊓ L.U j') (L.g j j').val =
      valAt' (p ≫ F) (L.U i ⊓ L.U i') (L.g i i').val *
        valAt' p ((LB.div (L.pull F) L).U ((fun _ => i'), j')) (w.s ((fun _ => i'), j')).val := by
  have e : gw w p cpt i j * gm p cpt _ (L.g j j') = gm (p ≫ F) cpt _ (L.g i i') * gw w p cpt i' j' := by
    rw [h _ p cpt i i' j j' hi hi' hj hj', mul_right_comm, inv_mul_cancel_right]
  rw [← ev_gw w p hi hj, ← ev_gw w p hi' hj', ← ev_gm p (L.U j ⊓ L.U j') ⟨hj, hj'⟩,
    ← ev_gm (p ≫ F) (L.U i ⊓ L.U i') ⟨hi, hi'⟩, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, e]

theorem val_pmaps {w : LB.Iso L (L.pull F)} {e : Y ⟶ X} {t : LB.Gen (L.pull e)} {ρ : Y ⟶ Y} (he : e ≫ F = ρ ≫ e)
    (h : PMaps w (K := PUnit) (fun _ => e) (fun _ => e) (fun _ => 1) t t ρ) (x : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((x ≫ e) cpt) ∈ L.U i) (hj : (x ≫ e) cpt ∈ L.U j) :
    valAt' (x ≫ ρ) ((L.pull e).U (fun _ => i)) (t.s (fun _ => i)).val =
      valAt' (x ≫ e) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' x ((L.pull e).U (fun _ => j)) (t.s (fun _ => j)).val := by
  have A := h _ x cpt (fun _ => i) (fun _ => j) (fun _ => hi) (fun _ => hj)
  rw [Fintype.prod_unique, zpow_one] at A
  have m : (x ≫ ρ) cpt ∈ (L.pull e).U (fun _ => i) := mem_pull.2 (by
    have h' : (e ≫ F) (x cpt) ∈ L.U i := hi
    rw [he] at h'
    exact h')
  rw [← ev_gw w (x ≫ e) hi hj, ← ev_gm (x ≫ ρ) _ m, ← ev_gm x ((L.pull e).U (fun _ => j)) (mem_pull.2 hj),
    ← map_mul, ← Units.val_mul]
  exact congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val) A

theorem val_carry {w : LB.Iso L (L.pull F)} {q : Y ⟶ X} {q' : Y' ⟶ X} {pm : Y ⟶ Y'} (hpm : pm ≫ q' = q ≫ F)
    {a : Fam L q} {a' : Fam L q'} (h : Carry w pm a a') (pt : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((pt ≫ q) cpt) ∈ L.U i) (hj : (pt ≫ q) cpt ∈ L.U j) :
    valAt' (pt ≫ pm) _ (a' fun _ => i) =
      valAt' (pt ≫ q) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' pt _ (a fun _ => j) := by
  have m : (pt ≫ pm) cpt ∈ LB.wchart L (fun _ : Fin 1 => q') (fun _ => i) := mem_chart.2 (by
    have h' : (q ≫ F) (pt cpt) ∈ L.U i := hi
    rw [← hpm] at h'
    exact h')
  rw [← ev_gw w (pt ≫ q) hi hj, ← ev_gs (pt ≫ pm) _ m,
    ← ev_gs pt (LB.wchart L (fun _ : Fin 1 => q) (fun _ => j)) (mem_chart.2 hj), ← map_mul]
  exact congrArg ev (h _ pt cpt i j hi hj)

end General

theorem frMove_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y y' : FrPt Xo c (CAt σ)), FrMove ρ ν y y' → ∃ (O : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → Xo.univ.t.G.left.Opens) (ω : ∀ i j, Γ(Xo.univ.t.G.left, O i j)), (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j ↔ (⊤ ≤ (p ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ p ⁻¹ᵁ Xo.univ.t.PP.L.U j)) ∧ (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0) ∧ (∀ i j i' j' (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' → valAt' p (O i j) (ω i j) * valAt' p (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val = valAt' (p ≫ ν.φ) (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * valAt' p (O i' j') (ω i' j')) ∧ (∀ i j (x : Sp ℂ ⟶ Xo.X) (p : Sp ℂ ⟶ Xo.univ.t.G.left), p = x ≫ eSec Xo.univ.t.G → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' (x ≫ ρ) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val = valAt' p (O i j) (ω i j) * valAt' x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧ ∀ i j (pt : Sp ℂ ⟶ Gx y.x) (pt' : Sp ℂ ⟶ Gx y'.x) (p : Sp ℂ ⟶ Xo.univ.t.G.left), pt ≫ Formalism.L2.PjFree.gxFst y.x = p → pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) → pt' ≫ Formalism.L2.PjFree.gxFst y'.x = p ≫ ν.φ → pt' ≫ Formalism.L2.PjFree.gxSnd y'.x = 𝟙 (Sp ℂ) → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' pt' ((PPx y'.x).U (fun _ => i)) (y'.s.f (fun _ => i)) = valAt' p (O i j) (ω i j) * valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) := by
  intro E _ _ _ H Dw l Xo c σ ρ ν y y' h
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := frMove_iff_carry.1 h
  obtain ⟨g, r, -⟩ := (cubIso_iff ν w).1 hw
  refine ⟨fun i j => (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j),
    fun i j => (w.s ((fun _ => i), j)).val, fun i j p => ?_, fun i j p hp => ?_, fun i j i' j' p hp hp' => ?_,
    fun i j x p e hp => ?_, fun i j pt pt' p e₁ e₂ e₃ e₄ hp => ?_⟩
  · exact mem_div.trans (and_congr (mem_iff (p ≫ ν.cm.F) _) (mem_iff p _))
  · exact val_ne w p (mem_div.1 hp).1 (mem_div.1 hp).2
  · exact val_pgen g p (mem_div.1 hp).1 (mem_div.1 hp).2 (mem_div.1 hp').1 (mem_div.1 hp').2
  · subst e
    have A := val_pmaps ν.cm.e_comm r x (mem_div.1 hp).1 (mem_div.1 hp).2
    rw [ν.base] at A
    exact A
  · subst e₁
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact e₄.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · exact e₃.trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm)
    exact val_carry hs hc pt (mem_div.1 hp).1 (mem_div.1 hp).2

end GlobalTheory.MoveValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove
section
noncomputable section

namespace GlobalTheory.LevelCusp.Transport

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LevelCusp
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
open GlobalTheory.Dict (castFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem integral_eq_zero_cast {α : Type} {Ψ Ψ' : Finset α} (h : Ψ = Ψ') {L : AddSubgroup (Ψ → ℝ)}
    {L' : AddSubgroup (Ψ' → ℝ)} [Countable L] [Countable L'] {D : Set (Ψ → ℝ)} {D' : Set (Ψ' → ℝ)}
    {g : (Ψ → ℝ) → ℂ} {g' : (Ψ' → ℝ) → ℂ} {c : ℂ}
    (hg : ∀ s, g s = c * g' (fun τ => s ⟨τ.1, h ▸ τ.2⟩))
    (hD : IsAddFundamentalDomain L D volume) (hD' : IsAddFundamentalDomain L' D' volume)
    (hf : volume D < ⊤) (hf' : volume D' < ⊤) (hp' : 0 < volume D') (hc : Continuous g)
    (hb : ∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) (hL : ∀ p ∈ L, ∀ s, g (p + s) = g s)
    (hL' : ∀ p ∈ L', ∀ s, g' (p + s) = g' s) (h0 : ∫ s in D', g' s = 0) : ∫ s in D, g s = 0 := by
  subst h
  have hg' : ∀ s, g s = c * g' s := hg
  have key := GlobalTheory.mean_fundamentalDomain_eq_of_periodic Ψ L L' D D' g hD hD' hf hf' hc hb (fun p hp s => by rw [add_comm, hL p hp])
    (fun p hp s => by rw [hg', hg', add_comm, hL' p hp])
  have e : ∫ s in D', g s = 0 := by
    simp only [hg']
    rw [integral_const_mul, h0, mul_zero]
  rw [e, mul_zero] at key
  refine (mul_eq_zero.1 key.symm).resolve_left ?_
  exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne'

variable {X X' : Data E r} {a : GL (Fin r) E}

theorem nfac_eq (h : IsMatch X X' a) {la : Wt X.Ψ r} {la' : Wt X'.Ψ r}
    (hl : ∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) (x : Frame X.Ψ r) :
    X'.nfac la' (lact a (castFr h.psi x)) = X.nfac la x := by
  unfold Data.nfac
  simp only [h.dmin_eq]
  exact (GlobalTheory.Dict.Pull.cast_wt h.psi rfl hl (castFr h.psi x)).symm

theorem isIso_map (h : IsMatch X X' a) {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X'.IsIso ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) := by
  refine ⟨(h.lat ξ).1 hξ.1, by rw [h.iso, hξ.2.1], fun e => hξ.2.2 ?_⟩
  rw [← GlobalTheory.Dict.Pull.inv_mulVec a ξ, e, Matrix.mulVec_zero]

theorem map_mul_flowMat (h : IsMatch X X' a) (ξ : Fin r → E) (τ : X'.Ψ) (s : ℂ) :
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ ⟨τ.1, h.mem τ⟩ s =
      X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ s * (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
  have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hc : X'.c τ = X.c ⟨τ.1, h.mem τ⟩ := by simp only [Data.c, h.xi]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he, h.hermC_eq, hc,
    Matrix.mulVec_add, Matrix.mulVec_smul]

theorem lact_flow (h : IsMatch X X' a) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (castFr h.psi (X.flow ξ s x)) =
      X'.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => s ⟨τ.1, h.mem τ⟩) (lact a (castFr h.psi x)) := by
  funext τ
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) *
      mat x ⟨τ.1, h.mem τ⟩) = X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, map_mul_flowMat h]

theorem freq_zero (X : Data E r) (la : Wt X.Ψ r) :
    ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, (0 : X.Ψ → ℝ) τ * p τ = k := fun p _ => ⟨0, by simp⟩

theorem fjI_zero (X : Data E r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (s : X.Ψ → ℝ) :
    fjI X ξ 0 P x s = P (X.flow ξ (cR X s) x) := by
  simp [fjI]
  rfl

theorem fj_zero_eq (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.fj la ξ 0 P x = ((volume (ExponentialGrowthExclusion.exists_fd X la).choose).toReal : ℂ)⁻¹ *
      ∫ s in (ExponentialGrowthExclusion.exists_fd X la).choose, fjI X ξ 0 P x s := by
  rw [Data.fj, if_pos (freq_zero X la), dite_eq_left (ExponentialGrowthExclusion.exists_fd X la)]
  rfl

end GlobalTheory.LevelCusp.Transport

end

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix


open GlobalTheory.LevelCusp.Transport ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity in
theorem GlobalTheory.LevelCusp.mem_SS_of_isMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r), (∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) → ∀ (P : Frame X.Ψ r → ℂ) (Q : Frame X'.Ψ r → ℂ) (c : ℂ), X.IsSec la P → Q ∈ X'.SS la' → (∀ x ∈ X.dom, P x = c * Q (lact a (castFr h.psi x))) → P ∈ X.SS la := by
  intro E _ _ _ r X X' a h la la' hl P Q c hP hQ hPQ
  obtain ⟨⟨hQs, C, hC⟩, hQ0⟩ := hQ
  have hb : ∀ x ∈ X.dom, X.pnorm la P x ≤ ‖c‖ * C := fun x hx => by
    have := hC _ (h.mem_dom hx)
    rw [BoundedSectionAlgebra.pnorm_eq, nfac_eq h hl] at this
    rw [BoundedSectionAlgebra.pnorm_eq, hPQ x hx, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  refine ⟨⟨hP, _, hb⟩, fun ξ hξ x hx => ?_⟩
  have hξ' := isIso_map h hξ
  have hx' := h.mem_dom hx
  have h0 := hQ0 _ hξ' _ hx'
  obtain ⟨-, hD, -, hf⟩ := (ExponentialGrowthExclusion.exists_fd X la).choose_spec
  obtain ⟨-, hD', hp', hf'⟩ := (ExponentialGrowthExclusion.exists_fd X' la').choose_spec
  rw [fj_zero_eq] at h0 ⊢
  have hne : ((MeasureTheory.volume (ExponentialGrowthExclusion.exists_fd X' la').choose).toReal : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne')
  have : Countable (X.periods la) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have : Countable (X'.periods la') := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  rw [integral_eq_zero_cast h.psi (c := c) (fun s => ?_) hD hD' hf hf' hp'
    (fjI_continuous X la P hP hξ.2.1 0 hx) ⟨‖c‖ * C / X.nfac la x, fun s => ?_⟩
    (fjI_periodic X la P hP hξ.1 hξ.2.1 0 (freq_zero X la) hx)
    (fjI_periodic X' la' Q hQs hξ'.1 hξ'.2.1 0 (freq_zero X' la') hx')
    ((mul_eq_zero.1 h0).resolve_left hne), mul_zero]
  · rw [fjI_zero, fjI_zero, hPQ _ (flow_real_mem_dom X hξ.2.1 s x hx), lact_flow h]
    rfl
  · have hT := hb _ (flow_real_mem_dom X hξ.2.1 s x hx)
    rw [BoundedSectionAlgebra.pnorm_eq, BoundedSectionAlgebra.nfac_flow_real X hξ.2.1] at hT
    rw [fjI_zero, le_div_iff₀ (BoundedSectionAlgebra.nfac_pos X hx la)]
    exact hT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F], Nonempty (TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))) := by
  first | exact @GlobalTheory.IntegralTate.nonempty_tateIso_of_intChart | exact GlobalTheory.IntegralTate.nonempty_tateIso_of_intChart | (intros; apply GlobalTheory.IntegralTate.nonempty_tateIso_of_intChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedPullback_section_expands_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (α : 𝓞 E) (N k q : ℕ) (e : k * N = q), α * star α = (N : 𝓞 E) → 0 < N → (k = 1 ∨ 4 ≤ k) → ∀ (σ : P.U.toUnifPre.SecGF F k) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo xF))) (θ : Fam P.D.toPre F k) (σ₁ : P.U.toUnifPre.SecGF F q) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (θα : Fam P.D.toPre F (k * N)), SecTieF I P F xF k σ s → P.U.toUnifPre.ExpandsG F k σ θ → IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) (q : ℤ) (k : ℤ) s s₁ → SecTieF I P F xF q σ₁ s₁ → PullAl P.D F P.oD α k N θ θα → P.U.toUnifPre.ExpandsG F q σ₁ (PowGerm.famCast (Dp := P.D.toPre) (F := F) e θα) := by
  first | exact @GlobalTheory.NormPullExp.main | exact GlobalTheory.NormPullExp.main | (intros; apply GlobalTheory.NormPullExp.main <;> assumption)
end

