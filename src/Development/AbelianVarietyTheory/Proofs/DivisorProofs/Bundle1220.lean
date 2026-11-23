module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTarget
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionAutomorphySourceGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCoveringChartsGenericallyFiniteField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory.ChartGlue

namespace GlobalTheory.CoverDegField

theorem exists_open_covering_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q σ D hpP hqP hsm π hπ hη hδ
  haveI : SmoothOfRelativeDimension D p := hsm
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨U₁, t₁, hU₁, hx₁, ht⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := p) (D := D) (genericPoint X)
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hpP hqP π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover p π D _ _ U₁ U₂ hU₁ hx₁ ⟨t₁, ht⟩ hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩
  · rw [GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hG.1 hG.2.1 σ y hy]
    exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := GlobalTheory.CoverDeg.etale_pullback_coords π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDegField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionLieAlgebraPullbackDetStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_function_lie_algebra_pullback_det : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ α : glG E a → ℂ, (glH E a).IsSmoothFun α → HasCompactSupport α → ∃ β : Lie E a → ℂ, GlobalTheory.CuspQuot.IsTest (invSet E a) β ∧ ∀ y : glG E a, β (toL y.1.val) = ((|LinearMap.det ((lmul (toL y.1.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * α y := by
  first | exact @GlobalTheory.GLExt.exists_isTest_ext | exact GlobalTheory.GLExt.exists_isTest_ext | (intros; apply GlobalTheory.GLExt.exists_isTest_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationSqZeroPointsUnitToPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

abbrev ovT (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : Over (Sp R) :=
  Over.mk (spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)))

abbrev ovB (R : Type) [CommRing R] (B : Type) [CommRing B] [Algebra R B] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R B))

theorem one_left (A : Over (Sp R)) [GrpObj A] (T : Over (Sp R)) : (1 : T ⟶ A).left = T.hom ≫ η[A].left := rfl

theorem inl_w (A : Over (Sp R)) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    (spMap (TrivSqZeroExt.inlHom B M) ≫ P) ≫ A.hom = (ovT R B M).hom := by
  rw [Category.assoc, hP]
  exact (GlobalTheory.Cris.spMap_comp _ _).symm

theorem fst_w (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ (ovT R B M).hom = (ovB R B).hom := by
  show _ ≫ spMap _ = spMap _
  rw [← GlobalTheory.Cris.spMap_comp]
  congr 1 <;> ext r <;> simp

theorem fst_inl (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap (TrivSqZeroExt.inlHom B M) = 𝟙 (Sp B) := by
  rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
  congr 1 <;> ext r <;> simp

def eFst (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : ovB R B ⟶ ovT R B M :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) (fst_w B M)


open Classical in
def tau (A : Over (Sp R)) [GrpObj A] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (z : Sp (TrivSqZeroExt B M) ⟶ A.left) :
    Sp (TrivSqZeroExt B M) ⟶ A.left :=
  if h : P ≫ A.hom = spMap (algebraMap R B) ∧ z ≫ A.hom = (ovT R B M).hom then
    ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P h.1) *
      Over.homMk (U := ovT R B M) (V := A) z h.2 : ovT R B M ⟶ A)).left
  else z

theorem tau_eq (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B))
    (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : z ≫ A.hom = (ovT R B M).hom) :
    tau A B M P z = ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) *
      Over.homMk (U := ovT R B M) (V := A) z hz : ovT R B M ⟶ A)).left := by
  rw [tau, dite_eq_left ⟨hP, hz⟩]

theorem red_iff (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (g : ovT R B M ⟶ A) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ g.left = P ↔
      eFst B M ≫ g = Over.homMk (U := ovB R B) (V := A) P hP := by
  constructor
  · intro h; ext; simpa [eFst] using h
  · intro h; have := congrArg CommaMorphism.left h; simpa [eFst] using this

theorem unit_eq (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B]
    (h : unitPt A B ≫ A.hom = spMap (algebraMap R B)) :
    Over.homMk (U := ovB R B) (V := A) (unitPt A B) h = 1 := by
  ext; rw [one_left]; rfl

end GlobalTheory.AbTan.Transl

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

theorem unit_w (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] :
    unitPt A B ≫ A.hom = spMap (algebraMap R B) := by
  rw [unitPt, Category.assoc, Over.w η[A]]
  exact Category.comp_id _

theorem bijOn_tau (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    Set.BijOn (tau A B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z} := by
  set Q : ovT R B M ⟶ A := Over.homMk (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) with hQ
  have hU := unit_w A B
  have keyQ : eFst B M ≫ Q = Over.homMk (U := ovB R B) (V := A) P hP := by
    ext
    simp only [eFst, Q, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, fst_inl]
    exact Category.id_comp _
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := hz
    show Lifts A.hom P (tau A B M P z)
    rw [tau_eq A P hP z h1]
    refine ⟨Over.w _, ?_⟩
    rw [red_iff A _ P hP, MonObj.comp_mul, keyQ,
      (red_iff A (Over.homMk (U := ovT R B M) (V := A) z h1) (unitPt A B) hU).1 h2, unit_eq, _root_.mul_one]
  · intro z1 hz1 z2 hz2 he
    obtain ⟨h11, -⟩ := hz1
    obtain ⟨h21, -⟩ := hz2
    rw [tau_eq A P hP z1 h11, tau_eq A P hP z2 h21] at he
    have := mul_left_cancel (Over.OverMorphism.ext he)
    exact congrArg CommaMorphism.left this
  · intro z' hz'
    obtain ⟨h1, h2⟩ := hz'
    set Z : ovT R B M ⟶ A := Q⁻¹ * Over.homMk (U := ovT R B M) (V := A) z' h1 with hZ
    refine ⟨Z.left, ⟨Over.w Z, ?_⟩, ?_⟩
    · rw [red_iff A Z (unitPt A B) hU, unit_eq, hZ, MonObj.comp_mul, GrpObj.comp_inv, keyQ,
        (red_iff A (Over.homMk (U := ovT R B M) (V := A) z' h1) P hP).1 h2, inv_mul_cancel]
    · show tau A B M P Z.left = z'
      rw [tau_eq A P hP Z.left (Over.w Z)]
      have e : Over.homMk (U := ovT R B M) (V := A) Z.left (Over.w Z) = Z := by ext; rfl
      rw [← hQ, e, hZ, mul_inv_cancel_left]
      rfl

theorem tau_natural (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] {B' M' : Type} [CommRing B'] [Algebra R B']
    [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (hβ : IsSum β α f) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) (z : Sp (TrivSqZeroExt B M) ⟶ A.left)
    (hz : Lifts A.hom (unitPt A B) z) :
    Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧
      tau A B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ tau A B M P z := by
  obtain ⟨hz1, hz2⟩ := hz
  have hβinl : β.comp (TrivSqZeroExt.inlHom B M) = (TrivSqZeroExt.inlHom B' M').comp (α : B →+* B') :=
    RingHom.ext fun b => hβ.1 b
  have hβT : β.comp ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) =
      (TrivSqZeroExt.inlHom B' M').comp (algebraMap R B') := by
    rw [← RingHom.comp_assoc, hβinl, RingHom.comp_assoc, AlgHom.comp_algebraMap]
  have hβfst : (TrivSqZeroExt.fstHom B' B' M').toRingHom.comp β =
      (α : B →+* B').comp (TrivSqZeroExt.fstHom B B M).toRingHom := by
    ext x
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    simp [map_add (f := _), hβ.1, hβ.2]
  let b : ovT R B' M' ⟶ ovT R B M := Over.homMk (spMap β) (by
    show spMap β ≫ spMap _ = spMap _
    rw [← GlobalTheory.Cris.spMap_comp, hβT])
  set Z : ovT R B M ⟶ A := Over.homMk z hz1 with hZ
  have hz' : (spMap β ≫ z) ≫ A.hom = (ovT R B' M').hom := Over.w (b ≫ Z)
  have hP' : (spMap (α : B →+* B') ≫ P) ≫ A.hom = spMap (algebraMap R B') := by
    rw [Category.assoc, hP, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  refine ⟨⟨hz', ?_⟩, ?_⟩
  · rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hβfst, GlobalTheory.Cris.spMap_comp, Category.assoc, hz2, unitPt,
      unitPt, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [tau_eq A _ hP' _ hz', tau_eq A P hP z hz1]
    have e1 : b ≫ (Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP)) =
        Over.homMk (U := ovT R B' M') (V := A) (spMap (TrivSqZeroExt.inlHom B' M') ≫ spMap (α : B →+* B') ≫ P)
          (inl_w A _ hP') := by
      ext
      simp only [b, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp, hβinl]
    have e2 : b ≫ Z = Over.homMk (U := ovT R B' M') (V := A) (spMap β ≫ z) hz' := by ext; rfl
    show _ = (b ≫ (_ * Z)).left
    rw [MonObj.comp_mul, e1, e2]

end GlobalTheory.AbTan.Transl


open GlobalTheory.AbTan.Transl in
theorem GlobalTheory.AbTan.exists_translation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∃ τ : ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M], (Sp B ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left), (∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → Set.BijOn (τ B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z}) ∧ ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (B' M' : Type) [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f → ∀ (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → ∀ z, Lifts A.hom (unitPt A B) z → Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧ τ B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ τ B M P z := by
  intro R _ A _
  refine ⟨fun B M => tau A B M, ?_, ?_⟩
  · intro B M _ _ _ _ _ _ P hP
    exact bijOn_tau A P hP
  · intro B M _ _ _ _ _ _ B' M' _ _ _ _ _ _ α f β hβ P hP z hz
    exact tau_natural A α f β hβ P hP z hz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueRingHomOfSqZeroExtPointAffine
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

theorem range_spMap_fst_eq (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ⟨spMap (TrivSqZeroExt.inlHom B M) y, ?_⟩
  change PrimeSpectrum.comap _ (PrimeSpectrum.comap _ y) = y
  apply PrimeSpectrum.ext
  ext x
  change (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) ∈ y.asIdeal ↔ x ∈ y.asIdeal
  have hm : (TrivSqZeroExt.inr x.snd : TrivSqZeroExt B M) ∈ y.asIdeal :=
    y.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact y.asIdeal.zero_mem)
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
  constructor
  · intro h; rw [hx]; exact y.asIdeal.add_mem h hm
  · intro h
    have e : (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) = x - TrivSqZeroExt.inr x.snd := by
      rw [eq_sub_iff_add_eq]; exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x
    rw [e]; exact y.asIdeal.sub_mem h hm

theorem exists_unique_ringHom_of_sqZero (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (U : X.affineOpens) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (ρ : Sec s U.1 →+* B) (z : Sp (TrivSqZeroExt B M) ⟶ X)
    (hz : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap ρ ≫ affPt s U) :
    ∃! c : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = z ∧ ∀ b, (c b).fst = ρ b := by
  have hr : Set.range z ⊆ Set.range (affPt s U) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : y ∈ Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) := by
      rw [range_spMap_fst_eq]; trivial
    refine ⟨spMap ρ x, ?_⟩
    change (spMap ρ ≫ affPt s U) x = (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z) x
    rw [hz]
  haveI : IsOpenImmersion (affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
  set g := IsOpenImmersion.lift (affPt s U) z hr with hg
  have hgf : g ≫ affPt s U = z := IsOpenImmersion.lift_fac _ _ _
  have hsp : ∀ c c' : Sec s U.1 →+* TrivSqZeroExt B M,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  have hsp' : ∀ c c' : Sec s U.1 →+* B,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  set c₀ : Sec s U.1 →+* TrivSqZeroExt B M := (Spec.preimage g).hom with hc₀
  have hc : spMap c₀ = g := Spec.map_preimage g
  have h₁ : spMap c₀ ≫ affPt s U = z := by rw [hc, hgf]
  refine ⟨c₀, ⟨h₁, ?_⟩, fun c hc' ↦ hsp _ _ (hc'.1.trans h₁.symm)⟩
  have e : spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp c₀) ≫ affPt s U =
      spMap ρ ≫ affPt s U := by
    rw [← hz, ← h₁, ← Category.assoc, ← Spec.map_comp]; rfl
  intro b
  exact congrArg (fun f : Sec s U.1 →+* B ↦ f b) (hsp' _ _ e)

end GlobalTheory.AbTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParametersStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q), letI := hQ.isLocalRing;
  ∀ (r N : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
  IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
  (∃ x : Fin N → L, TrBasis c x) →
  ∃ V : Place c, V.Contains Q ∧ (∀ q : Q, IsUnit q → V.ord q = 0) ∧ (∀ i, V.ord (z i) = wt i) ∧
    (∀ (d : ℕ) (q : Q), (q : L) ≠ 0 → q ∈ IsLocalRing.maximalIdeal Q ^ d → (d : ℤ) ≤ V.ord q) ∧
    ∀ y : Fin N → Q, IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) y) →
      V.formOrd (dForm c (fun i => (y i : L))) + 1 ≤ ∑ i, (wt i : ℤ) := by
  first | exact @GlobalTheory.MonoVal.monomial_place | exact GlobalTheory.MonoVal.monomial_place | (intros; apply GlobalTheory.MonoVal.monomial_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO

variable {D : D7}

theorem isHeckeChar_pow {η : (AE D)ˣ →* Circle} (h : IsHeckeChar D η) (n : ℕ) : IsHeckeChar D (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEta_pow {η : (AE D)ˣ →* Circle} (h : ResEta D η 1) (n : ℕ) : ResEta D (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem mem_GfC_of_supp {a : AE D} (ha : infPart D a = 0) {V : HSp D} {g : GA D V}
    (hg : ∀ i j, a * (mt V g - 1) i j = (mt V g - 1) i j) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfC_of_suppAt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : g ∈ GfC V := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfC_of_supp (h2 ▸ infPart_placeIdem h1) hg

theorem exists_weilDatum_etaTilde : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∃ om, IsWeilDatumO ψ S T (η ^ S.rank) (η ^ T.rank) om ∧ (∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε) ∧ VacCharPlus ψ θ S T om := by
  intro D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨of, hf⟩ := exists_isFinWeil D ψ hψ S T ΛS ΛT hS hT _ _ (isHeckeChar_pow hη.1 S.rank)
    (isHeckeChar_pow hη.1 T.rank) (resEta_pow hη.2.2.1 _) (resEta_pow hη.2.2.1 _)
  obtain ⟨oi, hi⟩ := GlobalTheory.RealWeil.exists_isInfWeil D ψ hψ θ hθ S T
  have hcomm := fun p q f h1 => fin_inf_comm hψ hS hT hf hi p q (f := f) h1
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T)
    ({ toFun := fun p => (of p * oi p).restrict fun f h1 => hf.pres p _ (hi.pres p f h1)
       map_one' := LinearMap.ext fun f => Subtype.ext (by
         show of 1 (oi 1 f) = f
         rw [map_one, map_one]; rfl)
       map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
         show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q f)))
         rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres q _ f.2)]) } :
      GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T))
  have ho : ∀ p f, IsThetaFunO ψ S T f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  have hfin : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = of (g, h) f := fun g hg h hh f h1 => by
    rw [ho _ f h1, hi.triv g hg h hh f h1]
  have hinf : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = oi (g, h) f :=
    fun g hg h hh f h1 => by rw [ho _ f h1, hf.triv g hg h hh _ (hi.pres _ f h1)]
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨om, ⟨hψ, isHeckeChar_pow hη.1 _, isHeckeChar_pow hη.1 _, resEta_pow hη.2.2.1 _, resEta_pow hη.2.2.1 _, hp,
    fun g h u f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 u => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩, fun v ε hv g h hg hh hst f h1 hfix => ?_,
    fun sS sT cS cT g hg h hh kS kT f h1 hv => ?_⟩
  · obtain ⟨a, ha, b, hb, k, hk, l, hl, e, -⟩ := exists_parts (g, h)
    obtain ⟨rfl, rfl⟩ : g = a * k ∧ h = b * l := Prod.ext_iff.1 e
    rw [actO_mul, e, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfin k hk l hl _ (hth u f h1),
      hf.Heisenberg₂ k hk l hl u f h1, hfin k hk l hl f h1, hinf a ha b hb _ (hth _ _ (hf.pres _ f h1)),
      hi.Heisenberg₂ a ha b hb _ _ (hf.pres _ f h1), hinf a ha b hb _ (hf.pres _ f h1)]
  · rw [show ((γ, γ') : GA D S × GA D T) = (γ, 1) * (1, γ') by simp, map_mul, Module.End.mul_apply,
      ho _ _ (hp _ f h1), _root_.GlobalTheory.DualSwap.automorphy_source D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ hγ _ (hp _ f h1), ho _ f h1]
    exact _root_.GlobalTheory.RatAut.automorphy_target D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ' hγ' f h1
  · simp only [ho _ f h1]
    exact continuous_product hψ hS hT hf hi h1 u
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [hfin g (mem_GfC_of_suppAt he hg) h (mem_GfC_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1
  · rw [hfin g (mem_GfC_of_supp (infPart_placeIdem hv.1) hg) h (mem_GfC_of_supp (infPart_placeIdem hv.1) hh) f h1]
    exact hf.inert v ε hv g h hg hh hst f h1 hfix
  · rw [hinf g hg h hh f h1]
    exact hi.vac sS sT cS cT g hg h hh kS kT f h1 hv

end GlobalTheory.WeilProduct

end
end

