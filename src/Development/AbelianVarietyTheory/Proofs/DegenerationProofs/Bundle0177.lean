module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0176
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationsTorusExtensionPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EigensectionSupport
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.UT

theorem eigensection_support : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (q : QkPt D.toPre F N) τ, q.y = 0 → IsTor τ q.g → ∀ x, QkToAkU U.toUnifPre F N q x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (t t' : SecA A F N) (s : Fam D.toPre F N) (c : F), U.ExpandsF F N w₀ t s → IsActOf A.A A.L N θ t t' → (∀ j, t'.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j) → ∀ β, (τ (Multiplicative.ofAdd β)).val ≠ c → ∀ j, (s.s β).f j = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN q τ hy hτ x hx θ hθ w₀ hw₀ t t' s c hs hact ht β hβ j
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hI D F N hN q).1
  have h₁ := (expBijF_and_expandsF_lin hL R I hI D A G hG U).2 F N w₀ t t t' s s (c - 1) hs hs (fun i => by
    rw [ht i]
    simp only [liftFun, map_sub, map_one, sub_mul, _root_.one_mul, sub_add_cancel])
  have h₂ := symLift_acts_as_phi hL R I hI D A G hG U F N hN q x hx θ hθ w₀ hw₀ w hw t t' s _ hs h₁ hact
  have h₃ := ((TorusWeight.torus_weight hL R I hI D A G hG U F N hN q τ hy hτ w hw).2 _ _).1 h₂ β j
  rw [sub_smul, one_smul, sub_add_cancel, DVR.smul_f, constBF_eq] at h₃
  have key : ∀ {S : Type} [CommRing S] (g : F →+* S) (a b : F) (y : S), a ≠ b → g b * y = g a * y → y = 0 := by
    intro S _ g a b y hab e
    have hu : IsUnit (g (a - b)) := (IsUnit.mk0 _ (sub_ne_zero.2 hab)).map g
    exact hu.mul_right_eq_zero.1 (by rw [map_sub, sub_mul, e, sub_self])
  exact key ((((DegPre.BF D.toPre F).left.presheaf.map (homOfLE le_top).op).hom).comp (gF D.toPre F)) _ c _ hβ h₃

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomAlgebraisingThickeningsProjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MorAlgIdeal

open GlobalTheory.MorAlg

theorem exists_section (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (hI : I ≠ ⊤) (hc : IsAdicComplete I R) (Y P : Over (Spec (CommRingCat.of R))) (q : P ⟶ Y)
    [IsSeparated q.left] [IsProper Y.hom] [Flat Y.hom] (hP : IsProjBy P.hom)
    (j : ∀ e, (thickObj R I e Y).left ⟶ P.left)
    (hq : ∀ e, j e ≫ q.left = pullback.fst Y.hom (thick R I e))
    (hj : ∀ e, thickMap R I e Y ≫ j (e + 1) = j e) :
    ∃ g : Y ⟶ P, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = j e := by
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  choose t ht using fun e => exists_isPull (j e) hH s
  have hv : ∀ e, IsPull (thickMap R I e Y) (t (e + 1)) (t e) := fun e =>
    IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)
  choose v hv cv using hv
  have hjR : ∀ e, j e ≫ P.hom = (thickObj R I e Y).hom ≫ thick R I e := fun e => by
    rw [← Over.w q, ← Category.assoc, hq]
    exact pullback.condition
  have hci : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hva : VeryAmpleBy (thickObj R I 0 Y).hom (H.pull (j 0)) (t 0) := by
    obtain ⟨w, hw, c⟩ := ht 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (I ^ (0 + 1))) _ _ (j 0) (hjR 0) ?_ _ w _
      (hL 0) hw c
    have h₁ : IsClosedImmersion (j 0 ≫ q.left) := by
      rw [hq]
      have := hci 0
      infer_instance
    have h₂ : IsClosedImmersion (j 0) := IsClosedImmersion.of_comp _ q.left
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj R I 0 Y).hom (hjR 0) ≫
        pullback.fst P.hom (thick R I 0)) := by
      rw [pullback.lift_fst]
      exact h₂
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick R I 0))
  have hpb : ∀ e, IsPullback (thickMap R I e Y) (thickObj R I e Y).hom (thickObj R I (e + 1) Y).hom
      (thickTrans R I e) := fun e => by
    refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I (e + 1))) (h₂₂ := thick R I (e + 1))
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.Degen.exists_projective_of_formal_embedding_local R I hI hc (fun e => thickObj R I e Y)
    (fun e => thickMap R I e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick R I e))))
    (fun e => H.pull (j e)) v (fun e => ⟨hL e, hv e⟩) n t cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => heq d F hF fun e k => by
      rw [← hjR]
      exact (ht e).eqn P.hom hH hF h0 k
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections R P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjR]
    exact (hb e).w
  let φ' : B ⟶ P := Over.homMk φ hφ
  have hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick R I e) := fun e => by
    rw [← hq, ← hbφ]
    exact (Category.assoc _ _ _).symm
  have hB : IsProper ((φ' ≫ q).left ≫ Y.hom) := by
    rw [Over.w]
    exact GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ ⟨H', hH', n, s', hs'⟩
  have hp : IsProper (φ' ≫ q).left := IsProper.of_comp _ Y.hom
  have hiso : IsIso (φ' ≫ q) := GlobalTheory.IsoLimitIdeal.main R I hI B Y (φ' ≫ q) fun e => by
    have h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map (φ' ≫ q)).left = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [← hbp e, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]
        exact (hb e).isoPullback_hom_snd
    have h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick R I e)).map (φ' ≫ q))) :=
      @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩
  rw [← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]
  exact hbφ e

theorem exists_hom_of_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), IsProjBy Y.hom → IsProjBy Z.hom → Flat Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  intro R _ _ _ I hI hcI Y Z hY hZ hfl f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hZ
  have hsep : IsSeparated (fst Y Z).left := inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))
  obtain ⟨g, hg⟩ := exists_section R I hI hcI Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor R Y Z hY hZ)
    (fun e => pullback.lift (pullback.fst Y.hom (thick R I e)) (f e) (hf e).symm)
    (fun e => pullback.lift_fst _ _ _) (fun e => by
      apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])
  refine ⟨g ≫ snd Y Z, fun e => ?_⟩
  have := congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)
  exact ((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)

end GlobalTheory.MorAlgIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcDataStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedArc_uAdicUniformisation_of_arcData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → PushInvertible Y.t.G Y.t.PP.L → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → Y.HasArcData a (Ideal.span {(PowerSeries.X : PowerSeries O')}) (PowerSeries.C (R := O')) PowerSeries.X χ := by
  first | exact @GlobalTheory.ArcData.hasArcData_of_traitData | exact GlobalTheory.ArcData.hasArcData_of_traitData | (intros; apply GlobalTheory.ArcData.hasArcData_of_traitData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesAtPointIntegralOfPeriodValuation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesAtPoint

section Pull
variable {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem secLin_of_secScal {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : scal π (1 : R) = 1 := by simp [scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

theorem exists_pull (hL : L.IsLB) {φ : K₁ → (Y ⟶ X)} {ε : K₁ → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    {φ' : K₁ → (Y' ⟶ X)} (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε s' φ ε s h 1 ∧
      ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y') (j : K₁ → L.ι), ⊤ ≤ (x ≫ h) ⁻¹ᵁ LB.wchart L φ j →
        valR x (LB.wchart L φ' j) (s'.f j) = valR (x ≫ h) (LB.wchart L φ j) (s.f j) := by
  subst e
  refine ⟨DVR.pullSec L φ ε s h, DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
    (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ (𝟙 _) y hJ).symm, fun R _ x j hj => ?_⟩
  have hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := fun y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k
  refine (CrdCalc.valR_res x _ hj' _).trans ?_
  exact (CrdCalc.valR_eq x (h ⁻¹ᵁ LB.wchart L φ j) hj _).trans (CrdCalc.valR_eq (x ≫ h) _ hj (s.f j)).symm

theorem exists_isGen {R : Type} [CommRing R] [IsLocalRing R] {M : LB (Sp R)} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  have : (𝟙 (Sp R) : Sp R ⟶ Sp R) (IsLocalRing.closedPoint R) ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  have hl' : ⊤ ≤ M.U l := (CrdCalc.top_le_iff (𝟙 (Sp R)) _).2 hl
  have le : ∀ V : (Sp R).Opens, V ≤ V ⊓ M.U l := fun V => le_inf le_rfl (le_top.trans hl')
  refine ⟨⟨fun j => res (le _) (M.g j l)⟩, fun i j => ?_⟩
  have e := congrArg (res (le (M.U i ⊓ M.U j))) (hM.cocycle i j l)
  rw [map_mul, DVR.res_res', DVR.res_res', DVR.res_res', DVR.res_refl'] at e
  simp only [DVR.res_res']
  exact e.symm

end Pull

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem exists_frm (k : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) :
    ∃ w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b, w.IsGen :=
  exists_isGen (R := PadicAlgCl p) (DVR.linComb_isLB _ u.D.toPre.P.isLB _ _)

theorem hasSum_crd {k : ℕ} {J : Type} {σ : J → (u.H k).Sec} {f : J → ∀ α, u.D.toPre.SecB k α}
    (hf : ∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) {s : J → Fam u.D.toPre (PadicAlgCl p) k}
    (hs : ∀ i, FamOf u.D.toPre _ (f i) (s i)) {a : u.PtC} {g : GtPtF u.D.toPre (PadicAlgCl p)} (hg : u.ParAt k a g)
    {w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b} (hw : w.IsGen) {v : J → PadicAlgCl p}
    (hv : Crd (u.H k) σ (u.toG a) v) :
    ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ i, HasSum (fun χ => GlobalTheory.UT.coef (s i) g w χ) (κ * v i) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  obtain ⟨l, rfl⟩ : ∃ l₀, l = fun _ : Fin 1 => l₀ := ⟨l 0, funext fun i => congrArg l (Subsingleton.elim _ _)⟩
  obtain ⟨κ, hκ, H⟩ := hg w hw l (hl.trans ((u.toG a).preimage_mono
    (LB.wchart_le u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l) 0)))
  refine ⟨κ * (c⁻¹).val, mul_ne_zero hκ (Units.ne_zero _), fun i => ?_⟩
  obtain ⟨σ', h₁, h₂⟩ := exists_pull u.U.LG.isLB (σ i) (UnifPre.gFK (G := u.G) (PadicAlgCl p))
    (φ' := fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (funext fun _ => (Category.comp_id _).symm)
  have e : (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = u.toG a := by
    rw [← Category.assoc, ← Over.comp_left, lift_snd]
    rfl
  have hsum := H σ' (s i) ⟨1, fun _ => 1, fun _ => σ i, fun _ => f i, fun _ => hf i, secLin_of_secScal _ h₁,
    fun α => secLin_of_secScal _ (hs i α)⟩
  have h₃ := h₂ (PadicAlgCl p) (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left (fun _ => l) (e.symm ▸ hl)
  have h₄ := h₃.trans (congrArg (fun x => valR x (LB.wchart u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l))
    ((σ i).f fun _ => l)) e)
  rw [hv, _root_.mul_assoc, Units.inv_mul_cancel_left]
  exact (congrArg (fun x => HasSum _ (κ * x)) h₄).mp hsum

theorem main : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∀ w, Crd (u.H S.N) σ a w → ∃ ν : u.D.toPre.X →+ ℝ, Ser l.q S.N cls w ν ∧ ((∃ m, ∀ α, ν α = QuadraticMap.polar l.q m α) → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = a) := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hB a ha w hw
  have hN : 4 ≤ S.N := (_root_.GlobalTheory.ZH.utest_dim_and_split hL o Ω S ρ p y₀ u).2.2.2.1
  have hN1 : 1 ≤ S.N := le_trans (by norm_num) hN
  obtain ⟨-, hsep, hon⟩ := _root_.GlobalTheory.ZH.AdaptedSep.basis_separates hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB
  obtain ⟨a, rfl⟩ := hon a ha
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.ZH.exists_parAt hL hT o Ω S ρ p y₀ u l a
  obtain ⟨-, hex, huq, hadd, hι⟩ := _root_.GlobalTheory.ZH.TorusVal.main hL o Ω S ρ p y₀ u l
  obtain ⟨ν, hν⟩ := hex g
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) S.N, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hB.2.2.2.2.1 i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D S.N s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  obtain ⟨fr, hfr⟩ := exists_frm u S.N g
  obtain ⟨κ, hκ, hsum⟩ := hasSum_crd u hB.2.2.2.1 hs hg hfr hw
  refine ⟨ν, ?_, ?_⟩
  · obtain ⟨r, hr, H⟩ := _root_.GlobalTheory.TermSize.term_sizes hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB s hs g ν fr hν hfr
    refine ⟨fun α i => κ⁻¹ * GlobalTheory.UT.coef (s i) g fr α, ‖κ⁻¹‖ * r,
      mul_pos (norm_pos_iff.2 (inv_ne_zero hκ)) hr, fun i => ?_, fun α i h => ?_, fun α => ⟨fun i => ?_, ?_⟩⟩
    · have := (hsum i).mul_left κ⁻¹
      rwa [inv_mul_cancel_left₀ hκ] at this
    · exact (H α).1 i (right_ne_zero_of_mul h)
    · rw [norm_mul, _root_.mul_assoc]
      exact mul_le_mul_of_nonneg_left ((H α).2.1 i) (norm_nonneg _)
    · obtain ⟨i, hi⟩ := (H α).2.2
      exact ⟨i, by rw [norm_mul, _root_.mul_assoc, hi]⟩
  · rintro ⟨m, hm⟩
    obtain ⟨-, hio, hsub⟩ := GlobalTheory.ZH.gt_add_iota_sub_exist hL o Ω S ρ p y₀ u
    obtain ⟨h, hh⟩ := hio m
    obtain ⟨g', hg'⟩ := hsub g h
    obtain ⟨ν', hν'⟩ := hex g'
    have e := huq g _ _ hν (hadd g' h g _ _ hg' hν' (hι m h hh))
    have e0 : (ν' : u.D.toPre.X → ℝ) = 0 := funext fun α => by
      have := congrFun e α
      rw [Pi.add_apply, hm α] at this
      exact right_eq_add.1 this
    obtain ⟨c, hc, hlev⟩ := _root_.GlobalTheory.GtDescent.exists_integral_point hL o Ω S ρ p y₀ u g' (e0 ▸ hν')
    obtain ⟨a', ha'⟩ := hon (gPt p ≫ c) (by rw [Category.assoc, hc])
    have hp' : u.ParAt S.N a' g :=
      (_root_.GlobalTheory.ZH.IotaShift.parAt_add_iota hL o Ω S ρ p y₀ u S.N a' g' h g m hN1 hh hg').1
        ((_root_.GlobalTheory.ZH.IntegralSum.gtN_zero_and_parAt hL o Ω S ρ p y₀ u c g' a' hc ha'.symm hlev).2 S.N hN1)
    obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (DVR.linComb_isLB _ u.U.LG.isLB _ _) σ (u.toG a')
    obtain ⟨κ', hκ', hsum'⟩ := hasSum_crd u hB.2.2.2.1 hs hp' hfr hw'
    have h₁ := CrdCalc.crd_smul (Units.mk0 κ hκ) hw
    have h₂ := CrdCalc.crd_smul (Units.mk0 κ' hκ') hw'
    have e₃ : (fun j => ((Units.mk0 κ' hκ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w' j) =
        fun j => ((Units.mk0 κ hκ : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w j :=
      funext fun j => (hsum' j).unique (hsum j)
    rw [e₃] at h₂
    exact ⟨c, hc, ha'.symm.trans (congrArg u.toG (hsep a' a _ h₂ h₁))⟩

end GlobalTheory.ZH.SeriesAtPoint
end

