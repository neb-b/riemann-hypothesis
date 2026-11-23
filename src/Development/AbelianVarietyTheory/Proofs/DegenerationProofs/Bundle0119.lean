module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseChangeTestOfSurjectiveMulAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFacOfClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalSectionNeZeroOnFibres

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdditiveWeightPointsOfTorusTower
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.WeightPoint

theorem w_of_isCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B'] [GrpObj B]
    [IsCommMonObj B] {M' : CP B'} {M : CP B} {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsCPPullback M' M f β) :
    β ≫ B.hom = B'.hom ≫ f := by
  obtain ⟨h, -⟩ := h
  exact h.1.w

section Tower
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]
  {T : TowerR I P X} (a : T.Alg)


omit [IsDomain R] [IsLocalRing R] [IsCommMonObj G] in
theorem isGrpPullback_thickMap (e : ℕ) :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel ((isGrpPullback_pullback G (thick R I e)).congr
    (thickTrans_comp R I e).symm ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm)
    (pullback.lift_snd _ _ _)


omit [IsDomain R] in
theorem exists_section [IsAdicComplete I R] {B : Over (Spec (CommRingCat.of R))}
    (x : ∀ e : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ B.left) (hx : ∀ e, x e ≫ B.hom = thick R I e)
    (hc : ∀ e, thickTrans R I e ≫ x (e + 1) = x e) : ∃ c : 𝟙_ _ ⟶ B, ∀ e, thick R I e ≫ c.left = x e := by
  obtain ⟨c, ⟨h₁, h₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (I := I) (f := x) (𝟙 _) B.hom hc
    fun e => (hx e).trans (Category.comp_id _).symm
  exact ⟨Over.homMk c h₁, h₂⟩

theorem isGrpPullback_level (e : ℕ) : IsGrpPullback (T.l e).Q.B a.B (thick R I e) (a.b e) := by
  obtain ⟨h, -⟩ := a.b_pb e
  exact h

theorem exists_rep_level (hP : PicardZeroDegenerationCondition) [IsNoetherianRing R] (hI : I ≠ ⊤) (hK : KTriv a.B a.M.L.L) (χ : X) (e : ℕ) :
    ∃ x, x ≫ a.B.hom = thick R I e ∧ Rep (T.l e).Q a.M.L.L (a.b e) x χ :=
  have := isLocalRing_quotient_pow hI e
  exists_rep hP a.M a.ample hK (T.l e).Q (isGrpPullback_level a e) χ

theorem rep_level_pull {χ : X} {e : ℕ} {x} (h : Rep (T.l (e + 1)).Q a.M.L.L (a.b (e + 1)) x χ) :
    Rep (T.l e).Q a.M.L.L (a.b e) (thickTrans R I e ≫ x) χ :=
  Rep.pull (Q := (T.l (e + 1)).Q) (Q' := (T.l e).Q) (isGrpPullback_thickMap e) (T.tor e)
    (w_of_isCPPullback (T.β_pb e)) (T.β_q e) (a.b_β e) h

theorem exists_repWt (hP : PicardZeroDegenerationCondition) [IsNoetherianRing R] [IsAdicComplete I R] (hK : KTriv a.B a.M.L.L) (χ : X) :
    ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  choose x hx hr using exists_rep_level a hP (ne_top_of_isHausdorff I) hK χ
  obtain ⟨c, hc⟩ := exists_section x hx fun e => Rep.unique a.M.L.isLB hK (isGrpPullback_level a e).1
    (by rw [Category.assoc, hx, thickTrans_comp]) (hx e) (rep_level_pull a (hr (e + 1))) (hr e)
  refine ⟨c, fun e => Rep.section (isGrpPullback_level a e).1.w c ?_⟩
  rw [hc]
  exact hr e

theorem repWt_unique [IsHausdorff I R] (hK : KTriv a.B a.M.L.L) {χ : X} {c c' : 𝟙_ _ ⟶ a.B}
    (hc : ∀ e, a.RepWt c χ e) (hc' : ∀ e, a.RepWt c' χ e) : c = c' := by
  refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isHausdorff I fun e => ?_)
  obtain ⟨pb, -⟩ := a.b_pb e
  have k := section_eq_of_isWt a.M.L.isLB hK c c' (T.l e).Q pb.1 χ (hc e) (hc' e)
  rw [Over.comp_left, Over.comp_left, Rosenlicht.toUnit_left] at k
  exact k

theorem repWt_add {χ χ' : X} {c c' : 𝟙_ _ ⟶ a.B} {e : ℕ} (h : a.RepWt c χ e) (h' : a.RepWt c' χ' e) :
    a.RepWt (c * c') (χ + χ') e := by
  refine exists_genWt_add (fun Z x g => ?_) a.M.L.isLB (GlobalTheory.Square.triv_inv (triv_square_sections a.M.c c c'))
    (fun U _ f => ?_) h h'
  · rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]
  · simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

end Tower

theorem exists_weightPoints : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X) (a : T.Alg), KTriv a.B a.M.L.L → ∃ c : X → (𝟙_ _ ⟶ a.B), (∀ χ χ', c (χ + χ') = c χ * c χ') ∧ ∀ χ e, a.RepWt (c χ) χ e := by
  intro _ _ hE R _ _ _ I hR G _ _ P X _ T a hK
  have := hR.1.1
  have := hR.1.2.2.2
  choose c hc using exists_repWt a hE.2.2.2 hK
  exact ⟨c, fun χ χ' => repWt_unique a hK (hc _) fun e => repWt_add a (hc χ e) (hc χ' e), hc⟩

end GlobalTheory.WeightPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegDataPsiOfSectionNonzeroFibres
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
namespace GlobalTheory.PsiRing

theorem ne_zero_of_secCmp {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)} {xe : D'.X ≃+ D.X}
    (hw : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α}
    (h : SecCmp D D' β v xe f f') (h' : ∀ α, ∃ j, (f' α).f j ≠ 0) (α : D.X) : ∃ j, (f α).f j ≠ 0 := by
  obtain ⟨x, rfl⟩ := xe.surjective α
  by_contra h0
  push Not at h0
  obtain ⟨j, hj⟩ := h' x
  refine hj (ThetaScalar.eq_zero_of_sval D'.P.isLB _ (fun y J' hJ' => ?_) j)
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB y
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (((snd (𝟙_ _) D'.P.A).left ≫ β) ≫ D.P.A.hom)
  let p : T ⟶ D.P.A := Over.homMk ((snd (𝟙_ _) D'.P.A).left ≫ β) rfl
  have e := h x _ (𝟙 _) (lift (toUnit T) p).left
    ((congrArg (fun q => q.left) (lift_snd (toUnit T) p)).trans (Category.id_comp _).symm) y J J' hJ hJ'
  rw [ThetaScalar.sval_eq_zero _ h0 _ y hJ] at e
  exact (Units.mul_right_eq_zero _).1 e.symm

theorem exists_generic_map {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V}
    (hφ : Function.Injective φ) : ∃ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ := by
  have hi : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hφ
  obtain ⟨g, e⟩ : ∃ g : FractionRing R →+* FractionRing V,
      g.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
    ⟨IsLocalization.lift (M := nonZeroDivisors R) (g := (algebraMap V (FractionRing V)).comp φ) fun y =>
      IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (nonZeroDivisors.coe_ne_zero y)), IsLocalization.lift_comp _⟩
  have e' : spMap g ≫ jK R = jK V ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  exact ⟨spMap g, e'⟩

theorem exists_degData_of_thetaNZ : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ φ : R →+* V, Function.Injective φ → (IsLocalRing.maximalIdeal V).comap φ = I → ∀ (D : DegPre R) (D' : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G') (U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), Under U' U₀.toUnifPre → ThetaNZ G U.P.L.L → ∃ (psi : _) (h : _) (Dd : DegData R I) (hD : IsPullDeg φ (withPsi D psi h) D'.toPre), Dd.toPre = withPsi D psi h ∧ hD.e.hom.left ≫ pullback.fst _ _ = C.β ∧ HEq hD.w C.v ∧ hD.xe = C.xe := by
  intro h₁ h₂ hE R _ _ _ I hA V _ _ _ hV φ hφ hI D D' A A' G _ _ G' _ _ U U' U₀ F C hU hθ
  obtain ⟨hR, -, -, hP, -⟩ := hA
  have := hV.1
  have hV' : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : IsLocalRing.maximalIdeal V ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  have hIm : I.map φ ≤ IsLocalRing.maximalIdeal V := Ideal.map_le_iff_le_comap.2 hI.ge
  obtain ⟨hσ₁, hσ₂⟩ := _root_.GlobalTheory.fibNZ_prod_and_baseChange R V I _ φ D D'.toPre A G A' G' U U' F C
  obtain ⟨σ, hσ⟩ := hσ₁ hθ
  obtain ⟨f, hf, -⟩ := CompleteBaseExpansion.main h₁ h₂ hE R I hR hP.ne_top D A G U 1 σ
  obtain ⟨σ', f', hf', hσσ, hff⟩ := ExpCmp.expT_cmp R V I _ φ hIm D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := _root_.GlobalTheory.PsiExpansion.psiRel_of_expT h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 := by
    refine _root_.GlobalTheory.forall_ne_zero_of_psiRel V D'.toPre f' hrel' ?_
    obtain ⟨T, y, z, J, α, hJ, -, -, hu⟩ := _root_.GlobalTheory.PsiRing.exists_unit_term V _ hm D'.toPre A' G' U' 1 σ' f' hf' (hσ₂ 1 σ σ' hσσ hσ)
    refine ⟨α, ?_⟩
    by_contra h0
    push Not at h0
    rw [ThetaScalar.sval_eq_zero _ h0 _ z hJ] at hu
    exact not_isUnit_zero hu
  obtain ⟨psi, h, hrel⟩ := exists_psi_psiRel h₁ h₂ R D f (ne_zero_of_secCmp C.pbB.1.w hcmp hne')
  let E : DegPre R := withPsi D psi h
  have hrelE : PsiRel E (𝟙_ _) f := hrel
  have hrig : RigCmp φ E D'.toPre C.β C.v := _root_.GlobalTheory.rigCmp_of_cmp R V I _ φ hm hIm D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := exists_generic_map hφ
  have hpsi : PsiCmp E D'.toPre C.β C.v C.xe gam :=
    _root_.GlobalTheory.psiCmp_of_secCmp R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp hrelE hrel' (hne' 0) gam hgam
  have hev : E.PsiEven :=
    _root_.GlobalTheory.PsiRing.psiEven_descend h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    _root_.GlobalTheory.tauBimult_of_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨hD, hD₁, hD₂, hD₃⟩ :=
    _root_.GlobalTheory.PsiRing.exists_isPullDeg_of_cmp R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi hbi
  obtain ⟨ga, a, hS⟩ := exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := _root_.GlobalTheory.PsiRing.exists_basis_fibNZ h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hS χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hS hrelE hth χ q (b χ) hq (hb χ)
  have hbI : ∀ χ : D.X, χ ≠ 0 → b χ ∈ I := fun χ hχ => by
    obtain ⟨x, rfl⟩ := C.xe.surjective χ
    obtain ⟨m, hm₁, hm₂⟩ := GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi ga a hS x _
      (D'.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
    refine hI.le (Ideal.mem_comap.2 ?_)
    exact (congrArg (· ∈ IsLocalRing.maximalIdeal V) hm₂).mpr (Ideal.mul_mem_left _ _ hm₁)
  have hqu : IsUnit q := by
    obtain ⟨T, y, z, J, α, hJ, hz, h0, hu⟩ := _root_.GlobalTheory.PsiRing.exists_unit_term R I hP.ne_top D A G U 1 σ f hf hσ
    by_cases hα : α = 0
    · subst hα
      rw [hq _ _ z J hJ, show (lift (toUnit T) y).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom from Over.w _] at hu
      by_contra hn
      exact cst_not_isUnit T.hom z hz hn (isUnit_of_mul_isUnit_left hu)
    · rw [hb α T y z J hJ, h0 _ (hbI α hα), MulZeroClass.zero_mul] at hu
      exact absurd hu not_isUnit_zero
  obtain ⟨q, rfl⟩ := hqu
  have hin : ∀ (χ : D.X) (J : Ideal R), b χ ∈ J → E.PsiIn χ J := fun χ J hJ =>
    (PsiScalIn.main_local E ga a hS χ J).2 ⟨(q⁻¹).val * b χ, J.mul_mem_left _ hJ, by
      rw [map_mul]
      refine (congrArg (_ * ·) (hab χ).symm).trans ?_
      rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]⟩
  refine ⟨psi, h, ⟨E, hev, hbi, fun χ hχ => hin χ I (hbI χ hχ), fun n => ?_⟩, hD, rfl, hD₁, hD₂, hD₃⟩
  obtain ⟨s, hs⟩ := GlobalTheory.T.expansionCoef_mem_adic_pow R I hP.ne_top D A G U σ f th hf hth n
  refine s.finite_toSet.subset fun χ hχ => ?_
  by_contra hn
  exact hχ (hin χ _ (Ideal.pow_le_pow_right (Nat.le_succ n) (hs χ hn _ _ (hb χ))))

end GlobalTheory.PsiRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesIsoFieldPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesPullIso
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm

theorem units_of_vF {t : LB.Gen (LB.LinComb L φ ε)} {r : Sp F ⟶ Y} {z : Sp F} {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L z J) {u : Fˣ} (h : (u : F) = vF t r J) : stalkUnits z u = val t r z J :=
  Units.ext ((congrArg (stalkConst z) h).trans (const_vF t r hJ))
end Val

section Num
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

theorem good : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem stalk_θ (x y u : N.A) : stalkUnits z (N.θ x y u) = thS D z ν.J (ν.eA x) (ν.eA y) (ν.eA u) :=
  units_of_vF (good ν z) (ν.θ_eq x y u)

theorem stalk_σ (x : N.A) : stalkUnits z (N.σ x) = val (Z := Sp F) D.sym (ν.eA x).left z ν.J :=
  units_of_vF (good ν z) (ν.σ_eq x)

theorem const_rig : stalkConst z (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
    (TF (R := R) F).hom ν.J) = (val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J).val :=
  (const_vF _ _ (good ν z)).trans (congrArg Units.val (val_pull (good ν z) _ _ _).symm)

theorem stalk_ψ (χ : N.X) : stalkUnits z (N.ψ χ) =
    val (Z := Sp F) (D.psi (ν.eX χ)) (jFK (R := R) F) z ν.J * val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J :=
  Units.ext ((congrArg (stalkConst z) (ν.ψ_eq χ)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (const_vF _ _ (good ν z)) (const_rig ν z))))

theorem stalk_th (x : N.A) : stalkConst z (N.th x) * (val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J).val =
    sval (Z := Sp F) ν.th (ν.eA x).left z ν.J :=
  (congrArg _ (const_rig ν z).symm).trans ((map_mul _ _ _).symm.trans
    ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))

theorem stalk_pt {g : GtPtF D F} {c : N.Gt} (h : ν.Pt g c) (χ : N.X) :
    stalkUnits z (c.s χ) = val (Z := Sp F) (g.s (ν.eX χ)) (𝟙 (Sp F)) z ν.J :=
  units_of_vF (good ν z) (h.2 χ)
end Num

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem injective_of_compat (hF : ArcPull.Compat φ F) : Function.Injective φ := fun a b h =>
  IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective
    ((hF a).trans ((congrArg _ (congrArg _ h)).trans (hF b).symm)))

def pushEquiv (hF : ArcPull.Compat φ F) : (TF (R := R') F ⟶ D'.P.A) ≃* (TF (R := R) F ⟶ D.P.A) :=
  MulEquiv.ofBijective (MonoidHom.mk' (pushF (pull_grp hD) hF.base) (pushF_mul _ _))
    ⟨pushF_injective (pull_grp hD) hF.base, pushF_surjective (pull_grp hD) hF.base⟩

theorem exists_iso_of_th (hG : GlobalFnsSt) (hF : ArcPull.Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') (z : Sp F) (lam : ((Sp F).presheaf.stalk z)ˣ)
    (hth : ∀ x : TF (R := R') F ⟶ D'.P.A, sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
      (lam * om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) ν'.th x.left z ν'.J) :
    ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  have hJ := good ν z
  have hJ' := good ν' z
  let Ω : (TF (R := R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x => om hD.w z ν.J ν'.J x.left
  obtain ⟨h, hh⟩ : ∃ h : N'.A → Fˣ, ∀ x, stalkUnits z (h x) = Ω (ν'.eA x) * (Ω 1)⁻¹ :=
    ⟨fun x => (stalkUnits z).symm _, fun x => (stalkUnits z).apply_symm_apply _⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : N'.A ≃* N.A, ∀ x, ν.eA (Φ x) = pushF (pull_grp hD) hF.base (ν'.eA x) :=
    ⟨(ν'.eA.trans (pushEquiv hD hF)).trans ν.eA.symm, fun x => ν.eA.apply_symm_apply _⟩
  obtain ⟨e, he⟩ : ∃ e : N'.X ≃+ N.X, ∀ y, ν.eX (e y) = hD.xe (ν'.eX y) :=
    ⟨(ν'.eX.trans hD.xe).trans ν.eX.symm, fun x => ν.eX.apply_symm_apply _⟩
  have hc : ∀ χ, ν'.eA (N'.c χ) = cP D' _ (ν'.eX χ) := ν'.c_eq
  have a₁ : ∀ χ, jFK (R := R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := fun χ => (Category.assoc _ _ _).symm
  have a₂ : jFK (R := R') F ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).symm
  have rig : val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J = Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J :=
    (rig_val hD (Z := Sp F) _ _ hF.sq hJ hJ').trans
      (congrArg (fun q => om hD.w z ν.J ν'.J q * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J) a₂)
  refine ⟨{
    φ := Φ, h := h, lam := (stalkUnits z).symm lam, e := e
    h_one := ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    c_eq := fun χ => ?_, ψ_eq := fun χ => ?_ }, he, fun g g' c c' hg hg' H => ⟨?_, fun χ => ?_⟩⟩
  · apply (stalkUnits z).injective
    rw [hh, map_one, map_one, mul_inv_cancel]
  · apply (stalkUnits z).injective
    have k : thS D z ν.J (pushF (pull_grp hD) hF.base (ν'.eA x)) (pushF (pull_grp hD) hF.base (ν'.eA y))
        (pushF (pull_grp hD) hF.base (ν'.eA u)) =
        Ω (ν'.eA x * ν'.eA y * ν'.eA u) * (Ω (ν'.eA x * ν'.eA y))⁻¹ * (Ω (ν'.eA x * ν'.eA u))⁻¹ *
          (Ω (ν'.eA y * ν'.eA u))⁻¹ * Ω (ν'.eA x) * Ω (ν'.eA y) * Ω (ν'.eA u) * (Ω 1)⁻¹ *
          thS D' z ν'.J (ν'.eA x) (ν'.eA y) (ν'.eA u) :=
      thS_push (pull_grp hD) hF.base ((isGen_iff _).1 hD.w_gen) hG hJ hJ' _ _ _
    simp only [map_mul, hh, stalk_θ ν, stalk_θ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) D.sym (pushF (pull_grp hD) hF.base (ν'.eA x)).left z ν.J =
        Ω (ν'.eA x)⁻¹ * (Ω (ν'.eA x))⁻¹ * val (Z := Sp F) D'.sym (ν'.eA x).left z ν'.J :=
      PsiEvenPull.sym_pull hG hD (Z := Sp F) (ν'.eA x).left z hJ hJ'
    simp only [map_mul, map_inv, hh, stalk_σ ν, stalk_σ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkConst z).injective
    have k := stalk_th ν z (Φ x)
    have k' := stalk_th ν' z x
    rw [hΦ, rig] at k
    have k₁ := k.trans ((hth (ν'.eA x)).trans (congrArg _ k'.symm))
    rw [map_mul, ← stalkUnits_val, map_mul, hh, MulEquiv.apply_symm_apply]
    refine (Units.mul_left_inj (Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J)).1 (k₁.trans ?_)
    have := (Ω 1).inv_mul
    simp only [Units.val_mul]
    linear_combination (-(lam.val * (Ω (ν'.eA x)).val * stalkConst z (N'.th x) *
      (val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J).val)) * this
  · apply ν.eA.injective
    rw [hΦ, ν.c_eq, he, hc]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hF.base.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) (D.psi (hD.xe (ν'.eX χ))) (jFK (R := R) F) z ν.J =
        (Ω (cP D' _ (ν'.eX χ)))⁻¹ * val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J :=
      (psi_val hD (Z := Sp F) _ _ hF.sq hJ hJ' _).trans (congrArg (fun q => (om hD.w z ν.J ν'.J q)⁻¹ *
        val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J) (a₁ _))
    rw [map_mul, hh, stalk_ψ ν, stalk_ψ ν', he, k, rig, hc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply ν.eA.injective
    refine hg.1.trans (Eq.trans ?_ (hΦ _).symm)
    rw [hg'.1]
    exact Over.OverMorphism.ext H.1.symm
  · apply (stalkUnits z).injective
    have k₀ := pullGt_val hD H (ν'.eX χ) (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at k₀
    have k : val (Z := Sp F) (g.s (hD.xe (ν'.eX χ))) (𝟙 (Sp F)) z ν.J =
        (Ω (cP D' _ (ν'.eX χ) * g'.b))⁻¹ * Ω (cP D' _ (ν'.eX χ)) * Ω g'.b * (Ω 1)⁻¹ *
          val (Z := Sp F) (g'.s (ν'.eX χ)) (𝟙 (Sp F)) z ν'.J := k₀
    show stalkUnits z (c.s (e χ) * h (N'.c χ * c'.b)) = stalkUnits z (c'.s χ * h (N'.c χ) * h c'.b)
    rw [map_mul, map_mul, map_mul, hh, hh, hh, stalk_pt ν z hg, stalk_pt ν' z hg', he, k, map_mul, hc, hg'.1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem exists_values_iso : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K) (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing K) F], ArcPull.Compat φ F → ∀ (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧ ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' → IsPullGtF φ hD F g g' → I.Rel c' c := by
  intro hG R K _ _ _ φ D D' hD F _ _ _ hF N N' ν ν'
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.exists_unit_generating_section_pull R K φ (injective_of_compat hF) D D' hD ν.th ν'.th ν.th_gen ν'.th_gen
  let z : Sp F := IsLocalRing.closedPoint F
  refine exists_iso_of_th hD hG hF ν ν' z (TauTwist.unitAt (Z := Sp F) (TF (R := K) F).hom z c) fun x => ?_
  have := hc (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
  exact this.trans (congrArg (fun q => (TauTwist.unitAt (Z := Sp F) q z c * om hD.w z ν.J ν'.J x.left).val *
    sval (Z := Sp F) ν'.th x.left z ν'.J) (Over.w x))

end GlobalTheory.ValuesPullIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleExtensionThetaSectionSemiAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_extension_with_section : Semi.extend_existsSt.{0} → Out.MulNSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → C.HasTests → C.TorsSec n → T.Few n → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  intro hE hM hS C L T n hG hT hTors hFew
  have hB : T.BTest L := _root_.GlobalTheory.ZJ.bTest_of_surjective_mulN hS C L T
  have hO : IsOpen (T.Om L) := (GlobalTheory.ZJ.etale_mulN_and_isOpen_om_of_isSemiAbelian C L T hG hM).2
  obtain ⟨ν, hν⟩ := _root_.GlobalTheory.ZJ.Core.Theta.exists_norms hE C L T hT hB
  have h6 : L.CompanionTheory (T.Om L) := _root_.GlobalTheory.ZJ.Core.Law.six_of_few hE C L T n hT hB hTors hFew
  have hγ := GlobalTheory.ZJ.Core.exists_gen_normOne C L T (T.Om L) ν hO hν h6
  obtain ⟨-, hlft, -, hint, hflat, -, hop, -⟩ := core_basic C
  have := C.lft
  have hsm : Smooth C.GG.hom := by
    have := L.smooth
    exact SmoothOfRelativeDimension.smooth C.g _
  have hN : Geo.Tor.IsNormalScheme C.G.toScheme := fun x =>
    GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth C.GG.hom C.normal x
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  exact _root_.GlobalTheory.exists_local_section_ne_zero_on_fibres C L T (T.Om L) ν hO hν h6
    (@GlobalTheory.exists_lineBundle_of_normOne_generators C.G.toScheme C.A.left hint (C.GG.hom ≫ C.π) hflat hlft' hN C.a hop T.L.L T.L.isLB ν hν.isNrm hγ)

end GlobalTheory.ZJ
end

