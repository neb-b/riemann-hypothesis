module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoTranslateEvenCubicalBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismUniformisedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GroupAdjoint

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem exists_adjoint {K : Type} [CommRing K] (Q : PolAV (Sp K)) (f : Q.A ⟶ Q.A) [IsMonHom f] :
    ∃ x : Q.A ⟶ Q.A, IsMonHom x ∧ ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A),
      lam (cls Q.L Q.isLB) (a ≫ f) b = lam (cls Q.L Q.isLB) a (b ≫ x) := by
  have := Q.isAb.comm
  have hd : IsDual Q.A Q.A (abelian₂ Q.A Q.L) := CompanionTheory.PfDual.kTrivDual K Q.A Q.g Q.isAb Q.smoothDim Q.L Q.isLB Q.ktriv
  have hΛ : (abelian₂ Q.A Q.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = lam (cls Q.L Q.isLB) a b := fun Y a b ↦ by
    rw [evc, show cls _ hΛ = lam (cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
      cls_cube_two Q.isLB _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp K)) (a a' b : Y ⟶ Q.A), evc hΛ (a * a') b = evc hΛ a b + evc hΛ a' b :=
    (isAdditive_iff hΛ).1 hd.additive
  have l₂ : ∀ (Y : Over (Sp K)) (a b b' : Y ⟶ Q.A), evc hΛ a (b * b') = evc hΛ a b + evc hΛ a b' := fun Y a b b' ↦ by
    rw [e, e, e, lam_comm, lam_comm _ a b, lam_comm _ a b', ← e, ← e, ← e]
    exact l₁ _ _ _ _
  have a₂ : IsAdditive (swap (abelian₂ Q.A Q.L)) := (BirigidLift.isAdditive_swap_iff hΛ).2 l₂
  have hM := pull_isLB hΛ (lift (fst Q.A Q.A ≫ f) (snd Q.A Q.A)).left
  have m : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hM a b = evc hΛ (a ≫ f) b := fun Y a b ↦ by
    rw [evc_ev hΛ]
    simp only [lift_fst_assoc, lift_snd]
  obtain ⟨x, hx, ex⟩ := BirigidLift.exists_hom hd a₂ hM
    ((isAdditive_iff hM).2 fun Y u u' t ↦ by rw [m, m, m, MonObj.mul_comp, l₁])
    ((BirigidLift.isAdditive_swap_iff hM).2 fun Y u t t' ↦ by rw [m, m, m, l₂])
  refine ⟨x, hx, fun Y a b ↦ ?_⟩
  rw [← e, ← e, ← m]
  exact BirigidLift.evc_of_cls hd.isLB hM ex a b

theorem exists_adjoint_on_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U g hg
  have hN : IsNoetherianRing R := hR.1.1
  have hI : IsIntegrallyClosed R := hR.1.2.2.1
  have := U.gen_hom
  have hL := U.LG.isLB
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨x, hx, ex⟩ := exists_adjoint A (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (jK R) := .fractionField R (FractionRing R)
  obtain ⟨g', ⟨hg', eg'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R) hj hG hG (U.gen.hom ≫ x ≫ U.gen.inv)
  refine ⟨g', hg', ?_⟩
  have := hG.smooth
  have := hG.geomConnected
  have := GlobalTheory.smooth_tensorObj_hom G G
  have := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  have h₁ : (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  refine _root_.GlobalTheory.Mum.lbIso_of_generic_local R (G ⊗ G) (1 : 𝟙_ _ ⟶ G ⊗ G).left (Over.w _) _ _ h₁ h₂ ?_
  refine (cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).1 ?_

  have ec : pull U.gen.hom.left (cls A.L A.isLB) = pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) := by
    rw [← cls_pull A.isLB _ (pull_isLB A.isLB _), ← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 U.ext
  have key : ∀ a b : G ⊗ G ⟶ G, pull (pullback.fst (G ⊗ G).hom (jK R)) (lam (cls U.LG.L hL) a b) =
      lam (cls A.L A.isLB) ((Over.pullback (jK R)).map a ≫ U.gen.hom) ((Over.pullback (jK R)).map b ≫ U.gen.hom) := by
    intro a b
    rw [← lam_pull, ec, lam_pull_of_isGrpPullback hp]
    refine GlobalTheory.CompanionTheory.DualScheme.pull_lam_of_left (T' := Over.mk (_ ≫ jK R)) _ _ ?_ ?_
    · exact (ExtUnique.pullback_map_left_fst (jK R) a).symm
    · exact (ExtUnique.pullback_map_left_fst (jK R) b).symm
  rw [cls_pull h₁, cls_pull h₂, cls_cube_two hL, cls_cube_two hL, key, key, Functor.map_comp, Functor.map_comp, eg']
  have := ex _ ((Over.pullback (jK R)).map (fst G G) ≫ U.gen.hom) ((Over.pullback (jK R)).map (snd G G) ≫ U.gen.hom)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using this

end GlobalTheory.Mum.GroupAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparatingStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleSections_vanishing_origin_separating : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB → Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)), (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧ ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  first | (exact @GlobalTheory.RelAmpleSep.exists_sec_sep_origin) | (exact GlobalTheory.RelAmpleSep.exists_sec_sep_origin) | (intros; apply GlobalTheory.RelAmpleSep.exists_sec_sep_origin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOrigin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem eq_comp_section_of_apply_eq {K L : Type} [Field K] [Field L] {X : Scheme.{0}} (t : X ⟶ Sp K)
    (e : Sp K ⟶ X) (he : e ≫ t = 𝟙 _) (q : Sp L ⟶ Sp K) (y : Sp L ⟶ X) (hy : y ≫ t = q)
    (p : Sp L) (p' : Sp K) (h : y p = e p') : y = q ≫ e := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective y
  obtain ⟨⟨z', α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective e
  simp only [Scheme.SpecToEquivOfField_symm_apply] at he hy h ⊢
  have hz : z = z' := by simpa using h
  subst hz
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField z ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at he
  rw [Category.assoc, ← hc, ← Spec.map_comp] at hy
  have h₁ := Spec.map_injective he
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun r => r.hom k) h₁
  subst hy
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  ext w
  have e₂ : c.hom (α.hom w) = w := α.hom.injective (e₁ _)
  simp [e₂]

theorem exists_apply_ne_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 →
    ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  intro K _ A B f hf
  by_contra hcon
  push_neg at hcon
  apply hf
  refine ext_of_pt_eq K A B f 0 fun x => ?_
  rw [zero_hom]
  let e : Sp K ⟶ B.X.left := (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X)
  have h1 : (x ≫ (1 : A.X ⟶ B.X)).left = (ptOver K (AlgebraicClosure K)).hom ≫ e := by
    have hP : (toUnit (ptOver K (AlgebraicClosure K))).left = (ptOver K (AlgebraicClosure K)).hom := by
      simpa using Over.w (toUnit (ptOver K (AlgebraicClosure K)))
    have hU : toUnit (Over.mk (𝟙 (Sp K))) = 𝟙 _ := toUnit_unique _ _
    simp only [e, Hom.one_def, ← Category.assoc, comp_toUnit, hU, Category.id_comp, Over.comp_left, hP]
  apply Over.OverMorphism.ext
  rw [h1]
  exact eq_comp_section_of_apply_eq B.X.hom e he _ _ (Over.w (x ≫ f.hom))
    (IsLocalRing.closedPoint _) (IsLocalRing.closedPoint K) (hcon _)

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitArc

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dm : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {T : Formalism.L2.Pj.CDVR}

theorem tateCl_of (β : O →+* c.F) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ)
    (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M)
    (h : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
      ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre oD F),
        (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧
        (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧
        ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a)) :
    TateCl D oD hϖ Dm β b hdiv pA pM := by
  intro F _ _ _ z hz
  letI := H.starRing
  obtain ⟨I, hζ, e₂, e₃⟩ := h F z hz
  have hw := GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)
  have ht := isScalarForm_tF D oD hϖ
  have hq := psiRel0 (H := H) D hϖ
  have hR := isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (dvd_refl l.M') hdiv)
  let s : D.toPre.X → D.toPre.X → Fˣ := fun y x =>
    Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (rF D hϖ l.M' y x)
  have hs : IsRootForm (𝓞 E) l.M' (tF D hϖ) s :=
    ⟨hR.1.map _, fun y x => by
      show (Units.map _ _) ^ _ = _
      rw [← map_pow, hR.2 y x]
      rfl⟩
  obtain ⟨s', I', s₁, -, s₃, s₄, s₅⟩ := exists_tateIsoQ_twist D.tau_bimult hw ht oD l.M' s hs I
  have lev : ∀ {k : ℕ} (hk : 0 < k) (hd : k ∣ l.M') (p : QkPt D.toPre (FractionRing T.V) k) (v : Dm.La),
      (∀ q, QkExt (algebraMap _ F) p q → QkPt.Equiv D.toPre F q (I.ev k v)) → ∀ q',
      QkExt (algebraMap _ F) (qkScale hw ht hq (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ hd hdiv)) _ p) q' →
      QkPt.Equiv (D0 (H := H) D hϖ) F q' (I'.ev k v) := by
    intro k hk hd p v he q' hq'
    obtain ⟨q, rfl⟩ := (qkScaleEquiv hw ht hq (s₁ k hk) _).surjective q'
    have e := qkRel_qkScaleEquiv (D := D.toPre) (hψ := (D0 (H := H) D hϖ).psi_gen) hw ht hq (s₁ k hk) q
    refine e.equiv hw ht hq (s₁ k hk) (s₅ k hk v) (he q (QkRel.qkExt_of (fun y x => ?_)
      (qkRel_qkScale hw ht hq (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ hd hdiv)) p) e hq'))
    rw [s₃ k hk hd]
    show (Units.map _ _) ^ _ = _
    rw [← map_pow]
    congr 1
    obtain ⟨j, hj⟩ := dvd_of_dvd D hϖ (dvd_refl l.M') hdiv y x
    obtain ⟨i, hi⟩ := hd
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
    have hi0 : (i : ℤ) ≠ 0 := by
      rintro h
      have : i = 0 := by exact_mod_cast h
      rw [this, mul_zero] at hi
      omega
    simp only [rF, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hj, hi, Nat.mul_div_cancel_left _ hk]
    push_cast
    rw [Int.mul_ediv_cancel_left _ (mul_ne_zero hk0 hi0), _root_.mul_assoc, Int.mul_ediv_cancel_left _ hk0]
    ring
  exact ⟨I', by rw [s₄]; exact hζ, fun v => lev l.A_pos (Nat.dvd_lcm_right l.M l.A) _ v (e₂ v),
    fun v _ q hq => lev (lt_of_lt_of_le (by decide) l.three_le) (Nat.dvd_lcm_left l.M l.A) _ v (e₃ v) q hq⟩

end GlobalTheory.TraitArc


open GlobalTheory.TraitArc in
theorem GlobalTheory.TraitArc.exists_input_recovering : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ρ : R →+* V) (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), GlobalTheory.LN.CDvr V ∧ Function.Injective ρ ∧ ρ.Finite ∧ Irreducible ϖ ∧ ∀ (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp V ⟶ Y.X), Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y → ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal V) t), Nonempty (IsPullDeg ρ D.toPre P.D.toPre) := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP l c O _ β hβ V₁ _ _ _ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁
  have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
  obtain ⟨T, ρ, b, ϖ, D', hρ, hρf, hb, hϖ, ⟨hD⟩, hdvd, hrat⟩ :=
    _root_.GlobalTheory.TraitInputExt.exists_ext_dvd_rational R D O V₁ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁ (2 * l.M') (by omega)
  have hBase : Base R := ⟨by haveI := hR.1; exact ⟨inferInstance, inferInstance, inferInstance, hR.2.1⟩, hR.2.2⟩
  obtain ⟨inst, o', hP'⟩ := GlobalTheory.Mum.pelOK_of_isPullDeg R hBase E H Dm D o hP T.V ρ hρ D' ⟨hD⟩
  letI := inst
  have hX' : Nontrivial D'.toPre.X := hD.xe.toEquiv.nontrivial
  have hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D' hϖ a a' := fun a a' => by
    have := hdvd _ (isQ_qv D' hϖ) a a'
    exact_mod_cast this
  obtain ⟨pA, pM, hT⟩ := GlobalTheory.T.exists_rational_tate_pairs_unitaryType E H Dm l c O β hβ T b hb D' o' hP' (fun k hk => hrat k (hk.mul_left 2))
  have hLie : LieCl D' o' Dm β b := by
    intro F _ _ _ r _ τ
    obtain ⟨n, h₁, h₂⟩ := (hP'.2.2.2 F).1 τ
    refine ⟨n, h₁, ?_⟩
    split_ifs
    · exact h₂
    · exact h₂.trans hP'.1
  have hTate := tateCl_of β b D' o' hϖ hdiv pA pM hT
  refine ⟨T.V, T.cr, T.dom, inferInstance, ρ, b, ϖ, arc D' o' hϖ β b hX' hP'.2.2.1 hdiv pA pM hLie hTate,
    ⟨T.dvr, T.cpl, T.ch0⟩, hρ, hρf, hϖ, ?_⟩
  intro Xo Y y hy
  obtain ⟨t, m, P, ⟨hD₂⟩⟩ := GlobalTheory.T.exists_pullDeg_arcData_at_uniformiser E H Dm l c O β T b D' o' ϖ hϖ hX' hP'.2.2.1 hdiv pA pM hLie hTate Xo Y y hy
  refine ⟨t, m, P, ?_⟩
  have := GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R T.V T.V ρ (RingHom.id T.V) D.toPre D'.toPre P.D.toPre
    Function.injective_id ⟨hD⟩ ⟨hD₂⟩
  rwa [RingHom.id_comp] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBertiniPolyDiscrepancySncBoundary
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem exists_mvPolynomial_of_forall_nhds {X : Type} [TopologicalSpace X] [CompactSpace X]
    {ι : Type} (P : (ι → ℂ) → X → Prop)
    (h : ∀ x₀ : X, ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧
      ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ x ∈ W, P c x) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ x, P c x := by
  classical
  choose W hW hxW Q hQ hP using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨∏ x ∈ t, Q x, Finset.prod_ne_zero_iff.2 fun x _ => hQ x, fun c hc y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  rw [map_prod] at hc
  exact hP x c (Finset.prod_ne_zero_iff.1 hc x hx) y hy

theorem exists_poly_neg_one_lt_discrep_member : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) [Fintype ι] (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (u i) * s i → ∀ y : Y, (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c : ℚ) (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c < 1 → (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g → (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y → -1 < discrep E η m g - c * E.ord f := by
  intro Y _ _ q n _ hproj B hB A ι _ s hs
  haveI : IsProper q := ((isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hproj).1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  refine (exists_mvPolynomial_of_forall_nhds (X := Y) (fun c y =>
    ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (c i) * s i →
    (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c' : ℚ)
      (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c' < 1 →
      (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g →
      (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y →
      -1 < discrep E η m g - c' * E.ord f) fun y₀ => ?_).imp
    fun Q ⟨hQ, hQc⟩ => ⟨hQ, fun c hc t ht y => hQc c hc y t ht⟩
  obtain ⟨W, hW, z, w, u, e, f, hfr, he, hf, hch⟩ := _root_.GlobalTheory.PairStep.exists_sncChart_isEqn_affine Y q n B hB A ι s hs y₀
  obtain ⟨Q, hQ, hQc⟩ := _root_.GlobalTheory.StrataBertini.bertini_strata_cotangent Y q n W z hfr ι f
  refine ⟨W, W.isOpen, hW, Q, hQ, fun c hc y hy t ht hgen η K Θ m c' g f' hη hK hm hΘ hc' hmult
    hg hf' E hE => ?_⟩
  obtain ⟨J, hJ, hJz⟩ := hch y hy
  have hFv : fnOf W (gen_mem hy) (∑ i, algX q W (c i) * f i) = ((t * e : Y.functionFieldˣ) : Y.functionField) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Units.val_mul, ht, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hf i, ← RingHom.comp_apply, fnOf_comp_algX, mul_assoc]
  have hunit : UnitAt y ((f' : Y.functionField) / ((t * e : Y.functionFieldˣ) : Y.functionField)) :=
    ((CartierDiv.isEqn_principal t y).add (he y hy)).iff_unitAt.1 hf'
  have hbas : ∃ i, y ∈ Y.basicOpen (f i) := by
    obtain ⟨i, hi⟩ := hgen
    refine ⟨i, (unitAt_fnOf_iff hy (gen_mem hy) (f i)).1 ?_⟩
    rw [hf i]
    exact (he y hy).generatesAt_iff.1 hi
  rw [_root_.GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum Y q n B y W hy z J w u hJ η K Θ m g hη hK hm hΘ hg E hE]
  exact _root_.GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep Y q n B y W hy z J w u hJ hJz _ (fun h => hQc c hc y hy hbas J h) (t * e) f'
    (fun j => (Θ.mult (w j) : ℚ) / m) c' hFv.symm hunit (fun j hj => by
      have := hmult (w j) (hJ.spec j hj)
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      rw [div_lt_one hm']
      exact_mod_cast this) hc' E hE

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedAlgebraicFormFderivUniformisedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_algebraic_form_fderiv_uniformised : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ), DifferentiableOn ℂ h (pre u.ex U.1) → (∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) → ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  first | exact @GlobalTheory.CechPer.exists_closed_form_fderiv_eq | exact GlobalTheory.CechPer.exists_closed_form_fderiv_eq | (intros; apply GlobalTheory.CechPer.exists_closed_form_fderiv_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureDescendedLineBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_cubicalStr_of_descended_bundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (L : LB G.left) (hL : L.IsLB), LBIso U'.LG.L (L.pull β) → ∀ (rig : LB.Gen (L.pull (eSec G))) (hr : rig.IsGen), Nonempty (CubicalStr G (⟨L, rig, hL, hr⟩ : RigLB G)) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hgal D D' hD A' G' _ _ hG' U' a G _ _ β hG hβ hact L hL _ rig hr
  obtain ⟨A, gen, -, -, -, -⟩ := _root_.GlobalTheory.Mum.GenDesc.polarisedGeneric R hR R' ρ hρ hgal D D' hD A' G' hG' U' a G β hG hβ hact
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hR
  have : IsProper (pullback.snd G.hom (jK R)) := by
    have : IsProper A.A.hom := A.isAb.proper
    have : IsIso gen.hom.left := ((Over.forget _).mapIso gen).isIso_hom
    have hw : gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w gen.hom
    rw [← hw]
    infer_instance
  obtain ⟨L₀, c, rfl⟩ := GlobalTheory.RigCube.exists_rigLB_cubicalStr R G hG this L hL
  exact ⟨⟨c.t, c.isGen, c.face, c.cubeSymmetric_swap_first, c.cubeSymmetric_swap_last, c.cocycle⟩⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_even_translate_split : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SplitClosed G → TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ EvenOn P₁ := by
  intro R _ _ _ hR G _ _ hG hS hT P A gen hgen hL
  obtain ⟨a, ha, hE⟩ := _root_.GlobalTheory.EvenTransl.exists_even_of_transl R hR G hG hS hT P A gen hgen hL
  obtain ⟨P₁, A₁, gen₁, h1, h2, h3, h4⟩ := _root_.GlobalTheory.Mum.exists_transl_pkg R hR G hG P A gen hgen hL a ha
  exact ⟨P₁, A₁, gen₁, h1, h2, h3, hE P₁ h4⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSubgroupSchemeOfGaloisStablePoiStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_subgroupScheme_of_galoisStable_points : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (H : Over (Sp K)) (_ : GrpObj H) (i : H ⟶ A.X), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ x : A.Pt, x ∈ G ↔ ∃ y, y ≫ i = x := by
  first | (exact @GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points) | (exact GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points) | (intros; apply GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_mumford_bundle_polarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ PP : LB (G2 G).left, PP.IsLB → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((PP.pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left)) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((PP.pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)]) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (PP.pull β₂) := by
  first | exact @GlobalTheory.MumDesc.exists_extLam_finExt | exact GlobalTheory.MumDesc.exists_extLam_finExt | (intros; apply GlobalTheory.MumDesc.exists_extLam_finExt <;> assumption)
end

