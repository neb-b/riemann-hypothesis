module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2483
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedCubicalRootPolarisationEtale
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.PolBundleLocEt

open GlobalTheory.PolRoot GlobalTheory.PolBundleLoc

theorem exists_rigLB_sFam_etale :
    ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ y : Sp R ⟶ F.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R'), IsAdicComplete (maximalIdeal R') R' ∧ IsLocalHom ρ ∧ Function.Injective ρ ∧ ρ.Finite ∧ ρ.Etale ∧ ∃ (B : Over (Sp R')) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left) (M : RigLB B) (_ : CubicalStr B M), IsGrpPullback B F.univ.A (spMap ρ ≫ y) β ∧ IsSquare β β₂ ∧ RelAmple B M.L ∧ KTriv B M.L ∧ LBIso (abelian₂ B M.L) (F.univ.P.pull β₂) := by
  intro o _ ζ g n F R _ _ _ hR y
  haveI : IsAdicComplete (maximalIdeal R) R := hR
  haveI : HenselianLocalRing R :=
    { is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }
  have hAb := F.univ.ab
  have hP := F.univ.isLB
  let k := ResidueField R
  let t₀ : Sp k ⟶ F.X := spMap (residue R) ≫ y

  have h₁ : Root F.univ.A F.univ.P (spMap (algebraMap k (AlgebraicClosure k)) ≫ t₀) :=
    root_geom F (AlgebraicClosure k) _

  obtain ⟨B, hB, h₂⟩ := _root_.GlobalTheory.RootFG.root_fg F.X F.univ.A hAb F.univ.P hP k t₀ (AlgebraicClosure k) h₁
  haveI : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : Algebra.IsIntegral k B := ⟨fun b => (isIntegral_algHom_iff B.val Subtype.val_injective).1 (Algebra.IsIntegral.isIntegral (R := k) (b : AlgebraicClosure k))⟩
  haveI : Module.Finite k B := Algebra.IsIntegral.finite

  obtain ⟨C, _, _, _, _, hC, ⟨ιC⟩, hdom⟩ := _root_.GlobalTheory.SepRing.exists_complete_local_geomDomain k B inferInstance
  let tC : Sp C ⟶ F.X := spMap (algebraMap k C) ≫ t₀
  have h₃ : Root F.univ.A F.univ.P (spMap (residue C) ≫ tC) := by
    refine root_congr ?_ (h₂.comp hAb (spMap ιC.toRingHom))
    simp only [tC, ← Category.assoc, spMap_comp']
    congr 2
    exact ιC.comp_algebraMap.trans (IsScalarTower.algebraMap_eq k C (ResidueField C))
  have h₄ : Root F.univ.A F.univ.P tC :=
    _root_.GlobalTheory.PolRootComplete.root_of_residue F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 C hC tC h₃

  obtain ⟨B', hB', h₅⟩ := _root_.GlobalTheory.RootFG.root_fg F.X F.univ.A hAb F.univ.P hP k t₀ C h₄
  have hdom' : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B') := by
    intro K _ _ h1 h2
    haveI := hdom K h1 h2
    let m : K ⊗[k] B' →ₐ[K] K ⊗[k] C := Algebra.TensorProduct.map (AlgHom.id K K) B'.val
    have hm : Function.Injective m := by
      have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) (B'.val.toLinearMap)
        Subtype.val_injective
      exact this
    exact hm.isDomain m
  obtain ⟨k'', _, _, hfin, hsep, ⟨ψ⟩⟩ := _root_.GlobalTheory.SepPoint.exists_sepPoint k B' ((Subalgebra.fg_iff_finiteType B').1 hB') hdom'
  have h₆ : Root F.univ.A F.univ.P (spMap (algebraMap k k'') ≫ t₀) := by
    refine root_congr ?_ (h₅.comp hAb (spMap ψ.toRingHom))
    rw [← Category.assoc, spMap_comp']
    congr 2
    exact ψ.comp_algebraMap

  haveI : Module.Finite (ResidueField R) k'' := hfin
  haveI : Algebra.IsSeparable (ResidueField R) k'' := hsep
  obtain ⟨R', _, _, hfinR, het, _, ⟨ε⟩⟩ := exists_etale_lift_of_isSeparable R k''
  haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'
  haveI : IsLocalHom (algebraMap R R') :=
    ((local_hom_tfae (algebraMap R R')).out 1 5).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' := Algebra.FormallyUnramified.map_maximalIdeal
  have hcR' : IsAdicComplete (maximalIdeal R') R' := by
    have := isAdicComplete_map_of_finite (maximalIdeal R) R'
    rwa [hm] at this
  haveI : IsNoetherianRing R' := isNoetherian_of_tower R inferInstance
  let ρ : R →+* R' := algebraMap R R'
  obtain ⟨φ, hφ⟩ := residue_lift R R' k'' ε
  let T : Sp R' ⟶ F.X := spMap ρ ≫ y
  have h₇ : Root F.univ.A F.univ.P (spMap (residue R') ≫ T) := by
    refine root_congr ?_ (h₆.comp hAb (spMap φ))
    simp only [T, t₀, ← Category.assoc, spMap_comp']
    congr 2
    rw [← RingHom.comp_assoc, hφ]
    exact (ResidueField.map_comp_residue ρ).symm
  obtain ⟨B₁, _, _, β, β₂, hβ, hsq, L, hL, hΛ⟩ :=
    _root_.GlobalTheory.PolRootComplete.root_of_residue F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 R' hcR' T h₇
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hβ
  have hP' : (F.univ.P.pull β₂).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb hP _ _
  have hker := GlobalTheory.SiegelPull.nondeg_pull hβ hsq hP hP' ((GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl) F.princ.2
  obtain ⟨M, hM, ⟨hcub⟩⟩ := exists_rigLB_cubical R' B₁ hB₁ L hL
  have hK := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ B₁ hB₁ (F.univ.P.pull β₂) hP' hker L hL hΛ
  have hA := _root_.GlobalTheory.MumAmple.relAmple_of_lam_iso_univ F R' T B₁ β β₂ hβ hsq L hL hΛ
  subst hM
  have hinj : Function.Injective ρ := by
    letI : Algebra.Etale R R' := het
    haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective R R'
  exact ⟨R', inferInstance, inferInstance, ρ, hcR', inferInstance, hinj, RingHom.finite_algebraMap.mpr hfinR,
    RingHom.etale_algebraMap.mpr het, B₁, inferInstance, inferInstance, β, β₂, M, hcub,
    hβ, hsq, hA, hK, hΛ⟩

end GlobalTheory.PolBundleLocEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtendingModelAboveThetaSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

theorem GlobalTheory.GSep.exists_zhAbove : ∀ (X₁ : GlobalTheory.GSep.GSet), ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z),
    GlobalTheory.GSep.ZHAbove X₁ Y πY := by
  intro X₁
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver X₁.projM
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  exact ⟨Y, q, U₀, EE, ⟨G⟩, hO, hE, hq, hqp⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantDvdPowOverDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DvrScale

open GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale GlobalTheory.Poinc.IntTerm.DvrScale
open Classical


attribute [local instance] gtGroup in
theorem exists_dvd_pow : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ b, ∀ a, ∃ (w : X) (r : V), 𝔪.YY a w ∧ 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (t w) := by
  intro I X₁ z₁ act V _ _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hc : IsAdicComplete (maximalIdeal V) V := 𝔪.cn.2.2.1
  obtain ⟨hL, hL₂⟩ := abelianSchemeLaws_all
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have hm := odd_level' X₁.ρ
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, hc⟩
  have hB := 𝔪.D.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using QForm.exists_QVal hϖ 𝔪.D
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨t', ht⟩ := hsec 1 X₁.ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW 𝔪.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t'
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set Fc := AlgebraicClosure (FractionRing V) with hF
  set y₀ : X₁.S.R →+* Fc := (algebraMap (FractionRing V) Fc).comp 𝔪.yK with hy₀
  have tv : ∀ a z J, Good 𝔪.A.L z J → cst (R := V) Fc z sc *
      @id ((TF (R := V) Fc).left.presheaf.stalk z) (sA th (ptSecT 𝔪.A.A (x a)).left z J) =
      cst (R := V) Fc z (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) * @id ((TF (R := V) Fc).left.presheaf.stalk z)
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := X₁.ρ.th_val a
      rw [← powFrame_one' (X₁.ρ.pt a) (X₁.ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) := fun a => by
    obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, (f₁ _ _).2 hq.symm⟩
  have yyOf : ∀ a q (χ : 𝔪.D.toPre.X), QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) →
      𝔪.YY a (𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y)) := fun a q χ hq =>
    ⟨qkShift hB q χ, x a, by
      rw [AddEquiv.apply_symm_apply]
      show q.y + (X₁.S.r * X₁.S.N) • χ = _
      rw [add_comm],
      (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB q _))), hx a⟩
  have hM2 : (X₁.S.r * X₁.S.N) ^ 2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := Fc)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) Fc).left) 𝔪.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    have z1 : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a =>
      (map_eq_zero_iff _ (algebraMap (FractionRing V) Fc).injective).1 (z0 a)
    refine ⟨0, fun a => ?_⟩
    obtain ⟨q, hq⟩ := ex a
    refine ⟨_, 0, yyOf a q 0 hq, ?_⟩
    rw [z1 a, zero_pow hM2, map_zero, zero_mul, zero_mul]

  have tv' : ∀ a z J, Good 𝔪.A.L z J → sA th (ptSecT 𝔪.A.A (x a)).left z J =
      @id ((TFK (R := V) Fc).left.presheaf.stalk z)
        (cst (R := V) Fc z (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)) *
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = 0 → v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc :=
    fun a h => by rw [split a, h, add_zero]
  have h2 : 2 ≤ X₁.S.r * X₁.S.N := X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨b, hb⟩ : ∃ b, v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) = v sc := by
    obtain ⟨p₀, hp₀⟩ := exists_qkPt (F := Fc) H.1.mulN (Or.inr H.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) hm.pos.ne' 0
    obtain ⟨q', x', -, hx', -, hval⟩ := (key p₀ (f p₀) ((f₁ _ _).2 rfl)).2 (X₁.S.r * X₁.S.N) h2 dvd_rfl hp₀
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    exact ⟨a', nz a' (hval _ _ (he a') (tv' a'))⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
  refine ⟨b, fun a => ?_⟩
  obtain ⟨q, hq₁⟩ := ex a
  obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((X₁.S.r * X₁.S.N) • χ + q.y) = k)
    ⟨0, by
      rintro _ ⟨χ, rfl⟩
      by_cases c : (X₁.S.r * X₁.S.N) • χ + q.y = 0
      · rw [c, QForm.Q_zero hϖ 𝔪.D hQ]
      · exact zero_le_one.trans (QForm.Q_pos hϖ 𝔪.D hQ c)⟩ ⟨_, 0, rfl⟩
  have hk := ((key q _ hq₁).1 _ _ (he a) (tv' a)).1
    ((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) fun χ' =>
      div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _)
  set w := 𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y) with hw
  have hew : 𝔪.e₈ w = (X₁.S.r * X₁.S.N) • χ + q.y := AddEquiv.apply_symm_apply _ _
  have hmono : v (algebraMap (FractionRing V) Fc (algebraMap V (FractionRing V) (t w))) =
      (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨u, hpc⟩ := 𝔪.psi w
    rw [hew] at hpc
    exact hv _ _ (hasVal_of_unit_mul u (GlobalTheory.ValForm.hasVal_coord (hQ _) hpc))
  have hb0 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := fun h => hvs (by
    rw [← hb]; show v (algebraMap (FractionRing V) Fc (𝔪.yK _)) = ⊤; rw [h, map_zero, AddValuation.map_zero])
  have hne : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (t w) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hb0)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
        (let ⟨_, h⟩ := 𝔪.psi w; right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord h)))
  have hle : v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (t w))) ≤
      v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))) := by
    rw [map_mul, map_pow, map_pow, v.map_mul, v.map_pow, v.map_pow, hmono]
    change (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) + _ ≤
      (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)
    rw [hb, split a, ← hs]

    have hN : (((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM2
    have e : (((X₁.S.r * X₁.S.N) ^ 2 • (s : WithTop ℚ)) + (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ)) =
        (X₁.S.r * X₁.S.N) ^ 2 • ((s : WithTop ℚ) +
          (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) : WithTop ℚ)) := by
      rw [← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_eq_coe,
        nsmul_eq_mul, nsmul_eq_mul, mul_add, mul_div_cancel₀ _ hN]
    rw [e]
    exact nsmul_le_nsmul_right (add_le_add le_rfl hk) _
  obtain ⟨r', hr', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hne hle
  refine ⟨w, r', yyOf a q χ hq₁, ?_⟩
  rw [hr', _root_.mul_assoc]

end GlobalTheory.GSep.DvrScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSectionNormalisedUnitAtTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_theta_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁
  obtain ⟨θ₀, hθ₀⟩ := _root_.GlobalTheory.Mum.exists_sec_exp_intFam_one R hR D C F₁
  obtain ⟨r, t, hr, ht, h⟩ := _root_.GlobalTheory.Mum.ratio_odd_mul R hR D C m hm Φ hΦ F₁ θ₀ hθ₀
  have hr' : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom
    (algebraMap R (FractionRing R) t / algebraMap R (FractionRing R) r)) θ₀, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, v, ha, hb, hE, hv⟩ := h W T
  exact ⟨v, _root_.GlobalTheory.Mum.Rescale.rescale R hR D C F₁ θ₀ r t _ hr (div_mul_cancel₀ _ hr') W T a b v ha hb hE hv⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointsTransportedFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep

theorem exists_points_frames : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X)
    (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  refine ⟨x, fr, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩⟩
  have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
  rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
  exact e.symm

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTorsionLiftZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusExtension_torsion_lift_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℕ), 1 ≤ n → ∀ (c' : D.X → (𝟙_ (Over (Sp R)) ⟶ D.P.A)), (∀ χ, c' χ ^ n = D.c χ) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A), b ^ n = 1 → ∃ p : QkPt D F n, p.y = 0 ∧ p.g.b = b := by
  first | exact @GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq | exact GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq | (intros; apply GlobalTheory.TorsLiftRoot.exists_qk_zero_of_pow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftToSemiAbelianModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep.TraitLift

theorem exists_lift : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  intro X₁ z₁ Y πY h V _ _ _ _ ev _ hV
  obtain ⟨U₀, EE, -, -, -, hf, hp⟩ := h
  haveI := GlobalTheory.Poinc.Sep.TraitLift.surjective_of_isHom_id hf
  obtain ⟨V', _, _, _, j, ξ, h1, h2, h3, h4⟩ :=
    GlobalTheory.Poinc.Sep.TraitLift.exists_lift_of_proper πY V hV (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, j, ξ, h1, h2, h3, ?_⟩
  rw [h4, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.GSep.TraitLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupPointSameDerivationsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedGroup_point_sameDerivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → Function.Injective φ → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∃ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) ∧ (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) ∧ (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) ∧ GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') := by
  exact @GlobalTheory.FormalPointG.exists_point_sameDerivations
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsEqOfFiniteIndexStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_balancedIntBilinForms_eq_of_finite_index : ∀ {O : Type} [CommRing O] (bar : O → O) (X Y : Type) [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (f : Y →ₗ[O] X) (m : ℕ), 0 < m → Function.Injective f → (∀ x : X, m • x ∈ LinearMap.range f) → Module.finrank ℤ (GlobalTheory.BalRank.balBil bar Y) = Module.finrank ℤ (GlobalTheory.BalRank.balBil bar X) := by
  first | exact @GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex | exact GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex | (intros; apply GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex <;> assumption)
end

