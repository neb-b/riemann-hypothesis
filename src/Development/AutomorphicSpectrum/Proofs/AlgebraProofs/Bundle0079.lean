module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericTrivialNearSpecial
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero


open GlobalTheory.PrimSec in
theorem exists_open_pull_eq_zero {O K : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O]
    [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X}
    {fK : XK ⟶ Sp K} (H : IsPullback j fK f (spMap (algebraMap O K))) [Smooth f] [GeometricallyIntegral f]
    {x : X} (hfx : f x = IsLocalRing.closedPoint O) (l : Pic XK) :
    ∃ V : X.Opens, (∃ y ∈ V, f y = IsLocalRing.closedPoint O) ∧ pull (j ⁻¹ᵁ V).ι l = 0 := by
  haveI : IsIntegral XK := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  obtain ⟨V, hV, hxV, -, n, φ, hφ, hφ'⟩ := exists_etale_chart f (U := ⊤) (x := x) trivial
  have hp := isPrime_map f hV hxV hfx
  have hinj := app_injective H V
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hne : Nonempty (j ⁻¹ᵁ V) :=
    nonempty_of_ne_zero (a := 1) fun h => one_ne_zero (hinj ((map_one _).trans (h.trans (map_zero _).symm)))
  haveI : IsDomain Γ(X, V) := hinj.isDomain _
  obtain ⟨⟨p, hpV⟩⟩ := id hne
  obtain ⟨W, hpW, hW⟩ := exists_pull_eq_zero l p
  have hjV : IsAffineOpen (j ⁻¹ᵁ V) := by
    haveI : IsAffineHom j := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
    exact hV.preimage j
  obtain ⟨σ, hσW, hpσ⟩ := hjV.exists_basicOpen_le (V := W) ⟨p, hpW⟩ hpV
  obtain ⟨π, b, hπ, hb⟩ := exists_numerator H hV σ
  have hπ' : algebraMap O K π ≠ 0 := fun h => hπ (IsFractionRing.injective O K (h.trans (map_zero _).symm))
  have hc : ∀ c : K, c ≠ 0 → ∀ z ∈ j ⁻¹ᵁ V, z ∈ XK.basicOpen (AbLaw.cst fK (j ⁻¹ᵁ V) c) := fun c hc z hz =>
    (mem_basicOpen_cst fK _ c hz).2 fun h => hc (by
      haveI := (fK z).isPrime
      have e : (fK z).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      rw [e] at h
      exact h)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    have h0 : p ∈ XK.basicOpen (0 : Γ(XK, j ⁻¹ᵁ V)) := by
      rw [hb, Scheme.basicOpen_mul]
      exact ⟨hc _ hπ' p hpV, hpσ⟩
    rw [Scheme.basicOpen_zero] at h0
    exact h0
  letI := (AbLaw.cst f V).toAlgebra
  letI := φ.toAlgebra
  haveI : IsScalarTower O (MvPolynomial (Fin n) O) Γ(X, V) := .of_algebraMap_eq' hφ.symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) O) Γ(X, V) := hφ'
  obtain ⟨ρ, b', e, hb'⟩ := GlobalTheory.etale_mvPolynomial_exists_content O K n Γ(X, V) hp b hb0
  obtain ⟨y, hy⟩ := hV.isoSpec.hom.surjective
    (⟨(IsLocalRing.maximalIdeal O).map (AbLaw.cst f V), hp⟩ : PrimeSpectrum Γ(X, V))
  have hy' : (hV.primeIdealOf y).asIdeal = (IsLocalRing.maximalIdeal O).map (AbLaw.cst f V) :=
    congrArg PrimeSpectrum.asIdeal hy
  refine ⟨X.basicOpen b', ⟨y.1, (mem_basicOpen_iff hV y b').2 (hy' ▸ hb'), ?_⟩,
    pull_eq_zero_of_mem W _ (fun z => ?_) hW⟩
  · refine PrimeSpectrum.ext (((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (f y.1).isPrime.ne_top
      fun a ha => ?_).symm)
    by_contra h
    exact (mem_basicOpen_iff hV y _).1 ((mem_basicOpen_cst f V a y.2).2 h) (hy' ▸ Ideal.mem_map_of_mem _ ha)
  · have hz : j z.1 ∈ X.basicOpen b' := z.2
    have hzV : z.1 ∈ j ⁻¹ᵁ V := X.basicOpen_le b' hz
    have hz' : z.1 ∈ XK.basicOpen ((j.app V).hom b') := by
      rw [← Scheme.preimage_basicOpen]
      exact hz
    have hρ : algebraMap O K ρ ≠ 0 := fun h => hb0 (by
      rw [e, IsFractionRing.injective O K (h.trans (map_zero _).symm), map_zero, zero_mul])
    have e' : (j.app V).hom b = AbLaw.cst fK (j ⁻¹ᵁ V) (algebraMap O K ρ) * (j.app V).hom b' := by
      rw [e, map_mul]
      change (j.app V).hom (AbLaw.cst f V ρ) * _ = _
      rw [app_cst H.w]
    have h1 : z.1 ∈ XK.basicOpen ((j.app V).hom b) := by
      rw [e', Scheme.basicOpen_mul]
      exact ⟨hc _ hρ _ hzV, hz'⟩
    rw [hb, Scheme.basicOpen_mul] at h1
    exact hσW h1.2

theorem near_zero : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ l : Pic (pullback A.hom (spMap (algebraMap R C))),
      ∃ V : A.left.Opens, (∃ y ∈ V, A.hom y = IsLocalRing.closedPoint R) ∧
        pull (pullback.fst A.hom (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA l
  have := hA.smooth
  have := hA.geomConnected
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ A
  obtain ⟨x, hx⟩ := A.hom.surjective (IsLocalRing.closedPoint R)
  exact exists_open_pull_eq_zero (IsPullback.of_hasPullback A.hom (spMap (algebraMap R C))) hx l

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardMayerVietorisExtend
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.CechMV

theorem exists_extend_of_pull_inf_eq_zero (X : Scheme.{0}) (W V : X.Opens) (p : Pic W.toScheme)
    (hp : pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0) :
    ∃ q : Pic (W ⊔ V).toScheme, pull (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) q = p := by
  obtain ⟨N, hN, rfl⟩ := cls_surj p
  have sq : IsPullback (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) (X.homOfLE (inf_le_right : W ⊓ V ≤ V))
      (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) (X.homOfLE (le_sup_right : V ≤ W ⊔ V)) :=
    isPullback_opens_inf_le le_sup_left le_sup_right
  have hcov : Set.range (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) ∪
      Set.range (X.homOfLE (le_sup_right : V ≤ W ⊔ V)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rcases x.2 with h | h
    · refine Or.inl ⟨⟨x.1, h⟩, ?_⟩
      exact Subtype.ext (by simp [Scheme.homOfLE_apply])
    · refine Or.inr ⟨⟨x.1, h⟩, ?_⟩
      exact Subtype.ext (by simp [Scheme.homOfLE_apply])
  have hT := LB.isLB_triv V.toScheme
  have iso : LBIso (N.pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)))
      ((LB.triv V.toScheme).pull (X.homOfLE (inf_le_right : W ⊓ V ≤ V))) := by
    refine (cls_eq_iff (pull_isLB hN _) (pull_isLB hT _)).1 ?_
    rw [cls_pull hN _ (pull_isLB hN _), cls_pull hT _ (pull_isLB hT _), hp]
    exact (map_zero (pull (X.homOfLE (inf_le_right : W ⊓ V ≤ V)))).symm
  obtain ⟨L, hL, e, -⟩ := GlobalTheory.GlueTwoLB.glue _ _ _ _ _ _ _ _ N (LB.triv V.toScheme) inferInstance inferInstance
    sq hcov hN hT iso
  exact ⟨cls L hL, ((cls_eq_iff hN (pull_isLB hL _)).2 e).symm⟩

end GlobalTheory.CompanionTheory.CechMV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfSamePolarization
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AmpleForm

theorem relAmple_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (M L : LB B.left) (hM : M.IsLB) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L →
    lam (cls M hM) (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) → Out.RelAmple B M := by
  intro K _ _ B _ hB M L hM hL ha hk hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls M hM - cls L hL)
  have hlam0 : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L hL hk O hO hlam0
  have hN : (RigidTranslate.rigTransl L x).IsLB := DVR.linComb_isLB _ hL _ _
  have hA := RigidTranslate.relAmple_rigTransl_point K B hB L hL x ha
  have e1 := PrimitiveOverField.lam_const (cls L hL) x (𝟙 B)
  have e2 : ((toUnit B ≫ x) * 𝟙 B) = PolTranslate.transl x := by
    rw [PolTranslate.transl, _root_.mul_comm]
  have e3 : CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, CechPic.pull_comp, ThetaExtend.pic_local (CechPic.pull x.left (cls L hL)), map_zero]
  have e : cls M hM = cls _ hN := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, e3, neg_zero, add_zero]
    rw [e2, Over.id_left, CechPic.pull_id] at e1
    exact sub_left_inj.1 (eO.symm.trans (hx.trans e1))
  have hN' := pull_isLB hN (𝟙 _)
  have e' : cls M hM = cls _ hN' := by
    rw [CechPic.cls_pull hN, CechPic.pull_id]; exact e
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hM hN').1 e'
  exact relAmple_pull (A' := B) (A := B) (φ := 𝟙 _) (f := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) hN hM ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hA

end GlobalTheory.CompanionTheory.AmpleForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SectionThroughClosedPoint
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Sections

theorem exists_section_fibre {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom)
    (y : ↥(pullback X.hom (spMap (IsLocalRing.residue R)))) (hy : IsClosed {y}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) =
      pullback.fst X.hom (spMap (IsLocalRing.residue R)) y := by
  let x₀ := pointOfClosedPoint (pullback.snd X.hom (spMap (IsLocalRing.residue R))) y hy
  obtain ⟨⟨s, hs⟩, e⟩ := GlobalTheory.reducePoint_residue_surjective X.hom R (𝟙 _)
    ⟨x₀ ≫ pullback.fst _ _, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  have e' : spMap (IsLocalRing.residue R) ≫ s = x₀ ≫ pullback.fst _ _ := congrArg Subtype.val e
  refine ⟨Over.homMk s hs, ?_⟩
  have e2 : s (PrimeSpectrum.comap (IsLocalRing.residue R) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
      pullback.fst X.hom (spMap (IsLocalRing.residue R)) (x₀ (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    congr($e' (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)))
  rw [IsLocalRing.comap_closedPoint] at e2
  exact e2.trans (congrArg _ (pointOfClosedPoint_apply _ y hy _))

theorem exists_section_closed {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom) {z : X.left}
    (hz : X.hom z = IsLocalRing.closedPoint R) (hc : IsClosed {z}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z := by
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    .spec_of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst X.hom (spMap (IsLocalRing.residue R))) := by
    rw [GlobalTheory.range_fst_residue]; exact hz
  refine exists_section_fibre X hX y ?_
  have := hc.preimage (pullback.fst X.hom (spMap (IsLocalRing.residue R))).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _
    (pullback.fst X.hom (spMap (IsLocalRing.residue R))).isClosedEmbedding.injective] at this

theorem exists_section_open {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom)
    {U : Set X.left} (hU : IsOpen U) {z : X.left} (hzU : z ∈ U)
    (hz : X.hom z = IsLocalRing.closedPoint R) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U := by
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    .spec_of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst X.hom (spMap (IsLocalRing.residue R))) := by
    rw [GlobalTheory.range_fst_residue]; exact hz
  have : JacobsonSpace ↥(pullback X.hom (spMap (IsLocalRing.residue R))) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd X.hom (spMap (IsLocalRing.residue R)))
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints
    (Z := pullback.fst X.hom (spMap (IsLocalRing.residue R)) ⁻¹' U) ⟨y, hzU⟩
    (hU.preimage (pullback.fst X.hom (spMap (IsLocalRing.residue R))).continuous).isLocallyClosed
  obtain ⟨s, hs⟩ := exists_section_fibre X hX c hc'
  exact ⟨s, hs ▸ hc⟩

theorem exists_section :
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)), Smooth X.hom →
    (∀ z : X.left, IsClosed {z} → X.hom z = IsLocalRing.closedPoint R →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z) ∧
    (∀ U : X.left.Opens, (∃ z ∈ U, X.hom z = IsLocalRing.closedPoint R) →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U) := by
  intro R _ _ _ X hX
  refine ⟨fun z hc hz => exists_section_closed X hX hz hc, ?_⟩
  rintro U ⟨z, hzU, hz⟩
  exact exists_section_open X hX U.isOpen hzU hz

end GlobalTheory.CompanionTheory.Sections
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationIntegersRankOne
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin

theorem integers_valuationRing_dimensionLEOne_isFractionRing :
    ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    ∃ (_ : IsDomain R), ValuationRing R ∧ Ring.DimensionLEOne R ∧ IsFractionRing R C := by
  intro C _ _ v R _ _ hv
  haveI hdom : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI hval : ValuationRing R := ValuationRing.of_integers v hv
  refine ⟨hdom, hval, ⟨?_⟩, ?_⟩
  · intro p hp0 hp
    have hle : IsLocalRing.maximalIdeal R ≤ p := by
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact p.zero_mem
      obtain ⟨y, hyp, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
      have hxu : ¬ IsUnit x := by
        simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
      have hvx : v (algebraMap R C x) < 1 :=
        lt_of_le_of_ne (hv.map_le_one x) fun e => hxu (hv.isUnit_iff_valuation_eq_one.2 e)
      have hvy : 0 < v (algebraMap R C y) := by
        rw [zero_lt_iff, Valuation.ne_zero_iff]
        exact fun e => hy0 (hv.hom_inj (by rw [e, map_zero]))
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hvy hvx
      have hdvd : y ∣ x ^ n := by
        rw [hv.dvd_iff_le, map_pow, map_pow]
        exact hn.le
      exact hp.mem_of_pow_mem n (p.mem_of_dvd hdvd hyp)
    have heq : p = IsLocalRing.maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal hp.ne_top) hle
    rw [heq]
    exact IsLocalRing.maximalIdeal.isMaximal R
  · haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hv.hom_inj
    refine IsFractionRing.of_field R C fun z => ?_
    by_cases hz0 : z = 0
    · exact ⟨0, 1, by simp [hz0]⟩
    rcases le_total (v z) 1 with h | h
    · obtain ⟨a, ha⟩ := hv.exists_of_le_one h
      exact ⟨a, 1, by simp [ha]⟩
    · have h' : v z⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ h
      obtain ⟨a, ha⟩ := hv.exists_of_le_one h'
      exact ⟨1, a, by simp [ha]⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin
end

