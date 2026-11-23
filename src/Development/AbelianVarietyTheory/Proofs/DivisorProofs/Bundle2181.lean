module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermDvdOfSectionExpansionDvdClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ClosedFibreDvd

theorem mem_span_of_forall_pow {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] (a s : O)
    (h : ∀ n : ℕ, s ∈ Ideal.span {a} ⊔ maximalIdeal O ^ (n + 1)) : s ∈ Ideal.span {a} := by
  by_cases ht : Ideal.span {a} = ⊤
  · rw [ht]; trivial
  haveI : Nontrivial (O ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.2 ht
  haveI : IsLocalRing (O ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk (Ideal.span {a})) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (maximalIdeal (O ⧸ Ideal.span {a})) (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
  intro n
  have hle : Ideal.map (Ideal.Quotient.mk (Ideal.span {a})) (Ideal.span {a} ⊔ maximalIdeal O ^ (n + 1)) ≤
      maximalIdeal (O ⧸ Ideal.span {a}) ^ n := by
    rw [Ideal.map_sup, Ideal.map_pow]
    refine sup_le ?_ ?_
    · rw [Ideal.map_quotient_self]; exact bot_le
    · refine le_trans ?_ (Ideal.pow_le_pow_right (Nat.le_succ n))
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit _ r hr) _
  exact hle (Ideal.mem_map_of_mem _ (h n))

theorem ker_stalkMap_le {X H : Scheme.{0}} (j : H ⟶ X) [IsClosedImmersion j] (z : H)
    (I : Ideal (X.presheaf.stalk (j z))) (hI : I ≠ ⊤)
    (ℓ : Spec (CommRingCat.of (X.presheaf.stalk (j z) ⧸ I)) ⟶ H)
    (hℓ : ℓ ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk (j z)) :
    RingHom.ker (j.stalkMap z).hom ≤ I := by
  intro a ha
  haveI : Nontrivial (X.presheaf.stalk (j z) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : IsLocalRing (X.presheaf.stalk (j z) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have e : ℓ (IsLocalRing.closedPoint _) = z := by
    apply j.isEmbedding.injective
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_
    exact (congrArg (X.fromSpecStalk (j z)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint
  let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ
  have hψ : j.stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (j z)), ← hℓ, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
  have hψ' := congrArg (fun q => q.hom a) hψ
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'
  rw [RingHom.mem_ker.1 ha, map_zero] at hψ'
  exact Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm

def cstHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) : R →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p x) trivial ≫ p.stalkMap x).hom

theorem cstHom_apply {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) (c : R) :
    cstHom p x c = cst p x c := by
  rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl

theorem fromSpecStalk_comp {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) :
    X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom (cstHom p x)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp]; rfl

theorem exists_lift {R : Type} [CommRing R] (J : Ideal R) {X Y P : Scheme.{0}} (π : Y ⟶ Sp R) (p : X ⟶ Sp R)
    (fs : P ⟶ Y) (sn : P ⟶ Spec (CommRingCat.of (R ⧸ J)))
    (hP : IsPullback fs sn π (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (k : Y ⟶ X) (h : X ⟶ Y) (hh : h ≫ π = p) (hk : h ≫ k = 𝟙 X) (z : P)
    (I : Ideal (X.presheaf.stalk ((fs ≫ k) z))) (hJ : Ideal.map (cstHom p _) J ≤ I) :
    ∃ ℓ : Spec (CommRingCat.of (X.presheaf.stalk ((fs ≫ k) z) ⧸ I)) ⟶ P,
      ℓ ≫ (fs ≫ k) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk _ := by
  let L : R ⧸ J →+* X.presheaf.stalk ((fs ≫ k) z) ⧸ I := Ideal.Quotient.lift J ((Ideal.Quotient.mk I).comp (cstHom p _))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hJ (Ideal.mem_map_of_mem _ ha)))
  have w : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk _) ≫ h) ≫ π =
      Spec.map (CommRingCat.ofHom L) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [Category.assoc, Category.assoc, hh, fromSpecStalk_comp, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  refine ⟨hP.lift _ _ w, ?_⟩
  rw [← Category.assoc, hP.lift_fst, Category.assoc, hk, Category.comp_id]

theorem cst_stalkMap' {V : Type} [CommRing V] {X Z : Scheme.{0}} (r : Z ⟶ X) (p : X ⟶ Sp V) (z : Z) (a : V) :
    (r.stalkMap z).hom (cst p (r z) a) = cst (r ≫ p) z a := by
  have e := gs_pull (𝟙 X) p (r z) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  rw [Category.id_comp] at e
  exact (congrArg (r.stalkMap z).hom e.symm).trans ((gs_stalkMap r z (p ⁻¹ᵁ ⊤) trivial _).symm.trans
    (gs_pull r p z ⊤ trivial _))

theorem germ_dvd_of_expT_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∀ (x : (𝟙_ (Over (Sp R)) ⊗ G).left), (𝟙_ (Over (Sp R)) ⊗ G).hom x = closedPoint R → ∀ (j : Fin 1 → U.P.L.L.ι), x ∈ LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j → ∃ t, gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) = cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q * t := by
  intro R _ _ _ hR D A G _ _ U σ f g q hE hM x hx j hxj
  haveI : IsNoetherianRing R := hR.1.1
  haveI : Smooth G.hom := U.semi.smooth
  have lam : (snd (𝟙_ (Over (Sp R))) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ (Over (Sp R))) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  have lamA' : (λ_ D.P.A).inv.left ≫ (snd (𝟙_ (Over (Sp R))) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  have toU : ∀ {Y : Over (Sp R)} (h : Y ⟶ 𝟙_ (Over (Sp R))), h.left = Y.hom := fun h => by simpa using Over.w h
  have hpG : (snd (𝟙_ (Over (Sp R))) G).left ≫ G.hom = (𝟙_ (Over (Sp R)) ⊗ G).hom := Over.w _
  haveI : IsIso (snd (𝟙_ (Over (Sp R))) G).left := ⟨⟨(λ_ G).inv.left, lam, lam'⟩⟩
  haveI : LocallyOfFiniteType (𝟙_ (Over (Sp R)) ⊗ G).hom := by rw [← hpG]; infer_instance
  haveI : IsLocallyNoetherian (𝟙_ (Over (Sp R)) ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (𝟙_ (Over (Sp R)) ⊗ G).hom
  suffices H : gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) ∈
      Ideal.span {cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q} by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 H
    exact ⟨t, by rw [← ht, mul_comm]⟩
  refine mem_span_of_forall_pow _ _ fun e => ?_
  have hxg : G.hom ((snd (𝟙_ (Over (Sp R))) G).left x) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, hpG]; exact hx
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hw : thick R (maximalIdeal R) e (closedPoint _) = closedPoint R := by
    have := IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))
    exact this
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R (maximalIdeal R) e) _ _
    (hxg.trans hw.symm)
  have hzx : (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z = x := by
    rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, lam]; rfl
  subst hzx

  have hc : IsClosedImmersion (thick R (maximalIdeal R) e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

  haveI : IsIso (λ_ G).inv.left := ⟨⟨(snd (𝟙_ (Over (Sp R))) G).left, lam', lam⟩⟩
  haveI : IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e)) := inferInstance
  haveI : IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) := inferInstance

  have hmap : Ideal.map (cstHom (𝟙_ (Over (Sp R)) ⊗ G).hom
      ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)) (maximalIdeal R ^ (e + 1)) ≤
      maximalIdeal _ ^ (e + 1) := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_) _
    rw [Ideal.mem_comap, cstHom_apply]
    exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (cst_not_isUnit _ _ hx hc'))
  have hker : RingHom.ker ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap z).hom ≤
      maximalIdeal _ ^ (e + 1) := by
    have hI : Ideal.map (cstHom (𝟙_ (Over (Sp R)) ⊗ G).hom
        ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)) (maximalIdeal R ^ (e + 1)) ≠ ⊤ :=
      ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (hmap.trans (Ideal.pow_le_self (Nat.succ_ne_zero e)))
    obtain ⟨ℓ, hℓ⟩ := exists_lift (maximalIdeal R ^ (e + 1)) G.hom (𝟙_ (Over (Sp R)) ⊗ G).hom
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) (λ_ G).inv.left
      (snd (𝟙_ (Over (Sp R))) G).left hpG lam z _ le_rfl
    exact (ker_stalkMap_le _ z _ hI ℓ hℓ).trans hmap

  obtain ⟨S, hS⟩ := hE e
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt U.P.L.isLB z
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  have h3 : ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (fst (𝟙_ (Over (Sp R))) D.P.A).left =
      (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫ (fst (𝟙_ (Over (Sp R))) G).left := by
    rw [toU, toU, Category.assoc, Category.assoc, Over.w (λ_ D.P.A).inv, Over.w (λ_ G).inv, Over.w (U.gt e).pG,
      pullback.condition]
    rfl
  have key := (hS _ (𝟙 _) (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left)
    ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left)
    (by rw [Category.assoc, lam', Category.comp_id, Category.id_comp]; rfl)
    (by rw [Category.assoc, lamA', Category.comp_id, Category.id_comp]) h3 z JG J hJG hJ).2

  have aux : ∀ {O : Type} [CommRing O] (u : Oˣ) (a b : O) (I : Ideal O), (u : O) ^ 1 * a = b → b ∈ I → a ∈ I :=
    fun u a b I h hb => by
      rw [pow_one] at h
      rw [← u.inv_mul_cancel_left a, h]
      exact I.mul_mem_left _ hb
  have hq : ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [Category.assoc, Category.assoc, Over.w (λ_ D.P.A).inv, Over.w (λ_ G).inv, Over.w (U.gt e).pG,
      pullback.condition]
    rfl
  have hmem : sval σ (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z JG ∈
      Ideal.span {cst ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫
        (𝟙_ (Over (Sp R)) ⊗ G).hom) z q} := by
    refine aux _ _ _ _ key (Ideal.sum_mem _ fun α _ => ?_)
    have hF : sval (f α) ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) z J =
        cst (((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom) z q *
          sval (g α) ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) z J :=
      secIsMul_gs (hM α) _ z _ (hJ.mem _ _)
    rw [hF, hq, _root_.mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hπ : ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap z).hom
      (gs (𝟙 _) ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)
        (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j)) ∈
      Ideal.span {cst ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫
        (𝟙_ (Over (Sp R)) ⊗ G).hom) z q} := by
    have e1 := gs_stalkMap (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z _ hxj (σ.f j)
    erw [← e1, sec_trans σ _ z hxj (hJG.mem _ _)]
    exact Ideal.mul_mem_left _ _ hmem
  obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨t, rfl⟩ := (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap_surjective z t'
  refine Submodule.mem_sup.2 ⟨t * cst (𝟙_ (Over (Sp R)) ⊗ G).hom
    ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z) q,
    Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), _, hker ?_, add_sub_cancel _ _⟩
  rw [RingHom.mem_ker, map_sub, map_mul, cst_stalkMap', ht', sub_self]

end GlobalTheory.ClosedFibreDvd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictions
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverForms

open KaehlerDifferential

theorem exists_pow_smul_eq_zero {R C B : Type} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (g : C →ₐ[R] B) (f : C)
    (hloc : @IsLocalization.Away C _ f B _ g.toRingHom.toAlgebra)
    (L : Ω[C⁄R] →ₗ[R] Ω[B⁄R]) (hD : ∀ c, L (D R C c) = D R B (g c))
    (hs : ∀ (c : C) (α : Ω[C⁄R]), L (c • α) = g c • L α)
    (α : Ω[C⁄R]) (h : L α = 0) : ∃ m : ℕ, f ^ m • α = 0 := by
  letI : Algebra C B := g.toRingHom.toAlgebra
  haveI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  have hL : ∀ β, L β = KaehlerDifferential.map R R C B β := by
    intro β
    have hβ : β ∈ Submodule.span C (Set.range (D R C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hβ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      rw [hD, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [hs, hx, (KaehlerDifferential.map R R C B).map_smul]
      exact algebraMap_smul B c _
  haveI := KaehlerDifferential.isLocalizedModule_map R C B (Submonoid.powers f)
  have h' : KaehlerDifferential.map R R C B α = KaehlerDifferential.map R R C B 0 := by
    rw [← hL, h, map_zero]
  obtain ⟨⟨c, hc⟩, hc0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'
  obtain ⟨m, rfl⟩ := hc
  refine ⟨m, ?_⟩
  simpa [Submonoid.smul_def] using hc0

theorem eq_zero_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  intro R _ X s hX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.card, fun k => Opposite.op (t.equivFin.symm k).1, fun w hw => ?_⟩
  have hcov : ∀ x : X, ∃ U ∈ t, x ∈ (U.1 : Set X) := fun x => by
    simpa using ht (Set.mem_univ x)
  have hV0 : ∀ U ∈ t, w.1 (Opposite.op U) = 0 := fun U hU => by
    have : evForm s (Opposite.op (t.equivFin.symm (t.equivFin ⟨U, hU⟩)).1) w = 0 := hw _
    have e : t.equivFin.symm (t.equivFin ⟨U, hU⟩) = ⟨U, hU⟩ := Equiv.symm_apply_apply _ _
    rw [e] at this
    exact this
  apply Subtype.ext
  funext W
  obtain ⟨W₀⟩ := W
  have hW : IsAffineOpen W₀.1 := W₀.2
  let S : Set Γ(X, W₀.1) := {f | ∃ U ∈ t, X.basicOpen f ≤ U.1}
  have hS : Ideal.span S = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) ?_
    intro x hx
    obtain ⟨U, hU, hxU⟩ := hcov x
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := U.1) ⟨x, hxU⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, U, hU, hf⟩, hxf⟩
  let α : Ω[Sec s W₀.1⁄R] := w.1 (Opposite.op W₀)
  let I : Ideal (Sec s W₀.1) := LinearMap.ker (LinearMap.toSpanSingleton (Sec s W₀.1) _ α)
  have hrad : ∀ f ∈ S, f ∈ I.radical := by
    rintro f ⟨U, hU, hf⟩
    let D' : X.affineOpens := ⟨X.basicOpen f, hW.basicOpen f⟩
    let φ : (Opposite.op W₀ : AffOp X) ⟶ Opposite.op D' := (homOfLE (X.basicOpen_le f)).op
    let ψ : (Opposite.op U : AffOp X) ⟶ Opposite.op D' := (homOfLE hf).op
    have h0 : p1 (OAff s) φ α = 0 := by
      have e1 := w.2 φ
      have e2 := w.2 ψ
      rw [hV0 U hU, map_zero] at e2
      exact e1.symm.trans e2
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero (mp (OAff s) φ) f
      (hW.isLocalization_basicOpen f) (p1 (OAff s) φ) (p1_D (OAff s) φ) (oneFormsMapOfFunctorMorphism_smul (OAff s) φ) α h0
    exact ⟨m, by simpa [I] using hm⟩
  have hI : I = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff]
    have h2 := Ideal.span_le.2 hrad
    exact (show (⊤ : Ideal (Sec s W₀.1)) ≤ Ideal.span S from hS.ge).trans h2
  have h1 : (1 : Sec s W₀.1) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end GlobalTheory.CoverForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCoo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm.RigidW

theorem triple_ext {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g h : Z ⟶ Triple f)
    (h1 : g ≫ pullback.fst _ _ ≫ pullback.fst f f = h ≫ pullback.fst _ _ ≫ pullback.fst f f)
    (h2 : g ≫ pullback.fst _ _ ≫ pullback.snd f f = h ≫ pullback.fst _ _ ≫ pullback.snd f f)
    (h3 : g ≫ pullback.snd _ _ ≫ pullback.snd f f = h ≫ pullback.snd _ _ ≫ pullback.snd f f) : g = h := by
  have c := pullback.condition (f := pullback.snd f f) (g := pullback.fst f f)
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · simpa only [Category.assoc] using h2
  · apply pullback.hom_ext
    · simp only [Category.assoc, ← c]
      simpa only [Category.assoc] using h2
    · simpa only [Category.assoc] using h3

theorem appTop_comp {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

theorem snd_hom : pullback.snd (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom := by
  rw [← Over.w (q ▷ B), pullback.condition_assoc]


variable (B) in
def W0 : Over (Sp K) :=
  Over.mk (pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom : Triple (q ▷ B).left ⟶ Sp K)

def p1 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.fst _ _) (by simp [W0])

def p2 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom])

def p3 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.snd _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom, ← pullback.condition_assoc, snd_hom])

theorem rigidityTripleFibreProductFirstCoord_left : (p1 q).left = pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductSecondCoord_left : (p2 q).left = pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductThirdCoord_left : (p3 q).left = pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl

theorem p12 : p1 q ≫ q ▷ B = p2 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductFirstCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem p23 : p2 q ≫ q ▷ B = p3 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductThirdCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (congrArg (· ≫ _) pullback.condition).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm))

end
end GlobalTheory.DescNorm.RigidW

namespace GlobalTheory.DescNorm.RigidW
section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

def beta : W0 B q ⟶ B := p1 q ≫ snd A B

theorem rigidityTripleSecondCoord_snd_eq_groupCoord : p2 q ≫ snd A B = beta q := by
  rw [beta, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p12]

theorem rigidityTripleThirdCoord_snd_eq_groupCoord : p3 q ≫ snd A B = beta q := by
  rw [← rigidityTripleSecondCoord_snd_eq_groupCoord, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p23]

def E (u : W0 B q ⟶ A ⊗ B) : B ⊗ W0 B q ⟶ A ⊗ B := lift (snd B (W0 B q) ≫ u ≫ fst A B) (fst B (W0 B q))

theorem E_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) : E q u ≫ q ▷ B = E q v ≫ q ▷ B := by
  have h' : u ≫ fst A B ≫ q = v ≫ fst A B ≫ q := by
    have := congrArg (· ≫ fst A' B) h
    simpa using this
  apply CartesianMonoidalCategory.hom_ext
  · simp [E, h']
  · simp [E]

theorem E_left_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) :
    (E q u).left ≫ (q ▷ B).left = (E q v).left ≫ (q ▷ B).left := by
  rw [← Over.comp_left, ← Over.comp_left, E_eq q h]

theorem lift_E (x : W0 B q ⟶ B) (u : W0 B q ⟶ A ⊗ B) : lift x (𝟙 _) ≫ E q u = lift (u ≫ fst A B) x := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [E]

def eL : (B ⊗ W0 B q).left ⟶ Triple (q ▷ B).left :=
  pullback.lift (pullback.lift (E q (p1 q)).left (E q (p2 q)).left (E_left_eq q (p12 q)))
    (pullback.lift (E q (p2 q)).left (E q (p3 q)).left (E_left_eq q (p23 q)))
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)

theorem eL_1 : eL q ≫ pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left = (E q (p1 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
theorem eL_2 : eL q ≫ pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p2 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
theorem eL_3 : eL q ≫ pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p3 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_snd, pullback.lift_snd]

theorem sec_beta : (lift (beta q) (𝟙 (W0 B q))).left ≫ eL q = 𝟙 _ := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p1 q ≫ fst A B) (beta q) = p1 q)).trans
      ((rigidityTripleFibreProductFirstCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [beta]
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p2 q ≫ fst A B) (beta q) = p2 q)).trans
      ((rigidityTripleFibreProductSecondCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleSecondCoord_snd_eq_groupCoord]
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p3 q ≫ fst A B) (beta q) = p3 q)).trans
      ((rigidityTripleFibreProductThirdCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleThirdCoord_snd_eq_groupCoord]

theorem lift_one (u : W0 B q ⟶ A ⊗ B) : lift (u ≫ fst A B) (1 : W0 B q ⟶ B) = u ≫ zb A B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [zb]
  · simp [zb, MonObj.comp_one]

theorem sec_one : (lift (1 : W0 B q ⟶ B) (𝟙 (W0 B q))).left ≫ eL q = rhoW q := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductFirstCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_fst q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductSecondCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductThirdCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_snd_assoc q _).symm

theorem rhoW_appTop (hB : IsAbelianScheme B) (D : Γ(Triple (q ▷ B).left, ⊤)) : (rhoW q).appTop.hom D = D := by
  have hs : Function.Surjective ((snd B (W0 B q)).left.appTop).hom :=
    surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback (W0 B q).hom B hB) ⊤
  obtain ⟨F, hF⟩ := hs ((eL q).appTop.hom D)
  have hsnd : ∀ x : W0 B q ⟶ B, (lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have key : ∀ x : W0 B q ⟶ B, ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D = F := by
    intro x
    calc ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D
        = (lift x (𝟙 (W0 B q))).left.appTop.hom ((eL q).appTop.hom D) := appTop_comp _ _ _
      _ = (lift x (𝟙 (W0 B q))).left.appTop.hom ((snd B (W0 B q)).left.appTop.hom F) := by rw [hF]
      _ = ((lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left).appTop.hom F := (appTop_comp _ _ _).symm
      _ = F := by rw [hsnd x, Scheme.Hom.id_appTop]; rfl
  have h1 : D = F := by
    have h := key (beta q)
    rw [sec_beta] at h
    exact h
  have h0 := key 1
  rw [sec_one] at h0
  exact h0.trans h1.symm

end

theorem gm_rhoW_eq_gm_id_of_abelian : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj B] (q : A ⟶ A'), IsAbelianScheme B →
    ∀ (D : Γ(Triple (q ▷ B).left, ⊤)ˣ) (w : Triple (q ▷ B).left), gm (rhoW q) w ⊤ D = gm (𝟙 _) w ⊤ D := by
  intro K _ A A' B _ q hB D w
  have := gm_comp_top (𝟙 _) (rhoW q) w D D (rhoW_appTop q hB D.val)
  rwa [Category.id_comp] at this

end GlobalTheory.DescNorm.RigidW
end
end

