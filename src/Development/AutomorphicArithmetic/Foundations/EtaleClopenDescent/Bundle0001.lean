module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.EtaleCohomology.WeilConjectures.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleMayerVietorisLongExact
section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.BiprodCls

namespace UpperTheory.Cb.EtaleMayerVietoris

variable {R : Type} [CommRing R]

private theorem cpull_lift_neg {N K L : Cx R} (a : N ⟶ K) (b : N ⟶ L) (I : Cx R) (n : ℤ)
    (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a (-b)) I n y =
      cpull a I n (cpull biprod.inl I n y) - cpull b I n (cpull biprod.inr I n y) := by
  have hl : biprod.lift a (-b) = a ≫ biprod.inl + (-b) ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp
  have h0 : ∀ {P Q : Cx R} (x : CohomologyClass Q I n), cpull (0 : P ⟶ Q) I n x = 0 := by
    intro P Q x
    have h := cpull_add (0 : P ⟶ Q) 0 I n x
    rw [add_zero] at h
    simpa using h
  have hn : ∀ {P Q : Cx R} (f : P ⟶ Q) (x : CohomologyClass Q I n),
      cpull (-f) I n x = -cpull f I n x := by
    intro P Q f x
    have h := cpull_add f (-f) I n x
    rw [add_neg_cancel, h0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [hl, cpull_add, ← cpull_cpull, ← cpull_cpull, hn, sub_eq_add_neg]

private theorem cpull_inl_desc {K L M : Cx R} (c : K ⟶ M) (e : L ⟶ M) (I : Cx R) (n : ℤ)
    (z : CohomologyClass M I n) :
    cpull biprod.inl I n (cpull (biprod.desc c e) I n z) = cpull c I n z := by
  rw [cpull_cpull, biprod.inl_desc]

private theorem cpull_inr_desc {K L M : Cx R} (c : K ⟶ M) (e : L ⟶ M) (I : Cx R) (n : ℤ)
    (z : CohomologyClass M I n) :
    cpull biprod.inr I n (cpull (biprod.desc c e) I n z) = cpull e I n z := by
  rw [cpull_cpull, biprod.inr_desc]

end UpperTheory.Cb.EtaleMayerVietoris

set_option maxHeartbeats 800000 in
open UpperTheory.Cb.EtaleMayerVietoris in
theorem UpperTheory.Cb.etale_mayer_vietoris_long_exact :
    LateralTheory.E.MayerVietorisSequence.LES := by
  intro R _ F
  obtain ⟨d0, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (_root_.GlobalTheory.EtC.ResBasic.res_basic R F).2.1
  refine ⟨fun a b c e w hS n => d0 _ hS n, ?_, ?_⟩
  · intro N K L M a b c e w hS n
    have hE := hex _ hS n
    obtain ⟨hinj, hsurj⟩ := cpull_biprod_bijective R K L (res R F) n
    have back : ∀ (z : CohomologyClass M (res R F) n) (u : CohomologyClass (K ⊞ L) (res R F) n),
        cpull biprod.inl (res R F) n u = cpull c (res R F) n z →
        cpull biprod.inr (res R F) n u = cpull e (res R F) n z →
        cpull (biprod.desc c e) (res R F) n z = u := by
      intro z u h1 h2
      refine hinj (Prod.ext ?_ ?_)
      · change cpull biprod.inl _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inl _ n u
        rw [cpull_inl_desc, h1]
      · change cpull biprod.inr _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inr _ n u
        rw [cpull_inr_desc, h2]
    refine ⟨fun x y => ?_, fun t => ?_, fun z => ?_⟩
    · obtain ⟨u, hu⟩ := hsurj (x, y)
      simp only [Prod.mk.injEq] at hu
      obtain ⟨hx, hy⟩ := hu
      have key : HK.pull R a F n x = HK.pull R b F n y ↔
          cpull (biprod.lift a (-b)) (res R F) n u = 0 := by
        rw [cpull_lift_neg, hx, hy, sub_eq_zero]
        rfl
      refine key.trans ((hE.1 u).trans ?_)
      constructor
      · rintro ⟨z, hz⟩
        have hz' : cpull (biprod.desc c e) (res R F) n z = u := hz
        refine ⟨z, ?_, ?_⟩
        · change cpull c (res R F) n z = x
          rw [← hx, ← hz', cpull_inl_desc]
        · change cpull e (res R F) n z = y
          rw [← hy, ← hz', cpull_inr_desc]
      · rintro ⟨z, hzx, hzy⟩
        exact ⟨z, back z u (hx.trans hzx.symm) (hy.trans hzy.symm)⟩
    · refine (hE.2.1 t).trans ?_
      constructor
      · rintro ⟨u, hu⟩
        have hu' : cpull (biprod.lift a (-b)) (res R F) n u = t := hu
        refine ⟨cpull biprod.inl (res R F) n u, cpull biprod.inr (res R F) n u, ?_⟩
        rw [← hu', cpull_lift_neg]
        rfl
      · rintro ⟨x, y, rfl⟩
        obtain ⟨u, hu⟩ := hsurj (x, y)
        simp only [Prod.mk.injEq] at hu
        obtain ⟨hx, hy⟩ := hu
        refine ⟨u, ?_⟩
        change cpull (biprod.lift a (-b)) (res R F) n u = _
        rw [cpull_lift_neg, hx, hy]
        rfl
    · obtain ⟨hinj1, -⟩ := cpull_biprod_bijective R K L (res R F) (n + 1)
      refine Iff.trans ?_ (hE.2.2 z)
      change _ ↔ cpull (biprod.desc c e) (res R F) (n + 1) z = 0
      constructor
      · rintro ⟨h1, h2⟩
        refine hinj1 (Prod.ext ?_ ?_)
        · change cpull biprod.inl _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inl _ _ 0
          rw [cpull_inl_desc, map_zero]
          exact h1
        · change cpull biprod.inr _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inr _ _ 0
          rw [cpull_inr_desc, map_zero]
          exact h2
      · intro h
        constructor
        · change cpull c (res R F) (n + 1) z = 0
          rw [← cpull_inl_desc c e, h, map_zero]
        · change cpull e (res R F) (n + 1) z = 0
          rw [← cpull_inr_desc c e, h, map_zero]
  · intro N K L M N' K' L' M' a b c e a' b' c' e' w w' hS hS' φN φK φL φM h1 h2 h3 h4 n t
    let φ : ShortComplex.mk (biprod.lift a (-b)) (biprod.desc c e) w ⟶
        ShortComplex.mk (biprod.lift a' (-b')) (biprod.desc c' e') w' :=
      { τ₁ := φN
        τ₂ := biprod.map φK φL
        τ₃ := φM
        comm₁₂ := by
          apply biprod.hom_ext <;> simp [h1, h2]
        comm₂₃ := by
          apply biprod.hom_ext' <;> simp [h3, h4] }
    exact hnat _ _ hS hS' φ n t
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleMayerVietorisShortExact
section
theorem UpperTheory.Cb.etale_mayer_vietoris_short_exact :
    LateralTheory.E.MayerVietorisSequence.SES := by
  intro R _ U V E f g h
  exact GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RestrictionInjectiveOfAcyclic
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb

open LateralTheory.EWeil.AcycPf

private lemma exact_filtered (R : Type) [CommRing R] (J : Type 1) [Category.{0} J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{1} (ULift.{1} R)) := by
  let e : J ≌ ULiftHom.{1} J := ULiftHom.equiv
  haveI : IsFiltered (ULiftHom.{1} J) := IsFiltered.of_equivalence e
  exact HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{1} (ULift.{1} R)) e.symm

private lemma mono_of_isColimit {J : Type 1} [Category.{0} J] {A : Type 2} [Category.{1} A] [Abelian A]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] {K L : J ⥤ A} (τ : K ⟶ L) [Mono τ]
    {c : Cocone K} {d : Cocone L} (hc : IsColimit c) (hd : IsColimit d) (m : c.pt ⟶ d.pt)
    (hm : ∀ j, c.ι.app j ≫ m = τ.app j ≫ d.ι.app j) : Mono m := by
  have key : m = (hc.coconePointUniqueUpToIso (colimit.isColimit K)).hom ≫ colimMap τ ≫
      (hd.coconePointUniqueUpToIso (colimit.isColimit L)).inv := by
    refine hc.hom_ext fun j => ?_
    simp [hm]
  have hτ : Mono (colim.map τ) := inferInstance
  have hτ' : Mono (colimMap τ) := hτ
  rw [key]
  infer_instance

private lemma lan_mono {C D : Type 1} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) [RepresentablyFlat G]
    {A : Type 2} [Category.{1} A] [Abelian A]
    [∀ X, HasColimitsOfShape (CostructuredArrow G.op X) A]
    (hA : ∀ (J : Type 1) [Category.{0} J] [IsFiltered J] [HasColimitsOfShape J A], HasExactColimitsOfShape J A)
    {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) [Mono φ] : Mono ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ) := by
  have hφ : ∀ c, Mono (φ.app c) := fun c => inferInstance
  have key : ∀ X, Mono (((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X) := by
    intro X
    haveI : IsFiltered (CostructuredArrow G.op X) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G (unop X))
    haveI := hA (CostructuredArrow G.op X)
    haveI : ∀ j, Mono ((Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ).app j) :=
      fun j => hφ _
    haveI : Mono (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ) :=
      NatTrans.mono_of_mono_app _
    refine mono_of_isColimit (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op P X)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op Q X) _ ?_
    intro j
    have h₂ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app (G.op.obj j.left) =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left :=
      (congr_app (G.op.lanUnit.naturality φ) j.left).symm
    have h₃ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj P).map j.hom ≫
        ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj Q).map j.hom := by
      rw [NatTrans.naturality, reassoc_of% h₂]
    first
      | exact (Category.assoc _ _ _).trans h₃
      | (dsimp only [Functor.LeftExtension.coconeAt_ι_app, Functor.whiskerLeft_app]
         simpa only [Category.assoc] using h₃)
  exact NatTrans.mono_of_mono_app _

set_option backward.isDefEq.respectTransparency false in
private lemma incl_flat (S : Scheme.{0}) : RepresentablyFlat (incl S) := by
  have : PreservesFiniteLimits (incl S) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget S))
  exact flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
private lemma incl_cont (S : Scheme.{0}) :
    (incl S).IsContinuous S.smallEtaleTopology (Scheme.etaleTopology.over S) := by
  have := incl_flat S
  haveI : (incl S).Full := inferInstanceAs (Scheme.Etale.forget S).Full
  haveI : (incl S).Faithful := inferInstanceAs (Scheme.Etale.forget S).Faithful
  haveI : (incl S).LocallyCoverDense (Scheme.etaleTopology.over S) :=
    Scheme.locallyCoverDense_of_le (P := @Etale) S le_rfl
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology (incl S) (Scheme.etaleTopology.over S)

private lemma restr_inj : RestrInj := by
  intro R _ S G _
  haveI := incl_cont S
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (incl S)
    (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology (Scheme.etaleTopology.over S)
  haveI : (Functor.sheafPullbackConstruction.sheafPullback (incl S) (ModuleCat.{1} (ULift.{1} R))
      S.smallEtaleTopology (Scheme.etaleTopology.over S)).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    haveI := incl_flat S
    haveI : Mono ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f) :=
      inferInstance
    haveI : Mono (((incl S).op.lan : _ ⥤ (Over S)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)).map
        ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f)) :=
      lan_mono (incl S) (fun J _ _ _ => exact_filtered R J) _
    exact (presheafToSheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))).map_mono _
  exact ⟨(((incl S).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology
    (Scheme.etaleTopology.over S)).obj G).property, adj.map_injective G inferInstance⟩

end UpperTheory.Cb

theorem UpperTheory.Cb.restrInj : LateralTheory.EWeil.AcycPf.RestrInj := UpperTheory.Cb.restr_inj
end
end

