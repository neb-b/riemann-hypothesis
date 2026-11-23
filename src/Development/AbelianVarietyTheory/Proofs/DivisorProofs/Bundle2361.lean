module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueUnitsGlueArtinFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.PinchUnits

open ReciprocityTheory.ChartRestriction.G.Out.TLinPf

theorem pushout_sec_exists {X₀ X₁ X₂ X : Scheme.{0}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (H : IsPushout i₁ i₂ j₁ j₂) (s₁ : Γ(X₁, ⊤)) (s₂ : Γ(X₂, ⊤))
    (h : i₁.appTop.hom s₁ = i₂.appTop.hom s₂) :
    ∃ s : Γ(X, ⊤), j₁.appTop.hom s = s₁ ∧ j₂.appTop.hom s = s₂ := by
  have w : i₁ ≫ mOf s₁ = i₂ ≫ mOf s₂ := by rw [comp_mOf, comp_mOf, h]
  refine ⟨fnOf (H.desc (mOf s₁) (mOf s₂) w), ?_, ?_⟩
  · rw [← fnOf_comp, H.inl_desc, fnOf_mOf]
  · rw [← fnOf_comp, H.inr_desc, fnOf_mOf]

theorem pushout_sec_ext {X₀ X₁ X₂ X : Scheme.{0}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (H : IsPushout i₁ i₂ j₁ j₂) (s s' : Γ(X, ⊤))
    (h₁ : j₁.appTop.hom s = j₁.appTop.hom s') (h₂ : j₂.appTop.hom s = j₂.appTop.hom s') : s = s' := by
  apply mOf_inj
  apply H.hom_ext
  · rw [comp_mOf, comp_mOf, h₁]
  · rw [comp_mOf, comp_mOf, h₂]

theorem resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]

theorem isPullback_resLE_self {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) (f ⁻¹ᵁ U).ι U.ι f := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact isPullback_morphismRestrict f U

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → (∀ (U : Y.left.Opens) (a₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ), (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) a₁ = gm i₂ x (j₂ ⁻¹ᵁ U) a₂) → ∃ d : Γ(Y.left, U)ˣ, pullU j₁ U d = a₁ ∧ pullU j₂ U d = a₂) ∧ (∀ (U : Y.left.Opens) (d d' : Γ(Y.left, U)ˣ), pullU j₁ U d = pullU j₁ U d' → pullU j₂ U d = pullU j₂ U d' → d = d') := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hfl h₁ h₂ h₀ hc hc₂
  have hle : ∀ U : Y.left.Opens, i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U) ≤ i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ U) := by
    intro U x hx
    have e : (i₁ ≫ j₁) x = (i₂ ≫ j₂) x := by rw [hc]
    show j₂ (i₂ x) ∈ U
    simp only [Scheme.Hom.comp_apply] at e
    rw [← e]; exact hx
  have key : ∀ U : Y.left.Opens,
      (∀ (s₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)) (s₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)),
        (i₁.appLE (j₁ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) le_rfl).hom s₁ =
          (i₂.appLE (j₂ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) (hle U)).hom s₂ →
        ∃ d : Γ(Y.left, U), (j₁.app U).hom d = s₁ ∧ (j₂.app U).hom d = s₂) ∧
      (∀ d d' : Γ(Y.left, U), (j₁.app U).hom d = (j₁.app U).hom d' →
        (j₂.app U).hom d = (j₂.app U).hom d' → d = d') := by
    intro U
    let V₁ := j₁ ⁻¹ᵁ U
    let V₂ := j₂ ⁻¹ᵁ U
    let V₀ := i₁ ⁻¹ᵁ V₁
    let k₁ := j₁.resLE U V₁ le_rfl
    let k₂ := j₂.resLE U V₂ le_rfl
    let l₁ := i₁.resLE V₁ V₀ le_rfl
    let l₂ := i₂.resLE V₂ V₀ (hle U)
    have pb1 : IsPullback k₁ (V₁.ι ≫ Y₁.hom) (U.ι ≫ Y.hom) (Spec.map f₁) :=
      (isPullback_resLE_self j₁ U).paste_vert h₁
    have pb2 : IsPullback k₂ (V₂.ι ≫ Y₂.hom) (U.ι ≫ Y.hom) (Spec.map f₂) :=
      (isPullback_resLE_self j₂ U).paste_vert h₂
    have pb0 : IsPullback l₁ (V₀.ι ≫ Y₀.hom) (V₁.ι ≫ Y₁.hom) (Spec.map g₁) :=
      (isPullback_resLE_self i₁ V₁).paste_vert h₀
    have e1 : l₁ ≫ k₁ = l₂ ≫ k₂ := by
      rw [← cancel_mono U.ι]
      simp only [k₁, k₂, l₁, l₂, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, hc]
    have e2 : l₂ ≫ (V₂.ι ≫ Y₂.hom) = (V₀.ι ≫ Y₀.hom) ≫ Spec.map g₂ := by
      simp only [l₂, Category.assoc, Scheme.Hom.resLE_comp_ι_assoc, hc₂]
    have hfl' : Flat (Over.mk (U.ι ≫ Y.hom)).hom := by
      haveI := hfl
      show Flat (U.ι ≫ Y.hom)
      infer_instance
    have H : IsPushout l₁ l₂ k₁ k₂ :=
      _root_.GlobalTheory.FlatPinch.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (Over.mk (U.ι ≫ Y.hom))
        (Over.mk (V₁.ι ≫ Y₁.hom)) (Over.mk (V₂.ι ≫ Y₂.hom)) (Over.mk (V₀.ι ≫ Y₀.hom)) k₁ k₂ l₁ l₂
        hfl' pb1 pb2 pb0 e1 e2
    have hj : ∀ d : Γ(Y.left, U), k₁.appTop.hom (U.topIso.inv.hom d) = V₁.topIso.inv.hom ((j₁.app U).hom d) ∧
        k₂.appTop.hom (U.topIso.inv.hom d) = V₂.topIso.inv.hom ((j₂.app U).hom d) := fun d =>
      ⟨(resLE_appTop_topIso_inv j₁ le_rfl d).trans (by rw [Scheme.Hom.app_eq_appLE]),
       (resLE_appTop_topIso_inv j₂ le_rfl d).trans (by rw [Scheme.Hom.app_eq_appLE])⟩
    refine ⟨fun s₁ s₂ h => ?_, fun d d' e₁ e₂ => ?_⟩
    · obtain ⟨t, ht1, ht2⟩ := pushout_sec_exists H (V₁.topIso.inv.hom s₁) (V₂.topIso.inv.hom s₂)
        (by rw [resLE_appTop_topIso_inv, resLE_appTop_topIso_inv, h])
      refine ⟨U.topIso.hom.hom t, ?_, ?_⟩
      · have := congrArg V₁.topIso.hom.hom ((hj (U.topIso.hom.hom t)).1)
        rwa [Iso.hom_inv_id_apply, ht1, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, eq_comm] at this
      · have := congrArg V₂.topIso.hom.hom ((hj (U.topIso.hom.hom t)).2)
        rwa [Iso.hom_inv_id_apply, ht2, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, eq_comm] at this
    · have := pushout_sec_ext H (U.topIso.inv.hom d) (U.topIso.inv.hom d')
        (by rw [(hj d).1, (hj d').1, e₁]) (by rw [(hj d).2, (hj d').2, e₂])
      have := congrArg U.topIso.hom.hom this
      rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
  refine ⟨fun U a₁ a₂ hg => ?_, fun U d d' e₁ e₂ => Units.ext ((key U).2 d.val d'.val
    (congrArg Units.val e₁) (congrArg Units.val e₂))⟩
  have heq : ∀ (b₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (b₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ),
      (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) b₁ = gm i₂ x (j₂ ⁻¹ᵁ U) b₂) →
      (i₁.appLE (j₁ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) le_rfl).hom b₁.val =
        (i₂.appLE (j₂ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) (hle U)).hom b₂.val := by
    intro b₁ b₂ hb
    apply TopCat.Presheaf.section_ext Y₀.left.sheaf
    intro x hx
    have := congrArg Units.val (hb x hx)
    rw [gm_val i₁ x _ hx, gm_val i₂ x _ (hle U hx)] at this
    simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact this
  obtain ⟨d, hd1, hd2⟩ := (key U).1 a₁.val a₂.val (heq a₁ a₂ hg)
  obtain ⟨d', hd1', hd2'⟩ := (key U).1 (a₁⁻¹).val (a₂⁻¹).val (heq a₁⁻¹ a₂⁻¹ (fun x hx => by
    rw [map_inv, map_inv, hg x hx]))
  have hdd : d * d' = 1 := (key U).2 _ _ (by rw [map_mul, map_one, hd1, hd1', Units.mul_inv])
    (by rw [map_mul, map_one, hd2, hd2', Units.mul_inv])
  exact ⟨⟨d, d', hdd, by rw [mul_comm, hdd]⟩, Units.ext hd1, Units.ext hd2⟩

end GlobalTheory.PinchUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitPullbackThetaSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitPullAct

theorem mono_spMap_toRat {o Ω F : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field F] [CharZero F] (R : Subalgebra o Ω)
    (s : Sp (ratHull R) ⟶ Sp F) : Mono (spMap (toRat R)) := by
  haveI : CharZero Ω :=
    (RingHom.charZero_iff ((ratHull R).val.toRingHom.comp (Spec.preimage s).hom).injective).1 inferInstance
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  exact SurjectiveOnStalks.mono_of_injective (IsPreimmersion.isEmbedding _).injective

theorem exists_pull_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : UTrait Xo c) :
    ∃ ψ : T.P.A.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback T.P.A.A Xo.univ.t.G (T.y ≫ pullback.fst _ _) ψ ∧
      LBIso T.P.A.L (Xo.univ.t.PP.L.pull ψ) ∧
      ∀ a : 𝓞 E, (T.P.oA.act a).left ≫ ψ = ψ ≫ (Xo.univ.t.act.act a).left := by
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  have hm := T.P.U.gen_hom
  haveI : IsMonHom T.P.U.gen.symm.hom := inferInstanceAs (IsMonHom T.P.U.gen.inv)
  have hgen : IsGrpPullback T.P.A.A T.t.G (jK T.V) (T.P.U.gen.inv.left ≫ pullback.fst T.t.G.hom (jK T.V)) :=
    ((isGrpPullback_of_iso T.P.U.gen.symm).comp (isGrpPullback_pullback T.t.G (jK T.V))).congr (Category.id_comp _) rfl
  obtain ⟨e, he, he₁⟩ := grpPullback_iso hgen m₁.cart
  haveI := he
  refine ⟨e.hom.left ≫ m₂.cm.F, ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · have hext : LBIso (T.t.PP.L.pull (pullback.fst T.t.G.hom (jK T.V))) (T.P.A.L.pull T.P.U.gen.hom.left) := by
      obtain ⟨w, hw⟩ := T.P.U.ext
      have hb := T.P.bundle
      exact LBIso.symm (hb ▸ ⟨w, hw⟩)
    have s1 := GlobalTheory.TripleTheta.lbIso_inv T.P.U.gen hext
    have s2 := (GlobalTheory.GenSpread.lbIso_pull_pull T.t.PP.isLB (a := pullback.fst T.t.G.hom (jK T.V))
      T.P.U.gen.inv.left rfl).symm
    have s3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₁) e.hom.left he₁.symm
    have s4 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₂) e.hom.left rfl
    exact LBIso.trans T.P.A.isLB (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB Xo.univ.t.PP.isLB _) s1
      (LBIso.trans (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB T.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) s2
      (LBIso.trans (pull_isLB T.t.PP.isLB _) (pull_isLB tK.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) (LBIso.symm s3) s4))
  · letI := H.starRing
    have h0 := T.P.lin.ext a
    have h1 : T.P.oA.act a ≫ T.P.U.gen.inv = T.P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (T.t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc, eq_comm, Iso.inv_comp_eq]
      exact h0
    have h2 : ((Over.pullback (jK T.V)).map (T.t.act.act a)).left ≫ pullback.fst T.t.G.hom (jK T.V) =
        pullback.fst T.t.G.hom (jK T.V) ≫ (T.t.act.act a).left := pullback.lift_fst _ _ _
    have h3 : (T.P.oA.act a).left ≫ e.hom.left = e.hom.left ≫ (tK.act.act a).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, m₁.act a, ← Category.assoc e.hom.left, he₁, ← Category.assoc,
          ← Over.comp_left, h1, Over.comp_left, Category.assoc, h2, Category.assoc]
      · rw [← Over.comp_left, ← Over.comp_left, Over.w, Over.w]
    rw [← Category.assoc, h3, Category.assoc, m₂.act a, Category.assoc]

theorem exists_pull_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (T : UTrait Xo cf) (yK : ratHull S.R →+* FractionRing T.V), spMap yK ≫ u' = T.y → ∃ φ : T.P.A.A.left ⟶ ρ.P.A.left, IsGrpPullback T.P.A.A ρ.P.A (spMap (yK.comp (toRat S.R))) φ ∧ LBIso T.P.A.L (ρ.P.L.pull φ) ∧ ∀ (Y : Over (Sp (FractionRing T.V))) (x x' : Y ⟶ T.P.A.A) (w w' : Y.left ⟶ G.left) (a : 𝓞 E), w ≫ α = x.left ≫ φ → w' ≫ α = x'.left ≫ φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → x' = x ≫ T.P.oA.act a := by
  intro E _ _ _ H Dw l Xo cf o Ω _ _ _ S ρ u' G _ α β hα hβ hL T yK hy
  obtain ⟨ψ, hψ, hψL, hψa⟩ := exists_pull_univ T
  have e₀ : T.y ≫ pullback.fst _ _ = spMap yK ≫ u' ≫ pullback.fst _ _ := by rw [← hy, Category.assoc]
  have w₀ : ψ ≫ Xo.univ.t.G.hom = (T.P.A.A.hom ≫ spMap yK) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc, ← e₀]; exact hψ.1.w
  have e₁ := hβ.1.lift_fst _ _ w₀
  have hγ := hβ.cancel (hψ.congr e₀ e₁.symm) (hβ.1.lift_snd _ _ w₀)
  generalize hβ.1.lift _ _ w₀ = γ at e₁ hγ
  refine ⟨γ ≫ α, (hγ.comp hα).congr (by rw [← Spec.map_comp]; rfl) rfl, ?_, fun Y x x' w w' a hw hw' h => ?_⟩
  · exact LBIso.trans T.P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB ρ.P.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp γ rfl e₁.symm hL).symm
  · haveI := mono_spMap_toRat S.R (u' ≫ pullback.snd _ _)
    haveI : Mono α := ⟨fun f g hfg => hα.1.hom_ext hfg ((cancel_mono (spMap (toRat S.R))).1 (by
      rw [Category.assoc, Category.assoc, ← hα.1.w, ← Category.assoc, hfg, Category.assoc]))⟩
    obtain rfl : w = x.left ≫ γ := (cancel_mono α).1 (hw.trans (Category.assoc _ _ _).symm)
    obtain rfl : w' = x'.left ≫ γ := (cancel_mono α).1 (hw'.trans (Category.assoc _ _ _).symm)
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψa a, ← e₁]
      simpa only [Category.assoc] using h
    · rw [Over.w, Over.w]

end GlobalTheory.UPoinc.TraitPullAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBySecBZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.WeightZero

open GlobalTheory.ProjSpace GlobalTheory.AbLaw GlobalTheory.Cartier

theorem veryAmpleBy_of_sval {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Z ⟶ X)} {ε' : K' → ℤ}
    (g : Z ⟶ Y) [IsIso g] (f : Y ⟶ Sp R) {m : ℕ} (s : Fin (m + 1) → (LB.LinComb L φ ε).Sec)
    (t : Fin (m + 1) → (LB.LinComb L φ' ε').Sec)
    (h : ∀ i z J, Good L z J → sval (t i) (𝟙 Z) z J = sval (s i) g z J) (hs : VeryAmpleBy f _ s) :
    VeryAmpleBy (g ≫ f) _ t := by
  obtain ⟨hc, hi⟩ := (veryAmpleBy_iff f s).1 hs
  have key : ∀ z : Z, ∃ (W : Z.Opens) (_ : z ∈ W) (k : (LB.LinComb L φ ε).ι)
      (hk : W ≤ g ⁻¹ᵁ (LB.LinComb L φ ε).U k) (l : (LB.LinComb L φ' ε').ι) (hl : W ≤ (LB.LinComb L φ' ε').U l),
      ∀ j, resG Z hl ((t j).f l) = (g.appLE _ W hk).hom ((s j).f k) := by
    intro z
    choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
    refine ⟨LB.wchart L φ' (fun k => J (𝟙 Z ≫ φ' k)) ⊓ g ⁻¹ᵁ LB.wchart L φ (fun k => J (g ≫ φ k)),
      ⟨Good.mem hJ φ' (𝟙 Z), Good.mem hJ φ g⟩, fun k => J (g ≫ φ k), inf_le_right, fun k => J (𝟙 Z ≫ φ' k),
      inf_le_left, fun j => fn_ext fun y hy => ?_⟩
    obtain ⟨J', hJ', e⟩ := exists_good L hL y (Sum.elim (fun k => 𝟙 Z ≫ φ' k) (fun k => g ≫ φ k))
      (fun a => J (Sum.elim (fun k => 𝟙 Z ≫ φ' k) (fun k => g ≫ φ k) a)) (fun a b e => congrArg J e) (by
        rintro (a | a)
        exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
    have e₁ := h j y J' hJ'
    rw [sval_of (t j) _ y J' _ (fun k => e (.inl k)), sval_of (s j) _ y J' _ (fun k => e (.inr k))] at e₁
    refine (gs_res _ y _ hy _).trans (e₁.trans (Eq.symm ?_))
    exact (gs_res (𝟙 Z) y inf_le_right hy _).trans (gs_pull (𝟙 Z) g y _ hy.2 _)
  have ht : ⨆ i, nonzeroLocus (t i) = ⊤ := by
    refine _root_.top_le_iff.1 fun z _ => ?_
    obtain ⟨W, hz, k, hk, l, hl, e⟩ := key z
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (g z)))
    have h₁ : z ∈ Z.basicOpen (resG Z hl ((t i).f l)) := by
      rw [e i, Scheme.basicOpen_appLE]
      exact ⟨hz, (mem_nonzeroLocus_iff _ k (hk hz)).1 hi⟩
    rw [Scheme.basicOpen_res] at h₁
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, basicOpen_le_nonzeroLocus _ l h₁.2⟩
  refine (veryAmpleBy_iff _ t).2 ⟨ht, ?_⟩
  rw [toProj_eq_comp_of_locally hc g ht fun z => by
    obtain ⟨W, hz, k, hk, l, hl, e⟩ := key z
    exact ⟨W, hz, k, hk, l, hl, 1, fun j => (e j).trans (_root_.one_mul _).symm⟩]
  infer_instance

theorem formEq_weight_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) :
    FormEq (fun _ : Fin k => 𝟙 D.P.A.left) (fun _ => 1) (D.famφB 0) (DegPre.famε k) := by
  intro U _ h
  have h0 : D.c 0 = 1 := by
    have h : D.c 0 = D.c 0 * D.c 0 := by
      have := D.c_add 0 0
      rwa [add_zero] at this
    exact mul_eq_left.1 h.symm
  have h1 : toUnit D.P.A ≫ D.c 0 = 1 := by rw [h0, comp_one]
  have h2 : toUnit D.P.A ≫ η[D.P.A] = 1 := rfl
  have h3 : padd D.P.A (𝟙 D.P.A) (1 : D.P.A ⟶ D.P.A) = 𝟙 _ := _root_.mul_one (𝟙 D.P.A)
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, h1, h2, h3]
  simp [zpow_sub]

theorem exists_veryAmpleBy_secB_zero (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (k : ℕ)
    (hk : 4 ≤ k) : ∃ (m : ℕ) (s : Fin (m + 1) → D.SecB k 0), VeryAmpleBy D.P.A.hom _ s := by
  obtain ⟨m, s, H⟩ := (GlobalTheory.allSixLaws.1.ample (Sp R) D.P k hk).2 ⊤ (isAffineOpen_top _)
  have : IsIso (⊤ : (Sp R).Opens).ι := inferInstanceAs (IsIso (Sp R).topIso.hom)
  have : IsIso (D.P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso D.P.A.left.topIso.hom)
  have h' := (veryAmpleBy_comp_iff (D.P.A.hom ∣_ ⊤) (⊤ : (Sp R).Opens).ι s).2 H
  rw [morphismRestrict_ι] at h'
  let ψ := inv (D.P.A.hom ⁻¹ᵁ ⊤).ι
  have hψ : ψ ≫ (D.P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsIso.inv_hom_id _
  choose s' hs' using fun i => exists_sec_pull (L := D.P.L) _ _ (s i) ψ (fun _ : Fin k => 𝟙 D.P.A.left) fun _ => hψ.symm
  choose t ht using fun i => exists_sec D.P.isLB (formEq_weight_zero D k) (s' i)
  have := veryAmpleBy_of_sval D.P.isLB ψ _ s t (fun i z J hJ => by
    refine (ht i _ _ z J hJ).trans ((hs' i _ z _ (hJ.mem _ _)).trans ?_)
    rw [Category.id_comp, sval_of (s i) ψ z J (fun _ => J (𝟙 _ ≫ 𝟙 _)) fun _ => by rw [hψ, Category.id_comp]]) h'
  rw [← Category.assoc, hψ, Category.id_comp] at this
  exact ⟨m, t, this⟩

end GlobalTheory.Mum.WeightZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.OriginSec

theorem isUnit_sval_iff' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  simp only [add_zero, padd] at h
  rw [← Hom.mul_def] at h
  have : D.c 0 = 1 := by simpa using h
  rw [this, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem formEq_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) :
    FormEq (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => (k : ℤ)) (D.famφB 0) (DegPre.famε k) := by
  have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A])).left = 𝟙 D.P.A.left := by
    rw [padd, ← Hom.mul_def, ← Hom.one_def, _root_.mul_one]; rfl
  intro U _ h
  rw [Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, c_zero, e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

end GlobalTheory.Mum.OriginSec


open GlobalTheory.Mum.OriginSec GlobalTheory.SecRingIso in
theorem GlobalTheory.Mum.exists_secB_zero_nonzero_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  intro R _ _ _ _ D
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨n, hn, a, b, ha, hb⟩ := GlobalTheory.exists_sec_succ_of_relAmple R D.toPre.P.A D.toPre.P.L D.toPre.P.isLB
    D.toPre.P.ample (eSec D.toPre.P.A (closedPoint R))
  let Q : ℕ → Prop := fun m => ∃ d : H0 D.toPre.P.L m, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus d
  have hQ : ∀ m m', Q m → Q m' → Q (m + m') := fun m m' ⟨d, hd⟩ ⟨d', hd'⟩ => by
    obtain ⟨e, he⟩ := exists_mul d d'
    exact ⟨e, mem_mul he hd hd'⟩
  have hij : ∀ i j : ℕ, Q (n * (i + 1) + (n + 1) * j) := by
    intro i j
    induction j with
    | zero =>
      induction i with
      | zero => simpa using (⟨a, ha⟩ : Q n)
      | succ i ih =>
        have := hQ _ _ ih ⟨a, ha⟩
        rwa [show n * (i + 1 + 1) + (n + 1) * 0 = n * (i + 1) + (n + 1) * 0 + n by ring]
    | succ j ih =>
      have := hQ _ _ ih ⟨b, hb⟩
      rwa [show n * (i + 1) + (n + 1) * (j + 1) = n * (i + 1) + (n + 1) * j + (n + 1) by ring]
  refine ⟨n * (n + 1), fun k hk => ?_⟩
  obtain ⟨d, hd⟩ : Q k := by
    have hk' : n * (k / n) + k % n = k := Nat.div_add_mod k n
    have hr : k % n < n := Nat.mod_lt _ hn
    have hq : n + 1 ≤ k / n := (Nat.le_div_iff_mul_le hn).2 (by rw [mul_comm]; exact hk)
    obtain ⟨t, ht⟩ : ∃ t, k / n = k % n + 1 + t := ⟨k / n - k % n - 1, by omega⟩
    have e : k = n * (t + 1) + (n + 1) * (k % n) := by
      conv_lhs => rw [← hk', ht]
      ring
    rw [e]
    exact hij _ _
  obtain ⟨b', hb'⟩ := exists_sec D.toPre.P.isLB (formEq_zero D.toPre k) d
  refine ⟨b', ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L (eSec D.toPre.P.A (closedPoint R)) J :=
    ⟨fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose,
      fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose_spec⟩
  have h1 := (isUnit_sval_iff' d (𝟙 _) _ hJ).2 hd
  rw [← hb' _ (𝟙 _) _ J hJ] at h1
  exact (isUnit_sval_iff' b' (𝟙 _) _ hJ).1 h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extLI_preimage_le {X X' Y : Scheme.{0}} (a : Y ⟶ X') (f : X' ⟶ X) (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X.Opens) : a ⁻¹ᵁ (f ⁻¹ᵁ W) ≤ α ⁻¹ᵁ W := by
  intro y hy
  show α y ∈ W
  rw [← e, Scheme.Hom.comp_apply]
  exact hy

theorem extLI_le_chart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X'.Opens) (j : L.ι) (hW : W ≤ f ⁻¹ᵁ L.U j) :
    a ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => extLI_preimage_le a f α e (L.U j) (hW hy)

theorem extLI_le_wchart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (j : Fin 1 → L.ι) :
    a ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j ≤ LB.wchart L (K := Fin 1) (fun _ => α) j :=
  fun _ hy => Set.mem_iInter.2 fun k => extLI_preimage_le a f α e (L.U (j k)) (Set.mem_iInter.1 hy k)

theorem extLI_preimage_mono {X Y : Scheme.{0}} (a : Y ⟶ X) {V V' : X.Opens} (hV : V ≤ V') : a ⁻¹ᵁ V ≤ a ⁻¹ᵁ V' :=
  fun _ hz => hV hz

theorem extLI_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE h3).op).hom x := by
  change (Y.presheaf.map (homOfLE h1).op ≫ Y.presheaf.map (homOfLE h2).op).hom x = _
  rw [← Functor.map_comp]
  rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentPairs
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_pairs : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Algebra R D]
    [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D'), (ψ : D →+* D').FaithfullyFlat → ∀ a : D',
    (∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → α a = β a) →
      ∃! e : D, ψ e = a := by
  intro R _ D D' _ _ _ _ ψ hψ a h
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
  have hinj : Function.Injective (algebraMap D D') := FaithfulSMul.algebraMap_injective D D'
  let α : D' →ₐ[R] D' ⊗[D] D' := Algebra.TensorProduct.includeLeft
  let β : D' →ₐ[R] D' ⊗[D] D' := (Algebra.TensorProduct.includeRight).restrictScalars R
  have hαβ : α.comp ψ = β.comp ψ := by
    ext x
    show ψ x ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] ψ x
    have : ψ x = algebraMap D D' x := rfl
    rw [this, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hab : a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a := h _ α β hαβ
  obtain ⟨e, he⟩ := GlobalTheory.ff_descent_elem D D' a hab
  exact ⟨e, he, fun e' he' => hinj (he'.trans he.symm)⟩

end GlobalTheory
end

