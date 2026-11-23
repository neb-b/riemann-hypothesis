module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2992
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValuesMemSubfieldGaloisDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem spMap_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem gen_unique_of_eq {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {Ix : Type} [Fintype Ix]
    {φ φ' : Ix → (Y ⟶ X)} {ε : Ix → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (hφ : φ' = φ) {u : LB.Gen (LB.LinComb M φ' ε)}
    {u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  subst hφ
  exact gen_unique hM p e he hp hu hu' h Z r z J hJ

theorem gen_values_mem : ∀ (V₁ W₀ : Type) [CommRing V₁] [CommRing W₀] (ib : W₀ →+* V₁) (A : Over (Sp V₁)) [GrpObj A],
    IsAbelianScheme A → ∀ (B₀ : Over (Sp W₀)) (β : A.left ⟶ B₀.left), IsPullback β A.hom B₀.hom (spMap ib) →
    ∀ (M₀ : LB B₀.left), M₀.IsLB → ∀ (Ix : Type) [Fintype Ix] (φ : Ix → (A.left ⟶ B₀.left))
    (ψ : Ix → (B₀.left ⟶ B₀.left)), (∀ k, φ k = β ≫ ψ k) → ∀ (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb M₀ φ ε)),
    t.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    (∀ a, ev (ib a) ∈ k₀) → ∀ x₁ : Sp K ⟶ A.left, x₁ ≫ A.hom = spMap ev → DefOver k₀ (x₁ ≫ β) →
    (∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → val t x₁ z J = 1) →
    ∀ x : Sp K ⟶ A.left, x ≫ A.hom = spMap ev → DefOver k₀ (x ≫ β) →
    ∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → ∃ c ∈ k₀, (val t x z J).val = toStk z c := by
  intro V₁ W₀ _ _ ib A _ hA B₀ β hβ M₀ hM₀ Ix _ φ ψ hφ ε t ht K _ _ ev k₀ hk₀ hk x₁ hx₁ hd₁ h1 x hx hd z J hJ
  classical
  have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
  let v : (Sp K ⟶ A.left) → ((Sp K ⟶ B₀.left) → M₀.ι) → K := fun x J =>
    valF x (LB.wchart M₀ φ (fun k => J (x ≫ φ k))) ((genSec t ht).f (fun k => J (x ≫ φ k)))
  have hv : ∀ x z J, Good M₀ z J → (val t x z J).val = toStk z (v x J) := fun x z J hJ =>
    (sval_genSec t ht x z hJ).symm.trans (toStk_valF_gs x _ z (hJ.mem φ x) _).symm
  have hfix : ∀ x : Sp K ⟶ A.left, DefOver k₀ (x ≫ β) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) →
      ∀ k, spMap σ.toRingHom ≫ x ≫ φ k = x ≫ φ k := by
    intro x hd σ hσ k
    obtain ⟨P₀, hP₀⟩ := hd
    rw [hφ k, ← Category.assoc x, ← hP₀, Category.assoc, ← Category.assoc (spMap σ.toRingHom),
      spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  have hvσ : ∀ x : Sp K ⟶ A.left, DefOver k₀ (x ≫ β) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∀ z J, Good M₀ z J →
      (val t (spMap σ.toRingHom ≫ x) z J).val = toStk z (σ (v x J)) := fun x hd σ hσ z J hJ =>
    (sval_genSec t ht _ z hJ).symm.trans (sval_spMap _ σ.toRingHom x z hJ (hfix x hd σ hσ))
  have hsurj : Function.Surjective (pullback.snd A.hom (spMap ev)).appTop.hom :=
    fun w => TLinPf.const_pullback GlobalTheory.SemiRigid.globalFns (spMap ev) A hA w
  have key : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ (v x J) = v x J := by
    intro σ hσ
    have hc : (pullback.fst A.hom (spMap ev) ≫ β) ≫ B₀.hom =
        (pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom ≫ spMap ev) ≫ spMap ib := by
      simp only [Category.assoc]
      rw [hβ.w, pullback.condition_assoc, spMap_two, spMap_conj k₀ _ hf σ hσ]
    obtain ⟨l, hl1, hl2⟩ : ∃ l : pullback A.hom (spMap ev) ⟶ A.left, l ≫ β = pullback.fst A.hom (spMap ev) ≫ β ∧
        l ≫ A.hom = pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom ≫ spMap ev :=
      ⟨hβ.lift _ _ hc, hβ.lift_fst _ _ hc, hβ.lift_snd _ _ hc⟩
    obtain ⟨σt, hs1, hs2⟩ : ∃ σt : pullback A.hom (spMap ev) ⟶ pullback A.hom (spMap ev),
        σt ≫ pullback.fst A.hom (spMap ev) = l ∧
        σt ≫ pullback.snd A.hom (spMap ev) = pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom :=
      ⟨pullback.lift l _ (by rw [hl2, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hσβ : σt ≫ pullback.fst A.hom (spMap ev) ≫ β = pullback.fst A.hom (spMap ev) ≫ β := by
      rw [reassoc_of% hs1, hl1]
    have hpt : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev), DefOver k₀ (y ≫ β) →
        pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp]) ≫ σt =
          spMap σ.toRingHom ≫ pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp]) := by
      intro y hy hd
      obtain ⟨P₀, hP₀⟩ := hd
      apply pullback.hom_ext
      · simp only [Category.assoc, hs1, pullback.lift_fst]
        apply hβ.hom_ext
        · simp only [Category.assoc, hl1, pullback.lift_fst_assoc]
          rw [← hP₀, ← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
        · simp only [Category.assoc, hl2, pullback.lift_snd_assoc, Category.id_comp, hy]
      · simp only [Category.assoc, hs2, pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd, Category.comp_id]
    let tK := LB.pullGen M₀ φ ε t (pullback.fst A.hom (spMap ev))
    have htK : tK.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
    have hu : (LB.pullGen M₀ _ ε tK σt).IsGen := DVR.pullGen_isGen _ _ _ _ htK _
    have hval : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev), DefOver k₀ (y ≫ β) → ∀ z J, Good M₀ z J →
        val (LB.pullGen M₀ _ ε tK σt) (pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp])) z J =
          val t (spMap σ.toRingHom ≫ y) z J := by
      intro y hy hd z J hJ
      rw [val_pull hJ, hpt y hy hd, val_pull hJ, Category.assoc, pullback.lift_fst]
    have hvalK : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev) z J, Good M₀ z J →
        val tK (pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp])) z J = val t y z J := by
      intro y hy z J hJ
      rw [val_pull hJ, pullback.lift_fst]
    have huniq := gen_unique_of_eq hM₀ (pullback.snd A.hom (spMap ev))
      (pullback.lift x₁ (𝟙 _) (by rw [hx₁, Category.id_comp])) (pullback.lift_snd _ _ _) hsurj
      (funext fun k => by rw [hφ k]; exact (reassoc_of% hσβ) (ψ k)) hu htK (fun y J hJ => by
        rw [hval x₁ hx₁ hd₁ y J hJ, hvalK x₁ hx₁ y J hJ, h1 y J hJ]
        apply Units.ext
        have e1 := hv x₁ y J hJ
        rw [h1 y J hJ, Units.val_one, ← map_one (toStk y)] at e1
        rw [hvσ x₁ hd₁ σ hσ y J hJ, ← (toStk y).injective e1, map_one, map_one, Units.val_one])
      (Sp K) (pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])) z J hJ
    rw [hval x hx hd z J hJ, hvalK x hx z J hJ] at huniq
    have e2 := congrArg Units.val huniq
    rw [hvσ x hd σ hσ z J hJ, hv x z J hJ] at e2
    exact (toStk z).injective e2
  refine ⟨v x J, ?_, hv x z J hJ⟩
  apply mem_of_finite_conj k₀ hk₀
  apply (Set.finite_singleton (v x J)).subset
  rintro b ⟨σ, hσ, rfl⟩
  exact key σ hσ

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelIsProperOfCompact
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

lemma specMap_contravariant_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem isProper_model_of_compact (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R]
    [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (M : Model b N)
    (hc : 2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) : IsProper M.s := by
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  refine _root_.GlobalTheory.ValuativeFlat.isProper_of_lift_dominating R M.X M.s M.qproj inferInstance ?_
  intro V K _ _ _ _ _ _ _ _ β x hx

  obtain ⟨oK, ⟨hK⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp K) M.s x M.univ
  generalize hs : x ≫ M.s = s₀ at oK hK
  obtain rfl : s₀ = spMap ((algebraMap V K).comp β) := hs.symm.trans hx

  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomp, _, hloc, _, G, _, hmod, hab⟩ :=
    _root_.GlobalTheory.HTPotGood.potGood p D R b N V K ((algebraMap V K).comp β) oK hc

  obtain ⟨oL, ⟨hL⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp K) (Sp L) (spMap ((algebraMap V K).comp β))
    (spMap (algebraMap K L)) oK
  have hLs : spMap (algebraMap K L) ≫ spMap ((algebraMap V K).comp β) =
      spMap ((algebraMap W L).comp ((algebraMap V W).comp β)) := by
    rw [specMap_contravariant_comp_ringHom, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hcomp]
  generalize hs' : spMap (algebraMap K L) ≫ spMap ((algebraMap V K).comp β) = s₁ at oL hL
  obtain rfl : s₁ = spMap ((algebraMap W L).comp ((algebraMap V W).comp β)) := hs'.symm.trans hLs
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L oK.A G hmod oL.A hL.φ hL.cart
  obtain ⟨oW, ⟨hW⟩⟩ := _root_.GlobalTheory.HTObjExt.extends_obj p D R b N W L ((algebraMap V W).comp β) oL G φ hab hφ
  obtain ⟨f, ⟨hfs, ⟨hf⟩⟩, -⟩ := M.rep (Sp W) _ oW
  obtain ⟨h₁⟩ := _root_.GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oL oW M.univ _ _ hW hf
  obtain ⟨h₂⟩ := _root_.GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oL oK M.univ _ _ hL hK
  obtain ⟨g, -, hg⟩ := M.rep (Sp L) _ oL
  have e₁ : spMap (algebraMap W L) ≫ f = g := hg _ ⟨by rw [Category.assoc, hfs, specMap_contravariant_comp_ringHom], ⟨h₁⟩⟩
  have e₂ : spMap (algebraMap K L) ≫ x = g := hg _ ⟨by rw [Category.assoc, hx, hLs], ⟨h₂⟩⟩
  exact ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcomp, hloc, f, e₂.trans e₁.symm⟩

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeNoetherianInducBis
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Step

theorem exists_sq_zero (R : Type) [CommRing R] [IsNoetherianRing R] (h : ¬ IsReduced R) :
    ∃ J : Ideal R, J ≠ ⊥ ∧ J ^ 2 = ⊥ := by
  classical
  set N := nilradical R with hNdef
  have hN : N ≠ ⊥ := by
    intro h0
    apply h
    refine ⟨fun x hx => ?_⟩
    have : x ∈ N := (mem_nilradical).2 hx
    rw [h0] at this
    exact (Submodule.mem_bot R).1 this
  have hnil : IsNilpotent N := IsNoetherianRing.isNilpotent_nilradical R
  let n := Nat.find hnil
  have hn : N ^ n = 0 := Nat.find_spec hnil
  have hn0 : n ≠ 0 := by
    intro h0
    have : N ^ 0 = 0 := h0 ▸ hn
    rw [pow_zero] at this
    apply hN
    rw [eq_bot_iff, ← Ideal.zero_eq_bot, ← this, Ideal.one_eq_top]
    exact le_top
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hN
    rw [hk] at hn
    simpa using hn
  refine ⟨N ^ k, ?_, ?_⟩
  · intro h0
    have := Nat.find_min hnil (show k < n by omega)
    exact this h0
  · rw [← pow_mul]
    apply le_bot_iff.1
    calc N ^ (k * 2) ≤ N ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      _ = ⊥ := by rw [← Nat.succ_eq_add_one, ← hk]; exact hn

theorem hasRep_opens {S X : Scheme.{0}} (i : X ⟶ S) [IsOpenImmersion i] (A : Over S) [GrpObj A] (g : ℕ)
    (V : S.Opens) (hV : (V : Set S) ⊆ Set.range i) (h : HasRep A g (Over.mk i)) : HasRep A g (Over.mk V.ι) := by
  have hr : Set.range V.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]; exact hV
  let m : Over.mk V.ι ⟶ Over.mk i := Over.homMk (IsOpenImmersion.lift i V.ι hr) (IsOpenImmersion.lift_fac _ _ _)
  exact GlobalTheory.T.baseChangeBis S A (Over.mk i) (Over.mk V.ι) g m h

theorem comap_ne_bot_away {R : Type} [CommRing R] (f : R) (J' : Ideal (Localization.Away f)) (h : J' ≠ ⊥) :
    J'.comap (algebraMap R (Localization.Away f)) ≠ ⊥ := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) y
  have hx : algebraMap R (Localization.Away f) x ∈ J' := by
    rw [← IsLocalization.mk'_spec (Localization.Away f) x s]
    exact J'.mul_mem_right _ hy
  have hx0 : algebraMap R (Localization.Away f) x ≠ 0 := by
    intro h0
    apply hy0
    rw [IsLocalization.mk'_eq_zero_iff]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ x).1 h0
  intro hb
  have : x ∈ J'.comap (algebraMap R (Localization.Away f)) := hx
  rw [hb, Submodule.mem_bot] at this
  exact hx0 (by rw [this, map_zero])

theorem hasRep_quot {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (ha : ∀ J' : Ideal R', J' ≠ ⊥ → J'.comap a ≠ ⊥) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (φ : A'.left ⟶ A.left) (hφ : IsGrpPullback A' A (spMap a) φ) (g : ℕ)
    (hJ : ∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) :
    ∀ J' : Ideal R', J' ≠ ⊥ → HasRep A' g (Over.mk (spMap (Ideal.Quotient.mk J'))) := by
  intro J' hJ'
  set J := J'.comap a
  let q : R ⧸ J →+* R' ⧸ J' := Ideal.quotientMap J' a le_rfl
  have hq : q.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk J').comp a := by
    ext x; rfl
  have w : spMap q ≫ spMap (Ideal.Quotient.mk J) = (Over.mk (spMap (Ideal.Quotient.mk J') ≫ spMap a)).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let m : Over.mk (spMap (Ideal.Quotient.mk J') ≫ spMap a) ⟶ Over.mk (spMap (Ideal.Quotient.mk J)) :=
    Over.homMk (spMap q) w
  have h1 := GlobalTheory.T.baseChangeBis _ A _ _ g m (hJ J (ha J' hJ'))
  exact ((_root_.GlobalTheory.DualCon.hasRep_baseChange_iff _ _ (spMap a) A A' φ hφ g (Over.mk (spMap (Ideal.Quotient.mk J')))).1).2 h1

theorem local_rep (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hJ : ∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) (s : Sp R) :
    ∃ V : (Sp R).Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι) := by
  obtain ⟨f, hs, W, hW, hWf⟩ := _root_.GlobalTheory.chartAroundUnit R A s
  let a := algebraMap R (Localization.Away f)
  let A' := (Over.pullback (spMap a)).obj A
  letI : GrpObj A' := Functor.grpObjObj
  have hφ : IsGrpPullback A' A (spMap a) (pullback.fst _ _) := isGrpPullback_pullback A (spMap a)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback a A A' _ g hφ hA hg
  obtain ⟨V, hV, hVs⟩ := _root_.GlobalTheory.affine_preimage_pullback_meets_fibres a A W hW hWf
  haveI : @Algebra.FiniteType ℤ (Localization.Away f) _ _ (Ring.toIntAlgebra _) := by
    have h := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ R)
      (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) (Localization.Away f))
    convert h using 1 <;> first | rfl | exact Subsingleton.elim _ _
  have h1 : HasRep A' g (𝟙_ _) :=
    _root_.GlobalTheory.DualConStep.step (Localization.Away f) A' g hA' hg' V hV hVs
      (hasRep_quot a (comap_ne_bot_away f) A A' _ hφ g hJ)
  have h2 := ((_root_.GlobalTheory.DualCon.hasRep_baseChange_iff _ _ (spMap a) A A' _ hφ g (𝟙_ _)).1).1 h1
  have h3 : HasRep A g (Over.mk (spMap a)) := by
    convert h2 using 2 <;> first | rfl | exact (Category.id_comp _).symm
  have : IsOpenImmersion (spMap a) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨(spMap a).opensRange, hs, hasRep_opens (spMap a) A g _ (fun x hx => hx) h3⟩

theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  by_cases hr : IsReduced R
  · exact _root_.GlobalTheory.DualCon.hasRep_of_local _ A g hA (local_rep R A g hA hg hJ)
  · obtain ⟨J, hJ0, hJ2⟩ := exists_sq_zero R hr
    exact _root_.GlobalTheory.LBLift.hasRep_of_sqZero R A g hA hg J hJ2 (hJ J hJ0)

end GlobalTheory.DualCon.Step
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConnectionClosedFibre
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem heat_connection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (e : ℕ), 1 ≤ e → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∃ (V : h.J → P.D.toPre.P.A.left.Opens) (ed : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.D.toPre.P.A P.D.toPre.P.L A₀ m₀ (fun r => (ρ r).snd) V h.j ed pb ∧ (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∃ c : P.D.toPre.X →+ k, ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ P.D.toPre.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ O : A₀.left.Opens, O ≤ m₀ ⁻¹ᵁ LB.wchart P.D.toPre.P.L (P.D.toPre.famφB α) (fun j => h.j (i j)) → (∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) O = 2 * (e : Γ(A₀.left, O)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) O + pbT m₀ (σ.f (fun j => h.j (i j))) O * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O + constFn A₀.hom O (c α))) := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _
  letI := H.starRing
  intro Y n' v' dd hv D q _ h hB _ hΘ ρ hρ e he A₀ _ m₀ hpull
  have hfst : ∀ r, (ρ r).fst = MvPowerSeries.constantCoeff r := fun r => by
    rw [hρ r]; simp
  have hsnd : ∀ r, (ρ r).snd = MvPowerSeries.constantCoeff (D r) := fun r => by
    rw [hρ r]; simp
  have he0 : (e : k) ≠ 0 := by
    have : (0 : ℕ) < e := he
    exact_mod_cast this.ne'
  have hF : IsFibre Y h ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) e
      (algebraMap k (ChartRing k m d) ((e : k)⁻¹)) A₀ m₀ :=
    { field := fun a => (hv a).1
      const := fun a V r => GlobalTheory.Heat.Adjust.inv_constFn Y.H (v' a) (dd a) (hv a) V r
      wt := fun a α V f hf => GlobalTheory.Heat.IsInv.isWt Y (v' a) (dd a) (hv a) α V f hf
      basic := hB
      symb := fun a b => by
        show (ρ (h.Θ a b)).fst = 0
        rw [hfst]
        by_contra hne
        have hu : IsUnit (h.Θ a b) :=
          MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hne)
        exact (IsLocalRing.mem_maximalIdeal _).mp (hΘ a b) hu
      inv := by
        rw [← map_natCast (algebraMap k (ChartRing k m d)) e, ← map_mul, inv_mul_cancel₀ he0, map_one]
      pull := hpull }
  obtain ⟨V, ed, pb, hC, hDs⟩ := _root_.GlobalTheory.HeatConn.exists_connK_desc Y h _ e _ A₀ m₀ hF
  have hD' : (fun r => ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) (D r)) = fun r => (ρ r).snd := by
    funext r
    show (ρ (D r)).fst = (ρ r).snd
    rw [hfst, hsnd]
  rw [hD'] at hC
  refine ⟨V, ed, pb, hC, hDs.1, ?_⟩
  intro B' _ π₁ π₂ c' h1 h2 h3 h4 pr hpr1 hpr2 hed
  have hCom := _root_.GlobalTheory.HeatConn.Comm.commutes P.D.toPre ρ A₀ m₀ hpull ed B' π₁ π₂ c' h1 h2 h3 h4 pr hpr1 hpr2 hed
  rw [← hD'] at hC
  have hCF := _root_.GlobalTheory.HeatConn.chartFree Y h _ e _ A₀ m₀ hF V ed pb hC hDs hCom
  choose cf hcf using fun α => _root_.GlobalTheory.HeatConn.exists_coordEq Y h _ e _ A₀ m₀ hF V ed pb hC hDs α (hCF α)
  have hadd : ∀ α β, cf (α + β) = cf α + cf β := fun α β =>
    _root_.GlobalTheory.HeatConn.coordEq_const_add Y h _ e _ A₀ m₀ hF V ed pb hC hDs hCom α β (cf α) (cf β) (cf (α + β))
      (hcf α) (hcf β) (hcf (α + β))
  refine ⟨AddMonoidHom.mk' cf hadd, ?_⟩
  intro α σ σ' hT i T hT1 hT2 O' hO1 hO2
  exact _root_.GlobalTheory.HeatConn.heat_term_fibre Y h _ e _ A₀ m₀ hF V ed pb hC hDs α (cf α) (hcf α) σ σ' hT i T hT1 hT2 O' hO1 hO2

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomialStatement
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
theorem _root_.GlobalTheory.T.heatOperator_shift_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  first | exact @GlobalTheory.Heat.heat_div_monomial | exact GlobalTheory.Heat.heat_div_monomial | (intros; apply GlobalTheory.Heat.heat_div_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDim
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_finite_free_rank_le_of_prime (K : Type) [Field K] (l : ℕ) [Fact l.Prime]
    (hl : (l : K) ≠ 0) (A B : AbVar K) :
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  obtain ⟨hFA, hfA, hrA, -, -⟩ := _root_.GlobalTheory.AV.AbVar.tl_free_finrank K l hl A
  obtain ⟨hFB, hfB, hrB, -, -⟩ := _root_.GlobalTheory.AV.AbVar.tl_free_finrank K l hl B
  obtain ⟨Q, hpar, hpos, hdef⟩ := GlobalTheory.T.exists_posDef_quadraticForm_hom K A B
  have hrT : Module.finrank ℤ_[l] (Tl l A →ₗ[ℤ_[l]] Tl l B) = 4 * A.dim * B.dim := by
    rw [Module.finrank_linearMap, hrA, hrB]; ring
  refine _root_.GlobalTheory.finite_free_of_definite_form_of_rank_le (A ⟶ B) Q hpar hpos hdef (4 * A.dim * B.dim) ?_
  intro n u hu
  rw [← hrT]
  refine GlobalTheory.T.rank_le_finrank_of_injective_mod_prime_posDef_form l (A ⟶ B) (Tl l A →ₗ[ℤ_[l]] Tl l B) Q hpar hpos hdef (tmap l A B) ?_ n u hu
  intro f φ hφ
  exact GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul K l hl A B f φ hφ

theorem hom_finite_free_rank_le : ∀ (K : Type) [Field K] (A B : AbVar K),
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  intro K _ A B
  by_cases h2 : ((2 : ℕ) : K) = 0
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : ((3 : ℕ) : K) ≠ 0 := by
      have : ((3 : ℕ) : K) = ((2 : ℕ) : K) + 1 := by push_cast; ring
      rw [this, h2, zero_add]; exact one_ne_zero
    exact hom_finite_free_rank_le_of_prime K 3 h3 A B
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hom_finite_free_rank_le_of_prime K 2 h2 A B

end GlobalTheory.AV.AbVar
end

