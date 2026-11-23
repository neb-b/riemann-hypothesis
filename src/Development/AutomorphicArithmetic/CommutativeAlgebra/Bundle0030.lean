module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001
public import Development.EtaleCohomology.EtaleSheaves.Bundle0041
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0026
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0018
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0022
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0017
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0020
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0016
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0025
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicOfIsoOfIsZeroOfBiproduct
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

namespace UpperTheory.AdditiveHomTwist

universe v₁ v₂ u₁ u₂

private theorem biprod_iso {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (S₁ S₂ : C) [HasBinaryBiproduct S₁ S₂] (T : D)
    (s₁ : F.obj S₁ ⟶ T) (p₁ : T ⟶ F.obj S₁) (s₂ : F.obj S₂ ⟶ T) (p₂ : T ⟶ F.obj S₂)
    (h₁ : s₁ ≫ p₁ = 𝟙 _) (h₂ : s₂ ≫ p₂ = 𝟙 _) (h₁₂ : s₁ ≫ p₂ = 0) (h₂₁ : s₂ ≫ p₁ = 0)
    (ht : p₁ ≫ s₁ + p₂ ≫ s₂ = 𝟙 _) : Nonempty (F.obj (S₁ ⊞ S₂) ≅ T) := by
  refine ⟨{ hom := F.map biprod.fst ≫ s₁ + F.map biprod.snd ≫ s₂
            inv := p₁ ≫ F.map biprod.inl + p₂ ≫ F.map biprod.inr
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₁₂, reassoc_of% h₂₁,
      zero_comp, comp_zero, add_zero, zero_add]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add (f := _), biprod.total, F.map_id]
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc]
    simp only [biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      F.map_id, F.map_zero, Category.id_comp, zero_comp, comp_zero, add_zero, zero_add]
    exact ht

variable {B : Scheme.{0}} {q : ℕ}

private noncomputable def hm {P P' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (J : Shv (ZMod q)) : HP P' J ⟶ HP P J :=
  Functor.whiskerRight (NatTrans.op φ) _

private theorem hm_id (P : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : hm (𝟙 P) J = 𝟙 _ := by
  unfold hm
  rw [NatTrans.op_id]
  exact Functor.whiskerRight_id' _

private theorem hm_comp {P P' P'' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (ψ : P' ⟶ P'') (J : Shv (ZMod q)) :
    hm ψ J ≫ hm φ J = hm (φ ≫ ψ) J := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change φ.app U.unop ≫ ψ.app U.unop ≫ (x : P''.obj U.unop ⟶ J) = (φ.app U.unop ≫ ψ.app U.unop) ≫ x
  exact (Category.assoc _ _ _).symm

private theorem hm_zero (P P' : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : hm (0 : P ⟶ P') J = 0 := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change (0 : P.obj U.unop ⟶ P'.obj U.unop) ≫ (x : P'.obj U.unop ⟶ J) = 0
  exact zero_comp

private theorem hm_add {P P' : B.Etale ⥤ Shv (ZMod q)} (φ ψ : P ⟶ P') (J : Shv (ZMod q)) :
    hm (φ + ψ) J = hm φ J + hm ψ J := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change (φ.app U.unop + ψ.app U.unop) ≫ (x : P'.obj U.unop ⟶ J) = φ.app U.unop ≫ x + ψ.app U.unop ≫ x
  exact Preadditive.add_comp _ _ _ _ _ _

private theorem transfer (S : SShv B q) [Injective S] {G : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} (e : S.obj ≅ G) :
    ∃ h : Presheaf.IsSheaf (EtTop B) G, Injective (⟨G, h⟩ : SShv B q) := by
  have h : Presheaf.IsSheaf (EtTop B) G := (Presheaf.isSheaf_of_iso_iff e).1 S.property
  refine ⟨h, ?_⟩
  have i : S ≅ (⟨G, h⟩ : SShv B q) :=
    (fullyFaithfulSheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).preimageIso e
  exact Injective.of_iso i inferInstance

end UpperTheory.AdditiveHomTwist

open UpperTheory.AdditiveHomTwist ZeroObject in
theorem UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct :
    ∀ (q : ℕ) (B : Scheme.{0}), (∀ P P' : B.Etale ⥤ Shv (ZMod q), Nonempty (P ≅ P') → Good P → Good P') ∧ (∀ P : B.Etale ⥤ Shv (ZMod q), (∀ U, IsZero (P.obj U)) → Good P) ∧ ∀ (P P₁ P₂ : B.Etale ⥤ Shv (ZMod q)) (i₁ : P₁ ⟶ P) (r₁ : P ⟶ P₁) (i₂ : P₂ ⟶ P) (r₂ : P ⟶ P₂), i₁ ≫ r₁ = 𝟙 _ → i₂ ≫ r₂ = 𝟙 _ → i₁ ≫ r₂ = 0 → i₂ ≫ r₁ = 0 → r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 _ → Good P₁ → Good P₂ → Good P := by
  intro q B
  refine ⟨?_, ?_, ?_⟩
  · intro P P' hPP hP
    obtain ⟨e⟩ := hPP
    unfold Good at hP ⊢
    intro J hJ
    obtain ⟨h, hi⟩ := hP J hJ
    have e' : HP P J ≅ HP P' J :=
      { hom := hm e.inv J
        inv := hm e.hom J
        hom_inv_id := by rw [hm_comp, e.hom_inv_id, hm_id]
        inv_hom_id := by rw [hm_comp, e.inv_hom_id, hm_id] }
    exact transfer (⟨HP P J, h⟩ : SShv B q) e'
  · intro P hP
    unfold Good
    intro J hJ
    have hz : IsZero (HP P J) := by
      rw [IsZero.iff_id_eq_zero]
      have h0 : (𝟙 P : P ⟶ P) = 0 :=
        NatTrans.ext (funext fun U => (hP U).eq_of_src _ _)
      rw [← hm_id, h0, hm_zero]
    have hz0 : IsZero ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
        (0 : SShv B q)) :=
      Functor.map_isZero _ (isZero_zero _)
    exact transfer (0 : SShv B q) (hz0.iso hz)
  · intro P P₁ P₂ i₁ r₁ i₂ r₂ h1 h2 h12 h21 ht hP₁ hP₂
    unfold Good at hP₁ hP₂ ⊢
    intro J hJ
    obtain ⟨g₁, hi₁⟩ := hP₁ J hJ
    obtain ⟨g₂, hi₂⟩ := hP₂ J hJ
    let S₁ : SShv B q := ⟨HP P₁ J, g₁⟩
    let S₂ : SShv B q := ⟨HP P₂ J, g₂⟩
    haveI : Injective S₁ := hi₁
    haveI : Injective S₂ := hi₂
    obtain ⟨e⟩ := biprod_iso (sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q))))
      S₁ S₂ (HP P J) (hm r₁ J) (hm i₁ J) (hm r₂ J) (hm i₂ J)
      (by rw [hm_comp, h1, hm_id]; rfl) (by rw [hm_comp, h2, hm_id]; rfl)
      (by rw [hm_comp, h21, hm_zero]) (by rw [hm_comp, h12, hm_zero])
      (by rw [hm_comp, hm_comp, ← hm_add, ht, hm_id])
    exact transfer (S₁ ⊞ S₂) e
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffineIsDomainPullbackStandardOpens
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

private lemma aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map (e.symm : S →+* R)) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hp' : p = (p.map (e.symm : S →+* R)).map (e : R →+* S) := by
    rw [Polynomial.map_map]
    ext n
    simp
  rw [hp', Polynomial.eval_map]
  change Polynomial.eval₂ (e : R →+* S) ((e : R →+* S) a) _ = 0
  rw [Polynomial.eval₂_at_apply, ha, map_zero]

private lemma aic_chart {Z U : Scheme.{0}} (hZ : AICSch Z) (ι : U ⟶ Z) [IsOpenImmersion ι] [IsAffine U] [Nonempty U] :
    AIC Γ(U, ⊤) := by
  have hA : IsAffineOpen (ι ''ᵁ ⊤) := (isAffineOpen_top U).image_of_isOpenImmersion ι
  have hN : ((ι ''ᵁ ⊤ : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨ι x, x, trivial, rfl⟩
  exact aic_of_equiv (ι.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ hA hN)

private lemma range_fst_eq {P Z U V : Scheme.{0}} (g : Z ⟶ P) (O O' : P.Opens) (τ : Γ(P, O))
    (hb : P.basicOpen τ = O ⊓ O') (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z)
    (r2 : Set.range ι₂ = (g ⁻¹ᵁ O' : Set Z)) (h : (⊤ : U.Opens) ≤ (ι₁ ≫ g) ⁻¹ᵁ O) {W : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V)
    (sq : IsPullback a b ι₁ ι₂) :
    Set.range a = (U.basicOpen (((ι₁ ≫ g).appLE O ⊤ h).hom τ) : Set U) := by
  have h1 : Set.range a = Set.range (pullback.fst ι₁ ι₂) := by
    rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ]
  rw [h1, Scheme.Pullback.range_fst, r2, Scheme.basicOpen_appLE, hb]
  ext x
  have hx : x ∈ (ι₁ ≫ g) ⁻¹ᵁ O := h trivial
  constructor
  · intro hx'
    exact ⟨trivial, hx, hx'⟩
  · rintro ⟨-, -, hx'⟩
    exact hx'

private lemma top_appLE {X Y P : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ P) (w : X ⟶ P) (e : f ≫ g = w) (O : P.Opens)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ O) (k : (⊤ : X.Opens) ≤ w ⁻¹ᵁ O) : g.appLE O ⊤ h ≫ f.appTop = w.appLE O ⊤ k := by
  subst e
  rw [← Scheme.Hom.appLE_comp_appLE f g O ⊤ ⊤ h le_top]
  congr 1
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  exact (Category.comp_id _).symm

private lemma ts_eq {P W U V : Scheme.{0}} (O O' : P.Opens) (τ : Γ(P, O)) (σ : Γ(P, O'))
    (hts : P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op τ * P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op σ = 1)
    (g₁ : U ⟶ P) (g₂ : V ⟶ P) (h₁ : (⊤ : U.Opens) ≤ g₁ ⁻¹ᵁ O) (h₂ : (⊤ : V.Opens) ≤ g₂ ⁻¹ᵁ O')
    (a : W ⟶ U) (b : W ⟶ V) (e : a ≫ g₁ = b ≫ g₂) :
    a.appTop.hom ((g₁.appLE O ⊤ h₁).hom τ) * b.appTop.hom ((g₂.appLE O' ⊤ h₂).hom σ) = 1 := by
  have k₁ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ O := fun x _ => h₁ (show a x ∈ (⊤ : U.Opens) from trivial)
  have k₂ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ O' := by
    rw [e]
    exact fun x _ => h₂ (show b x ∈ (⊤ : V.Opens) from trivial)
  have k₃ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ (O ⊓ O') := fun x hx => ⟨k₁ hx, k₂ hx⟩
  have e₁ := top_appLE a g₁ (a ≫ g₁) rfl O h₁ k₁
  have e₂ := top_appLE b g₂ (a ≫ g₁) e.symm O' h₂ k₂
  have l₁ : P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op ≫ (a ≫ g₁).appLE (O ⊓ O') ⊤ k₃ =
      (a ≫ g₁).appLE O ⊤ k₁ := Scheme.Hom.map_appLE _ _ _
  have l₂ : P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op ≫ (a ≫ g₁).appLE (O ⊓ O') ⊤ k₃ =
      (a ≫ g₁).appLE O' ⊤ k₂ := Scheme.Hom.map_appLE _ _ _
  change (g₁.appLE O ⊤ h₁ ≫ a.appTop).hom τ * (g₂.appLE O' ⊤ h₂ ≫ b.appTop).hom σ = 1
  rw [e₁, e₂, ← l₁, ← l₂]
  change ((a ≫ g₁).appLE (O ⊓ O') ⊤ k₃).hom (P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op |>.hom τ) *
    ((a ≫ g₁).appLE (O ⊓ O') ⊤ k₃).hom (P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op |>.hom σ) = 1
  rw [← map_mul, hts, map_one]

private lemma inj_of {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S] (φ : R →+* S) (t : R)
    (ht : IsUnit (φ t)) (ker : ∀ y, φ y = 0 → ∃ k : ℕ, t ^ k * y = 0) : Function.Injective φ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨k, hk⟩ := ker y hy
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero _ ht0)

theorem UpperTheory.isAffine_isDomain_pullback_standard_opens :
    ∀ (A : Type) [CommRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z) [IsOpenImmersion ι₁] [IsOpenImmersion ι₂] [IsAffine U] [IsAffine V],
      StdPair p ι₁ ι₂ → IsAffine (pullback ι₁ ι₂) ∧ (Nonempty ↥(pullback ι₁ ι₂) →
        letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p).appTop).hom).toAlgebra
        IsDomain Γ(pullback ι₁ ι₂, ⊤) ∧ Function.Injective (pullback.fst ι₁ ι₂).appTop.hom ∧ Function.Injective (pullback.snd ι₁ ι₂).appTop.hom ∧
        ∃ T : TC A Γ(pullback ι₁ ι₂, ⊤), T.Int ∧ Roots T.B ∧ Roots T.C ∧ (T.B : Set Γ(pullback ι₁ ι₂, ⊤)) = Set.range (pullback.fst ι₁ ι₂).appTop.hom ∧
          (T.C : Set Γ(pullback ι₁ ι₂, ⊤)) = Set.range (pullback.snd ι₁ ι₂).appTop.hom) := by
  intro A _ Z U V p hZ ι₁ ι₂ _ _ _ _ hstd
  obtain ⟨L, u, l, f, hu, -, hf, rfl, r1, r2⟩ := hstd
  obtain ⟨τ, σ, a0, a1, gτ, gσ, bτ, bσ, hts⟩ := UpperTheory.projectiveLine_std_opens_basicOpen_generators
  have h1 : (⊤ : U.Opens) ≤ (ι₁ ≫ u ≫ f) ⁻¹ᵁ stdOpen 0 := by
    intro x _
    have m : ι₁ x ∈ ((u ≫ f) ⁻¹ᵁ stdOpen 0 : Set Z) := r1 ▸ ⟨x, rfl⟩
    exact m
  have h2 : (⊤ : V.Opens) ≤ (ι₂ ≫ u ≫ f) ⁻¹ᵁ stdOpen 1 := by
    intro x _
    have m : ι₂ x ∈ ((u ≫ f) ⁻¹ᵁ stdOpen 1 : Set Z) := r2 ▸ ⟨x, rfl⟩
    exact m
  have sq : IsPullback (pullback.fst ι₁ ι₂) (pullback.snd ι₁ ι₂) ι₁ ι₂ := IsPullback.of_hasPullback ι₁ ι₂
  have ra := range_fst_eq (u ≫ f) _ _ τ bτ ι₁ ι₂ r2 h1 _ _ sq
  have rb := range_fst_eq (u ≫ f) (stdOpen 1) (stdOpen 0) σ (bσ.trans (inf_comm _ _)) ι₂ ι₁ r1 h2 _ _ sq.flip
  obtain ⟨aff, locA, kerA⟩ := UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen (pullback.fst ι₁ ι₂) _ ra
  obtain ⟨-, locB, kerB⟩ := UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen (pullback.snd ι₁ ι₂) _ rb
  refine ⟨aff, fun hne => ?_⟩
  letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom).toAlgebra
  haveI : IsIntegral Z := hZ.1
  haveI : Nonempty U := ⟨pullback.fst ι₁ ι₂ hne.some⟩
  haveI : Nonempty V := ⟨pullback.snd ι₁ ι₂ hne.some⟩
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion ι₁
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion ι₂
  haveI : IsIntegral (pullback ι₁ ι₂) := isIntegral_of_isOpenImmersion (pullback.fst ι₁ ι₂ ≫ ι₁)
  have ts := ts_eq (stdOpen 0) (stdOpen 1) τ σ hts _ _ h1 h2 (pullback.fst ι₁ ι₂) (pullback.snd ι₁ ι₂)
    (by rw [pullback.condition_assoc])
  have injA := inj_of _ _ (IsUnit.of_mul_eq_one _ ts) kerA
  have injB := inj_of _ _ (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans ts)) kerB
  refine ⟨inferInstance, injA, injB, ?_⟩
  exact UpperTheory.isIntegral_of_localization_cover_unit_product _ _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι₁ ≫ u ≫ l).appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι₂ ≫ u ≫ l).appTop).hom
    (by
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom
      rw [Scheme.Hom.comp_appTop (pullback.fst ι₁ ι₂)]
      rfl)
    (by
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom
      rw [pullback.condition_assoc, Scheme.Hom.comp_appTop (pullback.snd ι₁ ι₂)]
      rfl)
    injA injB _ _ ts locA locB (UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart A u l f hu hf _ a0 τ gτ ι₁ r1 h1) (UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart A u l f hu hf _ a1 σ gσ ι₂ r2 h2)
    (aic_chart hZ ι₁) (aic_chart hZ ι₂)

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartCoverOfIsCurve
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_tensor_lift {k L K M : Type} [Field k] [Field L] [Field K] [CommRing M] [Algebra k L] [Algebra k K]
    (f : L →+* M) (g : K →+* M) (h : ∀ r : k, f (algebraMap k L r) = g (algebraMap k K r)) :
    ∃ θ : L ⊗[k] K →+* M, ∀ l a, θ (l ⊗ₜ[k] a) = f l * g a := by
  letI : Algebra k M := (g.comp (algebraMap k K)).toAlgebra
  let f' : L →ₐ[k] M := { f with commutes' := fun r => h r }
  let g' : K →ₐ[k] M := { g with commutes' := fun r => rfl }
  exact ⟨(Algebra.TensorProduct.productMap f' g').toRingHom, fun l a => by simp [f', g']⟩

private theorem core (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]
    (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L)
    (hpb : IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [Algebra k C.functionField]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    {n : ℕ} (U : Fin n → C.Opens) (hUa : ∀ i, IsAffineOpen (U i)) [hne : ∀ i, Nonempty (U i)]
    (hUc : ∀ y : C, ∃ i, y ∈ U i) (hn : 0 < n)
    (B : Fin n → Subalgebra k C.functionField)
    (hB : ∀ i, (B i : Set C.functionField) = Set.range (C.germToFunctionField (U i)))
    (hfr : ∀ i, IsFractionRing (B i) C.functionField) :
    ∃ θ : L ⊗[k] C.functionField →+* X.functionField,
      Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c u x hpb
  obtain ⟨φ, hφgen, hφgerm⟩ := UpperTheory.exists_functionField_hom_germ_of_surjective u hsurj
  obtain ⟨f, hfk, hfx⟩ := UpperTheory.baseChange_functionField_hom_genericPoint_comp k L c u x hpb hK φ hφgen
  obtain ⟨θ, hθ⟩ := exists_tensor_lift f φ hfk
  have hne' : ∀ i, Nonempty (u ⁻¹ᵁ U i) := by
    intro i
    obtain ⟨⟨z, hz⟩⟩ := hne i
    obtain ⟨y, rfl⟩ := hsurj.surj z
    exact ⟨⟨y, hz⟩⟩
  have chart : ∀ i, IsAffineOpen (u ⁻¹ᵁ U i) ∧ ∃ e : L ⊗[k] B i ≃+* Γ(X, u ⁻¹ᵁ U i),
      ∀ s, θ (inc L (B i) s) = X.germToFunctionField (u ⁻¹ᵁ U i) (e s) := by
    intro i
    haveI := hne' i
    obtain ⟨hV, e, he1, he2⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c u x hpb hK (U i) (hUa i) (B i) (hB i)
    refine ⟨hV, e, fun s => ?_⟩
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul l b =>
      obtain ⟨a, ha⟩ : (b : C.functionField) ∈ Set.range (C.germToFunctionField (U i)) := by
        rw [← hB i]
        exact b.2
      have hsplit : l ⊗ₜ[k] b = (l ⊗ₜ[k] (1 : B i)) * ((1 : L) ⊗ₜ[k] b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [show inc L (B i) (l ⊗ₜ[k] b) = l ⊗ₜ[k] (b : C.functionField) from rfl, hθ, hsplit,
        map_mul, map_mul, he1 a b ha.symm, he2 l, hfx, ← hφgerm (U i) a, ha]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have hcomp : θ.comp Algebra.TensorProduct.includeRight.toRingHom = φ := by
    ext a
    simp [Algebra.TensorProduct.includeRight_apply, hθ]
  have hinj : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨hV0, e0, he0⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    obtain ⟨s, β, hβ, hs⟩ := UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator k L C.functionField (B ⟨0, hn⟩) (hfr _) t
    have h1 : θ (inc L (B ⟨0, hn⟩) s) = 0 := by rw [← hs, map_mul, ht, zero_mul]
    rw [he0] at h1
    have h2 : e0 s = 0 :=
      X.germToFunctionField_injective _ (h1.trans (map_zero _).symm)
    have h3 : s = 0 := e0.injective (h2.trans (map_zero e0).symm)
    rw [h3, map_zero] at hs
    have hβ' : (β : C.functionField) ≠ 0 := fun h => hβ (Subtype.ext h)
    have hu : IsUnit ((1 : L) ⊗ₜ[k] (β : C.functionField)) := by
      refine ⟨⟨1 ⊗ₜ[k] (β : C.functionField), 1 ⊗ₜ[k] (β : C.functionField)⁻¹, ?_, ?_⟩, rfl⟩
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hβ']
        rfl
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hβ']
        rfl
    exact hu.mul_left_eq_zero.mp hs
  refine ⟨θ, by rw [hcomp]; exact hφgen, hinj, ?_, ?_⟩
  · intro h
    obtain ⟨hV, e, he⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    haveI := functionField_isFractionRing_of_isAffineOpen X _ hV
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) h
    refine ⟨inc L (B ⟨0, hn⟩) (e.symm p), inc L (B ⟨0, hn⟩) (e.symm q), ?_, ?_⟩
    · intro h0
      have h4 := congrArg θ h0
      rw [he, map_zero, e.apply_symm_apply] at h4
      have h5 : (q : Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) = 0 :=
        X.germToFunctionField_injective _ (h4.trans (map_zero _).symm)
      exact nonZeroDivisors.coe_ne_zero q h5
    · rw [he, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hpq
  · intro y
    obtain ⟨i, hi⟩ := hUc (u y)
    haveI := hne' i
    obtain ⟨hV, e, he⟩ := chart i
    have hy : y ∈ u ⁻¹ᵁ U i := hi
    refine ⟨i, (hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap e.toRingHom, inferInstance, fun s hs => ?_⟩
    have hsP : e s ∉ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := hs
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
    haveI := hV.isLocalization_stalk ⟨y, hy⟩
    refine ⟨(IsLocalization.map_units (X.presheaf.stalk y)
      (⟨e s, hsP⟩ : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)).unit, ?_⟩
    rw [he]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hy (e s)

theorem UpperTheory.isFunctionField_and_chart_cover_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ ∃ (n : ℕ) (B : Fin n → Subalgebra k C.functionField), (∀ i, IsChart (B i)) ∧ ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L], ∃ (X : Scheme.{0}) (_ : IsIntegral X) (u : X ⟶ C) (x : X ⟶ Sp L) (θ : L ⊗[k] C.functionField →+* X.functionField), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧ (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) ∧ Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  intro k _ _ C _ c hcurve _ hK
  have hprop : IsProper c := hcurve.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨n, U, hUa, hUne, hn, hUc⟩ := UpperTheory.exists_finite_nonempty_affine_cover_of_integral C
  haveI : ∀ i, Nonempty (U i) := hUne
  have hex : ∀ i, ∃ B : Subalgebra k C.functionField,
      (B : Set C.functionField) = Set.range (C.germToFunctionField (U i)) :=
    fun i => UpperTheory.exists_subalgebra_eq_range_germToFunctionField k c hK (U i)
  choose B hB using hex
  have hchart : ∀ i, IsChart (B i) :=
    fun i => UpperTheory.isChart_affine_sections_of_isCurve k c hcurve hK (U i) (hUa i) (B i) (hB i)
  refine ⟨UpperTheory.isFunctionField_of_dedekind_finiteType_fractionRing k C.functionField (B ⟨0, hn⟩) (hchart _).2.1 (hchart _).1
    (hchart _).2.2.1 (hchart _).2.2.2.1, n, B, hchart, ?_⟩
  intro L _ _ _
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hpb : IsPullback (pullback.fst c g) (pullback.snd c g) c g := IsPullback.of_hasPullback c g
  have hcurve' := UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hcurve
  haveI hXint : IsIntegral (pullback c g) := hcurve'.1
  have hstalk := (UpperTheory.isDedekindDomain_affine_sections_of_isCurve L (pullback.snd c g) hcurve').2
  obtain ⟨θ, h1, h2, h3, h4⟩ := core k L c (pullback.fst c g) (pullback.snd c g) hpb hK U hUa hUc hn
    B hB (fun i => (hchart i).2.2.2.1)
  exact ⟨pullback c g, hXint, pullback.fst c g, pullback.snd c g, θ, hpb, hstalk, h1, h2, h3, h4⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LeafH0Holds
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private theorem tw_q_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) : q • a = 0 := by
  have h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]

private theorem tw_nsmul_mod {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) (n : ℕ) :
    n • a = (n % q) • a := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_smul, mul_smul, tw_q_nsmul, add_zero]

private theorem mod_eq_of_nsmul_eq {q : ℕ} [NeZero q] {i : ℤ} {U : Scheme.{0}} [Nonempty U]
    (ζ : Prim q Γ(U, ⊤)) {c c' : ℕ} (h : c • twGen i ζ = c' • twGen i ζ) : c % q = c' % q := by
  have key : ∀ {c c' : ℕ}, c ≤ c' → c • twGen i ζ = c' • twGen i ζ → c % q = c' % q := by
    intro c c' hle h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [add_nsmul] at h
    have h0 : d • twGen i ζ = 0 := by
      have h' := h.symm
      rwa [add_eq_left] at h'
    obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ d h0
    rw [Nat.add_mul_mod_self_left]
  rcases le_total c c' with hle | hle
  · exact key hle h
  · exact (key hle h.symm).symm

private theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem exists_prim (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω)) :
    Nonempty (Prim q Ω) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (Polynomial.degree_cyclotomic_pos q Ω (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem UpperTheory.leafH0_holds :
    LateralTheory.E.E4.H0TwistOverClosedField := by
  intro hyp q _ Ω _ _ hq i
  obtain ⟨-, e, he, -⟩ := hyp.2.2.2.2.2.2.2.1 (ZMod q) (tw q i)
  obtain ⟨ζ0⟩ := exists_prim q Ω hq
  let ζ : Prim q Γ(Sp Ω, ⊤) :=
    Prim.map (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv) ζ0
  have hsec : ∀ {X : Scheme.{0}} [ConnectedSpace X] (ξ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X),
      ∃ c < q, y = c • twGen i ξ := by
    intro X _ ξ y
    obtain ⟨c, rfl⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q i X ξ y
    exact ⟨c % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q)), tw_nsmul_mod _ c⟩
  refine ⟨?_, ?_⟩
  · have hsurj : Function.Surjective (fun k : Fin q => e (Sp Ω) ((k : ℕ) • twGen i ζ)) := by
      intro x
      obtain ⟨c, hc, hy⟩ := hsec ζ ((e (Sp Ω)).symm x)
      refine ⟨⟨c, hc⟩, ?_⟩
      show e (Sp Ω) (c • twGen i ζ) = x
      rw [← hy, AddEquiv.apply_symm_apply]
    exact Finite.of_surjective _ hsurj
  · intro X _ c
    have hcomm : ∀ s, pl q i c 0 (e (Sp Ω) s) = e X (Sec.res c s) := fun s => he c s
    have hres : Function.Bijective (Sec.res (F := tw q i) c) := by
      have ht : Sec.res c (twGen i ζ) =
          twGen i (Prim.map (CommRingCat.Hom.hom (Scheme.Hom.appTop c)) ζ) :=
        (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 X (Sp Ω) c ζ
      constructor
      · intro s s' hss
        obtain ⟨c1, -, rfl⟩ := hsec ζ s
        obtain ⟨c2, -, rfl⟩ := hsec ζ s'
        rw [res_nsmul, res_nsmul, ht] at hss
        have hm := mod_eq_of_nsmul_eq _ hss
        rw [tw_nsmul_mod _ c1, tw_nsmul_mod _ c2, hm]
      · intro y
        obtain ⟨c1, -, rfl⟩ := hsec (Prim.map (CommRingCat.Hom.hom (Scheme.Hom.appTop c)) ζ) y
        exact ⟨c1 • twGen i ζ, by rw [res_nsmul, ht]⟩
    have hfun : (pl q i c 0 : _ → _) = (e X) ∘ Sec.res c ∘ (e (Sp Ω)).symm := by
      funext x
      simp only [Function.comp]
      rw [← hcomm, AddEquiv.apply_symm_apply]
    rw [hfun]
    exact (e X).bijective.comp (hres.comp (e (Sp Ω)).symm.bijective)
end

