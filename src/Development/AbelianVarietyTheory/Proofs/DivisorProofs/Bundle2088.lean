module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg

theorem affineFromSpec_comp_eq_specMap_cst {R : Type} [CommRing R] {W : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    V.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (cst f V.1)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) V.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

theorem comap_idealSheaf_pow_eq {X Y : Scheme.{0}} (g : Y ⟶ X) (K : X.IdealSheafData) (k : ℕ) :
    (K ^ k).comap g = (K.comap g) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Scheme.IdealSheafData.comap_top g
  | succ n ih =>
    rw [pow_succ, pow_succ, GlobalTheory.Principalise.comap_mul_idealSheaf, ih]

theorem isIso_pullbackSnd_restrict_preimage {X Y S : Scheme.{0}} (π : X ⟶ S) (g : Y ⟶ S) (U : S.Opens)
    (h : IsIso (π ∣_ U)) : IsIso (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) := by
  have hEq : pullback.fst π g ⁻¹ᵁ π ⁻¹ᵁ U = pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U := by
    show (pullback.fst π g ≫ π) ⁻¹ᵁ U = (pullback.snd π g ≫ g) ⁻¹ᵁ U
    rw [pullback.condition]
  have L : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U).ι (π ⁻¹ᵁ U).ι (pullback.fst π g) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by simpa only [Scheme.Opens.opensRange_ι] using hEq)
  have s := L.paste_vert (IsPullback.of_hasPullback π g)
  have key : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) (π ∣_ U) (g ∣_ U) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_morphismRestrict g U)
    · rw [morphismRestrict_ι, morphismRestrict_ι]
      exact s
    · rw [← cancel_mono U.ι]
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
        Scheme.Hom.resLE_comp_ι_assoc, pullback.condition]
  exact key.isIso_snd_of_isIso h

theorem ideal_eq_of_reduces_affine : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t →
    ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) →
    ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  intro R _ I W W' _ f π U hπ hU K hK t ht V
  obtain ⟨hbc, hbs, -⟩ := _root_.GlobalTheory.FormalAlg.baseIdeal_calculus
  obtain ⟨hbC, hloc⟩ := _root_.GlobalTheory.FormalAlg.specIdeal
  haveI : IsNoetherianRing Γ(W, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨C, _, φ, hCn, hφ, hC, hfaith⟩ := _root_.GlobalTheory.AdicPackage.adicCompletion_package Γ(W, V.1) (I.map (cst f V.1))
  haveI := hCn
  haveI := hπ
  have hJjac : (I.map (cst f V.1)).map φ ≤ Ideal.jacobson ⊥ := by
    haveI := hC
    exact IsAdicComplete.le_jacobson_bot _
  haveI hφF : Flat (Spec.map (CommRingCat.ofHom φ)) := AlgebraicGeometry.Flat.SpecMap_iff.mpr hφ
  have hOF : Flat V.2.fromSpec :=
    @HasRingHomProperty.of_isOpenImmersion @Flat RingHom.Flat _ _ _ _ RingHom.Flat.containsIdentities
      V.2.isOpenImmersion_fromSpec
  have hgF : Flat (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) :=
    MorphismProperty.comp_mem @Flat _ _ hφF hOF
  have F1 : ∀ X : W.IdealSheafData, X.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((X.ideal V).map φ) := fun X => hloc W V C φ X
  have F2 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).ideal V = (I.map (cst f V.1)) ^ (e + 1) := by
    intro e
    rw [baseIdeal_ideal, Ideal.map_pow]
  have F4 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, F2, Ideal.map_pow]
  have F5 : ∀ e : ℕ, ((t e).ideal V).map φ = ((t (e + 1)).ideal V).map φ ⊔ ((I.map (cst f V.1)).map φ) ^ (e + 1) := by
    intro e
    conv_lhs => rw [ht e]
    rw [← Ideal.map_pow, ← F2 e, ← Ideal.map_sup]
    rfl
  have F6 := _root_.GlobalTheory.iInf_sup_pow_eq_of_compatible C ((I.map (cst f V.1)).map φ) hC (fun e => ((t e).ideal V).map φ) F5
  have F7 : ∀ e : ℕ, (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, ← (hbC C).2, F6 e]
  have F8 : ∀ e : ℕ, (baseIdeal (π ≫ f) (I ^ (e + 1))).comap
      (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) =
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    have hgf : (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ≫ f =
        Spec.map (CommRingCat.ofHom (φ.comp (cst f V.1))) := by
      rw [Category.assoc, affineFromSpec_comp_eq_specMap_cst, ← Spec.map_comp]
      rfl
    rw [hbc, ← Category.assoc, pullback.condition, Category.assoc, hgf, hbs, ← Ideal.map_map,
      Ideal.map_pow, Ideal.map_pow]
  have hKC : ∀ x, x ∉ (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)).support →
      x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U := by
    intro x hx
    refine hK _ (fun h => hx ?_)
    rw [Scheme.IdealSheafData.support_comap]
    exact h
  have hπC : IsProper (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := inferInstance
  obtain ⟨k₀, hk₀⟩ := _root_.GlobalTheory.FormalAlg.map_inf_eq_of_reductions C ((I.map (cst f V.1)).map φ) hJjac _
    (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) _ hπC
    (isIso_pullbackSnd_restrict_preimage π _ U hU) _
    (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ)) hKC
  refine ⟨k₀, fun k hk T' T'' hT' hT'' e => ?_⟩
  have h1 : ∀ e : ℕ, T'.comap (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ⊔
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1))).comap
        (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := by
    intro e
    have hT'e : T' ⊔ baseIdeal (π ≫ f) (I ^ (e + 1)) = (t e).comap π := hT' e
    rw [← F8 e, ← Scheme.IdealSheafData.comap_sup, hT'e, ← F7 e,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, pullback.condition]
  have h2 : ∀ e : ℕ, T''.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⊔
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) ⊔
        (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ^ k := by
    intro e
    have hT''e : T'' ⊔ baseIdeal f (I ^ (e + 1)) = t e ⊔ K ^ k := hT'' e
    rw [← F4 e, ← Scheme.IdealSheafData.comap_sup, hT''e, Scheme.IdealSheafData.comap_sup, F7 e,
      comap_idealSheaf_pow_eq, F4 e]
  have hmain := hk₀ k hk _ _ h1 h2
  have hX : ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).comap
      (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) := by
    rw [Scheme.IdealSheafData.comap_sup, _root_.GlobalTheory.FlatInf.comap_inf_of_flat _ _ _ hgF,
      _root_.GlobalTheory.FlatBaseChangeIdeal.map_comap_flat W W' _ _ π _ (pullback.fst π _) (pullback.snd π _) (IsPullback.of_hasPullback π _) hgF
        inferInstance, hmain, F4 e, F7 e]
  rw [F1, F1] at hX
  have hX' := (hbC C).1.1 hX
  have hle1 : (I.map (cst f V.1)) ^ (e + 1) ≤ ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp le_sup_right V
  have hle2 : (I.map (cst f V.1)) ^ (e + 1) ≤ (t e).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp (ht.baseIdeal_le e) V
  calc ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V
      = ((((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V).map φ).comap φ := (hfaith _ _ hle1).symm
    _ = ((((t e).ideal V)).map φ).comap φ := by rw [hX']
    _ = (t e).ideal V := hfaith _ _ hle2

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureGaloisFiniteAutGroupInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem integralClosure_galois_finite_invariants :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L], letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra; Module.Finite A (integralClosure A L) ∧ Finite (integralClosure A L ≃ₐ[A] integralClosure A L) ∧ Function.Injective (algebraMap A (integralClosure A L)) ∧ ∀ b : integralClosure A L, (∀ σ : integralClosure A L ≃ₐ[A] integralClosure A L, σ b = b) → b ∈ Set.range (algebraMap A (integralClosure A L)) := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable K L := inferInstance
  refine ⟨IsIntegralClosure.finite A K L (integralClosure A L), ?_, ?_, ?_⟩
  · exact Finite.of_equiv _ (galRestrict A K L (integralClosure A L)).toEquiv
  · intro x y h
    have h' := congrArg (algebraMap (integralClosure A L) L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h'
    exact IsFractionRing.injective A K ((algebraMap K L).injective h')
  · intro b hb
    haveI : IsFractionRing (integralClosure A L) L :=
      integralClosure.isFractionRing_of_finite_extension K L
    have := Algebra.isInvariant_of_isGalois' A K L (integralClosure A L)
    exact this.isInvariant b hb

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.ModelFrameCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isCombAtG_push {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f : S₁ ⟶ S₀} (mm : SABMap t' t f)
    {R : Type} [CommRing R] (x : Sp R ⟶ S₁) {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} {a : Fin n → R}
    {w : Sp (DualNumber R) ⟶ t'.G.left} (h : IsCombAtG t' x v a w) :
    IsCombAtG t (x ≫ f) (fun i => v i ≫ mm.φ) a (w ≫ mm.φ) := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv mm.cart
    (spMap (algebraMap R (DualNumber R)) ≫ x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _)
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨fun i => B (u i), fun i => ?_, ?_⟩
  · rw [hB, hu, Category.assoc]
  · have e : B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [← e, hB, hw]

theorem isCombAtG_reflect {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f : S₁ ⟶ S₀} (mm : SABMap t' t f)
    {R : Type} [CommRing R] (x : Sp R ⟶ S₁) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left))
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) {a : Fin n → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t (x ≫ f) (fun i => v i ≫ mm.φ) a w) :
    ∃ w' : Sp (DualNumber R) ⟶ t'.G.left, w' ≫ mm.φ = w ∧ IsCombAtG t' x v a w' := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv mm.cart
    (spMap (algebraMap R (DualNumber R)) ≫ x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _)
  obtain ⟨u, hu, hw⟩ := h
  have hBs : ∀ z, (B.symm z).left ≫ mm.φ = z.left := fun z => by rw [← hB, B.apply_symm_apply]
  refine ⟨(B.symm (List.ofFn u).prod).left, by rw [hBs, hw], fun i => B.symm (u i), fun i => ?_, ?_⟩
  · refine mm.cart.1.hom_ext ?_ ?_
    · rw [hBs, hu, Category.assoc]
    · rw [Over.w (B.symm (u i)), Category.assoc, hv, ← Category.assoc, GlobalTheory.Exist.FlagBaseChange.epsMul_over]
      rfl
  · rw [map_list_prod, List.map_ofFn]
    rfl

theorem exists_sabMap_congr {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f f' : S₁ ⟶ S₀} (mm : SABMap t' t f)
    (h : f = f') : ∃ mm' : SABMap t' t f', mm'.φ = mm.φ := by
  subst h
  exact ⟨mm, rfl⟩

end GlobalTheory.ModelFrameCompare

namespace GlobalTheory.ModelFrameCompare


set_option maxHeartbeats 1000000 in
theorem images_eigenBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (σ : E →+* ℂ) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (xV : Sp T.V ⟶ Y.X) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ xV → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ v : Fin (Dw.mult σ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left), (∀ j, IsTanAtG Y.t xV (v j)) ∧ (∀ u : Sp (DualNumber T.V) ⟶ Y.t.G.left, IsTanAtG Y.t xV u → (∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) → u ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u) → ∃ cf : Fin (Dw.mult σ) → T.V, IsCombAtG Y.t xV v cf u) ∧ ∀ (cf : Fin (Dw.mult σ) → T.V) (u : Sp (DualNumber T.V) ⟶ Y.t.G.left) (w : Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left), IsCombAtG Y.t xV v cf u → w ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u → (letI := io.toAlgebra; IsCombAt y₀.1.x (y₀.1.u σ) (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ ν.φ)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν σ T io y₀ xV yy hxV hpt
  let _ := io.toAlgebra
  obtain ⟨G₂, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull xV Y.t
  obtain ⟨t₂, n₀, n₂, m', -, h2⟩ := GlobalTheory.ThetaFrameCheck.genFibre_tied Xo' c' T _ _ Y xV yy hxV G₂ m
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t t₂ _ yy ν m'
  obtain ⟨G, t', m1, m2, ⟨ub, ht, he, hb, hl⟩, -⟩ := y₀.2.2
  have hx : y₀.1.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hpt]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨m1', hm1'⟩ := exists_sabMap_congr m1 hx
  obtain ⟨k, n, hk1, hk2⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr _ G G₂ t' t₂ m1' m2 n₁ n₂
  obtain ⟨nm, hnm⟩ := sabComp pullCubComp E H _ _ _ Y.t G₂ G xV (𝟙 _) m n
  obtain ⟨q₀, hq₀⟩ := exists_sabMap_congr nm (Category.id_comp xV)
  rw [hnm] at hq₀
  obtain ⟨B, hB, hBt, hBe, hBc⟩ := GlobalTheory.FactorDepth.Extension.exists_tanEquiv q₀
  refine ⟨fun j => (B (ub σ j)).left, fun j => (hBt _).2 (ht σ j), ?_, ?_⟩
  · intro u hu hue
    obtain ⟨w', hw'⟩ := B.surjective (ovT hu)
    have e : u = (B w').left := by rw [hw']; rfl
    subst e
    obtain ⟨cf, hcf, -⟩ := hb σ w' ((hBt _).1 hu) fun a z hz => (hBe _ a z).1 (hue a z hz)
    exact ⟨cf, (hBc _ _ cf w').2 hcf⟩
  · intro cf u w hc hw
    have h3 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) hc
    obtain ⟨q, hq⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t₂ _ yy Y.m m'
    choose u' hu1 hu2 using hl σ
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub σ j), spMap_comp',
        ← dualMap_comp_alg, ← spMap_comp']
      rfl
    have hov' : ∀ j, (u' j ≫ k.φ) ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
      intro j
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, hov]
    have hvec : ∀ j, spMap (dualMap (algebraMap T.V T.Fr)) ≫ (B (ub σ j)).left = (u' j ≫ k.φ) ≫ q.φ := by
      intro j
      rw [hB, hq₀, hq, ← Category.assoc, ← hu2, Category.assoc, ← Category.assoc m2.φ, hk2]
      simp only [Category.assoc, h2]
    have hpt' : spMap (algebraMap T.V T.Fr) ≫ xV = 𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _ := by
      rw [Category.id_comp, ← hxV]; rfl
    have h4 : IsCombAtG Y.t (𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _) (fun j => (u' j ≫ k.φ) ≫ q.φ)
        (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ Y.m.φ) := by
      rw [← hpt', hw]
      simpa only [hvec] using h3
    obtain ⟨w₂, hw₂, hc₂⟩ := isCombAtG_reflect q (𝟙 _) (fun j => u' j ≫ k.φ) hov' h4
    have hw₂' : w₂ ≫ m'.φ = w := by
      refine Y.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, ← hq, hw₂]
      · have := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
        have hmono : Mono Y.j := inferInstance
        have e2 : w₂ ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
          obtain ⟨uu, -, hh⟩ := hc₂
          rw [← hh]; exact Over.w _
        have e1 : u ≫ Y.t.G.hom = spMap (algebraMap T.V (DualNumber T.V)) ≫ xV := by
          obtain ⟨uu, -, hh⟩ := hc
          rw [← hh]; exact Over.w _
        rw [Category.assoc, m'.cart.1.w, ← Category.assoc, e2, Category.comp_id]
        apply hmono.right_cancellation
        have e3 : spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) ≫ xV =
            spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ yy ≫ Y.j := by
          rw [← Category.assoc, spMap_comp', dualMap_comp_alg, ← spMap_comp', Category.assoc, hxV]
        show (spMap _ ≫ yy) ≫ Y.j = w ≫ Y.oF.t.G.hom ≫ Y.jQ ≫ pullback.fst _ _
        rw [← Y.m.cart.1.w, ← Category.assoc w, hw, Category.assoc (spMap _) u, e1, e3, Category.assoc]
    have h5 := isCombAtG_push n₁ (𝟙 _) hc₂
    have hv5 : (fun j => (u' j ≫ k.φ) ≫ n₁.φ) = y₀.1.u σ := by
      funext j
      rw [Category.assoc, hk1, hm1', hu1]
    rw [hv5, hn₁, ← Category.assoc w₂, hw₂', Category.id_comp, ← hx] at h5
    exact h5

end GlobalTheory.ModelFrameCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSwapOfDoubleSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Dbl

theorem interPoly_rename_swap : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (gr : κ → Y.Dv) (D₁ D₂ : κ → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ a → x ≠ b → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ a) + toPic (D₁ b) = toPic (D₂ a) + toPic (D₂ b) ∧ toPic Θ = toPic (D₂ b) - toPic (D₁ a) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ → ∀ Q : MvPolynomial κ ℝ, Y.interPoly gr (rename (Equiv.swap a b) Q) = - Y.interPoly gr Q := by
  intro F _ Y W hW κ a b hab gr D₁ D₂ Θ ⟨h₁, h₂, hx, hsum, hΘ, hE, hS⟩
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.T.exists_intersectionForm_picard_doubleSpace F Y W hW
  obtain ⟨μ, hμ, hc⟩ := GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section F Y W hW Θ hE hS
  let N : AddSubgroup (CartierDiv W.Z) := (toPic (X := W.Z)).ker
  let π : CartierDiv W.Z →+ CartierDiv W.Z ⧸ N := QuotientAddGroup.mk' N
  let φ : (CartierDiv W.Z ⧸ N) →+ Pic W.Z := QuotientAddGroup.kerLift toPic
  have hφ : Function.Injective φ := QuotientAddGroup.kerLift_injective _
  have hπ (D : CartierDiv W.Z) : φ (π D) = toPic D := rfl
  let T' : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (Y.dim + 1) => CartierDiv W.Z ⧸ N) ℤ :=
    T.compLinearMap fun _ => φ.toIntLinearMap
  have hT' (y : Fin (Y.dim + 1) → CartierDiv W.Z) : T' (fun i => π (y i)) = W.num y := hT y
  refine _root_.GlobalTheory.FlagPush.MultiLevel.antisymm_of_multilinear κ a b hab (CartierDiv W.Z ⧸ N) Y.dim T' (fun σ y => hTs σ fun i => φ (y i))
    (fun x => π (D₁ x)) (fun x => π (D₂ x))
    (Y.interPoly gr) μ hμ (fun x ha hb => hφ (hx x ha hb)) (hφ ?_) (fun s => ?_) (fun s => ?_)
    (fun k P hP hk => GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim F Y κ gr k P hP hk) (fun s => ?_)
  · simpa only [map_add (f := _), hπ] using hsum
  · exact (hT' (fun i => D₁ (s i))).trans
      (_root_.GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull F Y W hW W.p₁ _ (fun i => gr (s i)) fun i => h₁ (s i))
  · exact (hT' (fun i => D₂ (s i))).trans
      (_root_.GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull F Y W hW W.p₂ _ (fun i => gr (s i)) fun i => h₂ (s i))
  · have hΘ' : π (D₂ b) - π (D₁ a) = π Θ := hφ (by simp only [map_sub, hπ, hΘ])
    have e : (Fin.cons (π (D₂ b) - π (D₁ a))
        (Sum.elim (fun x => π (D₁ x)) (fun x => π (D₂ x)) ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z ⧸ N) =
        fun i => π ((Fin.cons Θ (Sum.elim D₁ D₂ ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z) i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero, hΘ']
      · simp only [Fin.cons_succ, Function.comp_apply]
        cases s j <;> rfl
    have r := GlobalTheory.T.doubleSpace_section_intersectionNumber_eq_base F Y W (Sum.elim D₁ D₂ ∘ s) (gr ∘ fun i => Sum.elim id id (s i)) fun i => by
      simp only [Function.comp_apply]
      cases s i with
      | inl x => exact Or.inl (h₁ x)
      | inr x => exact Or.inr (h₂ x)
    rw [e, hT', hc, r, Var.interPoly_prod]
    push_cast
    rfl

end GlobalTheory.FlagPush.Dbl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_apply_constant_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ O r, dd O (constFn G.hom O r) = 0 := by
  first | exact @GlobalTheory.Heat.isInv_constFn | exact GlobalTheory.Heat.isInv_constFn | (intros; apply GlobalTheory.Heat.isInv_constFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def IsFactorAH (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧
    ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)

theorem isFactorAH_of_isAH {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) : IsFactorAH u Hm χ :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem isAH_of_isFactorAH {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : IsFactorAH u Hm χ) (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) : u.IsAH Hm χ :=
  ⟨h.1, pos, h.2.1, h.2.2⟩

end GlobalTheory.TorusRM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAddInfPreimageSubGrpSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_add_inf_preimage_sub_grpScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens), IsAffineOpen V → ∀ (T : Over (Sp R)) [IsAffine T.left] (a : T ⟶ A), IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub | exact GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub | (intros; apply GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub <;> assumption)
end

