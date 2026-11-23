module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0531
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionOfCohomologyDerivativeRelation
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_obRel_of_dRel : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w → (∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = 0) → ∃ (m : ℕ) (u v : Fin m → Glob1 F), ObRel F x u v := by
  intro R _ C _ F hF h0 x n y w hD hy
  obtain ⟨N, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl2⟩ := _root_.GlobalTheory.AbCoh.frame_coord R C F h0 N Φ
  obtain ⟨f, g, ω, hf, hg, hfD⟩ := hD
  have hcl : ∀ i, ∃ b : C0 F, d0 F b = (∑ k, l i (w k) • g k).1 := fun i ↦ by
    refine H1.mk_eq_zero.1 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hg]
    exact hy (l i)
  choose b hb using hcl
  have hb' : ∀ i ⦃T T' : C⦄ (φ : T ⟶ T'),
      b i T' - mp F φ (b i T) = ∑ k, l i (w k) • (g k).1 T T' φ := fun i T T' φ ↦ by
    have := congrFun (congrFun (congrFun (hb i) T) T') φ
    rw [amitsur_d0_apply] at this
    rw [this, Submodule.coe_sum]
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  have hw : ∀ k (T : C), (w k).1 T = ∑ i, l i (w k) • (Φ.w i).1 T := fun k T ↦ by
    have := congrArg (fun v : Glob1 F ↦ v.1 T) (hl2 (w k))
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hsum : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ∑ k, (g k).1 T T' φ • (w k).1 T' =
      ∑ i, (b i T' - mp F φ (b i T)) • (Φ.w i).1 T' := fun T T' φ ↦ by
    simp only [hb', hw, Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_comm, smul_assoc]
  let ω' : A0 F := fun T ↦ ω T + ∑ i, b i T • (Φ.w i).1 T
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω' T' = p1 F φ (ω' T) + D R (F.obj T') (f.1 T T' φ) := by
    intro T T' φ
    rw [hfD φ, hsum φ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ω', map_add (f := _), map_sum, oneFormsMapOfFunctorMorphism_smul, ← (Φ.w _).2 φ, sub_smul, Finset.sum_sub_distrib]
    abel
  have hglob : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'),
      dOne R (F.obj T') (ω' T') = pOm F 2 φ (dOne R (F.obj T) (ω' T)) := by
    intro T T' φ
    rw [hconn φ, map_add (f := _), dOne_D, add_zero, pOm_dOne]
  obtain ⟨m, u, v, hζ⟩ := _root_.GlobalTheory.AbCoh.twoForm_eq_wsum R C F ⟨N, ⟨Φ⟩⟩ h0 (fun T ↦ dOne R (F.obj T) (ω' T)) hglob
  exact ⟨m, u, v, f, ω', hf, hconn, fun T ↦ congrFun hζ T⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgCl
section
open IsLocalRing

namespace GlobalTheory.DvrFinExt

theorem exists_finite_intermediateField (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F Ω]
    [Algebra.IsIntegral F Ω] [Algebra K Ω] (hQ : ∀ q : F, algebraMap F Ω q ∈ (algebraMap K Ω).range)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* Ω) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ ∀ a, y₀ a ∈ L := by
  have hb : Function.Bijective (algebraMap K Ω).rangeRestrict :=
    ⟨(algebraMap K Ω).rangeRestrict.injective, (algebraMap K Ω).rangeRestrict_surjective⟩
  let e := RingEquiv.ofBijective _ hb
  let u : F →+* K := e.symm.toRingHom.comp ((algebraMap F Ω).codRestrict _ hQ)
  have hu : (algebraMap K Ω).comp u = (RingHom.id Ω).comp (algebraMap F Ω) := by
    ext q
    have h := e.apply_symm_apply ((algebraMap F Ω).codRestrict _ hQ q)
    exact congrArg Subtype.val h
  have hint : ∀ x : Ω, IsIntegral K x := fun x =>
    IsIntegral.map_of_comp_eq u (RingHom.id Ω) hu (Algebra.IsIntegral.isIntegral (R := F) x)
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  haveI : Finite (y₀ '' (s : Set R)) := (s.finite_toSet.image y₀).to_subtype
  refine ⟨IntermediateField.adjoin K (y₀ '' (s : Set R)),
    IntermediateField.finiteDimensional_adjoin (fun x _ => hint x), fun a => ?_⟩
  have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  | algebraMap n => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W) (fV : V →+* W) (fK : FractionRing V →+* FractionRing W) (κ' : FractionRing W →+* PadicAlgCl p), Function.Injective fV ∧ IsLocalHom fV ∧ fV.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (fV a)) ∧ κ'.comp fK = κ ∧ (∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ ∀ a, y₀ a ∈ κ'.range := by
  intro p _ V _ _ _ _ hc κ hκ hQ R _ _ y₀
  letI : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  obtain ⟨L, hL, hy⟩ := exists_finite_intermediateField ℚ_[p] (FractionRing V) (PadicAlgCl p) hQ R y₀
  obtain ⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  let e := FractionRing.algEquiv W L
  let κ' : FractionRing W →+* PadicAlgCl p := L.val.toRingHom.comp e.toRingEquiv.toRingHom
  let fK : FractionRing V →+* FractionRing W :=
    e.symm.toRingEquiv.toRingHom.comp (algebraMap (FractionRing V) L)
  have hfK : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (algebraMap V W a) := by
    intro a
    apply e.injective
    rw [e.commutes]
    have h := congrArg (fun g : V →+* L => g a) hcomp
    exact (e.apply_symm_apply _).trans h.symm
  have hκ' : κ'.comp fK = κ := by
    refine RingHom.ext fun x => ?_
    show ((e (e.symm (algebraMap (FractionRing V) L x)) : L) : PadicAlgCl p) = κ x
    rw [e.apply_symm_apply]
    rfl
  haveI : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcW, inferInstance, algebraMap V W, fK, κ', hinj, hloc,
    RingHom.finite_algebraMap.2 hfin, hfK, hκ', GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ κ' (fun v => ?_) hκ,
    fun a => ⟨e.symm ⟨y₀ a, hy a⟩, ?_⟩⟩
  · rw [← hfK]
    exact congrArg (fun g : FractionRing V →+* PadicAlgCl p => g (algebraMap V (FractionRing V) v)) hκ'
  · show ((e (e.symm ⟨y₀ a, hy a⟩) : L) : PadicAlgCl p) = y₀ a
    rw [e.apply_symm_apply]

end GlobalTheory.DvrFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctional
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_vectorField_of_functional : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ l : Glob1 F →ₗ[R] R, ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T, (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧ ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  intro R _ C _ F hF h0 l
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨c, hc, hsum⟩ := _root_.GlobalTheory.AbCoh.frame_coord R C F h0 n Φ
  refine ⟨fun T ↦ ∑ i, algebraMap R (F.obj T) (l (Φ.w i)) • Φ.δ i T, ?_, ?_⟩
  · intro T T' φ ω
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul,
      AlgHom.commutes, Φ.nat]
  · intro w T
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hc, ← map_mul, ← map_sum]
    have hw : l w = l (∑ i, c i w • Φ.w i) := congrArg l (hsum w)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sum]
    simp [mul_comm]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueToLocallyDirectedColimitOfBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.ColimitGlue


set_option backward.isDefEq.respectTransparency false in
theorem exists_glue {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0})
    [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected]
    (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ G U → x ∈ G V → ∃ W ∈ 𝒰, x ∈ G W ∧ W ≤ U ∧ W ≤ V)
    (hc : ∀ x : X, ∃ U ∈ 𝒰, x ∈ G U)
    (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U)
    (hnat : ∀ {U V : 𝒰} (h : U.1 ≤ V.1),
      X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) :
    ∃ j : X ⟶ colimit F, ∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U := by
  have hcov : TopologicalSpace.IsOpenCover (fun U : 𝒰 ↦ G U.1) :=
    eq_top_iff.2 fun x _ =>
      TopologicalSpace.Opens.mem_iSup.2 (by obtain ⟨U, hU, hx⟩ := hc x; exact ⟨⟨U, hU⟩, hx⟩)
  let 𝒱 : X.OpenCover := X.openCoverOfIsOpenCover (fun U : 𝒰 ↦ G U.1) hcov
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f U) (𝒱.f V) x).1 = (pullback.snd (𝒱.f U) (𝒱.f V) x).1 :=
      congr($(pullback.condition (f := 𝒱.f U) (g := 𝒱.f V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (pullback.fst (𝒱.f U) (𝒱.f V) x).2
      (hx ▸ (pullback.snd (𝒱.f U) (𝒱.f V) x).2)
    let α : (G W).toScheme ⟶ pullback (𝒱.f U) (𝒱.f V) :=
      pullback.lift (X.homOfLE (hG h1)) (X.homOfLE (hG h2))
        ((X.homOfLE_ι (hG h1)).trans (X.homOfLE_ι (hG h2)).symm)
    have hα1 : α ≫ pullback.fst _ _ = X.homOfLE (hG h1) := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = X.homOfLE (hG h2) := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; infer_instance
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    refine ⟨α.opensRange, ⟨⟨_, hxW⟩, ?_⟩, ?_⟩
    · apply (pullback.fst (𝒱.f U) (𝒱.f V)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      rw [reassoc_of% hα1, reassoc_of% hα2, reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) h1),
        reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) h2), colimit.w, colimit.w])
  exact ⟨j, fun U ↦ 𝒱.ι_glueMorphisms _ _ U⟩

end GlobalTheory.ColimitGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodMem
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem exists_good_mem : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂] (x : Y₀), ∃ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, x ∈ U := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ _ x
  obtain ⟨V₁, hV₁, hx₁, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y₁.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (i₁ x))
  obtain ⟨V₂, hV₂, hx₂, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y₂.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (i₂ x))
  have hV₁' : IsAffineOpen V₁ := hV₁
  have hV₂' : IsAffineOpen V₂ := hV₂
  have hW₁ : IsAffineOpen (i₁ ⁻¹ᵁ V₁) := hV₁'.preimage i₁
  have hW₂ : IsAffineOpen (i₂ ⁻¹ᵁ V₂) := hV₂'.preimage i₂
  obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hW₁ hW₂ x ⟨hx₁, hx₂⟩
  obtain ⟨f', rfl⟩ := i₁.app_surjective V₁ hV₁' f
  obtain ⟨g', rfl⟩ := i₂.app_surjective V₂ hV₂' g
  refine ⟨Y₀.basicOpen ((i₁.app V₁).hom f'), ⟨hW₁.basicOpen _, ?_, ?_⟩, hxf⟩
  · rw [← Scheme.preimage_basicOpen, upOpen_preimage]
    exact hV₁'.basicOpen f'
  · rw [e, ← Scheme.preimage_basicOpen, upOpen_preimage]
    exact hV₂'.basicOpen g'

end GlobalTheory.FerrandPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrallyClosedPadicIntegralSubring
section
noncomputable section

open GlobalTheory.LatVal (Sz)
open Polynomial

namespace GlobalTheory.QFam.SzRing

variable (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])

abbrev nval : Valuation ℂ_[l] NNReal := NormedField.valuation

theorem mem_integer_iff (y : ℂ_[l]) : y ∈ (nval l).integer ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
  exact Iff.rfl

def szRing : Subring ℂ :=
  ((nval l).integer.comap lam).map (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_szRing (x : ℂ) : x ∈ szRing l lam ↔ Sz l lam 0 x := by
  unfold szRing Sz
  rw [Real.rpow_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (mem_integer_iff l _).1 hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨x, h⟩, (mem_integer_iff l _).2 hy, rfl⟩

def toAlg : szRing l lam →+* algebraicClosure ℚ ℂ :=
  (szRing l lam).subtype.codRestrict (algebraicClosure ℚ ℂ) fun r => ((mem_szRing l lam r.1).1 r.2).1

theorem lam_toAlg_mem (r : szRing l lam) : (lam.comp (toAlg l lam)) r ∈ (nval l).integer := by
  obtain ⟨h, hr⟩ := (mem_szRing l lam r.1).1 r.2
  rw [Real.rpow_zero] at hr
  exact (mem_integer_iff l _).2 hr

theorem mem_szRing_of_isIntegral (x : ℂ) (hx : IsIntegral (szRing l lam) x) : x ∈ szRing l lam := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hc : (algebraMap (algebraicClosure ℚ ℂ) ℂ).comp (toAlg l lam) = algebraMap (szRing l lam) ℂ :=
    RingHom.ext fun _ => rfl
  have h1 : IsIntegral (algebraicClosure ℚ ℂ) x :=
    ⟨p.map (toAlg l lam), hp.map _, by rw [eval₂_map, hc, hpx]⟩
  have : Algebra.IsIntegral ℚ (algebraicClosure ℚ ℂ) :=
    ⟨fun y => (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val Subtype.val_injective).1
      (mem_algebraicClosure_iff'.1 y.2)⟩
  have h2 : x ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff'.2 (isIntegral_trans x h1)
  have h3 : eval₂ (toAlg l lam) ⟨x, h2⟩ p = 0 := by
    apply (algebraMap (algebraicClosure ℚ ℂ) ℂ).injective
    rw [hom_eval₂, hc, map_zero]
    exact hpx
  have h4 : eval₂ (lam.comp (toAlg l lam)) (lam ⟨x, h2⟩) p = 0 := by
    rw [← hom_eval₂, h3, map_zero]
  let g : szRing l lam →+* (nval l).integer :=
    (lam.comp (toAlg l lam)).codRestrict (nval l).integer (lam_toAlg_mem l lam)
  have hg : (algebraMap (nval l).integer ℂ_[l]).comp g = lam.comp (toAlg l lam) :=
    RingHom.ext fun _ => rfl
  have h5 : IsIntegral (nval l).integer (lam ⟨x, h2⟩) :=
    ⟨p.map g, hp.map _, by rw [eval₂_map, hg, h4]⟩
  have h6 := (Valuation.integer.integers (nval l)).mem_of_integral h5
  rw [mem_szRing]
  refine ⟨h2, ?_⟩
  rw [Real.rpow_zero]
  exact (mem_integer_iff l _).1 h6

end GlobalTheory.QFam.SzRing

theorem GlobalTheory.QFam.exists_szRing (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) :
    ∃ R : Subring ℂ, (∀ x, x ∈ R ↔ Sz l lam 0 x) ∧ ∀ x, IsIntegral R x → x ∈ R :=
  ⟨GlobalTheory.QFam.SzRing.szRing l lam, GlobalTheory.QFam.SzRing.mem_szRing l lam,
    GlobalTheory.QFam.SzRing.mem_szRing_of_isIntegral l lam⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelTorsorOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherian_model_torsor_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j →
    ∀ (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T), Function.Injective i ∧ IsLocalHom i ∧ IsUnit (q : A) ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA ∧
      ∃ (DA : Type) (_ : CommRing DA) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)
        (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA ∧
        ∀ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA →
          ∃ σ₁ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_noetherian_model) | (exact GlobalTheory.KeyOriginNoeth.exists_noetherian_model) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_noetherian_model  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNbhdSectionFibreIsPreirreducible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem affineOpen_fromSpec_mem_basicOpen_iff {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U)
    (c : Γ(Y, U)) (P : PrimeSpectrum Γ(Y, U)) : hU.fromSpec P ∈ Y.basicOpen c ↔ c ∉ P.asIdeal :=
  SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen c) P

theorem exists_open_nbhd_section_fibre_isPreirreducible : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X),
    Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (U : X.Opens) (V₀ V : S.Opens) (I : Finset Γ(S, V)),
      V₀ ≤ V ∧ s ∈ V₀ ∧ e s ∈ U ∧ (∀ c ∈ I, s ∉ S.basicOpen c) ∧
      ∀ t ∈ V₀, (∀ c ∈ I, t ∉ S.basicOpen c) → IsPreirreducible ((U : Set X) ∩ f ⁻¹' {t}) := by
  intro X S f e hf hef s
  obtain ⟨V, W, hWV, hV, hW, hes, hirr⟩ := _root_.GlobalTheory.exists_affine_chart_preirreducible_fiber X S f e hf hef s
  have hfes : f (e s) = s := by rw [← Scheme.Hom.comp_apply, hef]; rfl
  have hsV : s ∈ V := by have h := hWV hes; rwa [Scheme.Hom.mem_preimage, hfes] at h
  letI : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  have hsm : Algebra.Smooth Γ(S, V) Γ(X, W) :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.appLE @Smooth f hf ⟨V, hV⟩ ⟨W, hW⟩ hWV)

  have hcomap : ∀ (x : X) (hxW : x ∈ W) (hxV : f x ∈ V),
      (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) =
        (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal := fun x hxW hxV =>
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hxW)
  have hfx : ∀ r : Spec Γ(X, W), f (hW.fromSpec r) =
      hV.fromSpec (Spec.map (f.appLE V W hWV) r) := fun r => by
    show (hW.fromSpec ≫ f) r = (Spec.map (f.appLE V W hWV) ≫ hV.fromSpec) r
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV]
  set q := hW.primeIdealOf ⟨e s, hes⟩ with hqdef
  set p₀ := hV.primeIdealOf ⟨s, hsV⟩ with hp₀def
  have hq : q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = p₀.asIdeal := by
    rw [hqdef, hcomap (e s) hes (hWV hes)]
    congr 2; exact Subtype.ext hfes
  let Ω := AlgebraicClosure p₀.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap Γ(S, V) Ω) = p₀.asIdeal := by
    rw [IsScalarTower.algebraMap_eq Γ(S, V) p₀.asIdeal.ResidueField Ω, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap p₀.asIdeal.ResidueField Ω).injective]
    exact Ideal.ker_algebraMap_residueField _
  have hpt : (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) ≫ hV.fromSpec)
      (IsLocalRing.closedPoint Ω) = s := by
    have : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω) = p₀ := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap Γ(S, V) Ω) (IsLocalRing.maximalIdeal Ω) = p₀.asIdeal
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
    show hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω)) = s
    rw [this, hp₀def, hV.fromSpec_primeIdealOf]
  have h1 := hirr Ω _ hpt
  have h2 := _root_.GlobalTheory.preirreducibleSpace_tensor_of_pullback X S f V W hWV hV hW Ω rfl h1
  obtain ⟨b, a, I, hb, ha, hI, hmain⟩ := _root_.GlobalTheory.exists_basicOpen_fibres_preirreducible Γ(S, V) Γ(X, W) hsm q Ω (hq.trans hker.symm) h2
  refine ⟨X.basicOpen b, S.basicOpen a, V, I, S.basicOpen_le a, ?_, ?_, ?_, ?_⟩
  · have h := (affineOpen_fromSpec_mem_basicOpen_iff hV a p₀).mpr (by rw [← hq]; exact ha)
    rwa [hp₀def, hV.fromSpec_primeIdealOf] at h
  · have h := (affineOpen_fromSpec_mem_basicOpen_iff hW b q).mpr hb
    rwa [hqdef, hW.fromSpec_primeIdealOf] at h
  · intro c hc hsc
    have h := (affineOpen_fromSpec_mem_basicOpen_iff hV c p₀).mp
      (by rw [hp₀def, hV.fromSpec_primeIdealOf]; exact hsc)
    exact h (by rw [← hq]; exact hI c hc)
  · intro t htV₀ htI
    have htV : t ∈ V := S.basicOpen_le a htV₀
    set t' := hV.primeIdealOf ⟨t, htV⟩ with ht'def
    have hft' : hV.fromSpec t' = t := hV.fromSpec_primeIdealOf _
    have ha' : a ∉ t'.asIdeal :=
      (affineOpen_fromSpec_mem_basicOpen_iff hV a t').mp (by rw [hft']; exact htV₀)
    have hc' : ∀ c ∈ I, c ∈ t'.asIdeal := fun c hc => by
      by_contra hnc
      exact htI c hc (hft' ▸ (affineOpen_fromSpec_mem_basicOpen_iff hV c t').mpr hnc)
    have hZ := hmain t' ha' hc'
    have heq : ((X.basicOpen b : X.Opens) : Set X) ∩ f ⁻¹' {t} = hW.fromSpec ''
        {r : PrimeSpectrum Γ(X, W) | r.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = t'.asIdeal ∧
          b ∉ r.asIdeal} := by
      ext x
      constructor
      · rintro ⟨hxU, hxt⟩
        have hxW : x ∈ W := X.basicOpen_le b hxU
        have hxt' : f x = t := hxt
        refine ⟨hW.primeIdealOf ⟨x, hxW⟩, ⟨?_, ?_⟩, hW.fromSpec_primeIdealOf _⟩
        · rw [hcomap x hxW (hWV hxW), ht'def]
          congr 2; exact Subtype.ext hxt'
        · exact (affineOpen_fromSpec_mem_basicOpen_iff hW b _).mp
            (by rw [hW.fromSpec_primeIdealOf]; exact hxU)
      · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
        refine ⟨(affineOpen_fromSpec_mem_basicOpen_iff hW b r).mpr hr2, ?_⟩
        show f (hW.fromSpec r) = t
        have : Spec.map (f.appLE V W hWV) r = t' := PrimeSpectrum.ext hr1
        rw [hfx, this, hft']
    rw [heq]
    exact hZ.image _ (Scheme.Hom.continuous _).continuousOn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdealStatement
section
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameReduction_eq_one_of_congruent_mod_ideal : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ → x ∈ Formalism.L2.DIV.St β → ∀ (I : Ideal (𝓞 E)), (∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) → ∀ (PP : Formalism.L2.DIV.Pl E), I ≤ PP.asIdeal → Formalism.L2.DIV.redFn β PP x = 1 := by
  first | exact @GlobalTheory.FrameCong.redFn_eq_one_of_congr | exact GlobalTheory.FrameCong.redFn_eq_one_of_congr | (intros; apply GlobalTheory.FrameCong.redFn_eq_one_of_congr <;> assumption)
end

