module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdMulInertiaDegEqFinrankMulOrd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0148

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgOfSaturatedIdealPowerIntoImage
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem fg_of_saturated_ideal_power_into_image :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] (I : Ideal S),
      (∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ I ^ k, IsLocalization.IsInteger S (a • c)) →
        IsLocalization.IsInteger S c) →
      ∀ (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M]
        (N : Submodule S (FractionRing S ⊗[S] M)),
        (∀ z ∈ N, ∃ k : ℕ, ∀ a ∈ I ^ k,
          a • z ∈ LinearMap.range (TensorProduct.mk S (FractionRing S) M 1)) → N.FG := by
  intro S _ _ _ I hsat M _ _ _ N hN
  classical
  set K := FractionRing S
  let V := K ⊗[S] M
  let b := Module.Free.chooseBasis K V
  let ι := Module.Free.ChooseBasisIndex K V
  let T : V →ₗ[S] (ι → K) := (b.equivFun.toLinearMap).restrictScalars S

  let L : Submodule S (ι → K) := LinearMap.range ((Algebra.linearMap S K).compLeft ι)
  have memL : ∀ v : ι → K, (∀ i, IsLocalization.IsInteger S (v i)) → v ∈ L := by
    intro v hv
    choose w hw using hv
    exact ⟨w, funext fun i => hw i⟩
  have memL' : ∀ v ∈ L, ∀ i, IsLocalization.IsInteger S (v i) := by
    rintro v ⟨w, rfl⟩ i
    exact ⟨w i, rfl⟩
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := S) (M := M)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors S)
    (Finset.univ : Finset (Fin n × ι)) (fun p => T (1 ⊗ₜ g p.1) p.2)
  let F : V →ₗ[S] (ι → K) := (d : S) • T
  have hFM : ∀ m : M, F (1 ⊗ₜ m) ∈ L := by
    intro m
    have hle : Submodule.span S (Set.range g) ≤ L.comap (F ∘ₗ TensorProduct.mk S K M 1) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show F (1 ⊗ₜ g j) ∈ L
      apply memL
      intro i
      exact hd (j, i) (Finset.mem_univ _)
    have : m ∈ Submodule.span S (Set.range g) := by rw [hg]; trivial
    exact hle this
  have hFN : ∀ z ∈ N, F z ∈ L := by
    intro z hz
    obtain ⟨k, hk⟩ := hN z hz
    apply memL
    intro i
    apply hsat k
    intro a ha
    obtain ⟨m, hm⟩ := hk a ha
    have h1 := hFM m
    simp only [TensorProduct.mk_apply] at hm
    rw [hm, map_smul] at h1
    simpa using memL' _ h1 i
  have hFinj : Function.Injective F := by
    intro x y hxy
    have hd0 : algebraMap S K (d : S) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have : algebraMap S K (d : S) • b.equivFun x = algebraMap S K (d : S) • b.equivFun y := by
      simpa [F, T, algebraMap_smul] using hxy
    exact b.equivFun.injective (smul_right_injective _ hd0 this)
  have hLfg : L.FG := by
    show (LinearMap.range ((Algebra.linearMap S K).compLeft ι)).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  haveI : IsNoetherian S L := isNoetherian_of_fg_of_noetherian L hLfg
  apply Submodule.fg_of_fg_map_injective F hFinj
  exact Submodule.FG.of_le_of_isNoetherian (T := L) (by
    rintro _ ⟨z, hz, rfl⟩
    exact hFN z hz)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationComm
section
set_option autoImplicit false

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem dw_comm (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W) :
    dw a (dw b x) = dw b (dw a x) := by
  have key : ∀ (u v : Tot I g) (p : Tot I g), p ∈ W →
      (Hol.der u (Hol.der v x)).fn p = fderiv ℂ (fderiv ℂ x.fn) p u v := by
    intro u v p hp
    have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
    have e : (Hol.der v x).fn =ᶠ[nhds p] fun q ↦ fderiv ℂ x.fn q v := by
      filter_upwards [W.isOpen.mem_nhds hp] with q hq using Hol.fn_der v x hq
    rw [Hol.fn_der u _ hp, e.fderiv_eq,
      fderiv_clm_apply hx.fderiv.differentiableAt (differentiableAt_const v)]
    simp
  refine Hol.ext_fn fun p hp ↦ ?_
  have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
  have hs : IsSymmSndFDerivAt ℂ x.fn p :=
    (hx.contDiffAt (n := ⊤)).isSymmSndFDerivAt (by simp)
  unfold dw
  rw [key _ _ p hp, key _ _ p hp]
  exact hs _ _

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCutOutSubalgebraQuasiCoherent
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem subMap_finite (X : Scheme.{0}) (_hX : IsNoetherian X) (F : X.Opensᵒᵖ ⥤ CommRingCat)
    (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (hint : ∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral)
    {ι : Type} (V : ι → X.Opens) (_hV : ∀ j, IsAffineOpen (V j)) (hcov : ∀ x : X, ∃ j, x ∈ V j)
    (T : ∀ j, Set (F.obj (op (V j)))) (hT : ∀ j, (T j).Finite) (W : X.Opens)
    (hW : IsAffineOpen W) : (subMap F α V T W).Finite := by
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI alg : Algebra Γ(X, W) (F.obj (op W)) := (α.app (op W)).hom.toAlgebra
  let S : Subalgebra Γ(X, W) (F.obj (op W)) :=
    { sub F α V T W with algebraMap_mem' := algebraMap_mem_sub F α V T W }
  let s : Set Γ(X, W) := {g | ∃ j, X.basicOpen g ≤ V j}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨g, hg, hxg⟩ := hW.exists_basicOpen_le (V := V j) ⟨x, hj⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, j, hg⟩, hxg⟩
  have hloc : ∀ g ∈ s, ∃ E : Finset (F.obj (op W)), ∀ b ∈ S.toSubmodule, ∃ m : ℕ,
      algebraMap Γ(X, W) (F.obj (op W)) g ^ m * b ∈ Submodule.span Γ(X, W) (E : Set _) := by
    rintro g ⟨j, hj⟩
    have hD : IsAffineOpen (X.basicOpen g) := hW.basicOpen g
    letI a1 : Algebra Γ(X, W) Γ(X, X.basicOpen g) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI a2 : Algebra Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      (α.app (op (X.basicOpen g))).hom.toAlgebra
    letI a3 : Algebra (F.obj (op W)) (F.obj (op (X.basicOpen g))) :=
      (F.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI a4 : Algebra Γ(X, W) (F.obj (op (X.basicOpen g))) :=
      ((α.app (op (X.basicOpen g))).hom.comp
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).toAlgebra
    haveI : IsScalarTower Γ(X, W) (F.obj (op W)) (F.obj (op (X.basicOpen g))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ by
        have := congr($(α.naturality (homOfLE (X.basicOpen_le g)).op).hom r)
        simp only [CommRingCat.comp_apply] at this
        exact this
    haveI : IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ rfl
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) := hW.isLocalization_basicOpen g
    haveI : IsLocalization.Away (algebraMap Γ(X, W) (F.obj (op W)) g)
        (F.obj (op (X.basicOpen g))) := isLocalizationAway F α hα hW g
    let N : Submodule Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      (Algebra.adjoin Γ(X, X.basicOpen g) ((F.map (homOfLE hj).op).hom '' T j)).toSubmodule
    have hN : N.FG := fg_adjoin_of_finite ((hT j).image _) (fun x _ ↦ hint _ hD x)
    obtain ⟨E, hE⟩ := GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway (R := Γ(X, W)) (A := F.obj (op W)) (R' := Γ(X, X.basicOpen g))
      (A' := F.obj (op (X.basicOpen g))) g N hN
    refine ⟨E, fun b hb ↦ hE b ?_⟩
    have := (mem_sub F α V T).mp hb j (X.basicOpen g) hD (X.basicOpen_le g) hj
    rw [gen_eq_adjoin] at this
    exact this
  have hfg : S.toSubmodule.FG := GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem S.toSubmodule s hs hloc
  letI := (subMap F α V T W).toAlgebra
  have hfin : Module.Finite Γ(X, W) S.toSubmodule := Module.Finite.iff_fg.mpr hfg
  let e : S.toSubmodule ≃ₗ[Γ(X, W)] sub F α V T W :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact Module.Finite.equiv e

end GlobalTheory.QcSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfGaloisTraceRelation
section
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleFinite

theorem finite_of_trace_relation (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R) :
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  intro hT a ha n x y hrel htf
  set b : R := algebraMap A R a with hb

  have key : ∀ c : C, b • c = ∑ i, T (y i * c) • x i := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i
      rw [Algebra.smul_def, hT, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hrel]
    simp [Algebra.smul_def]
  let S : Submodule R C := Submodule.span R (Set.range x)
  have hmem : ∀ c : C, b • c ∈ S := by
    intro c
    rw [key c]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : C →ₗ[R] S := LinearMap.codRestrict S (b • LinearMap.id) (fun c => by simpa using hmem c)
  have hf : Function.Injective f := by
    intro c d hcd
    have : b • c = b • d := by simpa [f] using congrArg Subtype.val hcd
    have h0 : b • (c - d) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf a ha _ h0)
  haveI : Module.Finite R S := Module.Finite.span_of_finite R (Set.finite_range x)
  haveI : IsNoetherian R S := isNoetherian_of_isNoetherianRing_of_finite R S
  exact Module.Finite.of_injective f hf

end GlobalTheory.GoodEtaleFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpan
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem finrank_addValuationInteger_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X →
    finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) =>
      (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  intro C _ v N X hX
  let ι : (Fin N → Int0 v) →ₗ[Int0 v] (Fin N → C) := (Algebra.linearMap (Int0 v) C).compLeft (Fin N)
  have hι : Function.Injective ι := by
    intro x y h; funext i; exact Subtype.ext (congrFun h i)
  let L : X →ₗ[Int0 v] (Fin N → C) := ι ∘ₗ X.subtype
  have hL : Function.Injective L := hι.comp Subtype.val_injective
  have hInt : v.toValuation.Integers (Int0 v) := by
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro x
      change 0 ≤ v (x : C)
      exact (mem_addValuationIntegerRing_iff v _).mp x.property
    · intro x hx
      change 0 ≤ v x at hx
      exact ⟨⟨x, (mem_addValuationIntegerRing_iff v x).mpr hx⟩, rfl⟩
  have : ValuationRing (Int0 v) := ValuationRing.of_integers _ hInt
  have : IsFractionRing (Int0 v) C := hInt.isFractionRing
  have : Module.IsTorsionFree (Int0 v) X := inferInstance
  have : Module.Free (Int0 v) X := free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) X
  let b := Module.Free.chooseBasis (Int0 v) X
  have hli : LinearIndependent (Int0 v) (L ∘ b) :=
    b.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hL)
  have hliC : LinearIndependent C (L ∘ b) := (LinearIndependent.iff_fractionRing (Int0 v) C).mp hli
  have hspan : Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
      (X : Set (Fin N → Int0 v))) = Submodule.span C (Set.range (L ∘ b)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : L ⟨x, hx⟩ ∈ Submodule.span (Int0 v) (L '' Set.range b) :=
        Submodule.apply_mem_span_image_of_mem_span L (by rw [b.span_eq]; trivial)
      rw [← Set.range_comp] at h1
      exact Submodule.span_le_restrictScalars (Int0 v) C _ h1
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(b k : Fin N → Int0 v), (b k).2, rfl⟩
  rw [hspan, finrank_span_eq_card hliC, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyModPrimeUniversalCoefficients
section
open CategoryTheory Limits

namespace GlobalTheory

theorem uct_mod_p : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  intro C p _ hinj hfin n
  obtain ⟨π, hz, hS⟩ := _root_.GlobalTheory.shortExact_mul_p_modP C p hinj
  have e := _root_.GlobalTheory.natCard_homology_of_shortExact_mul p C _ π hz hS n
  rw [_root_.GlobalTheory.natCard_homology_restrictScalars] at e
  haveI := hfin n
  haveI := hfin (n + 1)
  have a1 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology n) p
  have a2 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology (n + 1)) p
  rw [← GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples] at a1 a2 e
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hcp : Nat.card (ZMod p) = p := by simp
  have c1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology n))
  have c2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology (n + 1)))
  rw [hcp] at c1 c2
  set D := (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n
  have hk : Nat.card (LinearMap.ker ((p : ℤ) • LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1))) ≠ 0 := by
    intro h0; rw [h0, zero_mul, c2] at a2; exact absurd a2 (pow_ne_zero _ (by omega))
  have hD : Nat.card D ≠ 0 := by
    rw [e, c1]; exact mul_ne_zero (pow_ne_zero _ (by omega)) hk
  haveI : Finite D := Nat.finite_of_card_ne_zero hD
  haveI : Module.Finite (ZMod p) D := Module.Finite.of_finite
  have c0 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := D)
  rw [hcp] at c0
  have key : p ^ (Module.finrank (ZMod p) D + Module.finrank ℤ (C.homology (n + 1))) = p ^ (Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1)))) := by
    rw [pow_add, pow_add, ← c0, e, ← c1, ← c2, a2]; ring
  have := Nat.pow_right_injective hp key
  push_cast; omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutative
section
open scoped Pointwise

namespace GlobalTheory

theorem finsum_doubleCoset_regroup (G : Type) [Group G] (T Γ C K' : Subgroup G) (φ : G → ℂ)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hCT : C ≤ T)
    (hU : ∀ x : G, T ⊓ K'.map (MulAut.conj x).toMonoidHom ≤ C ∧ (T ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0)
    (hφ : ∀ t ∈ T, ∀ k ∈ K', ∀ x, φ (t * x * k) = φ x) :
    ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G), ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) * ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K' : Set G), (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out q) := by
  classical
  have hconj : ∀ t ∈ T, ∀ k ∈ K', ∀ x : G,
      T ⊓ K'.map (MulAut.conj (t * x * k)).toMonoidHom = T ⊓ K'.map (MulAut.conj x).toMonoidHom := by
    intro t ht k hk x
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · rintro ⟨hg, hm⟩
      refine ⟨hg, ?_⟩
      have e1 : t⁻¹ * g * t = g := by rw [mul_assoc, hT g hg t ht, inv_mul_cancel_left]
      have e2 : (t * x * k)⁻¹ * g * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * g * t) * x) * k := by group
      rw [e1] at e2
      rw [e2] at hm
      have e3 : x⁻¹ * g * x = k * (k⁻¹ * (x⁻¹ * g * x) * k) * k⁻¹ := by group
      rw [e3]
      exact K'.mul_mem (K'.mul_mem hk hm) (K'.inv_mem hk)
    · rintro ⟨hg, hm⟩
      refine ⟨hg, ?_⟩
      have e1 : t⁻¹ * g * t = g := by rw [mul_assoc, hT g hg t ht, inv_mul_cancel_left]
      have e2 : (t * x * k)⁻¹ * g * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * g * t) * x) * k := by group
      rw [e1] at e2
      rw [e2]
      exact K'.mul_mem (K'.mul_mem (K'.inv_mem hk) hm) hk
  let π : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) →
      DoubleCoset.Quotient (T : Set G) (K' : Set G) := fun q => DoubleCoset.mk T K' (Quotient.out q)
  let h : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ := fun p =>
    ((Nat.card (Γ ⊓ (T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom) : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out p)
  have hLHS : ∀ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G),
      ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = h (π q) := by
    intro q
    obtain ⟨t, ht, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul T K' (Quotient.out q)
    show _ = ((Nat.card (Γ ⊓ (T ⊓ K'.map (MulAut.conj (Quotient.out (DoubleCoset.mk T K' (Quotient.out q)))).toMonoidHom) : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out (DoubleCoset.mk T K' (Quotient.out q)))
    rw [e, hconj t ht k hk, hφ t ht k hk, inf_assoc]
  set a : ℂ := (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) with ha_def
  have hfinal : ∀ p, (Nat.card (π ⁻¹' {p}) : ℂ) * h p
      = a * ((((T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out p)) := by
    intro p
    have e1 := _root_.GlobalTheory.doubleCoset_fibre_card T Γ K' (Quotient.out p)
    rw [DoubleCoset.out_eq'] at e1
    have e2 := _root_.GlobalTheory.DCIndex.index_identity T Γ (T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom) C hT (hU _).1 hCT (hU _).2
    show (Nat.card (π ⁻¹' {p}) : ℂ) * (((Nat.card (Γ ⊓ (T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom) : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out p)) = _
    rw [e1, ← mul_assoc, ← div_eq_mul_inv, e2, ha_def]
    ring
  have hmul : ∀ (c : ℂ) (f : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ),
      c * ∑ᶠ p, f p = ∑ᶠ p, c * f p := by
    intro c f
    exact mul_finsum f c
  have hdich : (∀ p, h p ≠ 0 → (π ⁻¹' {p}).Finite) ∨ (∀ p, h p ≠ 0 → Nat.card (π ⁻¹' {p}) = 0) := by
    by_cases ha : a = 0
    · right
      intro p hp
      have hc := hfinal p
      rw [ha, zero_mul] at hc
      rcases mul_eq_zero.mp hc with h1 | h1
      · exact_mod_cast h1
      · exact absurd h1 hp
    · left
      intro p hp
      have hφp : φ (Quotient.out p) ≠ 0 := fun e => hp (by simp [h, e])
      have hne : (Nat.card (π ⁻¹' {p}) : ℂ) * h p ≠ 0 := by
        rw [hfinal p]
        exact mul_ne_zero ha (mul_ne_zero (by exact_mod_cast (hU _).2) hφp)
      have hn : Nat.card (π ⁻¹' {p}) ≠ 0 := by
        intro e; apply hne; simp [e]
      exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hn)
  calc _ = ∑ᶠ q, h (π q) := finsum_congr hLHS
    _ = ∑ᶠ p, (Nat.card (π ⁻¹' {p}) : ℂ) * h p := GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul π h hdich
    _ = ∑ᶠ p, a * ((((T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out p)) := finsum_congr hfinal
    _ = _ := (hmul a _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdMulInertiaDegEqFinrankMulOrdStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord' : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ringKrullDim A = 1 → ∀ a : A, a ≠ 0 → ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A}, ((Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ (algebraMap A B a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg A : ℤ) = (Module.finrank A B : ℤ) * ((Ring.ord A a).toNat : ℤ) := by
  first | exact @GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | exact GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | (intros; apply GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumStabilizerWeightedPairOrbitsConjClassStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    ∀ γ₀ : Γ, ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  first | (exact @GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (exact GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (intros; apply GlobalTheory.MassConj.finsum_pairOrbit_fibre  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainL2BoundStatement
section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_L2_bound : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ, (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) → ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧ ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.QuotLocInt.integrableOn_compact | exact GlobalTheory.QuotLocInt.integrableOn_compact | (intros; apply GlobalTheory.QuotLocInt.integrableOn_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HartTensorOfFlatStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hart_baseChange_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  first | (exact @GlobalTheory.GoodEtale.hart_tensor_of_flat) | (exact GlobalTheory.GoodEtale.hart_tensor_of_flat) | (intros; apply GlobalTheory.GoodEtale.hart_tensor_of_flat  <;> assumption)
end

