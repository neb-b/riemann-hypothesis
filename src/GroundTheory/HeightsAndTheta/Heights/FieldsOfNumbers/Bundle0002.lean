module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem isRelevant_iff {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (I : Ideal (MRing ι R)) :
    IsRelevant I ↔ ∀ k, ∃ v : Σ k, ι k, v.1 = k ∧ (X v : MRing ι R) ∉ I := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨⟨k, i⟩, rfl, hi⟩
  · intro h k
    obtain ⟨⟨k', i⟩, hk, hi⟩ := h k
    subst hk
    exact ⟨i, hi⟩

theorem extend_zero_inj {K K' : Type*} {j : K → K'} (hj : Function.Injective j)
    {x y : K → ℕ} : Function.extend j x 0 = Function.extend j y 0 ↔ x = y :=
  ⟨fun h => funext fun k => by simpa [hj.extend_apply] using congrFun h (j k), fun h => h ▸ rfl⟩

variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {j : K → K'} {g : (Σ k, ι k) → (Σ k, ι' k)} (hgj : ∀ v, (g v).1 = j v.1)

include hgj

include hgj in
theorem weight_mapDomain (hj : Function.Injective j) (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g d) =
      Function.extend j (Finsupp.weight (blockWeight ι) d) 0 := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • blockWeight ι' i)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext k'
  by_cases hk : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hj.extend_apply]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply,
      hj.eq_iff]
  · rw [Function.extend_apply' _ _ _ hk]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply,
      Pi.zero_apply]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [ite_eq_right fun h => hk ⟨v.1, h.symm⟩, smul_zero]


include hgj in
theorem rename_weightedHomogeneousComponent (hj : Function.Injective j)
    (hg : Function.Injective g) {R : Type*} [CommSemiring R] (b : K → ℕ)
    (f : MvPolynomial (Σ k, ι k) R) :
    rename g (weightedHomogeneousComponent (blockWeight ι) b f) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0) (rename g f) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain g d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain g hg, coeff_rename_mapDomain g hg,
      coeff_weightedHomogeneousComponent, weight_mapDomain hgj hj, extend_zero_inj hj]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    · rfl


include hgj in
theorem isMultiProjPrime_comap_rename (hj : Function.Injective j) (hg : Function.Injective g)
    (hsurj : ∀ w : Σ k, ι' k, w.1 ∈ Set.range j → ∃ v, g v = w) {R : Type*} [CommRing R]
    {P : Ideal (MRing ι' R)} (hP : IsMultiProjPrime P) :
    IsMultiProjPrime (P.comap (rename (R := R) g)) := by
  refine ⟨?_, ?_, ?_⟩
  · have := hP.isPrime
    exact Ideal.comap_isPrime _ _
  · intro f hf b
    rw [Ideal.mem_comap] at hf ⊢
    rw [rename_weightedHomogeneousComponent hgj hj hg]
    exact hP.multiHomog _ hf _
  · rw [isRelevant_iff]
    intro k
    obtain ⟨w, hw, hwP⟩ := (isRelevant_iff P).1 hP.relevant (j k)
    obtain ⟨v, rfl⟩ := hsurj w ⟨k, hw.symm⟩
    refine ⟨v, hj (by rw [← hgj, hw]), ?_⟩
    rw [Ideal.mem_comap, rename_X]
    exact hwP

end

end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherCharP
section
set_option maxSynthPendingDepth 1

open Polynomial

namespace GroundTheory.Heights₂.Heights.FieldNumbers

universe u


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem finite_integralClosure_mvPolynomial_of_charP (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (s : ℕ) (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) := by
  classical
  set B := MvPolynomial (Fin s) k
  set F := FractionRing B
  have hp : p.Prime := Fact.out
  have hinjBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective B F)
  have : CharP L p := charP_of_injective_ringHom (f := (algebraMap B L).comp MvPolynomial.C)
    (hinjBL.comp (MvPolynomial.C_injective (Fin s) k)) p

  have : ExpChar (separableClosure F L) p := ExpChar.prime hp
  have : IsPurelyInseparable (separableClosure F L) L := separableClosure.isPurelyInseparable F L
  set e := IsPurelyInseparable.exponent (separableClosure F L) L
  set q := p ^ e with hqdef
  have hq : 0 < q := pow_pos hp.pos e
  have hsepq : ∀ y : L, IsSeparable F (y ^ q) := by
    intro y
    rw [← IsPurelyInseparable.algebraMap_iterateFrobenius (separableClosure F L) p (le_refl e) y]
    exact mem_separableClosure_iff.mp
      (IsPurelyInseparable.iterateFrobenius (separableClosure F L) L p (le_refl e) y).2

  let : Algebra k L := ((algebraMap B L).comp (algebraMap k B)).toAlgebra
  have : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq' rfl
  set Ω := AlgebraicClosure L
  have hinjBΩ : Function.Injective (algebraMap B Ω) := by
    rw [IsScalarTower.algebraMap_eq B L Ω]
    exact (algebraMap L Ω).injective.comp hinjBL

  let b := Module.finBasis F L
  let g : Fin (Module.finrank F L) → F[X] := fun j => minpoly F (b j ^ q)
  choose num den hden hnd using fun c : F => IsFractionRing.div_surjective (A := B) c
  let Tk : Finset k := Finset.univ.biUnion fun j => (Finset.range ((g j).natDegree + 1)).biUnion
    fun i => (num ((g j).coeff i)).support.image (num ((g j).coeff i)).coeff ∪
      (den ((g j).coeff i)).support.image (den ((g j).coeff i)).coeff

  choose r hr using fun a : k => IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω a) hq
  choose t ht using fun i : Fin s =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap B Ω (MvPolynomial.X i)) hq
  let k' : IntermediateField k Ω := IntermediateField.adjoin k (r '' (Tk : Set k))
  have : FiniteDimensional k k' := by
    have : Finite (r '' (Tk : Set k)) := ((Tk.finite_toSet).image r).to_subtype
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨a, -, rfl⟩
    refine ⟨X ^ q - C a, monic_X_pow_sub_C a hq.ne', ?_⟩
    simp [eval₂_sub, hr a, Algebra.algebraMap_eq_smul_one]
  have hk'root : ∀ a ∈ Tk, ∃ z : k', z ^ q = algebraMap k k' a := by
    intro a ha
    refine ⟨⟨r a, IntermediateField.subset_adjoin k _ ⟨a, ha, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    simp [hr a]
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p

  set B' := MvPolynomial (Fin s) k'
  let θ : B →ₐ[k] B' := (MvPolynomial.mapAlgHom (Algebra.ofId k k')).comp (MvPolynomial.expand q)
  have hθ : ∀ N : B, θ N = MvPolynomial.map (algebraMap k k') (MvPolynomial.expand q N) :=
    fun N => rfl
  let : Algebra B B' := θ.toRingHom.toAlgebra
  have : Module.Finite B B' := finite_mapExpand k k' (Fin s) q hq
  have : Algebra.IsIntegral B B' := Algebra.IsIntegral.of_finite B B'
  let ψ : B' →ₐ[k'] Ω := MvPolynomial.aeval t
  have hψθ : ∀ N : B, ψ (θ N) = algebraMap B Ω N := by
    have h : (ψ.restrictScalars k).comp θ = IsScalarTower.toAlgHom k B Ω := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, θ, ψ, MvPolynomial.mapAlgHom_apply,
        MvPolynomial.expand_X, map_pow, MvPolynomial.map_X]
      erw [MvPolynomial.aeval_X]
      rw [ht]
      rfl
    intro N
    exact DFunLike.congr_fun h N
  have hψinj : Function.Injective ψ := by
    refine injective_of_isIntegral (B := B) ψ.toRingHom ?_
    convert hinjBΩ using 1
    funext N
    exact hψθ N
  let : Algebra B' Ω := ψ.toRingHom.toAlgebra
  have : IsScalarTower B B' Ω := IsScalarTower.of_algebraMap_eq fun N => (hψθ N).symm
  have : FaithfulSMul B' Ω := (faithfulSMul_iff_algebraMap_injective B' Ω).mpr hψinj
  set F' := FractionRing B'
  let : Algebra F' Ω := FractionRing.liftAlgebra B' Ω

  have hFF' : ∀ c : F, ∃ c' : F', algebraMap F' Ω c' = algebraMap F Ω c := by
    intro c
    refine ⟨algebraMap B' F' (θ (num c)) / algebraMap B' F' (θ (den c)), ?_⟩
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    change ψ (θ (num c)) / ψ (θ (den c)) = _
    rw [hψθ, hψθ]
    conv_rhs => rw [← hnd c]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hrootB : ∀ N : B, (∀ m ∈ N.support, N.coeff m ∈ Tk) →
      ∃ N' : B', ψ N' ^ q = algebraMap B Ω N := by
    intro N hN
    obtain ⟨N', hN'⟩ := exists_pow_eq_map_expand (k' := k') p e N fun m => by
      by_cases hm : m ∈ N.support
      · exact hk'root _ (hN m hm)
      · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
        exact ⟨0, zero_pow hq.ne'⟩
    refine ⟨N', ?_⟩
    rw [← map_pow, hN', ← hθ, hψθ]
  have hcoeff : ∀ j i, ∃ d : F', algebraMap F' Ω d ^ q = algebraMap F Ω ((g j).coeff i) := by
    intro j i
    by_cases hc : (g j).coeff i = 0
    · exact ⟨0, by rw [hc, map_zero, map_zero, zero_pow hq.ne']⟩
    have hi : i ∈ Finset.range ((g j).natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hc))
    set c := (g j).coeff i
    obtain ⟨N', hN'⟩ := hrootB (num c) fun m hm => Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm)⟩⟩
    obtain ⟨D', hD'⟩ := hrootB (den c) fun m hm => Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)⟩⟩
    refine ⟨algebraMap B' F' N' / algebraMap B' F' D', ?_⟩
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_pow]
    change ψ N' ^ q / ψ D' ^ q = _
    rw [hN', hD']
    conv_rhs => rw [← hnd c]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

  let ω : Fin (Module.finrank F L) → Ω := fun j => algebraMap L Ω (b j)
  have hωsep : ∀ j, IsSeparable F' (ω j) := by
    intro j
    refine isSeparable_of_pow_coeff p e (g j) (hsepq (b j)) (ω j) ?_ (hcoeff j)
    rw [← map_pow, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  let E : IntermediateField F' Ω := IntermediateField.adjoin F' (Set.range ω)
  have : FiniteDimensional F' E := by
    have : Finite (Set.range ω) := Set.finite_range ω
    exact IntermediateField.finiteDimensional_adjoin fun x ⟨j, hj⟩ => hj ▸ (hωsep j).isIntegral
  have : Algebra.IsSeparable F' E :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable (F := F') (E := Ω)).mpr fun x ⟨j, hj⟩ => hj ▸ hωsep j
  have hLE : ∀ y : L, algebraMap L Ω y ∈ E := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr y, map_sum]
    refine sum_mem fun j _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    obtain ⟨c', hc'⟩ := hFF' (b.repr y j)
    rw [← hc']
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin F' _ ⟨j, rfl⟩)
  have : IsScalarTower B' F' Ω := FractionRing.isScalarTower_liftAlgebra B' Ω
  let : Algebra B' E := E.algebra'
  have : IsScalarTower B' F' E := IntermediateField.isScalarTower E
  have : IsScalarTower B' E Ω := IsScalarTower.of_algebraMap_eq fun x => rfl

  have hC' : Module.Finite B' (integralClosure B' E) :=
    IsIntegralClosure.finite B' F' E (integralClosure B' E)
  let S : Submodule B' Ω :=
    (integralClosure B' E).toSubmodule.map (IsScalarTower.toAlgHom B' E Ω).toLinearMap
  have hSfg : S.FG := (Module.Finite.iff_fg.mp hC').map _
  have : Module.Finite B (S.restrictScalars B) := Module.Finite.iff_fg.mpr hSfg.restrictScalars
  have : IsNoetherian B (S.restrictScalars B) := isNoetherian_of_isNoetherianRing_of_finite B (S.restrictScalars B)
  let φ : L →ₗ[B] Ω := (IsScalarTower.toAlgHom B L Ω).toLinearMap
  have hle : (integralClosure B L).toSubmodule.map φ ≤ S.restrictScalars B := by
    rintro _ ⟨y, hy, rfl⟩
    have hint : IsIntegral B' (algebraMap L Ω y) :=
      ((hy : IsIntegral B y).map (IsScalarTower.toAlgHom B L Ω)).tower_top
    refine ⟨⟨algebraMap L Ω y, hLE y⟩, ?_, rfl⟩
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B' E Ω)
      (algebraMap E Ω).injective).mp hint
  have : IsNoetherian B ((integralClosure B L).toSubmodule.map φ) := isNoetherian_of_le hle
  have hfg : ((integralClosure B L).toSubmodule.map φ).FG := Module.Finite.iff_fg.mp (Module.IsNoetherian.finite B _)
  exact Module.Finite.iff_fg.mpr
    (Submodule.fg_of_fg_map_injective φ (algebraMap L Ω).injective hfg)

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFiniteAlgebraLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Module

theorem FiniteAlgebraLengthSum.proof : FiniteAlgebraLengthSum.Statement := by
  classical
  intro A B _ _ _ _ _ ι _ 𝔪 h𝔪 hinj hall C _ _ hC α
  have : ∀ i, (𝔪 i).IsMaximal := h𝔪
  have : ∀ i, IsLocalization.AtPrime (C i) (𝔪 i) := hC
  have hrange : LinearMap.range (LinearMap.lsmul A B α) =
      (Ideal.span {algebraMap A B α}).restrictScalars A := by
    ext b
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton', Algebra.smul_def, mul_comm]
  rw [(Submodule.quotEquivOfEq _ _ hrange).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A B α})).length_eq,
    LengthSumLocalizations.length_eq_sum 𝔪 C hinj hall A]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ring.ord, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i)
    (Ideal.span {algebraMap A B α})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton]

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalizedQuotientLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

universe u v

theorem LocalizedQuotientLength.proof : LocalizedQuotientLength.Statement.{u, v} := by
  intro S _ P W _ x R _ _ hR
  let f : S →+* R := (algebraMap (S ⧸ P) R).comp (Ideal.Quotient.mk P)
  have hu : ∀ t : W.primeCompl, IsUnit (f t) := fun t => IsLocalization.map_units R
    (⟨Ideal.Quotient.mk P t, Submonoid.mem_map_of_mem _ t.2⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  let g : Localization.AtPrime W →+* R := IsLocalization.lift (M := W.primeCompl) hu
  have hg : ∀ s, g (algebraMap S (Localization.AtPrime W) s) = f s := IsLocalization.lift_eq hu
  have gsurj : Function.Surjective g := by
    intro r
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (W.primeCompl.map (Ideal.Quotient.mk P)) r
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t, ht, hmt⟩ := Submonoid.mem_map.mp m.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime W) s ⟨t, ht⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec, mul_comm]
    show algebraMap (S ⧸ P) R (Ideal.Quotient.mk P s) = _ * algebraMap (S ⧸ P) R (Ideal.Quotient.mk P t)
    rw [hmt, IsLocalization.mk'_spec]
  let _ : Algebra (Localization.AtPrime W) R := g.toAlgebra
  let _ : Algebra S R := f.toAlgebra
  have _ : IsScalarTower S (Localization.AtPrime W) R := IsScalarTower.of_algebraMap_eq fun s => (hg s).symm
  set J := Ideal.span {algebraMap (S ⧸ P) R (Ideal.Quotient.mk P x)}
  rw [← Module.length_eq_of_surjective (S := Localization.AtPrime W) (R := R) (M := R ⧸ J) gsurj]
  have hI : P ⊔ Ideal.span {x} ≤ LinearMap.ker (Algebra.linearMap S (R ⧸ J)) := by
    refine sup_le (fun p hp => ?_) (Ideal.span_le.2 ?_)
    · show Ideal.Quotient.mk J (algebraMap (S ⧸ P) R (Ideal.Quotient.mk P p)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero, map_zero]
    · rintro _ rfl
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  let φ : (S ⧸ (P ⊔ Ideal.span {x})) →ₗ[S] R ⧸ J := (P ⊔ Ideal.span {x}).liftQ _ hI
  have _ : IsLocalizedModule W.primeCompl φ := by
    constructor
    · intro t
      obtain ⟨u, hu'⟩ := hu t
      rw [Module.End.isUnit_iff]
      have key : ∀ q : R ⧸ J, algebraMap S (Module.End S (R ⧸ J)) t q = (u : R) • q := fun q => by
        rw [Module.algebraMap_end_apply, hu', ← algebraMap_smul R (t : S) q]; rfl
      refine ⟨fun a b hab => ?_, fun q => ⟨(↑u⁻¹ : R) • q, ?_⟩⟩
      · rw [key, key] at hab
        simpa [smul_smul] using congrArg ((↑u⁻¹ : R) • ·) hab
      · rw [key, smul_smul, Units.mul_inv, one_smul]
    · intro q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨z, rfl⟩ := gsurj r
      obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
      refine ⟨⟨Ideal.Quotient.mk _ s, t⟩, ?_⟩
      show Ideal.Quotient.mk J (f t * g (IsLocalization.mk' _ s t)) = Ideal.Quotient.mk J (f s)
      rw [← hg, ← hg, ← map_mul, IsLocalization.mk'_spec']
    · intro a1 a2 h
      obtain ⟨a1, rfl⟩ := Ideal.Quotient.mk_surjective a1
      obtain ⟨a2, rfl⟩ := Ideal.Quotient.mk_surjective a2
      change Ideal.Quotient.mk J (f a1) = Ideal.Quotient.mk J (f a2) at h
      rw [Ideal.Quotient.eq, ← map_sub, Ideal.mem_span_singleton'] at h
      obtain ⟨r, hr⟩ := h
      obtain ⟨z, rfl⟩ := gsurj r
      obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
      have e : f t * g (IsLocalization.mk' _ b t) = f b := by
        rw [← hg, ← hg, ← map_mul, IsLocalization.mk'_spec']
      have h2 : f (t * (a1 - a2) - b * x) = 0 := by
        rw [map_sub, map_mul, map_mul, ← hr, ← mul_assoc, e]
        exact sub_self _
      obtain ⟨⟨m, hm⟩, hm0⟩ := (IsLocalization.map_eq_zero_iff
        (W.primeCompl.map (Ideal.Quotient.mk P)) R (Ideal.Quotient.mk P _)).1 h2
      obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hm
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm0
      refine ⟨⟨u, hu⟩ * t, ?_⟩
      show Ideal.Quotient.mk _ ((u * t) * a1) = Ideal.Quotient.mk _ ((u * t) * a2)
      rw [Ideal.Quotient.eq, show u * t * a1 - u * t * a2 = u * (t * (a1 - a2) - b * x) + u * b * x by ring]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm0)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)))
  exact ((IsLocalizedModule.iso W.primeCompl φ).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u u' v v' w

section Objects

def HasRelDim {F : Type u} [Field F] {K : Type v} [Fintype K] {ι : K → Type w}
    (I : Ideal (MRing ι F)) (n : ℕ) : Prop :=
  ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)



end Objects


section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
end

