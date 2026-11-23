module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.LengthSumLocalizations
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Module TensorProduct

noncomputable section

namespace LengthSumLocalizations

variable {B : Type*} [CommRing B]

theorem algebraMap_quot_maximalIdeal_surjective (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*)
    [CommRing C] [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    Function.Surjective (algebraMap B (C ⧸ IsLocalRing.maximalIdeal C)) := by
  intro _ y
  obtain ⟨x, hx⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 C).surjective y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨b, by rw [← hx]; rfl⟩

theorem isSimpleModule_quot_maximalIdeal (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    IsSimpleModule B (C ⧸ IsLocalRing.maximalIdeal C) := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
  let : Field (C ⧸ IsLocalRing.maximalIdeal C) := Ideal.Quotient.field _
  rw [← Module.length_eq_one_iff,
    Module.length_eq_of_surjective (algebraMap_quot_maximalIdeal_surjective 𝔪 C)]
  exact Module.length_eq_one _ _

theorem isFiniteLength_of_atPrime (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] (M : Type*) [AddCommGroup M] [Module C M]
    [instB : Module B M] [instT : IsScalarTower B C M] (hM : IsFiniteLength C M) :
    IsFiniteLength B M := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
  revert instB instT
  induction hM with
  | of_subsingleton => intro _ _; exact .of_subsingleton
  | @of_simple_quotient M _ _ N hs hN ih =>
    intro _ _
    have hN' : IsFiniteLength B (N.restrictScalars B) := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain rfl := IsLocalRing.eq_maximalIdeal hI
    have := isSimpleModule_quot_maximalIdeal 𝔪 C
    have : IsSimpleModule B (M ⧸ N.restrictScalars B) :=
      IsSimpleModule.congr ((Submodule.Quotient.restrictScalarsEquiv B N).trans
        (e.restrictScalars B))
    exact .of_simple_quotient hN'

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal B) [h𝔪 : ∀ i, (𝔪 i).IsMaximal]
  (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)]
  [∀ i, IsLocalization.AtPrime (C i) (𝔪 i)]

omit [Fintype ι] in

omit [Fintype ι] in
theorem length_tensor_quot (hinj : Function.Injective 𝔪) (i j : ι) :
    Module.length (C i) (C i ⊗[B] (B ⧸ 𝔪 j)) = if i = j then 1 else 0 := by
  have : IsLocalRing (C i) := IsLocalization.AtPrime.isLocalRing (C i) (𝔪 i)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i) (𝔪 j)).toLinearEquiv.length_eq]
  split_ifs with h
  · subst h
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal (𝔪 i) (C i)]
    have : IsSimpleModule (C i) (C i ⧸ IsLocalRing.maximalIdeal (C i)) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  · have hne : ¬ 𝔪 j ≤ 𝔪 i := fun hle =>
      h (hinj ((h𝔪 j).eq_of_le (h𝔪 i).ne_top hle)).symm
    obtain ⟨x, hxj, hxi⟩ := Set.not_subset.mp hne
    have htop : (𝔪 j).map (algebraMap B (C i)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxj)
        (IsLocalization.map_units (C i) (⟨x, hxi⟩ : (𝔪 i).primeCompl))
    rw [htop, Module.length_eq_zero_iff]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl

omit [Fintype ι] [DecidableEq ι] in

omit [Fintype ι] [DecidableEq ι] in
theorem pi_mk_injective (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (N : Type*)
    [AddCommGroup N] [Module B N] :
    Function.Injective (LinearMap.pi fun i => TensorProduct.mk B (C i) N 1) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro n hn
  by_contra hne
  have hlt : LinearMap.ker (LinearMap.toSpanSingleton B N n) ≠ ⊤ := by
    intro htop
    apply hne
    have h1 : (1 : B) ∈ LinearMap.ker (LinearMap.toSpanSingleton B N n) := htop ▸ Submodule.mem_top
    simpa using h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hlt
  obtain ⟨i, rfl⟩ := hall M hM
  have : IsLocalizedModule (𝔪 i).primeCompl (TensorProduct.mk B (C i) N 1) :=
    (isLocalizedModule_iff_isBaseChange (𝔪 i).primeCompl (C i) _).mpr
      (TensorProduct.isBaseChange B N (C i))
  have h0 : TensorProduct.mk B (C i) N 1 n = 0 := by
    simpa using congrFun hn i
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (𝔪 i).primeCompl _).mp h0
  exact s.2 (hle (by rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hs))

theorem length_eq_sum_of_isFiniteLength (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [instA : Module A N] [instT : IsScalarTower A B N]
    (hN : IsFiniteLength B N) :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
  revert instA instT
  induction hN with
  | of_subsingleton => intro _ _; simp [Module.length_eq_zero]
  | @of_simple_quotient M _ _ P hs hP ih =>
    intro _ _
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain ⟨j, rfl⟩ := hall I hI
    let f : P →ₗ[B] M := P.subtype
    let g : M →ₗ[B] B ⧸ 𝔪 j := e.toLinearMap ∘ₗ P.mkQ
    have hf : Function.Injective f := P.subtype_injective
    have hg : Function.Surjective g := e.surjective.comp P.mkQ_surjective
    have hfg : Function.Exact f g := LinearMap.exact_iff.mpr (by
      rw [LinearEquiv.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype])
    have key : ∀ i, Module.length (C i) (C i ⊗[B] M) =
        Module.length (C i) (C i ⊗[B] P) + if i = j then 1 else 0 := by
      intro i
      have : Module.Flat B (C i) := IsLocalization.flat (C i) (𝔪 i).primeCompl
      rw [Module.length_eq_add_of_exact (AlgebraTensorModule.lTensor (C i) (C i) f)
        (AlgebraTensorModule.lTensor (C i) (C i) g)
        (Module.Flat.lTensor_preserves_injective_linearMap f hf)
        (LinearMap.lTensor_surjective (C i) hg) (Module.Flat.lTensor_exact (C i) hfg),
        length_tensor_quot 𝔪 C hinj i j]
    rw [Module.length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg, ih]
    simp only [key, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem length_eq_sum (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
  by_cases hN : IsFiniteLength B N
  · exact length_eq_sum_of_isFiniteLength 𝔪 C hinj hall A N hN
  have hA : Module.length A N = ⊤ := by
    by_contra hA
    apply hN
    have hA' := isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hA)
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hA'.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
  obtain ⟨i, hi⟩ : ∃ i, ¬ IsFiniteLength (C i) (C i ⊗[B] N) := by
    by_contra! h
    apply hN
    have hpi : Module.length B (∀ i, C i ⊗[B] N) ≠ ⊤ := by
      rw [Module.length_pi_of_fintype, ENat.sum_ne_top]
      exact fun i _ => Module.length_ne_top_iff.mpr
        (isFiniteLength_of_atPrime (𝔪 i) (C i) _ (h i))
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top hpi (Module.length_le_of_injective _ (pi_mk_injective 𝔪 C hall N))
  have : Nontrivial (B ⧸ 𝔪 i) := Ideal.Quotient.nontrivial_iff.mpr (h𝔪 i).ne_top
  have hd : Module.length A (B ⧸ 𝔪 i) ≠ 0 := (Module.length_pos (R := A)).ne'
  have hti : Module.length (C i) (C i ⊗[B] N) = ⊤ := by
    by_contra h'
    exact hi (Module.length_ne_top_iff.mp h')
  rw [hA, eq_comm, ← top_le_iff]
  calc (⊤ : ℕ∞) = Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
        rw [hti, ENat.top_mul hd]
    _ ≤ _ := Finset.single_le_sum (f := fun i =>
        Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i))
        (fun _ _ => zero_le) (Finset.mem_univ i)

end LengthSumLocalizations

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherCharPLemmas
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Polynomial

theorem exists_pow_eq_map_expand {σ k k' : Type*} [Field k] [Field k'] [Algebra k k'] (p : ℕ)
    [Fact p.Prime] [CharP k' p] (e : ℕ) (N : MvPolynomial σ k)
    (hN : ∀ m, ∃ z : k', z ^ p ^ e = algebraMap k k' (N.coeff m)) :
    ∃ N' : MvPolynomial σ k',
      N' ^ p ^ e = MvPolynomial.map (algebraMap k k') (MvPolynomial.expand (p ^ e) N) := by
  choose r hr using hN
  refine ⟨∑ m ∈ N.support, MvPolynomial.monomial m (r m), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPolynomial.map_iterateFrobenius_expand p, map_sum, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [N.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.expand_monomial, iterateFrobenius_def, hr]

theorem finite_mapExpand (k k' : Type*) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (σ : Type*) [Finite σ] (q : ℕ) (hq : 0 < q) :
    ((MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k k')).comp
      (MvPolynomial.expand q)).toRingHom.Finite := by
  set θ := (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k k')).comp (MvPolynomial.expand q)
  let : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := θ.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ k') :=
    IsScalarTower.of_algebraMap_eq fun x => (θ.commutes x).symm
  have hX : ∀ i, IsIntegral (MvPolynomial σ k) (MvPolynomial.X i : MvPolynomial σ k') := by
    intro i
    refine IsIntegral.of_pow hq ?_
    have : (MvPolynomial.X i : MvPolynomial σ k') ^ q =
        algebraMap (MvPolynomial σ k) (MvPolynomial σ k') (MvPolynomial.X i) := by
      change _ = θ (MvPolynomial.X i)
      simp [θ]
    rw [this]
    exact isIntegral_algebraMap
  have : Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ k') := by
    constructor
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
      have h1 : IsIntegral k (algebraMap k' (MvPolynomial σ k') a) :=
        (Algebra.IsIntegral.isIntegral (R := k) a).map (IsScalarTower.toAlgHom k k' _)
      rw [MvPolynomial.algebraMap_eq] at h1
      exact h1.tower_top
    | add f g hf hg => exact hf.add hg
    | mul_X f i hf => exact hf.mul (hX i)
  have : Algebra.FiniteType k (MvPolynomial σ k') :=
    Algebra.FiniteType.trans (S := k') inferInstance inferInstance
  have : Algebra.FiniteType (MvPolynomial σ k) (MvPolynomial σ k') :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  exact Algebra.IsIntegral.finite

theorem injective_of_isIntegral {B B' Ω : Type*} [CommRing B] [Nontrivial B] [CommRing B']
    [IsDomain B'] [CommRing Ω] [Algebra B B'] [Algebra.IsIntegral B B'] (ψ : B' →+* Ω)
    (h : Function.Injective (ψ.comp (algebraMap B B'))) : Function.Injective ψ := by
  have : RingHom.ker ψ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := B)
    rw [Ideal.under_def, RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).mp h
  exact (RingHom.injective_iff_ker_eq_bot ψ).mpr this

theorem isSeparable_of_pow_coeff {F F' Ω : Type*} [Field F] [Field F'] [Field Ω] [Algebra F Ω]
    [Algebra F' Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (e : ℕ) (g : F[X]) (hg : g.Separable)
    (ω : Ω) (hω : aeval (ω ^ p ^ e) g = 0)
    (hc : ∀ i, ∃ d : F', algebraMap F' Ω d ^ p ^ e = algebraMap F Ω (g.coeff i)) :
    IsSeparable F' ω := by
  choose d hd using hc
  set h : F'[X] := ∑ i ∈ Finset.range (g.natDegree + 1), C (d i) * X ^ i
  have hmap : (h.map (algebraMap F' Ω)).map (iterateFrobenius Ω p e) = g.map (algebraMap F Ω) := by
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h, coeff_map, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_X,
      map_C, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hi
    · rw [iterateFrobenius_def, hd]
    · rw [coeff_eq_zero_of_natDegree_lt (by simp at hi; omega), map_zero]
  have hsepΩ : (h.map (algebraMap F' Ω)).Separable := by
    rw [← separable_map (iterateFrobenius Ω p e), hmap]
    exact hg.map
  have hsep : h.Separable := (separable_map (algebraMap F' Ω)).mp hsepΩ
  have hroot : aeval ω h = 0 := by
    have : (aeval ω h) ^ p ^ e = 0 := by
      rw [aeval_def, ← eval_map, ← iterateFrobenius_def (R := Ω) p e, ← eval₂_hom,
        ← eval_map, hmap, eval_map, iterateFrobenius_def, ← aeval_def, hω]
    exact pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp this
  exact hsep.of_dvd (minpoly.dvd F' ω hroot)

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherReduction
section
set_option maxSynthPendingDepth 1

open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.FieldNumbers

universe u

theorem finite_integralClosure_of_forall_mvPolynomial
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L]
    (hpoly : ∀ (s : ℕ) (L' : Type u) [Field L'] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L']
      [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L']
      [Algebra (MvPolynomial (Fin s) k) L']
      [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L'],
      Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L')) :
    Module.Finite A (integralClosure A L) := by
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  set B := MvPolynomial (Fin s) k
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hgfin
  let : Algebra B K := ((algebraMap A K).comp (algebraMap B A)).toAlgebra
  let : Algebra B L := ((algebraMap A L).comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L (algebraMap B A x) = algebraMap K L (algebraMap A K (algebraMap B A x))
    exact IsScalarTower.algebraMap_apply A K L _
  have hinjBK : Function.Injective (algebraMap B K) :=
    (IsFractionRing.injective A K).comp hginj
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr hinjBK
  let : Algebra (FractionRing B) K := FractionRing.liftAlgebra B K
  let : Algebra (FractionRing B) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing B) K)).toAlgebra
  have : IsScalarTower (FractionRing B) K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B (FractionRing B) L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (FractionRing B) K L,
      ← IsScalarTower.algebraMap_apply B (FractionRing B) K,
      ← IsScalarTower.algebraMap_apply B K L]
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FiniteDimensional (FractionRing B) K := by
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule B A).FG)
    let T : Set K := algebraMap A K '' t
    have hTint : ∀ x ∈ T, IsIntegral (FractionRing B) x := by
      rintro _ ⟨a, -, rfl⟩
      have : IsIntegral B (algebraMap A K a) :=
        (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom B A K)
      exact this.tower_top
    have : Finite T := (t.finite_toSet.image _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing B) T = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing B) T := by
        intro a
        have ha : a ∈ Submodule.span B (t : Set A) := ht ▸ Submodule.mem_top
        induction ha using Submodule.span_induction with
        | mem y hy => exact IntermediateField.subset_adjoin (FractionRing B) T ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
        | smul b y _ hy =>
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply B (FractionRing B) K]
          exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing B) (E := K)).toLinearEquiv.finiteDimensional
  have : FiniteDimensional (FractionRing B) L := Module.Finite.trans K L
  have hB := hpoly s L
  have hle : (integralClosure A L).toSubmodule.restrictScalars B ≤
      (integralClosure B L).toSubmodule := fun y hy => isIntegral_trans (R := B) (A := A) y hy
  have : IsNoetherian B (integralClosure B L).toSubmodule :=
    isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B L)
  have : IsNoetherian B ((integralClosure A L).toSubmodule.restrictScalars B) :=
    isNoetherian_of_le hle
  have : Module.Finite B (integralClosure A L) :=
    Module.IsNoetherian.finite B ((integralClosure A L).toSubmodule.restrictScalars B)
  exact Module.Finite.of_restrictScalars_finite B A (integralClosure A L)

theorem finite_integralClosure_mvPolynomial_of_isSeparable (k : Type u) [Field k] (s : ℕ)
    (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra.IsSeparable (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) :=
  IsIntegralClosure.finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L
    (integralClosure (MvPolynomial (Fin s) k) L)

theorem finite_integralClosure_mvPolynomial_of_charZero (k : Type u) [Field k] [CharZero k]
    (s : ℕ) (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) := by
  have : CharZero (FractionRing (MvPolynomial (Fin s) k)) :=
    (RingHom.charZero_iff ((algebraMap (MvPolynomial (Fin s) k)
      (FractionRing (MvPolynomial (Fin s) k))).comp (algebraMap k (MvPolynomial (Fin s) k))).injective).mp
      inferInstance
  exact finite_integralClosure_mvPolynomial_of_isSeparable k s L

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFiniteAlgebraLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

def FiniteAlgebraLengthSum.Statement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (ι : Type u) [Fintype ι] (𝔪 : ι → Ideal B) (h𝔪 : ∀ i, (𝔪 i).IsMaximal),
    Function.Injective 𝔪 → (∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) →
    ∀ (C : ι → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)],
      (∀ i, haveI := (h𝔪 i).isPrime
        IsLocalization.AtPrime (C i) (𝔪 i)) →
      ∀ α : A,
        Module.length A (B ⧸ LinearMap.range (LinearMap.lsmul A B α)) =
          ∑ i, Ring.ord (C i) (algebraMap B (C i) (algebraMap A B α)) *
            Module.length A (B ⧸ 𝔪 i)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsLocalizedQuotientLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u v

def LocalizedQuotientLength.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (P W : Ideal S) [W.IsPrime] (x : S) (R : Type v) [CommRing R]
    [Algebra (S ⧸ P) R], IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) R →
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (S ⧸ (P ⊔ Ideal.span {x}))) =
        Module.length R (R ⧸ Ideal.span {algebraMap (S ⧸ P) R (Ideal.Quotient.mk P x)})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsNoetherIntegralClosure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

universe u

def NoetherIntegralClosureFinite.Statement : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L],
    Module.Finite A (integralClosure A L)

end GroundTheory.Heights₂.Heights.FieldNumbers
end

