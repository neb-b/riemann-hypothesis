module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFreenessLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace GenericFreeness

open Module

universe u

variable {A : Type u} [CommRing A]

def IsGenericallyFree (A : Type u) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

theorem free_iff_of_isLocalizedModule (f : A) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers f) g]
    (Rf : Type*) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf] [Module Rf N]
    [IsScalarTower A Rf N] :
    Module.Free Rf N ↔ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  let e₁ : Localization.Away f ≃+* Rf :=
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) Rf).toRingEquiv
  let e₂ : LocalizedModule (Submonoid.powers f) M ≃ₗ[A] N := IsLocalizedModule.iso _ g
  have key : ∀ (r : Localization.Away f) (x : LocalizedModule (Submonoid.powers f) M),
      e₂ (r • x) = e₁ r • e₂ x := by
    intro r x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) r
    have hs := IsLocalizedModule.map_units g s
    rw [Module.End.isUnit_iff] at hs
    apply hs.1
    simp only [Module.algebraMap_end_apply]
    have h1 : (s : A) • IsLocalization.mk' (Localization.Away f) a s = algebraMap A _ a := by
      rw [Algebra.smul_def, IsLocalization.mk'_spec']
    have h2 : (s : A) • e₁ (IsLocalization.mk' (Localization.Away f) a s) = algebraMap A Rf a := by
      have : e₁ (IsLocalization.mk' (Localization.Away f) a s) = IsLocalization.mk' Rf a s :=
        IsLocalization.algEquiv_mk' _ _
      rw [this, Algebra.smul_def, IsLocalization.mk'_spec']
    rw [← map_smul, ← smul_assoc, h1, algebraMap_smul, ← smul_assoc, h2, algebraMap_smul, map_smul]
  haveI := RingHomInvPair.of_ringEquiv e₁
  haveI := RingHomInvPair.of_ringEquiv_symm e₁
  let e : LinearEquiv (e₁ : Localization.Away f →+* Rf) (LocalizedModule (Submonoid.powers f) M) N :=
    { e₂.toAddEquiv with map_smul' := fun r x ↦ key r x }
  exact (Module.Free.iff_of_equiv e).symm

theorem isLocalizedModule_powers_mul (a c : A) {M N P : Type*} [AddCommGroup M] [Module A M]
    {Ra : Type*} [CommRing Ra] [Algebra A Ra] [IsLocalization.Away a Ra]
    [AddCommGroup N] [Module A N] [Module Ra N] [IsScalarTower A Ra N]
    [AddCommGroup P] [Module A P] [Module Ra P] [IsScalarTower A Ra P]
    (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers a) g]
    (h : N →ₗ[Ra] P) [IsLocalizedModule (Submonoid.powers (algebraMap A Ra c)) h] :
    IsLocalizedModule (Submonoid.powers (a * c)) (h.restrictScalars A ∘ₗ g) := by
  have hh : IsLocalizedModule (Submonoid.powers c) (h.restrictScalars A) :=
    IsLocalizedModule.restrictScalars_powers c h
  have ha : IsUnit (algebraMap A (Module.End A P) a) := by
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Ra) a
    rw [Module.End.isUnit_iff]
    have hb : Function.Bijective (fun p : P ↦ (u : Ra) • p) := by
      refine ⟨fun p q hpq ↦ ?_, fun p ↦ ⟨(↑u⁻¹ : Ra) • p, ?_⟩⟩
      · have := congr_arg (fun x : P ↦ (↑u⁻¹ : Ra) • x) hpq
        simpa only [smul_smul, Units.inv_mul, one_smul] using this
      · show (u : Ra) • ((↑u⁻¹ : Ra) • p) = p
        rw [smul_smul, Units.mul_inv, one_smul]
    convert hb using 1
    funext p
    simp [hu]
  have hc : IsUnit (algebraMap A (Module.End A P) c) :=
    hh.map_units ⟨c, Submonoid.mem_powers c⟩
  constructor
  · rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap A (Module.End A P) ((a * c) ^ k))
    rw [map_pow, map_mul]
    exact (ha.mul hc).pow k
  · intro y
    obtain ⟨⟨n, ⟨_, j, rfl⟩⟩, hn⟩ := hh.surj y
    obtain ⟨⟨m, ⟨_, i, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers a) g n
    refine ⟨⟨(a ^ j * c ^ i) • m, ⟨(a * c) ^ (i + j), i + j, rfl⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at hn hm ⊢
    have e1 : (h.restrictScalars A ∘ₗ g) ((a ^ j * c ^ i) • m) =
        (a ^ j * c ^ i * a ^ i) • (h.restrictScalars A) n := by
      rw [LinearMap.comp_apply, map_smul, ← hm, map_smul, map_smul, smul_smul]
    rw [e1, ← hn, smul_smul]
    congr 1
    ring
  · intro m₁ m₂ e
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := hh.exists_of_eq e
    simp only [Submonoid.smul_def] at hj
    rw [← map_smul, ← map_smul] at hj
    obtain ⟨⟨_, i, rfl⟩, hi⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers a) (f := g) hj
    refine ⟨⟨(a * c) ^ (i + j), i + j, rfl⟩, ?_⟩
    simp only [Submonoid.smul_def] at hi ⊢
    have : (a * c) ^ (i + j) = a ^ j * c ^ i * (a ^ i * c ^ j) := by ring
    rw [this]
    simp only [mul_smul (a ^ j * c ^ i), mul_smul (a ^ i) (c ^ j), hi]

theorem free_away_mul {f : A} (g : A) {M : Type*} [AddCommGroup M] [Module A M]
    (hf : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free (Localization.Away (f * g)) (LocalizedModule (Submonoid.powers (f * g)) M) := by
  let Ra := Localization.Away f
  let N := LocalizedModule (Submonoid.powers f) M
  let T := Localization.Away (algebraMap A Ra g)
  let P := LocalizedModule (Submonoid.powers (algebraMap A Ra g)) N
  have hP : Module.Free T P :=
    Module.free_of_isLocalizedModule (Submonoid.powers (algebraMap A Ra g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N)
  haveI := isLocalizedModule_powers_mul f g (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N)
  exact (free_iff_of_isLocalizedModule (f * g)
    ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N).restrictScalars A ∘ₗ
      LocalizedModule.mkLinearMap (Submonoid.powers f) M) T).1 hP

theorem IsGenericallyFree.of_linearEquiv {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (e : M ≃ₗ[A] M') (hM : IsGenericallyFree A M) : IsGenericallyFree A M' := by
  obtain ⟨f, hf, hfree⟩ := hM
  refine ⟨f, hf, ?_⟩
  exact (free_iff_of_isLocalizedModule f
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M ∘ₗ e.symm.toLinearMap) (Localization.Away f)).1 hfree

theorem isGenericallyFree_of_smul_eq_zero {M : Type*} [AddCommGroup M] [Module A M] (a : A) (ha : a ≠ 0)
    (h : ∀ m : M, a • m = 0) : IsGenericallyFree A M := by
  refine ⟨a, ha, ?_⟩
  have h0 : ∀ x : LocalizedModule (Submonoid.powers a) M, x = 0 := fun x ↦ by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      exact LocalizedModule.eq_zero_of_smul_eq_zero a (Submonoid.mem_powers a) _
        (by rw [LocalizedModule.smul'_mk, h, LocalizedModule.zero_mk])
  haveI : Subsingleton (LocalizedModule (Submonoid.powers a) M) := ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
  infer_instance

theorem isGenericallyFree_of_free [Nontrivial A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M] :
    IsGenericallyFree A M :=
  ⟨1, one_ne_zero, Module.free_of_isLocalizedModule (Submonoid.powers (1 : A))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : A)) M)⟩

theorem IsGenericallyFree.of_injective [IsDomain A] {N M : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M]
    [Module A M] (i : N →ₗ[A] M) (hi : Function.Injective i) (a : A) (ha : a ≠ 0)
    (hsat : ∀ m : M, ∃ k : ℕ, a ^ k • m ∈ LinearMap.range i) (hN : IsGenericallyFree A N) :
    IsGenericallyFree A M := by
  obtain ⟨f, hf, hfree⟩ := hN
  have hfree' := free_away_mul a hfree
  set F := f * a with hF
  refine ⟨F, mul_ne_zero hf ha, ?_⟩
  haveI : IsLocalizedModule (Submonoid.powers F) (LocalizedModule.mkLinearMap (Submonoid.powers F) M ∘ₗ i) := by
    constructor
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers F) M)
    · intro y
      obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (Submonoid.powers F)
        (LocalizedModule.mkLinearMap (Submonoid.powers F) M) y
      obtain ⟨k, n, hn⟩ := hsat m
      refine ⟨⟨f ^ k • n, ⟨F ^ k, k, rfl⟩ * s⟩, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, LinearMap.coe_comp, Function.comp_apply,
        map_smul, hn] at hms ⊢
      rw [mul_smul, hms, ← map_smul, smul_smul, hF, mul_pow]
      exact map_smul _ _ _
    · intro n₁ n₂ e
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers F)
        (f := LocalizedModule.mkLinearMap (Submonoid.powers F) M) e
      refine ⟨c, hi ?_⟩
      simpa only [Submonoid.smul_def, map_smul] using hc
  exact (free_iff_of_isLocalizedModule F
    (LocalizedModule.mkLinearMap (Submonoid.powers F) M ∘ₗ i) (Localization.Away F)).2 hfree'

theorem IsGenericallyFree.of_exact [IsDomain A] {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] (i : N₁ →ₗ[A] N₂) (p : N₂ →ₗ[A] N₃)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (h₁ : IsGenericallyFree A N₁) (h₃ : IsGenericallyFree A N₃) : IsGenericallyFree A N₂ := by
  obtain ⟨f₁, hf₁, hfree₁⟩ := h₁
  obtain ⟨f₃, hf₃, hfree₃⟩ := h₃
  have free₁ := free_away_mul f₃ hfree₁
  have free₃ := free_away_mul f₁ hfree₃
  rw [mul_comm f₃ f₁] at free₃
  set f := f₁ * f₃
  refine ⟨f, mul_ne_zero hf₁ hf₃, ?_⟩
  let S := Submonoid.powers f
  let iL : LocalizedModule S N₁ →ₗ[Localization.Away f] LocalizedModule S N₂ :=
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N₁) (LocalizedModule.mkLinearMap S N₂) i).extendScalarsOfIsLocalization S (Localization.Away f)
  let pL : LocalizedModule S N₂ →ₗ[Localization.Away f] LocalizedModule S N₃ :=
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N₂) (LocalizedModule.mkLinearMap S N₃) p).extendScalarsOfIsLocalization S (Localization.Away f)
  have ex : Function.Exact iL pL := LocalizedModule.map_exact S i p hex
  have hiL : Function.Injective iL := IsLocalizedModule.map_injective S _ _ i hi
  have hpL : Function.Surjective pL := IsLocalizedModule.map_surjective S _ _ p hp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property pL LinearMap.id hpL
  exact Module.Free.of_equiv (ex.splitSurjectiveEquiv hiL ⟨s, hs⟩).1.symm

end GenericFreeness

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PrimitiveLinearForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Polynomial TensorProduct

noncomputable section

namespace PrimitiveLinearForm

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]

abbrev tensorRightAlgebra : Algebra B (FractionRing R ⊗[R] B) := Algebra.TensorProduct.rightAlgebra

attribute [local instance] tensorRightAlgebra

theorem isLocalization_tensor :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (FractionRing R ⊗[R] B) := by
  refine isLocalizedModule_iff_isLocalization.mp ?_
  have h := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) (FractionRing R)
    (IsScalarTower.toAlgHom R B (FractionRing R ⊗[R] B)).toLinearMap).mpr ?_
  · exact h
  · exact TensorProduct.isBaseChange R B (FractionRing R)

theorem exists_linear_primitive {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {n : ℕ} (ι : ℂ →+* K) (x : Fin n → L)
    (hx : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K, (∀ j, φ (x j) = ψ (x j)) → φ = ψ) :
    ∃ c : Fin n → ℂ, IntermediateField.adjoin K {∑ j, algebraMap K L (ι (c j)) * x j} = ⊤ := by
  classical
  let A := AlgebraicClosure K
  let ι' : ℂ →+* A := (algebraMap K A).comp ι
  let p : (L →ₐ[K] A) × (L →ₐ[K] A) → Polynomial A := fun φψ =>
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (φψ.1 (x j) - φψ.2 (x j))
  have hp : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), φψ.1 ≠ φψ.2 → p φψ ≠ 0 := by
    intro φψ hne h
    apply hne
    apply hx
    intro j
    have hc := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q (j : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [sub_eq_zero] using hc
    · intro b _ hb
      simp [Finsupp.single_apply, show (b : ℕ) ≠ (j : ℕ) from fun h => hb (Fin.ext h)]
    · simp
  have hev : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), ∀ t : A,
      (p φψ).eval t = ∑ j : Fin n, (φψ.1 (x j) - φψ.2 (x j)) * t ^ (j : ℕ) := by
    intro φψ t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  let S : Finset A := (Finset.univ.filter (fun φψ : (L →ₐ[K] A) × (L →ₐ[K] A) => φψ.1 ≠ φψ.2)).biUnion
    (fun φψ => (p φψ).roots.toFinset)
  have hSf : {t : ℂ | ι' t ∈ S}.Finite :=
    (S.finite_toSet.preimage (ι'.injective.injOn))
  obtain ⟨t, ht⟩ := hSf.infinite_compl.nonempty
  refine ⟨fun j => t ^ (j : ℕ), ?_⟩
  have hA : ∀ y : L, ((minpoly K y).map (algebraMap K A)).Splits := fun y => IsAlgClosed.splits _
  rw [Field.primitive_element_iff_algHom_eq_of_eval' K A hA]
  intro φ ψ hφψ
  by_contra hne
  apply ht
  simp only [Set.mem_ofPred_eq, S, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(φ, ψ), hne, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp (φ, ψ) hne), Polynomial.IsRoot, hev]
  have h1 : ∀ χ : L →ₐ[K] A, χ (∑ j : Fin n, algebraMap K L (ι (t ^ (j : ℕ))) * x j) =
      ∑ j : Fin n, ι' t ^ (j : ℕ) * χ (x j) := by
    intro χ
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_mul, AlgHom.commutes, ι', map_pow]
  have h2 := congrArg id hφψ
  simp only [id] at h2
  rw [h1, h1] at h2
  rw [← sub_eq_zero] at h2
  rw [← h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_primitive_data {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B)) (ι : ℂ →+* R) {n : ℕ} (x : Fin n → B)
    (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    ∃ (c : Fin n → ℂ) (m : R[X]) (D : R) (Q : Fin n → R[X]),
      m.Monic ∧ m.natDegree = Module.finrank (FractionRing R) (FractionRing R ⊗[R] B) ∧
      (∀ p : R[X], aeval (∑ j, algebraMap R B (ι (c j)) * x j) p = 0 ↔ m ∣ p) ∧
      D ≠ 0 ∧ (∃ a b : R[X], a * m + b * derivative m = C D) ∧
      ∀ j, algebraMap R B D * x j = aeval (∑ j, algebraMap R B (ι (c j)) * x j) (Q j) := by
  classical
  let K := FractionRing R
  let L := K ⊗[R] B
  let _ : Algebra B L := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) L :=
    isLocalization_tensor R B
  have hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors R) ≤ nonZeroDivisors B := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hr (hinj (by rw [h, map_zero])))
  have : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors L hM
  have hBL : Function.Injective (algebraMap B L) := IsLocalization.injective L hM
  have : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  let _ : Field L := (isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)).toField
  let ιK : ℂ →+* K := (algebraMap R K).comp ι
  have : CharZero K := ⟨fun a b h => by
    have h' : ιK (a : ℂ) = ιK (b : ℂ) := by simpa [map_natCast] using h
    exact_mod_cast ιK.injective h'⟩
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hxgen : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K,
      (∀ j, φ (algebraMap B L (x j)) = ψ (algebraMap B L (x j))) → φ = ψ := by
    intro φ ψ h
    have h1 : (φ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) =
        (ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) := by
      apply AlgHom.ext_of_adjoin_eq_top hx
      rintro _ ⟨j, rfl⟩
      exact h j
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
    exact RingHom.ext fun b => AlgHom.congr_fun h1 b
  obtain ⟨c, hc⟩ := exists_linear_primitive ιK (fun j => algebraMap B L (x j)) hxgen
  refine ⟨c, ?_⟩
  set ℓ : B := ∑ j, algebraMap R B (ι (c j)) * x j with hℓ
  have hℓL : algebraMap B L ℓ = ∑ j, algebraMap K L (ιK (c j)) * algebraMap B L (x j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]
    rfl
  rw [← hℓL] at hc
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  have hint : IsIntegral R ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hmK : minpoly K (algebraMap B L ℓ) = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    rw [← (minpoly.monic hint).natDegree_map (algebraMap R K), ← hmK]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq K _).mp hc
  have : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hdiv : ∀ p : R[X], aeval ℓ p = 0 ↔ minpoly R ℓ ∣ p := fun p =>
    ⟨minpoly.isIntegrallyClosed_dvd hint, fun ⟨q, hq⟩ => by rw [hq, map_mul, minpoly.aeval, zero_mul]⟩

  have hirr : Irreducible ((minpoly R ℓ).map (algebraMap R K)) :=
    hmK ▸ minpoly.irreducible (IsIntegral.of_finite K _)
  have hsep : IsCoprime ((minpoly R ℓ).map (algebraMap R K))
      (derivative ((minpoly R ℓ).map (algebraMap R K))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  rw [Polynomial.derivative_map] at hab
  obtain ⟨α, hα, hαa⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨β, hβ, hβb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  have hinjK : Function.Injective (Polynomial.map (algebraMap R K)) :=
    Polynomial.map_injective _ (IsFractionRing.injective R K)
  have hid : C β * IsLocalization.integerNormalization (nonZeroDivisors R) a * minpoly R ℓ +
      C α * IsLocalization.integerNormalization (nonZeroDivisors R) b * derivative (minpoly R ℓ) =
      C (α * β) := by
    apply hinjK
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, hαa, hβb,
      Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
    linear_combination (C (algebraMap R K α) * C (algebraMap R K β)) * hab

  have hmem : ∀ j, ∃ P : K[X], aeval (algebraMap B L ℓ) P = algebraMap B L (x j) := by
    intro j
    have h1 : algebraMap B L (x j) ∈ (IntermediateField.adjoin K {algebraMap B L ℓ}).toSubalgebra := by
      rw [hc]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨P, hP⟩ := h1
    exact ⟨P, hP⟩
  choose P hP using hmem
  have hclear : ∀ j, ∃ e ∈ nonZeroDivisors R, ∃ P' : R[X], aeval ℓ P' = algebraMap R B e * x j := by
    intro j
    obtain ⟨e, he, hPe⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) (P j)
    refine ⟨e, he, IsLocalization.integerNormalization (nonZeroDivisors R) (P j), hBL ?_⟩
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap K, hPe,
      Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.aeval_C, hP j, map_mul,
      ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]
  choose e he Q' hQ' using hclear
  refine ⟨minpoly R ℓ, α * β * ∏ j, e j,
    fun j => C (α * β * ∏ k ∈ Finset.univ.erase j, e k) * Q' j, minpoly.monic hint, hdeg, hdiv,
    ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero (nonZeroDivisors.ne_zero hα) (nonZeroDivisors.ne_zero hβ)) ?_
    exact Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.ne_zero (he j)
  · refine ⟨C (∏ j, e j) * (C β * IsLocalization.integerNormalization (nonZeroDivisors R) a),
      C (∏ j, e j) * (C α * IsLocalization.integerNormalization (nonZeroDivisors R) b), ?_⟩
    rw [C_mul (a := α * β)]
    linear_combination C (∏ j, e j) * hid
  · intro j
    rw [map_mul (aeval ℓ), Polynomial.aeval_C, hQ' j, ← Finset.mul_prod_erase Finset.univ e
      (Finset.mem_univ j)]
    simp only [map_mul]
    ring

end PrimitiveLinearForm

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

def areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) : ℝ :=
  √(LinearMap.det (LinearMap.adjoint L ∘ₗ L))

def AreaMultiplicity.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k → finrank ℝ F = k →
    ∀ (A : Set E) (f : E → F) (f' : E → E →L[ℝ] F), MeasurableSet A →
      (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      ∫⁻ x in A, ENNReal.ofReal (areaJacobian (f' x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)]) =
        ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂(μH[(k : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAuslanderBuchsbaumDepthLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

def AuslanderBuchsbaumDepthLower.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (ℓ : ℕ) (rs : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) ℓ → (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs →
      ∃ ms : List R, (∀ r ∈ ms, r ∈ maximalIdeal R) ∧ IsWeaklyRegular M ms ∧ ms.length = rs.length - ℓ

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAuslanderBuchsbaumProjDimUpper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

def AuslanderBuchsbaumProjDimUpper.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (n d : ℕ) (ms : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) n →
    (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
    (∀ r ∈ ms, r ∈ maximalIdeal R) → IsWeaklyRegular M ms →
      HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBrouwerFixedPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def BrouwerFixedPoint.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℝ) → Fin n → ℝ),
    ContinuousOn f (Metric.closedBall 0 1) →
      Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1) →
        ∃ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, f x = x

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

