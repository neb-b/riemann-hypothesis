module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0059

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericLinearFormPrime
section
open MvPolynomial TensorProduct

noncomputable section

namespace GlobalTheory.GenericForm

variable (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (N : ℕ)

def polyEquiv : MvPolynomial (Fin N) k ⊗[k] A ≃+* MvPolynomial (Unit × Fin N) A :=
  ((Algebra.TensorProduct.comm k (MvPolynomial (Fin N) k) A).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv k A).toRingEquiv).trans
    (renameEquiv A (Equiv.punitProd (Fin N)).symm).toRingEquiv

theorem polyEquiv_X_tmul (i : Fin N) (x : A) :
    polyEquiv k A N (X i ⊗ₜ x) = C x * X ((), i) := by
  simp [polyEquiv, smul_eq_C_mul]

theorem polyEquiv_one_tmul (x : A) : polyEquiv k A N (1 ⊗ₜ x) = C x := by
  simp [polyEquiv, smul_eq_C_mul]

variable {k A N}

def genForm (a : Fin N → A) : MvPolynomial (Fin N) k ⊗[k] A := ∑ i, X i ⊗ₜ a i

theorem polyEquiv_genForm (a : Fin N → A) :
    polyEquiv k A N (genForm (k := k) a) = linForm a () := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [genForm, linForm, map_sum, polyEquiv_X_tmul]

theorem isDomain_tensor : IsDomain (MvPolynomial (Fin N) k ⊗[k] A) :=
  Function.Injective.isDomain (polyEquiv k A N).toRingHom
    (polyEquiv k A N).injective

theorem genForm_ne_zero (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) :
    genForm (k := k) a ≠ 0 := by
  intro h
  have h1 := congrArg (polyEquiv k A N) h
  rw [polyEquiv_genForm, map_zero, ← linFormEquiv_X_of_mem (ι := Unit) a hu (Set.mem_univ ())] at h1
  exact X_ne_zero _ ((linFormEquiv a Set.univ j hu).injective (h1.trans (map_zero _).symm))

theorem map_span_genForm (a : Fin N → A) :
    (Ideal.span {genForm (k := k) a}).map (polyEquiv k A N) = Ideal.span {linForm a ()} := by
  rw [Ideal.map_span, Set.image_singleton, polyEquiv_genForm]

theorem isPrime_span_genForm (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) :
    (Ideal.span {genForm (k := k) a}).IsPrime := by
  have hp : (Ideal.span {linForm a ()}).IsPrime := by
    have := isPrime_span_linForm (ι := Unit) a hu Set.univ
    rwa [Set.image_univ, Set.range_unique] at this
  have : Ideal.span {genForm (k := k) a} =
      (Ideal.span {linForm a ()}).map (polyEquiv k A N).symm := by
    rw [Ideal.map_span, Set.image_singleton, ← polyEquiv_genForm (k := k) a, RingEquiv.symm_apply_apply]
  rw [this]
  exact Ideal.map_isPrime_of_equiv _

theorem eq_zero_of_one_tmul_mem (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) {x : A}
    (hx : (1 : MvPolynomial (Fin N) k) ⊗ₜ[k] x ∈ Ideal.span {genForm (k := k) a}) : x = 0 := by
  have h1 := Ideal.mem_map_of_mem (polyEquiv k A N) hx
  rw [map_span_genForm, polyEquiv_one_tmul] at h1
  have h2 : C x ∈ RingHom.ker (linFormElim a hu (Set.univ : Set Unit)) := by
    rw [ker_linFormElim, Set.image_univ, Set.range_unique]
    exact h1
  rw [RingHom.mem_ker, algHom_C, algebraMap_eq, C_eq_zero] at h2
  exact h2

theorem span_genericForm_isPrime_or_eq_top :
    ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (N : ℕ) (a : Fin N → A)
      (j : Fin N), IsUnit (a j) → ∀ t : FractionRing (MvPolynomial (Fin N) k) ⊗[k] A,
      t = ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k))
        (MvPolynomial.X i) ⊗ₜ[k] a i →
      t ≠ 0 ∧ (Ideal.span {t} = ⊤ ∨ (Ideal.span {t}).IsPrime ∧
        ∀ x : A, (1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] x ∈ Ideal.span {t} → x = 0) := by
  intro k A _ _ _ _ N a j hu t ht
  let P := MvPolynomial (Fin N) k
  let K := FractionRing P
  let B := P ⊗[k] A
  haveI : IsDomain B := isDomain_tensor
  let φ : B →ₐ[k] K ⊗[k] A :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)
  letI : Algebra B (K ⊗[k] A) := φ.toRingHom.toAlgebra
  have hφ : ∀ x, algebraMap B (K ⊗[k] A) x = φ x := fun _ => rfl
  haveI : IsScalarTower P B (K ⊗[k] A) := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    rw [hφ]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have H : (algebraMap B (K ⊗[k] A)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    change φ (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  let M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors P)
  haveI hL : IsLocalization M (K ⊗[k] A) :=
    IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K H
  have hkA : Function.Injective (algebraMap k A) := (algebraMap k A).injective
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨p, hp, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp ?_
    refine Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := P) (B := A) hkA ?_
    rw [map_zero]
    exact h
  have hinj : Function.Injective (algebraMap B (K ⊗[k] A)) := IsLocalization.injective _ hM
  have ht0 : t = algebraMap B (K ⊗[k] A) (genForm (k := k) a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht, hφ, genForm, map_sum]
    rfl
  have hspan : Ideal.span {t} = (Ideal.span {genForm (k := k) a}).map (algebraMap B (K ⊗[k] A)) := by
    rw [Ideal.map_span, Set.image_singleton, ht0]
  refine ⟨?_, ?_⟩
  · rw [ht0]
    exact fun h => genForm_ne_zero (k := k) a hu (hinj (h.trans (map_zero _).symm))
  haveI hQ := isPrime_span_genForm (k := k) a hu
  by_cases hd : Disjoint (M : Set B) (Ideal.span {genForm (k := k) a} : Set B)
  · right
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hspan]
      exact IsLocalization.isPrime_of_isPrime_disjoint M (K ⊗[k] A) _ hQ hd
    · have h1 : (1 : K) ⊗ₜ[k] x = algebraMap B (K ⊗[k] A) ((1 : P) ⊗ₜ[k] x) := by
        rw [hφ, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      rw [h1, hspan] at hx
      have h2 := IsLocalization.under_map_of_isPrime_disjoint M (K ⊗[k] A) hQ hd
      have h3 : (1 : P) ⊗ₜ[k] x ∈ ((Ideal.span {genForm (k := k) a}).map
          (algebraMap B (K ⊗[k] A))).under B := hx
      rw [h2] at h3
      exact eq_zero_of_one_tmul_mem a hu h3
  · left
    obtain ⟨m, hmM, hmQ⟩ := Set.not_disjoint_iff.1 hd
    rw [hspan]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmQ)
      (IsLocalization.map_units (K ⊗[k] A) (⟨m, hmM⟩ : M))

end GlobalTheory.GenericForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecomp
section
open MeasureTheory MeasureTheory.Measure Topology Pointwise
open scoped ENNReal NNReal

namespace GlobalTheory.HaarQK

theorem lintegral_mul_right_modular {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] {f : H → ℝ≥0∞} (hf : Measurable f) (h : H) :
    ∫⁻ x, f (x * h) ∂ν = (modularCharacterFun h : ℝ≥0∞) * ∫⁻ x, f x ∂ν := by
  rw [← lintegral_map hf (measurable_mul_const h), map_right_mul_eq_modularCharacterFun_smul,
    lintegral_smul_measure]
  rfl

theorem secondCountable_subgroup {G : Type} [Group G] [TopologicalSpace G]
    [SecondCountableTopology G] (Q : Subgroup G) : SecondCountableTopology Q :=
  TopologicalSpace.Subtype.secondCountableTopology (Q : Set G)

attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem iter_right (u : G → ℝ≥0∞) (hu : Measurable u) (q₀ : Q) (k₀ : K) :
    ∫⁻ k, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν ∂κ =
      (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
  have e1 : ∀ k : K, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν =
      (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ q, u (q.1 * (k₀ * k).1) ∂ν := by
    intro k
    have hf : Measurable fun q : Q => u (q.1 * (k₀ * k).1) :=
      hu.comp ((continuous_subtype_val.mul continuous_const).measurable)
    rw [← lintegral_mul_right_modular ν hf q₀]
    congr 1
    ext q
    congr 1
    simp only [Subgroup.coe_mul]
    group
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  congr 1
  exact lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, u (q.1 * k.1) ∂ν) k₀

theorem iter_left (v : G → ℝ≥0∞) (q₀ : Q) (k₀ : K) :
    ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν ∂κ =
      ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν ∂κ := by
  haveI := GlobalTheory.isInvInvariant_of_compactSpace κ
  have e1 : ∀ k : K, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν =
      ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k⁻¹).1) ∂ν := by
    intro k
    have := lintegral_mul_left_eq_self
      (μ := ν) (fun q : Q => v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹)) q₀
    rw [← this]
    congr 1
    ext q
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  simp_rw [e1]
  have e2 := lintegral_inv_eq_self (μ := κ) (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k).1) ∂ν)
  rw [e2]
  exact lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν) k₀

end GlobalTheory.HaarQK

namespace GlobalTheory.HaarQK
attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem weil_exchange (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (u v : G → ℝ≥0∞) (hu : Measurable u) (hv : Measurable v) :
    ∫⁻ g, u g * ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ ∂μ =
      ∫⁻ g, v g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ := by
  have cF : Continuous fun x : G × (Q × K) => (x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹ := by fun_prop
  have cH : Continuous fun x : G × (Q × K) => x.2.1.1 * x.1 * x.2.2.1 := by fun_prop
  have mF : Measurable fun x : G × (Q × K) => u x.1 * v ((x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹) :=
    (hu.comp measurable_fst).mul (hv.comp cF.measurable)
  have mH : Measurable fun x : G × (Q × K) => u (x.2.1.1 * x.1 * x.2.2.1) * v x.1 :=
    (hu.comp cH.measurable).mul (hv.comp measurable_fst)
  have mv : ∀ g : G, Measurable fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) := fun g =>
    hv.comp (Continuous.measurable (by fun_prop))
  have mu : ∀ g : G, Measurable fun p : Q × K => u (p.1.1 * g * p.2.1) := fun g =>
    hu.comp (Continuous.measurable (by fun_prop))
  have p1 : ∀ g : G, ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ =
      ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) := fun g =>
    (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹))
      (mv g).aemeasurable).symm
  have p2 : ∀ g : G, ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ =
      ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) := fun g =>
    (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => u (p.1.1 * g * p.2.1))
      (mu g).aemeasurable).symm
  simp_rw [p1, p2]
  calc ∫⁻ g, u g * ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) ∂μ
      = ∫⁻ g, ∫⁻ p : Q × K, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) ∂μ := by
        congr 1; ext g
        exact (lintegral_const_mul _ (mv g)).symm
    _ = ∫⁻ p : Q × K, ∫⁻ g, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ ∂(ν.prod κ) :=
        lintegral_lintegral_swap mF.aemeasurable
    _ = ∫⁻ p : Q × K, ∫⁻ g, u (p.1.1 * g * p.2.1) * v g ∂μ ∂(ν.prod κ) := by
        congr 1; ext p
        set F : G → ℝ≥0∞ := fun g => u (p.1.1 * g * p.2.1) * v g with hF
        have h1 : ∫⁻ g, F ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ :=
          lintegral_mul_left_eq_self (fun g => F (g * (p.2.1)⁻¹)) _
        have h2 : ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F g ∂μ := lintegral_mul_right_eq_self F _
        rw [← h2, ← h1]
        congr 1; ext g
        simp only [hF]
        congr 1
        congr 1; group
    _ = ∫⁻ g, ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) * v g ∂(ν.prod κ) ∂μ :=
        lintegral_lintegral_swap (mH.comp measurable_swap).aemeasurable
    _ = ∫⁻ g, v g * ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) ∂μ := by
        congr 1; ext g
        rw [lintegral_mul_const _ (mu g), mul_comm]

end GlobalTheory.HaarQK

namespace GlobalTheory.HaarQK
attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem iter_indicator_pos_finite (hQ : IsClosed (Q : Set G)) {S : Set G} (hS : IsCompact S)
    (m : Q × K → G) (hm : Continuous m) (h1 : m 1 ∈ interior S) {C : Set G} (hC : IsCompact C)
    (hmC : ∀ p, m p ∈ S → (p.1 : G) ∈ C) :
    ∫⁻ k, ∫⁻ q, S.indicator 1 (m (q, k)) ∂ν ∂κ ≠ 0 ∧
      ∫⁻ k, ∫⁻ q, S.indicator 1 (m (q, k)) ∂ν ∂κ ≠ ⊤ := by
  have hmeas : Measurable fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p) :=
    (measurable_one.indicator hS.measurableSet).comp hm.measurable
  rw [← lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p))
    hmeas.aemeasurable]
  have e : (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p)) = (m ⁻¹' S).indicator 1 := by
    ext p; by_cases hp : m p ∈ S <;> simp [Set.indicator, hp]
  rw [e, lintegral_indicator_one (hm.measurable hS.measurableSet)]
  constructor
  · refine (lt_of_lt_of_le ?_ (measure_mono (Set.preimage_mono interior_subset))).ne'
    exact (hm.isOpen_preimage _ isOpen_interior).measure_pos (ν.prod κ) ⟨1, h1⟩
  · have hcpt : IsCompact ((Subtype.val ⁻¹' C : Set Q) ×ˢ (Set.univ : Set K)) :=
      (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hC).prod isCompact_univ
    refine (lt_of_le_of_lt (measure_mono ?_) hcpt.measure_lt_top).ne
    intro p hp
    exact ⟨hmC p hp, trivial⟩

end GlobalTheory.HaarQK

namespace GlobalTheory


open GlobalTheory.HaarQK in
attribute [local instance] secondCountable_subgroup in
theorem lintegral_haar_eq_mul_iterated_closed_compact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Q K : Subgroup G), IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) →
    ∀ (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ φ : G → ENNReal, Measurable φ → ∫⁻ g, φ g ∂μ = c * ∫⁻ k, ∫⁻ q, φ (q.1 * k.1) ∂ν ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec ν κ _ _
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨S, hS, hS1⟩ := exists_compact_mem_nhds (1 : G)
  have hS1' : (1 : G) ∈ interior S := mem_interior_iff_mem_nhds.mpr hS1
  set w : G → ℝ≥0∞ := S.indicator 1 with hw_def
  have hw : Measurable w := measurable_one.indicator hS.measurableSet

  obtain ⟨hσ0, hσT⟩ := iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => p.1.1 * p.2.1)
    (by fun_prop) (by simpa using hS1') (hS.mul hK) (by
      intro p hp
      have : (p.1 : G) = (p.1.1 * p.2.1) * (p.2.1)⁻¹ := by group
      rw [this]; exact Set.mul_mem_mul hp (K.inv_mem p.2.2))

  obtain ⟨hE0, hET⟩ := iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => (p.1.1)⁻¹ * p.2.1)
    (by fun_prop) (by simpa using hS1') (hK.mul hS.inv) (by
      intro p hp
      have : (p.1 : G) = p.2.1 * ((p.1.1)⁻¹ * p.2.1)⁻¹ := by group
      rw [this]; exact Set.mul_mem_mul p.2.2 (by simpa using hp))
  change ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ 0 at hσ0
  change ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ ⊤ at hσT
  change ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ 0 at hE0
  change ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ ⊤ at hET
  set σw := ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ with hσw
  set E := ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ with hE
  have hμw0 : ∫⁻ g, w g ∂μ ≠ 0 := by
    rw [hw_def, lintegral_indicator_one hS.measurableSet]
    exact (measure_pos_of_mem_nhds μ hS1).ne'
  have hμwT : ∫⁻ g, w g ∂μ ≠ ⊤ := by
    rw [hw_def, lintegral_indicator_one hS.measurableSet]
    exact hS.measure_lt_top.ne

  have key1 : ∀ u : G → ℝ≥0∞, Measurable u →
      (∫⁻ g, u g ∂μ) * E = ∫⁻ g, w g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ := by
    intro u hu
    rw [← weil_exchange ν κ μ u w hu hw, ← lintegral_mul_const _ hu]
    congr 1; ext g
    obtain ⟨q₀, hq₀, k₀, hk₀, rfl⟩ := hdec g
    rw [iter_left ν κ w ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]
  have key2 : ∀ u : G → ℝ≥0∞, Measurable u → ∀ g : G,
      (∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ) * σw =
        (∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
    intro u hu g
    obtain ⟨q₀, hq₀, k₀, hk₀, rfl⟩ := hdec g
    rw [iter_right ν κ u hu ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩, iter_right ν κ w hw ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]
    ring
  have mA : Measurable fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ := by
    have mf : Measurable fun x : G × (Q × K) => w (x.2.1.1 * x.1 * x.2.2.1) :=
      hw.comp (Continuous.measurable (by fun_prop))
    have e : (fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) =
        fun g => ∫⁻ p : Q × K, w (p.1.1 * g * p.2.1) ∂(ν.prod κ) := by
      funext g
      exact (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => w (p.1.1 * g * p.2.1))
        (mf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    rw [e]
    exact mf.lintegral_prod_right'
  have key : ∀ u : G → ℝ≥0∞, Measurable u →
      (∫⁻ g, u g ∂μ) * σw = (∫⁻ g, w g ∂μ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
    intro u hu
    have mwA : Measurable fun g => w g * ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ := hw.mul mA
    have h : (∫⁻ g, u g ∂μ) * E * σw = (∫⁻ g, w g ∂μ) * E * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
      rw [key1 u hu, key1 w hw, ← lintegral_mul_const' _ _ hσT,
        ← lintegral_mul_const _ mwA]
      congr 1; ext g
      rw [mul_assoc, key2 u hu g, ← mul_assoc]
    rw [mul_right_comm, mul_right_comm (∫⁻ g, w g ∂μ)] at h
    exact (ENNReal.mul_left_inj hE0 hET).mp h
  refine ⟨(∫⁻ g, w g ∂μ) / σw, ?_, ?_, ?_⟩
  · exact ENNReal.div_ne_zero.mpr ⟨hμw0, hσT⟩
  · exact ENNReal.div_ne_top hμwT hσ0
  · intro φ hφ
    rw [← ENNReal.mul_div_cancel_right (a := ∫⁻ g, φ g ∂μ) hσ0 hσT, key φ hφ, ENNReal.mul_div_right_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HartTensorOfFlat
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.HartFlatBaseChange

def divIdeal (A S X : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup X] [Module S X]
    (a : A) (y : X) : Ideal A where
  carrier := {u | ∃ x : X, algebraMap A S u • y = algebraMap A S a • x}
  add_mem' := by
    rintro u v ⟨x, hx⟩ ⟨x', hx'⟩
    exact ⟨x + x', by rw [map_add (f := _), add_smul, hx, hx', smul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c u ⟨x, hx⟩
    refine ⟨algebraMap A S c • x, ?_⟩
    rw [smul_eq_mul, map_mul, mul_smul, hx, smul_comm]

theorem lTensor_smul_id_apply (R M O : Type) [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    [Algebra R O] (r : R) (x : O ⊗[R] M) :
    (r • LinearMap.id : M →ₗ[R] M).lTensor O x = algebraMap R O r • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o n => simp [LinearMap.lTensor_tmul, algebraMap_smul, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

end GlobalTheory.HartFlatBaseChange

open GlobalTheory.HartFlatBaseChange in
theorem GlobalTheory.GoodEtale.hart_tensor_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  intro A R M O _ _ _ _ _ _ _ _ _ _ _ hM a ha m hm
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (divIdeal A O (O ⊗[R] M) a m) : Submodule.FG _)
  have hsI : ∀ b ∈ s, b ∈ divIdeal A O (O ⊗[R] M) a m := fun b hb => hs ▸ Ideal.subset_span hb
  let f : M →ₗ[R] M := algebraMap A R a • LinearMap.id
  let N : Submodule R M := LinearMap.range f
  let g : M →ₗ[R] (s → M ⧸ N) := LinearMap.pi fun i => N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id)
  have hex : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      have hyI : divIdeal A O (O ⊗[R] M) a m ≤ divIdeal A R M a y := by
        rw [← hs, Ideal.span_le]
        intro b hb
        have := congrFun hy ⟨b, hb⟩
        simp only [g, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range] at this
        obtain ⟨x, hx⟩ := this
        exact ⟨x, by simpa [f] using hx.symm⟩
      obtain ⟨m', hm'⟩ := hM a ha y fun p hp hp1 => by
        obtain ⟨u, hup, hu⟩ := hm p hp hp1
        exact ⟨u, hup, hyI hu⟩
      exact ⟨m', by simp [f, hm']⟩
    · rintro ⟨x, rfl⟩
      funext i
      simp only [g, f, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range]
      exact ⟨algebraMap A R i.1 • x, by simp [f, smul_comm (algebraMap A R a)]⟩
  have hexO := Module.Flat.lTensor_exact O hex
  have hcomp : ∀ (z : O ⊗[R] (s → M ⧸ N)) (i : s),
      TensorProduct.piRight R R O (fun _ : s => M ⧸ N) z i = (LinearMap.proj i).lTensor O z := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul o n => simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add x y hx hy => rw [map_add (f := _), Pi.add_apply, hx, hy, map_add (f := _)]
  have hg : g.lTensor O m = 0 := by
    apply (TensorProduct.piRight R R O (fun _ : s => M ⧸ N)).injective
    funext i
    rw [hcomp, map_zero, Pi.zero_apply, ← LinearMap.lTensor_comp_apply]
    have hpg : (LinearMap.proj i).comp g = N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id) := rfl
    obtain ⟨m', hm'⟩ := hsI i.1 i.2
    rw [hpg, LinearMap.lTensor_comp_apply, lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply,
      hm', IsScalarTower.algebraMap_apply A R O, ← lTensor_smul_id_apply, ← LinearMap.lTensor_comp_apply,
      LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨m', hm'⟩ := (hexO m).1 hg
  exact ⟨m', by rw [← hm', lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponential
section
open scoped ContDiff

namespace GlobalTheory

theorem hasDerivAt_of_continuous_additive_to_mul (χ : ℝ → ℂ) (hc : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) (h0 : χ 0 = 1) :
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first
  | exact @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | (apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add ..)

end GlobalTheory
end

