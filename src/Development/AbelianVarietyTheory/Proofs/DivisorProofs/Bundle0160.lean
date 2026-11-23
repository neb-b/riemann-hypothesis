module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0080

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalDomainUnfoldRefoldMeasure
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem lintegral_unfold_refold (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X]
    [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
  haveI : MeasurableConstSMul Γ X :=
    ⟨fun c => (measurable_const_smul (c : S) : Measurable fun x : X => (c : S) • x)⟩
  haveI : SMulInvariantMeasure Γ X μ :=
    ⟨fun c A hA => SMulInvariantMeasure.measure_preimage_smul (c : S) hA⟩
  haveI : MeasurableConstSMul Γ S :=
    ⟨fun c => (measurable_const_mul (c : S) : Measurable fun x : S => (c : S) * x)⟩
  haveI : SMulInvariantMeasure Γ S ν :=
    ⟨fun c A _ => measure_preimage_mul ν (c : S) A⟩
  set F : X → ℝ≥0∞ := fun y => ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) with hF
  have hQ : MeasurableSet {p : X × S | p.2 ∈ E ∧ p.2⁻¹ • p.1 ∈ D₁} :=
    (measurable_snd hE).inter (hD₁.preimage (measurable_snd.inv.smul measurable_fst))
  have hmeasν : Measurable fun y : X => ν (E ∩ {s | s⁻¹ • y ∈ D₁}) := by
    have := measurable_measure_prodMk_left (ν := ν) hQ
    exact this
  have hFm : Measurable F := hψ.mul hmeasν
  have hstep : ∀ y : X, ∑' γ : Γ, F (γ • y) = ψ y * ν {s | s⁻¹ • y ∈ D₁} := by
    intro y
    have h1 : ∀ γ : Γ, F (γ • y) = ψ y * ν (E ∩ {s | s⁻¹ • ((γ : S) • y) ∈ D₁}) := by
      intro γ
      simp only [hF, Subgroup.smul_def, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [hEf.measure_eq_tsum {s | s⁻¹ • y ∈ D₁}]
    refine tsum_congr fun γ => ?_
    congr 1
    ext s
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq,
      Subgroup.smul_def, smul_eq_mul, mul_inv_rev, inv_inv, mul_smul]
    exact and_comm
  calc ∫⁻ y, F y ∂μ = ∑' γ : Γ, ∫⁻ y in D₂, F (γ • y) ∂μ := hD₂.lintegral_eq_tsum'' F
    _ = ∫⁻ y in D₂, ∑' γ : Γ, F (γ • y) ∂μ := by
      rw [lintegral_tsum]
      intro γ
      exact (hFm.comp (measurable_const_smul γ)).aemeasurable
    _ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
      simp_rw [hstep]

end GlobalTheory.CovolIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulMeasureInterSmulPreimageOfInvariant
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory

theorem lintegral_mul_measure_inter_smul_preimage :
    ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (D : Set X), MeasurableSet D → ∀ (E : Set S), MeasurableSet E → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
  intro S X _ _ _ _ _ _ ν _ μ _ _ D hD E hE ψ hψ hinv
  have hmeas : Measurable (Function.uncurry fun (s : S) (y : X) =>
      ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y))) := by
    have hsm' : Measurable (fun p : S × X => p.1⁻¹ • p.2) :=
      (measurable_fst.inv).smul measurable_snd
    refine (hψ.comp measurable_snd).mul ?_
    exact ((measurable_one.indicator hE).comp measurable_fst).mul
      ((measurable_one.indicator hD).comp hsm')
  have h1 : ∀ y : X, ν (E ∩ {s | s⁻¹ • y ∈ D}) =
      ∫⁻ s, E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂ν := by
    intro y
    have hm : MeasurableSet (E ∩ {s : S | s⁻¹ • y ∈ D}) :=
      hE.inter (hD.preimage (measurable_inv.smul_const y))
    rw [← lintegral_indicator_one hm]
    congr 1; ext s
    by_cases h1 : s ∈ E <;> by_cases h2 : s⁻¹ • y ∈ D <;> simp [Set.indicator, h1, h2]
  have h2 : ∀ s : S, ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ = ∫⁻ x in D, ψ x ∂μ := by
    intro s
    have hf : Measurable (fun x : X => ψ x * D.indicator (1 : X → ℝ≥0∞) x) :=
      hψ.mul (measurable_one.indicator hD)
    calc ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ
        = ∫⁻ y, (fun x : X => ψ x * D.indicator (1 : X → ℝ≥0∞) x) (s⁻¹ • y) ∂μ := by
          congr 1; ext y; simp only [hinv]
      _ = ∫⁻ x, ψ x * D.indicator (1 : X → ℝ≥0∞) x ∂μ :=
          (measurePreserving_smul s⁻¹ μ).lintegral_comp hf
      _ = ∫⁻ x in D, ψ x ∂μ := by
          rw [← lintegral_indicator hD]
          congr 1; ext x
          by_cases hx : x ∈ D <;> simp [Set.indicator, hx]
  calc ν E * ∫⁻ x in D, ψ x ∂μ
      = ∫⁻ s, E.indicator (1 : S → ℝ≥0∞) s * ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ ∂ν := by
        simp only [h2]
        rw [lintegral_mul_const _ (measurable_one.indicator hE), lintegral_indicator_one hE]
    _ = ∫⁻ s, ∫⁻ y, ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) ∂μ ∂ν := by
        congr 1; ext s
        rw [← lintegral_const_mul' _ _ (by by_cases h : s ∈ E <;> simp [Set.indicator, h])]
        congr 1; ext y; ring
    _ = ∫⁻ y, ∫⁻ s, ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) ∂ν ∂μ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
        congr 1; ext y
        have hm : Measurable (fun s : S =>
            E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) :=
          (measurable_one.indicator hE).mul
            ((measurable_one.indicator hD).comp (measurable_inv.smul_const y))
        rw [h1 y]
        exact lintegral_const_mul (ψ y) hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfCompStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_away_range_le_of_dvd_of_comp : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range := by
  first | exact @GlobalTheory.away_range_le_of_dvd' | exact GlobalTheory.away_range_le_of_dvd' | (intros; apply GlobalTheory.away_range_le_of_dvd' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationDirectedUnionEssEtaleLocal
section
open IsLocalRing

namespace GlobalTheory

theorem localDecomp_core : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → (∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (W : μ → Subalgebra R (Localization.AtPrime Q)), Monotone W ∧ (∀ x : Localization.AtPrime Q, ∃ m, x ∈ W m) ∧ (∀ m, ∀ x ∈ W m, IsUnit x → ∃ z ∈ W m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W m)) := by
  intro R B _ _ _ Q _ ι _ _ _ C hC hcov hét hann
  have hV := fun i => _root_.GlobalTheory.localization_subalgebra_frac R B Q (C i) (hann i)
  choose V hVmem hVeq using hV
  refine ⟨ι, inferInstance, inferInstance, inferInstance, V, ?_, ?_, ?_, ?_⟩
  · intro i j hij x hx
    obtain ⟨a, ha, s, hs, hsQ, hxs⟩ := (hVmem i x).1 hx
    exact (hVmem j x).2 ⟨a, hC hij ha, s, hC hij hs, hsQ, hxs⟩
  · intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨i1, h1⟩ := hcov a
    obtain ⟨i2, h2⟩ := hcov (s : B)
    obtain ⟨k, hk1, hk2⟩ := directed_of (· ≤ ·) i1 i2
    exact ⟨k, (hVmem k _).2 ⟨a, hC hk1 h1, s, hC hk2 h2, s.2, IsLocalization.mk'_spec _ _ _⟩⟩
  · intro m x hx hu
    obtain ⟨a, ha, s, hs, hsQ, hxs⟩ := (hVmem m x).1 hx
    have hsu : IsUnit (algebraMap B (Localization.AtPrime Q) s) :=
      IsLocalization.map_units _ (⟨s, hsQ⟩ : Q.primeCompl)
    have hau : IsUnit (algebraMap B (Localization.AtPrime Q) a) := hxs ▸ hu.mul hsu
    have haQ : a ∉ Q := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q a).1 hau
    refine ⟨↑hu.unit⁻¹, (hVmem m _).2 ⟨s, hs, a, ha, haQ, ?_⟩, hu.mul_val_inv⟩
    calc (↑hu.unit⁻¹ : Localization.AtPrime Q) * algebraMap B _ a
        = ↑hu.unit⁻¹ * (x * algebraMap B _ s) := by rw [hxs]
      _ = algebraMap B _ s := by rw [← mul_assoc, hu.val_inv_mul, one_mul]
  · intro m
    obtain ⟨A, i1, i2, i3, q, i4, ⟨e⟩⟩ := hét m
    obtain ⟨f⟩ := hVeq m
    exact ⟨A, i1, i2, i3, q, i4, ⟨e.trans f⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationInverseModF
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_inverse_mod_f : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (f : B) (P : Ideal B) (Q : Ideal D) (g : D), Q.comap (algebraMap B D) = P → (∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) → ∀ s : B, s ∉ P → ∃ t : Localization.Away g, algebraMap B (Localization.Away g) s * t - 1 ∈ Ideal.span {algebraMap B (Localization.Away g) f} := by
  first | (exact @GlobalTheory.unitsMod_away_of_unique_prime) | (exact GlobalTheory.unitsMod_away_of_unique_prime) | (intros; apply GlobalTheory.unitsMod_away_of_unique_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
section
open scoped TensorProduct

namespace GlobalTheory

namespace LocalizationIntegrallyClosedDomain

variable {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]

lemma algebraMap_eq_zero_of_sub (C : Subring B) (c : C)
    (h : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) c = 0) :
    algebraMap B (Localization.AtPrime Q) (c : B) = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Q.comap C.subtype).primeCompl] at h
  obtain ⟨⟨m, hm⟩, hmc⟩ := h
  rw [IsLocalization.map_eq_zero_iff Q.primeCompl]
  refine ⟨⟨(m : B), by exact hm⟩, ?_⟩
  simpa using congrArg Subtype.val hmc

lemma algebraMap_eq_zero_of_witness (C : Subring B) (u e : C) (hu : (u : B) ∉ Q)
    (h : u * e = 0) :
    algebraMap C (Localization.AtPrime (Q.comap C.subtype)) e = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Q.comap C.subtype).primeCompl]
  exact ⟨⟨u, by exact hu⟩, h⟩

variable {Q}

lemma noZeroDivisors
    (H : ∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
      ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧
        IsIntegrallyClosed (Localization.AtPrime q)) :
    NoZeroDivisors (Localization.AtPrime Q) := by
  classical
  refine ⟨fun {x y} hxy => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hxy
  obtain ⟨u, hu⟩ := hxy
  obtain ⟨C, hC, hCq⟩ := H {a, c, (u : B)}
  have ha : a ∈ C := hC (by simp)
  have hc : c ∈ C := hC (by simp)
  have hu' : (u : B) ∈ C := hC (by simp)
  haveI := (hCq (Q.comap C.subtype)).1
  have h0 : algebraMap C (Localization.AtPrime (Q.comap C.subtype))
      ((⟨a, ha⟩ : C) * ⟨c, hc⟩) = 0 :=
    algebraMap_eq_zero_of_witness Q C ⟨u, hu'⟩ _ u.2 (Subtype.ext (by simpa using hu))
  rw [map_mul] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · left
    have h1 := algebraMap_eq_zero_of_sub Q C _ h
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl] at h1
    rw [IsLocalization.mk'_eq_zero_iff]
    exact h1
  · right
    have h1 := algebraMap_eq_zero_of_sub Q C _ h
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl] at h1
    rw [IsLocalization.mk'_eq_zero_iff]
    exact h1

end LocalizationIntegrallyClosedDomain

end GlobalTheory

namespace GlobalTheory

namespace LocalizationIntegrallyClosedDomain

variable {B : Type} [CommRing B] {Q : Ideal B} [Q.IsPrime]


set_option maxHeartbeats 1600000 in
lemma isIntegrallyClosed
    (H : ∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
      ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧
        IsIntegrallyClosed (Localization.AtPrime q))
    [IsDomain (Localization.AtPrime Q)] :
    IsIntegrallyClosed (Localization.AtPrime Q) := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing (Localization.AtPrime Q))]
  intro z hz
  have hf : ∀ x ∈ Q.primeCompl, algebraMap B (FractionRing (Localization.AtPrime Q)) x ≠ 0 := by
    intro x hx
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q))]
    exact ((IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hx⟩ : Q.primeCompl)).map (algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)))).ne_zero
  have key : ∀ (b : B) (v : Q.primeCompl),
      algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) b v) * algebraMap B (FractionRing (Localization.AtPrime Q)) v = algebraMap B (FractionRing (Localization.AtPrime Q)) b := by
    intro b v
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) v, IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) b, ← map_mul,
      IsLocalization.mk'_spec]

  obtain ⟨D, A0, hD, hDz⟩ : ∃ D A0 : B, algebraMap B (FractionRing (Localization.AtPrime Q)) D ≠ 0 ∧
      algebraMap B (FractionRing (Localization.AtPrime Q)) D * z = algebraMap B (FractionRing (Localization.AtPrime Q)) A0 := by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := (Localization.AtPrime Q)) z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
    have hyK : algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) c t) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    have hcK : algebraMap B (FractionRing (Localization.AtPrime Q)) c ≠ 0 := by
      intro h0
      apply hyK
      have h1 := key c t
      rw [h0] at h1
      exact (mul_eq_zero.mp h1).resolve_right (hf _ t.2)
    refine ⟨c * s, a * t, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hcK (hf _ s.2)
    · have k1 := key a s
      have k2 := key c t
      rw [map_mul, map_mul, ← k1, ← k2]
      field_simp
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization Q.primeCompl z hz
  obtain ⟨p, hpm, hp⟩ := hm
  set A : B := (m : B) * A0 with hA
  have hDA : algebraMap B (FractionRing (Localization.AtPrime Q)) D * (m • z) = algebraMap B (FractionRing (Localization.AtPrime Q)) A := by
    rw [Submonoid.smul_def, Algebra.smul_def, hA, map_mul, ← hDz]; ring
  have hE : algebraMap B (Localization.AtPrime Q) (p.scaleRoots D |>.eval A) = 0 := by
    have h1 := Polynomial.scaleRoots_eval₂_mul (p := p) (algebraMap B (FractionRing (Localization.AtPrime Q))) (m • z) D
    rw [hp, mul_zero, hDA, Polynomial.eval₂_at_apply, IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q))] at h1
    exact (map_eq_zero_iff _ (IsFractionRing.injective (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)))).mp h1
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl (Localization.AtPrime Q) _).mp hE
  obtain ⟨C, hC, hCq⟩ := H (insert A (insert D (insert (u : B) p.coeffs)))
  have hAC : A ∈ C := hC (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hDC : D ∈ C := hC (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have huC : (u : B) ∈ C := hC (Finset.mem_coe.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  have hcoef : (↑p.coeffs : Set B) ⊆ (C : Set B) := fun x hx => hC (Finset.mem_coe.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))))
  set p' := p.toSubring C hcoef with hp'
  have hp'm : p'.Monic := (Polynomial.monic_toSubring p C hcoef).mpr hpm
  set A' : C := ⟨A, hAC⟩
  set D' : C := ⟨D, hDC⟩
  set u' : C := ⟨u, huC⟩
  haveI : Nontrivial B := (algebraMap B (Localization.AtPrime Q)).domain_nontrivial
  have hlc : C.subtype p'.leadingCoeff ≠ 0 := by
    rw [hp'm.leadingCoeff, map_one]; exact one_ne_zero
  have hsub : C.subtype ((p'.scaleRoots D').eval A') = (p.scaleRoots D).eval A := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ hlc,
      Polynomial.map_toSubring]
    rfl
  have hE' : u' * (p'.scaleRoots D').eval A' = 0 := by
    apply Subtype.ext
    have : (u : B) * C.subtype ((p'.scaleRoots D').eval A') = 0 := by rw [hsub]; exact hu
    simpa using this
  haveI := (hCq (Q.comap C.subtype)).1
  haveI := (hCq (Q.comap C.subtype)).2
  have hgE : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) ((p'.scaleRoots D').eval A') = 0 :=
    algebraMap_eq_zero_of_witness Q C u' _ u.2 hE'
  have hgD : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D' ≠ 0 := by
    intro h0
    have h1 : algebraMap B (Localization.AtPrime Q) D = 0 := algebraMap_eq_zero_of_sub Q C D' h0
    apply hD
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)), h1, map_zero]
  have hhD : algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))))).mpr hgD
  set x : (FractionRing (Localization.AtPrime (Q.comap C.subtype))) := algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A') / algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') with hx
  have hxD : algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') * x = algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A') := by
    rw [hx]; field_simp
  have hlc2 : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) p'.leadingCoeff ≠ 0 := by
    rw [hp'm.leadingCoeff, map_one]; exact one_ne_zero
  have hxint : IsIntegral (Localization.AtPrime (Q.comap C.subtype)) x := by
    refine ⟨p'.map (algebraMap C (Localization.AtPrime (Q.comap C.subtype))), hp'm.map _, ?_⟩
    have h2 := Polynomial.scaleRoots_eval₂_mul (p := p'.map (algebraMap C (Localization.AtPrime (Q.comap C.subtype)))) (algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype)))) x
      (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D')
    rw [hxD, ← Polynomial.map_scaleRoots _ _ _ hlc2, Polynomial.eval₂_at_apply, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hgE, map_zero] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hhD)
  obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Localization.AtPrime (Q.comap C.subtype)) (K := FractionRing (Localization.AtPrime (Q.comap C.subtype)))).mp hxint
  have hwD : w * algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D' = algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A' := by
    apply IsFractionRing.injective (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype)))
    rw [map_mul, hw, mul_comm, hxD]
  obtain ⟨⟨e, v⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.comap C.subtype).primeCompl w
  have hev : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) (e * D') = algebraMap C (Localization.AtPrime (Q.comap C.subtype)) (A' * v) := by
    rw [map_mul, map_mul, ← hwD, ← IsLocalization.mk'_spec (Localization.AtPrime (Q.comap C.subtype)) e v]; ring
  obtain ⟨n, hn⟩ := (IsLocalization.eq_iff_exists (Q.comap C.subtype).primeCompl (Localization.AtPrime (Q.comap C.subtype))).mp hev
  have hnB : ((n : C) : B) * ((e : B) * D) = ((n : C) : B) * (A * ((v : C) : B)) := by
    simpa using congrArg Subtype.val hn
  have hK := congrArg (algebraMap B (FractionRing (Localization.AtPrime Q))) hnB
  simp only [map_mul, hA] at hK
  have hfn : algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) ≠ 0 := hf _ (by exact n.2)
  have hfv : algebraMap B (FractionRing (Localization.AtPrime Q)) ((v : C) : B) ≠ 0 := hf _ (by exact v.2)
  have hfm : algebraMap B (FractionRing (Localization.AtPrime Q)) (m : B) ≠ 0 := hf _ m.2
  let v'' : Q.primeCompl := ⟨((v : C) : B), by exact v.2⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime Q) (e : B) (m * v''), ?_⟩
  have key2 := key (e : B) (m * v'')
  simp only [Submonoid.coe_mul, map_mul] at key2
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hfn hD) (mul_ne_zero hfm hfv))
  linear_combination (algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) D) * key2
    - (algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) (m : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) ((v : C) : B)) * hDz + hK

end LocalizationIntegrallyClosedDomain

theorem localization_isDomain_isIntegrallyClosed_of_finset_subring :
    ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro B _ Q _ H
  haveI : NoZeroDivisors (Localization.AtPrime Q) := LocalizationIntegrallyClosedDomain.noZeroDivisors H
  haveI : IsDomain (Localization.AtPrime Q) := NoZeroDivisors.to_isDomain _
  exact ⟨inferInstance, LocalizationIntegrallyClosedDomain.isIntegrallyClosed H⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationMaximalIdealEqSpanNilpotentArtinianStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_maximalIdeal_eq_span_nilpotent_artinian : ∀ (D : Type) [CommRing D] [IsArtinianRing D] (x : D), IsNilpotent x → IsReduced (D ⧸ Ideal.span {x}) → ∀ (P : Ideal D) [P.IsMaximal], IsLocalRing.maximalIdeal (Localization.AtPrime P) = Ideal.span {algebraMap D (Localization.AtPrime P) x} := by
  first | exact @GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent | exact GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent | (intros; apply GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationPreservesRingPullbackSquare
section
namespace GlobalTheory

theorem locPullback : ∀ {A R₀ A' B₀ : Type} [CommRing A] [CommRing R₀] [CommRing A'] [CommRing B₀]
    (φ : A →+* R₀) (ψ : A →+* A') (α : R₀ →+* B₀) (κ : A' →+* B₀), α.comp φ = κ.comp ψ →
    (∀ a, φ a = 0 → ψ a = 0 → a = 0) → (∀ r c, α r = κ c → ∃ a, φ a = r ∧ ψ a = c) →
    ∀ (s : A) (LA LR LA' LB : Type) [CommRing LA] [CommRing LR] [CommRing LA'] [CommRing LB]
    [Algebra A LA] [Algebra R₀ LR] [Algebra A' LA'] [Algebra B₀ LB]
    [IsLocalization.Away s LA] [IsLocalization.Away (φ s) LR] [IsLocalization.Away (ψ s) LA']
    [IsLocalization.Away (α (φ s)) LB]
    (Φ : LA →+* LR) (Ψ : LA →+* LA') (Aα : LR →+* LB) (Kκ : LA' →+* LB),
    Φ.comp (algebraMap A LA) = (algebraMap R₀ LR).comp φ →
    Ψ.comp (algebraMap A LA) = (algebraMap A' LA').comp ψ →
    Aα.comp (algebraMap R₀ LR) = (algebraMap B₀ LB).comp α →
    Kκ.comp (algebraMap A' LA') = (algebraMap B₀ LB).comp κ →
    (∀ t, Φ t = 0 → Ψ t = 0 → t = 0) ∧ ∀ a b, Aα a = Kκ b → ∃ t, Φ t = a ∧ Ψ t = b := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.QuotientMapComposition.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.QuotientMapComposition.main
  | exact @_root_.GlobalTheory.QuotientMapComposition.main
  | exact _root_.GlobalTheory.QuotientMapComposition.main
  | (apply _root_.GlobalTheory.QuotientMapComposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMapComposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMapComposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMapComposition.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationResidueApproximation
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_residue_approximation : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal D) (g : D), g ∉ Q → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Q.map (algebraMap D (Localization.Away g)) := by
  first | (exact @GlobalTheory.residue_surj_localizationAway) | (exact GlobalTheory.residue_surj_localizationAway) | (intros; apply GlobalTheory.residue_surj_localizationAway <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedModuleMemAnnSpanSmulTopStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizedModule_mem_annSpan_smul_of_mem : ∀ (D : Type) [CommRing D] (S : Submonoid D) (x : D) (N : Type 1) [AddCommGroup N] [Module D N], (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) → ∀ n : LocalizedModule S N, algebraMap D (Localization S) x • n = 0 → n ∈ Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} • (⊤ : Submodule (Localization S) (LocalizedModule S N)) := by
  first | exact @GlobalTheory.localizedModule_mem_annSpan_smul_top | exact GlobalTheory.localizedModule_mem_annSpan_smul_top | (intros; apply GlobalTheory.localizedModule_mem_annSpan_smul_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogThetaWeightSizeLeStatement
section
open Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_le_twenty_mul_of_bounds : ∀ (f r Lb S sz : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ Lb → Real.log (f * r) ≤ Lb → (∃ N : ℕ, S = N) → Real.log S ≤ 10 * Lb → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → Real.log sz ≤ 20 * Lb := by
  first | exact @GlobalTheory.log_theta_weight_size_le | exact GlobalTheory.log_theta_weight_size_le | (intros; apply GlobalTheory.log_theta_weight_size_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDomainRelationLiftCommutingSquareStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDomain_relation_lift_commuting_square : ∀ (M : Type 1) [AddCommGroup M] (X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : Type) (c : X₂ → X₄) (d : X₃ → X₄) (u : Y₁ → Y₂) (v : Y₁ → Y₃) (c' : Y₂ → Y₄) (d' : Y₃ → Y₄) (r₂ : X₂ → Y₂) (r₃ : X₃ → Y₃) (r₄ : X₄ → Y₄) (G : Y₄ → Prop), (∀ x, c' (r₂ x) = r₄ (c x)) → (∀ y, d' (r₃ y) = r₄ (d y)) → (∀ x, c' (u x) = d' (v x)) → Function.Injective c' → (∀ x, G (c' x)) → (∀ y, G (d' y) → ∃ x, v x = y) → ∀ (a₂ : X₂ →₀ M) (a₃ : X₃ →₀ M), Finsupp.mapDomain c a₂ + Finsupp.mapDomain d a₃ = 0 → (∀ y ∈ a₃.support, ∀ y' ∈ a₃.support, d y = d y' → r₃ y = r₃ y' ∨ G (d' (r₃ y))) → ∃ a : Y₁ →₀ M, Finsupp.mapDomain u a = Finsupp.mapDomain r₂ a₂ ∧ Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
  first | (exact @GlobalTheory.mapDomain_corner_lift) | (exact GlobalTheory.mapDomain_corner_lift) | (intros; apply GlobalTheory.mapDomain_corner_lift  <;> assumption)
end

