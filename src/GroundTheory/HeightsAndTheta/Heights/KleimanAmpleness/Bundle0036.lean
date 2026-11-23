module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionBundle
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeIndep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ e, t = monomial e 1 := by
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, -, rfl⟩ := hx
    exact ⟨Finsupp.single ⟨k, i⟩ 1, rfl⟩
  | one => exact ⟨0, by rw [monomial_zero', C_1]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hy
    exact ⟨e + e', by rw [monomial_mul, mul_one]⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eq_zero_of_monomial_mul (e : (Σ k, ι k) →₀ ℕ) {p : MRingOver S ι}
    (h : monomial e (1 : S) * p = 0) : p = 0 := by
  ext d
  have := congrArg (AddMonoidAlgebra.coeff · (e + d)) h
  rw [coeff_monomial_mul, one_mul] at this
  simpa using this


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eq_zero_of_mk_eq_zero {I : ∀ k, Finset (ι k)} {p : MRingOver S ι}
    (h : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) p) (1 : KH.cellMon S I) = 0) :
    p = 0 := by
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I), LocalizedModule.mk_eq] at h
  obtain ⟨t, ht⟩ := h
  rw [one_smul, one_smul, smul_zero, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at ht
  obtain ⟨e, he⟩ := cellMon_monomial t.2
  rw [he] at ht
  exact eq_zero_of_monomial_mul e ht

theorem shift_injective (u : (Σ k, ι k) →₀ ℕ) {b b' : (Σ k, ι k) → ℤ} (hb : negExp b ≤ u)
    (hb' : negExp b' ≤ u) (h : posExp b + u - negExp b = posExp b' + u - negExp b') : b = b' := by
  funext p
  have h1 := DFunLike.congr_fun h p
  have h2 := Finsupp.le_def.1 hb p
  have h3 := Finsupp.le_def.1 hb' p
  simp only [posExp, negExp, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
    Finsupp.coe_equivFunOnFinite_symm] at h1 h2 h3
  omega

theorem smul_smul_monoFrac (I : ∀ k, Finset (ι k)) (u : (Σ k, ι k) →₀ ℕ) (r : S) (b : (Σ k, ι k) → ℤ)
    (hI : ∀ k, negSet b k ⊆ I k) (hb : negExp b ≤ u) :
    (monomial u (1 : S) : MRingOver S ι) • (r • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (monomial (posExp b + u - negExp b) r)) (1 : KH.cellMon S I) := by
  rw [monoFrac, dif_pos hI, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  rw [one_smul, one_smul, one_smul, Submonoid.smul_def]
  rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  congr 1
  simp only [smul_eq_mul, smul_monomial, monomial_mul, mul_one, one_mul]
  congr 1
  rw [add_tsub_cancel_of_le (le_add_left hb), add_comm]

theorem eq_zero_of_sum_smul_monoFrac (I : ∀ k, Finset (ι k)) (A : Finset ((Σ k, ι k) → ℤ))
    (g : ((Σ k, ι k) → ℤ) → S) (hg : ∀ b ∈ A, ¬ (∀ k, negSet b k ⊆ I k) → g b = 0)
    (h : ∑ b ∈ A, g b • monoFrac S I b = 0) : ∀ a ∈ A, g a = 0 := by
  classical
  set u : (Σ k, ι k) →₀ ℕ := ∑ b ∈ A.filter (fun b => ∀ k, negSet b k ⊆ I k), negExp b with hu
  set c : ((Σ k, ι k) → ℤ) → ((Σ k, ι k) →₀ ℕ) := fun b => posExp b + u - negExp b with hc
  have hle : ∀ b ∈ A, (∀ k, negSet b k ⊆ I k) → negExp b ≤ u := fun b hb hI =>
    Finset.single_le_sum (f := negExp) (fun _ _ => zero_le) (Finset.mem_filter.2 ⟨hb, hI⟩)
  have hterm : ∀ b ∈ A, (monomial u (1 : S) : MRingOver S ι) • (g b • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (c b) (g b)))
        (1 : KH.cellMon S I) := by
    intro b hb
    by_cases hI : ∀ k, negSet b k ⊆ I k
    · exact smul_smul_monoFrac I u (g b) b hI (hle b hb hI)
    · rw [hg b hb hI, zero_smul, smul_zero, monomial_zero, map_zero, LocalizedModule.zero_mk]
  have key : ∑ b ∈ A, monomial (c b) (g b) = 0 := by
    apply eq_zero_of_mk_eq_zero (I := I)
    have e1 : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (∑ b ∈ A, monomial (c b) (g b))) (1 : KH.cellMon S I) =
        ∑ b ∈ A, LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
          (monomial (c b) (g b))) (1 : KH.cellMon S I) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact map_sum (LocalizedModule.mkLinearMap (KH.cellMon S I) _) _ _
    rw [e1, ← Finset.sum_congr rfl hterm, ← Finset.smul_sum, h, smul_zero]
  intro a ha
  by_cases hI : ∀ k, negSet a k ⊆ I k
  · have hk := congrArg (AddMonoidAlgebra.coeff · (c a)) key
    rw [coeff_sum, Finset.sum_eq_single a, coeff_monomial, if_pos rfl,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hk
    · exact hk
    · intro b hb hba
      by_cases hbI : ∀ k, negSet b k ⊆ I k
      · rw [coeff_monomial, if_neg]
        exact fun hcb => hba (shift_injective u (hle b hb hbI) (hle a ha hI) hcb)
      · simp [hg b hb hbI]
    · exact fun hna => absurd ha hna
  · exact hg a ha hI

end KHFreeIndep

theorem KHFreeIndep.full : KHFreeIndep.Statement := by
  intro S _ K _ _ ι _ _ n A f h a ha
  classical
  funext J
  let g : ((Σ k, ι k) → ℤ) → S := fun b =>
    if hb : ∀ k, negSet b k ⊆ J.1.1 k then f b ⟨J.1, hb⟩ else 0
  have hsum : ∑ b ∈ A, g b • monoFrac S J.1.1 b = 0 := by
    have h0 := congrFun h J.1
    rw [Finset.sum_apply, Pi.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [embed, LinearMap.pi_apply, g]
    split_ifs with hb1
    · rfl
    · simp [monoFrac, hb1]
  have hJ := KHFreeIndep.eq_zero_of_sum_smul_monoFrac J.1.1 A g (fun b _ hb => dif_neg hb) hsum a ha
  rw [show g a = f a J from dif_pos J.2] at hJ
  simpa using hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLineBundleRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

def restrictUnion (I J : Chart y) : Chart y :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem redAt_isUnit_of_isUnit {I J : Chart y} (h : I.1 ⊆ J.1)
    (a : chartRing k x (liftChart hxy I))
    (ha : IsUnit (chartIncl (S := k) (x := x) (I := liftChart hxy I) (J := liftChart hxy J) h a)) :
    (a : Ω) ∈ locAt k x y ∧ ∃ b ∈ chartRing k y J, redAt k x y a * b = 1 := by
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  have hc' : (a : Ω) * (c : Ω) = 1 := congrArg Subtype.val hc
  have haL := chartRing_sub_locAt hsp hxy I a.2
  have hcL := chartRing_sub_locAt hsp hxy J c.2
  refine ⟨haL.1, _, hcL.2, ?_⟩
  rw [← (locAt_mul hsp haL.1 hcL.1).2, hc', (locAt_one hsp).2]

theorem exists_mul_mem_of_mem_restrictUnion (Q : LineBundle k x) (I J : Chart y) {z : Ω}
    (hz : z ∈ Q.sub (liftChart hxy (restrictUnion I J))) :
    ∃ a ∈ chartRing k x (liftChart hxy I), a ∈ locAt k x y ∧ redAt k x y a ≠ 0 ∧
      a * z ∈ Q.sub (liftChart hxy I) := by
  have hIJ : I.1 ⊆ (restrictUnion I J).1 := Finset.subset_union_left
  obtain ⟨a, ha, haz⟩ := (Q.mem_iff (liftChart hxy I) (liftChart hxy (restrictUnion I J)) hIJ z).mp hz
  obtain ⟨haL, b, -, hb⟩ := redAt_isUnit_of_isUnit hsp hxy hIJ a ha
  rw [smul_eq_mul] at haz
  exact ⟨a, a.2, haL, left_ne_zero_of_mul_eq_one hb, haz⟩

theorem exists_restrict_gen (Q : LineBundle k x) :
    ∃ γ : Ω, γ ≠ 0 ∧ RedGood hxy Q.toSubSystem γ ∧ ∀ I : Chart y,
      ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
        b * γ ∈ Q.sub (liftChart hxy I) := by
  by_cases hI : Nonempty (Chart y)
  swap
  · exact ⟨1, one_ne_zero, fun I => (hI ⟨I⟩).elim, fun I => (hI ⟨I⟩).elim⟩
  obtain ⟨I₀⟩ := hI
  obtain ⟨M, hM⟩ := Q.invertible (liftChart hxy I₀)
  have hA : ∀ {q m : Ω}, q ∈ Q.sub (liftChart hxy I₀) → m ∈ M → q * m ∈ locAt k x y :=
    fun hq hm => (chartRing_sub_locAt hsp hxy I₀ (mul_mem_chartRing_of_mul_eq_one hM hq hm)).1
  have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy I₀) * M := by
    rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨γ, hγ, m₀, hm₀, hne⟩ :
      ∃ γ ∈ Q.sub (liftChart hxy I₀), ∃ m₀ ∈ M, redAt k x y (γ * m₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z = 0) h1
      (fun q hq m hm => ⟨hA hq hm, hcon q hq m hm⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2, hu.2, hv.2, add_zero]⟩)
    rw [(locAt_one hsp).2] at this
    exact one_ne_zero this.2
  have hγm := hA hγ hm₀
  have hγm0 := (locAt_inv hsp hγm hne).1
  have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hγm0
  have hm0 : m₀ ≠ 0 := right_ne_zero_of_mul hγm0
  refine ⟨γ, hγ0, ?_, ?_⟩
  · intro I q hq
    have hsub : I.1 ⊆ (restrictUnion I₀ I).1 := Finset.subset_union_right
    obtain ⟨a, -, haL, har, haq⟩ := exists_mul_mem_of_mem_restrictUnion hsp hxy Q I₀ I
      (Q.mono (liftChart hxy I) (liftChart hxy (restrictUnion I₀ I)) hsub q hq)
    have ha0 : a ≠ 0 := (locAt_inv hsp haL har).1
    have hnum := hA haq hm₀
    have hden := locAt_mul hsp haL hγm
    have hden0 : redAt k x y (a * (γ * m₀)) ≠ 0 := by rw [hden.2]; exact mul_ne_zero har hne
    have heq : q / γ = a * q * m₀ / (a * (γ * m₀)) := by
      rw [mul_assoc a q m₀, mul_div_mul_left _ _ ha0, mul_div_mul_right _ _ hm0]
    rw [heq]; exact (locAt_div hsp hnum hden.1 hden0).1
  · intro I
    have hsub : I₀.1 ⊆ (restrictUnion I I₀).1 := Finset.subset_union_right
    exact exists_mul_mem_of_mem_restrictUnion hsp hxy Q I I₀
      (Q.mono (liftChart hxy I₀) (liftChart hxy (restrictUnion I I₀)) hsub γ hγ)

variable {γ : Ω} {Q : LineBundle k x}

theorem redSys_sub_eq_span (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y) {s : Set Ω}
    (hs : Submodule.span (chartRing k x (liftChart hxy I)) s = Q.sub (liftChart hxy I)) :
    (redSys hxy Q.toSubSystem γ).sub I =
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Submodule.span (chartRing k x (liftChart hxy I)) s := by rw [hs]; exact hq
    refine Submodule.span_induction (p := fun q _ => redAt k x y (q / γ) ∈
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s)) ?_ ?_ ?_ ?_ hq'
    · intro q hq; exact Submodule.subset_span ⟨q, hq, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hg I u (hs ▸ hu)) (hg I v (hs ▸ hv))).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hg I u (hs ▸ hu))).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Q.sub (liftChart hxy I) := by rw [← hs]; exact Submodule.subset_span hq
    exact Submodule.subset_span ⟨q, hq', rfl⟩

theorem redSys_mem_iff (hg : RedGood hxy Q.toSubSystem γ) (I J : Chart y) (h : I.1 ⊆ J.1) (z : K') :
    z ∈ (redSys hxy Q.toSubSystem γ).sub J ↔ ∃ c : chartRing k y I, IsUnit (chartIncl h c) ∧
      (c : K') • z ∈ (redSys hxy Q.toSubSystem γ).sub I := by
  constructor
  · intro hz
    obtain ⟨q, hq, rfl⟩ := (mem_redSys_iff hsp hxy hg J z).mp hz
    obtain ⟨b, hb, hbq⟩ := (Q.mem_iff (liftChart hxy I) (liftChart hxy J) h q).mp hq
    obtain ⟨hbL, b', hb'A, hbb'⟩ := redAt_isUnit_of_isUnit hsp hxy h b hb
    have hbI := (chartRing_sub_locAt hsp hxy I b.2).2
    refine ⟨⟨_, hbI⟩, IsUnit.of_mul_eq_one ⟨b', hb'A⟩ (Subtype.ext hbb'), ?_⟩
    rw [smul_eq_mul] at hbq
    change redAt k x y b * redAt k x y (q / γ) ∈ (redSys hxy Q.toSubSystem γ).sub I
    rw [← (locAt_mul hsp hbL (hg J q hq)).2, ← mul_div_assoc]
    exact Submodule.subset_span ⟨_, hbq, rfl⟩
  · rintro ⟨c, hc, hcz⟩
    obtain ⟨c', hc'⟩ := hc.exists_left_inv
    have hc'' : (c' : K') * (c : K') = 1 := congrArg Subtype.val hc'
    have := Submodule.smul_mem _ c' ((redSys hxy Q.toSubSystem γ).mono I J h _ hcz)
    rwa [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hc'', one_mul] at this

theorem redSys_invertible (hγ0 : γ ≠ 0) (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y)
    (hb : ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
      b * γ ∈ Q.sub (liftChart hxy I)) :
    ∃ M' : Submodule (chartRing k y I) K', (redSys hxy Q.toSubSystem γ).sub I * M' = 1 := by
  obtain ⟨b, -, hbL, hbr, hbγ⟩ := hb
  obtain ⟨M, hM⟩ := Q.invertible (liftChart hxy I)
  refine ⟨Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * γ)) '' M), ?_⟩
  have hA : ∀ {q m : Ω}, q ∈ Q.sub (liftChart hxy I) → m ∈ M →
      q * m ∈ chartRing k x (liftChart hxy I) :=
    fun hq hm => mul_mem_chartRing_of_mul_eq_one hM hq hm
  have hb0 : b ≠ 0 := (locAt_inv hsp hbL hbr).1
  have hmg : ∀ {m : Ω}, m ∈ M → m * γ ∈ locAt k x y := by
    intro m hm
    have h1 := (chartRing_sub_locAt hsp hxy I (hA hbγ hm)).1
    have heq : m * γ = b * γ * m / b := by rw [eq_div_iff hb0]; ring
    rw [heq]; exact (locAt_div hsp h1 hbL hbr).1
  have hsplit : ∀ q m : Ω, q * m = q / γ * (m * γ) := fun q m => by field_simp
  apply le_antisymm
  · change Submodule.span _ _ * Submodule.span _ _ ≤ 1
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨q, hq, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
    show redAt k x y (q / γ) * redAt k x y (m * γ) ∈ (1 : Submodule (chartRing k y I) K')
    rw [← (locAt_mul hsp (hg I q hq) (hmg hm)).2, ← hsplit]
    exact Submodule.mem_one.mpr ⟨⟨_, (chartRing_sub_locAt hsp hxy I (hA hq hm)).2⟩, rfl⟩
  · rw [Submodule.one_le]
    have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy I) * M := by
      rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z ∈
        (redSys hxy Q.toSubSystem γ).sub I *
          Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * γ)) '' M)) h1
      (fun q hq m hm => ⟨(chartRing_sub_locAt hsp hxy I (hA hq hm)).1, by
        rw [hsplit, (locAt_mul hsp (hg I q hq) (hmg hm)).2]
        exact Submodule.mul_mem_mul (Submodule.subset_span ⟨q, hq, rfl⟩)
          (Submodule.subset_span ⟨m, hm, rfl⟩)⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2]; exact Submodule.add_mem _ hu.2 hv.2⟩)
    rw [(locAt_one hsp).2] at this
    exact this.2


end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotDevissage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem twist_sub_mono {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) (Q : SubSystem S x Ω)
    (I : Chart x) : (F.twist Q).sub I ≤ (G.twist Q).sub I :=
  Submodule.span_mono fun _ ⟨q, hq, y, hy, hz⟩ => ⟨q, hq, y, h I hy, hz⟩


omit [Module S E] [IsScalarTower S Ω E] in
theorem twistPows_sub_mono {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ) (I : Chart x),
      (F.twistPows t L n).sub I ≤ (G.twistPows t L n).sub I
  | 0, _, _, I => h I
  | t + 1, _, _, I => twist_sub_mono (twistPows_sub_mono h t _ _) _ I

theorem exists_subFamily_twistPows (hB : SubFamilyTwist.Statement.{u, v, w}) (F : SubFamily S x E)
    (hF : ∀ I, (F.sub I).FG) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      ∃ H : SubFamily S x E, H.toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n ∧
        ∀ I, (H.sub I).FG := by
  intro t
  induction t with
  | zero => exact fun _ _ => ⟨F, rfl, hF⟩
  | succ t ih =>
    intro L n
    obtain ⟨H, hH, hHfg⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
    obtain ⟨P, hP⟩ := exists_lineBundle_twistMul (L (Fin.last t)) (n (Fin.last t)) 0
    obtain ⟨G, hG, hGfg⟩ := hB S Ω N x E H P hHfg
    refine ⟨G, ?_, hGfg⟩
    rw [hG, hP, hH, twistMul, SubSystem.twist_twistSys_zero]
    rfl

end Lemmas

theorem SnapperQuotDevissage.proof (hF : SnapperQuotFilt.Statement.{u, v, w})
    (hI : SnapperQuotIso.Statement.{u, v, w, w}) (hA : SnapperQuotAdd.Statement.{u, v, w})
    (hB : SubFamilyTwist.Statement.{u, v, w}) : SnapperQuotDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF
  obtain ⟨r, G, pp, a, hGfg, hG0, hGr, hmono, hpp, hiso⟩ := hF k Ω N x E F₁ F₂ hfg hle J hJ hxJ hJF
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  have hH : ∀ m, ∃ H : SubFamily k x E, H.toSubSystem =
      ((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) ∧
        ∀ I, (H.sub I).FG := fun m => by
    obtain ⟨H, hH, hHfg⟩ := exists_subFamily_twistPows hB (G m) (hGfg m) t L n
    obtain ⟨H', hH', hH'fg⟩ := hB k Ω N x E H (twistBundle k x c) hHfg
    exact ⟨H', by rw [hH', hH]; rfl, hH'fg⟩
  choose H hHeq hHfg using hH
  have hHmono : ∀ m < r, ∀ I, (H m).sub I ≤ (H (m + 1)).sub I := fun m hm I => by
    rw [hHeq, hHeq]
    exact twist_sub_mono (twistPows_sub_mono (hmono m hm) t _ n) _ I
  have hstep : ∀ m (hm : m < r), eulerCharQuot k (H (m + 1)).toSubSystem (H m).toSubSystem =
      pieceChar k (pp ⟨m, hm⟩) (a ⟨m, hm⟩) L n c := fun m hm => by
    rw [hHeq, hHeq]
    exact hI k Ω N x E Ω _ _ _ _ (hiso ⟨m, hm⟩ t L n c).some
  have key : ∀ m ≤ r, (∀ I, (H 0).sub I ≤ (H m).sub I) ∧
      eulerCharQuot k (H m).toSubSystem (H 0).toSubSystem =
        ∑ i ∈ Finset.range m, (if h : i < r then pieceChar k (pp ⟨i, h⟩) (a ⟨i, h⟩) L n c else 0) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨fun I => le_rfl, by simp [eulerCharQuot_self]⟩
    | succ m ih =>
      intro hm
      obtain ⟨h0, hχ⟩ := ih (by omega)
      refine ⟨fun I => (h0 I).trans (hHmono m (by omega) I), ?_⟩
      rw [hA k Ω N x E (H (m + 1)) (H m) (H 0) (hHfg _) (hHmono m (by omega)) h0, hχ,
        hstep m (by omega), Finset.sum_range_succ, dite_eq_left (by omega), add_comm]
  rw [← hGr, ← hG0, ← hHeq r, ← hHeq 0, (key r le_rfl).2, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp [i.2]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

