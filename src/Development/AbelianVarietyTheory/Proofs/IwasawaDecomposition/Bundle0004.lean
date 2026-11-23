module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbeddingClosedIntegral
section
namespace GlobalTheory.CoefEmbed

open IsLocalRing Topology

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

open IsLocalRing Topology in
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem _root_.GlobalTheory.CoefEmbed.norm_prime_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

open IsLocalRing Topology in
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
private lemma norm_le_one_of_monic_root_lemma {R F : Type*} [CommRing R] [NormedField F]
    [IsUltrametricDist F] (f : R →+* F) (hf : ∀ r, ‖f r‖ ≤ 1) {P : Polynomial R}
    (hP : P.Monic) {y : F} (hy : P.eval₂ f y = 0) : ‖y‖ ≤ 1 := by
  by_contra h
  push_neg at h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, map_one,
    one_mul] at hy
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := by
    refine ⟨P.natDegree - 1, ?_⟩
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · rw [h0] at hy
      simp at hy
    · omega
  rw [hk] at hy
  have hsum : ‖∑ i ∈ Finset.range (k + 1), f (P.coeff i) * y ^ i‖ ≤ ‖y‖ ^ k := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    calc ‖f (P.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ k :=
          mul_le_mul (hf _) (pow_le_pow_right₀ h.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
            (by positivity) zero_le_one
      _ = ‖y‖ ^ k := one_mul _
  have heq : y ^ (k + 1) = -∑ i ∈ Finset.range (k + 1), f (P.coeff i) * y ^ i := by
    linear_combination hy
  have h1 : ‖y‖ ^ (k + 1) ≤ ‖y‖ ^ k := by
    rw [← norm_pow, heq, norm_neg]
    exact hsum
  have h2 : ‖y‖ ^ k < ‖y‖ ^ (k + 1) := pow_lt_pow_right₀ h (Nat.lt_succ_self k)
  linarith


open IsLocalRing Topology in
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem _root_.GlobalTheory.CoefEmbed.embedding_closed_integral : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ κ : FractionRing O →+* PadicAlgCl l, (∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → Topology.IsEmbedding (fun x : O => κ (algebraMap O (FractionRing O) x)) ∧ IsClosed (Set.range κ) ∧ (∀ x : FractionRing O, ‖κ x‖ ≤ 1 → ∃ y : O, algebraMap O (FractionRing O) y = x) ∧ ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
  intro l _ O _ _ _ _ _ _ _ hO κ hκ
  set g : O →+* PadicAlgCl l := κ.comp (algebraMap O (FractionRing O)) with hg
  have hgz : ∀ z : ℤ_[l], g (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]) :=
    hκ
  have hgnat : g ((l : ℕ) : O) = ((l : ℕ) : PadicAlgCl l) := map_natCast g l
  have hl_lt : ‖g ((l : ℕ) : O)‖ < 1 := hgnat ▸ _root_.GlobalTheory.CoefEmbed.norm_prime_lt_one (l := l)
  have hl_pos : 0 < ‖g ((l : ℕ) : O)‖ := by
    have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [hgnat, h, norm_algebraMap', Padic.norm_p]
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  have hint : ∀ x : O, ‖g x‖ ≤ 1 := by
    intro x
    obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x
    refine norm_le_one_of_monic_root_lemma (g.comp (algebraMap ℤ_[l] O)) (fun z => ?_) hPm ?_
    · rw [RingHom.comp_apply, hgz, norm_algebraMap']
      exact PadicInt.norm_le_one z
    · rw [← Polynomial.hom_eval₂, hP, map_zero]
  have hunit : ∀ u : Oˣ, ‖g u‖ = 1 := by
    intro u
    have h1 := hint u
    have h2 := hint ↑u⁻¹
    have h3 : ‖g u‖ * ‖g ↑u⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (g u))
    linarith
  have hmax : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have := hunit u
    rw [hu] at this
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hl_pos
    exact lt_irrefl _ hl_pos
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have he : e ≠ 0 := by
    rintro rfl
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmax) (by rw [hw, pow_zero, mul_one]; exact w.isUnit)
  have hϖlt : ‖g ϖ‖ < 1 := by
    have h : ‖g ((l : ℕ) : O)‖ = ‖g ϖ‖ ^ e := by
      rw [hw, map_mul, norm_mul, hunit, one_mul, map_pow, norm_pow]
    by_contra h'
    push_neg at h'
    have := one_le_pow₀ (n := e) h'
    linarith
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hginj : Function.Injective g :=
    κ.injective.comp (IsFractionRing.injective O (FractionRing O))
  have hϖpos : 0 < ‖g ϖ‖ := norm_pos_iff.mpr ((map_ne_zero_iff g hginj).mpr hϖ0)
  have hm : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O → ‖g y‖ ≤ ‖g ϖ‖ := by
    intro y hy
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [map_mul, norm_mul]
    calc ‖g ϖ‖ * ‖g c‖ ≤ ‖g ϖ‖ * 1 := mul_le_mul_of_nonneg_left (hint c) (norm_nonneg _)
      _ = ‖g ϖ‖ := mul_one _
  have hintc : ∀ x : FractionRing O, ‖κ x‖ ≤ 1 → ∃ y : O, algebraMap O (FractionRing O) y = x := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, by rw [hx0, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger O x with h | h
    · exact h
    · obtain ⟨y, hy⟩ := h
      by_cases hyu : IsUnit y
      · obtain ⟨u, rfl⟩ := hyu
        refine ⟨↑u⁻¹, ?_⟩
        have h1 : algebraMap O (FractionRing O) ↑u⁻¹ * algebraMap O (FractionRing O) ↑u = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [hy] at h1
        exact (mul_inv_eq_one₀ hx0).mp h1
      · exfalso
        have hym : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hyu
        have h1 : ‖κ x⁻¹‖ ≤ ‖g ϖ‖ := by
          rw [← hy]
          exact hm y hym
        have h2 : ‖κ x‖ * ‖κ x⁻¹‖ = 1 := by
          rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
        have h3 := mul_le_mul_of_nonneg_right hx (norm_nonneg (κ x⁻¹))
        linarith
  have hdiv : ∀ b : O, b ≠ 0 → ∃ (n : ℕ) (c : O), b * c = ((l : ℕ) : O) ^ n := by
    intro b hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    refine ⟨n, ↑u⁻¹ * ↑w ^ n * ϖ ^ (e' * n), ?_⟩
    rw [hw]
    have := u.mul_inv
    linear_combination (↑w ^ n * ϖ ^ (n + e' * n)) * this
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  set V : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (g '' (s : Set O)) with hV
  have hgV : ∀ x : O, g x ∈ V := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact V.zero_mem
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact V.add_mem hy hz
    | smul z y _ hy =>
      rw [Algebra.smul_def, map_mul, hgz, ← Algebra.smul_def]
      exact V.smul_mem _ hy
  have hrange : Set.range κ = (V : Set (PadicAlgCl l)) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective O x
      obtain ⟨n, c, hc⟩ := hdiv b (nonZeroDivisors.ne_zero hb)
      have hb' : g b ≠ 0 := (map_ne_zero_iff g hginj).mpr (nonZeroDivisors.ne_zero hb)
      have hln : g (((l : ℕ) : O) ^ n) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (norm_pos_iff.mp hl_pos)
      have hc' : g c ≠ 0 := by
        intro h
        apply hln
        rw [← hc, map_mul, h, mul_zero]
      have key : κ (algebraMap O (FractionRing O) a / algebraMap O (FractionRing O) b) =
          ((l : ℚ_[l]) ^ n)⁻¹ • g (a * c) := by
        rw [map_div₀, Algebra.smul_def, map_inv₀, map_pow, map_natCast]
        change g a / g b = _
        rw [← map_natCast g, ← map_pow, ← hc, map_mul, map_mul]
        field_simp
      rw [SetLike.mem_coe, key]
      exact V.smul_mem _ (hgV _)
    · intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, _, rfl⟩ := hy
        exact ⟨_, rfl⟩
      | zero => exact ⟨0, map_zero κ⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, rfl⟩ := hy
        obtain ⟨b, rfl⟩ := hz
        exact ⟨a + b, map_add κ a b⟩
      | smul q y _ hy =>
        obtain ⟨x, rfl⟩ := hy
        obtain ⟨z1, z2, -, rfl⟩ := IsFractionRing.div_surjective ℤ_[l] q
        refine ⟨algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z1) /
          algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z2) * x, ?_⟩
        rw [map_mul, map_div₀, hκ, hκ, Algebra.smul_def, map_div₀]
        rfl
  have hclosed : IsClosed (Set.range κ) := by
    rw [hrange]
    haveI : FiniteDimensional ℚ_[l] V :=
      FiniteDimensional.span_of_finite ℚ_[l] ((s.finite_toSet).image g)
    exact V.closed_of_finiteDimensional
  obtain ⟨hopen, hsmall⟩ := isAdic_iff.mp hO
  have hemb : Topology.IsEmbedding g := by
    refine ⟨(IsTopologicalAddGroup.isInducing_iff_nhds_zero).mpr ?_, hginj⟩
    apply le_antisymm
    · rw [(Metric.nhds_basis_ball.comap g).ge_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖlt
      refine Filter.mem_of_superset ((hopen n).mem_nhds (IsLocalRing.maximalIdeal O ^ n).zero_mem) ?_
      intro x hx
      simp only [Set.mem_preimage, mem_ball_zero_iff]
      rw [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_mul, norm_mul, map_pow, norm_pow]
      calc ‖g ϖ‖ ^ n * ‖g c‖ ≤ ‖g ϖ‖ ^ n * 1 :=
            mul_le_mul_of_nonneg_left (hint c) (by positivity)
        _ < ε := by rw [mul_one]; exact hn
    · intro t ht
      obtain ⟨n, hn⟩ := hsmall t ht
      rw [(Metric.nhds_basis_ball.comap g).mem_iff]
      refine ⟨‖g ϖ‖ ^ n, by positivity, ?_⟩
      intro x hx
      simp only [Set.mem_preimage, mem_ball_zero_iff] at hx
      apply hn
      rw [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have hϖn : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr (pow_ne_zero _ hϖ0)
      have hgϖn : 0 < ‖g (ϖ ^ n)‖ :=
        norm_pos_iff.mpr ((map_ne_zero_iff g hginj).mpr (pow_ne_zero _ hϖ0))
      obtain ⟨y, hy⟩ := hintc (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) (ϖ ^ n))
        (by
          rw [map_div₀, norm_div]
          change ‖g x‖ / ‖g (ϖ ^ n)‖ ≤ 1
          rw [div_le_one hgϖn, map_pow, norm_pow]
          exact hx.le)
      refine ⟨y, ?_⟩
      apply IsFractionRing.injective O (FractionRing O)
      rw [map_mul, hy]
      field_simp
  exact ⟨hemb, hclosed, hintc, hmax⟩

end GlobalTheory.CoefEmbed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFamily
section
namespace GlobalTheory.AdaptedFamilyIwasawaDecomposition

theorem exists_adapted_family (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)) (hIL : I ≤ L)
    (hg : Module.finrank ℚ ↥L = g) :
    ∃ rk ≤ g, ∃ (ε : Fin g → Fin r → ℚ), LinearIndependent ℚ ε ∧ (∀ (i : Fin g), ε i ∈ L) ∧
      (∀ (i : Fin g), (↑i : ℕ) < rk → ε i ∈ I) ∧
      ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i : Fin g | (↑i : ℕ) < rk}) := by
  obtain ⟨C₀, hC₀⟩ := I.exists_isCompl
  have hdis : Disjoint I (C₀ ⊓ L) := hC₀.disjoint.mono_right inf_le_left
  have hsup : I ⊔ (C₀ ⊓ L) = L := by
    rw [← sup_inf_assoc_of_le C₀ hIL, hC₀.sup_eq_top, top_inf_eq]
  have hCL : C₀ ⊓ L ≤ L := inf_le_right
  generalize C₀ ⊓ L = C at hdis hsup hCL
  have hdim : Module.finrank ℚ I + Module.finrank ℚ C = g := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq I C
    rw [hsup, hdis.eq_bot, finrank_bot, hg] at h
    omega
  obtain ⟨k, ⟨bI⟩⟩ : ∃ k, Nonempty (Module.Basis (Fin k) ℚ I) := ⟨_, ⟨Module.finBasis ℚ I⟩⟩
  obtain ⟨m, ⟨bC⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℚ C) := ⟨_, ⟨Module.finBasis ℚ C⟩⟩
  rw [Module.finrank_eq_card_basis bI, Module.finrank_eq_card_basis bC, Fintype.card_fin,
    Fintype.card_fin] at hdim
  clear hg
  subst hdim
  let u : Fin k → Fin r → ℚ := I.subtype ∘ bI
  let v : Fin m → Fin r → ℚ := C.subtype ∘ bC
  have hu : LinearIndependent ℚ u := bI.linearIndependent.map' _ (Submodule.ker_subtype I)
  have hv : LinearIndependent ℚ v := bC.linearIndependent.map' _ (Submodule.ker_subtype C)
  have huI : ∀ i, u i ∈ I := fun i => (bI i).2
  have hvC : ∀ i, v i ∈ C := fun i => (bC i).2
  have hus : Submodule.span ℚ (Set.range u) = I := by
    rw [Set.range_comp, ← Submodule.map_span, bI.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hvs : Submodule.span ℚ (Set.range v) ≤ C := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hvC i
  have hli : LinearIndependent ℚ (Sum.elim u v) :=
    hu.sum_type hv (by rw [hus]; exact hdis.mono_right hvs)
  refine ⟨k, Nat.le_add_right k m, Sum.elim u v ∘ finSumFinEquiv.symm,
    hli.comp _ finSumFinEquiv.symm.injective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using hIL (huI j)
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr] using hCL (hvC j)
  · intro i hi
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using huI j
    · simp at hi
  · intro x hx
    rw [← hus] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨j, rfl⟩
    refine ⟨finSumFinEquiv (Sum.inl j), ?_, ?_⟩
    · simp
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

end GlobalTheory.AdaptedFamilyIwasawaDecomposition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgClosedTranscendentalSpecialisingEverywh
section
open Polynomial IsLocalRing

namespace GlobalTheory

theorem genval_descent {K : Type} [Field K] {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ιV : K →+* V) (sV v : V) (a : K) (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0) :
    ∀ n : ℕ, ∀ p : Polynomial (Polynomial K), p.leadingCoeff.natDegree = n → p ≠ 0 →
      p.eval₂ (eval₂RingHom ιV sV) v = 0 →
      ∃ q : Polynomial K, q ≠ 0 ∧ q.eval₂ ((residue V).comp ιV) (residue V v) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp hpv
  by_cases hq : p.map (evalRingHom a) = 0
  · have hdvd : C (X - C a) ∣ p := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      rw [dvd_iff_isRoot]
      have := congrArg (fun q => q.coeff i) hq
      simpa [coeff_map] using this
    obtain ⟨p', rfl⟩ := hdvd
    have hp' : p' ≠ 0 := by rintro rfl; simp at hp
    have hXa : (X - C a : Polynomial K) ≠ 0 := X_sub_C_ne_zero a
    refine ih p'.leadingCoeff.natDegree ?_ p' rfl hp' ?_
    · rw [← hn, leadingCoeff_mul, leadingCoeff_C,
        natDegree_mul hXa (leadingCoeff_ne_zero.mpr hp'), natDegree_X_sub_C]
      omega
    · rw [eval₂_mul, eval₂_C] at hpv
      have h2 : (eval₂RingHom ιV sV) (X - C a) = sV - ιV a := by simp
      rw [h2] at hpv
      exact (mul_eq_zero.mp hpv).resolve_left hne
  · refine ⟨_, hq, ?_⟩
    have h1 : (residue V).comp (eval₂RingHom ιV sV) =
        ((residue V).comp ιV).comp (evalRingHom a) := by
      apply Polynomial.ringHom_ext
      · intro c; simp
      · have : residue V sV = residue V (ιV a) := by
          rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
        simpa using this
    rw [eval₂_map, ← h1, ← hom_eval₂, hpv, map_zero]

theorem genval_residue_bij {K : Type} [Field K] [IsAlgClosed K] {L : Type} [Field L]
    (V : ValuationSubring L) (ιV : K →+* V) (sV : V) (a : K)
    (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0)
    (halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
      p.eval₂ (eval₂RingHom ιV sV) v = 0) :
    Function.Bijective ((residue V).comp ιV) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro x
  obtain ⟨v, rfl⟩ := residue_surjective x
  obtain ⟨p, hp, hpv⟩ := halg v
  obtain ⟨q, hq, hqv⟩ := genval_descent ιV sV v a hsa hne _ p rfl hp hpv
  refine ⟨q * C (q.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq, ?_⟩
  rw [eval₂_mul, hqv, zero_mul]

theorem genval (K : Type) [Field K] [IsAlgClosed K] : ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by
  let L := AlgebraicClosure (RatFunc K)
  let φ0 : Polynomial K →+* L := algebraMap (Polynomial K) L
  have hφ0 : Function.Injective φ0 := by
    have : φ0 = (algebraMap (RatFunc K) L).comp (algebraMap (Polynomial K) (RatFunc K)) :=
      IsScalarTower.algebraMap_eq _ _ _
    rw [this]
    exact (algebraMap (RatFunc K) L).injective.comp (IsFractionRing.injective _ _)
  let ι : K →+* L := φ0.comp C
  let s : L := φ0 X
  have hev : ∀ P : Polynomial K, P.eval₂ ι s = φ0 P := by
    intro P
    have : eval₂RingHom ι s = φ0 := Polynomial.ringHom_ext (fun c => by simp [ι]) (by simp [s])
    exact congrArg (fun f => f P) this
  refine ⟨L, inferInstance, inferInstance, ι, s, ?_, ?_⟩
  · intro P hP
    rw [hev] at hP
    exact hφ0 (by rw [hP, map_zero])
  · intro a
    let e : Polynomial K ≃+* φ0.range := RingEquiv.ofBijective φ0.rangeRestrict
      ⟨fun x y h => hφ0 (congrArg Subtype.val h), φ0.rangeRestrict_surjective⟩
    let ψ : φ0.range →+* K := (evalRingHom a).comp e.symm.toRingHom
    obtain ⟨V, hAV, hI⟩ :=
      Ideal.image_subset_nonunits_valuationSubring (RingHom.ker ψ) (RingHom.ker_ne_top ψ)
    have hmemA : ∀ P, φ0 P ∈ V := fun P => hAV ⟨P, rfl⟩
    let ιV : K →+* V := ι.codRestrict V (fun c => hmemA (C c))
    let sV : V := ⟨s, hmemA X⟩
    have hsaL : s - ι a ∈ V.nonunits := by
      apply hI
      refine ⟨φ0.rangeRestrict (X - C a), ?_, ?_⟩
      · rw [SetLike.mem_coe, RingHom.mem_ker]
        have : e.symm (φ0.rangeRestrict (X - C a)) = X - C a :=
          e.symm_apply_apply (X - C a)
        show evalRingHom a (e.symm (φ0.rangeRestrict (X - C a))) = 0
        rw [this]
        simp
      · simp [ι, s]
    have hsa : sV - ιV a ∈ maximalIdeal V := by
      have hsaL' : s - ι a ∈ ((↑) : V → L) '' (maximalIdeal V : Set V) := by
        rw [ValuationSubring.image_maximalIdeal]; exact hsaL
      obtain ⟨w, hw, hw'⟩ := hsaL'
      have heq : sV - ιV a = w := by
        apply Subtype.ext
        exact hw'.symm
      rw [heq]
      exact hw
    have hne : sV - ιV a ≠ 0 := by
      intro h
      have h1 := congrArg Subtype.val h
      have h2 : φ0 (X - C a) = 0 := by simpa [ι, s, sV, ιV] using h1
      exact X_sub_C_ne_zero a (hφ0 (by rw [h2, map_zero]))
    have hcomp : (algebraMap V L).comp (eval₂RingHom ιV sV) = φ0 :=
      Polynomial.ringHom_ext (fun c => by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]; rfl)
        (by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]; rfl)
    have halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
        p.eval₂ (eval₂RingHom ιV sV) v = 0 := by
      intro v
      have h1 : IsAlgebraic (Polynomial K) (v : L) :=
        (IsFractionRing.isAlgebraic_iff (Polynomial K) (RatFunc K) L).mpr
          (Algebra.IsAlgebraic.isAlgebraic _)
      obtain ⟨p, hp, hpv⟩ := h1
      refine ⟨p, hp, ?_⟩
      apply IsFractionRing.injective V L
      rw [hom_eval₂, hcomp, map_zero]
      exact hpv
    have hbij := genval_residue_bij V ιV sV a hsa hne halg
    let E := RingEquiv.ofBijective _ hbij
    have hres : residue V sV = E a := by
      show residue V sV = residue V (ιV a)
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
    refine ⟨V, ιV, E.symm.toRingHom.comp (residue V), sV, ?_, ?_, ?_, rfl, ?_⟩
    · exact RingHom.ext fun c => rfl
    · ext c
      exact E.symm_apply_apply c
    · ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        map_eq_zero_iff _ E.symm.injective, residue_eq_zero_iff]
    · show E.symm (residue V sV) = a
      rw [hres, E.symm_apply_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonNonzeroOfPolynomialOnRealLines
section
namespace GlobalTheory

theorem exists_common_nonzero_of_polynomial_on_lines (V : Type) [AddCommGroup V] [Module ℝ V]
    (ι : Type) [Finite ι] (f : ι → V → ℂ)
    (hpoly : ∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ))
    (hne : ∀ i, ∃ v, f i v ≠ 0) : ∃ v, ∀ i, f i v ≠ 0 := by
  classical
  have _ := Fintype.ofFinite ι
  have key : ∀ t : Finset ι, ∃ v, ∀ i ∈ t, f i v ≠ 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j t hj ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := hne j
      choose p hp using fun i => hpoly i v (w - v)
      have hp0 : ∀ i ∈ insert j t, p i ≠ 0 := by
        intro i hi h
        rcases Finset.mem_insert.1 hi with hij | hi
        · subst hij
          apply hw
          have := hp i 1
          simpa [h] using this
        · apply hv i hi
          have := hp i 0
          simpa [h] using this
      have hfin : Set.Finite (⋃ i ∈ (insert j t : Finset ι),
          (fun s : ℝ => (s : ℂ)) ⁻¹' {z | (p i).IsRoot z}) :=
        Set.Finite.biUnion (Finset.finite_toSet _) fun i hi =>
          (Polynomial.finite_setOf_isRoot (hp0 i hi)).preimage Complex.ofReal_injective.injOn
      obtain ⟨s, hs⟩ := hfin.exists_notMem
      refine ⟨v + s • (w - v), fun i hi => ?_⟩
      rw [hp i s]
      intro h0
      apply hs
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨i, hi, h0⟩
  obtain ⟨v, hv⟩ := key Finset.univ
  exact ⟨v, fun i => hv i (Finset.mem_univ i)⟩

end GlobalTheory
end

