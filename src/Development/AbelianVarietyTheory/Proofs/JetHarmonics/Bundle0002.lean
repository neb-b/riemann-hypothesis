module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfIntertwinerOfIrreducible
section
namespace GlobalTheory

open scoped InnerProductSpace

theorem exists_isometry_of_intertwiner_of_irreducible
    (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂]
    (ι : Type) (π₁ : ι → (V₁ →L[ℂ] V₁)) (π₂ : ι → (V₂ →L[ℂ] V₂)) (T : V₁ ≃ₗ[ℂ] V₂)
    (h₁ : ∀ i v, ‖π₁ i v‖ = ‖v‖) (h₂ : ∀ i v, ‖π₂ i v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ V₁, (∀ i, ∀ v ∈ S, π₁ i v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hT : ∀ i v, T (π₁ i v) = π₂ i (T v)) :
    ∃ φ : V₁ ≃ₗᵢ[ℂ] V₂, ∀ i v, φ (π₁ i v) = π₂ i (φ v) := by
  rcases subsingleton_or_nontrivial V₁ with hV | hV
  · refine ⟨⟨T, fun v => ?_⟩, hT⟩
    rw [Subsingleton.elim v 0]
    simp
  let p₁ : ι → (V₁ →ₗᵢ[ℂ] V₁) := fun i => ⟨(π₁ i : V₁ →ₗ[ℂ] V₁), h₁ i⟩
  let p₂ : ι → (V₂ →ₗᵢ[ℂ] V₂) := fun i => ⟨(π₂ i : V₂ →ₗ[ℂ] V₂), h₂ i⟩
  have i₁ : ∀ i a b, ⟪π₁ i a, π₁ i b⟫_ℂ = ⟪a, b⟫_ℂ := fun i a b => (p₁ i).inner_map_map a b
  have i₂ : ∀ i a b, ⟪π₂ i a, π₂ i b⟫_ℂ = ⟪a, b⟫_ℂ := fun i a b => (p₂ i).inner_map_map a b
  have s₁ : ∀ i, Function.Surjective (π₁ i) := fun i =>
    (LinearMap.injective_iff_surjective (f := (π₁ i : V₁ →ₗ[ℂ] V₁))).1 (p₁ i).injective
  let X : Module.End ℂ V₁ :=
    (LinearMap.adjoint (T : V₁ →ₗ[ℂ] V₂)).comp (T : V₁ →ₗ[ℂ] V₂)
  have hX : ∀ a b, ⟪X a, b⟫_ℂ = ⟪T a, T b⟫_ℂ := fun a b =>
    LinearMap.adjoint_inner_left (T : V₁ →ₗ[ℂ] V₂) b (T a)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue X
  have htop : X.eigenspace c = ⊤ := by
    refine (hirr _ ?_).resolve_left hc
    intro i v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    refine ext_inner_right ℂ fun u => ?_
    obtain ⟨w, rfl⟩ := s₁ i u
    rw [hX, hT, hT, i₂, ← hX, hv, ← map_smul, i₁]
  have hall : ∀ v, ‖T v‖ = Real.sqrt ‖c‖ * ‖v‖ := by
    intro v
    have hv : X v = c • v := Module.End.mem_eigenspace_iff.1 (htop ▸ Submodule.mem_top)
    have h := hX v v
    rw [hv, inner_smul_left] at h
    have h' := congrArg norm h
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
    simp only [RCLike.norm_conj, norm_pow, RCLike.norm_ofReal, abs_norm, norm_norm, Complex.coe_algebraMap, Complex.norm_real] at h'
    have e : ‖T v‖ ^ 2 = (Real.sqrt ‖c‖ * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (norm_nonneg c), h']
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 e
  have hr : Real.sqrt ‖c‖ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
    have := hall v
    rw [h0, zero_mul, norm_eq_zero] at this
    exact hv (T.map_eq_zero_iff.1 this)
  have hr' : (((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero hr
  refine ⟨⟨T.trans (LinearEquiv.smulOfNeZero ℂ V₂ _ hr'), fun v => ?_⟩, fun i v => ?_⟩
  · change ‖(((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T v‖ = ‖v‖
    rw [norm_smul, hall, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← mul_assoc,
      inv_mul_cancel₀ hr, one_mul]
  · change (((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T (π₁ i v)
      = π₂ i ((((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T v)
    rw [hT, map_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
section
open NumberField

namespace GlobalTheory.SplitEmbSep


open NumberField in
theorem _root_.GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C]
    {x : C} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  rw [← Polynomial.aeval_def, hm.as_sum] at hp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
    algebraMap_int_eq, eq_intCast, map_intCast] at hp
  set n := p.natDegree
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at hp
    simp at hp
  have hs : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr hn.ne'
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs
    (fun i => ((p.coeff i : ℤ) : C) * x ^ i)
  have hxn : x ^ n = -∑ i ∈ Finset.range n, ((p.coeff i : ℤ) : C) * x ^ i :=
    eq_neg_of_add_eq_zero_left hp
  have h1 : ‖x‖ ^ n ≤ ‖x‖ ^ i := by
    calc ‖x‖ ^ n = ‖x ^ n‖ := (norm_pow x n).symm
      _ = ‖∑ i ∈ Finset.range n, ((p.coeff i : ℤ) : C) * x ^ i‖ := by rw [hxn, norm_neg]
      _ ≤ ‖((p.coeff i : ℤ) : C) * x ^ i‖ := hle
      _ = ‖((p.coeff i : ℤ) : C)‖ * ‖x‖ ^ i := by rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖x‖ ^ i := by
        gcongr
        exact IsUltrametricDist.norm_intCast_le_one C _
      _ = ‖x‖ ^ i := one_mul _
  have h2 : ‖x‖ ^ i < ‖x‖ ^ n := pow_lt_pow_right₀ h (Finset.mem_range.mp hi)
  exact absurd h1 (not_le.mpr h2)


open NumberField in
theorem _root_.GlobalTheory.SplitEmbSep.norm_det_lt_one {C ι : Type*} [NormedField C] [IsUltrametricDist C]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C) (hM : ∀ i j, ‖M i j‖ ≤ 1) (k : ι)
    (hk : ∀ i, ‖M i k‖ < 1) : ‖M.det‖ < 1 := by
  rw [Matrix.det_apply]
  obtain ⟨σ, -, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty (α := Equiv.Perm ι))
    (fun σ => Equiv.Perm.sign σ • ∏ i, M (σ i) i)
  refine lt_of_le_of_lt hle ?_
  have hprod : ‖∏ i, M (σ i) i‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hk _)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hM _ _))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs, Units.smul_def] using hprod


open NumberField in
theorem _root_.GlobalTheory.SplitEmbSep.one_le_norm_intCast {C : Type*} [NormedField C] [IsUltrametricDist C] {g : ℕ}
    (hg : g.Prime) (hgC : ‖(g : C)‖ < 1) {d : ℤ} (hd : ¬ (g : ℤ) ∣ d) : 1 ≤ ‖(d : C)‖ := by
  obtain ⟨a, b, hab⟩ :=
    ((Nat.prime_iff_prime_int.mp hg).irreducible.coprime_iff_not_dvd).mpr hd
  have hC : (a : C) * (g : C) + (b : C) * (d : C) = 1 := by exact_mod_cast congrArg (Int.cast (R := C)) hab
  have h1 : ‖(a : C) * (g : C)‖ < 1 := by
    rw [norm_mul]
    calc ‖(a : C)‖ * ‖(g : C)‖ ≤ 1 * ‖(g : C)‖ := by
          gcongr
          exact IsUltrametricDist.norm_intCast_le_one C a
      _ < 1 := by rwa [one_mul]
  have h2 : 1 ≤ max ‖(a : C) * (g : C)‖ ‖(b : C) * (d : C)‖ := by
    rw [← norm_one (α := C), ← hC]
    exact IsUltrametricDist.norm_add_le_max _ _
  have h3 : 1 ≤ ‖(b : C) * (d : C)‖ := by
    rcases le_max_iff.mp h2 with h | h
    · exact absurd h (not_le.mpr h1)
    · exact h
  calc 1 ≤ ‖(b : C)‖ * ‖(d : C)‖ := by rwa [← norm_mul]
    _ ≤ 1 * ‖(d : C)‖ := by
      gcongr
      exact IsUltrametricDist.norm_intCast_le_one C b
    _ = ‖(d : C)‖ := one_mul _


open NumberField in
theorem _root_.GlobalTheory.SplitEmbSep.not_dvd_discr_of_split {g : ℕ} (hg : g.Prime) (E : Type*) [Field E]
    [NumberField E]
    (h : (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    ¬ (g : ℤ) ∣ discr E := by
  have hgp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  set p : Ideal ℤ := Ideal.span {(g : ℤ)} with hp_def
  have hp0 : p ≠ ⊥ := by simpa [hp_def] using hgp.ne_zero
  haveI hpprime : p.IsPrime := (Ideal.span_singleton_prime hgp.ne_zero).mpr hgp
  haveI hpmax : p.IsMaximal := hpprime.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E hp0
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← IsDedekindDomain.coe_primesOverFinset hp0, Set.ncard_coe_finset]
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact hp0
  have hge : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 E),
      1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    have hP' : P ∈ p.primesOver (𝓞 E) := by
      rw [← IsDedekindDomain.coe_primesOverFinset hp0]
      exact hP
    haveI := hP'.1
    haveI := hP'.2
    have he : p.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero hmap hP'.1
        (Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def P p)))
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he (Ideal.inertiaDeg'_pos p P).ne')
  have hone := (Finset.sum_eq_sum_iff_of_le hge).mp (by
    rw [← Finset.card_eq_sum_ones, hcard, hsum])
  rw [NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hgp]
  intro P hPprime hgP
  have hunder : p = P.under ℤ := by
    have hle : p ≤ P.under ℤ := by
      rw [hp_def, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (by simpa using hgP)
    exact hpmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  haveI : P.LiesOver p := ⟨hunder⟩
  have hPF : P ∈ IsDedekindDomain.primesOverFinset p (𝓞 E) := by
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp0]
    exact ⟨hPprime, this⟩
  have he := Nat.eq_one_of_mul_eq_one_right (hone P hPF).symm
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
  exact he

end GlobalTheory.SplitEmbSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HomValueCongruentIntModPrime
section
namespace GlobalTheory

theorem mem_span_prime_of_not_isUnit_of_pow_sub_mem {O : Type} [CommRing O] [IsLocalRing O] (g : ℕ)
    (hg : g.Prime) (y : O) (hy : y ^ g - y ∈ Ideal.span {(g : O)}) (hn : ¬ IsUnit y) :
    y ∈ Ideal.span {(g : O)} := by
  have hm : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal y).mpr hn
  have hpos : 1 ≤ g - 1 := by have := hg.two_le; omega
  have hz : y ^ (g - 1) ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hpos
    rw [hk, pow_add, pow_one]
    exact Ideal.mul_mem_right _ _ hm
  obtain ⟨u, hu⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((IsLocalRing.mem_maximalIdeal _).mp hz)
  have e : y ^ g = y * y ^ (g - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hg.one_lt.le]
  have hy' : y = -(y ^ g - y) * ↑u⁻¹ := by
    calc y = y * (↑u * ↑u⁻¹) := by simp
      _ = -(y ^ g - y) * ↑u⁻¹ := by rw [hu, e]; ring
  rw [hy']
  exact Ideal.mul_mem_right _ _ (neg_mem hy)

theorem hom_value_congruent_int_mod_prime :
    ∀ (A O : Type) [CommRing A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (σ : A →+* O) (x : A), (∃ i : ℤ, σ x - (i : O) ∈ Ideal.span {(g : O)}) ∧ (¬ IsUnit (σ x) → σ x ∈ Ideal.span {(g : O)}) := by
  intro A O _ _ _ g hg hgu hA σ x
  have hy : σ x ^ g - σ x ∈ Ideal.span {(g : O)} := by
    have h := Ideal.mem_map_of_mem σ (hA x)
    rw [Ideal.map_span, Set.image_singleton, map_natCast, map_sub, map_pow] at h
    exact h
  refine ⟨?_, fun hn => mem_span_prime_of_not_isUnit_of_pow_sub_mem g hg (σ x) hy hn⟩
  have : Fact g.Prime := ⟨hg⟩
  have : NeZero g := ⟨hg.ne_zero⟩
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hgu
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  have hgk : ((g : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hgm
  have : CharP (IsLocalRing.ResidueField O) g := (CharP.charP_iff_prime_eq_zero hg).mpr hgk
  have hfix : IsLocalRing.residue O (σ x) ^ g = IsLocalRing.residue O (σ x) := by
    have h := (IsLocalRing.residue_eq_zero_iff _).mpr (hspan hy)
    rwa [map_sub, map_pow, sub_eq_zero] at h
  obtain ⟨a, ha⟩ : ∃ a : ZMod g,
      IsLocalRing.residue O (σ x) = ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O) a := by
    by_contra hno
    simp only [not_exists] at hno
    classical
    have hpoly : (Polynomial.X ^ g - Polynomial.X : Polynomial (IsLocalRing.ResidueField O)) ≠ 0 :=
      Polynomial.X_pow_sub_X_ne_zero hg.one_lt
    have hnot : IsLocalRing.residue O (σ x) ∉
        Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)) := by
      intro h
      obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h
      exact hno b hb.symm
    have hsub : (insert (IsLocalRing.residue O (σ x))
        (Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)))).val ⊆
        (Polynomial.X ^ g - Polynomial.X : Polynomial (IsLocalRing.ResidueField O)).roots := by
      intro z hz
      have hz' : z ∈ insert (IsLocalRing.residue O (σ x))
        (Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O))) := hz
      rw [Polynomial.mem_roots hpoly, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hz' with h | h
      · rw [h]; exact hfix
      · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp h
        rw [← map_pow, ZMod.pow_card]
    have hcard := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Polynomial.natDegree_X_pow_sub_X hg.one_lt, Finset.card_insert_of_notMem hnot,
      Finset.card_image_of_injective _ (RingHom.injective _), Finset.card_univ, ZMod.card] at hcard
    omega
  have ha' : IsLocalRing.residue O (σ x) = IsLocalRing.residue O ((a.val : ℕ) : O) := by
    rw [ha, map_natCast, ← map_natCast (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)),
      ZMod.natCast_zmod_val]
  have hnu : ¬ IsUnit (σ x - ((a.val : ℕ) : O)) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, ha', sub_self]
  have hne : Ideal.span {(g : O)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hgu
  have : Nontrivial (O ⧸ Ideal.span {(g : O)}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : CharP (O ⧸ Ideal.span {(g : O)}) g := (CharP.charP_iff_prime_eq_zero hg).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _)
  have hyQ : Ideal.Quotient.mk (Ideal.span {(g : O)}) (σ x) ^ g
      - Ideal.Quotient.mk (Ideal.span {(g : O)}) (σ x) = 0 := by
    rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact hy
  have hnQ : ((a.val : ℕ) : O ⧸ Ideal.span {(g : O)}) ^ g = ((a.val : ℕ) : O ⧸ Ideal.span {(g : O)}) := by
    rw [← map_natCast (ZMod.castHom (dvd_refl g) (O ⧸ Ideal.span {(g : O)})), ← map_pow, ZMod.pow_card]
  have hsh : (σ x - ((a.val : ℕ) : O)) ^ g - (σ x - ((a.val : ℕ) : O)) ∈ Ideal.span {(g : O)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_sub, map_natCast, sub_pow_char, hnQ]
    linear_combination hyQ
  refine ⟨(a.val : ℤ), ?_⟩
  rw [Int.cast_natCast]
  exact mem_span_prime_of_not_isUnit_of_pow_sub_mem g hg _ hsh hnu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.Imports
section
open Finset

namespace GlobalTheory.LamSize

theorem main : ∀ (C b T T' : ℝ) (r N : ℕ), 0 ≤ C → 3 ≤ b → (N : ℝ) ≤ b → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T' → 1 ≤ b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) ∧ (N : ℝ) * b ^ (11 * (2 * r + 2)) ≤ (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (T * T') := by
  intro C b T T' r N hC hb hN hT hT'
  have hm1 : 1 ≤ 2 * r + 2 := by omega
  generalize 2 * r + 2 = m at *
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨Real.one_le_rpow hb1 (by positivity), ?_⟩
  have hp : 0 < b ^ (-(C * (m : ℝ))) := Real.rpow_pos_of_pos hb0 _
  have hTT : b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))) ≤ T * T' :=
    mul_le_mul hT hT' hp.le (hp.le.trans hT)
  have key : (b ^ ((6 + C) * (m : ℝ))) ^ 2 * (b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))))
      = b ^ (12 * m) := by
    rw [sq, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc (N : ℝ) * b ^ (11 * m) ≤ b * b ^ (11 * m) := by gcongr
    _ = b ^ (11 * m + 1) := by ring
    _ ≤ b ^ (12 * m) := pow_le_pow_right₀ hb1 (by omega)
    _ = _ := key.symm
    _ ≤ _ := by gcongr

end GlobalTheory.LamSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsAlt
section
namespace GlobalTheory.JetConstSq

theorem main : ∀ C₃ CΛ C₀ C₂ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (b Λ : ℝ) (r n₀ p₀ : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((r : ℝ) + 1) ^ 2 → 2 * (3 * b) ^ (2 * n₀) * (1 * (C₂ * Λ ^ 2) ^ (r + 1)) * b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) ≤ b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
  intro C₃ CΛ C₀ C₂ h3 hΛ h0 h2
  refine ⟨40 + CΛ + C₂ + 2 * C₃ * (C₀ + 9), ?_⟩
  intro b Λ r n₀ p₀ hb hΛ1 hΛb hn hp
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hnR : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have hm : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have hq : ((2 * p₀ + n₀ : ℕ) : ℝ) = 2 * (p₀ : ℝ) + n₀ := by push_cast; ring
  have hr : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  rw [hm] at hΛb
  rw [hm, hq]
  have hs : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith

  have hC2 : C₂ ≤ b ^ C₂ := by
    have h1 : (1 : ℝ) ≤ Real.log b := by
      rw [Real.le_log_iff_exp_le hb0]
      have := Real.exp_one_lt_d9
      linarith
    rw [Real.rpow_def_of_pos hb0]
    have h4 : C₂ ≤ Real.log b * C₂ := by nlinarith
    have := Real.add_one_le_exp (Real.log b * C₂)
    linarith
  have e1 : (2 : ℝ) ≤ b ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
  have e2 : (3 * b) ^ (2 * n₀) ≤ b ^ (4 * (n₀ : ℝ)) := by
    have : (3 * b) ^ (2 * n₀) ≤ (b * b) ^ (2 * n₀) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    refine this.trans (le_of_eq ?_)
    rw [show (4 * (n₀ : ℝ)) = ((4 * n₀ : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have e3 : 1 * (C₂ * Λ ^ 2) ^ (r + 1) ≤
      b ^ ((C₂ + 2 * (CΛ * (2 * ((r : ℝ) + 1)))) * ((r : ℝ) + 1)) := by
    rw [one_mul, Real.rpow_mul hb0.le, ← hr, Real.rpow_natCast]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [Real.rpow_add hb0, mul_comm (2 : ℝ) (CΛ * _), Real.rpow_mul hb0.le, Real.rpow_two, hr]
    exact mul_le_mul hC2 (pow_le_pow_left₀ (by linarith) hΛb 2) (by positivity) (by positivity)
  generalize ((r : ℝ) + 1) = s at *
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hs12 : s ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  calc _ ≤ b ^ (1 : ℝ) * b ^ (4 * (n₀ : ℝ)) * b ^ ((C₂ + 2 * (CΛ * (2 * s))) * s) *
        b ^ (2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        gcongr
    _ = b ^ (1 + 4 * (n₀ : ℝ) + (C₂ + 2 * (CΛ * (2 * s))) * s +
        2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        have a1 : 1 + 4 * (n₀ : ℝ) ≤ 40 * (2 * s) ^ 4 := by nlinarith
        have a2 : C₂ * s ≤ C₂ * (2 * s) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ h2.le; nlinarith
        have a3 : CΛ * (4 * s ^ 2) ≤ CΛ * (2 * s) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ hΛ; nlinarith
        have a4 : 2 * (p₀ : ℝ) + n₀ ≤ (C₀ + 9) * (2 * s) ^ 2 := by
          have : 0 ≤ C₀ * s ^ 2 := by positivity
          nlinarith
        have a5 : 2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀) ≤
            2 * C₃ * (2 * s) ^ 2 * ((C₀ + 9) * (2 * s) ^ 2) :=
          mul_le_mul_of_nonneg_left a4 (by positivity)
        nlinarith

end GlobalTheory.JetConstSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedFDerivProdCoordAt
section
open scoped BigOperators

namespace GlobalTheory.CoordProdDeriv

theorem card_filter_cons {g k : ℕ} (a : Fin g) (σ : Fin k → Fin g) (i : Fin g) :
    (Finset.univ.filter (fun j => (Fin.cons a σ : Fin (k + 1) → Fin g) j = i)).card
      = (Finset.univ.filter (fun j => σ j = i)).card + if a = i then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [add_comm]

theorem fderiv_prod_iteratedDeriv {g : ℕ} (f : Fin g → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (n : Fin g → ℕ) (z : Fin g → ℂ) :
    HasFDerivAt (fun z : Fin g → ℂ => ∏ i, iteratedDeriv (n i) (f i) (z i))
      (∑ a : Fin g, (∏ i, iteratedDeriv (n i + if a = i then 1 else 0) (f i) (z i)) •
        (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ)) z := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin g)),
      HasFDerivAt (fun z : Fin g → ℂ => iteratedDeriv (n i) (f i) (z i))
        (iteratedDeriv (n i + 1) (f i) (z i) •
          (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ)) z := by
    intro i _
    have hd : Differentiable ℂ (iteratedDeriv (n i) (f i)) :=
      ((hf i).contDiff (n := ⊤)).differentiable_iteratedDeriv _ (by
        exact WithTop.coe_lt_top _)
    have h1 : HasDerivAt (iteratedDeriv (n i) (f i)) (iteratedDeriv (n i + 1) (f i) (z i)) (z i) := by
      rw [iteratedDeriv_succ]
      exact (hd (z i)).hasDerivAt
    exact h1.comp_hasFDerivAt z
      (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).hasFDerivAt
  have h2 := HasFDerivAt.finsetProd h
  refine h2.congr_fderiv (Eq.symm ?_)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  congr 2
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi).symm, add_zero]
  · rw [if_pos rfl]

theorem iteratedFDeriv_prod_coord_at {g : ℕ} (f : Fin g → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (k : ℕ) :
    ∀ (ys : Fin k → Fin g → ℂ) (z : Fin g → ℂ),
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) z ys
        = ∑ σ : Fin k → Fin g, (∏ j, ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) (z i) := by
  have hF : ContDiff ℂ ⊤ (fun z : Fin g → ℂ => ∏ i, f i (z i)) :=
    contDiff_prod fun i _ => ((hf i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)
  induction k with
  | zero => intro ys z; simp
  | succ k ih =>
    intro ys z
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i))) z :=
      hF.differentiable_iteratedFDeriv (m := k) (by exact WithTop.coe_lt_top _) z
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd]
    have e : (fun z => iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) z (Fin.tail ys))
        = fun z => ∑ σ : Fin k → Fin g, (∏ j, Fin.tail ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) (z i) :=
      funext fun z => ih _ z
    rw [e]
    have h3 := HasFDerivAt.fun_sum (u := Finset.univ) (fun (σ : Fin k → Fin g) _ =>
      (fderiv_prod_iteratedDeriv f hf
        (fun i => (Finset.univ.filter (fun j => σ j = i)).card) z).const_mul
        (∏ j, Fin.tail ys j (σ j)))
    rw [h3.fderiv]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
    have e2 : (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)) (a, σ) = Fin.cons a σ := rfl
    simp only [e2, card_filter_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    ring

theorem iteratedFDeriv_prod_coord :
    ∀ (g k : ℕ) (f : Fin g → ℂ → ℂ) (ys : Fin k → Fin g → ℂ), (∀ i, Differentiable ℂ (f i)) →
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) 0 ys
        = ∑ σ : Fin k → Fin g, (∏ j, ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) 0 :=
  fun _ k f ys hf => iteratedFDeriv_prod_coord_at f hf k ys 0

end GlobalTheory.CoordProdDeriv
end

