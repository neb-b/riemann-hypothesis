module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfIsNilpotentKer
section
universe u_1 u_2

namespace GlobalTheory.NilpotentKernelSurjective

theorem pow_approx {R : Type u_1} {A : Type u_2} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (S : Subalgebra R A)
    (h0 : ∀ y : A, ∃ s ∈ S, y - s ∈ I)
    (h1 : ∀ y ∈ I, ∃ s ∈ S, s ∈ I ∧ y - s ∈ I ^ 2) (n : ℕ) :
    ∀ y ∈ I ^ n, ∃ s ∈ S, s ∈ I ^ n ∧ y - s ∈ I ^ (n + 1) := by
  induction n with
  | zero =>
    intro y _
    obtain ⟨s, hs, hys⟩ := h0 y
    exact ⟨s, hs, by simp, by simpa using hys⟩
  | succ n ih =>
    intro y hy

    have e1 : I ^ n * I ^ 2 = I ^ (n + 1 + 1) := by rw [← pow_add]
    have e2 : I ^ (n + 1) * I = I ^ (n + 1 + 1) := by rw [← pow_succ]
    have e3 : I ^ (n + 1) * I ^ 2 ≤ I ^ (n + 1 + 1) := by
      rw [← pow_add]
      exact Ideal.pow_le_pow_right (by omega)
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨s, hsS, hsI, hse⟩ := ih a ha
      obtain ⟨t, htS, htI, htf⟩ := h1 b hb
      refine ⟨s * t, S.mul_mem hsS htS, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hsI htI
      ·
        have hsplit : a * b - s * t = s * (b - t) + (a - s) * t + (a - s) * (b - t) := by ring
        rw [hsplit]
        refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
        · rw [← e1]
          exact Ideal.mul_mem_mul hsI htf
        · rw [← e2]
          exact Ideal.mul_mem_mul hse htI
        · exact e3 (Ideal.mul_mem_mul hse htf)
    · rintro u v ⟨s, hsS, hsI, hsu⟩ ⟨t, htS, htI, htv⟩
      refine ⟨s + t, S.add_mem hsS htS, Ideal.add_mem _ hsI htI, ?_⟩
      have hsplit : u + v - (s + t) = (u - s) + (v - t) := by ring
      rw [hsplit]
      exact Ideal.add_mem _ hsu htv

theorem aeval_surjective_of_isNilpotent_ker :
    ∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A]
      [inst_2 : Algebra R A] (ε : A →ₐ[R] R), IsNilpotent (RingHom.ker ε) →
      ∀ {d : ℕ} (x : Fin d → A), (∀ (i : Fin d), x i ∈ RingHom.ker ε) →
      (∀ y ∈ RingHom.ker ε, ∃ (l : Fin d → R),
        y - ∑ i : Fin d, l i • x i ∈ RingHom.ker ε ^ (2 : ℕ)) →
      Function.Surjective (⇑(MvPolynomial.aeval x) : MvPolynomial (Fin d) R → A) := by
  intro R A _ _ _ ε hnil d x hx hspan
  set K : Ideal A := RingHom.ker ε with hK
  set S : Subalgebra R A := (MvPolynomial.aeval x).range with hS
  have hxS : ∀ i, x i ∈ S := fun i => ⟨MvPolynomial.X i, MvPolynomial.aeval_X x i⟩

  have h0 : ∀ y : A, ∃ s ∈ S, y - s ∈ K := by
    intro y
    refine ⟨algebraMap R A (ε y), S.algebraMap_mem _, ?_⟩
    rw [hK, RingHom.mem_ker]
    simp

  have h1 : ∀ y ∈ K, ∃ s ∈ S, s ∈ K ∧ y - s ∈ K ^ 2 := by
    intro y hy
    obtain ⟨l, hl⟩ := hspan y hy
    refine ⟨∑ i : Fin d, l i • x i, S.sum_mem fun i _ => S.smul_mem (hxS i) _,
      K.sum_mem fun i _ => K.smul_of_tower_mem _ (hx i), hl⟩

  have hall : ∀ k : ℕ, ∀ y : A, ∃ s ∈ S, y - s ∈ K ^ k := by
    intro k
    induction k with
    | zero => intro y; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro y
      obtain ⟨s, hsS, hs⟩ := ih y
      obtain ⟨t, htS, -, ht⟩ := pow_approx K S h0 h1 k (y - s) hs
      refine ⟨s + t, S.add_mem hsS htS, ?_⟩
      have hsplit : y - (s + t) = y - s - t := by ring
      rw [hsplit]
      exact ht
  obtain ⟨m, hm⟩ := hnil
  intro y
  obtain ⟨s, hsS, hs⟩ := hall m y
  rw [hm, Submodule.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at hs
  obtain ⟨p, hp⟩ := hsS
  exact ⟨p, hp.trans hs.symm⟩

end GlobalTheory.NilpotentKernelSurjective
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffSubstSumLPowPowMvPowerSeries
section
namespace GlobalTheory.LogSubst

open MvPowerSeries

theorem coeff_pow_pow_eq_zero {C σ : Type} [CommRing C] {l : ℕ} (hl : 2 ≤ l)
    {u : MvPowerSeries σ C} (hu : constantCoeff u = 0) {μ : σ →₀ ℕ} {s : ℕ}
    (h : μ.degree ≤ s) : coeff μ (u ^ (l ^ s)) = 0 := by
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero _ hu)
  have : s < l ^ s := Nat.lt_pow_self (by omega)
  exact_mod_cast lt_of_le_of_lt h this

theorem coeff_subst_sum_pow_pow : ∀ (C : Type) [Field C] (σ τ I : Type) [Fintype σ] [Fintype τ] [Fintype I] (l : ℕ), 2 ≤ l → ∀ (co : I → ℕ → C) (t : I → MvPowerSeries σ C) (F : MvPowerSeries σ C) (f : σ → MvPowerSeries τ C), (∀ x, MvPowerSeries.constantCoeff (f x) = 0) → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F = ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, co c s * MvPowerSeries.coeff μ (t c ^ (l ^ s))) → ∀ ν : τ →₀ ℕ, MvPowerSeries.coeff ν (MvPowerSeries.subst f F) = ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s * MvPowerSeries.coeff ν ((MvPowerSeries.subst f (t c) : MvPowerSeries τ C) ^ (l ^ s)) := by
  intro C _ σ τ I _ _ _ l hl co t F f hf ht hF ν
  have hs : HasSubst f := hasSubst_of_constantCoeff_zero hf
  set G : MvPowerSeries σ C :=
    ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s • t c ^ (l ^ s) with hG
  have hord : ((ν.degree + 1 : ℕ) : ℕ∞) ≤ (F - G).order := by
    apply nat_le_order
    intro μ hμ
    rw [map_sub, hF μ, hG, sub_eq_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, coeff_smul]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro s _ hs'
    rw [Finset.mem_range] at hs'
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [coeff_pow_pow_eq_zero hl (ht c) (by omega), mul_zero]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (f i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (hf i)
  have h2 : ((ν.degree + 1 : ℕ) : ℕ∞) ≤ (subst f (F - G) : MvPowerSeries τ C).order := by
    refine le_trans ?_ (le_order_subst hs (F - G))
    calc ((ν.degree + 1 : ℕ) : ℕ∞) = 1 * ((ν.degree + 1 : ℕ) : ℕ∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 hord
  have h3 : coeff ν (subst f (F - G) : MvPowerSeries τ C) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h2
    exact_mod_cast Nat.lt_succ_self _
  rw [← substAlgHom_apply hs, map_sub, map_sub, sub_eq_zero, substAlgHom_apply] at h3
  rw [h3, hG]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_pow, substAlgHom_apply, smul_eq_mul]

end GlobalTheory.LogSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOfMapEqOfPowEqOne
section
namespace GlobalTheory.RootsOfUnityInjective

theorem eq_of_map_eq_of_pow_eq_one {R k : Type} [CommRing R] [IsDomain R] [CommRing k] [IsDomain k]
    (π : R →+* k) {N : ℕ} (hN : (N : k) ≠ 0) {u w : R} (hu : u ^ N = 1) (hw : w ^ N = 1)
    (h : π u = π w) : u = w := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  have hgeom := geom_sum₂_mul u w N
  rw [hu, hw, sub_self] at hgeom
  rcases mul_eq_zero.mp hgeom with h0 | h0
  · exfalso
    have h1 := congrArg π h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h1
    simp only [map_mul, map_pow, h] at h1
    have hpow : (π w) ^ N = 1 := by rw [← map_pow, hw, map_one]
    have hterm : ∀ i ∈ Finset.range N, π w ^ i * π w ^ (N - 1 - i) = π w ^ (N - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hN h2
    · have hw0 : π w ≠ 0 := by
        intro hz
        rw [hz, zero_pow hN0] at hpow
        exact zero_ne_one hpow
      exact pow_ne_zero _ hw0 h2
  · exact sub_eq_zero.mp h0

end GlobalTheory.RootsOfUnityInjective
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsMulInvolutionAddOneMemPow
section
namespace GlobalTheory.NormResidue

open Polynomial

theorem exists_mul_involution_eq_neg_one {k : Type*} [Field k] [Finite k] (σ : k →+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (h2 : (2 : k) ≠ 0) :
    ∃ z : k, z * σ z + 1 = 0 := by
  classical
  obtain ⟨x, hx⟩ := hne
  let F : Subfield k := σ.eqLocusField (RingHom.id k)
  let _ : Fintype F := Fintype.ofFinite F
  have memF : ∀ y : k, y ∈ F ↔ σ y = y := fun y => Iff.rfl
  have hθ : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ]; ring
  have hθ0 : x - σ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  let d : F := ⟨(x - σ x) * (x - σ x), (memF _).2 (by rw [map_mul, hθ]; ring)⟩
  have hd0 : d ≠ 0 := by
    intro h
    have h' : (x - σ x) * (x - σ x) = 0 := congrArg Subtype.val h
    exact hθ0 (mul_self_eq_zero.mp h')
  have hchar : ringChar F ≠ 2 := by
    intro hc
    apply h2
    have h0 : ((2 : ℕ) : F) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    have h0' := congrArg F.subtype h0
    rwa [map_natCast, map_zero, Nat.cast_ofNat] at h0'
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2 + Polynomial.C 1) (g := Polynomial.C (-d) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_add_C (by norm_num) _)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd0))
    (FiniteField.odd_card_of_char_ne_two hchar)
  have hab' := congrArg Subtype.val hab
  simp [d] at hab'
  have ha : σ a = a := (memF _).1 a.2
  have hb : σ b = b := (memF _).1 b.2
  refine ⟨a + b * (x - σ x), ?_⟩
  rw [map_add (f := _), map_mul, ha, hb, hθ]
  linear_combination hab'

theorem exists_mul_involution_add_one_mem_pow (O : Type) [CommRing O] (s : O →+* O)
    (hs : ∀ x, s (s x) = x) (P : Ideal O) [hP : P.IsMaximal] [Finite (O ⧸ P)]
    (hsP : ∀ x ∈ P, s x ∈ P) (hne : ∃ x, s x - x ∉ P) (h2 : (2 : O) ∉ P) (N : ℕ) (z0 : O)
    (hz : N = 0 ∨ z0 * s z0 + 1 ∈ P ^ N) :
    ∃ z : O, z * s z + 1 ∈ P ^ (N + 1) ∧ (N ≠ 0 → z - z0 ∈ P ^ N) := by
  classical
  have hPP : P ≤ P.comap s := fun x hx => hsP x hx
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    letI : Field (O ⧸ P) := Ideal.Quotient.field P
    let σ := Ideal.quotientMap P s hPP
    have hσ : ∀ x, σ (σ x) = x := by
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [σ, Ideal.quotientMap_mk, hs]
    have hne' : ∃ x, σ x ≠ x := by
      obtain ⟨x, hx⟩ := hne
      refine ⟨Ideal.Quotient.mk P x, fun h => hx ?_⟩
      rw [← Ideal.Quotient.eq]
      simpa only [σ, Ideal.quotientMap_mk] using h
    have h2' : (2 : O ⧸ P) ≠ 0 := by
      intro h
      apply h2
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
      exact h
    obtain ⟨w, hw⟩ := exists_mul_involution_eq_neg_one (k := O ⧸ P) σ hσ hne' h2'
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨z, ?_, fun h => absurd rfl h⟩
    rw [zero_add, pow_one, ← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [σ, Ideal.quotientMap_mk, map_add (f := _), map_mul, map_one] using hw
  · have hN0 : N ≠ 0 := hN.ne'
    obtain ⟨e, he_def⟩ : ∃ e, e = z0 * s z0 + 1 := ⟨_, rfl⟩
    have he : e ∈ P ^ N := he_def ▸ hz.resolve_left hN0
    have heP : e ∈ P := Ideal.pow_le_self hN0 he
    obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv h2
    have hh : y + s y - 1 ∈ P := by
      have h1 : y * 2 - 1 ∈ P := by
        have h1e : y * 2 - 1 = -i := by linear_combination hyi
        rw [h1e]
        exact P.neg_mem hi
      have h1' : s y * 2 - 1 ∈ P := by
        have h1s := hsP _ h1
        simpa [map_sub, map_mul, map_ofNat] using h1s
      have h3 : 2 * (y + s y - 1) ∈ P := by
        have h3e : 2 * (y + s y - 1) = (y * 2 - 1) + (s y * 2 - 1) := by ring
        rw [h3e]
        exact P.add_mem h1 h1'
      rcases (Ideal.IsMaximal.isPrime hP).mem_or_mem h3 with h | h
      · exact absurd h h2
      · exact h
    refine ⟨z0 + y * z0 * e, ?_, fun _ => ?_⟩
    · have hse : s e = e := by rw [he_def, map_add (f := _), map_mul, hs, map_one]; ring
      have key : (z0 + y * z0 * e) * s (z0 + y * z0 * e) + 1
          = e * (1 - (y + s y) + (y + s y) * e) + e * (e * (y * z0 * s y * s z0)) := by
        rw [map_add (f := _), map_mul, map_mul, hse]
        rw [he_def]
        ring
      rw [key, pow_succ]
      refine Ideal.add_mem _ (Ideal.mul_mem_mul he ?_)
        (Ideal.mul_mem_mul he (Ideal.mul_mem_right _ _ heP))
      have hx : 1 - (y + s y) + (y + s y) * e = -(y + s y - 1) + (y + s y) * e := by ring
      rw [hx]
      exact P.add_mem (P.neg_mem hh) (Ideal.mul_mem_left _ _ heP)
    · have hx : z0 + y * z0 * e - z0 = y * z0 * e := by ring
      rw [hx]
      exact Ideal.mul_mem_left _ _ he

end GlobalTheory.NormResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPthRootOfDerivationZero
section
open scoped BigOperators
open Polynomial IntermediateField

namespace GlobalTheory

theorem minpoly_eq_X_pow_sub_C_of_pow_mem {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : Subfield K) (hM : ∀ y : K, y ^ p ∈ M) (x : K) (hx : x ∉ M) :
    minpoly M x = X ^ p - C (⟨x ^ p, hM x⟩ : M) := by
  have hp : p.Prime := Fact.out
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    apply hx
    have h1 : (b : K) ^ p = x ^ p := by
      have := congrArg (fun z : M => (z : K)) hb
      simpa using this
    have h2 : (b : K) = x := frobenius_inj K p (by simpa [frobenius_def] using h1)
    rw [← h2]; exact b.2
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_self _
  · exact monic_X_pow_sub_C _ hp.ne_zero

theorem isIntegral_of_pow_mem_subfield {K : Type} [Field K] (p : ℕ) [Fact p.Prime]
    (M : Subfield K) (hM : ∀ y : K, y ^ p ∈ M) (x : K) : IsIntegral M x := by
  have hp : p.Prime := Fact.out
  refine ⟨X ^ p - C (⟨x ^ p, hM x⟩ : M), monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  exact sub_self _

theorem exists_pow_eq_of_forall_derivation_eq_zero (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (f : K) (hf : ∀ D : Derivation ℤ K K, D f = 0) : ∃ h : K, h ^ p = f := by
  have hp : p.Prime := Fact.out
  by_contra hne
  let S : Set (Subfield K) := {M | (∀ y : K, y ^ p ∈ M) ∧ f ∉ M}
  have h0 : (frobenius K p).fieldRange ∈ S := by
    refine ⟨fun y => ⟨y, rfl⟩, ?_⟩
    rintro ⟨y, hy⟩
    exact hne ⟨y, hy⟩
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    refine ⟨sSup c, ⟨fun z => (le_sSup hy : y ≤ sSup c) ((hcS hy).1 z), ?_⟩,
      fun z hz => le_sSup hz⟩
    rw [Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hc.directedOn]
    rintro ⟨z, hz, hfz⟩
    exact (hcS hz).2 hfz) _ h0
  obtain ⟨hMp, hMf⟩ := hM.prop
  have hrank : ∀ x : K, x ∉ M → Module.finrank M M⟮x⟯ = p := by
    intro x hx
    rw [adjoin.finrank (isIntegral_of_pow_mem_subfield p M hMp x),
      minpoly_eq_X_pow_sub_C_of_pow_mem p M hMp x hx, natDegree_X_pow_sub_C _]
  have htop : ∀ x : K, x ∈ M⟮f⟯ := by
    intro x
    by_cases hx : x ∈ M
    · exact (M⟮f⟯).algebraMap_mem ⟨x, hx⟩
    have hle : M ≤ (M⟮x⟯).toSubfield := fun z hz => (M⟮x⟯).algebraMap_mem ⟨z, hz⟩
    have hfx : f ∈ M⟮x⟯ := by
      by_contra hcon
      have h1 : (M⟮x⟯).toSubfield ∈ S := ⟨fun y => hle (hMp y), hcon⟩
      exact hx (hM.le_of_ge h1 hle (mem_adjoin_simple_self M x))
    haveI := adjoin.finiteDimensional (isIntegral_of_pow_mem_subfield p M hMp x)
    have heq : M⟮f⟯ = M⟮x⟯ :=
      eq_of_le_of_finrank_eq (adjoin_simple_le_iff.mpr hfx) (by rw [hrank f hMf, hrank x hx])
    rw [heq]; exact mem_adjoin_simple_self M x
  have hsurj : Function.Surjective (aeval f : M[X] →ₐ[M] K) := by
    intro x
    have h1 : x ∈ (M⟮f⟯).toSubalgebra := htop x
    rw [adjoin_simple_toSubalgebra_of_isAlgebraic
      (isIntegral_of_pow_mem_subfield p M hMp f).isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h1
    exact h1
  have hd : ∀ q : M[X], aeval f q = 0 → aeval f ((derivative' : Derivation M M[X] M[X]) q) = 0 := by
    intro q hq
    obtain ⟨r, rfl⟩ := minpoly.dvd M f hq
    have h1 : aeval f (derivative (minpoly M f)) = 0 := by
      rw [minpoly_eq_X_pow_sub_C_of_pow_mem p M hMp f hMf]
      simp [derivative_X_pow]
    simp [derivative'_apply, derivative_mul, h1]
  have h2 := hf ((Derivation.liftOfSurjective hsurj hd).restrictScalars ℤ)
  have h3 := Derivation.liftOfSurjective_apply hsurj hd X
  rw [Derivation.restrictScalars_apply] at h2
  simp only [aeval_X, derivative'_apply, derivative_X, map_one] at h3
  exact one_ne_zero (h3.symm.trans h2)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusPowerEmbeddings
section
namespace GlobalTheory

theorem exists_forall_eq_pow_of_finite_field (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F]
    (k : Type) [Field k] [CharP k p] (a b : F →+* k) : ∃ n : ℕ, ∀ x, b x = a x ^ p ^ n := by
  have : CharP F p := RingHom.charP a a.injective p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra F k := a.toAlgebra
  have : IsScalarTower (ZMod p) F k :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let b' : F →ₐ[ZMod p] k :=
    { b with
      commutes' := fun r => RingHom.congr_fun
        (Subsingleton.elim (b.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) k)) r }
  obtain ⟨n, hn⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p F (b'.restrictNormal' F)
  refine ⟨n, fun x => ?_⟩
  have h := AlgHom.restrictNormal_commutes b' F x
  have h2 : b'.restrictNormal F x = x ^ p ^ n := by
    have := hn x
    rw [Nat.card_zmod] at this
    exact this
  rw [h2, map_pow] at h
  exact h.symm

theorem exists_forall_eq_pow_of_ker_le (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (k : Type) [Field k] [CharP k p] (σ₀ σ : OE →+* k)
    (h : ∀ x, σ₀ x = 0 → σ x = 0) : ∃ n : ℕ, ∀ x, σ x = σ₀ x ^ p ^ n := by
  let I : Ideal OE := RingHom.ker σ₀
  have : I.IsPrime := RingHom.ker_isPrime σ₀
  have hp : (p : OE ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    simp [I, RingHom.mem_ker]
  have : Module.Finite ℤ (OE ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mk I).toIntAlgHom.toLinearMap
      Ideal.Quotient.mk_surjective
  have : Finite (OE ⧸ I) := by
    refine Module.finite_of_fg_torsion _ (fun x => ⟨⟨(p : ℤ), ?_⟩, ?_⟩)
    · exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    · change (p : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hp, zero_mul]
  let : Field (OE ⧸ I) := (Finite.isField_of_domain (OE ⧸ I)).toField
  obtain ⟨n, hn⟩ := exists_forall_eq_pow_of_finite_field p (OE ⧸ I) k
    (Ideal.Quotient.lift I σ₀ (fun _ hx => hx)) (Ideal.Quotient.lift I σ (fun x hx => h x hx))
  exact ⟨n, fun x => hn (Ideal.Quotient.mk I x)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubstEqOfCoeffEqOfKilled
section
namespace GlobalTheory

theorem subst_eq_of_coeff_eq_of_killed :
    ∀ (C : Type) [Field C] (σ τ : Type) [Fintype σ] [Fintype τ] (P : σ → Prop) (f : σ → MvPowerSeries τ C) (F F' : MvPowerSeries σ C), (∀ w, MvPowerSeries.constantCoeff (f w) = 0) → (∀ w, ¬ P w → f w = 0) → (∀ μ : σ →₀ ℕ, (∀ w ∈ μ.support, P w) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F') → MvPowerSeries.subst f F = MvPowerSeries.subst f F' := by
  intro C _ σ τ _ _ P f F F' h0 hk hF
  have hs : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  ext ν
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun μ => ?_
  by_cases h : ∀ w ∈ μ.support, P w
  · rw [hF μ h]
  · push Not at h
    obtain ⟨w, hw, hP⟩ := h
    have hz : (μ.prod fun s e => f s ^ e) = 0 := by
      refine Finset.prod_eq_zero hw ?_
      show f w ^ μ w = 0
      rw [hk w hP]
      exact zero_pow (Finsupp.mem_support_iff.mp hw)
    rw [hz]
    simp

end GlobalTheory
end

