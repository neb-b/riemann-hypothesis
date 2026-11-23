module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogMv

open PowerSeries

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [coeff_subst (HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem expMv_eq_subst {G : MvPowerSeries σ ℂ_[p]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (exp ℂ_[p]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem logMv_eq_subst {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 1) :
    GL3Theta.logMv F = (log ℂ_[p]).subst (F - 1) := by
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  ext α
  rw [coeff_subst_range h1]
  show GL3Theta.logMv F α = _
  rw [GL3Theta.logMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_log]
  split_ifs
  · simp
  · simp
    ring

theorem exp_neg_log_one_var (K : Type*) [Field K] [CharZero K] :
    (exp K).subst (-log K) * (1 + X : PowerSeries K) = 1 := by
  have h0 : constantCoeff (-log K) = 0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' h0
  have e : (1 + X) * PowerSeries.derivative (log K) = 1 := by
    rw [derivative_log]
    ext n
    cases n with
    | zero => simp [add_mul]
    | succ n => simp [add_mul, coeff_succ_X_mul, coeff_one, pow_succ]
  refine derivative.ext ?_ ?_
  · rw [Derivation.leibniz, derivative_subst hs, derivative_exp, map_neg, derivative_one, map_add (f := _),
      derivative_one, derivative_X]
    simp only [smul_eq_mul]
    linear_combination (-(exp K).subst (-log K)) * e
  · have : constantCoeff ((exp K).subst (-log K) : PowerSeries K) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
      · simp
      · intro k hk
        simp [hk]
    simp [this]

theorem expMv_neg_logMv_mul : ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (F : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff F = 1 → MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 ∧ expMv (-GL3Theta.logMv F) * F = 1 := by
  intro p _ σ F hF
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  have hs := HasSubst.of_constantCoeff_zero h1
  have h0 : MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 := by
    rw [logMv_eq_subst hF]
    exact constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  refine ⟨h0, ?_⟩
  have hl : HasSubst (-log ℂ_[p]) := HasSubst.of_constantCoeff_zero' (by simp)
  have e := congrArg (substAlgHom (R := ℂ_[p]) hs) (exp_neg_log_one_var ℂ_[p])
  have en : subst (F - 1) (-log ℂ_[p]) = -GL3Theta.logMv F := by
    rw [logMv_eq_subst hF, ← coe_substAlgHom hs, map_neg]
  rw [map_mul, map_add (f := _), map_one, substAlgHom_X, coe_substAlgHom, subst_comp_subst_apply hl hs,
    en, add_sub_cancel] at e
  rw [expMv_eq_subst (by rw [map_neg, h0, neg_zero])]
  exact e

end GlobalTheory.ExpLogMv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumNormNeg
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NormGauss

theorem exists_norm_eq {k : Type} [Field k] [Finite k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (u : k) (hu : s u = u) : ∃ t, t * s t = u := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  let σ : k ≃ₐ[F] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs,
      map_mul' := map_mul s, map_add' := map_add s, commutes' := fun r => r.2 }
  have hσ_apply : ∀ x, σ x = s x := fun _ => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨a, ha⟩ := hne
    intro h
    apply ha
    have := AlgEquiv.ext_iff.1 h a
    rwa [hσ_apply, AlgEquiv.one_apply] at this
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    rw [pow_two, AlgEquiv.mul_apply, hσ_apply, hσ_apply, hs, AlgEquiv.one_apply]
  have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    ext x
    rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_bot]
    constructor
    · intro h
      exact ⟨⟨x, h σ (Subgroup.mem_zpowers σ)⟩, rfl⟩
    · rintro ⟨r, rfl⟩ τ _
      exact τ.commutes r
  have htop : Subgroup.zpowers σ = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
    ext τ
    simp only [Subgroup.mem_top, iff_true]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact τ.commutes r
  have hcard : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← htop, Nat.card_zpowers,
      orderOf_eq_prime hσ2 hσ1]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, σ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hσ1.symm, hcard]
  have hnorm : ∀ t : k, algebraMap F k (Algebra.norm F t) = t * s t := by
    intro t
    rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hσ1.symm]
    rfl
  obtain ⟨t, ht⟩ := FiniteField.norm_surjective F k (⟨u, hu⟩ : F)
  refine ⟨t, ?_⟩
  rw [← hnorm, ht]
  rfl

theorem sum_norm_neg {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (ψ : AddChar k ℂ) (hψ : ∃ a, ψ (a + s a) ≠ 1) :
    ∃ m : ℝ, 0 < m ∧ ∑ t : k, ψ (t * s t) = -(m : ℂ) := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  have hs0 : ∀ x : k, s x = 0 → x = 0 := by
    intro x h
    have := congrArg s h
    rwa [hs, map_zero] at this
  have hNF : ∀ t : k, t * s t ∈ F := fun t => by
    show s (t * s t) = t * s t
    rw [map_mul, hs, mul_comm]
  let N : k → F := fun t => ⟨t * s t, hNF t⟩
  have hN : ∀ t, ((N t : F) : k) = t * s t := fun _ => rfl
  let φ : AddChar F ℂ := ψ.compAddMonoidHom F.subtype.toAddMonoidHom
  have hφ_apply : ∀ u : F, φ u = ψ (u : k) := fun _ => rfl
  have hφ : φ ≠ 1 := by
    obtain ⟨a, ha⟩ := hψ
    intro h
    have hmem : a + s a ∈ F := by
      show s (a + s a) = a + s a
      rw [map_add (f := _), hs, add_comm]
    apply ha
    have := congrArg (fun χ : AddChar F ℂ => χ ⟨a + s a, hmem⟩) h
    simpa only [hφ_apply, AddChar.one_apply] using this
  have hsumφ : ∑ u : F, ψ (u : k) = 0 := by
    simpa only [hφ_apply] using AddChar.sum_eq_zero_of_ne_one hφ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = (Finset.univ.filter (fun t : k => t * s t = 1)).card := ⟨_, rfl⟩
  have hfib : ∀ u : F,
      (Finset.univ.filter (fun t : k => N t = u)).card = if u = 0 then 1 else c := by
    intro u
    split_ifs with hu
    · subst hu
      rw [Finset.card_eq_one]
      refine ⟨0, ?_⟩
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have h' : t * s t = 0 := congrArg Subtype.val h
        rcases mul_eq_zero.1 h' with h0 | h0
        · exact h0
        · exact hs0 t h0
      · rintro rfl
        apply Subtype.ext
        rw [hN, zero_mul]
        rfl
    · obtain ⟨t0, ht0⟩ := exists_norm_eq s hs hne (u : k) u.2
      have hu0 : (u : k) ≠ 0 := fun h => hu (Subtype.ext h)
      have ht0ne : t0 ≠ 0 := by
        rintro rfl
        apply hu0
        rw [← ht0, zero_mul]
      rw [hc]
      apply Finset.card_nbij' (fun t => t * t0⁻¹) (fun t => t * t0)
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        have h' : t * s t = u := congrArg Subtype.val ht
        have e : t * t0⁻¹ * s (t * t0⁻¹) = (t * s t) * (t0 * s t0)⁻¹ := by
          rw [map_mul, map_inv₀, mul_inv]
          ring
        rw [e, h', ht0, mul_inv_cancel₀ hu0]
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        apply Subtype.ext
        rw [hN]
        have e : t * t0 * s (t * t0) = (t * s t) * (t0 * s t0) := by
          rw [map_mul]
          ring
        rw [e, ht, ht0, one_mul]
      · intro t _
        exact inv_mul_cancel_right₀ ht0ne t
      · intro t _
        exact mul_inv_cancel_right₀ ht0ne t
  have hsplit : ∑ t : k, ψ (t * s t) =
      ∑ u : F, ((Finset.univ.filter (fun t : k => N t = u)).card : ℂ) * ψ (u : k) := by
    rw [← Finset.sum_fiberwise Finset.univ N (fun t => ψ (t * s t))]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => ψ (u : k)), Finset.sum_const, nsmul_eq_mul]
    intro t ht
    have := (Finset.mem_filter.1 ht).2
    rw [← this]
  have hψ0 : ψ ((0 : F) : k) = 1 := by
    rw [ZeroMemClass.coe_zero, AddChar.map_zero_eq_one]
  have key : ∀ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) =
      (c : ℂ) * ψ (u : k) + (if u = 0 then (1 - (c : ℂ)) else 0) := by
    intro u
    split_ifs with h
    · subst h
      rw [hψ0]
      push_cast
      ring
    · ring
  have hval : ∑ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) = 1 - c := by
    rw [Finset.sum_congr rfl (fun u _ => key u), Finset.sum_add_distrib, ← Finset.mul_sum, hsumφ,
      mul_zero, zero_add]
    simp
  have hc2 : 2 ≤ c := by
    obtain ⟨a, ha⟩ := hne
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (map_zero s)
    have hsa0 : s a ≠ 0 := fun h => ha0 (hs0 a h)
    have hne1 : a * (s a)⁻¹ ≠ 1 := by
      intro h
      apply ha
      rw [mul_inv_eq_one₀ hsa0] at h
      exact h.symm
    rw [hc]
    calc 2 = ({1, a * (s a)⁻¹} : Finset k).card := (Finset.card_pair hne1.symm).symm
      _ ≤ _ := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · rw [map_one, one_mul]
        · rw [map_mul, map_inv₀, hs]
          field_simp
  refine ⟨(c : ℝ) - 1, ?_, ?_⟩
  · have : (2 : ℝ) ≤ c := by exact_mod_cast hc2
    linarith
  · rw [hsplit]
    simp_rw [hfib]
    rw [hval]
    push_cast
    ring

theorem finsum_norm_neg : ∀ (R : Type) [CommRing R] (σ : R →+* R) (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)], (∀ a, σ (σ a) = a) → (∀ a ∈ P, σ a ∈ P) → (∃ a, a - σ a ∉ P) → ∀ χ : R → ℂ, (∀ a b, χ (a + b) = χ a * χ b) → (∀ a ∈ P, χ a = 1) → (∃ a, χ (a + σ a) ≠ 1) → ∃ m : ℝ, 0 < m ∧ ∑ᶠ q : R ⧸ P, χ (Quotient.out q * σ (Quotient.out q)) = -(m : ℂ) := by
  intro R _ σ P _ _ hσ hP hne χ hχ hχP hχa
  classical
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (R ⧸ P) := Fintype.ofFinite _
  have hle : P ≤ P.comap σ := fun a ha => hP a ha
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ hle
  have hs_mk : ∀ a : R, s (Ideal.Quotient.mk P a) = Ideal.Quotient.mk P (σ a) :=
    fun a => Ideal.quotientMap_mk
  have hs : ∀ x, s (s x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hs_mk, hs_mk, hσ]
  have hsne : ∃ x, s x ≠ x := by
    obtain ⟨a, ha⟩ := hne
    refine ⟨Ideal.Quotient.mk P a, ?_⟩
    rw [hs_mk]
    intro h
    apply ha
    have h' := P.neg_mem (Ideal.Quotient.eq.1 h)
    rwa [neg_sub] at h'
  have hχ_congr : ∀ x y : R, x - y ∈ P → χ x = χ y := by
    intro x y h
    have e : x = y + (x - y) := by ring
    conv_lhs => rw [e]
    rw [hχ, hχP _ h, mul_one]
  let ψ : AddChar (R ⧸ P) ℂ :=
    { toFun := fun q => χ (Quotient.out q)
      map_zero_eq_one' := by
        apply hχP
        rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]
      map_add_eq_mul' := by
        intro q₁ q₂
        rw [← hχ]
        apply hχ_congr
        rw [← Ideal.Quotient.eq, map_add (f := _), Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
          Ideal.Quotient.mk_out] }
  have hψ_mk : ∀ a, ψ (Ideal.Quotient.mk P a) = χ a := fun a =>
    hχ_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])
  have hψne : ∃ x, ψ (x + s x) ≠ 1 := by
    obtain ⟨a, ha⟩ := hχa
    exact ⟨Ideal.Quotient.mk P a, by rw [hs_mk, ← map_add (f := _), hψ_mk]; exact ha⟩
  obtain ⟨m, hm, hsum⟩ := sum_norm_neg s hs hsne ψ hψne
  refine ⟨m, hm, ?_⟩
  rw [finsum_eq_sum_of_fintype, ← hsum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  conv_rhs => rw [← Ideal.Quotient.mk_out q]
  rw [hs_mk, ← map_mul, hψ_mk]

end GlobalTheory.NormGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FstMemClosureNatCast
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TwoAdicFirst

theorem cont_coe : Continuous fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2]) := by
  fun_prop

theorem coe_mem_closure (z : ℤ_[2]) :
    algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2]) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  refine map_mem_closure (f := fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2])) cont_coe
    (PadicInt.denseRange_natCast z) ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

theorem exists_root (k : ℕ) : ∃ z : ℤ_[2], z ^ 2 - z + 2 * (k : ℤ_[2]) = 0 := by
  let F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * (k : ℤ_[2]))
  have h0 : F.eval 0 = 2 * (k : ℤ_[2]) := by simp [F]
  have h1 : F.derivative.eval 0 = -1 := by simp [F]
  have hn : ‖F.eval 0‖ < ‖F.derivative.eval 0‖ ^ 2 := by
    rw [h0, h1, norm_neg, norm_one, one_pow, norm_mul]
    have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
      have := PadicInt.norm_p (p := 2)
      norm_num at this
      rw [this]; norm_num
    have hk : ‖(k : ℤ_[2])‖ ≤ 1 := PadicInt.norm_le_one _
    nlinarith [norm_nonneg (k : ℤ_[2]), norm_nonneg (2 : ℤ_[2])]
  obtain ⟨z, hz, -⟩ := hensels_lemma hn
  refine ⟨z, ?_⟩
  simpa [F] using hz

open GlobalTheory.CompletedBasis

theorem sq_neg_mem (d : ℕ) (hd : d % 8 = 7) {s : ℂ_[2]} (hs : s ^ 2 = -(d : ℂ_[2])) :
    s ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 8 * k := ⟨(d + 1) / 8, by omega⟩
  obtain ⟨z, hz⟩ := exists_root k
  let φ : ℤ_[2] →+* ℂ_[2] := (algebraMap ℚ_[2] ℂ_[2]).comp PadicInt.Coe.ringHom
  set u : ℂ_[2] := φ (2 * z - 1) with hu
  have hz' : φ z ^ 2 - φ z + 2 * (k : ℂ_[2]) = 0 := by
    have := congrArg φ hz
    simpa only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_zero] using this
  have hk' : (d : ℂ_[2]) + 1 = 8 * (k : ℂ_[2]) := by exact_mod_cast hk
  have hu2 : u ^ 2 = -(d : ℂ_[2]) := by
    rw [hu]
    simp only [map_sub, map_mul, map_ofNat, map_one]
    linear_combination 4 * hz' + hk'
  have h : (s - u) * (s + u) = 0 := by linear_combination hs - hu2
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨_, (sub_eq_zero.1 h).symm⟩
  · refine ⟨-(PadicInt.Coe.ringHom (2 * z - 1)), ?_⟩
    rw [map_neg]
    change -u = s
    linear_combination -h

variable (D : D7) (lam : Qbar →+* ℂ_[2])

theorem rhoBase_mem_of_K (x : D.host.K) : rhoBase D lam (x : D.host.E) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange := by
  let S : Subfield D.host.E := ((algebraMap ℚ_[2] ℂ_[2]).fieldRange).comap (rhoBase D lam)
  let F : IntermediateField ℚ D.host.E := S.toIntermediateField fun q => by
    refine ⟨(q : ℚ_[2]), ?_⟩
    change _ = rhoBase D lam (algebraMap ℚ D.host.E q)
    rw [eq_ratCast, map_ratCast, map_ratCast]
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hb : D.host.sqd ∈ F := by
    change rhoBase D lam (D.host.sqd) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange
    refine sq_neg_mem D.host.d (by omega) ?_
    rw [← map_pow, D.host.sqd_sq, map_neg, map_natCast]
  have hle : D.host.K ≤ F := IntermediateField.adjoin_simple_le_iff.2 hb
  exact hle x.2

theorem rhoK_mem (a : 𝓞 D.host.K) :
    rhoK D lam (a : D.host.K) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  obtain ⟨q, hq⟩ := rhoBase_mem_of_K D lam (a : D.host.K)
  have hq' : algebraMap ℚ_[2] ℂ_[2] q = rhoK D lam (a : D.host.K) := hq
  have hn : ‖q‖ ≤ 1 := by
    have := norm_le_one_of_mem (rhoK D lam) (mem_intClosure (rhoK D lam) a)
    rwa [← hq', norm_algebraMap'] at this
  have := coe_mem_closure ⟨q, hn⟩
  rwa [show ((⟨q, hn⟩ : ℤ_[2]) : ℚ_[2]) = q from rfl, hq'] at this

theorem fst_mem_closure_natCast :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∀ α ∈ GL3Theta.OKp D lam,
      α.1 ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  intro D lam α hα
  have h1 : α.1 ∈ (intClosure (rhoK D lam) : Set ℂ_[2]) := by
    rw [← fst_image_OKp]
    exact ⟨α, hα, rfl⟩
  rw [coe_intClosure] at h1
  refine closure_minimal ?_ isClosed_closure h1
  rintro _ ⟨a, rfl⟩
  exact rhoK_mem D lam a

end GlobalTheory.TwoAdicFirst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTransl

def sqThD (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (GlobalTheory.EvenTheta.sqTh Λ v) z - 2 * deriv (sgStar Λ) z * GlobalTheory.EvenTheta.sqTh Λ v z

end GlobalTheory.ThetaTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCombPeriodicTwiceLevelStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslation_comb_periodic_twice_level : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → ∀ (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (e₀ : VC D N N' → ℂ) (x : VC D N N') (m₀ : ℕ), e₀ ∈ ThSp D T A → m₀ • x ∈ A → (∀ i, m₀ • t i ∈ A) → ∀ l ∈ A, U D T (x + (2 * m₀) • l) (comb D T c t e₀) = U D T x (comb D T c t e₀) ∧ wdPh D T (x + (2 * m₀) • l) = wdPh D T x := by
  first | exact @GlobalTheory.GalTheta.Period.period | exact GlobalTheory.GalTheta.Period.period | (intros; apply GlobalTheory.GalTheta.Period.period <;> assumption)
end

