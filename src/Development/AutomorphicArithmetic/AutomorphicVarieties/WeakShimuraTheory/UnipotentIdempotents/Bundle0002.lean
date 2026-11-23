module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.RootChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.HalfEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem norm_algebraMap_padicInt_padicAlgCl {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  rfl

private theorem norm_le_one_of_isIntegral_padicInt' {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have hd0 : p.natDegree ≠ 0 := by
    intro h0
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
    subst h1
    simp at hp
  obtain ⟨m, hmdeg⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
  have hc : p.coeff (m + 1) = 1 := by
    rw [← hmdeg]
    exact Polynomial.Monic.coeff_natDegree hm
  rw [Polynomial.eval₂_eq_sum_range, hmdeg, Finset.sum_range_succ, hc, map_one, one_mul] at hp
  have hsum : ‖∑ i ∈ Finset.range (m + 1), (algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ m := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have h1 : ‖(algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i)‖ ≤ 1 := by
      rw [norm_algebraMap_padicInt_padicAlgCl]
      exact PadicInt.norm_le_one _
    have h2 : ‖x‖ ^ i ≤ ‖x‖ ^ m :=
      pow_le_pow_right₀ h.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    calc _ ≤ 1 * ‖x‖ ^ m := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = _ := one_mul _
  have heq : x ^ (m + 1) =
      -∑ i ∈ Finset.range (m + 1), (algebraMap ℤ_[l] (PadicAlgCl l)) (p.coeff i) * x ^ i := by
    linear_combination hp
  have hn := congrArg norm heq
  rw [norm_neg, norm_pow] at hn
  have h3 : ‖x‖ ^ (m + 1) ≤ ‖x‖ ^ m := hn ▸ hsum
  have h4 : ‖x‖ ^ m < ‖x‖ ^ (m + 1) := pow_lt_pow_right₀ h (Nat.lt_succ_self m)
  linarith

private theorem norm_coe_padicAlgCl_coefO_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  exact norm_le_one_of_isIntegral_padicInt' _ ((Algebra.IsIntegral.isIntegral x).map c.O.val)

private theorem norm_natCast_prime_padicAlgCl_eq_inv {l : ℕ} [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℤ_[l] (PadicAlgCl l)) l, norm_algebraMap_padicInt_padicAlgCl, PadicInt.norm_p]

private theorem norm_coe_lt_one_of_mem_maximalIdeal_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O)
    (hx : x ∈ IsLocalRing.maximalIdeal c.O) : ‖(x : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  have hcast : ((l : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) := by simp
  have hl : ‖((l : c.O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by rw [hcast, norm_natCast_prime_padicAlgCl_eq_inv]
  have hlt : (l : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : c.O) ≠ 0 := by
    intro h0
    have hne : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
    rw [h0, ZeroMemClass.coe_zero, norm_zero] at hl
    exact hne hl.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hL : Ideal.span {(l : c.O)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hL hϖ
  have hdvd : ϖ ∣ x := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ, Ideal.mem_span_singleton] at hx
    exact hx
  have hxn : x ^ n ∈ Ideal.span {(l : c.O)} := by
    rw [hn, Ideal.mem_span_singleton]
    exact pow_dvd_pow_of_dvd hdvd n
  rw [Ideal.mem_span_singleton] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hy' : (x : PadicAlgCl l) ^ n = ((l : c.O) : PadicAlgCl l) * (y : PadicAlgCl l) := by
    have h5 := congrArg (fun z : c.O => (z : PadicAlgCl l)) hy
    simpa using h5
  have hnorm : ‖(x : PadicAlgCl l)‖ ^ n < 1 := by
    rw [← norm_pow, hy', norm_mul, hl]
    calc (l : ℝ)⁻¹ * ‖(y : PadicAlgCl l)‖ ≤ (l : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (norm_coe_padicAlgCl_coefO_le_one c y) (by positivity)
      _ < 1 := by rw [mul_one]; exact hlt
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero] at hnorm
    exact absurd hnorm (lt_irrefl 1)
  · exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp hnorm

private theorem norm_pow_sub_one_le_of_norm_sub_one_lt_one {l : ℕ} [Fact l.Prime] (z : PadicAlgCl l) (h : ‖z - 1‖ < 1) (i : ℕ) :
    ‖z ^ i - 1‖ ≤ ‖z - 1‖ := by
  have hz1 : ‖z‖ ≤ 1 := by
    have h1 := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  rw [← geom_sum_mul, norm_mul, mul_comm]
  have h2 : ‖∑ j ∈ Finset.range i, z ^ j‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro j _
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz1
  calc ‖z - 1‖ * ‖∑ j ∈ Finset.range i, z ^ j‖ ≤ ‖z - 1‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖z - 1‖ := mul_one _

private theorem padicAlgCl_eq_one_of_pow_eq_one_of_norm_sub_one_lt_one {l : ℕ} [Fact l.Prime] (z : PadicAlgCl l) (m : ℕ)
    (hm : ‖(m : PadicAlgCl l)‖ = 1) (hz : z ^ m = 1) (h : ‖z - 1‖ < 1) : z = 1 := by
  have hS : ∑ i ∈ Finset.range m, z ^ i =
      (m : PadicAlgCl l) + ∑ i ∈ Finset.range m, (z ^ i - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hsmall : ‖∑ i ∈ Finset.range m, (z ^ i - 1)‖ < 1 :=
    lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      (fun i _ => norm_pow_sub_one_le_of_norm_sub_one_lt_one z h i)) h
  have hSn : ‖∑ i ∈ Finset.range m, z ^ i‖ = 1 := by
    rw [hS, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hm]; exact hsmall.ne'), hm]
    exact max_eq_left hsmall.le
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hz, sub_self]
  rcases mul_eq_zero.mp hprod with h0 | h0
  · rw [h0, norm_zero] at hSn
    exact absurd hSn zero_ne_one
  · exact sub_eq_zero.mp h0

private theorem norm_padicInt_unit_pow_pred_sub_one_lt_one {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ) :
    ‖(u : ℤ_[l]) ^ (l - 1) - 1‖ < 1 := by
  have hmem : (u : ℤ_[l]) ^ (l - 1) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_pow, map_one]
    have hne : PadicInt.toZMod (u : ℤ_[l]) ≠ 0 := ((u.isUnit).map PadicInt.toZMod).ne_zero
    rw [ZMod.pow_card_sub_one_eq_one hne, sub_self]
  rw [PadicInt.ker_toZMod] at hmem
  exact PadicInt.mem_nonunits.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)

private theorem norm_natCast_prime_sub_one_padicAlgCl_eq_one {l : ℕ} [Fact l.Prime] : ‖((l - 1 : ℕ) : PadicAlgCl l)‖ = 1 := by
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hlt : (l : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [Nat.cast_sub hl1, Nat.cast_one, sub_eq_neg_add,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one, norm_natCast_prime_padicAlgCl_eq_inv]; exact hlt.ne'),
    norm_neg, norm_one, norm_natCast_prime_padicAlgCl_eq_inv]
  exact max_eq_left hlt.le

private theorem sq_mul_eq_of_pow_two_mul_pred_eq_of_norm_sub_lt_one {l : ℕ} [Fact l.Prime] (b w y : PadicAlgCl l) (hb : ‖b - 1‖ < 1)
    (hw : w ^ (l - 1) = 1) (hw1 : ‖w‖ ≤ 1) (hwy : ‖w - y‖ < 1) (hy1 : ‖y‖ = 1)
    (hbn : b ^ (2 * (l - 1)) = y ^ (l - 1)) : b ^ 2 * w = y := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy1
    exact zero_ne_one hy1
  have hb1 : ‖b ^ 2 - 1‖ < 1 := lt_of_le_of_lt (norm_pow_sub_one_le_of_norm_sub_one_lt_one b hb 2) hb
  have hz : (b ^ 2 * w * y⁻¹) ^ (l - 1) = 1 := by
    rw [mul_pow, mul_pow, ← pow_mul, hbn, hw, mul_one, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hy0)]
  have hyi : ‖y⁻¹‖ = 1 := by rw [norm_inv, hy1, inv_one]
  have hz1 : ‖b ^ 2 * w * y⁻¹ - 1‖ < 1 := by
    have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
    have hsplit : b ^ 2 * w * y⁻¹ - 1 = (b ^ 2 - 1) * w * y⁻¹ + (w - y) * y⁻¹ := by
      linear_combination hyy
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul, norm_mul, hyi, mul_one]
      calc ‖b ^ 2 - 1‖ * ‖w‖ ≤ ‖b ^ 2 - 1‖ * 1 := mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hb1
    · rw [norm_mul, hyi, mul_one]
      exact hwy
  exact (mul_inv_eq_one₀ hy0).mp (padicAlgCl_eq_one_of_pow_eq_one_of_norm_sub_one_lt_one _ (l - 1) norm_natCast_prime_sub_one_padicAlgCl_eq_one hz hz1)

private theorem coe_cycBar_eq_algebraMap_cycZ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (g : G ℚ Ω) :
    ((cycBar ℚ Ω l g : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := rfl

private theorem coe_toQ_apply {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (om : G ℚ Ω →* (↥c.O)ˣ) (g : G ℚ Ω) :
    ((toQ om g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = ((om g : c.O) : PadicAlgCl l) := rfl

private theorem coe_chiO_eq_algebraMap_cycZ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (g : G ℚ Ω) :
    ((chiO ℚ Ω l c.O g : c.O) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := rfl

private theorem sub_chiO_mem_maximalIdeal_of_bar_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (om : G ℚ Ω →* (↥c.O)ˣ) (g : G ℚ Ω)
    (h : Raw.bar om g = Raw.bar (chiO ℚ Ω l c.O) g) :
    (om g : c.O) - (chiO ℚ Ω l c.O g : c.O) ∈ IsLocalRing.maximalIdeal c.O :=
  (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal c.O)).mp h

theorem UpperTheory.V.Ws.Lk.halfEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → ∃ γ : G ℚ Ω →* (PadicAlgCl l)ˣ, Continuous γ ∧ (∀ g, ‖(γ g : PadicAlgCl l) - 1‖ < 1) ∧ (∀ g, γ g ^ 2 * toQ D.om g = cycBar ℚ Ω l g) ∧ (cycZ ℚ Ω l).ker ≤ γ.ker := by
  intro Ω _ _ _ l _ c D hD
  have hl2 : l ≠ 2 := hD.l_odd
  have hlp : l.Prime := Fact.out
  obtain ⟨π, hπapp⟩ : ∃ π : G ℚ Ω →* ℤ_[l]ˣ, ∀ g, π g = (cycZ ℚ Ω l g) ^ (l - 1) :=
    ⟨(cycZ ℚ Ω l) ^ (l - 1), fun g => rfl⟩
  have hπc : Continuous π := by
    have hfun : (⇑π) = fun g => (cycZ ℚ Ω l g) ^ (l - 1) := funext hπapp
    rw [hfun]
    exact (continuous_cycZ ℚ Ω l).pow _
  have hπn : ∀ s, ‖((π s : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
    intro s
    rw [hπapp, Units.val_pow_eq_pow_val]
    exact norm_padicInt_unit_pow_pred_sub_one_lt_one _
  have hn : 0 < 2 * (l - 1) := by
    have := hlp.two_le
    omega
  obtain ⟨t, β, c₁, htc, htk, htβ, hβc, hβ1, hβn, -⟩ :=
    Tw.rootChar l hl2 (G ℚ Ω) π hπc hπn (2 * (l - 1)) hn
  refine ⟨β, hβc, fun g => (hβ1 g).2, ?_, ?_⟩
  · intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_cycBar_eq_algebraMap_cycZ, coe_toQ_apply]
    apply sq_mul_eq_of_pow_two_mul_pred_eq_of_norm_sub_lt_one (l := l) _ _ _ (hβ1 g).2
    · have h := congrArg (fun f : G ℚ Ω →* (↥c.O)ˣ => ((f g : c.O) : PadicAlgCl l)) hD.om_pow
      simpa using h
    · exact norm_coe_padicAlgCl_coefO_le_one c _
    · have h := norm_coe_lt_one_of_mem_maximalIdeal_coefO c _ (sub_chiO_mem_maximalIdeal_of_bar_eq D.om g (hD.om_bar g))
      rw [AddSubgroupClass.coe_sub, coe_chiO_eq_algebraMap_cycZ] at h
      exact h
    · rw [norm_algebraMap_padicInt_padicAlgCl]
      exact PadicInt.isUnit_iff.mp (Units.isUnit _)
    · rw [hβn g, hπapp, Units.val_pow_eq_pow_val, map_pow]
  · intro g hg
    apply htβ
    rw [htk, MonoidHom.mem_ker, hπapp, (MonoidHom.mem_ker).mp hg, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.KapConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem kapConj_alg {M : Type} [CommGroup M] (k k' y b b' o x p E : M) (e n : ℕ)
    (h0 : k * k' * (o ^ (e + 3) * x * p) = 1) (h1 : y ^ 2 * o = E) (h2 : b * b' = 1) :
    (k * y⁻¹ ^ (e + 4) * b ^ n) * (k' * y⁻¹ ^ (e + 4) * b' ^ n) * (E * o⁻¹ * x * (E ^ e * p)) * E ^ 3 = 1 := by
  subst h1
  apply Additive.ofMul.injective
  have h0' := congrArg Additive.ofMul h0
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one, add_smul, one_smul, neg_smul, smul_add, smul_neg] at h0' h2' ⊢
  have hk : Additive.ofMul k' = -(Additive.ofMul k +
      (e • Additive.ofMul o + 3 • Additive.ofMul o + Additive.ofMul x + Additive.ofMul p)) := by
    rw [eq_neg_iff_add_eq_zero, ← h0']
    abel
  have hb : Additive.ofMul b' = -Additive.ofMul b := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h2'
  rw [hk, hb]
  simp only [smul_add, smul_neg, neg_add, neg_neg, two_smul]
  abel

theorem UpperTheory.V.Ws.Lk.kapConj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), T.Deep → ∀ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, resQ T.L g' = σ * resQ T.L g * σ⁻¹ → P.κ g * P.κ g' * toQ D.th (resQ T.L g) * cycBar T.L Ω l g ^ 3 = 1 ∧ P.βL g * P.βL g' = 1 ∧ P.tL g * P.tL g' = 1 := by
  intro Ω _ _ _ l _ c D T P hDeep σ hσ g g' hgg
  have hKL := K_le T
  have hFL : T.F ≤ T.L := T.hL ▸ le_sup_left
  have hres : ∀ h : G T.L Ω, resQ T.K (resLe hKL h) = resQ T.L h := fun h => rfl
  have hresF : ∀ h : G T.L Ω, resQ T.F (resLe hFL h) = resQ T.L h := fun h => rfl
  have hss : resQ T.K (resLe hKL g') = σ * resQ T.K (resLe hKL g) * σ⁻¹ := by
    rw [hres, hres]
    exact hgg
  obtain ⟨m, hm, hψ⟩ := hDeep
  have hψg : ∃ m, l.Coprime m ∧ D.ψ (resQ T.K (resLe hKL g)) ^ m = 1 :=
    ⟨m, hm, by rw [hres, ← hresF]; exact hψ _⟩
  have h0 := P.κ₀_conj σ hσ _ _ hss hψg
  obtain ⟨hb, ht⟩ := P.conj σ hσ _ _ hss
  refine ⟨?_, hb, ht⟩
  have hγ : P.γ (resQ T.L g') = P.γ (resQ T.L g) := by
    rw [hgg, map_mul, map_mul, map_inv, mul_comm (P.γ σ), mul_inv_cancel_right]
  have hcyc : cycBar T.L Ω l g = cycBar ℚ Ω l (resQ T.L g) := by
    rfl
  have hchi : ∀ x, toQ (chiO ℚ Ω l c.O) x = cycBar ℚ Ω l x := fun x => by
    rw [← (auChi ℚ Ω c).1]
  have hth : ∀ x, toQ D.th x = toQ (chiO ℚ Ω l c.O) x * (toQ D.om x)⁻¹ * toQ D.ξ x *
      (toQ (chiO ℚ Ω l c.O) x ^ D.e * toQ D.ψ x) := by
    intro x
    simp only [toQ, W.pushCh, Raw.th, Raw.al, Raw.Psi, Chr.Psi, MonoidHom.comp_apply, MonoidHom.mul_apply,
      MonoidHom.inv_apply, map_mul, map_inv]
    rw [show (chiO ℚ Ω l c.O ^ (D.e : ℤ)) x = (chiO ℚ Ω l c.O x) ^ (D.e : ℤ) from rfl, zpow_natCast, map_pow]
  have hk0 : toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) (resQ T.L g) =
      toQ D.om (resQ T.L g) ^ (D.e + 3) * toQ D.ξ (resQ T.L g) * toQ D.ψ (resQ T.L g) := by
    simp only [toQ, W.pushCh, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, map_mul, map_pow]
  rw [hres, hk0] at h0
  have h1 := P.γ_sq (resQ T.L g)
  have key := kapConj_alg _ _ _ _ _ _ _ _ _ D.e (D.e % 2) h0 h1 hb
  rw [hth, hchi, hcyc]
  simp only [Pre.κ, Pre.βL, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.inv_apply]
  rw [hγ]
  exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.KapCont
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem cont_resLe {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω} (h : F ≤ L) :
    Continuous (resLe h) := by
  letI : Algebra F L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Af.continuous_restrictScalarsHom F L Ω

private theorem cont_of_open_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (h : IsOpen (f.ker : Set Γ)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one]
  have hk : (f.ker : Set Γ) ∈ nhds (1 : Γ) := h.mem_nhds (one_mem _)
  exact (Filter.tendsto_pure.2 (Filter.mem_of_superset hk fun x hx => MonoidHom.mem_ker.1 hx)).mono_right (pure_le_nhds _)

theorem UpperTheory.V.Ws.Lk.kapCont :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), Continuous P.κ ∧ Continuous P.βL ∧ Continuous P.tL := by
  intro Ω _ _ _ l _ c D T P
  have hβ : Continuous P.βL := P.β_cont.comp (cont_resLe _)
  have ht : Continuous P.tL := P.t_cont.comp (cont_resLe _)
  refine ⟨?_, hβ, ht⟩
  have h0 : Continuous (P.κ₀.comp (resLe (K_le T))) :=
    (cont_of_open_ker P.κ₀ P.κ₀_open).comp (cont_resLe _)
  have h1 : Continuous (P.γ.comp (resQ T.L)) :=
    P.γ_cont.comp (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.L Ω)
  show Continuous fun g => P.κ₀.comp (resLe (K_le T)) g * ((P.γ.comp (resQ T.L)) g)⁻¹ ^ (D.e + 4) * P.βL g ^ (D.e % 2)
  exact (h0.mul ((h1.inv).pow _)).mul (hβ.pow _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.KapCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem torsion_combination_smul_eq_zero {M : Type} [AddCommGroup M] (x γ β ε ω : M) (m n k q r : ℕ) (j : ℤ)
    (hx : m • x = 0) (hω : n • ω = 0) (hγ : 2 • γ + ω = ε) (hβ : k • (2 • β + (-(2 * j + 1)) • ε) = 0) :
    (2 * k * m * n) • (x + (2 * q + r + 4) • (-γ) + r • β + (-(r * j - q - 2 : ℤ)) • ε) = 0 := by
  linear_combination (norm := module) (2 * k * n : ℤ) • hx + (k * m * (2 * q + r + 4) : ℤ) • hω - (k * m * n * (2 * q + r + 4) : ℤ) • hγ + (m * n * r : ℤ) • hβ

private theorem mul_aux {M : Type} [CommGroup M] (x γ β ε ω : M) (m n k q r : ℕ) (j : ℤ)
    (hx : x ^ m = 1) (hω : ω ^ n = 1) (hγ : γ ^ 2 * ω = ε) (hβ : (β ^ 2 * ε ^ (-(2 * j + 1))) ^ k = 1) :
    (x * γ⁻¹ ^ (2 * q + r + 4) * β ^ r * ε ^ (-(r * j - q - 2 : ℤ))) ^ (2 * k * m * n) = 1 := by
  have h := torsion_combination_smul_eq_zero (M := Additive M) (Additive.ofMul x) (Additive.ofMul γ) (Additive.ofMul β)
    (Additive.ofMul ε) (Additive.ofMul ω) m n k q r j
    (by rw [← ofMul_pow, hx, ofMul_one]) (by rw [← ofMul_pow, hω, ofMul_one])
    (by rw [← ofMul_pow, ← ofMul_mul, hγ])
    (by rw [← ofMul_zpow, ← ofMul_pow, ← ofMul_mul, ← ofMul_pow, hβ, ofMul_one])
  apply_fun Additive.toMul at h
  simpa [toMul_nsmul, toMul_zsmul, toMul_add, toMul_neg, mul_pow, inv_pow] using h

theorem UpperTheory.V.Ws.Lk.kapCyc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (a b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ g ∈ Ine (F := T.L) A, (P.κ g * cycBar T.L Ω l g ^ (-a)) ^ k = 1 ∧ (P.βL g ^ 2 * cycBar T.L Ω l g ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ c D T P hG A hA
  obtain ⟨b, k, hk, hb, hcyc⟩ := P.cyc A hA
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
  have hl : l.Prime := Fact.out
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd (Nat.coprime_zero_right l |>.1 hm) hl.one_lt.ne'
    · exact h
  have hn0 : 0 < l - 1 := Nat.sub_pos_of_lt hl.one_lt
  refine ⟨((D.e % 2 : ℕ) : ℤ) * j - ((D.e / 2 : ℕ) : ℤ) - 2, 2 * j + 1, 2 * k * m * (l - 1),
    by positivity, ⟨j, rfl⟩, ?_⟩
  intro g hg
  have hω : (toQ D.om (resQ T.L g)) ^ (l - 1) = 1 := by
    rw [show toQ D.om (resQ T.L g) = Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l)
        (D.om (resQ T.L g)) from rfl,
      ← map_pow, ← MonoidHom.pow_apply, hG.om_pow, MonoidHom.one_apply, map_one]
  have hγ : P.γ (resQ T.L g) ^ 2 * toQ D.om (resQ T.L g) = cycBar T.L Ω l g := P.γ_sq _
  have hβ : (P.β (resLe (K_le T) g) ^ 2 * cycBar T.L Ω l g ^ (-(2 * j + 1))) ^ k = 1 :=
    hcyc _ hg
  have hx : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
    rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
  have hκ : P.κ g = P.κ₀ (resLe (K_le T) g) * (P.γ (resQ T.L g))⁻¹ ^ (D.e + 4) *
      P.β (resLe (K_le T) g) ^ (D.e % 2) := rfl
  constructor
  · rw [hκ, show D.e + 4 = 2 * (D.e / 2) + D.e % 2 + 4 by omega]
    exact mul_aux _ _ _ _ _ m (l - 1) k (D.e / 2) (D.e % 2) j hx hω hγ hβ
  · show (P.β (resLe (K_le T) g) ^ 2 * cycBar T.L Ω l g ^ (-(2 * j + 1))) ^ (2 * k * m * (l - 1)) = 1
    rw [show 2 * k * m * (l - 1) = k * (2 * m * (l - 1)) by ring, pow_mul, hβ, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.KapUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.kapUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := T.L) A ≤ P.tL.ker) ∧ (∀ A, Raw.Away D.S A → Ine (F := T.L) A ≤ P.κ.ker) ∧ ∃ m : ℕ, l.Coprime m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A, P.κ g ^ m = 1 := by
  intro Ω _ _ _ l _ c D T P hG
  have hK : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.L) A, resLe (K_le T) g ∈ Ine (F := T.K) A :=
    fun A g hg => hg
  have hQ : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.L) A, resQ T.L g ∈ Ine (F := ℚ) A :=
    fun A g hg => hg
  have ht : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.t (resLe (K_le T) g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.t_unr A hA (hK A g hg))
  have hb : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.β (resLe (K_le T) g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.β_t (P.t_unr A hA (hK A g hg)))
  have hc : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.γ (resQ T.L g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.γ_ker ((places ℚ Ω l A).2.2.2 hA (hQ A g hg)))
  have hκ : ∀ g, P.κ g = P.κ₀ (resLe (K_le T) g) * (P.γ (resQ T.L g))⁻¹ ^ (D.e + 4) *
      P.β (resLe (K_le T) g) ^ (D.e % 2) := fun g => rfl
  obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
  refine ⟨fun A hA g hg => MonoidHom.mem_ker.2 (ht A hA g hg), ?_, m, hm, ?_⟩
  · intro A hA g hg
    have hl : ¬ A.valuation (l : Ω) < 1 := hA l hG.l_mem
    rw [MonoidHom.mem_ker, hκ, MonoidHom.mem_ker.1 (P.κ₀_unr A hA (hK A g hg)), hc A hl g hg,
      hb A hl g hg]
    simp
  · intro A hA g hg
    have h0 : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
      rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
    rw [hκ, hc A hA g hg, hb A hA g hg]
    simp [h0]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.NoMu
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.noMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → ∀ (L : IntermediateField ℚ Ω) (g : G L Ω), Raw.bar D.om (resQ L g) ≠ 1 → ¬ ∃ ζ : L, IsPrimitiveRoot ζ l := by
  intro Ω _ _ _ l _ c D hD L g hbar hroot
  obtain ⟨ζ, hζ⟩ := hroot
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  haveI := c.fin
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hζΩ : IsPrimitiveRoot (ζ : Ω) l := hζ.map_of_injective (L.val : L →+* Ω).injective
  set σ : G ℚ Ω := resQ L g with hσ
  set χ : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hχ
  have hfix : (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (ζ : Ω) = (ζ : Ω) := g.commutes ζ
  have hspec := cyclotomicCharacter.spec (L := Ω) l (n := 1)
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (ζ : Ω) (by rw [pow_one]; exact hζΩ.pow_eq_one)
  rw [hfix] at hspec
  have hmod : PadicInt.toZModPow 1 χ = 1 := by
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl⟩
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hlt : (PadicInt.toZModPow 1 χ).val < l :=
      lt_of_lt_of_eq (ZMod.val_lt (PadicInt.toZModPow 1 χ)) (pow_one l)
    apply hζΩ.pow_inj hlt hl
    exact hspec.symm.trans (pow_one _).symm
  have hmem : χ - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, hmod, map_one, sub_self]
  have hnu : algebraMap ℤ_[l] c.O (χ - 1) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_map (algebraMap ℤ_[l] c.O) _ hu)
  apply hbar
  rw [hD.om_bar]
  change IsLocalRing.residue c.O (algebraMap ℤ_[l] c.O χ) = 1
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, map_one] at hnu
  exact sub_eq_zero.mp hnu
end

