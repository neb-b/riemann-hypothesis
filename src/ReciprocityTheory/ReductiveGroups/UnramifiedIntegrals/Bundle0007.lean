module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem mem_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) : x ∈ Aio d l ι ↔ ‖ι (x : ℂ)‖ ≤ 1 := by
  rw [Aio, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  try exact Iff.rfl

theorem mem_nonunits_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) :
    x ∈ (Aio d l ι).nonunits ↔ ‖ι (x : ℂ)‖ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := Aio d l ι)]
  constructor
  · rintro ⟨h1, h2⟩
    have hle : ‖ι (x : ℂ)‖ ≤ 1 := (mem_Aio ι x).1 h1
    refine lt_of_le_of_ne hle fun heq => ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2
    apply h2
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at heq
    have hinv : x⁻¹ ∈ Aio d l ι :=
      (mem_Aio ι x⁻¹).2 (le_of_eq (by rw [IntermediateField.coe_inv, map_inv₀, norm_inv, heq, inv_one]))
    have hm : (⟨x, h1⟩ : Aio d l ι) * ⟨x⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    exact ⟨⟨_, _, hm, (mul_comm _ _).trans hm⟩, rfl⟩
  · intro h
    refine ⟨(mem_Aio ι x).2 h.le, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have hy := (mem_Aio ι (((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d)).1 ((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι).2
    have h0 : ((u : Aio d l ι) : Om d) * (((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) = 1 :=
      congrArg Subtype.val u.mul_inv
    rw [hu] at h0
    have hmul : (x : ℂ) * ((((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) : ℂ) = 1 :=
      congrArg (fun t : Om d => (t : ℂ)) h0
    have hn : ‖ι (x : ℂ)‖ * ‖ι ((((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) : ℂ)‖ = 1 := by
      simpa using congrArg (fun t => ‖ι t‖) hmul
    nlinarith [norm_nonneg (ι (x : ℂ)), mul_le_mul_of_nonneg_left hy (norm_nonneg (ι (x : ℂ)))]

theorem mem_of_isIntegral {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h2 : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

theorem exists_Om (d : ℕ) {z : ℂ} (hz : IsIntegral ℤ z) : ∃ x : Om d, (x : ℂ) = z ∧ IsIntegral ℤ x := by
  have hzK : IsIntegral (KQ d) z := hz.tower_top
  have hmem : z ∈ Om d := hzK
  refine ⟨⟨z, hmem⟩, rfl, ?_⟩
  exact (isIntegral_algHom_iff (x := (⟨z, hmem⟩ : Om d)) (algebraMap (Om d) ℂ).toIntAlgHom
    (algebraMap (Om d) ℂ).injective).mp hz

theorem Om_isAlgebraic (d : ℕ) (x : Om d) : IsAlgebraic ℚ (x : ℂ) := by
  have hx : IsIntegral (KQ d) (x : ℂ) := x.2
  exact (isIntegral_trans (R := ℚ) _ hx).isAlgebraic

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModHnf
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_hermite_normal_form_coords {m : ℕ} (hm : 0 < m) (p q r s : ℤ) (h : p * s - q * r = m) :
    ∃ (x y z w : ℤ) (a b e : ℕ), x * w - y * z = 1 ∧ a * e = m ∧ b < e ∧
      p = x * a ∧ q = x * b + y * e ∧ r = z * a ∧ s = z * b + w * e := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set g : ℕ := Int.gcd p r with hg
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [hg, Int.gcd_eq_zero_iff] at h0
      rw [h0.1, h0.2] at h
      simp at h
      omega
    · exact h0
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg0
  obtain ⟨x, hx⟩ : (g : ℤ) ∣ p := Int.gcd_dvd_left p r
  obtain ⟨z, hz⟩ : (g : ℤ) ∣ r := Int.gcd_dvd_right p r
  set u := Int.gcdA p r
  set v := Int.gcdB p r
  have hbez : (g : ℤ) = p * u + r * v := Int.gcd_eq_gcd_ab p r
  have h1 : x * u + z * v = 1 := by
    have : (g : ℤ) * (x * u + z * v) = g * 1 := by
      rw [mul_one]; conv_rhs => rw [hbez, hx, hz]
      ring
    exact mul_left_cancel₀ hgZ.ne' this
  set E : ℤ := x * s - z * q with hE
  have hgE : (g : ℤ) * E = m := by rw [← h, hx, hz, hE]; ring
  have hE0 : 0 < E := by
    by_contra hc
    have : (g : ℤ) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgZ.le (not_lt.mp hc)
    omega
  set b0 : ℤ := u * q + v * s with hb0
  have hmod0 : 0 ≤ b0 % E := Int.emod_nonneg _ hE0.ne'
  have hmod1 : b0 % E < E := Int.emod_lt_of_pos _ hE0
  have hdiv : b0 % E + E * (b0 / E) = b0 := Int.emod_add_mul_ediv b0 E
  set k := b0 / E
  set B := b0 % E
  have hEn : ((E.toNat : ℕ) : ℤ) = E := Int.toNat_of_nonneg hE0.le
  have hBn : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hmod0
  refine ⟨x, x * k - v, z, z * k + u, g, B.toNat, E.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · have : ((g * E.toNat : ℕ) : ℤ) = m := by push_cast; rw [hEn]; exact hgE
    exact_mod_cast this
  · omega
  · rw [hx]; ring
  · rw [hEn, hBn]
    have : x * B + (x * k - v) * E = x * b0 - v * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-q) * h1
  · rw [hz]; ring
  · rw [hEn, hBn]
    have : z * B + (z * k + u) * E = z * b0 + u * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-s) * h1

theorem hnf_exists {m : ℕ} (hm : 0 < m) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = m) :
    ∃ (γ : SL(2, ℤ)) (t : ℕ × ℕ × ℕ), t ∈ Tm m ∧ M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t := by
  rw [Matrix.det_fin_two] at hM
  obtain ⟨x, y, z, w, a, b, e, hdet, hae, hbe, h00, h01, h10, h11⟩ :=
    exists_hermite_normal_form_coords hm (M 0 0) (M 0 1) (M 1 0) (M 1 1) hM
  refine ⟨⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩, (a, b, e),
    (mem_Tm hm _).2 ⟨hae, hbe⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]

theorem hnf_unique {m : ℕ} (hm : 0 < m) {t t' : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (ht' : t' ∈ Tm m)
    (γ : SL(2, ℤ)) (h : Tmat t = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') : t = t' := by
  obtain ⟨a, b, e⟩ := t
  obtain ⟨a', b', e'⟩ := t'
  obtain ⟨hae, hbe⟩ := (mem_Tm hm _).1 ht
  obtain ⟨hae', hbe'⟩ := (mem_Tm hm _).1 ht'
  obtain ⟨ha, he⟩ := Tm_pos hm ht
  obtain ⟨ha', he'⟩ := Tm_pos hm ht'
  simp only at hae hbe hae' hbe' ha he ha' he'
  have hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact γ.2
  have h00 : (a : ℤ) = γ.1 0 0 * a' := by
    have := congrFun (congrFun h 0) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (b : ℤ) = γ.1 0 0 * b' + γ.1 0 1 * e' := by
    have := congrFun (congrFun h 0) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : (0 : ℤ) = γ.1 1 0 * a' := by
    have := congrFun (congrFun h 1) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (e : ℤ) = γ.1 1 0 * b' + γ.1 1 1 * e' := by
    have := congrFun (congrFun h 1) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  generalize γ.1 0 0 = x at *
  generalize γ.1 0 1 = y at *
  generalize γ.1 1 0 = z at *
  generalize γ.1 1 1 = w at *
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have haZ' : (0 : ℤ) < a' := by exact_mod_cast ha'
  have heZ' : (0 : ℤ) < e' := by exact_mod_cast he'
  have hz : z = 0 := by
    rcases mul_eq_zero.1 h10.symm with h0 | h0
    · exact h0
    · omega
  subst hz
  have hxw : x * w = 1 := by linear_combination hdet
  have hx0 : 0 < x := by
    by_contra hc
    have : x * a' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) haZ'.le
    omega
  have hx : x = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hxw with h0 | h0
    · exact h0
    · omega
  subst hx
  have hw : w = 1 := by linear_combination hxw
  subst hw
  have e1 : a = a' := by omega
  have e2 : e = e' := by omega
  subst e1 e2
  have hy : y = 0 := by
    have hbZ : (b : ℤ) < e := by exact_mod_cast hbe
    have hbZ' : (b' : ℤ) < e := by exact_mod_cast hbe'
    by_contra hc
    rcases lt_or_gt_of_ne hc with h0 | h0
    · have : y * e ≤ -1 * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
    · have : 1 * (e : ℤ) ≤ y * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
  subst hy
  have e3 : b = b' := by omega
  subst e3
  rfl

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem disc_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ := by
  have hc : c ≠ 0 := h.1
  have hD : DD τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [g₂_eq h, g₃_eq h, hD]
  field_simp
  ring

theorem jInv_eq_jT {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) : jInv L = jT τ := by
  have hc : c ≠ 0 := h.1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDD : DD τ ≠ 0 := DD_ne_zero τ
  show 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = E₄ τ ^ 3 / DD τ
  rw [disc_eq h, g₂_eq h]
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQuadInt
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_eq (d : ℕ) : omegaK d = (1 + sqD d) / 2 := by
  unfold omegaK sqD
  rfl

theorem KQ_mem_iff (d : ℕ) (z : ℂ) : z ∈ KQ d ↔ ∃ u v : ℚ, z = u + v * sqD d := by
  constructor
  · intro hz
    have h1 : z ∈ (KQ d).toSubalgebra := hz
    clear hz
    unfold KQ at h1
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (sqD_isIntegral d).isAlgebraic] at h1
    induction h1 using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      exact ⟨u + u', v + v', by push_cast; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      refine ⟨u * u' - d * v * v', u * v' + v * u', ?_⟩
      have hs := sqD_sq d
      push_cast
      linear_combination (v * v') * hs
  · rintro ⟨u, v, rfl⟩
    have hs : sqD d ∈ KQ d := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    refine add_mem ?_ (mul_mem ?_ hs)
    · simp
    · simp

theorem ratInt_of_isIntegral {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, q = n := by
  have h1 : IsIntegral ℤ q := by
    rw [← isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective]
    simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact ⟨n, by rw [← hn]; simp⟩

theorem conj_sqD (d : ℕ) : (starRingEnd ℂ) (sqD d) = - sqD d := by
  unfold sqD
  simp

theorem quadInt {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) :
    ∃ a b : ℤ, (((x : KQ d) : ℂ)) = a + b * omegaK d := by
  have hx : IsIntegral ℤ (((x : KQ d) : ℂ)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map (IntermediateField.val (KQ d)).toRingHom.toIntAlgHom
  obtain ⟨u, v, huv⟩ := (KQ_mem_iff d _).mp (x : KQ d).2
  rw [huv] at hx
  have hc : IsIntegral ℤ ((starRingEnd ℂ) ((u : ℂ) + v * sqD d)) := hx.map (starRingEnd ℂ).toIntAlgHom
  rw [map_add (f := _), map_mul, conj_sqD, map_ratCast, map_ratCast] at hc
  have hs := sqD_sq d
  obtain ⟨A, hA⟩ := ratInt_of_isIntegral (q := 2 * u) (by
    have e : (((2 * u : ℚ)) : ℂ) = ((u : ℂ) + v * sqD d) + ((u : ℂ) + v * -sqD d) := by
      push_cast; ring
    rw [e]; exact hx.add hc)
  obtain ⟨N, hN⟩ := ratInt_of_isIntegral (q := u ^ 2 + d * v ^ 2) (by
    have e : (((u ^ 2 + d * v ^ 2 : ℚ)) : ℂ) = ((u : ℂ) + v * sqD d) * ((u : ℂ) + v * -sqD d) := by
      push_cast; linear_combination ((v : ℂ) ^ 2) * hs
    rw [e]; exact hx.mul hc)

  have hd0 : (d : ℤ) ≠ 0 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℚ) * (2 * v) = k := by
    set r : ℚ := (d : ℚ) * (2 * v) with hr
    have hr2 : r ^ 2 = ((d * (4 * N - A ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [← hN, ← hA]; ring
    have hden : r.den = 1 := by
      have := congrArg Rat.den hr2
      rw [Rat.den_pow, Rat.den_intCast] at this
      exact (Nat.pow_eq_one.mp this).resolve_right (by norm_num)
    exact ⟨r.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
  have hk2 : k ^ 2 = d * (4 * N - A ^ 2) := by
    have : ((k ^ 2 : ℤ) : ℚ) = ((d * (4 * N - A ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [← hk, ← hN, ← hA]; ring
    exact_mod_cast this
  have hdk : (d : ℤ) ∣ k := by
    have hsq : Squarefree (d : ℤ) := Int.squarefree_natCast.mpr hsf
    exact (hsq.dvd_pow_iff_dvd (n := 2) (by norm_num)).mp ⟨_, hk2⟩
  obtain ⟨B, rfl⟩ := hdk
  have hB : 2 * v = B := by
    have : (d : ℚ) * (2 * v) = (d : ℚ) * B := by rw [hk]; push_cast; ring
    exact mul_left_cancel₀ (by exact_mod_cast hd0) this

  have h4 : A ^ 2 + (d : ℤ) * B ^ 2 = 4 * N := by
    have : ((A ^ 2 + (d : ℤ) * B ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← hN, ← hA, ← hB]; ring
    exact_mod_cast this
  obtain ⟨c, hc3⟩ : ∃ c : ℤ, (d : ℤ) = 4 * c + 3 := ⟨(d / 4 : ℕ), by omega⟩
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' A <;> obtain ⟨b, hb | hb⟩ := Int.even_or_odd' B
  · refine ⟨a - b, B, ?_⟩
    rw [omegaK_eq]
    have e1 : (u : ℂ) = ((A : ℚ) : ℂ) / 2 := by rw [← hA]; push_cast; ring
    have e2 : (v : ℂ) = ((B : ℚ) : ℂ) / 2 := by rw [← hB]; push_cast; ring
    rw [huv, e1, e2, ha, hb]; push_cast; ring
  · exfalso
    rw [ha, hb, hc3] at h4
    have : 4 * N = 4 * (a ^ 2 + 4 * c * b ^ 2 + 4 * c * b + c + 3 * b ^ 2 + 3 * b) + 3 := by
      rw [← h4]; ring
    omega
  · exfalso
    rw [ha, hb, hc3] at h4
    have : 4 * N = 4 * (a ^ 2 + a + 4 * c * b ^ 2 + 3 * b ^ 2) + 1 := by
      rw [← h4]; ring
    omega
  · refine ⟨a - b, B, ?_⟩
    rw [omegaK_eq]
    have e1 : (u : ℂ) = ((A : ℚ) : ℂ) / 2 := by rw [← hA]; push_cast; ring
    have e2 : (v : ℂ) = ((B : ℚ) : ℂ) / 2 := by rw [← hB]; push_cast; ring
    rw [huv, e1, e2, ha, hb]; push_cast; ring

end ReciprocityTheory.ChartRestriction.L1
end
end

