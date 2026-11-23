module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralPowerSeriesBounds.ExistsIntegralPowerSeriesOfBoundedDistribution
section
open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

theorem UpperTheory.exists_integral_powerSeries_of_bounded_distribution :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (ν : ∀ M : ℕ, (ZMod (l ^ M) → Qbar l) →ₗ[Qbar l] Qbar l),
      (∀ M, 1 ≤ M → ∀ (g : ZMod (l ^ M) → Qbar l) (g' : ZMod (l ^ (M + 1)) → Qbar l), (∀ y : ℕ, g' y = g y) → ν (M + 1) g' = ν M g) →
      (∀ M, 1 ≤ M → ∀ x : ZMod (l ^ M), ν M (Pi.single x 1) ∈ c.O) →
      ∃ L : PowerSeries (Qbar l), (∀ n, L.coeff n ∈ c.O) ∧ ∀ r, 1 ≤ r → ∀ z : Qbar l, z ^ (l ^ r) = 1 →
        Cg (2 * r) (tval L (l ^ (3 * r)) z) (ν r (fun x => z ^ x.val)) := by
  intro l _ c ν hcomp hO
  classical
  let μ : (r : ℕ) → ZMod (l ^ r) → Qbar l := fun r x =>
    if r = 0 then ∑ x' : ZMod (l ^ 1), ν 1 (Pi.single x' 1) else ν r (Pi.single x 1)
  have hsum : ∀ r, 1 ≤ r → ∀ x : ZMod (l ^ r), ν r (Pi.single x 1) =
      ∑ x' ∈ Finset.univ.filter (fun x' : ZMod (l ^ (r + 1)) =>
        ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x),
        ν (r + 1) (Pi.single x' 1) := by
    intro r hr x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    symm
    apply hcomp r hr
    intro y
    rw [Finset.sum_apply]
    simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and,
      map_natCast]
  obtain ⟨L, hLO, hL⟩ := GlobalTheory.AmiceDist.amice l c μ
    (fun r x => by
      by_cases hr : r = 0
      · simp only [μ, if_pos hr]
        exact sum_mem (fun x' _ => hO 1 le_rfl x')
      · simp only [μ, if_neg hr]
        exact hO r (Nat.one_le_iff_ne_zero.2 hr) x)
    (fun r x => by
      have hr1 : r + 1 ≠ 0 := by omega
      simp only [μ, if_neg hr1]
      by_cases hr : r = 0
      · subst hr
        simp only [if_true]
        have hf : Finset.univ.filter (fun x' : ZMod (l ^ (0 + 1)) =>
            ZMod.castHom (pow_dvd_pow l (Nat.le_succ 0)) (ZMod (l ^ 0)) x' = x) = Finset.univ :=
          Finset.filter_true_of_mem
            (fun x' _ => (show ∀ a b : ZMod 1, a = b from fun a b => Subsingleton.elim a b) _ _)
        rw [hf]
      · simp only [if_neg hr]
        exact hsum r (Nat.one_le_iff_ne_zero.2 hr) x)
  refine ⟨L, hLO, fun r hr z hz => ?_⟩
  have h1 := hL r hr z hz
  have h2 : ∑ x, μ r x * z ^ x.val = ν r (fun x => z ^ x.val) := by
    have hr0 : r ≠ 0 := by omega
    simp only [μ, if_neg hr0]
    have h3 : (fun x : ZMod (l ^ r) => z ^ x.val) = ∑ x, z ^ x.val • Pi.single x (1 : Qbar l) := by
      funext y
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h3, map_sum]
    simp [map_smul, mul_comm]
  rwa [h2] at h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralPowerSeriesBounds.GaussSumTwistCongrOfMeasure
section
open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem UpperTheory.pow_val_mul_zmod {K : Type*} [Monoid K] {m : ℕ} (z : K) (hz : z ^ m = 1) (a b : ZMod m) :
    (z ^ a.val) ^ b.val = z ^ (a * b).val := by
  rw [← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hz]

private theorem UpperTheory.norm_dirichlet_character_le_one {l : ℕ} [Fact l.Prime] {m : ℕ} [NeZero m] (ψ : DirichletCharacter (Qbar l) m)
    (b : (ZMod m)ˣ) : ‖ψ b‖ ≤ 1 := by
  have h1 : (ψ b) ^ (Fintype.card (ZMod m)ˣ) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖ψ b‖ ^ (Fintype.card (ZMod m)ˣ) = 1 := by rw [← norm_pow, h1, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2).le

theorem UpperTheory.gaussSum_twist_congr_of_measure :
    ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (N : (ZMod (l ^ r) → Qbar l) →ₗ[Qbar l] Qbar l) (L : PowerSeries (Qbar l)),
      (∀ g g' : ZMod (l ^ r) → Qbar l, (∀ x, IsUnit x → g x = g' x) → N g = N g') →
      (∀ z : Qbar l, z ^ (l ^ r) = 1 → Cg (2 * r) (tval L (l ^ (3 * r)) z) (N (fun x => z ^ x.val))) →
      ∀ (ψ' : DirichletCharacter (Qbar l) (l ^ r)) (z : Qbar l), z ^ (l ^ r) = 1 →
        Cg (2 * r) (∑ b : (ZMod (l ^ r))ˣ, ψ' b * tval L (l ^ (3 * r)) (z ^ (b : ZMod (l ^ r)).val))
          ((∑ b : (ZMod (l ^ r))ˣ, ψ' b * z ^ (b : ZMod (l ^ r)).val) * N (fun x => ψ'⁻¹ x)) := by
  intro l _ r N L hN hL ψ' z hz
  have key : (∑ b : (ZMod (l ^ r))ˣ, ψ' b * z ^ (b : ZMod (l ^ r)).val) * N (fun x => ψ'⁻¹ x) =
      ∑ b : (ZMod (l ^ r))ˣ, ψ' b * N (fun x => (z ^ (b : ZMod (l ^ r)).val) ^ x.val) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← smul_eq_mul (α := Qbar l) _ (N _), ← map_smul, ← map_sum]
    apply hN
    rintro _ ⟨x, rfl⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight x)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hx : ψ' x * ψ'⁻¹ x = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
    rw [UpperTheory.pow_val_mul_zmod z hz]
    simp only [Equiv.coe_mulRight, Units.val_mul, map_mul]
    linear_combination (ψ' b * z ^ ((b : ZMod (l ^ r)) * x).val) * hx
  rw [key]
  unfold Cg at hL ⊢
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  have h1 := hL (z ^ (b : ZMod (l ^ r)).val) (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow])
  calc _ ≤ 1 * _ := mul_le_mul (UpperTheory.norm_dirichlet_character_le_one ψ' b) h1 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralPowerSeriesBounds.NormCharacterPowDifferenceEstimate
section
open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem norm_int_eq_one (l : ℕ) [Fact l.Prime] (n : ℤ) (h : ¬ (l : ℤ) ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  have h1 : ‖(n : ℚ_[l])‖ = 1 := by
    rcases (Padic.norm_int_le_one (p := l) n).eq_or_lt with h1 | h1
    · exact h1
    · exact absurd (Padic.norm_intCast_lt_one_iff.1 h1) h
  have h2 : (n : Qbar l) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by simp
  rw [h2, norm_algebraMap', h1]

private theorem norm_pow_sub_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K] (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (e : ℕ) : ‖x ^ e - y ^ e‖ ≤ ‖x - y‖ :=
  _root_.UpperTheory.Reformulated.B.Qi18.norm_pow_sub_pow_le x y hx hy e

private theorem norm_char_le_one (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (x : ZMod l) :
    ‖φ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    rw [MulChar.map_zero]; simp
  · have h1 : x ^ (l - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
    have h2 : ‖φ x‖ ^ (l - 1) = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
    have h3 : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) h3).1 h2).le

theorem UpperTheory.norm_character_pow_difference_estimate :
    ∀ (l : ℕ) [Fact l.Prime] (r e : ℕ) (φ : DirichletCharacter (Qbar l) l) (y : ZMod (l ^ r)) (a : ℕ) (n : ℤ), 1 ≤ r → ¬ l ∣ a → ¬ (l : ℤ) ∣ n →
      y * (a : ZMod (l ^ r)) = (n : ZMod (l ^ r)) →
      ¬ l ∣ y.val ∧ ‖φ (y.val : ZMod l) * (y.val : Qbar l) ^ e - φ (n : ZMod l) * φ⁻¹ (a : ZMod l) * ((n : Qbar l) / a) ^ e‖ ≤ ‖(l : Qbar l) ^ r‖ := by
  intro l _ r e φ y a n hr ha hn hy
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hd : ((l ^ r : ℕ) : ℤ) ∣ (y.val : ℤ) * a - n := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [ZMod.natCast_zmod_val, hy]
  have hl : (l : ℤ) ∣ (y.val : ℤ) * a - n := by
    refine dvd_trans ?_ hd
    push_cast
    exact dvd_pow_self _ (by omega)
  have hyv : ¬ l ∣ y.val := by
    intro h
    apply hn
    have h1 : (l : ℤ) ∣ (y.val : ℤ) * a := (Int.natCast_dvd_natCast.2 h).mul_right _
    have h2 := dvd_sub h1 hl
    simpa using h2
  refine ⟨hyv, ?_⟩
  have hmod : ((n : ℤ) : ZMod l) = (y.val : ZMod l) * (a : ZMod l) := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub n ((y.val : ℤ) * a) l).2 hl
    rw [this]; push_cast; rfl
  have ha0 : (a : ZMod l) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hφa : φ (a : ZMod l) * φ⁻¹ (a : ZMod l) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (Ne.isUnit ha0)]
  have hφ : φ (n : ZMod l) * φ⁻¹ (a : ZMod l) = φ (y.val : ZMod l) := by
    rw [hmod, map_mul, mul_assoc, hφa, mul_one]
  have hna : ‖(a : Qbar l)‖ = 1 := by
    have := norm_int_eq_one l (a : ℤ) (by rwa [Int.natCast_dvd_natCast])
    simpa using this
  have haK : (a : Qbar l) ≠ 0 := by
    intro h; rw [h, norm_zero] at hna; exact zero_ne_one hna
  rw [hφ, ← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_char_le_one l φ _)).trans ?_
  refine (norm_pow_sub_pow_le _ _ (IsUltrametricDist.norm_natCast_le_one _ _) ?_ e).trans ?_
  · rw [norm_div, hna, div_one]
    exact IsUltrametricDist.norm_intCast_le_one _ _
  · obtain ⟨c, hc⟩ := hd
    have hc' : (y.val : Qbar l) * a - n = (l : Qbar l) ^ r * c := by
      exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) hc
    have h : (y.val : Qbar l) - (n : Qbar l) / a = (l : Qbar l) ^ r * c / a := by
      rw [← hc']; field_simp
    rw [h, norm_div, hna, div_one, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralPowerSeriesBounds.RestrictionToUnitsCongrOfMeasure
section
open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem orth {K : Type*} [Field K] {M : ℕ} (hM : 0 < M) {ξ : K} (hξ : IsPrimitiveRoot ξ M) {x y : ℕ}
    (hx : x < M) (hy : y < M) :
    ∑ k ∈ Finset.range M, ξ ^ (M - (k * x) % M) * (ξ ^ k) ^ y = if y = x then (M : K) else 0 := by
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hM.ne'
  have hterm : ∀ k, ξ ^ (M - (k * x) % M) * (ξ ^ k) ^ y = (ξ ^ y / ξ ^ x) ^ k := by
    intro k
    have h1 : ξ ^ (M - (k * x) % M) * ξ ^ (k * x) = 1 := by
      have hlt : (k * x) % M ≤ M := (Nat.mod_lt _ hM).le
      have e1 : ξ ^ (k * x) = ξ ^ ((k * x) % M) := by
        conv_lhs => rw [← Nat.mod_add_div (k * x) M]
        rw [pow_add, pow_mul, hξ.pow_eq_one, one_pow, mul_one]
      rw [e1, ← pow_add, Nat.sub_add_cancel hlt, hξ.pow_eq_one]
    rw [div_pow, eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hξ0))]
    simp only [← pow_mul]
    rw [mul_right_comm, mul_comm x k, h1, one_mul, mul_comm y k]
  simp_rw [hterm]
  split_ifs with hxy
  · subst hxy
    simp [div_self (pow_ne_zero _ hξ0)]
  · have hu1 : ξ ^ y / ξ ^ x ≠ 1 := by
      intro h
      apply hxy
      rw [div_eq_one_iff_eq (pow_ne_zero _ hξ0)] at h
      exact hξ.pow_inj hy hx h
    have huM : (ξ ^ y / ξ ^ x) ^ M = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm y, mul_comm x, pow_mul, pow_mul,
        hξ.pow_eq_one, one_pow, one_pow, div_one]
    rw [geom_sum_eq hu1, huM, sub_self, zero_div]

private theorem exact_sum {K : Type*} [Field K] {M : ℕ} (hM : 0 < M) {ξ : K} (hξ : IsPrimitiveRoot ξ M)
    (N : (ZMod M → K) →ₗ[K] K) (l : ℕ) (h : ℕ → K) :
    ∑ x ∈ (Finset.range M).filter (fun x => ¬ l ∣ x),
        h x * ∑ k ∈ Finset.range M, ξ ^ (M - (k * x) % M) * N (fun y => (ξ ^ k) ^ y.val) =
      (M : K) * N (fun y => if l ∣ y.val then 0 else h y.val) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have key : ∀ x ∈ (Finset.range M).filter (fun x => ¬ l ∣ x),
      ∑ k ∈ Finset.range M, ξ ^ (M - (k * x) % M) * N (fun y : ZMod M => (ξ ^ k) ^ y.val) =
      N (fun y : ZMod M => if y.val = x then (M : K) else 0) := by
    intro x hx
    have hxM : x < M := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    have hfun : (fun y : ZMod M => if y.val = x then (M : K) else 0) =
        ∑ k ∈ Finset.range M, ξ ^ (M - (k * x) % M) • (fun y : ZMod M => (ξ ^ k) ^ y.val) := by
      funext y
      rw [Finset.sum_apply, ← orth hM hξ hxM (ZMod.val_lt y)]
      simp [smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfun, map_sum]
    simp [map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun x hx => by rw [key x hx])]
  have hφ : (M : K) • (fun y : ZMod M => if l ∣ y.val then 0 else h y.val) =
      ∑ x ∈ (Finset.range M).filter (fun x => ¬ l ∣ x),
        h x • (fun y : ZMod M => if y.val = x then (M : K) else 0) := by
    funext y
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    have hy := ZMod.val_lt y
    by_cases hly : l ∣ y.val
    · simp [hly]
    · simp [hly, hy, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← smul_eq_mul (M : K), ← map_smul, hφ, map_sum]
  simp [map_smul, smul_eq_mul]

theorem UpperTheory.restriction_to_units_congr_of_measure :
    ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (N : (ZMod (l ^ r) → Qbar l) →ₗ[Qbar l] Qbar l) (L : PowerSeries (Qbar l)),
      (∀ z : Qbar l, z ^ (l ^ r) = 1 → Cg (2 * r) (tval L (l ^ (3 * r)) z) (N (fun x => z ^ x.val))) →
      ∀ (ξ : Qbar l), IsPrimitiveRoot ξ (l ^ r) → ∀ (h : ℕ → Qbar l), (∀ x, ‖h x‖ ≤ 1) →
        Cg (2 * r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), h x * mass L r ξ x)
          ((l : Qbar l) ^ r * N (fun y => if l ∣ y.val then 0 else h y.val)) := by
  intro l _ r N L hL ξ hξ h hh
  have hM : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have hξ1 : ‖ξ‖ = 1 := by
    have h1 : ‖ξ‖ ^ (l ^ r) = 1 := by rw [← norm_pow, hξ.pow_eq_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM.ne').1 h1
  unfold Cg
  rw [← Nat.cast_pow, ← exact_sum hM hξ N l h, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun x _ => ?_)
  rw [← mul_sub, GlobalTheory.KZ.mass, ← Finset.sum_sub_distrib, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (hh x)).trans ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun k _ => ?_)
  rw [← mul_sub, norm_mul, norm_pow, hξ1, one_pow, one_mul]
  exact hL (ξ ^ k) (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow])
end

