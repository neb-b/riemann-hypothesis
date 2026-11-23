module

public import Mathlib
public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.TwistIsPrimitiveCharacter
section
open DirichletCharacter

namespace Formalism.HermitianLattices.ThinSetIntegral

private lemma qc_ne_one (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q ≠ 1 := by
  intro h
  apply quadraticChar_ne_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  refine MulChar.ext fun a => ?_
  have h1 := congrArg (fun χ : DirichletCharacter ℂ q => χ (a : ZMod q)) h
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom,
    MulChar.one_apply_coe] at h1
  rw [MulChar.one_apply_coe]
  exact_mod_cast h1

private lemma qc_prim (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q).IsPrimitive := by
  have hd := conductor_dvd_level (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q)
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).1 hd with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q h2)
  · exact h

private lemma qc_sq (q : ℕ) [Fact q.Prime] : Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  rw [← Int.cast_pow, quadraticChar_sq_one a.ne_zero, Int.cast_one]

private lemma prim_mul {N m n : ℕ} [NeZero N] (hm : m ∣ N) (hn : n ∣ N) (hco : m.Coprime n) (hN : N = m * n)
    (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (changeLevel hm χ₁ * changeLevel hn χ₂).IsPrimitive := by
  have cA : (changeLevel hm χ₁).conductor = m := by rw [conductor_changeLevel]; exact h1
  have cB : (changeLevel hn χ₂).conductor = n := by rw [conductor_changeLevel]; exact h2
  generalize changeLevel hm χ₁ = A at *
  generalize changeLevel hn χ₂ = B at *
  have d1 : m ∣ (A * B).conductor.lcm n := by
    have h := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB] at h
  have d2 : n ∣ (A * B).conductor.lcm m := by
    have h := conductor_mul_dvd_lcm_conductor (B * A) A⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A] at h
  have e1 : m ∣ (A * B).conductor :=
    hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))
  have e2 : n ∣ (A * B).conductor :=
    hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))
  rw [isPrimitive_def]
  have e3 : N ∣ (A * B).conductor := by
    have h := hco.mul_dvd_of_dvd_of_dvd e1 e2
    rwa [← hN] at h
  exact Nat.dvd_antisymm (conductor_dvd_level _) e3

private lemma chi_eight_sq : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8 ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  have hu : IsUnit (ZMod.χ₈ (a : ZMod 8)) := by
    rw [← MulChar.coe_toUnitHom]
    exact Units.isUnit _
  rcases ZMod.isQuadratic_χ₈ (a : ZMod 8) with h | h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · rw [h]
    norm_num
  · rw [h]
    norm_num

private lemma chi_eight_primitive : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hne
  have hd := conductor_dvd_level Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8
  have h4 : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ∣ 4 := by
    have hle : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    generalize Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor = k at *
    interval_cases k <;> omega
  obtain ⟨hd4, χ₀, h0⟩ : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.FactorsThrough 4 :=
    (mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4
  have h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) :=
    changeLevel_eq_cast_of_dvd' χ₀ hd4 (by
      rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  rw [← h0] at h5
  have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
  have h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
  rw [h6, map_one, Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, h7] at h5
  norm_num at h5

theorem twist_is_primitive_character : Formalism.HermitianLattices.ZeroFreeRegionGL2.TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ h2 hco
  have hq : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hco
    exact hq.one_lt.ne' hco
  have : NeZero t := ⟨ht⟩
  have hp : (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q).IsPrimitive :=
    prim_mul _ _ hco.symm rfl θ (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q) hθ (qc_prim q h2)
  refine ⟨hp, ?_, ?_⟩
  · intro h1
    rw [isPrimitive_def, h1, conductor_one] at hp
    have h3 : 2 ≤ q := hq.two_le
    have h4 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hs
    rw [Formalism.HermitianLattices.ZeroFreeRegionGL2.tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]

end Formalism.HermitianLattices.ThinSetIntegral
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity
section
open Finset ArithmeticFunction

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem finite_splitting_of_group : GFiniteSplit := by
  intro q _ χ x z hx hxz
  unfold Gchi Sz tailL cN
  have hsub : Icc 1 ⌊x⌋₊ ⊆ Icc 1 ⌊z⌋₊ := Icc_subset_Icc le_rfl (Nat.floor_le_floor hxz)
  have e1 : (∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - 1 : ℝ) : ℂ)) =
      ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) := by
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).1 hn.2
      rw [min_eq_left ((one_le_div hn0).2 hle)]
    · intro n hn hn'
      rw [mem_Icc] at hn hn'
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have : x < n := by
        by_contra hc
        exact hn' ⟨hn.1, Nat.le_floor (not_lt.1 hc)⟩
      rw [min_eq_right ((div_le_one hn0).2 this.le)]; simp
  rw [e1]
  have : ∀ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) =
      (x : ℂ) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) - ((Λ n * min 1 (x / n) : ℝ) : ℂ) * χ (n : ZMod q) := by
    intro n _; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem twist_evaluation_formula : TwEval := by
  intro t θ q _ n
  by_cases hu : IsUnit (n : ZMod (t * q))
  · unfold tw
    rw [MulChar.mul_apply]
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu']
    have h1 : (ZMod.cast ((n : ZMod (t * q))) : ZMod t) = (n : ZMod t) := by
      have : (ZMod.castHom (Dvd.intro q rfl : t ∣ t * q) (ZMod t)) (n : ZMod (t*q)) = (n : ZMod t) := map_natCast _ n
      simpa using this
    have h2 : (ZMod.cast ((n : ZMod (t * q))) : ZMod q) = (n : ZMod q) := by
      have : (ZMod.castHom (Dvd.intro_left t rfl : q ∣ t * q) (ZMod q)) (n : ZMod (t*q)) = (n : ZMod q) := map_natCast _ n
      simpa using this
    rw [h1, h2]
    congr 1
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [qc, legendreSym]
  · rw [MulChar.map_nonunit _ hu]
    have hc : ¬ n.Coprime (t * q) := fun h => hu ((ZMod.isUnit_iff_coprime n _).2 h)
    by_cases h1 : n.Coprime t
    · have h2 : ¬ n.Coprime q := fun h => hc (Nat.Coprime.mul_right h1 h)
      have : jacobiSym (n : ℤ) q = 0 := by
        have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
        rw [jacobiSym.eq_zero_iff_not_coprime]
        simpa [Int.gcd_natCast_natCast] using h2
      simp [this]
    · have : θ (n : ZMod t) = 0 := MulChar.map_nonunit _ (fun h => h1 ((ZMod.isUnit_iff_coprime n _).1 h))
      simp [this]

end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

