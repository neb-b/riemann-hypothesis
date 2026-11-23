module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GelfandCentralHolds
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirPowerCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_pow (E : Fin n → Fin n → Module.End ℂ V) (hE : IsGlRep E) (c d : Fin n) :
    ∀ (k : ℕ) (a b : Fin n), E c d * (Mm E ^ k) a b - (Mm E ^ k) a b * E c d =
      (if d = a then (Mm E ^ k) c b else 0) - (if b = c then (Mm E ^ k) a d else 0) := by
  have hM : ∀ i j, Mm E i j = E i j := fun _ _ => rfl
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [pow_zero, Matrix.one_apply]
    have h0 : (if d = a then (if c = b then (1 : Module.End ℂ V) else 0) else 0) =
        (if b = c then (if a = d then 1 else 0) else 0) := by
      by_cases h2 : d = a
      · subst h2
        by_cases h3 : b = c
        · subst h3; simp
        · simp [h3, Ne.symm h3]
      · simp [h2, Ne.symm h2]
    rw [h0, sub_self]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    have key : ∀ j, E c d * ((Mm E ^ k) a j * E j b) - ((Mm E ^ k) a j * E j b) * E c d
        = (E c d * (Mm E ^ k) a j - (Mm E ^ k) a j * E c d) * E j b
          + (Mm E ^ k) a j * (E c d * E j b - E j b * E c d) := by
      intro j; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, hM]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [key, ih, hE c d]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : d = a <;> by_cases h2 : b = c <;> simp [h1, h2] <;> abel

end CasimirPowerCommute

theorem gelfand_central_holds : A2 := by
  intro n ε V _ _ E h k c d
  have hc := CasimirPowerCommute.comm_pow E h.gl c d k
  rw [← sub_eq_zero, Matrix.trace, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Matrix.diag_apply, hc, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GroupFactsHolds
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CompactGroupFacts

variable {n : ℕ}

theorem mul_mem (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

theorem hilbert_schmidt_continuous : Continuous (hs2 : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs2
  fun_prop

theorem isClosed_UJ (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  have : UJset ε = (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * Jm ε * g) ⁻¹' {Jm ε} := rfl
  rw [this]
  exact isClosed_singleton.preimage (by fun_prop)

theorem entry_le (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs2 g := by
  unfold hs2
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem compact (ε : Fin n → Bool) (ρ : ℝ) : IsCompact {g | g ∈ UJset ε ∧ hs2 g ≤ ρ} := by
  let K : Set (Fin n → Fin n → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) (Real.sqrt ρ)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset ((isClosed_UJ ε).inter (isClosed_le hilbert_schmidt_continuous continuous_const)) ?_
  rintro g ⟨-, hg⟩ i - j -
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact Real.le_sqrt_of_sq_le ((entry_le g i j).trans hg)

theorem Xp_inP (ε : Fin n → Bool) (p : Fin n × Fin n) (hp : p ∈ nc ε) : inP ε (Xp p.1 p.2) := by
  obtain ⟨a, b⟩ := p
  have hab : ε a ≠ ε b := by simpa [nc] using hp
  have hne : a ≠ b := fun h => hab (h ▸ rfl)
  set σ : Fin n → ℂ := fun k => if ε k then 1 else -1 with hσdef
  have hσ : σ b = -σ a := by
    simp only [hσdef]; revert hab; cases ε a <;> cases ε b <;> simp
  have h2 : Xp a b * Jm ε = -(Jm ε * Xp a b) := by
    show Xp a b * Matrix.diagonal σ = -(Matrix.diagonal σ * Xp a b)
    ext i j
    simp only [Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.add_apply,
      Matrix.single_apply]
    by_cases h1 : a = i ∧ b = j <;> by_cases h3 : b = i ∧ a = j
    · exact absurd (h1.1.trans h3.1.symm) hne
    · obtain ⟨rfl, rfl⟩ := h1; simp only [if_neg h3, hσ]; ring
    · obtain ⟨rfl, rfl⟩ := h3; simp only [if_neg h1, hσ]; ring
    · simp only [if_neg h1, if_neg h3]; ring
  have hh : (Xp a b)ᴴ = Xp a b := by
    ext i j
    simp only [Xp, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.single_apply]
    by_cases hi : a = i <;> by_cases hj : b = j <;> by_cases hi' : b = i <;> by_cases hj' : a = j <;>
      subst_vars <;> simp_all [Complex.ext_iff]
  refine ⟨?_, h2⟩
  show (Xp a b)ᴴ * Jm ε + Jm ε * Xp a b = 0
  rw [hh, h2, neg_add_cancel]

end CompactGroupFacts

theorem group_facts_holds : UnitaryGroupFacts := by
  intro n ε
  refine ⟨CompactGroupFacts.compact ε, ?_, ?_, ?_, CompactGroupFacts.hilbert_schmidt_continuous, CompactGroupFacts.Xp_inP ε⟩
  · show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  · intro g hg X hX t
    refine CompactGroupFacts.mul_mem ε hg ?_
    have := rq_exp_mem ε X hX.1 t
    rwa [Complex.coe_smul] at this
  · intro X s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left s |>.smul_right t)

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GrowthOfBasic
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace GrowthPolynomialOperator

variable {n : ℕ}

lemma actM_Xp {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Xp a b) = ((1 + Complex.I) / 2) • E a b + ((1 - Complex.I) / 2) • E b a := by
  simp only [actM, Xp, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.single_apply, ite_smul, zero_smul, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma sum_nc_swap {β : Type*} [AddCommMonoid β] (ε : Fin n → Bool) (g : Fin n × Fin n → β) :
    ∑ p ∈ nc ε, g p.swap = ∑ p ∈ nc ε, g p := by
  apply Finset.sum_nbij' Prod.swap Prod.swap <;> simp [nc, ne_comm]

lemma norm_id (x y : ℂ) :
    ‖(1 + Complex.I) / 2 * x + (1 - Complex.I) / 2 * y‖ ^ 2 +
      ‖(1 + Complex.I) / 2 * y + (1 - Complex.I) / 2 * x‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  ring

lemma coef1 : ((1 + Complex.I) / 2) ^ 2 + ((1 - Complex.I) / 2) ^ 2 = 0 := by
  ring_nf; simp [Complex.I_sq]

lemma coef2 : (1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2) = 1 := by
  linear_combination (-1/2 : ℂ) * Complex.I_sq

lemma inP_Xp (ε : Fin n → Bool) (a b : Fin n) (h : ε a ≠ ε b) : inP ε (Xp a b) := by
  have hab : a ≠ b := fun e => h (e ▸ rfl)
  refine ⟨?_, ?_⟩
  · unfold inG
    ext i j
    simp [Jm, Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply, ← sub_eq_add_neg]
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a
      subst h1b
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
    · by_cases h2 : b = i ∧ a = j
      · obtain ⟨h2a, h2b⟩ := h2
        subst h2a
        subst h2b
        cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
      · simp [h1, h2]
  · ext i j
    simp [Jm, Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a
      subst h1b
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
    · by_cases h2 : b = i ∧ a = j
      · obtain ⟨h2a, h2b⟩ := h2
        subst h2a
        subst h2b
        cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
      · simp [h1, h2]

end GrowthPolynomialOperator

open GrowthPolynomialOperator in
theorem growth_of_basic : A0 → B1 := by
  intro hA n ε V _ _ E hm
  obtain ⟨_, _, _, h4⟩ := hA n ε V E hm
  refine ⟨fun p hp => inP_Xp ε p.1 p.2 (by simpa [nc] using hp), fun κ hκ v => ?_, fun f w => ?_⟩
  · have hterm : ∀ a b : Fin n, actM E (Xp a b) (actM E (Xp a b) v) =
        ((1 + Complex.I) / 2) ^ 2 • E a b (E a b v) + ((1 + Complex.I) / 2 * ((1 - Complex.I) / 2)) • E a b (E b a v) +
        ((1 - Complex.I) / 2 * ((1 + Complex.I) / 2)) • E b a (E a b v) + ((1 - Complex.I) / 2) ^ 2 • E b a (E b a v) := by
      intro a b
      rw [actM_Xp]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul]
      module
    rw [Finset.sum_congr rfl (fun p _ => hterm p.1 p.2)]
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
    have s1 := sum_nc_swap ε (fun p => E p.1 p.2 (E p.1 p.2 v))
    have s2 := sum_nc_swap ε (fun p => E p.1 p.2 (E p.2 p.1 v))
    simp only [Prod.fst_swap, Prod.snd_swap] at s1 s2
    rw [s1, s2, ← (h4 κ hκ v).2.2]
    calc _ = (((1 + Complex.I) / 2) ^ 2 + ((1 - Complex.I) / 2) ^ 2) • ∑ p ∈ nc ε, E p.1 p.2 (E p.1 p.2 v) +
          ((1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2)) •
            ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 v) := by module
      _ = _ := by rw [coef1, coef2]; simp
  · have key : ∀ p ∈ nc ε, ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2 + ‖f (actM E (Xp p.2 p.1) w)‖ ^ 2 =
        ‖f (E p.1 p.2 w)‖ ^ 2 + ‖f (E p.2 p.1 w)‖ ^ 2 := by
      intro p _
      simp only [actM_Xp, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul, smul_eq_mul]
      exact norm_id _ _
    have h1 := sum_nc_swap ε (fun p => ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2)
    have h2 := sum_nc_swap ε (fun p => ‖f (E p.1 p.2 w)‖ ^ 2)
    simp only [Prod.fst_swap, Prod.snd_swap] at h1 h2
    have h3 := Finset.sum_congr rfl key
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2] at h3
    linarith

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GrowthPolynomialOperator
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace NoncommutativeSwapSum

lemma nc_swap {n : ℕ} {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p.swap = ∑ p ∈ nc ε, f p := by
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_ <;> simp [nc, ne_comm]

lemma sumS {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (κ : ℂ)
    (hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = κ • w - casimirK ε E w) :
    ∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1 = κ • (1 : Module.End ℂ V) - casimirK ε E := by
  ext w
  rw [LinearMap.sum_apply]
  simpa using hS w

lemma key {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (κ : ℂ)
    (hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = κ • w - casimirK ε E w) :
    ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 = -∑ p ∈ nc ε, Z ε E p.1 p.2 * E p.2 p.1 := by
  have h1 := sumS ε E κ hS
  have hc : casimirK ε E * (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1)
      - (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1) * casimirK ε E = 0 := by
    rw [h1, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    abel
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib] at hc
  have h2 : ∀ p ∈ nc ε, casimirK ε E * (E p.1 p.2 * E p.2 p.1) - E p.1 p.2 * E p.2 p.1 * casimirK ε E
      = Z ε E p.1 p.2 * E p.2 p.1 + E p.1 p.2 * Z ε E p.2 p.1 := by
    intro p _
    simp only [Z]
    noncomm_ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib] at hc
  have h3 : ∑ p ∈ nc ε, E p.1 p.2 * Z ε E p.2 p.1 = ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 :=
    nc_swap ε (fun p => E p.2 p.1 * Z ε E p.1 p.2)
  rw [h3] at hc
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hc)

end NoncommutativeSwapSum

theorem a9_of_a0_a1_eigenbasis_a6 : A0 → A1 → CasimirIsRealScalar → A6 → A9 := by
  intro h0 h1 h3 h6 n ε V _ _ E hM
  obtain ⟨_, _, _, h0c⟩ := h0 n ε V E hM
  obtain ⟨_, _, hE1, _, hcomm, hL2, hZ2⟩ := h1 n ε V E hM
  obtain ⟨κ, hκ⟩ := h3 n ε V E hM
  have hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w :=
    fun w => (h0c κ hκ w).2.2
  have hWU : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1)) ∈ U E 2 :=
    Submodule.sum_mem _ fun p _ => hcomm 1 2 _ (hE1 _ _) _ (hZ2 _ _)
  obtain ⟨C1, hC1, hW1⟩ := h6 n ε V E hM 2 _ hWU
  have hZZ : ∀ p : Fin n × Fin n,
      casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E ∈ U E 3 :=
    fun p => hcomm 2 2 _ hL2 _ (hZ2 _ _)
  choose Cp hCp0 hCp using fun p => h6 n ε V E hM 3 _ (hZZ p)
  have hCs : 0 ≤ ∑ p ∈ nc ε, Cp p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  refine ⟨C1 + ∑ p ∈ nc ε, Cp p ^ 2, by positivity, fun μ v hμ hv => ⟨?_, ?_⟩⟩
  · have hT : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1))
        = (2 : ℂ) • ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 := by
      rw [Finset.sum_sub_distrib, NoncommutativeSwapSum.key ε E (κ : ℂ) hS, two_smul]
      abel
    have hWv := hW1 μ v hμ hv
    rw [Real.sq_sqrt (by linarith), hT, LinearMap.smul_apply, norm_smul] at hWv
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at hWv
    have hTsum : ∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)
        = -inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v) := by
      rw [LinearMap.sum_apply, inner_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hne : ε p.1 ≠ ε p.2 := (Finset.mem_filter.mp hp).2
      rw [hM.uni, adjSign, if_neg hne]
      simp
    have hv0 := norm_nonneg v
    have hTv0 := norm_nonneg ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)
    rw [hTsum, norm_neg]
    calc ‖inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)‖
        ≤ ‖v‖ * ‖(∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (C1 * (1 + μ) * ‖v‖) := by
          apply mul_le_mul_of_nonneg_left _ hv0
          have : 0 ≤ C1 * (1 + μ) * ‖v‖ := by
            apply mul_nonneg (mul_nonneg hC1 (by linarith)) hv0
          linarith
      _ = C1 * (1 + μ) * ‖v‖ ^ 2 := by ring
      _ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          linarith
  · have hs : Real.sqrt (1 + μ) ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
    have hp : ∀ p ∈ nc ε,
        ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
          ≤ Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
      intro p _
      have h := hCp p μ v hμ hv
      have hm := mul_self_le_mul_self (norm_nonneg _) h
      calc ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
          = ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖
            * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ := sq _
        _ ≤ (Cp p * Real.sqrt (1 + μ) ^ 3 * ‖v‖) * (Cp p * Real.sqrt (1 + μ) ^ 3 * ‖v‖) := hm
        _ = Cp p ^ 2 * (Real.sqrt (1 + μ) ^ 2) ^ 3 * ‖v‖ ^ 2 := by ring
        _ = Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by rw [hs]
    calc ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
        ≤ ∑ p ∈ nc ε, Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := Finset.sum_le_sum hp
      _ = (∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
          linarith

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.IdentityFiltrationBound
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CommutatorAdjointLower

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_eq (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    (Mm E * Md ε E - Md ε E * Mm E) a b = ∑ c, (adjSign ε c b - adjSign ε a c) • (E a c * E c b) := by
  simp only [Mm, Md, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, mul_smul_comm, smul_mul_assoc,
    sub_smul, Finset.sum_sub_distrib]

theorem Z_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ V} (hE : IsGlRep E) (a b : Fin n) :
    Z ε E a b = ∑ c, ((if ε c = ε a then E a c * E c b + E c b * E a c else 0) -
      (if ε c = ε b then E a c * E c b + E c b * E a c else 0)) := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold Z casimirK
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ite_mul_sub_mul_ite, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [ite_sub_add_sub_eq, ← ite_and, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [and_comm (b := _ = a), and_comm (b := b = _), Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [@eq_comm _ (ε a), @eq_comm _ (ε b), ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs <;> abel

end CommutatorAdjointLower

theorem commutator_adjoint_holds : A1 → CommutatorAdjointModLower := by
  intro hA n ε V _ _ E h a b
  obtain ⟨-, -, hE1, -, hcomm, -, -⟩ := hA n ε V E h
  rw [CommutatorAdjointLower.comm_eq, CommutatorAdjointLower.Z_eq ε h.gl, ← Finset.sum_add_distrib]
  have key : ∀ c, (adjSign ε c b - adjSign ε a c) • (E a c * E c b) +
      ((if ε c = ε a then E a c * E c b + E c b * E a c else 0) -
        (if ε c = ε b then E a c * E c b + E c b * E a c else 0)) =
      ((if ε c = ε a then (1 : ℂ) else 0) - (if ε c = ε b then 1 else 0)) • (E c b * E a c - E a c * E c b) := by
    intro c
    simp only [adjSign, @eq_comm _ (ε a) (ε c)]
    split_ifs <;> module
  rw [Finset.sum_congr rfl fun c _ => key c]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hcomm 1 1 _ (hE1 c b) _ (hE1 a c))

end PositivityTheory.CW

end
end

