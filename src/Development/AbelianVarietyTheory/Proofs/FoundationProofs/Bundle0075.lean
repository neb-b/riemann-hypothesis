module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSubgroupSmoothCharacterDatumMonotone
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.StripGrp

variable {k : Type} [Field k] [ValuativeRel k]

theorem triv_mono {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) :
    Triv χ y :=
  fun u hu h1 => hx u hu (h1.trans h)

theorem triv_add {χ : kˣ →* ℂˣ} {x y : k} (hx : Triv χ x) (hy : Triv χ y) : Triv χ (x + y) := by
  rcases le_total (valuation k x) (valuation k y) with h | h
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le h le_rfl)) hy
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le le_rfl h)) hx

theorem triv_neg {χ : kˣ →* ℂˣ} {x : k} (hx : Triv χ x) : Triv χ (-x) :=
  triv_mono (by rw [Valuation.map_neg]) hx

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ h1
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm (by simpa using h1) zero_le'
  have hu : u = 1 := Units.ext (sub_eq_zero.mp ((Valuation.zero_iff _).mp h0))
  simp [hu]

theorem le_inv_of_mul_le {a b : ValueGroupWithZero k} (ha : a ≠ 0) (h : a * b ≤ 1) : b ≤ a⁻¹ :=
  calc b = a⁻¹ * (a * b) := (inv_mul_cancel_left₀ ha b).symm
    _ ≤ a⁻¹ * 1 := by gcongr
    _ = a⁻¹ := mul_one _

variable {n : ℕ}

theorem ne_of_blk {r : ℕ} {i j : Fin n} (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) : i ≠ j := by
  rintro rfl; omega

theorem val_one_apply_le (i j : Fin n) : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mul_eq_zero_of_blk {r : ℕ} {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → A i j = 0)
    (hB : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → B i j = 0) : A * B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < r
  · rw [hA i l (fun h => absurd h.2 (not_le.mpr hl)), zero_mul]
  · rw [hB l j (fun h => hl h.1), mul_zero]

variable {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ}

theorem mem_strip {g : GL (Fin n) k} : g ∈ strip ψ r ϖ m ↔ ∀ i j : Fin n,
    if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := Iff.rfl

theorem sub_one_of_mem {g : GL (Fin n) k} (hg : g ∈ strip ψ r ϖ m) (i j : Fin n)
    (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : (g.val - 1) i j = 0 := by
  have := mem_strip.mp hg i j
  rw [if_neg h] at this
  simp [Matrix.sub_apply, this]

theorem one_mem : (1 : GL (Fin n) k) ∈ strip ψ r ϖ m := by
  intro i j
  split_ifs with h
  · simp only [Units.val_one, Matrix.one_apply_ne (ne_of_blk h), mul_zero, map_zero, zero_le',
      true_and]
    exact triv_zero _
  · rfl

theorem mul_mem {a b : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) (hb : b ∈ strip ψ r ϖ m) :
    a * b ∈ strip ψ r ϖ m := by
  have key : (a * b).val = 1 + (a.val - 1) + (b.val - 1) := by
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem hb)
    rw [Units.val_mul]
    calc a.val * b.val = (1 + (a.val - 1)) * (1 + (b.val - 1)) := by simp
      _ = 1 + (a.val - 1) + (b.val - 1) + (a.val - 1) * (b.val - 1) := by noncomm_ring
      _ = _ := by rw [h0, add_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  have hB := mem_strip.mp hb i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA hB
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.add_apply, Matrix.sub_apply, h1, sub_zero, zero_add]
    rw [mul_add]
    exact ⟨(Valuation.map_add _ _ _).trans (max_le hA.1 hB.1), triv_add hA.2 hB.2⟩
  · rw [if_neg h] at hA hB
    simp only [Matrix.add_apply, Matrix.sub_apply, hA, hB, sub_self, add_zero]

theorem inv_mem {a : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) : a⁻¹ ∈ strip ψ r ϖ m := by
  have key : (a⁻¹).val = 1 - (a.val - 1) := by
    apply Units.inv_eq_of_mul_eq_one_right
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem ha)
    calc a.val * (1 - (a.val - 1)) = 1 - (a.val - 1) * (a.val - 1) := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.sub_apply, h1, sub_zero, zero_sub, mul_neg, Valuation.map_neg]
    exact ⟨hA.1, triv_neg hA.2⟩
  · rw [if_neg h] at hA
    simp only [Matrix.sub_apply, hA, sub_self, sub_zero]

theorem mono {m m' : ℕ} (hϖ : valuation k ϖ < 1) (hmm : m ≤ m') :
    strip ψ r ϖ m ⊆ strip ψ r ϖ m' := by
  intro g hg i j
  have hA := mem_strip.mp hg i j
  split_ifs with h
  · rw [if_pos h] at hA
    have hle : valuation k (ϖ ^ m' * g.val i j) ≤ valuation k (ϖ ^ m * g.val i j) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      gcongr ?_ * _
      exact pow_le_pow_right_of_le_one' hϖ.le hmm
    exact ⟨hle.trans hA.1, triv_mono hle hA.2⟩
  · rwa [if_neg h] at hA

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_triv (χ : kˣ →* ℂˣ) : IsClosed {x : k | Triv χ x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : valuation k x ≠ 0 := fun h0 => hx (by
    have : x = 0 := (Valuation.zero_iff _).mp h0
    rw [this]; exact triv_zero χ)
  refine Filter.mem_of_superset ((valuation k).locally_const hx0) ?_
  intro y hy hT
  exact hx (triv_mono (le_of_eq hy.symm) hT)

theorem isClosed_strip : IsClosed (strip ψ r ϖ m) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hball : IsClosed {z : k | valuation k z ≤ 1} :=
    (IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed
  have hS : IsClosed {A : Matrix (Fin n) (Fin n) k | ∀ i j : Fin n,
      if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * A i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * A i j)
      else A i j = (1 : Matrix (Fin n) (Fin n) k) i j} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous fun A : Matrix (Fin n) (Fin n) k => A i j :=
      (continuous_apply j).comp (continuous_apply i)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [if_pos h]
      exact (hball.inter (isClosed_triv _)).preimage (continuous_const.mul hc)
    · simp only [if_neg h]
      exact isClosed_eq hc continuous_const
  exact hS.preimage Units.continuous_val

theorem isCompact_strip (hϖ0 : ϖ ≠ 0) (hϖ : valuation k ϖ < 1) : IsCompact (strip ψ r ϖ m) := by
  set a := valuation k (ϖ ^ m) with ha_def
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).mpr (pow_ne_zero _ hϖ0)
  have ha1 : a ≤ 1 := by rw [ha_def, map_pow]; exact pow_le_one' hϖ.le _
  have h1t : (1 : ValueGroupWithZero k) ≤ a⁻¹ := le_inv_of_mul_le ha0 (by rw [mul_one]; exact ha1)
  have hbd : ∀ g ∈ strip ψ r ϖ m, ∀ i j : Fin n, valuation k (g.val i j) ≤ a⁻¹ := by
    intro g hg i j
    have hA := mem_strip.mp hg i j
    split_ifs at hA with h
    · exact le_inv_of_mul_le ha0 (by rw [ha_def, ← map_mul]; exact hA.1)
    · rw [hA]; exact (val_one_apply_le i j).trans h1t
  refine (GlobalTheory.PairingOne.isCompact_bounded (m := Fin n) a⁻¹).of_isClosed_subset isClosed_strip ?_
  intro g hg
  exact ⟨hbd g hg, hbd g⁻¹ (inv_mem hg)⟩

theorem strip_datum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  intro k _ _ _ _ n ψ r ϖ _ hϖ0 hϖ _
  refine ⟨fun m => ⟨one_mem, fun a ha b hb => mul_mem ha hb, fun a ha => inv_mem ha,
    isCompact_strip hϖ0 hϖ, rfl, fun _ _ _ _ => (mul_one 1).symm,
    ⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩⟩, fun m m' hmm => mono hϖ hmm⟩

end GlobalTheory.StripGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalOfEichlerPeriodSubConjMemCoboundaries
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Par

noncomputable def lam (w : ℕ) (x y : ℂ) : ℂ[X] →ₗ[ℂ] ℂ :=
  ∑ i ∈ Finset.range (w + 1), (x ^ i * y ^ (w - i)) • lcoeff ℂ i

lemma lam_apply (w : ℕ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y p = ∑ i ∈ Finset.range (w + 1), p.coeff i * (x ^ i * y ^ (w - i)) := by
  simp [lam, LinearMap.sum_apply, mul_comm]

lemma lam_eq (w : ℕ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y p = MvPolynomial.eval ![x, y] (p.homogenize w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lam_apply, Polynomial.homogenize, map_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp

lemma lam_mul (m n : ℕ) (x y : ℂ) (p q : ℂ[X]) (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    lam (m + n) x y (p * q) = lam m x y p * lam n x y q := by
  simp only [lam_eq, homogenize_mul p q hp hq, map_mul]

lemma natDegree_lin_pow (a b : ℂ) (i : ℕ) : ((C a * X + C b) ^ i).natDegree ≤ i := by
  refine natDegree_pow_le.trans ?_
  have : (C a * X + C b).natDegree ≤ 1 := natDegree_linear_le
  simpa using Nat.mul_le_mul_left i this

lemma lam_lin_pow (a b x y : ℂ) (i : ℕ) : lam i x y ((C a * X + C b) ^ i) = (a * x + b * y) ^ i := by
  induction i with
  | zero => simp [lam_apply]
  | succ i ih =>
    rw [pow_succ, lam_mul i 1 x y _ _ (natDegree_lin_pow a b i) natDegree_linear_le, ih, pow_succ]
    congr 1
    simp [lam_apply, Finset.sum_range_succ, coeff_X, coeff_C]
    ring

lemma polySlash_sum (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, lcoeff_apply]

lemma lam_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y (slP w g p) =
      lam w ((g 0 0 : ℤ) * x + (g 0 1 : ℤ) * y) ((g 1 0 : ℤ) * x + (g 1 1 : ℤ) * y) p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_sum, map_sum, lam_apply w _ _ p]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [map_smul, smul_eq_mul]
  congr 1
  have := lam_mul i (w - i) x y _ _ (natDegree_lin_pow ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ) i)
    (natDegree_lin_pow ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ) (w - i))
  rw [Nat.add_sub_cancel' hi', lam_lin_pow, lam_lin_pow] at this
  exact this

lemma lam_one_zero (w : ℕ) (p : ℂ[X]) : lam w 1 0 p = p.coeff w := by
  rw [lam_apply, Finset.sum_eq_single w]
  · simp
  · intro b hb hbw
    have : w - b ≠ 0 := by have := Finset.mem_range.mp hb; omega
    simp [this]
  · simp

lemma lam_conj (w : ℕ) (a c : ℤ) (p : ℂ[X]) :
    lam w a c (p.map (starRingEnd ℂ)) = starRingEnd ℂ (lam w a c p) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lam_apply, map_sum]

lemma coeff_eichler (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) :
    (eichler w f τ).coeff w = ∫ t in (0 : ℝ)..1,
      (f ∘ ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) * ((τ : ℂ) - Complex.I) := by
  rw [eichler, finsetSum_coeff, Finset.sum_eq_single w]
  · rw [coeff_C_mul_X_pow]
    simp
  · intro b _ hbw
    rw [coeff_C_mul_X_pow, if_neg hbw.symm]
  · simp

lemma coeff_eichler_period (w n : ℕ) (hn : 0 < n) (g : ℍ → ℂ) (hper : Function.Periodic (g ∘ ofComplex) (n : ℝ))
    (hhol : MDiff g) (hbdd : IsBoundedAtImInfty g) :
    (eichler w g (((n : ℤ) : ℝ) +ᵥ UpperHalfPlane.I)).coeff w = n * valueAtInfty g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 := qExpansion_coeff_zero hn' (analyticAt_cuspFunction_zero hn' hper hhol hbdd) hper
  rw [qExpansion_coeff_eq_intervalIntegral hn' hper hhol hbdd 0 one_pos] at h0
  rw [coeff_eichler, ← h0]
  have hτ : (((((n : ℤ) : ℝ) +ᵥ UpperHalfPlane.I : ℍ) : ℂ) - Complex.I) = (n : ℝ) := by
    simp
  rw [hτ, intervalIntegral.integral_mul_const]
  have h1 := intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1)
    (fun u : ℝ => (g ∘ ofComplex) (Complex.I + u)) (n : ℝ)
  simp only [zero_mul, one_mul, Complex.real_smul, Complex.ofReal_mul] at h1
  rw [mul_comm, h1]
  have hn'' : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_assoc, show (n : ℂ) * (1 / ((n : ℝ) : ℂ)) = 1 from by
    rw [Complex.ofReal_natCast] at hn'' ⊢; field_simp, one_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have hu : 0 < (Complex.I + (u : ℂ)).im := by simp
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hu, pow_zero, div_one, one_mul]
  congr 1
  ext
  simp [add_comm]

lemma periodic_slash {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k) (σ γ : SL(2, ℤ)) (n : ℤ)
    (hγ : γ ∈ Γ) (h : γ * σ = σ * ModularGroup.T ^ n) :
    Function.Periodic (((f : ℍ → ℂ) ∣[k] σ) ∘ ofComplex) ((n : ℝ) : ℂ) := by
  have h1 : (f : ℍ → ℂ) ∣[k] γ = f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)
  have h2 : ((f : ℍ → ℂ) ∣[k] σ) ∣[k] (ModularGroup.T ^ n) = (f : ℍ → ℂ) ∣[k] σ := by
    rw [← SlashAction.slash_mul, ← h, SlashAction.slash_mul, h1]
  have h3 : ∀ z : ℍ, ((f : ℍ → ℂ) ∣[k] σ) ((n : ℝ) +ᵥ z) = ((f : ℍ → ℂ) ∣[k] σ) z := by
    intro z
    have := (ModularForm.slash_action_eq'_iff k _ (ModularGroup.T ^ n) z).mp (congrFun h2 z)
    rw [modular_T_zpow_smul, ModularGroup.coe_T_zpow] at this
    simpa using this
  intro w
  by_cases! hw : 0 < w.im
  · have : 0 < (w + (n : ℝ)).im := by simp [hw]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    rw [← h3 ⟨w, hw⟩]
    refine congrArg _ (UpperHalfPlane.ext ?_)
    simp [add_comm]
  · have : (w + (n : ℝ)).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

lemma lambda_slParabolic (w : ℕ) (σ γ : SL(2, ℤ)) (n : ℤ) (h : γ * σ = σ * ModularGroup.T ^ n) (p : ℂ[X]) :
    lam w (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (slP w (mat γ) p) = lam w (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) p := by
  have h' : mat γ * mat σ = mat σ * !![1, n; 0, 1] := by
    rw [← ModularGroup.coe_T_zpow]
    exact congrArg Subtype.val h
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero] at h0 h1
  rw [lam_slP]
  congr 2
  · exact_mod_cast h0
  · exact_mod_cast h1

lemma lam_per {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (f : ModularForm Γ (k : ℤ))
    (σ : SL(2, ℤ)) (γ : Γ) (n : ℕ) (hn : 0 < n) (h : γ * σ = σ * ModularGroup.T ^ (n : ℤ)) :
    lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (per Γ (k - 2) f γ) =
      n * valueAtInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk f f.holo' σ
  have key : ∀ τ : ℍ, lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (eichler (k - 2) f (σ • τ)) =
      (eichler (k - 2) ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ).coeff (k - 2) + c.coeff (k - 2) := by
    intro τ
    rw [← coeff_add, ← hc τ, ← lam_one_zero, lam_slP]
    simp
  rw [(_root_.GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub Γ k hk f).2 γ (σ • UpperHalfPlane.I), map_sub, lambda_slParabolic _ σ γ n h, ← mul_smul, h,
    mul_smul, key, key, modular_T_zpow_smul, coeff_eichler_period _ n hn, coeff_eichler]
  · simp
  · simpa using periodic_slash f σ γ n γ.2 h
  · rw [ModularForm.SL_slash]
    exact MDifferentiable.slash f.holo' _ _
  · exact ModularFormClass.bdd_at_infty_slash f σ

end GlobalTheory.HeckeFamilyMatrices.Par


open GlobalTheory.HeckeFamilyMatrices.Par in
theorem GlobalTheory.HeckeFamilyMatrices.cuspidal_of_per_sub_cj_mem : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)), per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) → ∃ f' : CuspForm Γ (k : ℤ), ⇑f' = ⇑f := by
  intro N Γ k _ _ hΓ hk f h hB
  have hk2 : 2 ≤ k := by omega
  obtain ⟨p, hp⟩ := hB
  have hall : ∀ σ : SL(2, ℤ), IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
    intro σ
    obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero
      (σ * ModularGroup.T * σ⁻¹)
    have hγ : ((⟨_, hmem⟩ : Γ) : SL(2, ℤ)) * σ = σ * ModularGroup.T ^ (n : ℤ) := by
      simp [conj_pow]
    set γ : Γ := ⟨_, hmem⟩
    have hf := lam_per hk2 f σ γ n hn hγ
    have hh := lam_per hk2 (ModularFormClass.modularForm h) σ γ n hn hγ
    have hcoe : ((ModularFormClass.modularForm h : ModularForm Γ (k : ℤ)) : ℍ → ℂ) = h := rfl
    rw [hcoe, (CuspFormClass.zero_at_infty_slash h σ).valueAtInfty_eq_zero, mul_zero] at hh
    have h1 := congrArg (lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ)) (congrFun hp γ)
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      Pi.sub_apply, cj] at h1
    rw [lambda_slParabolic _ σ γ n hγ, sub_self, lam_conj, hh, hf, map_zero, sub_zero] at h1
    have hv : valueAtInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) = 0 :=
      (mul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast hn.ne')
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hper : Function.Periodic (((f : ℍ → ℂ) ∣[(k : ℤ)] σ) ∘ ofComplex) ((n : ℝ) : ℂ) := by
      simpa using periodic_slash f σ γ n γ.2 hγ
    have hhol : MDiff ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
      rw [ModularForm.SL_slash]
      exact MDifferentiable.slash f.holo' _ _
    have han := analyticAt_cuspFunction_zero hn' hper hhol (ModularFormClass.bdd_at_infty_slash f σ)
    have h2 : (cuspFunction n ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) ∘ fun τ : ℍ => Function.Periodic.qParam n τ : ℍ → ℂ) =
        (f : ℍ → ℂ) ∣[(k : ℤ)] σ := by
      funext τ
      exact eq_cuspFunction τ hn'.ne' hper
    have h3 := han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hn')
    rw [cuspFunction_apply_zero hn' han hper, hv, h2] at h3
    exact h3
  refine ⟨⟨f.toSlashInvariantForm, f.holo', ?_⟩, rfl⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact hall γ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
section
noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Lev (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f

def IntC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V

def SmallC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V.nonunits

def Prim (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop :=
  IntC X V f ∧ ∃ r : ℚ, V.valuation ((X.exp f).coeff r) = 1

def Dom (X : Tower Ω ε) (V : ValuationSubring Ω) (W : ValuationSubring X.K) : Prop :=
  (∀ f, IntC X V f → f ∈ W) ∧ (∀ f, SmallC X V f → W.valuation f < 1) ∧ ∀ f, Prim X V f → W.valuation f = 1

def Gauss {F L : Type} [Field F] [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L) : Prop :=
  (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ ∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) →
    (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1

def FrobV (V : ValuationSubring Ω) (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1

def Nq (X : Tower Ω ε) (M q : ℕ) (f : X.K) : X.K :=
  ∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f

def DiagMod (M q : ℕ) (γ : SL(2, ℤ)) : Prop :=
  (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = q

def levF (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω (AlgebraicClosure X.K) :=
  IntermediateField.adjoin Ω (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f})

def rootF (X : Tower Ω ε) (M₀ M m : ℕ) (U : X.K) : IntermediateField (levF X M₀) (AlgebraicClosure X.K) :=
  IntermediateField.adjoin (levF X M₀) (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f} ∪
    {y | ∃ γ ∈ CongruenceSubgroup.Gamma M₀, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) U)})

theorem lev_jK (X : Tower Ω ε) (M : ℕ) : Lev X M X.jK := fun γ _ => X.j_inv γ

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem exists_valuation_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) ∧
      (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
  intro p _ Ω _ _ h
  obtain ⟨_, hdvr, hirr⟩ := _root_.GlobalTheory.K5.completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    hirr.maximalIdeal_eq
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]; exact _root_.GlobalTheory.K5.o0_isAdicComplete_span_p p
  haveI := h.alg
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ω h.inj
  have hinv := GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral (O0 p) Ω h.inj v hv
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨v, hv, hinv, ?_, ?_⟩
  · exact (Valuation.pos_iff v).2 hp0
  · have hle : v (p : Ω) ≤ 1 := (hv _).2 (by
      have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
      simpa [IsInt] using this)
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : v (p : Ω)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have hint : IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 hi
    exact GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
      ⟨(p : Ω)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩

end GlobalTheory.K5
end

