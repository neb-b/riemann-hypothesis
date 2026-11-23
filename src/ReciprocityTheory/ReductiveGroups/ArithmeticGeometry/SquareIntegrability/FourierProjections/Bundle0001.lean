module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaUContinuous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.HfNegRight
section
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem Hf_add_left (x y z : EuclideanSpace ℂ ι) : Hf (x + y) z = Hf x z + Hf y z := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem Hf_add_right (x y z : EuclideanSpace ℂ ι) : Hf z (x + y) = Hf z x + Hf z y := by
  simp only [Hf, PiLp.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem Hf_neg_left (x z : EuclideanSpace ℂ ι) : Hf (-x) z = -Hf x z := by
  simp only [Hf, PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem Hf_conj (x y : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf x y) = Hf y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Hf_self (x : EuclideanSpace ℂ ι) : Hf x x = ((‖x‖ : ℝ) : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem conj_eq_sub (z : ℂ) : (starRingEnd ℂ) z = z - 2 * (z.im : ℂ) * I := by
  apply Complex.ext <;> simp
  ring

def Coc (Y : GT ι) (q : ℕ) : Prop :=
  ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
    Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)

theorem ka_zero {Y : GT ι} {q : ℕ} (hC : Coc Y q) : Y.ka 0 = 1 := by
  have h := hC 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  have hz : Hf (0 : EuclideanSpace ℂ ι) 0 = 0 := by simp [Hf]
  simp only [add_zero, hz, Complex.zero_im, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] at h
  have hne : Y.ka 0 ≠ 0 := by
    intro h0
    have h1 := Y.ka_abs 0 (Submodule.zero_mem _)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)

theorem paTh_add {Y : GT ι} {q : ℕ} (hC : Coc Y q) (F : EuclideanSpace ℂ ι → ℂ)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    paTh Y q F (v + γ) = Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * paTh Y q F v := by
  simp only [paTh]
  rw [← (Equiv.addLeft (⟨γ, hγ⟩ : lat Y.b)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun δ => ?_
  simp only [Equiv.coe_addLeft, Submodule.coe_add, paU]
  rw [hC γ hγ δ δ.2]
  have hF : v + γ - (γ + (δ : EuclideanSpace ℂ ι)) = v - δ := by abel
  rw [hF]
  have hexp : cexp (-(Real.pi * q * (Hf γ (δ : EuclideanSpace ℂ ι)).im) * I) *
      cexp (q * Real.pi * Hf (v + γ) (γ + (δ : EuclideanSpace ℂ ι)) -
        q * Real.pi * Hf (γ + (δ : EuclideanSpace ℂ ι)) (γ + (δ : EuclideanSpace ℂ ι)) / 2) =
      cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) *
        cexp (q * Real.pi * Hf v (δ : EuclideanSpace ℂ ι) -
          q * Real.pi * Hf (δ : EuclideanSpace ℂ ι) (δ : EuclideanSpace ℂ ι) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_add_left, Hf_add_right, Hf_add_right]
    have hc := conj_eq_sub (Hf γ (δ : EuclideanSpace ℂ ι))
    rw [Hf_conj] at hc
    rw [hc]
    ring
  linear_combination (Y.ka γ * Y.ka δ * F (v - δ)) * hexp

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaPolyTranslate
section
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem paMono_eq (α : ι →₀ ℕ) (v : EuclideanSpace ℂ ι) : paMono α v = ∏ i, v i ^ α i := by
  simp [paMono, paPF, MvPolynomial.eval_monomial, Finsupp.prod_pow]

def jRot (j : ι) (u : Circle) : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = j then rotation u else LinearIsometryEquiv.refl ℝ ℂ)

theorem jRot_apply (j : ι) (u : Circle) (z : EuclideanSpace ℂ ι) (i : ι) :
    jRot j u z i = (if i = j then (u : ℂ) else 1) * z i := by
  by_cases h : i = j <;> simp [jRot, h, rotation_apply]

theorem paMono_rot (α : ι →₀ ℕ) (j : ι) (u : Circle) (z : EuclideanSpace ℂ ι) :
    paMono α (jRot j u z) = (u : ℂ) ^ (α j) * paMono α z := by
  rw [paMono_eq, paMono_eq]
  simp only [jRot_apply, mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem gaussianInner_monomial_orthogonal (q : ℕ) {α β : ι →₀ ℕ} (h : α ≠ β) : paIP q (paMono α) (paMono β) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext hc)
  have hab : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ((α j : ℝ) - β j) * θ = Real.pi :=
    ⟨Real.pi / ((α j : ℝ) - β j), by field_simp⟩
  have hc : ((α j : ℂ) - β j) * θ = Real.pi := by exact_mod_cast hθ
  have hfac : ((Circle.exp θ : Circle) : ℂ) ^ (α j) *
      (starRingEnd ℂ) (((Circle.exp θ : Circle) : ℂ) ^ (β j)) = -1 := by
    rw [Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add, ← Complex.exp_pi_mul_I]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination I * hc
  have hw : ∀ v, paW q (jRot j (Circle.exp θ) v) = paW q v := by
    intro v
    simp only [paW, LinearIsometryEquiv.norm_map]
  have key : ∀ v, paMono α (jRot j (Circle.exp θ) v) * (starRingEnd ℂ) (paMono β (jRot j (Circle.exp θ) v)) *
      (paW q (jRot j (Circle.exp θ) v) : ℂ) = -(paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) := by
    intro v
    rw [paMono_rot, paMono_rot, hw, map_mul]
    linear_combination (paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) * hfac
  have hI : paIP q (paMono α) (paMono β) = -paIP q (paMono α) (paMono β) := by
    unfold paIP
    rw [← integral_neg]
    conv_lhs =>
      rw [← ((jRot j (Circle.exp θ)).measurePreserving).integral_comp
        (jRot j (Circle.exp θ)).toHomeomorph.measurableEmbedding]
    congr 1
    funext v
    exact key v
  linear_combination hI / 2

private lemma finsupp_apply_le_degree (α : ι →₀ ℕ) (i : ι) : α i ≤ α.degree := by
  unfold Finsupp.degree
  by_cases h : i ∈ α.support
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) h
  · have h0 : α i = 0 := by simpa [Finsupp.mem_support_iff] using h
    rw [h0]
    exact Nat.zero_le _

private lemma mem_paS' {c : ℕ} {α : ι →₀ ℕ} : α ∈ paS (ι := ι) c ↔ α.degree ≤ c := by
  simp only [paS, Finset.mem_filter, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨⟨α, fun i => ?_, ?_⟩, h⟩
    · have := finsupp_apply_le_degree α i
      omega
    · simp

private lemma finsupp_degree_eq_sum (α : ι →₀ ℕ) : α.degree = ∑ i, α i := by
  unfold Finsupp.degree
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)

private lemma paMono_mem_paPoly_of_degree_le {c : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ c) :
    paMono α ∈ paPoly (ι := ι) c := by
  unfold paPoly
  exact Submodule.subset_span ⟨α, mem_paS'.mpr h, rfl⟩

theorem paPoly_mono {c d : ℕ} (h : c ≤ d) : paPoly (ι := ι) c ≤ paPoly d := by
  unfold paPoly
  apply Submodule.span_mono
  apply Set.image_mono
  intro γ hγ
  exact mem_paS'.mpr (le_trans (mem_paS'.mp hγ) (by exact_mod_cast h))

theorem paPoly_contDiff {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ContDiff ℂ (⊤ : ℕ∞) F := by
  unfold paPoly at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, _, rfl⟩ := hx
    have he : paMono α = fun v : EuclideanSpace ℂ ι => ∏ i, v i ^ α i := funext (paMono_eq α)
    rw [he]
    exact contDiff_prod fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff).pow (α i)
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

private lemma paMono_mul (α β : ι →₀ ℕ) :
    paMono α * paMono β = paMono (ι := ι) (α + β) := by
  funext v
  simp only [Pi.mul_apply, paMono_eq, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

theorem paPoly_mul {c d : ℕ} {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (hG : G ∈ paPoly d) :
    F * G ∈ paPoly (c + d) := by
  unfold paPoly at hF hG ⊢
  have hm := Submodule.mul_mem_mul hF hG
  rw [Submodule.span_mul_span] at hm
  refine Submodule.span_le.mpr (Set.mul_subset_iff.mpr ?_) hm
  rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
  rw [paMono_mul]
  refine Submodule.subset_span ⟨α + β, mem_paS'.mpr ?_, rfl⟩
  rw [map_add (f := _)]
  exact add_le_add (mem_paS'.mp hα) (mem_paS'.mp hβ)

theorem paPoly_const (a : ℂ) : (fun _ : EuclideanSpace ℂ ι => a) ∈ paPoly 0 := by
  have h1 : paMono (0 : ι →₀ ℕ) = fun _ : EuclideanSpace ℂ ι => (1 : ℂ) := by
    funext v
    simp [paMono_eq]
  have h2 : (fun _ : EuclideanSpace ℂ ι => a) = a • paMono (0 : ι →₀ ℕ) := by
    rw [h1]
    funext v
    simp
  rw [h2]
  exact Submodule.smul_mem _ a (paMono_mem_paPoly_of_degree_le (by simp))

theorem paPoly_coord (i : ι) : (fun v : EuclideanSpace ℂ ι => v i) ∈ paPoly 1 := by
  have h1 : (fun v : EuclideanSpace ℂ ι => v i) = paMono (Finsupp.single i 1) := by
    funext v
    rw [paMono_eq, Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb, Ne.symm hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [h1]
  exact paMono_mem_paPoly_of_degree_le (le_of_eq (by rw [finsupp_degree_eq_sum]; simp [Finsupp.single_apply]))

theorem paPoly_pow {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (n : ℕ) :
    F ^ n ∈ paPoly (n * c) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul]
    exact paPoly_const 1
  | succ n ih =>
    rw [pow_succ, add_mul, one_mul]
    exact paPoly_mul ih hF

private lemma prod_mem_paPoly (s : Finset ι) (f : ι → EuclideanSpace ℂ ι → ℂ) (d : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ paPoly (ι := ι) (d i)) : (∏ i ∈ s, f i) ∈ paPoly (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact paPoly_const (ι := ι) 1
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact paPoly_mul (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem paPoly_translate {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (a : EuclideanSpace ℂ ι) : (fun v => F (v - a)) ∈ paPoly c := by
  unfold paPoly at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hdeg := mem_paS'.mp hα
    have he : (fun v => paMono α (v - a)) =
        ∏ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ^ (α i) := by
      funext v
      simp [paMono_eq, Finset.prod_apply]
    rw [he]
    have hi : ∀ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ∈ paPoly (ι := ι) 1 :=
      fun i => Submodule.sub_mem _ (paPoly_coord i) (paPoly_mono (Nat.zero_le 1) (paPoly_const (a i)))
    have hle : ∑ i, α i * 1 ≤ c := by
      rw [finsupp_degree_eq_sum] at hdeg
      simpa using hdeg
    exact paPoly_mono hle (prod_mem_paPoly Finset.univ _ (fun i => α i * 1)
      fun i _ => paPoly_pow (hi i) (α i))
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul b x _ hx => exact Submodule.smul_mem _ b hx

theorem paPoly_Hf (a : EuclideanSpace ℂ ι) : (fun v : EuclideanSpace ℂ ι => Hf v a) ∈ paPoly 1 := by
  have h1 : (fun v : EuclideanSpace ℂ ι => Hf v a) =
      ∑ i, (starRingEnd ℂ) (a i) • (fun v : EuclideanSpace ℂ ι => v i) := by
    funext v
    rw [Finset.sum_apply]
    simp only [Hf, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (paPoly_coord i)

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

