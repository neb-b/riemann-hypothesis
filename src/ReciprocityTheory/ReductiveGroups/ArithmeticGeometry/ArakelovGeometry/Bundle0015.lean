module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem bNormSq_nonneg' (μ : Measure (Ix κ → ℂ)) (m : ConeMetric (C := ℂ) (ι := Ix κ)) {r n : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) : 0 ≤ bNormSq μ s (wgt m n) c := by
  unfold bNormSq
  refine MeasureTheory.integral_nonneg fun z => mul_nonneg (sq_nonneg _) ?_
  unfold wgt
  refine inv_nonneg.mpr ?_
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem norm_le_of_sq_wgt_le {m : ConeMetric (C := ℂ) (ι := Ix κ)} {n : ℕ} {z : Ix κ → ℂ} (hz : z ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 * wgt m n z ≤ b) :
    a ≤ Real.sqrt b * m.ρ z ^ n := by
  have hρ : 0 < m.ρ z := m.pos z hz
  have hP : 0 < m.ρ z ^ n := pow_pos hρ n
  have hw : wgt m n z = ((m.ρ z ^ n) ^ 2)⁻¹ := by
    unfold wgt
    rw [← pow_mul, mul_comm n 2]
  rw [hw] at h
  have hP2 : 0 < (m.ρ z ^ n) ^ 2 := pow_pos hP 2
  have h2 : a ^ 2 ≤ b * (m.ρ z ^ n) ^ 2 := by
    rwa [← div_eq_mul_inv, div_le_iff₀ hP2] at h
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b * (m.ρ z ^ n) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt b * m.ρ z ^ n := by rw [Real.sqrt_mul hb, Real.sqrt_sq hP.le]

theorem log_sqrt_bound (D : ℕ) {T : ℝ} (hT : 1 ≤ T) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ∧
      Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ≤
        (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0' : 0 < T := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hpos : 0 < T * (n : ℝ) ^ D := mul_pos hT0' (pow_pos hnpos D)
  have hlog : Real.log (Real.sqrt (T * (n : ℝ) ^ D)) = (1 / 2) * (Real.log T + D * Real.log n) := by
    rw [Real.log_sqrt hpos.le, Real.log_mul hT0'.ne' (pow_pos hnpos D).ne', Real.log_pow]
    ring
  have hT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2n : Real.log 2 ≤ Real.log (n + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hln : Real.log n ≤ Real.log (n + 1) := Real.log_le_log hnpos (by linarith)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  refine ⟨?_, ?_⟩
  · rw [hlog]
    exact mul_nonneg (by norm_num) (add_nonneg hT0 (mul_nonneg hD0 hn0))
  · rw [hlog]
    have h1 : Real.log T ≤ Real.log T / Real.log 2 * Real.log (n + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hl2n hT0
    have h2 : (D : ℝ) * Real.log n ≤ D * Real.log (n + 1) := mul_le_mul_of_nonneg_left hln hD0
    have h3 : (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) =
        (1 / 2) * (Real.log T / Real.log 2 * Real.log (n + 1) + D * Real.log (n + 1)) := by ring
    rw [h3]
    linarith

theorem choose_bound (k D : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (((n + k + D).choose D : ℕ) : ℝ) ≤ ((1 + k + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
  have hN : n + k + D ≤ (1 + k + D) * n := by nlinarith
  have h1 : (n + k + D).choose D ≤ (n + k + D) ^ D := Nat.choose_le_pow _ _
  have h2 : (n + k + D) ^ D ≤ ((1 + k + D) * n) ^ D := Nat.pow_le_pow_left hN D
  have h3 : (n + k + D).choose D ≤ (1 + k + D) ^ D * n ^ D := by
    rw [← mul_pow]
    exact h1.trans h2
  exact_mod_cast h3

theorem le_of_injective_mulVec {R r : ℕ} (M : Matrix (Fin R) (Fin r) ℚ)
    (hM : Function.Injective M.mulVec) : r ≤ R := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := Matrix.mulVecLin M) hM
  simpa using h

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NatCardEqPowLength
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def dmap (W : Ideal (MRing ι)) (i : ∀ k, ι k) (a : K → ℕ) : mPiece W a → MRing ι ⧸ dehomI W i :=
  fun x => Ideal.Quotient.factor (le_sup_left : W ≤ dehomI W i) x.1

theorem dmap_injective {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) (a : K → ℕ) :
    Function.Injective (dmap W i a) := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hxy
  have hd : Ideal.Quotient.mk (dehomI W i) s = Ideal.Quotient.mk (dehomI W i) t := hxy
  have hsub : s - t ∈ dehomI W i := Ideal.Quotient.eq.1 hd
  have hW := mem_of_mem_dehomI hWp hWm hi (homog_of_mem (Submodule.sub_mem _ hs ht)) hsub
  apply Subtype.ext
  exact Ideal.Quotient.eq.2 hW

theorem dmap_mono (W : Ideal (MRing ι)) (i : ∀ k, ι k) {a a' : K → ℕ} (h : ∀ k, a k ≤ a' k)
    (x : mPiece W a) : ∃ x' : mPiece W a', dmap W i a' x' = dmap W i a x := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  obtain ⟨_, s, hs, rfl⟩ := x
  have hprod : s * xpow i (fun k => a' k - a k) ∈ mHom ι a' := by
    apply Submodule.subset_span
    have := isMultiHomog_mul (homog_of_mem hs) (isMultiHomog_xpow i (fun k => a' k - a k))
    have hsum : a + (fun k => a' k - a k) = a' := by
      funext k
      simp only [Pi.add_apply]
      have := h k
      omega
    rw [hsum] at this
    exact this
  refine ⟨⟨_, Submodule.mem_map_of_mem hprod⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i) (s * xpow i (fun k => a' k - a k)) = Ideal.Quotient.mk (dehomI W i) s
  rw [map_mul, mk_xpow, mul_one]

theorem isMultiHomog_monomial (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    IsMultiHomog (monomial m c : MRing ι) (fun k => ∑ i, m ⟨k, i⟩) := by
  classical
  intro m' hm' k
  rw [MvPolynomial.support_monomial] at hm'
  split_ifs at hm' with hc
  · simp at hm'
  · rw [Finset.mem_singleton] at hm'
    rw [hm']

theorem dmap_cover (W : Ideal (MRing ι)) (i : ∀ k, ι k) (y : MRing ι ⧸ dehomI W i) :
    ∃ (a : K → ℕ) (x : mPiece W a), dmap W i a x = y := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  let deg : ((Σ k, ι k) →₀ ℕ) → K → ℕ := fun m k => ∑ j, m ⟨k, j⟩
  let a : K → ℕ := fun k => f.support.sup (fun m => deg m k)
  have hle : ∀ m ∈ f.support, ∀ k, deg m k ≤ a k := fun m hm k =>
    Finset.le_sup (f := fun m => deg m k) hm
  have hterm : ∀ m ∈ f.support,
      monomial m (f.coeff m) * xpow i (fun k => a k - deg m k) ∈ mHom ι a := by
    intro m hm
    apply Submodule.subset_span
    have := isMultiHomog_mul (isMultiHomog_monomial m (f.coeff m))
      (isMultiHomog_xpow i (fun k => a k - deg m k))
    have hsum : (fun k => ∑ j, m ⟨k, j⟩) + (fun k => a k - deg m k) = a := by
      funext k
      simp only [Pi.add_apply]
      have := hle m hm k
      simp only [deg] at this ⊢
      omega
    rw [hsum] at this
    exact this
  have hF : (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) ∈ mHom ι a :=
    Submodule.sum_mem _ hterm
  refine ⟨a, ⟨_, Submodule.mem_map_of_mem hF⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i)
      (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) =
    Ideal.Quotient.mk (dehomI W i) f
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, mk_xpow, mul_one]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]

theorem card_dehom {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) {a₁ c0 : ℕ}
    (hconst : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) → Nat.card (mPiece W a) = c0)
    (hfin : ∀ a : K → ℕ, Finite (mPiece W a)) {a : K → ℕ} (ha : ∀ k, a₁ ≤ a k) :
    Nat.card (MRing ι ⧸ dehomI W i) = c0 := by
  classical
  have hinj := fun b => dmap_injective hWp hWm hi b
  have hsurj : Function.Surjective (dmap W i a) := by
    intro y
    obtain ⟨b, x, hx⟩ := dmap_cover W i y
    let a' : K → ℕ := fun k => max (a k) (b k)
    have ha' : ∀ k, a₁ ≤ a' k := fun k => le_trans (ha k) (le_max_left _ _)
    obtain ⟨x', hx'⟩ := dmap_mono W i (fun k => le_max_right (a k) (b k)) x
    haveI := hfin a
    haveI := hfin a'
    have hsub : Set.range (dmap W i a) ⊆ Set.range (dmap W i a') := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨z', hz'⟩ := dmap_mono W i (fun k => le_max_left (a k) (b k)) z
      exact ⟨z', hz'⟩
    have hcard : (Set.range (dmap W i a')).ncard ≤ (Set.range (dmap W i a)).ncard := by
      show Nat.card (Set.range (dmap W i a')) ≤ Nat.card (Set.range (dmap W i a))
      first
        | rw [Set.Nat.card_range_of_injective (hinj a), Set.Nat.card_range_of_injective (hinj a'),
            hconst a ha, hconst a' ha']
        | rw [Nat.card_range_of_injective (hinj a), Nat.card_range_of_injective (hinj a'),
            hconst a ha, hconst a' ha']
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.finite_range _)
    have hy : y ∈ Set.range (dmap W i a') := ⟨x', hx'.trans hx⟩
    rw [← heq] at hy
    exact hy
  rw [← hconst a ha]
  exact (Nat.card_eq_of_bijective _ ⟨hinj a, hsurj⟩).symm

theorem natCard_eq_pow_length {A : Type*} [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime)
    (h : ∀ x : A, p • x = 0) : Nat.card A = p ^ (Module.length ℤ A).toNat := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Module (ZMod p) A := AddCommGroup.zmodModule h
  have hlen : Module.length ℤ A = Module.length (ZMod p) A :=
    Module.length_eq_of_surjective (fun x => ⟨(x.val : ℤ), by simp⟩)
  have hfin : Module.length (ZMod p) A = (Module.finrank (ZMod p) A : ℕ∞) :=
    @Module.length_eq_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  have hcard : Nat.card A = Nat.card (ZMod p) ^ Module.finrank (ZMod p) A :=
    @Module.natCard_eq_pow_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  rw [hlen, hfin, ENat.toNat_coe, hcard, Nat.card_zmod]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

