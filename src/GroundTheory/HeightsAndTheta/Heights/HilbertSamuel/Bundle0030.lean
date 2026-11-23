module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSeparation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace GridSeparation

theorem norm_eval_le_of_torus {e : ℕ} (G : MvPolynomial (Fin e) ℤ) (ζ : Fin e → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := by
  rw [eval_map, eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_prod]
  simp [hζ]

theorem grid_finite (e m : ℕ) (hm : 0 < m) : {ζ : Fin e → ℂ | ∀ i, ζ i ^ m = 1}.Finite := by
  have h1 : {x : ℂ | x ^ m = 1}.Finite :=
    (Polynomial.nthRoots m (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hm] using hx
  convert Set.Finite.pi (t := fun _ : Fin e => {x : ℂ | x ^ m = 1}) fun _ => h1 using 1
  ext ζ
  simp [Set.mem_pi]

theorem norm_of_pow_eq_one {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ^ m = 1) : ‖x‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').mp (by rw [← norm_pow, hx, norm_one])

theorem proof (hNL : NormalLocusRep.Statement) (hFN : FibreNormBound.Statement)
    (hRG : RootGridLower.Statement) : GridSeparation.Statement := by
  classical
  intro K _ ι _ Ω _ y D A hV hBir hA
  obtain ⟨df, f, hf, hfP, hrep⟩ := hNL K ι Ω y D hV hBir
  obtain ⟨n, c, B, G, Fib, hn, hB1, hG0, hFib, hnorm⟩ := hFN K ι Ω y D A df f hV hBir hA hf hfP
  set SG : ℝ := ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) + 1 with hSG
  have hSG1 : 1 ≤ SG := by
    have : 0 ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := Finset.sum_nonneg fun d _ => by positivity
    linarith
  have hX : 1 ≤ 2 * B * SG := by nlinarith
  refine ⟨Real.log (2 * B * SG), Real.log_nonneg hX, fun τ => ?_⟩
  set m := G.totalDegree + c * (τ + 1) + 1 with hm
  have hm0 : 0 < m := by omega
  set Z := ((grid_finite (D + 1) m hm0).toFinset.filter
    fun ζ => eval ζ (map (Int.castRingHom ℂ) G) ≠ 0).biUnion Fib with hZ
  have hmem : ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ζ i ^ m = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
      ∀ z ∈ Fib ζ, z ∈ Z := fun ζ hζ hG z hz =>
    Finset.mem_biUnion.mpr ⟨ζ, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hζ, hG⟩, hz⟩
  have hZpt : ∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0 := by
    intro z hz
    obtain ⟨ζ, hζ, hzζ⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hζg, hGζ⟩ := Finset.mem_filter.mp hζ
    have hζg' : ∀ i, ζ i ^ m = 1 := (Set.Finite.mem_toFinset _).mp hζg
    exact hFib ζ (fun i => norm_of_pow_eq_one hm0 (hζg' i)) hGζ z hzζ
  refine ⟨Z, fun z hz => (hZpt z hz).1, fun s hs z hz => hrep A.a τ s hs z (hZpt z hz).1 (hZpt z hz).2, ?_⟩
  intro u hu hu0
  obtain ⟨F, hF0, hFdeg, hFb⟩ := hnorm τ u hu hu0
  by_contra hcon
  obtain ⟨ζ, hζm, hζ1⟩ := hRG (D + 1) m (G * F) (mul_ne_zero hG0 hF0) fun i => by
    have h1 := degreeOf_mul_le i G F
    have h2 := degreeOf_le_totalDegree G i
    have h3 := hFdeg i
    omega
  have hζn : ∀ i, ‖ζ i‖ = 1 := fun i => norm_of_pow_eq_one hm0 (hζm i)
  rw [map_mul, eval_mul, norm_mul] at hζ1
  have hGζ : eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at hζ1
    linarith
  set E := Real.exp (-(Real.log (2 * B * SG) * ((τ : ℝ) + 1))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hFle := hFb ζ hζn hGζ E hE0.le fun z hz => by
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0⟩ :=
      hrep A.a τ u hu z (hFib ζ hζn hGζ z hz).1 (hFib ζ hζn hGζ z hz).2
    refine ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, ?_⟩
    by_contra hlt
    exact hcon ⟨z, hmem ζ hζm hGζ z hz, dg, dh, g, h, hg, hh, hd, hy, hz0, (not_le.mp hlt).le⟩
  have hEX : E * (2 * B * SG) ^ (τ + 1) = 1 := by
    have : -(Real.log (2 * B * SG) * ((τ : ℝ) + 1)) = ((τ + 1 : ℕ) : ℝ) * (-Real.log (2 * B * SG)) := by
      push_cast
      ring
    rw [hE, this, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by linarith), ← mul_pow,
      inv_mul_cancel₀ (by linarith), one_pow]
  have hE1 : E ≤ 1 := by
    have : 1 ≤ (2 * B * SG) ^ (τ + 1) := one_le_pow₀ hX
    nlinarith
  have hEn : E ^ n ≤ E := pow_le_of_le_one hE0.le hE1 (by omega)
  have hGle : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ SG := by
    have := norm_eval_le_of_torus G ζ hζn
    linarith
  have hpow : 2 * SG * B ^ (τ + 1) ≤ (2 * B * SG) ^ (τ + 1) := by
    rw [show 2 * B * SG = (2 * SG) * B by ring, mul_pow]
    have hB0 : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
    have : 2 * SG ≤ (2 * SG) ^ (τ + 1) := le_self_pow₀ (by linarith) (by omega)
    nlinarith
  have hBp : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
  have hFn : ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * E := by
    calc _ ≤ B ^ (τ + 1) * E ^ n := hFle
      _ ≤ B ^ (τ + 1) * E := mul_le_mul_of_nonneg_left hEn hBp
  have key : 2 * (SG * (B ^ (τ + 1) * E)) ≤ 1 := by
    calc 2 * (SG * (B ^ (τ + 1) * E)) = (2 * SG * B ^ (τ + 1)) * E := by ring
      _ ≤ (2 * B * SG) ^ (τ + 1) * E := mul_le_mul_of_nonneg_right hpow hE0.le
      _ = 1 := by rw [mul_comm, hEX]
  have hFnn : 0 ≤ ‖eval ζ (map (Int.castRingHom ℂ) F)‖ := norm_nonneg _
  have : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ * ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤
      SG * (B ^ (τ + 1) * E) :=
    mul_le_mul hGle hFn hFnn (by linarith)
  linarith

end GridSeparation

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHeightsirationalHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockBirationalHilbert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def blockSum (γ : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, γ ⟨k, i⟩

omit [Fintype K] in
theorem isMultiHomog_monomial {γ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (h : blockSum γ = a) (r : ℤ) :
    IsMultiHomog (monomial γ r : MRing ι) a := by
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  exact congrFun h k

omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b c : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b)
    (habc : a + b = c) : IsMultiHomog (f * g) c := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, ← habc, Pi.add_apply]

omit [Fintype K] in
theorem isMultiHomog_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (d j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h1 := isMultiHomog_monomial (ι := ι) (γ := 0) (a := 0) (by funext k; simp [blockSum]) 1
    simpa using h1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact isMultiHomog_mul (h j (Finset.mem_insert_self j s))
      (ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj')) rfl


open Classical in
def monoSet (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) :=
  (Finset.Icc 0 (Finsupp.equivFunOnFinite.symm fun p : (Σ k, ι k) => a p.1)).filter (blockSum · = a)

theorem mem_monoSet {a : K → ℕ} {γ : (Σ k, ι k) →₀ ℕ} : γ ∈ monoSet a ↔ blockSum γ = a := by
  classical
  unfold monoSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨Finset.mem_Icc.mpr ⟨by simp, fun p => ?_⟩, h⟩⟩
  rw [Finsupp.coe_equivFunOnFinite_symm, ← h]
  exact Finset.single_le_sum (f := fun i => γ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)

omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem aeval_monomial_int (y : (Σ k, ι k) → Ω) (γ : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    aeval y (monomial γ r : MRing ι) = ((r : ℚ) : Ω) * aeval y (monomial γ (1 : ℤ) : MRing ι) := by
  simp [aeval_monomial]


omit [Fintype K] in
theorem valueSpan_le (y : (Σ k, ι k) → Ω) (a : K → ℕ) (W : Submodule ℚ Ω)
    (hW : ∀ γ : (Σ k, ι k) →₀ ℕ, blockSum γ = a → aeval y (monomial γ (1 : ℤ) : MRing ι) ∈ W) :
    valueSpan y a ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [g.as_sum, map_sum]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  rw [aeval_monomial_int, ← Rat.smul_def]
  exact W.smul_mem _ (hW γ (funext fun k => hg γ hγ k))

theorem finiteDimensional_valueSpan (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    FiniteDimensional ℚ (valueSpan y a) := by
  classical
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ
    (((monoSet a).image fun γ => aeval y (monomial γ (1 : ℤ) : MRing ι) : Finset Ω) : Set Ω))
    (valueSpan_le y a _ fun γ hγ => Submodule.subset_span ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨γ, mem_monoSet.mpr hγ, rfl⟩


omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem finrank_le_of_mul [CharZero Ω] {V W : Submodule ℚ Ω} [FiniteDimensional ℚ W] {t : Ω} (ht : t ≠ 0)
    (h : V ≤ W.comap (LinearMap.mulLeft ℚ t)) : Module.finrank ℚ V ≤ Module.finrank ℚ W := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ t) := fun a b hab => mul_left_cancel₀ ht hab
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj V)]
  exact Submodule.finrank_mono (Submodule.map_le_iff_le_comap.mpr h)

end BlockBirationalHilbert


open BlockBirationalHilbert in
theorem BlockBirationalHilbert.proof (hV : HilbFnValueSpan.Statement) : BlockBirationalHilbert.Statement := by
  intro K _ _ ι _ Ω _ _ y k₀ hy hbir m
  classical
  choose i hi using hy
  have hV' := hV K ι Ω y
  have := finiteDimensional_valueSpan (Ω := Ω) y

  have L : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else 0) =
      (Module.finrank ℚ (valueSpan y (blockDeg k₀ n)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk, blockDeg]
  have M : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else m k) =
      (Module.finrank ℚ (valueSpan y (fun k => if k = k₀ then n else m k)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk]

  set m₀ : K → ℕ := fun k => if k = k₀ then 0 else m k with hm₀
  let β : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.1 ≠ k₀ ∧ p.2 = i p.1 then m p.1 else 0
  have hβ : blockSum β = m₀ := by
    funext k
    by_cases hk : k = k₀ <;> simp [blockSum, β, hk, m₀]
  set u : Ω := aeval y (monomial β (1 : ℤ) : MRing ι) with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, aeval_monomial, map_one, one_mul, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
    rcases p with ⟨k, j⟩
    have h0 : β ⟨k, j⟩ ≠ 0 := Finsupp.mem_support_iff.mp hp
    simp only [β, Finsupp.coe_equivFunOnFinite_symm] at h0
    split_ifs at h0 with h
    · obtain ⟨_, rfl⟩ := h
      exact hi k
    · exact absurd rfl h0

  have key : ∀ α ∈ monoSet (ι := ι) m₀, ∃ (c : ℕ) (g h : MRing ι), IsMultiHomog g (blockDeg k₀ c) ∧
      IsMultiHomog h (blockDeg k₀ c) ∧ aeval y h ≠ 0 ∧
      aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y h = aeval y g * u := fun α hα =>
    hbir m₀ _ _ (isMultiHomog_monomial (mem_monoSet.mp hα) 1) (isMultiHomog_monomial hβ 1) hu
  choose c g h hg hh hh0 hgh using key
  refine ⟨∑ a ∈ (monoSet (ι := ι) m₀).attach, c a.1 a.2, fun n => ⟨?_, ?_⟩⟩
  ·
    rw [L, M]
    refine Nat.cast_le.mpr (finrank_le_of_mul hu (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨monomial β 1 * monomial γ 1,
      isMultiHomog_mul (isMultiHomog_monomial hβ 1) (isMultiHomog_monomial hγ 1) ?_, by
        simp only [map_mul, hu_def]⟩
    funext k; by_cases hk : k = k₀ <;> simp [hk, m₀, blockDeg]
  ·
    rw [M, L]
    have hH : aeval y (∏ a ∈ (monoSet (ι := ι) m₀).attach, h a.1 a.2) ≠ 0 := by
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun a _ => hh0 a.1 a.2
    refine Nat.cast_le.mpr (finrank_le_of_mul (mul_ne_zero (inv_ne_zero hu) hH)
      (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]

    set γ₀ := γ.filter (fun p => p.1 = k₀) with hγ₀
    set α := γ.filter (fun p => ¬ p.1 = k₀) with hα_def
    have hsplit : γ₀ + α = γ := Finsupp.filter_add_filter_not γ _
    have hα : blockSum α = m₀ := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, m₀]
    have hγ₀' : blockSum γ₀ = blockDeg k₀ n := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, blockDeg]
    have hαS : α ∈ monoSet (ι := ι) m₀ := mem_monoSet.mpr hα
    have hmem : (⟨α, hαS⟩ : {x // x ∈ monoSet (ι := ι) m₀}) ∈ (monoSet (ι := ι) m₀).attach :=
      Finset.mem_attach _ _
    refine Submodule.subset_span ⟨monomial γ₀ 1 * g α hαS *
      ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, h a.1 a.2,
      isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_monomial hγ₀' 1) (hg α hαS) rfl)
        (isMultiHomog_prod _ _ (fun a => blockDeg k₀ (c a.1 a.2)) fun a _ => hh a.1 a.2) ?_, ?_⟩
    · funext k
      by_cases hk : k = k₀
      · simp only [Pi.add_apply, Finset.sum_apply, blockDeg, hk, if_true]
        rw [← Finset.add_sum_erase _ _ hmem]
        ring
      · simp [blockDeg, hk, Finset.sum_apply]
    · have e1 : aeval y (monomial γ (1 : ℤ) : MRing ι) =
          aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι) := by
        rw [← map_mul, monomial_mul, hsplit, mul_one]
      rw [map_mul, map_mul, e1, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hmem]
      have e2 := hgh α hαS
      calc aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)
          = (u⁻¹ * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by
            rw [inv_mul_cancel₀ hu, one_mul]
        _ = u⁻¹ * (aeval y (g α hαS) * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by ring
        _ = u⁻¹ * (aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y (h α hαS)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by rw [e2]
        _ = u⁻¹ * (aeval y (h α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι)) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbFnValueSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HilbFnValueSpan

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def coneQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (coneQ y) := by
  have hring : ((coneQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MRing ι →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneQ, mConeMap]
    · intro i
      simp [coneQ, mConeMap]
  have hker : mCoordIdeal y =
      (RingHom.ker (coneQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (coneQ y))
  rw [e] at h
  rw [hker]
  exact h

theorem weight_blockWeight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem isWeightedHomogeneous_iff {R : Type} [CommRing R] (f : MvPolynomial (Σ k, ι k) R) (a : K → ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a ↔ ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight, h m (mem_support_iff.mpr hm) k]

theorem coneQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    coneQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  have hf' := (isWeightedHomogeneous_iff f a).mp hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p =
      ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
  simp only [coneQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_ker_iff (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    f ∈ RingHom.ker (coneQ y) ↔ aeval y f = 0 := by
  rw [RingHom.mem_ker, coneQ_eq y hf]
  constructor
  · intro h
    have hne : (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    rcases mul_eq_zero.mp h with h | h
    · exact MvPolynomial.C_eq_zero.mp h
    · exact absurd h hne
  · intro h
    rw [h, map_zero, zero_mul]

def evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] Ω :=
  (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap.comp (Submodule.subtype _)

def quotForms (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P :=
  (Ideal.Quotient.mkₐ ℚ P).toLinearMap.comp (Submodule.subtype _)

theorem range_evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    LinearMap.range (evalForms y a) = valueSpan y a := by
  apply le_antisymm
  · rintro _ ⟨⟨f, hf⟩, rfl⟩
    have hf' := (isWeightedHomogeneous_iff f a).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
    show aeval y f ∈ valueSpan y a
    conv => arg 2; rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    have hmon : aeval y (monomial v (AddMonoidAlgebra.coeff f v)) =
        AddMonoidAlgebra.coeff f v • aeval y (monomial v (1 : ℤ) : MRing ι) := by
      simp only [aeval_monomial, Algebra.smul_def, map_one, one_mul]
    rw [hmon]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨monomial v 1, ?_, rfl⟩)
    intro m hm k
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
    rw [hm]
    exact hf' v hv k
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    have hmem : MvPolynomial.map (Int.castRingHom ℚ) g ∈
        weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a := by
      rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff]
      exact fun m hm k => hg m (support_map_subset _ _ hm) k
    refine ⟨⟨_, hmem⟩, ?_⟩
    show aeval y (MvPolynomial.map (Int.castRingHom ℚ) g) = aeval y g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]

theorem finrank_gradedPiece (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    Module.finrank ℚ (NumbersDVR.gradedPiece
        ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) a) =
      Module.finrank ℚ (valueSpan y a) := by
  set P := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hrange : LinearMap.range (quotForms P a) = NumbersDVR.gradedPiece P a := by
    rw [quotForms, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hker : LinearMap.ker (quotForms P a) = LinearMap.ker (evalForms y a) := by
    ext ⟨f, hf⟩
    rw [mem_weightedHomogeneousSubmodule] at hf
    simp only [LinearMap.mem_ker, quotForms, evalForms, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    rw [show P = RingHom.ker (coneQ y) from map_mCoordIdeal y, mem_ker_iff y hf]
  rw [← hrange, ← range_evalForms y a, ← (quotForms P a).quotKerEquivRange.finrank_eq,
    ← (evalForms y a).quotKerEquivRange.finrank_eq]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq

end HilbFnValueSpan

theorem HilbFnValueSpan.proof : HilbFnValueSpan.Statement := by
  intro K _ _ ι _ Ω _ _ y a
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Int.natCast_nonneg _)]
  have ha : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => Int.toNat_natCast _
  rw [ha, HilbFnValueSpan.finrank_gradedPiece]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

