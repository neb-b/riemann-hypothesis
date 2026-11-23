module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpInert
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_inert : ∀ (p N j : ℕ), 2 ≤ p → j ≤ N → HasSum (fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ |((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)| ≤ N / ((p : ℝ) - 1) := by
  intro p N j hp hjN
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpsq : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp0' : (p : ℝ) ≠ 0 := hp0.ne'
  have hp1' : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hpsq' : (p : ℝ) ^ 2 - 1 ≠ 0 := hpsq.ne'
  refine ⟨?_, ?_⟩
  · have hr1 : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have hg := hasSum_geometric_of_lt_one (by positivity) hr1
    have hE : HasSum (fun k : ℕ => (if Even (2 * k + 1) then (j : ℝ) else (N : ℝ) - j) /
        (p : ℝ) ^ (2 * k + 1)) (((N : ℝ) - j) / p * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
      have hf : (fun k : ℕ => (if Even (2 * k + 1) then (j : ℝ) else (N : ℝ) - j) /
          (p : ℝ) ^ (2 * k + 1)) = fun k => ((N : ℝ) - j) / p * ((p : ℝ) ^ 2)⁻¹ ^ k := by
        funext k
        rw [if_neg (Nat.not_even_two_mul_add_one k), inv_pow, ← pow_mul, pow_succ,
          ← div_eq_mul_inv, div_div, mul_comm ((p : ℝ) ^ (2 * k)) (p : ℝ)]
      rw [hf]
      exact hg.mul_left _
    have hO : HasSum (fun k : ℕ => (if Even (2 * k + 1 + 1) then (j : ℝ) else (N : ℝ) - j) /
        (p : ℝ) ^ (2 * k + 1 + 1)) ((j : ℝ) / (p : ℝ) ^ 2 * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
      have hf : (fun k : ℕ => (if Even (2 * k + 1 + 1) then (j : ℝ) else (N : ℝ) - j) /
          (p : ℝ) ^ (2 * k + 1 + 1)) = fun k => (j : ℝ) / (p : ℝ) ^ 2 * ((p : ℝ) ^ 2)⁻¹ ^ k := by
        funext k
        rw [if_pos ⟨k + 1, by ring⟩, inv_pow, ← pow_mul, ← div_eq_mul_inv, div_div, ← pow_add,
          show 2 * k + 1 + 1 = 2 + 2 * k by ring]
      rw [hf]
      exact hg.mul_left _
    have h := HasSum.even_add_odd (f := fun n : ℕ =>
      (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)) hE hO
    have hinv : (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ = (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) := by
      rw [show (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 by
        rw [sub_div, div_self (pow_ne_zero 2 hp0'), one_div], inv_div]
    have hv : (j : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1) =
        ((N : ℝ) - j) / p * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ + (j : ℝ) / (p : ℝ) ^ 2 * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
      rw [hinv]
      field_simp
      ring
    rw [hv]
    exact h
  · have hA : |(N : ℝ) - 2 * j| ≤ N := abs_le.2 ⟨by linarith, by linarith⟩
    rw [abs_div, abs_mul, abs_of_pos hp0, abs_of_pos hpsq, div_le_div_iff₀ hpsq hp1]
    nlinarith [abs_nonneg ((N : ℝ) - 2 * j),
      mul_le_mul_of_nonneg_right hA (by nlinarith : (0 : ℝ) ≤ p * (p - 1)),
      mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hp1.le]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualElements
section
open Filter Topology Metric

namespace GlobalTheory.CompanionTheory.ExpChart.DualElements

theorem exists_det_ne_zero {X : Type} {g : ℕ} (w : X → Fin g → ℂ)
    (h : ∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * w x a = 0) → c = 0) :
    ∃ a : Fin g → X, (Matrix.of fun i j => w (a i) j).det ≠ 0 := by
  have hspan : Submodule.span ℂ (Set.range w) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hfx : ∀ y : Fin g → ℂ, f y = ∑ a, f (fun j => if a = j then 1 else 0) * y a := by
      intro y
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      exact Finset.sum_congr rfl fun a _ => by rw [smul_eq_mul, mul_comm]
    have hc := h (fun a => f (fun j => if a = j then 1 else 0)) (fun x => by
      rw [← hfx]
      exact hf (Submodule.subset_span ⟨x, rfl⟩))
    refine LinearMap.ext fun y => ?_
    rw [hfx y, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun a _ => by
      rw [show f (fun j => if a = j then 1 else 0) = 0 from congrFun hc a, zero_mul]
  obtain ⟨b, hb, hbs, hli⟩ := exists_linearIndependent ℂ (Set.range w)
  let B := Module.Basis.mk hli (by rw [Subtype.range_coe, hbs, hspan])
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = g := by
    rw [← Module.finrank_eq_card_basis B]
    simp
  let e : Fin g ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hex : ∀ i, ∃ x, w x = (e i : Fin g → ℂ) := fun i => hb (e i).2
  choose a ha using hex
  refine ⟨a, ?_⟩
  have hrow : LinearIndependent ℂ (Matrix.of fun i j => w (a i) j).row := by
    have hEq : (Matrix.of fun i j => w (a i) j).row = Subtype.val ∘ e := by
      ext i j
      simp [Matrix.row, ha]
    rw [hEq]
    exact hli.comp _ e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hrow
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem exists_dual_elements :
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (r : R) (g : ℕ)
      (E : A →+* Localization.Away r) (v : Fin g → (A →+* DualNumber (Localization.Away r)))
      (φ : Localization.Away r →+* ℂ),
      (∀ x : R, E (algebraMap R A x) = algebraMap R (Localization.Away r) x) →
      (∀ a (x : R), TrivSqZeroExt.snd (v a (algebraMap R A x)) = 0) →
      (∀ a x, TrivSqZeroExt.fst (v a x) = E x) →
      (∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * φ (TrivSqZeroExt.snd (v a x)) = 0) → c = 0) →
      ∃ (ρ : R) (t : Fin g → A), φ (algebraMap R (Localization.Away r) ρ) ≠ 0 ∧
        (∀ c, E (t c) = 0) ∧
        ∀ a c, TrivSqZeroExt.snd (v a (t c)) =
          if a = c then algebraMap R (Localization.Away r) ρ else 0 := by
  intro R A _ _ _ r g E v φ h1 h2 h3 h4
  let D : Fin g → A →+ Localization.Away r := fun a =>
    AddMonoidHom.mk' (fun x => TrivSqZeroExt.snd (v a x)) (fun x y => by
      rw [map_add (f := _), TrivSqZeroExt.snd_add])
  have hD : ∀ a x, D a x = TrivSqZeroExt.snd (v a x) := fun _ _ => rfl
  have hDmul : ∀ a x y, D a (x * y) = E x * D a y + E y * D a x := by
    intro a x y
    rw [hD, hD, hD, map_mul, TrivSqZeroExt.snd_mul, h3, h3, smul_eq_mul, op_smul_eq_mul, mul_comm (TrivSqZeroExt.snd (v a x))]
  have hDalg : ∀ a (s : R), D a (algebraMap R A s) = 0 := fun a s => h2 a s
  have hDs : ∀ a (s : R) x, D a (algebraMap R A s * x) =
      algebraMap R (Localization.Away r) s * D a x := by
    intro a s x
    rw [hDmul, hDalg, h1, mul_zero, add_zero]
  obtain ⟨a, ha⟩ := exists_det_ne_zero (X := A) (fun x i => φ (D i x)) h4
  obtain ⟨⟨b, hbm⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers r) (fun c => E (a c))
  have hbu : IsUnit (algebraMap R (Localization.Away r) b) :=
    IsLocalization.map_units _ (⟨b, hbm⟩ : Submonoid.powers r)
  have hb' : ∀ c, ∃ s, algebraMap R (Localization.Away r) s =
      algebraMap R (Localization.Away r) b * E (a c) := fun c => by
    obtain ⟨s, hs⟩ := hb c
    exact ⟨s, by rw [hs, Algebra.smul_def]⟩
  choose s hs using hb'
  let t' : Fin g → A := fun c => algebraMap R A b * a c - algebraMap R A (s c)
  have hEt' : ∀ c, E (t' c) = 0 := by
    intro c
    simp only [t', map_sub, map_mul, h1, hs, sub_self]
  have hDt' : ∀ i c, D i (t' c) = algebraMap R (Localization.Away r) b * D i (a c) := by
    intro i c
    simp only [t', map_sub, hDs, hDalg, sub_zero]
  let N : Matrix (Fin g) (Fin g) (Localization.Away r) := Matrix.of fun c i => D i (t' c)
  have hN : φ N.det ≠ 0 := by
    have hN0 : N = algebraMap R (Localization.Away r) b •
        Matrix.of (fun c i => D i (a c)) := by
      ext c i
      simp [N, hDt']
    rw [hN0, Matrix.det_smul, map_mul, map_pow, RingHom.map_det]
    refine mul_ne_zero (pow_ne_zero _ (hbu.map φ).ne_zero) ?_
    have hM : φ.mapMatrix (Matrix.of fun c i => D i (a c)) =
        Matrix.of fun i j => φ (D j (a i)) := by
      ext i j
      simp
    rw [hM]
    exact ha
  obtain ⟨⟨b2, hb2m⟩, hb2⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers r)
    (fun o : Option (Fin g × Fin g) => o.elim N.det (fun p => N.adjugate p.1 p.2))
  have hb2u : IsUnit (algebraMap R (Localization.Away r) b2) :=
    IsLocalization.map_units _ (⟨b2, hb2m⟩ : Submonoid.powers r)
  have hρ : ∃ ρ, algebraMap R (Localization.Away r) ρ =
      algebraMap R (Localization.Away r) b2 * N.det := by
    obtain ⟨s, hs⟩ := hb2 none
    exact ⟨s, by rw [hs, Algebra.smul_def]; rfl⟩
  have hn : ∀ c c', ∃ n, algebraMap R (Localization.Away r) n =
      algebraMap R (Localization.Away r) b2 * N.adjugate c c' := fun c c' => by
    obtain ⟨s, hs⟩ := hb2 (some (c, c'))
    exact ⟨s, by rw [hs, Algebra.smul_def]; rfl⟩
  obtain ⟨ρ, hρ⟩ := hρ
  choose n hn using hn
  refine ⟨ρ, fun c => ∑ c', algebraMap R A (n c c') * t' c', ?_, ?_, ?_⟩
  · rw [hρ, map_mul]
    exact mul_ne_zero (hb2u.map φ).ne_zero hN
  · intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun c' _ => by rw [map_mul, hEt', mul_zero]
  · intro i c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hD, map_sum]
    have hsum : ∑ c', D i (algebraMap R A (n c c') * t' c') =
        algebraMap R (Localization.Away r) b2 * (N.adjugate * N) c i := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [hDs, hn, mul_assoc]
      rfl
    rw [hsum, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hic : i = c
    · subst hic
      simp [hρ]
    · simp [hic, Ne.symm hic]

end GlobalTheory.CompanionTheory.ExpChart.DualElements
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsElementSamePrimeCount
section
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Ggeo

theorem exists_mem_count_normalizedFactors_span_eq :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I P : Ideal R), I ≠ ⊥ → P.IsPrime → P ≠ ⊥ →
      ∃ x ∈ I, x ≠ 0 ∧
        (normalizedFactors (Ideal.span {x})).count P = (normalizedFactors I).count P := by
  intro R _ _ I P hI hP hP0
  have hlt : I * P < I := by
    refine lt_of_le_of_ne Ideal.mul_le_left fun h => hP.ne_top ?_
    have h' : I * P = I * ⊤ := by rw [h, Ideal.mul_top]
    exact mul_left_cancel₀ hI h'
  obtain ⟨x, hxI, hxIP⟩ := SetLike.exists_of_lt hlt
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxIP (Submodule.zero_mem _)
  refine ⟨x, hxI, hx0, ?_⟩
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxI)
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hx0 hJ
  have hPJ : (normalizedFactors J).count P = 0 := by
    rw [Multiset.count_eq_zero]
    intro hmem
    obtain ⟨K, rfl⟩ := dvd_of_mem_normalizedFactors hmem
    apply hxIP
    have hle : Ideal.span {x} ≤ I * P := by
      rw [hJ, ← mul_assoc]
      exact Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self x)
  rw [hJ, normalizedFactors_mul hI hJ0, Multiset.count_add, hPJ, add_zero]

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem exists_eq_mul_mult_of_units (F : Type) [Field F] [NumberField F]
    (D : InfinitePlace F → ℝ)
    (h : ∀ u : (𝓞 F)ˣ, ∑ w : InfinitePlace F, Real.log (w ((u : 𝓞 F) : F)) * D w = 0) :
    ∃ c : ℝ, ∀ w, D w = c * (mult w : ℝ) := by
  classical
  have hsplit : ∀ f : InfinitePlace F → ℝ,
      ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)}, f v.1 = ∑ w, f w - f (w₀ : InfinitePlace F) := by
    intro f
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (w₀ : InfinitePlace F)), add_sub_cancel_right]
    exact (Finset.sum_subtype _ (fun w => by simp) f).symm
  let a : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ :=
    fun v => D v.1 / (mult v.1 : ℝ) - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ)
  let φ : ({w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ v, x v * a v
      map_add' := fun x y => by simp [Finset.sum_add_distrib, add_mul]
      map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u : (𝓞 F)ˣ, φ (logEmbedding F (Additive.ofMul u)) = 0 := by
    intro u
    have e1 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
          = 0 - Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) * D (w₀ : InfinitePlace F) := by
      rw [← h u]
      exact hsplit (fun w => Real.log (w (algebraMap (𝓞 F) F u)) * D w)
    have e2 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u))
          = 0 - (mult (w₀ : InfinitePlace F) : ℝ) * Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) := by
      rw [← sum_mult_mul_log u]
      exact hsplit (fun w => (mult w : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)))
    have hm0 : (mult (w₀ : InfinitePlace F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
    show ∑ v, logEmbedding F (Additive.ofMul u) v * a v = 0
    simp only [logEmbedding_component]
    calc ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)) * a v
        = ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
            - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ) * ((mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)))) := by
          apply Finset.sum_congr rfl
          intro v _
          have hm : (mult v.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
          simp only [a]
          field_simp
          try ring
      _ = 0 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
          field_simp
          try ring
  have hle : Submodule.span ℝ (unitLattice F : Set (logSpace F)) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hφ (Additive.toMul y)
  rw [unitLattice_span_eq_top F] at hle
  have ha : ∀ v, a v = 0 := by
    intro v
    have hv : (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) ∈ LinearMap.ker φ :=
      hle Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    have hφv : φ (Pi.single v (1 : ℝ)) = a v := by
      show ∑ v', (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) v' * a v' = a v
      simp [Pi.single_apply]
    rw [← hφv]
    exact hv
  refine ⟨D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ), fun w => ?_⟩
  have hm : (mult w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
  by_cases hw : w = (w₀ : InfinitePlace F)
  · subst hw
    field_simp
  · have hv := ha ⟨w, hw⟩
    simp only [a, sub_eq_zero] at hv
    rw [← hv]
    field_simp

theorem sum_eq_mean_of_units :
    ∀ (F : Type) [Field F] [NumberField F] (d t : (F →+* ℂ) → ℝ),
      (∀ u : (𝓞 F)ˣ, ∑ σ : F →+* ℂ, Real.log ‖σ ((u : 𝓞 F) : F)‖ * d σ = 0) →
      (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) →
      ∑ σ : F →+* ℂ, t σ * d σ =
        (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ) * ∑ σ : F →+* ℂ, d σ := by
  intro F _ _ d t hd ht
  classical
  have hfib : ∀ f : (F →+* ℂ) → ℝ, ∑ σ, f σ
      = ∑ w : InfinitePlace F, ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ :=
    fun f => (Finset.sum_fiberwise Finset.univ InfinitePlace.mk f).symm
  obtain ⟨c, hc⟩ := exists_eq_mul_mult_of_units F
    (fun w => ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), d σ) (by
      intro u
      have h1 := hd u
      rw [hfib] at h1
      refine Eq.trans ?_ h1
      apply Finset.sum_congr rfl
      intro w _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
      rw [InfinitePlace.apply])
  have ht' : ∀ σ : F →+* ℂ, t σ = t (InfinitePlace.mk σ).embedding := by
    intro σ
    have h2 : InfinitePlace.mk (InfinitePlace.mk σ).embedding = InfinitePlace.mk σ :=
      InfinitePlace.mk_embedding _
    rcases InfinitePlace.mk_eq_iff.mp h2 with h3 | h3
    · rw [h3]
    · have h4 := ht (InfinitePlace.mk σ).embedding
      rw [h3] at h4
      exact h4
  have hTfib : ∀ (w : InfinitePlace F) (f : (F →+* ℂ) → ℝ),
      ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), t σ * f σ
        = t w.embedding * ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ := by
    intro w f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
    rw [← ht' σ]
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hsum_d : ∑ σ, d σ = c * (Module.finrank ℚ F : ℝ) := by
    rw [hfib, ← InfinitePlace.sum_mult_eq, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact hc w
  have hsum_t : ∑ σ, t σ = ∑ w : InfinitePlace F, t w.embedding * (w.mult : ℝ) := by
    rw [hfib]
    apply Finset.sum_congr rfl
    intro w _
    have h5 := hTfib w (fun _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h5
    rw [h5, InfinitePlace.card_filter_mk_eq]
  have hsum_td : ∑ σ, t σ * d σ = c * ∑ σ, t σ := by
    conv_lhs => rw [hfib]
    rw [hsum_t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [hTfib w d]
    have h6 := hc w
    rw [h6]
    ring
  rw [hsum_td, hsum_d, div_mul_eq_mul_div, eq_div_iff hn]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHomAdjoinInv
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartHom

theorem exists_hom_adjoin_inv {σ Ω R : Type*} [Field Ω] [CharZero Ω] [CommRing R]
    (u : σ → Ω) (θ : MvPolynomial σ ℚ →+* R)
    (hker : ∀ G : MvPolynomial σ ℚ, aeval u G = (0 : Ω) → θ G = 0)
    (F : MvPolynomial σ ℚ) (hF : IsUnit (θ F))
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F : Ω)⁻¹ (Set.range u))) :
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval u G → ψ s = θ G := by
  classical
  by_cases hf : (aeval u F : Ω) = 0
  · have h0 : θ F = 0 := hker F hf
    have hR : Subsingleton R := by
      have : IsUnit (0 : R) := h0 ▸ hF
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp this)
    refine ⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
              map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun _ _ _ => Subsingleton.elim _ _⟩
  · let B := Localization.Away F
    have hunit : ∀ y : Submonoid.powers F, IsUnit (aeval u (y : MvPolynomial σ ℚ) : Ω) := by
      rintro ⟨_, n, rfl⟩
      simpa using (IsUnit.mk0 _ hf).pow n
    let Φ : B →ₐ[ℚ] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers F) (f := aeval u) hunit
    have hΦ : ∀ a : MvPolynomial σ ℚ, Φ (algebraMap _ B a) = aeval u a := fun a =>
      by simp [Φ, IsLocalization.liftAlgHom_apply]
    let Θ : B →+* R := IsLocalization.Away.lift F hF
    have hΘ : ∀ a : MvPolynomial σ ℚ, Θ (algebraMap _ B a) = θ a := fun a =>
      IsLocalization.Away.lift_eq F hF a
    have hnum : ∀ z : B, ∃ (n : ℕ) (a : MvPolynomial σ ℚ), z * algebraMap _ B (F ^ n) = algebraMap _ B a := by
      intro z
      obtain ⟨n, a, h⟩ := IsLocalization.Away.surj F z
      exact ⟨n, a, by simpa using h⟩
    have hmem : ∀ a : MvPolynomial σ ℚ, (aeval u a : Ω) ∈ S := by
      intro a
      have : (aeval u a : Ω) ∈ Algebra.adjoin ℚ (Set.range u) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨a, rfl⟩
      rw [hS]
      exact Algebra.adjoin_mono (Set.subset_insert _ _) this
    have hinv : (aeval u F : Ω)⁻¹ ∈ S := by
      rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
    have hΦS : ∀ z : B, Φ z ∈ S := by
      intro z
      obtain ⟨n, a, h⟩ := hnum z
      have h2 := congrArg Φ h
      rw [map_mul, hΦ, hΦ, map_pow] at h2
      have : Φ z = aeval u a * ((aeval u F : Ω)⁻¹) ^ n := by
        rw [← h2, inv_pow, _root_.mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hf), _root_.mul_one]
      rw [this]
      exact S.mul_mem (hmem a) (S.pow_mem hinv n)
    let Φ' : B →+* S := (Φ : B →+* Ω).codRestrict S.toSubsemiring hΦS
    have hΦ' : ∀ z, ((Φ' z : S) : Ω) = Φ z := fun _ => rfl
    have hsurj : Function.Surjective Φ' := by
      have hle : S ≤ Φ.range := by
        rw [hS]
        refine Algebra.adjoin_le ?_
        rintro _ (rfl | ⟨p, rfl⟩)
        · have hu : IsUnit (algebraMap _ B F) := IsLocalization.Away.algebraMap_isUnit F
          obtain ⟨v, hv⟩ := hu
          refine ⟨(↑v⁻¹ : B), ?_⟩
          have h1 : Φ (↑v⁻¹ : B) * aeval u F = 1 := by
            rw [← hΦ, ← hv, ← map_mul]; simp
          exact eq_inv_of_mul_eq_one_left h1
        · exact ⟨algebraMap (MvPolynomial σ ℚ) B (X p), (hΦ (X p)).trans (aeval_X u p)⟩
      intro s
      obtain ⟨z, hz⟩ := hle s.2
      exact ⟨z, Subtype.ext hz⟩
    have hkerΘ : RingHom.ker Φ' ≤ RingHom.ker Θ := by
      intro z hz
      rw [RingHom.mem_ker] at hz ⊢
      have hz0 : Φ z = 0 := by
        have := congrArg (Subtype.val) hz
        simpa [hΦ'] using this
      obtain ⟨n, a, h⟩ := hnum z
      have h2 := congrArg Φ h
      rw [map_mul, hz0, zero_mul, hΦ] at h2
      have ha : θ a = 0 := hker a h2.symm
      have h3 := congrArg Θ h
      rw [map_mul, hΘ, hΘ, ha, map_pow] at h3
      exact (hF.pow n).mul_left_eq_zero.mp h3
    refine ⟨RingHom.liftOfSurjective Φ' hsurj ⟨Θ, hkerΘ⟩, fun G s hs => ?_⟩
    have hsG : s = Φ' (algebraMap _ B G) := Subtype.ext (by rw [hΦ', hΦ, hs])
    rw [hsG, RingHom.liftOfRightInverse_comp_apply]
    exact hΘ G

end GlobalTheory.CompanionTheory.Ar.ChartHom
end

