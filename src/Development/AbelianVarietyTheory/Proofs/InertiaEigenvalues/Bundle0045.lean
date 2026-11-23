module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoSidedShiftSeriesHasSum
section
open Polynomial

namespace GlobalTheory.TwoSidedShift

theorem mem_pow_span_iff (l : ℕ) (A : Type) [CommRing A] (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by
  simp [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_sum_shift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A]
    [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A),
    (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) →
    ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) →
      HasSum (fun n : ℤ => Θ (c n)) (Θ w) := by
  intro l _ A _ _ φ h c hc hsh
  set ψ : A →+* A := φ ^ h with hψdef
  have hψ : ∀ x, φ^[h] x = ψ x := fun x => by rw [hψdef, RingHom.coe_pow]
  have hsh' : ∀ n : ℤ, ψ (c n) = (l : A) * c (n + 1) := fun n => by rw [← hψ]; exact hsh n
  set T : ℕ → A := fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, c n with hT
  have hIcc : ∀ N : ℕ, Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ)
      = insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
    intro N; ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  have hstep : ∀ N : ℕ, T (N + 1) = T N + c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) := by
    intro N
    simp only [hT]
    rw [hIcc N, Finset.sum_insert, Finset.sum_insert]
    · ring
    · simp only [Finset.mem_Icc]; push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
  have hdstep : ∀ N : ℕ, (l : A) ^ (N + 1) ∣ T (N + 1) - T N := by
    intro N
    rw [hstep N, show T N + c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) - T N
      = c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) by ring]
    refine dvd_add ?_ ?_
    · have := hc ((N + 1 : ℕ) : ℤ)
      rwa [show (((N + 1 : ℕ) : ℤ)).natAbs = N + 1 by omega] at this
    · have := hc (-((N + 1 : ℕ) : ℤ))
      rwa [show (-((N + 1 : ℕ) : ℤ)).natAbs = N + 1 by omega] at this
  have hcauchy : ∀ m n : ℕ, m ≤ n → (l : A) ^ m ∣ T n - T m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [show T (n + 1) - T m = (T (n + 1) - T n) + (T n - T m) by ring]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hdstep n)) ih
  obtain ⟨w, hw⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance (f := T)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_span_iff]
      rw [← dvd_neg, neg_sub]; exact hcauchy m n hmn)
  have hwT : ∀ N : ℕ, (l : A) ^ N ∣ w - T N := by
    intro N
    have := hw N
    rw [SModEq.sub_mem, mem_pow_span_iff] at this
    rw [← dvd_neg, neg_sub]; exact this

  have hE : ∀ N : ℕ, ψ (T N) - (l : A) * T N = (l : A) * (c ((N : ℤ) + 1) - c (-(N : ℤ))) := by
    intro N
    induction N with
    | zero => simp [hT, hsh']; ring
    | succ N ih =>
      rw [hstep N, map_add (f := _), map_add (f := _), hsh', hsh']
      have e1 : (-((N + 1 : ℕ) : ℤ) + 1) = -(N : ℤ) := by push_cast; ring
      have e2 : (((N + 1 : ℕ) : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) + 1 := rfl
      rw [e1]
      push_cast at ih ⊢
      linear_combination ih
  have hEd : ∀ N : ℕ, (l : A) ^ N ∣ ψ (T N) - (l : A) * T N := by
    intro N
    rw [hE N]
    have h1 : (l : A) ^ (N + 1) ∣ c ((N : ℤ) + 1) := by
      have := hc ((N : ℤ) + 1)
      rwa [show ((N : ℤ) + 1).natAbs = N + 1 by omega] at this
    have h2 : (l : A) ^ N ∣ c (-(N : ℤ)) := by simpa using hc (-(N : ℤ))
    exact dvd_mul_of_dvd_right (dvd_sub ((pow_dvd_pow _ (by omega)).trans h1) h2) _
  refine ⟨w, ?_, ?_⟩
  · rw [hψ, ← sub_eq_zero]
    refine IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance _ (fun N => ?_)
    rw [SModEq.sub_mem, sub_zero, mem_pow_span_iff]
    rw [show ψ w - (l : A) * w = ψ (w - T N) + (ψ (T N) - (l : A) * T N) - (l : A) * (w - T N) by
      rw [map_sub]; ring]
    refine dvd_sub (dvd_add ?_ (hEd N)) (dvd_mul_of_dvd_right (hwT N) _)
    have := map_dvd ψ (hwT N)
    simpa [map_pow, map_natCast] using this
  · intro Θ hΘ
    set r : ℝ := ‖(l : ℂ_[l])‖ with hr
    have hr1 : r < 1 := by
      have h := PadicComplex.norm_extends' l (l : ℚ_[l])
      have h2 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
      rw [← h] at h2
      simpa using h2
    have hr0 : 0 ≤ r := norm_nonneg _
    have hbound : ∀ (n : ℕ) (a : A), (l : A) ^ n ∣ a → ‖Θ a‖ ≤ r ^ n := by
      intro n a ⟨b, hb⟩
      rw [hb, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg hr0 _) (hΘ b)
    change Filter.Tendsto (fun s : Finset ℤ => ∑ b ∈ s, Θ (c b)) Filter.atTop (nhds (Θ w))
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr1
    refine ⟨Finset.Icc (-(N : ℤ)) N, fun s hs => ?_⟩
    rw [dist_eq_norm, ← Finset.sum_sdiff hs]
    have hrest : ‖∑ n ∈ s \ Finset.Icc (-(N : ℤ)) N, Θ (c n)‖ ≤ r ^ N := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_
      have hn' : n ∉ Finset.Icc (-(N : ℤ)) N := (Finset.mem_sdiff.1 hn).2
      rw [Finset.mem_Icc] at hn'
      refine (hbound _ _ (hc n)).trans (pow_le_pow_of_le_one hr0 hr1.le (by omega))
    have hhead : ‖∑ n ∈ Finset.Icc (-(N : ℤ)) N, Θ (c n) - Θ w‖ ≤ r ^ N := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← map_sub]
      refine hbound N _ ?_
      rw [← dvd_neg, neg_sub]; exact hwT N
    rw [add_sub_assoc]
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hrest hhead)) hN

end GlobalTheory.TwoSidedShift

theorem GlobalTheory.twoSided_shift_series : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A), (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) → ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun n : ℤ => Θ (c n)) (Θ w) :=
  GlobalTheory.TwoSidedShift.exists_sum_shift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UdlApply
section
namespace GlobalTheory.UnipotentDecomposition

open Matrix

theorem udl_apply {O : Type} [CommRing O] {m : ℕ} (A B : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (A * Matrix.diagonal d * B) i j = ∑ k, A i k * d k * B k j := by
  rw [Matrix.mul_apply]; simp_rw [Matrix.mul_diagonal]

theorem key {O : Type} [CommRing O] [IsLocalRing O] {α β : O} (hab : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
      (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        (∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)) ∧
        (∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)) ∧
        g = (u * Matrix.diagonal fun i => (d i : O)) * l ∧ ∀ i, α * β ∣ (d i : O) - g i i := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    refine ⟨1, fun i => i.elim0, 1, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    ext i; exact i.elim0
  | succ n ih =>
    intro g hg hu
    set a : Oˣ := (hu (Fin.last n)).unit with ha
    have haa : (a : O) = g (Fin.last n) (Fin.last n) := IsUnit.unit_spec _
    have hinv : (↑a⁻¹ : O) * ↑a = 1 := Units.inv_mul a
    set r : Fin n → O := fun i => g i.castSucc (Fin.last n) with hr_def
    set c : Fin n → O := fun j => g (Fin.last n) j.castSucc with hc_def
    set G : Matrix (Fin n) (Fin n) O := fun i j => g i.castSucc j.castSucc - r i * ↑a⁻¹ * c j with hG_def
    have hr : ∀ i, α ∣ r i := fun i => (hg i.castSucc (Fin.last n)).1 (Fin.castSucc_lt_last i)
    have hc : ∀ j, β ∣ c j := fun j => (hg (Fin.last n) j.castSucc).2 (Fin.castSucc_lt_last j)
    have hG : ∀ i j, (i < j → α ∣ G i j) ∧ (j < i → β ∣ G i j) := by
      intro i j
      constructor
      · intro h
        exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right (hr i) _) _)
      · intro h
        exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_left (hc j) _)
    have hrc : ∀ i, α * β ∣ r i * ↑a⁻¹ * c i := by
      intro i
      rw [show r i * ↑a⁻¹ * c i = r i * c i * ↑a⁻¹ by ring]
      exact Dvd.dvd.mul_right (mul_dvd_mul (hr i) (hc i)) _
    have hGu : ∀ i, IsUnit (G i i) := by
      intro i
      by_contra h
      have h1 : r i * ↑a⁻¹ * c i ∈ nonunits O := fun hu' => hab (isUnit_of_dvd_unit (hrc i) hu')
      have h2 := IsLocalRing.nonunits_add (show G i i ∈ nonunits O from h) h1
      have h3 : G i i + r i * ↑a⁻¹ * c i = g i.castSucc i.castSucc := sub_add_cancel _ _
      rw [h3] at h2
      exact h2 (hu _)
    obtain ⟨U, D, L, hU, hL, hUDL, hD⟩ := ih G hG hGu
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j)
              (fun i' => Fin.lastCases (motive := fun _ => O) (r i' * ↑a⁻¹) (fun j' => U i' j') j) i,
            fun i => Fin.lastCases (motive := fun _ => Oˣ) a D i,
            Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun j' => ↑a⁻¹ * c j') j)
              (fun i' => Fin.lastCases (motive := fun _ => O) 0 (fun j' => L i' j') j) i,
            ?_, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
        first | exact hr i | exact (hr i).mul_right _
      · simpa using hU i j
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
        first | exact hc j | exact (hc j).mul_left _
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
      · simpa using hL i j
    · ext i j
      rw [udl_apply, Fin.sum_univ_castSucc]
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [haa]
      · simp [c]
        done
      · simp [r]
        done
      · have e := congrFun (congrFun hUDL i) j
        rw [udl_apply] at e
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero, mul_one]
        rw [← e]
        simp only [G]
        linear_combination (-(r i * ↑a⁻¹ * c j)) * hinv
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [haa]
      · have e : ((D i : O)) - g i.castSucc i.castSucc = ((D i : O) - G i i) - r i * ↑a⁻¹ * c i := by
          simp [G]; ring
        simpa [e] using dvd_sub (hD i) (hrc i)

theorem main : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] [IsLocalRing O] {α β : O}, ¬IsUnit (α * β) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), d2 α β g → (∀ (i : Fin n), IsUnit (g i i)) → ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O), d3 α u ∧ d1 β l ∧ g = (u * Matrix.diagonal fun (i : Fin n) ↦ (↑(d i) : O)) * l ∧ ∀ (i : Fin n), α * β ∣ (↑(d i) : O) - g i i) := by
  intro d1 d2 d3 O _ _ α β hab n g hg hu
  exact key hab n g hg hu

end GlobalTheory.UnipotentDecomposition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldTsumIntegralFundamentalDomain
section
open MeasureTheory

namespace GlobalTheory

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {ν : Measure G} [ν.IsHaarMeasure]
    {Γ : Subgroup G} [Countable Γ] {𝓖 : Set G}

theorem fundamentalDomain_lintegral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G) :
    ∫⁻ y in 𝓖, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂ν
      = ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν := by
  rw [lintegral_tsum (fun γ => by fun_prop)]
  set F : G → ENNReal := fun g => ‖P (x⁻¹ * g)‖ₑ * ‖a x‖ₑ * ‖b g‖ₑ with hF
  have key : ∀ γ : Γ, ∀ y, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = ‖P (x⁻¹ * ((γ : G)⁻¹ * y))‖ₑ * ‖a x‖ₑ * ‖b ((γ : G)⁻¹ * y)‖ₑ
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.lintegral_eq_tsum' F, ← lintegral_mul_left_eq_self _ x]
  simp [hF]

theorem fundamentalDomain_integral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G)
    (hfin : ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ≠ ⊤) :
    ∑' γ : Γ, ∫ y in 𝓖, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) ∂ν
      = ∫ g, star (a x) * b (x * g) * P g ∂ν := by
  set F : G → ℂ := fun g => star (a x) * b g * P (x⁻¹ * g) with hF
  have hFi : Integrable F ν := by
    refine ⟨by fun_prop, ?_⟩
    unfold HasFiniteIntegral
    rw [← lintegral_mul_left_eq_self _ x]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
    refine lintegral_congr (fun g => ?_)
    have hs : ‖star (a x)‖ₑ = ‖a x‖ₑ := by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
    simp only [hF, enorm_mul, hs, inv_mul_cancel_left]
    ring
  have key : ∀ γ : Γ, ∀ y, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = star (a x) * b ((γ : G)⁻¹ * y) * P (x⁻¹ * ((γ : G)⁻¹ * y))
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.integral_eq_tsum' F hFi, ← integral_mul_left_eq_self F x]
  simp [hF]

theorem unfold_tsum_fundamentalDomain (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (a b P : G → ℂ)
    (ha : Continuous a) (hbc : Continuous b) (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g)
    (hP : StronglyMeasurable P)
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  have ham : Measurable a := ha.measurable
  have hbm : Measurable b := hbc.measurable
  have hPm : Measurable P := hP.measurable
  have hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ := fun z => by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
  set μ := ν.restrict 𝓖 with hμ

  have hT : ∫⁻ x, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ∂μ ≠ ⊤ := by
    rw [← lintegral_congr (fun x => fundamentalDomain_lintegral_unfold_left h𝓖 hb hbm hPm (a := a) x)]
    exact hfin
  set k : G → G → ℂ := fun x g => star (a x) * b (x * g) * P g with hk
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk, Function.uncurry_def]; fun_prop
  have hki : Integrable (Function.uncurry k) (μ.prod ν) := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ (by fun_prop)]
    refine lt_of_le_of_lt (le_of_eq ?_) hT.lt_top
    refine lintegral_congr (fun x => lintegral_congr (fun g => ?_))
    simp only [hk, Function.uncurry_apply_pair, enorm_mul, hs]
    ring
  refine ⟨?_, ?_⟩
  · have h1 := hki.swap.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall (fun g => ?_))
    simp only [hk, Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    rw [integral_mul_const, mul_comm]

  · set f : Γ → G × G → ℂ := fun γ z => star (a z.1) * b z.2 * P (z.1⁻¹ * (γ : G)⁻¹ * z.2) with hf
    have hfm : ∀ γ, Measurable (f γ) := fun γ => by simp only [hf]; fun_prop
    have hfe : ∀ γ x y, ‖f γ (x, y)‖ₑ = ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ := by
      intro γ x y; simp only [hf, enorm_mul, hs]; ring
    have hsum : ∑' γ : Γ, ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [← lintegral_tsum (fun γ => ((hfm γ).enorm.lintegral_prod_right').aemeasurable)]
      have hx : ∀ x, ∑' γ : Γ, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ
          = ∫⁻ y, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂μ := fun x => by
        rw [← lintegral_tsum (f := fun γ y => ‖f γ (x, y)‖ₑ)
          (fun γ => ((hfm γ).comp measurable_prodMk_left).enorm.aemeasurable)]
        simp only [hfe]
      rw [lintegral_congr hx]
      exact hfin
    have hfi : ∀ γ, Integrable (f γ) (μ.prod μ) := fun γ =>
      ⟨(hfm γ).aestronglyMeasurable, by
        unfold HasFiniteIntegral
        rw [lintegral_prod _ (hfm γ).enorm.aemeasurable]
        exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun γ : Γ => ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ) γ)
          hsum.lt_top⟩
    have lhs : ∀ γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν)
        = ∫ x, ∫ y, f γ (x, y) ∂μ ∂μ := by
      intro γ; rw [← Measure.prod_restrict, ← integral_prod _ (hfi γ)]
    rw [tsum_congr lhs, ← integral_tsum (fun γ => (hfi γ).integral_prod_left.aestronglyMeasurable)
      (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun γ =>
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _))]
    have hae : ∀ᵐ x ∂μ, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν < ⊤ :=
      ae_lt_top (show Measurable (fun z : G × G => ‖P z.2‖ₑ * ‖a z.1‖ₑ * ‖b (z.1 * z.2)‖ₑ) by
        fun_prop).lintegral_prod_right' hT
    have step : (∫ x, ∑' γ : Γ, ∫ y, f γ (x, y) ∂μ ∂μ) = ∫ x, ∫ g, k x g ∂ν ∂μ :=
      integral_congr_ae (hae.mono fun x hx => fundamentalDomain_integral_unfold_left h𝓖 hb hbm hPm x hx.ne)
    rw [step, integral_integral_swap hki]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hk]
    rw [integral_mul_const, mul_comm]
end
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsModSqFiniteOfFields
section
namespace GlobalTheory

theorem isSquare_one_add_of_pow_two_pow_eq_zero {A : Type} [CommRing A] (c : A)
    (hc : 2 * c = 1) : ∀ (m : ℕ) (n : A), n ^ (2 ^ m) = 0 → IsSquare (1 + n) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    simp only [pow_zero, pow_one] at hn
    exact ⟨1, by rw [hn]; ring⟩
  | succ m ih =>
    intro n hn
    have hnil : IsNilpotent (c * n) := ⟨2 ^ (m + 1), by rw [mul_pow, hn, mul_zero]⟩
    obtain ⟨v, hv⟩ := (hnil.isUnit_one_add).exists_right_inv
    have hn' : (-(c ^ 2 * n ^ 2 * v ^ 2)) ^ (2 ^ m) = 0 := by
      have : -(c ^ 2 * n ^ 2 * v ^ 2) = n ^ 2 * (-(c ^ 2 * v ^ 2)) := by ring
      rw [this, mul_pow, ← pow_mul, ← pow_succ', hn, zero_mul]
    obtain ⟨z, hz⟩ := ih _ hn'
    refine ⟨(1 + c * n) * z, ?_⟩
    linear_combination (1 + c * n) ^ 2 * hz + (c ^ 2 * n ^ 2 * ((1 + c * n) * v + 1)) * hv
      + (-n) * hc

theorem isSquare_one_add_of_isNilpotent {A : Type} [CommRing A] (c : A) (hc : 2 * c = 1)
    {n : A} (hn : IsNilpotent n) : IsSquare (1 + n) := by
  obtain ⟨N, hN⟩ := hn
  exact isSquare_one_add_of_pow_two_pow_eq_zero c hc N n
    (pow_eq_zero_of_le (Nat.lt_two_pow_self).le hN)

theorem units_modSq_finite_of_fields : ∀ (k : Type) [Field k] [CharZero k],
    (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L],
      Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) →
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A],
      Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  intro k _ _ hL A _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hc : (2 : A) * algebraMap k A (1 / 2) = 1 := by
    have h2 : (2 : A) * algebraMap k A (1 / 2) = algebraMap k A (2 * (1 / 2)) := by
      rw [map_mul, map_ofNat]
    rw [h2]
    norm_num
  let Q : MaximalSpectrum A → Type := fun I =>
    (A ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (A ⧸ I.asIdeal)ˣ →* (A ⧸ I.asIdeal)ˣ).range
  haveI hQ : ∀ I, Finite (Q I) := by
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact hL (A ⧸ I.asIdeal)
  let φ : Aˣ →* ((I : MaximalSpectrum A) → Q I) := MonoidHom.pi fun I =>
    (QuotientGroup.mk' _).comp (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have key : ∀ (I : MaximalSpectrum A) (u : Aˣ), φ u I = 1 ↔
      Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u ∈
        (powMonoidHom 2 : (A ⧸ I.asIdeal)ˣ →* (A ⧸ I.asIdeal)ˣ).range :=
    fun I u => QuotientGroup.eq_one_iff _
  have hS : (powMonoidHom 2 : Aˣ →* Aˣ).range ≤ φ.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    funext I
    rw [Pi.one_apply, key]
    exact ⟨Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom y, by simp⟩
  have hk : ∀ x : Aˣ, φ x = 1 → x ∈ (powMonoidHom 2 : Aˣ →* Aˣ).range := by
    intro x hx
    have hloc : ∀ I : MaximalSpectrum A, ∃ w : (A ⧸ I.asIdeal)ˣ,
        (w : A ⧸ I.asIdeal) ^ 2 = Ideal.Quotient.mk I.asIdeal x := by
      intro I
      have h1 := (key I x).1 (congrFun hx I)
      obtain ⟨w, hw⟩ := h1
      refine ⟨w, ?_⟩
      have := congrArg (fun u : (A ⧸ I.asIdeal)ˣ => (u : A ⧸ I.asIdeal)) hw
      simpa using this
    choose w hw using hloc
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun I : MaximalSpectrum A => I.asIdeal)
      (fun I J h => MaximalSpectrum.isCoprime_of_ne h) (fun I => (w I : A ⧸ I.asIdeal))
    have hmem : ∀ I : MaximalSpectrum A, (x : A) - a ^ 2 ∈ I.asIdeal := by
      intro I
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      rw [ha I, hw I, sub_self]
    have hjac : (x : A) - a ^ 2 ∈ (⊥ : Ideal A).jacobson := by
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    have hnil : IsNilpotent ((x : A) - a ^ 2) := by
      obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
      refine ⟨N, ?_⟩
      have := Ideal.pow_mem_pow hjac N
      rw [hN] at this
      simpa using this
    set m := (x : A) - a ^ 2 with hm
    have ha2 : IsUnit (a ^ 2) := by
      have : a ^ 2 = (x : A) + (-m) := by rw [hm]; ring
      rw [this]
      exact hnil.neg.isUnit_add_left_of_commute x.isUnit (Commute.all _ _)
    have hau : IsUnit a := (isUnit_pow_iff (by norm_num)).1 ha2
    obtain ⟨b, hb⟩ := hau
    have hn2 : IsNilpotent (((b⁻¹ : Aˣ) : A) ^ 2 * m) :=
      (Commute.all _ _).isNilpotent_mul_left hnil
    obtain ⟨z, hz⟩ := isSquare_one_add_of_isNilpotent _ hc hn2
    have hzu : IsUnit z := by
      have hu : IsUnit (1 + ((b⁻¹ : Aˣ) : A) ^ 2 * m) := hn2.isUnit_one_add
      rw [hz] at hu
      exact isUnit_of_mul_isUnit_left hu
    refine ⟨b * hzu.unit, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec]
    have hbb : (b : A) * ((b⁻¹ : Aˣ) : A) = 1 := by simp
    have hxm : (x : A) = a ^ 2 + m := by rw [hm]; ring
    rw [hxm, ← hb]
    linear_combination (b : A) ^ 2 * hz.symm + (m * ((b : A) * ((b⁻¹ : Aˣ) : A) + 1)) * hbb
  let ψ := QuotientGroup.lift _ φ hS
  have hinj : Function.Injective ψ := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with
    | H x =>
    induction q using QuotientGroup.induction_on with
    | H y =>
    rw [QuotientGroup.eq]
    apply hk
    have h1 : φ x = φ y := hpq
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  exact Finite.of_injective ψ hinj

end GlobalTheory
end

