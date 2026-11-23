module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogFreeZeroDensityDirichletOneModulus
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedDerivLogDerivDirichletLViaNearbyZeros
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumRpowZerosLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.ZeroSum

theorem mem_disc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosBox χ (1 / 2) T) :
    ⌊ρ.im⌋ ∈ Finset.Icc (-⌈T⌉) ⌈T⌉ ∧ ρ ∈ zerosDisc χ (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I) 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [abs_le] at h3
  have a1 := Int.floor_le ρ.im
  have a2 := Int.lt_floor_add_one ρ.im
  have a3 := Int.le_ceil T
  refine ⟨?_, ?_, Or.inr ?_, h4⟩
  · rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast; linarith
    · have : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ (⌈T⌉ : ℤ) := by linarith
      exact_mod_cast this
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have b1 : |(ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).re| ≤ 2 := by
      rw [abs_le]; simp; constructor <;> linarith
    have b2 : |(ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).im| ≤ 1 := by
      have : (ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).im = ρ.im - ⌊ρ.im⌋ := by simp
      rw [this, abs_le]; constructor <;> linarith
    linarith
  · rintro rfl
    simp at h2

theorem total_count : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ),
    2 ≤ T → ∃ h : (zerosBox χ (1 / 2) T).Finite,
      ∑ ρ ∈ h.toFinset, (ord χ ρ : ℝ) ≤ C * (q * T ^ 2) := by
  obtain ⟨C, hC, H⟩ := _root_.GlobalTheory.LogDerivHigher.main
  refine ⟨12 * C, by positivity, fun q _ χ T hT => ?_⟩
  have hf : ∀ n : ℤ, (zerosDisc χ (2 + ((n : ℝ) : ℂ) * I) 3).Finite :=
    fun n => (H q χ 2 n 0 (by norm_num) le_rfl).1
  have hfin : (zerosBox χ (1 / 2) T).Finite := by
    refine ((Finset.Icc (-⌈T⌉) ⌈T⌉).finite_toSet.biUnion (fun n _ => hf n)).subset ?_
    intro ρ hρ
    simp only [Set.mem_iUnion]
    exact ⟨_, (mem_disc χ hρ).1, (mem_disc χ hρ).2⟩
  refine ⟨hfin, ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have a3 := Int.ceil_lt_add_one T
  have a4 := Int.le_ceil T
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc (-⌈T⌉) ⌈T⌉) (g := fun ρ : ℂ => ⌊ρ.im⌋)
    (fun ρ hρ => (mem_disc χ (hfin.mem_toFinset.1 hρ)).1)]
  have key : ∀ n ∈ Finset.Icc (-⌈T⌉) ⌈T⌉,
      ∑ ρ ∈ hfin.toFinset with ⌊ρ.im⌋ = n, (ord χ ρ : ℝ) ≤ C * (q * (3 * T)) := by
    intro n hn
    have h2 := (H q χ 2 n 0 (by norm_num) le_rfl).2.1
    rw [finsum_mem_eq_finite_toFinset_sum _ (hf n)] at h2
    have hn' : |(n : ℝ)| ≤ T + 1 := by
      rw [Finset.mem_Icc] at hn
      have c1 : ((-⌈T⌉ : ℤ) : ℝ) ≤ n := by exact_mod_cast hn.1
      have c2 : (n : ℝ) ≤ (⌈T⌉ : ℤ) := by exact_mod_cast hn.2
      push_cast at c1
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ ∑ ρ ∈ (hf n).toFinset, (ord χ ρ : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
          intro ρ hρ
          rw [Finset.mem_filter] at hρ
          rw [Set.Finite.mem_toFinset, ← hρ.2]
          exact (mem_disc χ (hfin.mem_toFinset.1 hρ.1)).2
      _ ≤ _ := h2
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hC.le
          refine (Real.log_le_self (by positivity)).trans ?_
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine (Finset.sum_le_card_nsmul _ _ _ key).trans ?_
  rw [nsmul_eq_mul]
  have hc : ((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℝ) ≤ 4 * T := by
    have h0 : (0 : ℤ) ≤ ⌈T⌉ + 1 - -⌈T⌉ := by
      have : (0 : ℤ) ≤ ⌈T⌉ := Int.ceil_nonneg (by linarith)
      omega
    have : (((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℤ) : ℝ) = ((⌈T⌉ + 1 - -⌈T⌉ : ℤ) : ℝ) := by
      rw [Int.card_Icc, Int.toNat_of_nonneg h0]
    push_cast at this
    rw [this]; linarith
  calc _ ≤ (4 * T) * (C * (q * (3 * T))) := by gcongr
    _ = _ := by ring

theorem layers {ι : Type*} (s : Finset ι) (w δ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {L η e : ℝ}
    (hL : 0 < L) (J : ℕ) (hJ : L * e < J) (hη : 0 ≤ η) :
    ∑ i ∈ s with η ≤ δ i, w i * Real.exp (-(L * δ i)) ≤
      ∑ j ∈ Finset.range J, Real.exp (-(L * η) - j) *
        (∑ i ∈ s with δ i ≤ min (η + (j + 1) / L) e, w i) + Real.exp (-(L * e)) * ∑ i ∈ s, w i := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hwi := hw i
  have hnn : ∀ j ∈ Finset.range J, 0 ≤ Real.exp (-(L * η) - j) *
      (if δ i ≤ min (η + (j + 1) / L) e then w i else 0) := by
    intro j _
    split_ifs <;> positivity
  have hs := Finset.sum_nonneg hnn
  have he : 0 ≤ Real.exp (-(L * e)) * w i := by positivity
  split_ifs with h
  · by_cases h2 : δ i ≤ e
    · have h0 : 0 ≤ L * (δ i - η) := mul_nonneg hL.le (by linarith)
      have a1 := Nat.floor_le h0
      have a2 := Nat.lt_floor_add_one (L * (δ i - η))
      have hm : ⌊L * (δ i - η)⌋₊ ∈ Finset.range J := by
        rw [Finset.mem_range, Nat.floor_lt h0]
        nlinarith
      have := Finset.single_le_sum hnn hm
      rw [if_pos] at this
      · have h3 : Real.exp (-(L * δ i)) ≤ Real.exp (-(L * η) - ⌊L * (δ i - η)⌋₊) :=
          Real.exp_le_exp.2 (by linarith)
        nlinarith
      · refine le_min ?_ h2
        have : δ i - η ≤ (⌊L * (δ i - η)⌋₊ + 1) / L := by
          rw [le_div_iff₀ hL]; linarith
        linarith
    · have h3 : Real.exp (-(L * δ i)) ≤ Real.exp (-(L * e)) :=
        Real.exp_le_exp.2 (by nlinarith)
      nlinarith
  · linarith

theorem sum_rpow_zeros_le : ∃ A C η₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < η₀ ∧ ∀ (q : ℕ) [NeZero q] (T u η : ℝ), 2 ≤ T → ((q : ℝ) * T) ^ A ≤ u → 0 ≤ η → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤ C * (u ^ (-η / 2) + u ^ (-η₀)) := by
  obtain ⟨A₁, C₁, η₁, hA₁, hC₁, hη₁, H₁⟩ := _root_.GlobalTheory.Lin.LogFree.zero_density
  obtain ⟨C₂, hC₂, H₂⟩ := total_count
  obtain ⟨e, he0, he1, he2⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ η₁ ∧ e ≤ 1 / 2 :=
    ⟨min η₁ (1 / 2), by positivity, min_le_left _ _, min_le_right _ _⟩
  have hr : Real.exp (-1 / 2) < 1 := by
    simpa using Real.exp_lt_exp.2 (show (-1 / 2 : ℝ) < 0 by norm_num)
  have hsum := summable_geometric_of_lt_one (Real.exp_pos (-1 / 2)).le hr
  set K := ∑' j : ℕ, Real.exp (-1 / 2) ^ j with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => by positivity
  refine ⟨2 * A₁ + 4 / e, C₁ * Real.exp (1 / 2) * K + C₂, e / 2, by positivity, by positivity,
    by positivity, fun q _ T u η hT hu hη => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hqT : (1 : ℝ) < q * T := by nlinarith
  have hu1 : 1 < u := (Real.one_lt_rpow hqT (by positivity)).trans_le hu
  have hu0 : 0 < u := by linarith
  have hL : 0 < Real.log u := Real.log_pos hu1
  have hM : 0 < Real.log (q * T) := Real.log_pos hqT
  have hLM : (2 * A₁ + 4 / e) * Real.log (q * T) ≤ Real.log u := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by positivity) hu
  set L := Real.log u with hLdef
  set M := Real.log (q * T) with hMdef
  have h4 : 0 < 4 / e := by positivity
  have hLM1 : 2 * A₁ * M ≤ L := by nlinarith
  have hLM2 : 4 * M ≤ e * L := by
    have : 4 / e * M ≤ L := by nlinarith [mul_pos hA₁ hM]
    rw [div_mul_eq_mul_div, div_le_iff₀ he0] at this
    linarith
  choose hfin hcount using fun χ : DirichletCharacter ℂ q => H₂ q χ T hT
  obtain ⟨J, hJ⟩ := exists_nat_gt (L * e)
  have step1 : ∀ χ : DirichletCharacter ℂ q,
      (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤
      ∑ j ∈ Finset.range J, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) +
        Real.exp (-(L * e)) * (C₂ * (q * T ^ 2)) := by
    intro χ
    have h := layers (hfin χ).toFinset (fun ρ => (ord χ ρ : ℝ)) (fun ρ => 1 - ρ.re)
      (fun _ => Nat.cast_nonneg _) hL J hJ hη
    have e1 : zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η} =
        ((hfin χ).toFinset.filter (fun ρ : ℂ => η ≤ 1 - ρ.re) : Finset ℂ) := by
      ext ρ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
      exact and_congr_right fun _ => ⟨fun _ => by linarith, fun _ => by linarith⟩
    have e2 : ∀ x : ℝ, x ≤ e → zerosBox χ (1 - x) T =
        ((hfin χ).toFinset.filter (fun ρ : ℂ => 1 - ρ.re ≤ x) : Finset ℂ) := by
      intro x hx
      ext ρ
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, zerosBox]
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨by linarith, b, c, d⟩, by linarith⟩
      · rintro ⟨⟨a, b, c, d⟩, f⟩
        exact ⟨by linarith, b, c, d⟩
    rw [e1, finsum_mem_coe_finset]
    calc _ = _ := by
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Real.rpow_def_of_pos hu0, show Real.log u * (ρ.re - 1) = -(L * (1 - ρ.re)) by ring]
      _ ≤ _ := h
      _ ≤ _ := by
          refine add_le_add (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
            (mul_le_mul_of_nonneg_left (hcount χ) (Real.exp_pos _).le)
          rw [e2 _ (min_le_right _ _), finsum_mem_coe_finset]
  refine (Finset.sum_le_sum fun χ _ => step1 χ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hA : ∑ j ∈ Finset.range J, ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) ≤
        C₁ * Real.exp (1 / 2) * K * u ^ (-η / 2) := by
    have : ∀ j ∈ Finset.range J, ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) ≤
        C₁ * Real.exp (1 / 2) * u ^ (-η / 2) * Real.exp (-1 / 2) ^ j := by
      intro j _
      rw [← Finset.mul_sum]
      have hx0 : 0 ≤ min (η + (j + 1) / L) e := by positivity
      have hx1 := min_le_left (η + (j + 1) / L) e
      have hx2 := min_le_right (η + (j + 1) / L) e
      generalize min (η + (j + 1) / L) e = x at hx0 hx1 hx2 ⊢
      have h := H₁ q T (1 - x) hT (by linarith) (by linarith)
      refine (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans ?_
      rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos (by linarith), ← Real.exp_nat_mul,
        mul_left_comm, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
      rw [← hLdef, ← hMdef]
      have hx3 : L * x ≤ L * η + (j + 1) := by
        have := mul_le_mul_of_nonneg_left hx1 hL.le
        rwa [mul_add, mul_div_cancel₀ _ hL.ne'] at this
      nlinarith [mul_le_mul_of_nonneg_right hLM1 hx0]
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    have := hsum.sum_le_tsum (Finset.range J) (fun _ _ => by positivity)
    calc _ ≤ C₁ * Real.exp (1 / 2) * u ^ (-η / 2) * K := by gcongr
      _ = _ := by ring
  have hB : ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * e)) * (C₂ * (q * T ^ 2)) ≤
      C₂ * u ^ (-(e / 2)) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    have ht : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hE : Real.exp (2 * M) = (q * T) ^ 2 := by
      rw [show 2 * M = M + M by ring, Real.exp_add, hMdef, Real.exp_log (by linarith), sq]
    calc _ ≤ (q : ℝ) * (Real.exp (-(L * e)) * (C₂ * (q * T ^ 2))) := by gcongr
      _ = C₂ * (Real.exp (-(L * e)) * Real.exp (2 * M)) := by rw [hE]; ring
      _ ≤ _ := by
        rw [← Real.exp_add, Real.rpow_def_of_pos hu0, ← hLdef]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₂.le
        linarith
  have p1 : 0 ≤ u ^ (-η / 2) := by positivity
  have p2 : 0 ≤ u ^ (-(e / 2)) := by positivity
  have p3 : 0 ≤ C₁ * Real.exp (1 / 2) * K := by positivity
  nlinarith [mul_nonneg p3 p2, mul_nonneg hC₂.le p1]

end GlobalTheory.Lin.ZeroSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaLeW
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem eta_rows_of_pow_bounds {M k m r N L S η d W : ℝ} (hM : 8 ≤ M) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hr0 : 0 ≤ r) (hr : r ≤ M) (hN : N ≤ M) (hL1 : 1 ≤ L) (hL : L ≤ M) (hS0 : 0 ≤ S) (hS : S ≤ M ^ 3)
    (he0 : 0 ≤ η) (he : η ≤ M ^ 3) (hd0 : 0 ≤ d) (hd : 1 ≤ d * M) (hW : M ^ 10 ≤ W) :
    m * (S + η) ≤ W * L ∧ N * η ≤ d * m * W ∧ η ^ 2 * r * L ≤ d * m * W ^ 2 ∧ k * S ≤ W := by
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hW1 : 1 ≤ W := le_trans (one_le_pow₀ hM1) hW
  have h9 : M ^ 9 ≤ d * m * W := by
    calc M ^ 9 = 1 * M ^ 9 := by ring
      _ ≤ (d * M) * M ^ 9 := by gcongr
      _ = d * 1 * M ^ 10 := by ring
      _ ≤ d * m * W := by gcongr
  have h45 : 2 * M ^ 4 ≤ M ^ 10 := by
    calc 2 * M ^ 4 ≤ M * M ^ 4 := by gcongr; linarith
      _ = M ^ 5 := by ring
      _ ≤ M ^ 10 := pow_le_pow_right₀ hM1 (by norm_num)
  have h4 : 0 ≤ M ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m * (S + η) ≤ M * (M ^ 3 + M ^ 3) := by gcongr
      _ = 2 * M ^ 4 := by ring
      _ ≤ W * 1 := by linarith
      _ ≤ W * L := by gcongr
  · calc N * η ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ M ^ 9 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ _ := h9
  · calc η ^ 2 * r * L ≤ (M ^ 3) ^ 2 * M * M := by gcongr
      _ = M ^ 8 := by ring
      _ ≤ M ^ 9 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ d * m * W * 1 := by linarith
      _ ≤ d * m * W * W := by gcongr
      _ = _ := by ring
  · calc k * S ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ W := by linarith

theorem szRow_eta_le_w : SzRow (fun C D L => ((D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L) ∧ ((D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n) ∧ (L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2) ∧ ((D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n)) := by
  intro eps h0 h1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch hch => ?_⟩⟩
  obtain ⟨x1, hx1⟩ := _root_.GlobalTheory.scale_poly_comparison eps ((cD + ch + 402) * (10 : ℕ)) 1 h0 one_pos
  obtain ⟨x2, hx2⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps h0 h1
  refine ⟨max 8 (max x1 x2), fun D L he hx hV => ?_⟩
  have h8 : 8 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hxa : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxb : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ := hx2 L.sc D.R he hxb hV.ranks
  have hx1' : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hn0 : (0 : ℝ) < D.R.n := by exact_mod_cast hn1
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    simp only [Ranks.f]; push_cast; linarith
  have hW := ((hx1 L.sc he hxa).2.2.2.2.2.1 D.R.n hn1 hn3).1
  rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_mul_natCast hx0.le] at hW
  set M := L.sc.x ^ (cD + ch + 402) with hM
  have key : ∀ a : ℝ, a ≤ cD + ch + 402 → L.sc.x ^ a ≤ M := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx1' ha
  have hxM : L.sc.x ≤ M := by simpa using key 1 (by linarith)
  have hM8 : 8 ≤ M := h8.trans hxM
  have hrM : (D.R.r : ℝ) ≤ M := hr.trans (key _ (by linarith))
  have hkM : (D.R.k : ℝ) ≤ M := le_trans (by exact_mod_cast hkr) hrM
  have hceil : ∀ a : ℝ, 0 ≤ a → a ≤ cD + ch + 402 → (⌈L.sc.x ^ a⌉₊ : ℝ) ≤ 2 * M := by
    intro a ha ha'
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le a)
    have := key a ha'
    linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * (⌈L.sc.x ^ cD⌉₊ : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; simp [Delv]
  have hEta : L.etaSz = (D.R.m : ℝ) * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) := by
    rw [hV.eta_eq]; simp [h0v]
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn0]; exact hV.host.2.2.1
  have hdp : 0 < L.sc.x ^ (-L.sc.eps) := Real.rpow_pos_of_pos hx0 _
  refine eta_rows_of_pow_bounds hM8 hkM ?_ (hm.trans hxM) (Nat.cast_nonneg _) hrM
    (hN.trans (key _ (by linarith))) hL1 (hL.trans hxM) ?_ ?_ ?_ ?_ (hdp.le.trans hd) ?_ hW
  · have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  · rw [hSc]; positivity
  · rw [hSc]
    have := hceil cD hcD (by linarith)
    calc (D.R.k : ℝ) * (4 * (⌈L.sc.x ^ cD⌉₊ : ℝ)) ≤ M * (4 * (2 * M)) := by gcongr
      _ = 8 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := by gcongr
      _ = M ^ 3 := by ring
  · rw [hEta]; positivity
  · rw [hEta]
    have := hceil ch hch (by linarith)
    have hmM := hm.trans hxM
    calc (D.R.m : ℝ) * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) ≤ M * (2 * (2 * M)) := by gcongr
      _ = 4 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := by gcongr; linarith
      _ = M ^ 3 := by ring
  · have hLM : L.sc.x ^ L.sc.eps ≤ M := hL.trans hxM
    calc (1 : ℝ) = L.sc.x ^ (-L.sc.eps) * L.sc.x ^ L.sc.eps := by
          rw [← Real.rpow_add hx0]; simp
      _ ≤ L.de2 * M := by gcongr; exact hdp.le.trans hd

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowGapFunFN
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem gap_cube_bound (x t k m r : ℝ) (hx : 4 ≤ x) (ht0 : 0 ≤ t) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r)
    (ht : t ≤ x ^ 401) (hk : k ≤ x ^ 5) (hm : m ≤ x) (hr : r ≤ x ^ 5) :
    t + 2 * (k + m * (t + (r + 6) + 1)) ^ 3 + 1 ≤ x ^ 1210 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have h5 : x ^ 5 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
  have h7 : (7 : ℝ) ≤ x ^ 401 := by
    have : x ^ 2 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
    nlinarith
  have h402 : x ^ 401 ≤ x ^ 402 := pow_le_pow_right₀ hx1 (by norm_num)
  have hA : k + m * (t + (r + 6) + 1) ≤ x ^ 403 := by
    have h1 : m * (t + (r + 6) + 1) ≤ x * (3 * x ^ 401) :=
      mul_le_mul hm (by linarith) (by positivity) hx0
    have h2 : x * (3 * x ^ 401) = 3 * x ^ 402 := by ring
    have h3 : 4 * x ^ 402 ≤ x * x ^ 402 := mul_le_mul_of_nonneg_right hx (by positivity)
    have h4 : x * x ^ 402 = x ^ 403 := by ring
    linarith
  have hA3 : (k + m * (t + (r + 6) + 1)) ^ 3 ≤ (x ^ 403) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hA 3
  have e1 : (x ^ 403) ^ 3 = x ^ 1209 := by rw [← pow_mul]
  have h9 : x ^ 401 ≤ x ^ 1209 := pow_le_pow_right₀ hx1 (by norm_num)
  have h1 : (1 : ℝ) ≤ x ^ 1209 := one_le_pow₀ hx1
  have h3 : 4 * x ^ 1209 ≤ x * x ^ 1209 := mul_le_mul_of_nonneg_right hx (by positivity)
  have h4 : x * x ^ 1209 = x ^ 1210 := (pow_succ' x 1209).symm
  rw [e1] at hA3
  linarith

theorem szRow_gap_fun_fN : SzRow (fun C D L => ((D.R.t : ℝ) + 2 * ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 + 1 ≤ h0 L) ∧ ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ h0 L)) := by
  intro eps he0 he1 C hC
  have hCN : 1 ≤ C.P.Ch0N := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he0 he1
  refine ⟨0, fun cD _ => ⟨max 1210 (3 + 402 * C.P.Ch0N), fun ch hch => ⟨max x0 4, ?_⟩⟩⟩
  intro D L hε hx hV
  have hx4 : 4 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hxp : 0 < L.sc.x := by linarith
  obtain ⟨hf, hm, hr, hkr, -, -, -, -, -, -, -, -, -, ht, hN, hm1, -⟩ :=
    hx0 L.sc D.R hε (le_trans (le_max_left _ _) hx) hV.ranks
  have hmp : (0 : ℝ) < D.R.m := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hm1
  have hh : L.sc.x ^ ch ≤ h0 L := by
    have e : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0
      rw [hV.eta_eq]
      field_simp
    rw [e]
    unfold h0v
    push_cast
    have h1 := Nat.le_ceil (L.sc.x ^ ch)
    have h2 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by exact_mod_cast ht
    have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by exact_mod_cast hr
    have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
    have h1 := gap_cube_bound L.sc.x D.R.t D.R.k D.R.m D.R.r hx4 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) ht' hk' hm hr'
    have h2 : L.sc.x ^ ((1210 : ℕ) : ℝ) ≤ L.sc.x ^ ch :=
      Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (by push_cast; exact le_max_left _ _) hch)
    rw [Real.rpow_natCast] at h2
    linarith
  · have h1 : (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ (L.sc.x ^ (402 : ℝ)) ^ C.P.Ch0N :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by linarith)
    rw [← Real.rpow_mul hxp.le] at h1
    have h2 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ L.sc.x ^ (3 : ℝ) * L.sc.x ^ (402 * C.P.Ch0N) :=
      mul_le_mul hf h1 (by positivity) (by positivity)
    rw [← Real.rpow_add hxp] at h2
    have h3 : L.sc.x ^ (3 + 402 * C.P.Ch0N) ≤ L.sc.x ^ ch :=
      Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (le_max_right _ _) hch)
    linarith

end GlobalTheory.EX
end

