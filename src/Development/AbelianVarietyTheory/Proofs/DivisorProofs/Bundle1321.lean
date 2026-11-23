module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBoxBoundedValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Classical

namespace GlobalTheory.SchrodingerUniq

section Abstract

variable {G Y : Type} [AddCommGroup G] [AddCommGroup Y] (χ : Y → G → ℂ)

theorem chi_nsmul (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ) (hzero : ∀ ξ, χ 0 ξ = 1) (y : Y) (ξ : G) :
    ∀ m : ℕ, χ (m • y) ξ = χ y ξ ^ m
  | 0 => by rw [zero_nsmul, hzero, pow_zero]
  | m + 1 => by rw [succ_nsmul, hadd, chi_nsmul hadd hzero y ξ m, pow_succ]

theorem norm_avg_le_one (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ = 1) {M : ℕ} (hM : 0 < M) :
    ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, f m‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  calc (M : ℝ)⁻¹ * ‖∑ m ∈ Finset.range M, f m‖ ≤ (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, ‖f m‖ := by
        gcongr; exact norm_sum_le _ _
    _ = 1 := by simp only [hf, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; field_simp

theorem norm_avg_pow_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {M : ℕ} (hM : 0 < M) :
    ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, z ^ m‖ ≤ 2 / (M * ‖z - 1‖) := by
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ‖z ^ M - 1‖ ≤ 2 := by
    calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  rw [geom_sum_eq hz1, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  calc (M : ℝ)⁻¹ * (‖z ^ M - 1‖ / ‖z - 1‖) ≤ (M : ℝ)⁻¹ * (2 / ‖z - 1‖) := by gcongr
    _ = 2 / (M * ‖z - 1‖) := by field_simp

variable (c : G → ℂ)

def Good (a : G → ℂ) : Prop := (∀ ξ, ‖a ξ‖ ≤ 1) ∧ a 0 = 1 ∧ ∀ y, ∑' ξ, c ξ * χ y ξ * a ξ = 0

variable {χ c}

theorem good_avg (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (h0 : ∀ y, χ y 0 = 1) (hc : Summable fun ξ => ‖c ξ‖) {a : G → ℂ} (ha : Good χ c a) (y' : Y) {M : ℕ}
    (hM : 0 < M) : Good χ c (fun ξ => a ξ * ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ)) := by
  refine ⟨fun ξ => ?_, ?_, fun y => ?_⟩
  · rw [norm_mul]
    calc ‖a ξ‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ‖ ≤ 1 * 1 :=
          mul_le_mul (ha.1 ξ) (norm_avg_le_one _ (fun m => hnorm _ _) hM) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp only [ha.2.1, h0, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast hM.ne')
  · have hs : ∀ m ∈ Finset.range M, Summable fun ξ => c ξ * χ y ξ * a ξ * χ (m • y') ξ := fun m _ =>
      Summable.of_norm_bounded hc fun ξ => by
        rw [norm_mul, norm_mul, norm_mul, hnorm, hnorm, mul_one, mul_one]
        exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 ξ)
    calc ∑' ξ, c ξ * χ y ξ * (a ξ * ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ))
        = ∑' ξ, (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, c ξ * χ y ξ * a ξ * χ (m • y') ξ := by
          congr 1; funext ξ
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ = (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, ∑' ξ, c ξ * χ y ξ * a ξ * χ (m • y') ξ := by
          rw [tsum_mul_left, Summable.tsum_finsetSum hs]
      _ = 0 := by
          rw [Finset.sum_eq_zero fun m _ => ?_, mul_zero]
          rw [← ha.2.2 (y + m • y')]
          congr 1; funext ξ; rw [hadd]; ring

theorem exists_good_small (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (hzero : ∀ ξ, χ 0 ξ = 1) (h0 : ∀ y, χ y 0 = 1) (hsep : ∀ ξ, ξ ≠ 0 → ∃ y, χ y ξ ≠ 1)
    (hc : Summable fun ξ => ‖c ξ‖) (h1 : Good χ c fun _ => 1) :
    ∀ (T : Finset G), (0 : G) ∉ T → ∀ ε > 0, ∃ a, Good χ c a ∧ ∀ ξ ∈ T, ‖a ξ‖ ≤ ε := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _ ε _; exact ⟨fun _ => 1, h1, by simp⟩
  | insert ξ T hξT ih =>
    intro h0T ε hε
    have hξ0 : ξ ≠ 0 := fun e => h0T (by rw [← e]; exact Finset.mem_insert_self ξ T)
    obtain ⟨a, ha, haT⟩ := ih (fun e => h0T (Finset.mem_insert_of_mem e)) ε hε
    obtain ⟨y', hy'⟩ := hsep ξ hξ0
    have hd : 0 < ‖χ y' ξ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hy')
    obtain ⟨M, hM⟩ := exists_nat_gt (2 / (ε * ‖χ y' ξ - 1‖))
    have hM0 : 0 < M := by
      have : (0 : ℝ) < M := lt_trans (by positivity) hM
      exact_mod_cast this
    refine ⟨_, good_avg hnorm hadd h0 hc ha y' hM0, fun η hη => ?_⟩
    rw [norm_mul]
    rcases Finset.mem_insert.1 hη with rfl | hη
    · simp_rw [chi_nsmul χ hadd hzero]
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
      calc ‖a η‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ y' η ^ m‖ ≤ 1 * (2 / (M * ‖χ y' η - 1‖)) :=
            mul_le_mul (ha.1 _) (norm_avg_pow_le (hnorm _ _) hy' hM0) (norm_nonneg _) zero_le_one
        _ ≤ ε := by
            rw [one_mul, div_le_iff₀ (by positivity)]
            rw [div_lt_iff₀ (by positivity)] at hM
            have : ε * (M * ‖χ y' η - 1‖) = M * (ε * ‖χ y' η - 1‖) := by ring
            linarith
    · calc ‖a η‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') η‖ ≤ ε * 1 :=
            mul_le_mul (haT η hη) (norm_avg_le_one _ (fun m => hnorm _ _) hM0) (norm_nonneg _) hε.le
        _ = ε := mul_one ε

theorem coeff_zero_eq_zero (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (hzero : ∀ ξ, χ 0 ξ = 1) (h0 : ∀ y, χ y 0 = 1) (hsep : ∀ ξ, ξ ≠ 0 → ∃ y, χ y ξ ≠ 1)
    (hc : Summable fun ξ => ‖c ξ‖) (h : ∀ y, ∑' ξ, c ξ * χ y ξ = 0) : c 0 = 0 := by
  have h1 : Good χ c fun _ => 1 := ⟨fun _ => by simp, rfl, fun y => by simpa using h y⟩
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  set S := ∑' ξ, ‖c ξ‖
  have hS : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1
    ((tendsto_tsum_compl_atTop_zero fun ξ => ‖c ξ‖).eventually (gt_mem_nhds (half_pos hδ)))
  set s := insert (0 : G) s₀
  have htail := hs₀ s (Finset.subset_insert _ _)
  have hε : 0 < δ / (2 * (S + 1)) := by positivity
  obtain ⟨a, ha, haT⟩ := exists_good_small hnorm hadd hzero h0 hsep hc h1 (s.erase 0)
    (Finset.notMem_erase 0 s) _ hε
  have hsumm : Summable fun ξ => c ξ * a ξ := Summable.of_norm_bounded hc fun ξ => by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 ξ)
  have hsum : ∑' ξ, c ξ * a ξ = 0 := by simpa [hzero] using ha.2.2 0
  have hsplit := hsumm.sum_add_tsum_compl (s := s)
  rw [hsum, ← Finset.add_sum_erase s _ (Finset.mem_insert_self 0 s₀), ha.2.1, mul_one] at hsplit
  have hc0 : c 0 = -(∑ x ∈ s.erase 0, c x * a x + ∑' x : ↑((s : Set G)ᶜ), c x * a x) := by
    linear_combination hsplit
  have hA : ‖∑ x ∈ s.erase 0, c x * a x‖ ≤ δ / (2 * (S + 1)) * S := by
    calc ‖∑ x ∈ s.erase 0, c x * a x‖ ≤ ∑ x ∈ s.erase 0, ‖c x * a x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ s.erase 0, δ / (2 * (S + 1)) * ‖c x‖ := Finset.sum_le_sum fun x hx => by
          rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (haT x hx) (norm_nonneg _)
      _ = δ / (2 * (S + 1)) * ∑ x ∈ s.erase 0, ‖c x‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ δ / (2 * (S + 1)) * S := by
          gcongr; exact hc.sum_le_tsum _ fun _ _ => norm_nonneg _
  have hB : ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ ≤ ∑' x : {x // x ∉ s}, ‖c x‖ := by
    calc ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ ≤ ∑' x : ↑((s : Set G)ᶜ), ‖c x * a x‖ :=
          norm_tsum_le_tsum_norm ((hsumm.subtype _).norm)
      _ ≤ ∑' x : ↑((s : Set G)ᶜ), ‖c x‖ := Summable.tsum_le_tsum
          (fun x => by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 x))
          (hsumm.subtype _).norm (hc.subtype _)
      _ = ∑' x : {x // x ∉ s}, ‖c x‖ := rfl
  have hSS : δ / (2 * (S + 1)) * S ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  rw [hc0, norm_neg, zero_add]
  calc _ ≤ ‖∑ x ∈ s.erase 0, c x * a x‖ + ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ := norm_add_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (hA.trans hSS) (hB.trans htail.le)
    _ = δ := add_halves δ

end Abstract

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w : (κ → AF D.host.F) × (κ → AF D.host.F), GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ) =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ')) → φ = φ' := by
  intro D ψ hψ κ _ φ hφ φ' hφ' h
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨a₀, ha₀⟩ := hψ.1.2.2.2
  let ι : (κ → D.host.F) → (κ → AF D.host.F) := fun ξ i => algebraMap D.host.F (AF D.host.F) (ξ i)
  have hι0 : ι 0 = 0 := by funext i; simp [ι]
  funext x
  rw [← sub_eq_zero]
  have hΦ : (fun z => (φ - φ') (z + x)) ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    GlobalTheory.SchwartzTranslate.schA_translate D.host.F x (sub_mem hφ hφ')
  have hc : Summable fun ξ => ‖(φ - φ') (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F hΦ using 1
  have sφ : Summable fun ξ => ‖φ (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F x hφ) using 1
  have sφ' : Summable fun ξ => ‖φ' (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F x hφ') using 1
  have key := coeff_zero_eq_zero (χ := fun (y : κ → AF D.host.F) (ξ : κ → D.host.F) => ψ (ι ξ ⬝ᵥ y))
    (c := fun ξ => (φ - φ') (ι ξ + x)) (fun y ξ => hn _)
    (fun y y' ξ => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
    (fun ξ => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
    (fun y => by simp only [hι0, zero_dotProduct, AddChar.map_zero_eq_one])
    (fun ξ hξ => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have hi' : ξ i ≠ 0 := hi
      refine ⟨Pi.single i (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀), ?_⟩
      show ψ (ι ξ ⬝ᵥ Pi.single i (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [dotProduct_single]
      show ψ (algebraMap D.host.F (AF D.host.F) (ξ i) * (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
      exact ha₀)
    hc (fun y => ?_)
  · simpa [hι0] using key
  · have h' := h (x, y)
    simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, AddChar.map_add_eq_mul] at h'
    set b := ψ (⅟(2 : AF D.host.F) * (x ⬝ᵥ y))
    have hb : b ≠ 0 := by
      intro e
      have h1 : ‖b‖ = 1 := hn _
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have s1 : Summable fun ξ : κ → D.host.F => ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) :=
      Summable.of_norm_bounded sφ fun ξ => by rw [norm_mul, norm_mul, hn, hn, one_mul, one_mul]
    have s2 : Summable fun ξ : κ → D.host.F => ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x) :=
      Summable.of_norm_bounded sφ' fun ξ => by rw [norm_mul, norm_mul, hn, hn, one_mul, one_mul]
    have e : ∑' ξ : κ → D.host.F, (ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) - ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x)) = 0 := by
      rw [s1.tsum_sub s2, sub_eq_zero]; exact h'
    have e2 : ∑' ξ : κ → D.host.F, (φ - φ') (ι ξ + x) * ψ (ι ξ ⬝ᵥ y) =
        b⁻¹ * ∑' ξ : κ → D.host.F, (ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) - ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x)) := by
      rw [← tsum_mul_left]; congr 1; funext ξ; simp only [Pi.sub_apply]; field_simp
    rw [e2, e, mul_zero]

end GlobalTheory.SchrodingerUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ArchDecay

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def heisD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → AF F) : ℂ :=
  deriv (fun t : ℝ => M.heisLine ψ u t f x) 0

def liftI (M : Model σ X W)
    (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  M.co.e.symm (fun i => infAd F (ζ.1 i), fun i => infAd F (ζ.2 i))

def movI (M : Model σ X W) (p : UA σ X.J × UA σ W.J)
    (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  (arch F (M.co.e (actAB (cA σ) p⁻¹ (liftI M ζ))).1, arch F (M.co.e (actAB (cA σ) p⁻¹ (liftI M ζ))).2)

def wordH (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (zs : List ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)))
    (f : (Fin n × Fin d → AF F) → ℂ) : (Fin n × Fin d → AF F) → ℂ :=
  zs.foldr (fun ζ g => heisD M ψ (liftI M ζ) g) f

end Model

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def dR (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)
    (ζ : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  dD F ζ.1 f + c • mM F (T ζ.2) f

def wordR (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)
    (zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  zs.foldr (dR F T c) f

theorem dD_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F)
    (c : ℂ) (f : (κ → AF F) → ℂ) : dD F v (c • f) = c • dD F v f := by
  funext x
  simp only [dD, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_mul_field']

theorem mM_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (c : ℂ) (f : (κ → AF F) → ℂ) : mM F l (c • f) = c • mM F l f := by
  funext x
  simp only [mM, Pi.smul_apply, smul_eq_mul]
  ring

theorem app_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (o : Op F κ) (c : ℂ)
    (f : (κ → AF F) → ℂ) : app F o (c • f) = c • app F o f := by
  cases o with
  | inl v => exact dD_smul v c f
  | inr l => exact mM_smul l c f

theorem dD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : (κ → AF F) → ℂ) :
    dD F 0 f = 0 := by
  funext x
  have e : ∀ t : ℝ, (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i)) = x := by
    intro t
    funext i
    have h0 : infAd F (0 : mixedEmbedding.mixedSpace F) = 0 := by unfold infAd; rw [map_zero, map_zero]
    show x i + infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i) = x i
    rw [Pi.zero_apply, smul_zero, h0, add_zero]
  show deriv (fun t : ℝ => f (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i))) 0 = 0
  rw [show (fun t : ℝ => f (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i))) = fun _ => f x from
    funext fun t => by rw [e t]]
  exact deriv_const 0 (f x)

theorem mM_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : (κ → AF F) → ℂ) :
    mM F 0 f = 0 := by
  funext x
  simp [mM]

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundUnitaryAction
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.WeilDirBound

open GlobalTheory.AdelicU

theorem norm_entry_le_opNorm {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (i k : m) :
    ‖A i k‖ ≤ (opNorm A : ℝ) := by
  have h1 : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1) =
      WithLp.toLp 2 (A *ᵥ Pi.single k 1) := Matrix.toEuclideanCLM_toLp A _
  have h2 : (A *ᵥ Pi.single k (1 : ℂ)) i = A i k := by simp
  calc ‖A i k‖ = ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)).ofLp i‖ := by
        rw [h1, ← h2]
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A‖ * ‖EuclideanSpace.single k (1 : ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = (opNorm A : ℝ) := by simp [opNorm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_entry_le_heightGL {m : Type} [Fintype m] [DecidableEq m] (g : GL m (AF F ⊗[F] E))
    (w : InfinitePlace F) (τ : EmbOver E w) (i k : m) :
    ‖piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k)‖ ≤ (heightGL F g : ℝ) := by
  have e : piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k) =
      (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ)) i k := rfl
  rw [e]
  refine (norm_entry_le_opNorm _ i k).trans ?_
  have h1 : opNorm (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ))
      ≤ heightGL F g := by
    refine ((normInf_le_iff F w).1 le_rfl τ).trans ((le_htOf _ _).trans ?_)
    refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => one_le_htOf _ _))
    exact Finset.single_le_prod' (f := fun w => htInf F w (Formalism.UG.bc (compInf F E w) g))
      (fun _ _ => one_le_htOf _ _) (Finset.mem_univ w)
  exact_mod_cast h1

end GlobalTheory.WeilDirBound

end

namespace GlobalTheory.WeilDirBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_actAB_le (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (p : UA σ J × UA σ J')
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (x k l)‖ ≤ B) :
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j,
      ‖piInf τ (actAB (cA σ) p x i j)‖ ≤ n * d * ((ht p.1 : ℝ) * ht p.2) * B := by
  intro w τ i j
  set g : GL (Fin n) (AF F ⊗[F] E) := (p.1 : GL (Fin n) (AF F ⊗[F] E)) with hg
  set h : GL (Fin d) (AF F ⊗[F] E) := (p.2 : GL (Fin d) (AF F ⊗[F] E)) with hh
  have hg1 : (ht p.1 : ℝ) = heightGL F g := rfl
  have hh1 : (ht p.2 : ℝ) = heightGL F h := rfl
  have e : actAB (cA σ) p x i j = ∑ l, ∑ k,
      (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l := by
    simp only [actAB, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rfl
  have hG := fun k => norm_piInf_entry_le_heightGL g w τ i k
  have hH := fun l => norm_piInf_entry_le_heightGL h w τ j l
  have hG0 : (0 : ℝ) ≤ heightGL F g := NNReal.coe_nonneg _
  have hH0 : (0 : ℝ) ≤ heightGL F h := NNReal.coe_nonneg _
  rw [e, hg1, hh1]
  calc ‖piInf τ (∑ l, ∑ k, (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l)‖
      ≤ ∑ l : Fin d, ∑ k : Fin n, ((heightGL F g : ℝ) * heightGL F h * B) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [map_mul, map_mul, norm_mul, norm_mul]
        calc ‖piInf τ ((g : Matrix (Fin n) (Fin n) _) i k)‖ * ‖piInf τ (x k l)‖ *
              ‖piInf τ ((h : Matrix (Fin d) (Fin d) _) j l)‖
            ≤ (heightGL F g : ℝ) * B * heightGL F h :=
              mul_le_mul (mul_le_mul (hG k) (hx w τ k l) (norm_nonneg _) hG0) (hH l) (norm_nonneg _)
                (mul_nonneg hG0 hB)
          _ = (heightGL F g : ℝ) * heightGL F h * B := by ring
    _ = n * d * ((heightGL F g : ℝ) * heightGL F h) * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.WeilDirBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariant
section
open ValuativeRel Matrix

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hν1 i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0
  set g : Matrix A D k → ℂ := boxFn ϖ C (fun _ => m) with hg
  set g' : Matrix A D k → ℂ := boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) with hg'
  set lam : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) * apow ϖ (-(Fintype.card D : ℂ) / 2) with hlam
  set N : ℕ := Fintype.card (Fin r → GlobalTheory.SplitFlip.Res k 1) with hN
  let F : (Fin r → GlobalTheory.SplitFlip.Res k 1) → Matrix A D k → ℂ := fun b => boxFn ϖ (Matrix.updateRow C i₀
    ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m)

  have hz := _root_.GlobalTheory.RankCoinv.omA_diag_boxFn_succ k A D ϖ ν β i₀ C hC0 m (m - 1)
  have hupd : Function.update (fun _ : A => m) i₀ m = fun _ => m := Function.update_eq_self _ _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hupd] at hz
  have h3 : lam • g - g' ∈ twistSpan ν β := by
    rw [hlam, hg, ← hz]; exact sub_mem_twistSpan ν β _ (boxFn_mem_SB _ _ _)

  have h1 : g' - ∑ b, F b ∈ lowRank (r + 1) :=
    _root_.GlobalTheory.CountTranslates.boxFn_sub_sum_mem_lowRank k A D ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0

  have hv1 : valuation k (ϖ : k) ≤ 1 := by rw [hϖ]; exact (uniformizer_lt_one (R := k)).le
  have h2 : ∀ b, F b - g ∈ twistSpan ν β := by
    intro b
    have ht : ∀ l, valuation k ((ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
      intro l
      have hout : valuation k ((Quotient.out (b l) : 𝒪[k]) : k) ≤ 1 := (Quotient.out (b l)).2
      rw [map_mul, map_pow, Units.val_pow_eq_pow_val, map_pow]
      exact (mul_le_of_le_one_right' hout).trans (pow_le_pow_right_of_le_one' hv1 (by omega))
    have hu := _root_.GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan k A D ϖ ν β i₀ r c m C H _ hH0 hHv ht
    have hrow : C i₀ = 0 := funext hC0
    rw [hrow, zero_add] at hu
    exact hu

  have key : (lam - (N : ℂ)) • g ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    have e : (lam - (N : ℂ)) • g = (g' - ∑ b, F b) + ∑ b, (F b - g) + (lam • g - g') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, sub_smul, Nat.cast_smul_eq_nsmul ℂ]
      abel
    rw [e]
    exact add_mem (add_mem (Submodule.mem_sup_left h1)
      (Submodule.mem_sup_right (Submodule.sum_mem _ fun b _ => h2 b))) (Submodule.mem_sup_right h3)

  have hne : lam - (N : ℂ) ≠ 0 := by
    intro h
    have hl : lam = N := sub_eq_zero.1 h
    set a : ℝ := nabs k ϖ ^ (-(Fintype.card D : ℝ) / 2) with ha_def
    have hapos : 0 < a := Real.rpow_pos_of_pos (nabs_pos ϖ) _
    have ha : apow ϖ (-(Fintype.card D : ℂ) / 2) = (a : ℂ) := by
      rw [apow, ha_def, Complex.ofReal_cpow (nabs_pos ϖ).le]
      push_cast; ring_nf
    set u : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) with hu_def
    have hua : u * a = N := by rw [← ha]; exact hl
    have hu : u = ((N / a : ℝ) : ℂ) := by
      have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hapos.ne'
      rw [Complex.ofReal_div, Complex.ofReal_natCast, ← hua, mul_div_cancel_right₀ _ ha0]
    have hnorm : ‖u‖ = 1 := by
      rw [hu_def, Units.val_inv_eq_inv_val, norm_inv, hν, inv_one]
    rw [hu, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hapos.le)] at hnorm
    have hu1 : u = 1 := by rw [hu, hnorm]; simp
    apply hν1
    have : (ν ϖ)⁻¹ = 1 := Units.ext (by simpa [hu_def] using hu1)
    exact inv_eq_one.1 this
  exact (Submodule.smul_mem_iff _ hne).1 key
end

