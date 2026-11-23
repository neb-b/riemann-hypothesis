module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import Development.WeilBound.CoreStatements.FlagImmersions.MapProdLinear

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.AltCMul
section
noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def expo (a : Ψ → Fin N → ℕ) (σ : Ψ → Equiv.Perm (Fin N)) : (Ψ × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => a x.1 (σ x.1 x.2))

def alt (a : Ψ → Fin N → ℕ) (G : RP Ψ N) : ℝ :=
  ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * G.coeff (expo a σ)

def rho : Ψ → Fin N → ℕ := fun _ c => N - 1 - (c : ℕ)

def bump (τ : Ψ) (c : Fin N) (k : ℕ) : Ψ → Fin N → ℕ :=
  fun τ' c' => N - 1 - (c' : ℕ) + if τ' = τ ∧ c' = c then k else 0

def lam (τ : Ψ) (k : ℕ) (G : RP Ψ N) : ℝ := ∑ c, alt (bump τ c k) G

def Maj (f : Polynomial ℝ) (c A : ℝ) : Prop := ∀ s : ℕ, |f.coeff s| ≤ c * A ^ s / (s.factorial : ℝ)

def gdet (e : Fin N → ℕ) (v : Fin N → Polynomial ℝ) : Polynomial ℝ :=
  Matrix.det (Matrix.of fun c b => Polynomial.C (((e c).factorial : ℝ)⁻¹) * v b ^ e c)

theorem degFl_eq (G : RP Ψ N) : degFl G = (-1) ^ dimFl Ψ N * alt rho G := rfl

theorem alt_add (a : Ψ → Fin N → ℕ) (F G : RP Ψ N) : alt a (F + G) = alt a F + alt a G := by
  simp [alt, mul_add, Finset.sum_add_distrib]

theorem alt_C_mul (a : Ψ → Fin N → ℕ) (r : ℝ) (G : RP Ψ N) : alt a (C r * G) = r * alt a G := by
  simp only [alt, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem alt_sum {ι : Type*} (a : Ψ → Fin N → ℕ) (s : Finset ι) (F : ι → RP Ψ N) :
    alt a (∑ i ∈ s, F i) = ∑ i ∈ s, alt a (F i) := by
  simp only [alt, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem lam_add (τ : Ψ) (k : ℕ) (F G : RP Ψ N) : lam τ k (F + G) = lam τ k F + lam τ k G := by
  simp [lam, alt_add, Finset.sum_add_distrib]

theorem lam_sum {ι : Type*} (τ : Ψ) (k : ℕ) (s : Finset ι) (F : ι → RP Ψ N) :
    lam τ k (∑ i ∈ s, F i) = ∑ i ∈ s, lam τ k (F i) := by
  simp only [lam, alt_sum]
  exact Finset.sum_comm

end RootFieldNumerics.M5
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.CombLineSmoothConjInvariant
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem contDiffOn_zpow_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (hA : IsSmoothHerm A) (n : ℤ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h z ^ n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  unfold IsSmoothHerm at hA
  have hne : ∀ z ∈ {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, A.h z ≠ 0 :=
    fun z hz => (A.pos z hz).ne'
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using hA.pow m
  · simp only [zpow_neg, zpow_natCast]
    exact (hA.pow m).inv (fun z hz => pow_ne_zero _ (hne z hz))

end Ii

open Ii in
theorem combLine_smooth_conj_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  intro K _ ι _ J _ ℓ n
  refine ⟨fun h => ?_, fun h z => ?_, ?_⟩
  · exact contDiffOn_prod fun j _ => contDiffOn_zpow_h (ℓ j) (h j) (n j)
  · exact Finset.prod_congr rfl fun j _ => by rw [h j z]
  · exact contDiffOn_const

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.ContinuousBoundWallExtension
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem exists_rat_near_le (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : ∃ q : ℚ, |(q : ℝ)| ≤ |x| ∧ |(q : ℝ) - x| ≤ δ := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x < min (x + δ) 0 from lt_min (by linarith) hx)
    have m1 := min_le_left (x + δ) 0
    have m2 := min_le_right (x + δ) 0
    refine ⟨q, ?_, ?_⟩
    · rw [abs_of_neg hx, abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_le]
      constructor <;> linarith
  · exact ⟨0, by simp [hx], by simp [hx, hδ.le]⟩
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show max (x - δ) 0 < x from max_lt (by linarith) hx)
    have m1 := le_max_left (x - δ) 0
    have m2 := le_max_right (x - δ) 0
    refine ⟨q, ?_, ?_⟩
    · rw [abs_of_pos hx, abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_le]
      constructor <;> linarith

theorem continuous_bound_wall_extension : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b := by
  intro Ψ _ _ N j c₀ b τ₀ Φ hj hjN hc hΦ hrat lam hlam
  have hex : ∀ n : ℕ, ∀ x : ℝ, ∃ q : ℚ, |(q:ℝ)| ≤ |x| ∧ |(q:ℝ) - x| ≤ c₀ / 4 * (1 / ((n:ℝ) + 1)) :=
    fun n x => exists_rat_near_le _ (by positivity) x
  choose F hF1 hF2 using hex
  let A : ℕ → Wt Ψ N := fun n τ i => (F n (lam τ i) : ℝ)
  have hδ : ∀ n : ℕ, c₀ / 4 * (1 / ((n:ℝ) + 1)) ≤ c₀ / 4 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    exact mul_le_of_le_one_right (by positivity) h1
  have hent : ∀ n τ k, k < N → ent (A n) τ k = (F n (ent lam τ k) : ℝ) := by
    intro n τ k hk
    simp [ent, hk, A]
  have hclose : ∀ n τ k, k < N → |ent (A n) τ k - ent lam τ k| ≤ c₀ / 4 := by
    intro n τ k hk
    rw [hent n τ k hk]
    exact (hF2 n _).trans (hδ n)
  have hin : ∀ n, InWall j τ₀ (c₀ / 2) (A n) := by
    intro n
    obtain ⟨hn, hg0, hgτ, hcg⟩ := hlam
    have hj1 : j - 1 < N := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun τ =>
        (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      have h1 : ‖lam τ i‖ ≤ 1 / 2 := (norm_le_pi_norm (lam τ) i).trans ((norm_le_pi_norm lam τ).trans hn)
      simp only [Real.norm_eq_abs, A] at h1 ⊢
      exact (hF1 n _).trans h1
    · simp only [gap] at hg0 ⊢
      rw [hent n τ₀ _ hj1, hent n τ₀ _ hjN, show ent lam τ₀ (j - 1) = ent lam τ₀ j by linarith]
      ring
    · intro τ hτ
      have h := hgτ τ hτ
      simp only [gap] at h ⊢
      have a1 := abs_le.1 (hclose n τ _ hj1)
      have a2 := abs_le.1 (hclose n τ _ hjN)
      linarith [a1.1, a1.2, a2.1, a2.2]
    · intro τ i hi hij
      have h := hcg τ i hi hij
      have a1 := abs_le.1 (hclose n τ i (by omega))
      have a2 := abs_le.1 (hclose n τ (i + 1) hi)
      linarith [a1.1, a1.2, a2.1, a2.2]
  have hAr : ∀ n, IsRatWt (A n) := fun n τ i => ⟨F n (lam τ i), rfl⟩
  have htend : Tendsto A atTop (𝓝 lam) := by
    rw [tendsto_pi_nhds]
    intro τ
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => c₀ / 4 * (1 / ((n:ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (c₀ / 4)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    simp only [A, Real.norm_eq_abs]
    exact hF2 n _
  have hΦt : Tendsto (fun n => |Φ (A n)|) atTop (𝓝 |Φ lam|) :=
    (continuous_abs.tendsto _).comp ((hΦ.tendsto lam).comp htend)
  exact le_of_tendsto' hΦt fun n => hrat _ (hAr n) (hin n)

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.ExistsIntegerCoefficientsRational
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem exists_clear_denominators_bis {J : Type} [Fintype J] (c : J → ℚ) :
    ∃ (q : ℕ) (n : J → ℤ), 0 < q ∧ ∀ j, (n j : ℚ) = q * c j := by
  classical
  refine ⟨∏ i, (c i).den, fun j => (c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ), ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => (c i).den_pos)
  · intro j
    obtain ⟨k, hk⟩ : (c j).den ∣ ∏ i, (c i).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show (((c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ) : ℤ) : ℚ) = ((∏ i, (c i).den : ℕ) : ℚ) * c j
    rw [hk, Nat.mul_div_cancel_left _ (c j).den_pos]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

end RootFieldNumerics

theorem RootFieldNumerics.exists_integer_coefficients_rational : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j := by
  intro Ψ _ N M lam s hlam
  classical
  choose f hf using hlam
  let c : Option (Ψ × Fin N) → ℚ := fun j => match j with
    | some r => -f r.1 r.2
    | none => s / M.kA
  obtain ⟨q, n, hq, hn⟩ := RootFieldNumerics.exists_clear_denominators_bis c
  refine ⟨q, n, hq, fun j => ?_⟩
  have h : ((n j : ℚ) : ℝ) = ((q * c j : ℚ) : ℝ) := by rw [hn j]
  push_cast at h
  rw [h]
  congr 1
  cases j with
  | none => simp [c, RootModel.coef]
  | some r => simp [c, RootModel.coef, hf]
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.FlagDegLeGap
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem prod_le_mul_two_pow_card {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) (x₀ : ι) (c : ℝ) (hc : f x₀ = c) :
    ∏ x, f x ≤ c * 2 ^ Fintype.card ι := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ x₀), hc]
  refine mul_le_mul_of_nonneg_left ?_ (hc ▸ h0 x₀)
  calc ∏ x ∈ Finset.univ.erase x₀, f x ≤ ∏ x ∈ Finset.univ.erase x₀, (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun x _ => h0 x) (fun x _ => h2 x)
    _ = 2 ^ (Finset.univ.erase x₀).card := Finset.prod_const 2
    _ ≤ 2 ^ Fintype.card ι := pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

theorem flagDeg_le_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  intro Ψ _ _ N j hj hjN
  refine ⟨((GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N).factorial : ℝ) * 2 ^ Fintype.card (Ψ × Fin N × Fin N),
    by positivity, ?_⟩
  intro lam τ₀ hlam hdom
  have hj1 : j - 1 < N := by omega
  have hbound : ∀ τ i, |lam τ i| ≤ 1 := by
    intro τ i
    have h1 := norm_le_pi_norm (show Ψ → Fin N → ℝ from lam) τ
    have h2 := norm_le_pi_norm (lam τ) i
    rw [Real.norm_eq_abs] at h2
    have h3 : ‖(show Ψ → Fin N → ℝ from lam)‖ ≤ 1 := hlam
    linarith
  have hfac : ∀ τ (i k : Fin N),
      0 ≤ (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) ∧
        (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) ≤ 2 := by
    intro τ i k
    split_ifs with hik
    · have hik' : (i : ℕ) < (k : ℕ) := hik
      have hd : ((i : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hik'
      have hmono := hdom τ i k hik.le
      have hi := abs_le.mp (hbound τ i)
      have hk := abs_le.mp (hbound τ k)
      constructor
      · apply div_nonneg <;> linarith
      · rw [div_le_iff₀ (by linarith)]
        linarith
    · norm_num
  have hgap : GlobalTheory.CompanionTheory.Ar.Top.gap j lam τ₀ = lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩ := by
    unfold GlobalTheory.CompanionTheory.Ar.Top.gap GlobalTheory.CompanionTheory.Ar.Top.ent
    rw [dite_eq_left hj1, dite_eq_left hjN]
  have hx0 : (if (⟨j - 1, hj1⟩ : Fin N) < ⟨j, hjN⟩ then
      (lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩) /
        ((((⟨j, hjN⟩ : Fin N) : ℕ) : ℝ) - (((⟨j - 1, hj1⟩ : Fin N) : ℕ) : ℝ)) else 1) =
      lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩ := by
    have hlt : (⟨j - 1, hj1⟩ : Fin N) < ⟨j, hjN⟩ := by
      rw [Fin.lt_def]
      show j - 1 < j
      omega
    rw [if_pos hlt]
    have hden : (((⟨j, hjN⟩ : Fin N) : ℕ) : ℝ) - (((⟨j - 1, hj1⟩ : Fin N) : ℕ) : ℝ) = 1 := by
      show ((j : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ) = 1
      rw [Nat.cast_sub hj, Nat.cast_one]
      ring
    rw [hden, div_one]
  have key := prod_le_mul_two_pow_card
    (fun x : Ψ × Fin N × Fin N => if x.2.1 < x.2.2 then
      (lam x.1 x.2.1 - lam x.1 x.2.2) / (((x.2.2 : ℕ) : ℝ) - ((x.2.1 : ℕ) : ℝ)) else 1)
    (fun x => (hfac x.1 x.2.1 x.2.2).1) (fun x => (hfac x.1 x.2.1 x.2.2).2)
    (τ₀, ⟨j - 1, hj1⟩, ⟨j, hjN⟩) _ hx0
  simp only [Fintype.prod_prod_type] at key
  obtain ⟨hdeg, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.flagDeg_eq_weyl Ψ N lam
  rw [hdeg, hgap]
  calc _ ≤ ((GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N).factorial : ℝ) *
        ((lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩) * 2 ^ Fintype.card (Ψ × Fin N × Fin N)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.IntersectionConstantMetricLine
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ptsIntegral_const_mul (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun z => c * g z) = c * ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    refine congrArg _ (funext fun y => ?_)
    rw [← smul_eq_mul, smul_finsum]
    refine finsum_congr (fun w => ?_)
    rw [smul_finsum]
    refine finsum_congr (fun hw => ?_)
    unfold sheetDensity
    split_ifs <;> simp [mul_assoc]
  · simp

theorem ptsIntegral_const (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  simpa using ptsIntegral_const_mul P φ (fun _ => (1 : ℝ)) c

theorem smooth_constLine (c : ℝ) :
    IsSmoothHerm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) := by
  unfold IsSmoothHerm HermLine.ofWeight
  exact contDiffOn_const

theorem intersection_constant_metric_line : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (c : ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → II K ι P (e + 1) (Fin.snoc L (HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl))) = -c * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  intro II hII K _ ι _ P e L c hP hL
  have hA : IsSmoothHerm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) :=
    smooth_constLine c
  have hprime : P.IsPrime := hP.2.1.1
  have h1 : (1 : MRing ι) ∉ P := fun h => hprime.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hhom : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
    intro m hm k
    rw [MvPolynomial.support_one] at hm
    rw [Finset.mem_singleton.1 hm]
    simp
  rw [(hII K ι).2.2 P e L _ 1 (fun _ => 0) hP hL hA (fun k => by simp [HermLine.ofWeight]) hhom h1]
  have hempty : divSupp P (1 : MRing ι) = ∅ := by
    ext W
    simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hW
    rw [Ideal.span_singleton_one, sup_top_eq] at hW
    exact (hW.1.1.ne_top (top_le_iff.1 hW.1.2)).elim
  unfold recR arInt
  simp only [hempty, Set.mem_empty_iff_false, finsum_false, finsum_zero, zero_sub]
  have hln : logNorm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) (1 : MRing ι) = fun _ => c := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_exp]
  rw [hln, ptsIntegral_const]
  ring

end RootFieldNumerics
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMonomialLines
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem exists_perm_of_map_eq {α J : Type} [Fintype α] (f g : α → J)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ σ : Equiv.Perm α, ∀ a, g (σ a) = f a := by
  classical
  have hc : ∀ j, Fintype.card {a // f a = j} = Fintype.card {a // g a = j} := by
    intro j
    have := congrArg (Multiset.count j) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert this using 1 <;> simp [Finset.card_def, Finset.filter_val, eq_comm]
  let e : ∀ j, {a // f a = j} ≃ {a // g a = j} := fun j => Fintype.equivOfCardEq (hc j)
  let σ : Equiv.Perm α :=
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e)).trans (Equiv.sigmaFiberEquiv g)
  refine ⟨σ, fun a => ?_⟩
  exact (e (f a) ⟨a, rfl⟩).2

theorem toMultiset_sum_single {d : ℕ} {J : Type} (w : Fin d → J) :
    Finsupp.toMultiset (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ) = Finset.univ.val.map w := by
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  rw [← Multiset.sum_map_singleton (Finset.univ.val.map w), Multiset.map_map]
  rfl

end Ii

open Ii in
theorem intersection_monomial_lines : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) (ℓ : J → HermLine ι) (w : Fin d → J), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d ∧ ∃ σ : Equiv.Perm (Fin d), monoLines ℓ (∑ k, Finsupp.single (w k) 1) d = (fun k => ℓ (w k)) ∘ σ ∧ II K ι P d (monoLines ℓ (∑ k, Finsupp.single (w k) 1) d) = II K ι P d (fun k => ℓ (w k)) := by
  intro II hII K _ ι _ P d J ℓ w hP hℓ
  set m : J →₀ ℕ := ∑ k, Finsupp.single (w k) 1 with hm
  have hdeg : m.degree = d := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hm, map_sum, Finsupp.degree_single]
  set L : List J := (Finsupp.toMultiset m).toList with hL
  have hML : (L : Multiset J) = Finset.univ.val.map w := by
    rw [hL, Multiset.coe_toList, hm, toMultiset_sum_single]
  have hlen : L.length = d := by
    have := congrArg Multiset.card hML
    simpa using this
  let f : Fin d → J := fun k => L.get (Fin.cast hlen.symm k)
  have hf : List.ofFn f = L :=
    List.ext_get (by simp [hlen]) (fun i h1 h2 => by simp [f])
  have hmap : Finset.univ.val.map f = Finset.univ.val.map w := by
    rw [Fin.univ_val_map, hf, hML]
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq f w hmap
  have hmono : monoLines ℓ m d = (fun k => ℓ (w k)) ∘ σ := by
    funext k
    have hk : (k : ℕ) < L.length := by
      rw [hlen]
      exact k.2
    simp only [monoLines, Function.comp_apply, hσ k]
    rw [dite_eq_left hk]
    rfl
  refine ⟨hdeg, σ, hmono, ?_⟩
  rw [hmono]
  exact (hII K ι).1 P d (fun k => ℓ (w k)) σ hP (fun j => hℓ _)

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.LinearFunctionalProductExpansion
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.linear_functional_product_expansion : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (c : Fin d → J → ℝ), Φ (∏ k, ∑ j, C (c k j) * X j) = ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  intro J _ _ d Φ c
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.monomial_sum_one, C_mul', map_smul, smul_eq_mul]
  rfl
end

