module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import GroundTheory.GlobalFields.TateThesis.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0373
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicStandardTournament
section
noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights

variable {n : ℕ}

def t0 (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

def tB (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ :=
  t0 a b - 2 * (if (a, b) ∈ B then 1 else 0) + 2 * (if (b, a) ∈ B then 1 else 0)

structure IsT (t : Fin n → Fin n → ℝ) : Prop where
  diag : ∀ a, t a a = 0
  anti : ∀ a b, t b a = - t a b
  pm : ∀ a b, a ≠ b → t a b = 1 ∨ t a b = -1

theorem isTournament_standard : IsT (t0 (n := n)) := by
  constructor
  · intro a
    simp [t0]
  · intro a b
    unfold t0
    split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num
  · intro a b h
    unfold t0
    have : (a : ℕ) ≠ b := fun e => h (Fin.ext e)
    split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num

theorem isT_tB {B : Finset (Fin n × Fin n)} (hB : ∀ p ∈ B, p.1 < p.2) : IsT (tB B) := by
  constructor
  · intro a
    simp [tB, t0]
  · intro a b
    have := isTournament_standard.anti a b
    simp only [tB, this]
    ring
  · intro a b h
    have h1 : (a, b) ∈ B → (b, a) ∉ B := fun x y => by
      have := hB _ x; have := hB _ y; simp only [Fin.lt_def] at *; omega
    have h2 : (a, b) ∈ B → t0 a b = 1 := fun x => by
      have := hB _ x; simp only at this; simp [t0, this]
    have h3 : (b, a) ∈ B → t0 a b = -1 := fun x => by
      have := hB _ x; simp only at this
      have h' : ¬ a < b := not_lt.2 this.le
      simp [t0, this, h']
    have h4 := isTournament_standard.pm a b h
    simp only [tB]
    by_cases x : (a, b) ∈ B
    · simp [x, h1 x, h2 x]; norm_num
    · by_cases y : (b, a) ∈ B
      · simp [x, y, h3 y]; norm_num
      · simpa [x, y] using h4

def cyc (t : Fin n → Fin n → ℝ) (a b c : Fin n) : ℝ := t a b * t a c + t b c * t b a + t c a * t c b

theorem cyc_eq {t : Fin n → Fin n → ℝ} (h : IsT t) (a c : Fin n) : cyc t a a c = if c = a then 0 else 1 := by
  unfold cyc
  split_ifs with e
  · subst e; simp [h.diag]
  · rw [h.diag]
    rcases h.pm c a e with x | x <;> simp [x, h.anti c a]

theorem cyc_le {t : Fin n → Fin n → ℝ} (h : IsT t) {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    cyc t a b c ≤ 1 := by
  unfold cyc
  rw [h.anti a b, h.anti b c, h.anti c a]
  rcases h.pm a b hab with x | x <;> rcases h.pm b c hbc with y | y <;> rcases h.pm c a hca with z | z <;>
    rw [x, y, z] <;> norm_num

theorem cyclic_standard_tournament {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : cyc t0 a b c = 1 := by
  have h1 : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
  have h2 : (b : ℕ) ≠ c := fun e => hbc (Fin.ext e)
  have h3 : (c : ℕ) ≠ a := fun e => hca (Fin.ext e)
  unfold cyc t0
  split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num

theorem cyc_compare {t : Fin n → Fin n → ℝ} (h : IsT t) (a b c : Fin n) : cyc t a b c ≤ cyc t0 a b c := by
  by_cases hab : a = b
  · subst hab; rw [cyc_eq h, cyc_eq isTournament_standard]
  by_cases hbc : b = c
  · subst hbc
    have e : ∀ t : Fin n → Fin n → ℝ, cyc t a b b = cyc t b b a := fun t => by unfold cyc; ring
    rw [e, e, cyc_eq h, cyc_eq isTournament_standard]
  by_cases hca : c = a
  · subst hca
    have e : ∀ t : Fin n → Fin n → ℝ, cyc t c b c = cyc t c c b := fun t => by unfold cyc; ring
    rw [e, e, cyc_eq h, cyc_eq isTournament_standard]
  rw [cyclic_standard_tournament hab hbc hca]
  exact cyc_le h hab hbc hca

theorem rot (F : Fin n → Fin n → Fin n → ℝ) : ∑ a, ∑ b, ∑ c, F b c a = ∑ a, ∑ b, ∑ c, F a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

theorem three_mul (t : Fin n → Fin n → ℝ) :
    3 * ∑ c, (∑ b, t c b) ^ 2 = ∑ a, ∑ b, ∑ c, cyc t a b c := by
  have h0 : ∑ c, (∑ b, t c b) ^ 2 = ∑ a, ∑ b, ∑ c, t a b * t a c := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sq, Finset.sum_mul_sum]
  have h1 := rot (fun a b c => t a b * t a c)
  have h2 := rot (fun a b c => t c a * t c b)
  simp only [cyc, Finset.sum_add_distrib]
  rw [h0, h1, ← h2]
  ring

theorem score_sq_le {t : Fin n → Fin n → ℝ} (h : IsT t) :
    ∑ c, (∑ b, t c b) ^ 2 ≤ ∑ c : Fin n, (∑ b : Fin n, t0 c b) ^ 2 := by
  have : 3 * ∑ c, (∑ b, t c b) ^ 2 ≤ 3 * ∑ c : Fin n, (∑ b : Fin n, t0 c b) ^ 2 := by
    rw [three_mul, three_mul]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => cyc_compare h a b c
  linarith

theorem sum_standard_tournament (c : Fin n) : ∑ b, t0 c b = 2 * rhoV n c := by
  have e : ∀ b : Fin n, t0 c b = (if b ∈ Finset.Ioi c then 1 else 0) - (if b ∈ Finset.Iio c then 1 else 0) := by
    intro b
    simp only [t0, Finset.mem_Ioi, Finset.mem_Iio]
    split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Fin.card_Ioi, Fin.card_Iio, rhoV]
  have := c.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

theorem card_fst (B : Finset (Fin n × Fin n)) (c : Fin n) :
    (B.filter fun p => p.1 = c).card = (univ.filter fun b => (c, b) ∈ B).card := by
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    subst h2
    simpa using h1
  · intro p hp q hq e
    obtain ⟨_, h2⟩ := Finset.mem_filter.1 hp
    obtain ⟨_, h4⟩ := Finset.mem_filter.1 hq
    exact Prod.ext (h2.trans h4.symm) e
  · intro b hb
    exact ⟨(c, b), by simpa using hb, rfl⟩

theorem card_snd (B : Finset (Fin n × Fin n)) (c : Fin n) :
    (B.filter fun p => p.2 = c).card = (univ.filter fun b => (b, c) ∈ B).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    subst h2
    simpa using h1
  · intro p hp q hq e
    obtain ⟨_, h2⟩ := Finset.mem_filter.1 hp
    obtain ⟨_, h4⟩ := Finset.mem_filter.1 hq
    exact Prod.ext e (h2.trans h4.symm)
  · intro b hb
    exact ⟨(b, c), by simpa using hb, rfl⟩

theorem sum_tB (B : Finset (Fin n × Fin n)) (c : Fin n) : ∑ b, tB B c b = 2 * rhoV n c - 2 * wtB B c := by
  simp only [wtB, card_fst, card_snd]
  simp only [tB, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_standard_tournament, Finset.card_filter]
  push_cast
  ring

theorem sum_wtB (B : Finset (Fin n × Fin n)) (f : Fin n → ℝ) :
    ∑ c, f c * wtB B c = ∑ p ∈ B, (f p.1 - f p.2) := by
  have e : ∀ c, f c * wtB B c = ∑ p ∈ B, ((if p.1 = c then f c else 0) - (if p.2 = c then f c else 0)) := by
    intro c
    simp only [wtB, Finset.card_filter, Finset.sum_sub_distrib]
    push_cast
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Finset.sum_sub_distrib]

theorem wt_sq_le {B : Finset (Fin n × Fin n)} (hB : ∀ p ∈ B, p.1 < p.2) :
    ∑ c, wtB B c ^ 2 ≤ 2 * ∑ c, rhoV n c * wtB B c := by
  have h := score_sq_le (isT_tB hB)
  simp only [sum_tB, sum_standard_tournament] at h
  have e : ∑ c, (2 * rhoV n c - 2 * wtB B c) ^ 2 =
      ∑ c, (2 * rhoV n c) ^ 2 - 8 * ∑ c, rhoV n c * wtB B c + 4 * ∑ c, wtB B c ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e] at h
  linarith

theorem muQ_lt {lam : Fin n → ℤ} (hl : Antitone lam) {lev : Fin n → ℕ} (hm : Monotone lev) {a b : Fin n}
    (h : lev a < lev b) : muQ lam lev b < muQ lam lev a := by
  have hab : a ≤ b := by
    by_contra x
    exact absurd (hm (not_le.1 x).le) (not_le.2 h)
  have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hl hab
  have h2 : (univ.filter fun x => lev b < lev x).card + 1 ≤ (univ.filter fun x => lev a < lev x).card := by
    rw [← Finset.card_insert_of_notMem (a := b) (s := univ.filter fun x => lev b < lev x) (by simp)]
    refine Finset.card_le_card fun x hx => ?_
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using h
    · have := (Finset.mem_filter.1 hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  have h3 : (univ.filter fun x => lev x < lev a).card + 1 ≤ (univ.filter fun x => lev x < lev b).card := by
    rw [← Finset.card_insert_of_notMem (a := a) (s := univ.filter fun x => lev x < lev a) (by simp)]
    refine Finset.card_le_card fun x hx => ?_
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using h
    · have := (Finset.mem_filter.1 hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  have h2' : ((univ.filter fun x => lev b < lev x).card : ℝ) + 1 ≤ (univ.filter fun x => lev a < lev x).card := by
    exact_mod_cast h2
  have h3' : ((univ.filter fun x => lev x < lev a).card : ℝ) + 1 ≤ (univ.filter fun x => lev x < lev b).card := by
    exact_mod_cast h3
  simp only [muQ, rhoU]
  linarith

theorem nsq_comp (x : Fin n → ℝ) (w : Equiv.Perm (Fin n)) : Formalism.REAL.nsq (x ∘ w) = Formalism.REAL.nsq x := by
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Function.comp]
  exact Equiv.sum_comp w fun a => x a * x a

theorem nsq_lt (n : ℕ) (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ) (hlev : IsLev lam lev)
    (ν : Fin n → ℝ) (hν : IsSecondTypeWeight lam lev ν) : Formalism.REAL.nsq (ν + rhoV n) < Formalism.REAL.nsq (muQ lam lev + rhoV n) := by
  obtain ⟨B, hne, hB, -, w, hw⟩ := hν
  have hpos : ∀ p ∈ B, p.1 < p.2 := fun p hp => by
    by_contra x
    exact absurd (hlev.1 (not_lt.1 x)) (not_le.2 (hB p hp))
  have h1 := wt_sq_le hpos
  have h2 : 0 < ∑ c, muQ lam lev c * wtB B c := by
    rw [sum_wtB]
    exact Finset.sum_pos (fun p hp => sub_pos.2 (muQ_lt hl hlev.1 (hB p hp))) hne
  rw [hw, nsq_comp]
  have e : Formalism.REAL.nsq (muQ lam lev + rhoV n - wtB B) = Formalism.REAL.nsq (muQ lam lev + rhoV n)
      - 2 * ∑ c, muQ lam lev c * wtB B c - 2 * ∑ c, rhoV n c * wtB B c + ∑ c, wtB B c ^ 2 := by
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [e]
  linarith

end GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightSpacesSpan
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

variable {n : ℕ}

theorem diag_mem (t : Fin n → Circle) :
    diagonal (fun a => (t a : ℂ)) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  simp [Complex.mul_conj]

def torus : (Fin n → Circle) →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun t := ⟨diagonal fun a => (t a : ℂ), diag_mem t⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp [diagonal_mul_diagonal])

theorem continuous_torus : Continuous (torus (n := n)) := by
  apply Continuous.subtype_mk
  apply Continuous.matrix_diagonal
  exact continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)

variable (E : KMod n)

theorem inner_rho (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : E.V) : ⟪E.ρ k x, E.ρ k y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩ : E.V →ₗᵢ[ℂ] E.V).inner_map_map x y

theorem rho_inv_apply (k : Matrix.unitaryGroup (Fin n) ℂ) (y : E.V) : E.ρ k (E.ρ k⁻¹ y) = y := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]

theorem inner_rho_left (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : E.V) :
    ⟪E.ρ k x, y⟫_ℂ = ⟪x, E.ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← rho_inv_apply E k y]
  exact inner_rho E k x _

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

theorem jointEig_top {V I : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (T : I → V →ₗ[ℂ] V) (hc : ∀ i k, Commute (T i) (T k))
    (hadj : ∀ i, ∃ k, ∀ x y, ⟪T i x, y⟫_ℂ = ⟪x, T k y⟫_ℂ) :
    ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) = ⊤ := by
  choose s hs using hadj
  have hs' : ∀ i x y, ⟪T (s i) x, y⟫_ℂ = ⟪x, T i y⟫_ℂ := fun i x y => by
    rw [← inner_conj_symm, ← hs, inner_conj_symm]
  let H : I ⊕ I → V →ₗ[ℂ] V := Sum.elim (fun i => T i + T (s i)) (fun i => Complex.I • (T i - T (s i)))
  have hH : ∀ i, (H i).IsSymmetric := by
    rintro (i | i) x y
    · simp only [H, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, hs i, hs' i]
      ring
    · simp only [H, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, hs i, hs' i, Complex.conj_I]
      ring
  have hT : ∀ i k, Commute (H i) (T k) := by
    rintro (i | i) k
    · exact (hc _ _).add_left (hc _ _)
    · exact ((hc _ _).sub_left (hc _ _)).smul_left _
  have hHc : ∀ i k, Commute (H i) (H k) := by
    rintro i (k | k)
    · exact (hT _ _).add_right (hT _ _)
    · exact ((hT _ _).sub_right (hT _ _)).smul_right _
  have h := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hH (fun i k _ => hHc i k)
  rw [eq_top_iff, ← h]
  refine iSup_le fun χ => le_iSup_of_le (fun i => (χ (.inl i) - Complex.I * χ (.inr i)) / 2) fun x hx => ?_
  simp only [Submodule.mem_iInf, mem_eigenspace_iff] at hx ⊢
  intro i
  have h1 : T i x + T (s i) x = χ (.inl i) • x := hx (.inl i)
  have h2 : Complex.I • (T i x - T (s i) x) = χ (.inr i) • x := hx (.inr i)
  have h3 : T i x - T (s i) x = -(Complex.I * χ (.inr i)) • x := by
    rw [neg_smul, mul_smul, ← h2, smul_smul, Complex.I_mul_I]; simp
  have h4 : (2 : ℂ) • T i x = (χ (.inl i) - Complex.I * χ (.inr i)) • x := by
    rw [sub_eq_add_neg, add_smul, ← h1, ← h3, two_smul]; abel
  rw [div_eq_inv_mul, mul_smul, ← h4, smul_smul]; simp

variable {n : ℕ} (E : KMod n)

def rhoT (t : Fin n → Circle) : E.V →ₗ[ℂ] E.V := ((E.ρ (torus t) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V)

theorem span_V : ⨆ χ : (Fin n → Circle) → ℂ, ⨅ t, eigenspace (rhoT E t) (χ t) = ⊤ := by
  apply jointEig_top
  · intro s t
    have h : torus s * torus t = torus t * torus s := by rw [← map_mul, ← map_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    simp only [rhoT, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, h, map_mul, ContinuousLinearMap.mul_apply]
  · intro t
    refine ⟨t⁻¹, fun x y => ?_⟩
    simp only [rhoT, ContinuousLinearMap.coe_coe]
    rw [inner_rho_left, map_inv torus t]

theorem exists_weight {χ : (Fin n → Circle) → ℂ} {v : E.V}
    (hv : v ∈ ⨅ t, eigenspace (rhoT E t) (χ t)) (hv0 : v ≠ 0) :
    ∃ μ : Fin n → ℤ, ∀ t, E.ρ (torus t) v = (∏ a, (t a : ℂ) ^ μ a) • v := by
  have hχ : ∀ t, E.ρ (torus t) v = χ t • v := fun t =>
    mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv t)
  have hmul : ∀ s t, χ (s * t) = χ s * χ t := by
    intro s t
    have h := hχ (s * t)
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hχ t, map_smul, hχ s, smul_smul] at h
    rw [← smul_left_injective ℂ hv0 h, mul_comm]
  have hone : χ 1 = 1 := by
    have h := hχ 1
    rw [map_one, map_one, ContinuousLinearMap.one_apply] at h
    exact (smul_left_injective ℂ hv0 (h.symm.trans (one_smul ℂ v).symm))
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  have hform : ∀ t, χ t = ⟪v, E.ρ (torus t) v⟫_ℂ / ⟪v, v⟫_ℂ := by
    intro t
    rw [hχ, inner_smul_right, mul_div_assoc, div_self hvv, mul_one]
  have hcont : Continuous χ := by
    have : χ = fun t => ⟪v, E.ρ (torus t) v⟫_ℂ / ⟪v, v⟫_ℂ := funext hform
    rw [this]
    exact (continuous_const.inner ((E.cont.comp continuous_torus).clm_apply continuous_const)).div_const _
  let χM : (Fin n → Circle) →* ℂ := ⟨⟨χ, hone⟩, hmul⟩
  have hc : ∀ a, ∃ m : ℤ, ∀ z : Circle, χ (Pi.mulSingle a z) = (z : ℂ) ^ m := by
    intro a
    let f : Circle →* ℂˣ := (χM.comp (MonoidHom.mulSingle _ a)).toHomUnits
    have hf : Continuous f := by
      have hs : Continuous fun z : Circle => (Pi.mulSingle a z : Fin n → Circle) := by
        refine continuous_pi fun j => ?_
        rcases eq_or_ne j a with rfl | h
        · simp only [Pi.mulSingle_eq_same]; exact continuous_id'
        · simpa [Pi.mulSingle_eq_of_ne h] using continuous_const
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · show Continuous fun z => χ (Pi.mulSingle a z)
        exact hcont.comp hs
      have : (fun z => (((f z)⁻¹ : ℂˣ) : ℂ)) = fun z => χ (Pi.mulSingle a z⁻¹) := by
        funext z; rw [← map_inv]; rfl
      rw [this]; exact hcont.comp (hs.comp continuous_inv)
    obtain ⟨m, hm, -⟩ := GroundTheory.Global.existsUnique_circle_zpow ⟨f, hf⟩
    exact ⟨m, hm⟩
  choose μ hμ using hc
  refine ⟨μ, fun t => ?_⟩
  rw [hχ]
  congr 1
  conv_lhs => rw [← Finset.univ_prod_mulSingle t]
  change χM (∏ a, Pi.mulSingle a (t a)) = _
  rw [map_prod]
  exact Finset.prod_congr rfl fun a _ => hμ a (t a)

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

variable {n : ℕ}

theorem exists_torus (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) :
    ∃ t : Fin n → Circle, torus t = k ∧ ∀ a, (t a : ℂ) = z a := by
  have hn : ∀ a, ‖z a‖ = 1 := by
    intro a
    have h1 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 k.2) a) a
    rw [hk, Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal] at h1
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply, Complex.star_def] at h1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
    have h2 : ‖z a‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  refine ⟨fun a => ⟨z a, mem_sphere_zero_iff_norm.2 (hn a)⟩, Subtype.ext ?_, fun a => rfl⟩
  rw [hk]
  rfl

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.Tope

open PositivityTheory.RgBcC Module.End GlobalTheory.CompanionTheory.RealCount.TorusSpan

theorem iSup_wtDual_eq_top {n : ℕ} (E : KMod n) : (⨆ μ, wtDual E μ) = ⊤ := by
  haveI := FiniteDimensional.complete ℂ E.V
  rw [eq_top_iff]
  intro ξ _
  obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℂ E.V).surjective ξ
  have hv : v ∈ (⊤ : Submodule ℂ E.V) := trivial
  rw [← span_V E] at hv
  refine Submodule.iSup_induction _ (motive := fun v => InnerProductSpace.toDual ℂ E.V v ∈ ⨆ μ, wtDual E μ) hv
    ?_ ?_ ?_
  · intro χ v hv
    by_cases hv0 : v = 0
    · subst hv0; simp
    obtain ⟨μ, hμ⟩ := exists_weight E hv hv0
    refine Submodule.mem_iSup_of_mem (-μ) ?_
    intro k z hk
    obtain ⟨t, rfl, htz⟩ := exists_torus k z hk
    ext w
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply,
      InnerProductSpace.toDual_apply_apply, ← inner_rho_left, hμ, inner_smul_left, smul_eq_mul]
    congr 1
    rw [map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← htz, map_zpow₀, ← Circle.coe_inv_eq_conj, ← Circle.coe_zpow, ← Circle.coe_zpow, _root_.inv_zpow', Pi.neg_apply]
  · simp
  · intro x y hx hy
    rw [map_add (f := _)]
    exact add_mem hx hy

end GlobalTheory.CompanionTheory.RealCount.Tope
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormalOpenSubgroupCompactStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_open_subgroup_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) → ∃ K₁ : Subgroup (GL (Fin n) k), K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n) ∧ IsOpen (K₁ : Set (GL (Fin n) k)) ∧ (K₁ : Set (GL (Fin n) k)) ⊆ U ∧ K₁.relIndex (GlobalTheory.SplitWeil.KO k (Fin n)) ≠ 0 ∧ ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  first | exact @GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | exact GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | (intros; apply GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmoduleStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_not_in_codim_one_submodule : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (T : Submodule ℂ V), Module.rank ℂ (V ⧸ T) ≤ 1 → ∀ A C : Subrepresentation ρ, (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T → ¬ A.toSubmodule ≤ T → ¬ C.toSubmodule ≤ T → ¬ (A ⊓ C).toSubmodule ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | exact GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | (intros; apply GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet <;> assumption)
end

