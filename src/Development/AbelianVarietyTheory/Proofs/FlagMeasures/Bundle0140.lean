module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProd
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DoubledFlag


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.DoubledFlag.sum_range_double {M : Type} [AddCommMonoid M] (a : ℕ) (f : ℕ → M) :
    ∑ s ∈ range (2 * a + 1), f s = ∑ i : Fin a, (f i + f (2 * a - i)) + f a := by
  rw [show 2 * a + 1 = (a + 1) + a by ring, Finset.sum_range_add, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => f i + f (2 * a - i)), Finset.sum_add_distrib,
    ← Finset.sum_range_reflect (fun x => f (a + 1 + x)) a]
  have h : ∀ x ∈ range a, f (a + 1 + (a - 1 - x)) = f (2 * a - x) := fun x hx => by
    rw [Finset.mem_range] at hx; congr 1; omega
  rw [Finset.sum_congr rfl h]
  abel


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = _root_.GlobalTheory.FlagMeas.dimN n j ∧ _root_.GlobalTheory.Count.layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  intro n a j D ν hj hD hD0 hν0 hν hna hsym
  have hJ : ν a = ∑ i, j i := by
    have h1 : ∀ m, m ≤ a → ν m = ∑ i ∈ range m, if h : i < a then j ⟨i, h⟩ else 0 := by
      intro m hm
      induction m with
      | zero => simp [hν0]
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih (by omega), dite_eq_left (by omega)]
        exact hν ⟨m, by omega⟩
    rw [h1 a le_rfl, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < a then j ⟨i, h⟩ else 0)]
    simp
  have hmid : ν (a + 1) + ν a = n := by
    have h := (hsym a le_rfl).2
    rwa [show 2 * a + 1 - a = a + 1 by omega] at h
  have hlow : ∀ i : Fin a, (ν (i + 1) - ν i) * ν i = j i * ν i := by
    intro i; rw [hν i, Nat.add_sub_cancel_left]
  have hhigh : ∀ i : Fin a, (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i) + j i * ν (i + 1)
      = j i * n := by
    intro i
    have hi := i.isLt
    have h1 := (hsym i (by omega)).2
    have h2 := (hsym (i + 1) (by omega)).2
    have h3 := hν i
    rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
    rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
    rw [show ν (2 * a - i + 1) - ν (2 * a - i) = j i by omega, ← mul_add, h2]
  have hsq : ν a * ν a = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    have hsplit : ∀ i k : Fin a, j i * j k = ((if i < k then j i * j k else 0) +
        (if k < i then j k * j i else 0)) + (if i = k then j i ^ 2 else 0) := by
      intro i k
      rcases lt_trichotomy i k with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp [sq]
      · simp [h, h.ne', not_lt.2 h.le]; ring
    rw [hJ, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsplit i k]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_filter, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
    ring
  refine ⟨?_, ?_⟩
  · rw [_root_.GlobalTheory.DoubledFlag.sum_range_double]
    have hF : ∑ i : Fin a, ((ν (i + 1) - ν i) * ν i + (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i))
        + ∑ i, j i ^ 2 = n * ν a := by
      rw [← Finset.sum_add_distrib, hJ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := hhigh i
      rw [hν i] at h
      rw [hlow i]
      nlinarith
    unfold _root_.GlobalTheory.FlagMeas.dimN
    rw [← hJ]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * ν a := ⟨n - 2 * ν a, by omega⟩
    rw [show ν (a + 1) - ν a = m by omega, show m + 2 * ν a - 2 * ν a = m by omega]
    nlinarith
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ → ℝ, D = fun s => Real.exp (d s) :=
      ⟨fun s => Real.log (D s), funext fun s => (Real.exp_log (hD s)).symm⟩
    have hd0 : d 0 = 0 := by simpa using hD0
    have hdsym : ∀ s, s ≤ a → d (2 * a + 1 - s) = d s := fun s hs => by
      simpa using (hsym s hs).1
    have hc : ∀ i : Fin a, (Real.exp (d (i + 1)) / Real.exp (d i)) ^ (-(1 : ℝ) / j i)
        = Real.exp ((d i - d (i + 1)) / j i) := by
      intro i
      rw [← Real.exp_sub, ← Real.exp_mul]
      congr 1
      ring
    have htail : ∀ i : Fin a, ∑ k ∈ univ.filter (fun k => i < k), (j k : ℝ) = ν a - ν ((i : ℕ) + 1) := by
      intro i
      have hi := i.isLt
      have e : ∀ k : Fin a, (j k : ℝ) = ν ((k : ℕ) + 1) - ν k := fun k => by
        rw [hν k]; push_cast; ring
      simp only [e, Finset.sum_filter, Fin.lt_iff_val_lt_val]
      rw [Fin.sum_univ_eq_sum_range (fun x => if (i : ℕ) < x then (ν (x + 1) : ℝ) - ν x else 0) a,
        ← Finset.sum_filter,
        show (range a).filter (fun x => (i : ℕ) < x) = Ico ((i : ℕ) + 1) a by
          ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega,
        Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_sub (fun x => (ν x : ℝ)),
        Finset.sum_range_sub (fun x => (ν x : ℝ))]
      ring
    simp only [hc]
    unfold _root_.GlobalTheory.Count.layerProd
    simp only [id, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add, ← Real.exp_sum, ← Real.exp_neg,
      pow_one, mul_one]
    rw [Real.exp_eq_exp, ← hJ, _root_.GlobalTheory.DoubledFlag.sum_range_double, eq_neg_iff_add_eq_zero, ← add_assoc,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr (s₁ := (univ : Finset (Fin a))) rfl (g := fun i : Fin a =>
        (2 * (ν ((i : ℕ) + 1) : ℝ) * d ((i : ℕ) + 1) - n * d ((i : ℕ) + 1)) - (2 * (ν i : ℝ) * d i - n * d i)) ?_,
      Fin.sum_univ_eq_sum_range (fun x => (2 * (ν (x + 1) : ℝ) * d (x + 1) - n * d (x + 1)) - (2 * (ν x : ℝ) * d x - n * d x)),
      Finset.sum_range_sub (fun x => 2 * (ν x : ℝ) * d x - n * d x)]
    · have hm : (ν (a + 1) : ℝ) = n - ν a := by rw [eq_sub_iff_add_eq]; exact_mod_cast hmid
      have hda : d (a + 1) = d a := by rw [← hdsym a le_rfl]; congr 1; omega
      rw [hm, hda, hν0, hd0]
      push_cast
      ring
    · intro i _
      have hi := i.isLt
      have hji : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
      have h1 := (hsym i (by omega)).2
      have h2 := (hsym (i + 1) (by omega)).2
      rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
      rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
      have e1 : (ν (2 * a - i + 1) : ℝ) = n - ν i := by rw [eq_sub_iff_add_eq]; exact_mod_cast h1
      have e2 : (ν (2 * a - i) : ℝ) = n - ν ((i : ℕ) + 1) := by rw [eq_sub_iff_add_eq]; exact_mod_cast h2
      have e3 : (ν ((i : ℕ) + 1) : ℝ) = ν i + j i := by exact_mod_cast hν i
      have f1 : d (2 * a - i + 1) = d i := by rw [← hdsym i (by omega)]; congr 1; omega
      have f2 : d (2 * a - i) = d ((i : ℕ) + 1) := by rw [← hdsym (i + 1) (by omega)]; congr 1; omega
      rw [Finset.sum_congr rfl (g := fun k => 4 * (d i - d ((i : ℕ) + 1)) * (j k : ℝ))
          fun k _ => by push_cast; field_simp; ring, ← Finset.mul_sum, htail i, e1, e2, f1, f2, e3]
      push_cast [Nat.cast_sub hna]
      field_simp
      ring

end GlobalTheory.DoubledFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqZeroOnKCOfEqZeroOnKset
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

namespace GlobalTheory.Dec.KCIdent


open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder in
theorem exists_herm_log {n : ℕ} (y J : Matrix (Fin n) (Fin n) ℂ) (hy : IsUnit y)
    (hJ : Commute (yᴴ * y) J) :
    ∃ L : Matrix (Fin n) (Fin n) ℂ, Lᴴ = L ∧ Commute L J ∧ NormedSpace.exp L = yᴴ * y := by
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ yᴴ * y := star_mul_self_nonneg y
  have hu : IsUnit (yᴴ * y) := hy.star.mul hy
  have hsp : IsStrictlyPositive (yᴴ * y) := IsStrictlyPositive.iff_of_unital.mpr ⟨h0, hu⟩
  refine ⟨CFC.log (yᴴ * y), ?_, Commute.cfc_real hJ Real.log, CFC.exp_log (yᴴ * y) hsp⟩
  exact (IsSelfAdjoint.log : IsSelfAdjoint (CFC.log (yᴴ * y)))

theorem differentiable_exp_entry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ (fun z : ℂ => NormedSpace.exp (z • X) i j) := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  intro z
  have hz : DifferentiableAt ℂ (fun w : ℂ => NormedSpace.exp (w • X)) z :=
    (hasDerivAt_exp_smul_const (𝕂 := ℂ) X z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiableAt.comp z hz

theorem eq_zero_on_KC_of_eq_zero_on_Kset : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : Matrix (Fin n) (Fin n) ℂ → E), DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => F (Matrix.of y)) {y | Matrix.of y ∈ GlobalTheory.Dec.KC ε} → (∀ k ∈ Formalism.REAL.Kset ε, F k = 0) → ∀ y ∈ GlobalTheory.Dec.KC ε, F y = 0 := by
  intro n ε E _ _ _ F hF hK y hy
  unfold GlobalTheory.Dec.KC at hy
  obtain ⟨hyu, hyJ⟩ := hy
  have hJh : (Jm ε)ᴴ = Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hyhJ : yᴴ * Jm ε = Jm ε * yᴴ := by
    have h := congrArg Matrix.conjTranspose hyJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hc : Commute (yᴴ * y) (Jm ε) := by
    show yᴴ * y * Jm ε = Jm ε * (yᴴ * y)
    rw [mul_assoc, hyJ, ← mul_assoc, hyhJ, mul_assoc]
  obtain ⟨L, hLh, hLJ, hLe⟩ := exists_herm_log y (Jm ε) hyu hc
  obtain ⟨E', hE'⟩ : ∃ f : ℂ → Matrix (Fin n) (Fin n) ℂ, f = fun w => NormedSpace.exp (w • L) :=
    ⟨_, rfl⟩
  have hmul : ∀ a b : ℂ, E' a * E' b = E' (a + b) := by
    intro a b
    simp only [hE', add_smul]
    exact (Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left a).smul_right b)).symm
  have hstar : ∀ w : ℂ, (E' w)ᴴ = E' (star w) := by
    intro w
    simp only [hE']
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hLh]
  have hEJ : ∀ w : ℂ, E' w * Jm ε = Jm ε * E' w := by
    intro w
    simp only [hE']
    exact (hLJ.smul_left w).exp_left.eq
  have hE0 : E' 0 = 1 := by simp [hE']
  have hEone : E' 1 = yᴴ * y := by
    simp only [hE', one_smul]
    exact hLe
  have hEu : ∀ w : ℂ, IsUnit (E' w) := by
    intro w
    simp only [hE']
    exact Matrix.isUnit_exp _
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ, u = y * E' (-(1 / 2)) := ⟨_, rfl⟩
  have hhalf : star (-(1 / 2 : ℂ)) = -(1 / 2) := by simp
  have hu1 : uᴴ * u = 1 := by
    rw [hu, Matrix.conjTranspose_mul, hstar, hhalf]
    have e1 : E' (-(1 / 2)) * yᴴ * (y * E' (-(1 / 2))) = E' (-(1 / 2)) * (yᴴ * y) * E' (-(1 / 2)) := by
      simp only [mul_assoc]
    have e2 : (-(1 / 2 : ℂ) + 1 + -(1 / 2)) = 0 := by ring
    rw [e1, ← hEone, hmul, hmul, e2, hE0]
  have huJ : u * Jm ε = Jm ε * u := by
    rw [hu, mul_assoc, hEJ, ← mul_assoc, hyJ, mul_assoc]
  have huU : IsUnit u := by
    rw [hu]
    exact hyu.mul (hEu _)
  have hKC : ∀ z : ℂ, u * E' z ∈ GlobalTheory.Dec.KC ε := by
    intro z
    unfold GlobalTheory.Dec.KC
    refine ⟨huU.mul (hEu z), ?_⟩
    rw [mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]
  have hzero : ∀ t : ℝ, F (u * E' ((t : ℂ) * Complex.I)) = 0 := by
    intro t
    apply hK
    unfold Formalism.REAL.Kset
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hstar]
      have hsw : star ((t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0 := by
        rw [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [mul_assoc, ← mul_assoc uᴴ, hu1, one_mul, hmul, hsw, hE0]
    · rw [mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]
  have hγ : Differentiable ℂ (fun z : ℂ => (fun a b => (u * E' z) a b : Fin n → Fin n → ℂ)) := by
    refine differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    have hd : ∀ c, Differentiable ℂ (fun z : ℂ => E' z c b) := by
      intro c
      simp only [hE']
      exact differentiable_exp_entry L c b
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun c _ => (differentiable_const (u a c)).mul (hd c)
  have hg : Differentiable ℂ (fun z : ℂ => F (u * E' z)) := fun z =>
    ((hF _ (hKC z)).comp z ((hγ z).differentiableWithinAt (s := Set.univ))
      (fun w _ => hKC w)).differentiableAt Filter.univ_mem
  have han : AnalyticOnNhd ℂ (fun z : ℂ => F (u * E' z)) Set.univ := fun z _ => hg.analyticAt z
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, F (u * E' z) = 0 := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhdsWithin (0 : ℂ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hcont : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) := by fun_prop
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Complex.I_ne_zero] using ht
    exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero))
  have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq
  have h12 := hall (Set.mem_univ (1 / 2 : ℂ))
  have hy' : u * E' (1 / 2) = y := by
    have e3 : (-(1 / 2 : ℂ) + 1 / 2) = 0 := by ring
    rw [hu, mul_assoc, hmul, e3, hE0, mul_one]
  simp only [Pi.zero_apply] at h12
  rw [hy'] at h12
  exact h12

end GlobalTheory.Dec.KCIdent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockDiagUnitaryProductHom
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.BlockDiagEmb

section
variable {n : ℕ} {σ ι : Type} [Fintype σ] {π : σ → ι} {m : ι → ℕ}

def blk (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ) (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ s, T s * k (π s) * (T s)ᴴ

variable {T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ}

theorem frame_mul_blk (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) (s : σ) :
    (T s)ᴴ * blk T k = k (π s) * (T s)ᴴ := by
  unfold blk
  rw [Matrix.mul_sum, Finset.sum_eq_single s]
  · rw [Matrix.mul_assoc (T s), ← Matrix.mul_assoc, h1, Matrix.one_mul]
  · intro t _ hts
    rw [Matrix.mul_assoc (T t), ← Matrix.mul_assoc, h0 s t hts.symm, Matrix.zero_mul]
  · simp

theorem blk_mul (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k l : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    blk T k * blk T l = blk T (fun i => k i * l i) := by
  conv_lhs => rw [blk, Matrix.sum_mul]
  unfold blk
  refine Finset.sum_congr rfl fun s _ => ?_
  have := frame_mul_blk h1 h0 l s
  unfold blk at this
  rw [Matrix.mul_assoc, this]
  simp only [Matrix.mul_assoc]

theorem blk_one (hs : ∑ s, T s * (T s)ᴴ = 1) : blk T (fun _ => 1) = 1 := by
  simpa [blk] using hs

theorem blk_conjTranspose (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    (blk T k)ᴴ = blk T (fun i => (k i)ᴴ) := by
  simp [blk, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem blk_sub (k l : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    blk T k - blk T l = blk T (fun i => k i - l i) := by
  simp [blk, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem blk_trace (h1 : ∀ s, (T s)ᴴ * T s = 1) (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    (blk T k).trace = ∑ s, (k (π s)).trace := by
  unfold blk
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem hs_eq_trace {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    Formalism.REAL.hs X = (X * Xᴴ).trace.re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem blk_hs (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    Formalism.REAL.hs (blk T k) = ∑ s, Formalism.REAL.hs (k (π s)) := by
  rw [hs_eq_trace, blk_conjTranspose, blk_mul h1 h0, blk_trace h1, Complex.re_sum]
  simp only [hs_eq_trace]

theorem continuous_blk : Continuous (blk T) := by
  unfold blk
  refine continuous_finsetSum _ fun s _ => ?_
  exact (continuous_const.matrix_mul (continuous_apply (π s))).matrix_mul continuous_const

end

theorem unitary_of_allPos {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) : (uMat g)ᴴ * uMat g = 1 := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N) := g.2
  have hJ : Formalism.REAL.Jm (allPos N) = 1 := by simp [Formalism.REAL.Jm, allPos]
  simpa [hJ] using h

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one' {n : ℕ} {ε : Fin n → Bool} : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem continuous_uMat {n : ℕ} {ε : Fin n → Bool} : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem exists_blockDiag_hom : ∀ (n : ℕ) (ε : Fin n → Bool) (σ ι : Type) [Fintype σ] [Fintype ι] (π : σ → ι) (m : ι → ℕ) (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ), Function.Surjective π → (∀ s, (T s)ᴴ * T s = 1) → (∀ s t, s ≠ t → (T s)ᴴ * T t = 0) → ∑ s, T s * (T s)ᴴ = 1 → (∀ k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ, Formalism.REAL.Jm ε * ∑ s, T s * k (π s) * (T s)ᴴ = (∑ s, T s * k (π s) * (T s)ᴴ) * Formalism.REAL.Jm ε) → ∃ Φ : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Formalism.REAL.UJ ε, Continuous Φ ∧ Function.Injective Φ ∧ (∀ g, uMat (Φ g) = ∑ s, T s * uMat (g (π s)) * (T s)ᴴ) ∧ ∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ s, Formalism.REAL.hs (uMat (g (π s)) - 1) := by
  intro n ε σ ι _ _ π m T hπ h1 h0 hs hJ
  let f : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => blk T (fun i => uMat (g i))
      map_one' := by simp only [Pi.one_apply, uMat_one']; exact blk_one hs
      map_mul' := fun g h => by simp only [Pi.mul_apply, uMat_mul']; exact (blk_mul h1 h0 _ _).symm }
  have hfe : ∀ g, f g = blk T (fun i => uMat (g i)) := fun g => rfl
  clear_value f
  have hf : Continuous f := by
    have h : Continuous (fun (g : ∀ i, Formalism.REAL.UJ (allPos (m i))) => fun i => uMat (g i)) :=
      continuous_pi fun i => continuous_uMat.comp (continuous_apply i)
    have h2 := (continuous_blk (T := T)).comp h
    exact h2.congr fun g => (hfe g).symm
  have hmem : ∀ g, f.toHomUnits g ∈ Formalism.REAL.UJ ε := by
    intro g
    show (f g)ᴴ * Formalism.REAL.Jm ε * f g = Formalism.REAL.Jm ε
    rw [hfe]
    have hJ' : ∀ k, Formalism.REAL.Jm ε * blk T k = blk T k * Formalism.REAL.Jm ε := hJ
    have := hJ' (fun i => uMat (g i))
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc, blk_conjTranspose, blk_mul h1 h0]
    simp only [unitary_of_allPos]
    rw [blk_one hs, Matrix.one_mul]
  refine ⟨f.toHomUnits.codRestrict _ hmem, ?_, ?_, fun g => hfe g, fun g => ?_⟩
  · have hu : Continuous f.toHomUnits :=
      Units.continuous_iff.2 ⟨hf, hf.comp continuous_inv⟩
    exact hu.subtype_mk hmem
  · intro g h hgh
    have e : blk T (fun i => uMat (g i)) = blk T (fun i => uMat (h i)) := by
      rw [← hfe, ← hfe]
      exact congrArg (fun x : Formalism.REAL.UJ ε => uMat x) hgh
    funext i
    obtain ⟨s, rfl⟩ := hπ i
    have e2 := frame_mul_blk h1 h0 (fun i => uMat (g i)) s
    rw [e, frame_mul_blk h1 h0] at e2
    have e3 := congrArg (· * T s) e2
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one] at e3
    exact Subtype.ext (Units.ext e3.symm)
  · show Formalism.REAL.hs (f g - 1) = _
    rw [hfe, ← blk_one (T := T) hs, blk_sub, blk_hs h1 h0]

end GlobalTheory.BlockDiagEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceOne
section
open NumberField

namespace GlobalTheory.TraceOnto

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_star (x : 𝓞 E) : ∃ t : 𝓞 E, (t : E) = star (x : E) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd E) x, rfl⟩

def normTraceIdeal (E : Type) [Field E] [NumberField E] [StarRing E] : Ideal (𝓞 E) where
  carrier := {x | ∃ w : 𝓞 E, (w : E) + star (w : E) = (x : E) * star (x : E)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨t, ht⟩ := exists_star b
    refine ⟨u + v + a * t, ?_⟩
    push_cast
    simp only [ht, star_add, star_mul', star_star]
    linear_combination hu + hv
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    obtain ⟨t, ht⟩ := exists_star c
    refine ⟨c * t * u, ?_⟩
    simp only [smul_eq_mul]
    push_cast
    simp only [ht, star_mul', star_star]
    linear_combination ((c : E) * star (c : E)) * hu

theorem exists_trace_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E],
    Formalism.HermitianLatticesTheory.IsCMUnram E → ∃ w : 𝓞 E, (w : E) + star (w : E) = 1 := by
  intro E _ _ _ h
  have htop : normTraceIdeal E = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨θ, t, ht, hn⟩ := h.2.2 P hP
    apply hn
    apply hle
    have ht' : (t : E) = star (θ : E) := ht
    refine ⟨θ * t - θ * θ, ?_⟩
    push_cast
    simp only [ht', star_sub, star_mul', star_star]
    ring
  have h1 : (1 : 𝓞 E) ∈ normTraceIdeal E := htop ▸ Submodule.mem_top
  obtain ⟨w, hw⟩ := h1
  exact ⟨w, by simpa using hw⟩

end GlobalTheory.TraceOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducible
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem hcType_rep : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → Nontrivial Wp ∧ IsCRepOn (UWset k r z) π ∧ ContinuousOn π (UWset k r z) ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ (∀ S : Submodule ℂ Wp, (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤) := by
  intro k r z u Wp _ _ _ π _ hT hπ
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨h1, hmul, hunit, hcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ'
  obtain ⟨g, hg, hρ⟩ := hπ
  have hg' : PI.UpqRep.IsFrameW k r z g := hg
  refine ⟨hρ.1, ⟨h1, hmul⟩, continuousOn_clm_apply.mpr hcont, hunit, fun S hS => ?_⟩
  refine hρ.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ ?_ v hv
  exact GlobalTheory.BesselFrame.conj_mem_UW hg'
    (PI.HwUniqW.mem_UJset_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp hx.1))

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUpperUnitriangularSuperdiagNegStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_upperUnitriangular_superdiag_neg : ∀ (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k), (∀ x y : Fin n, y < x → A x y = 0) → (∀ x, A x x = 1) → (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧ ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  first | exact @GlobalTheory.inv_upperUnitriangular | exact GlobalTheory.inv_upperUnitriangular | (intros; apply GlobalTheory.inv_upperUnitriangular <;> assumption)
end

