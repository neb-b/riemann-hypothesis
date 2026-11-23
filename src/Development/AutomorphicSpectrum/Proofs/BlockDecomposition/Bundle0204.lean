module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementGelfandPolynomialFormula
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GelfRec

open Polynomial Matrix

noncomputable def entrySum {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ[X]) (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) : ℂ[X] :=
  ∑ a, ∑ b, (E * (A ^ k).map C) a b

theorem natDegree_adjugate_le (m : ℕ) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (a b : Fin (m + 1)) :
    (adjugate ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C) a b).natDegree
      ≤ m := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  have hs : ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C).submatrix
        b.succAbove a.succAbove =
      (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove).map C
        + (B.submatrix b.succAbove a.succAbove).map C := by
    rfl
  rw [hs]
  have h1 := natDegree_det_X_add_C_le
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove)
    (B.submatrix b.succAbove a.succAbove)
  rw [Fintype.card_fin] at h1
  refine natDegree_mul_le.trans ?_
  have h2 : ((-1 : ℂ[X]) ^ ((b : ℕ) + (a : ℕ))).natDegree = 0 := by
    rcases neg_one_pow_eq_or ℂ[X] ((b : ℕ) + (a : ℕ)) with h | h <;> simp [h]
  omega

theorem entrySum_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ[X]) (k : ℕ) :
    x * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A k
        + entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A (k + 1)
      = det (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C) * C (∑ a, ∑ b, (A ^ k) a b) := by
  set M := x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C with hM
  set E := adjugate M with hEdef
  have hE : E * M = M.det • (1 : Matrix (Fin n) (Fin n) ℂ[X]) := adjugate_mul M
  have hp : (A ^ (k + 1)).map C = A.map C * (A ^ k).map C := by
    rw [pow_succ']
    exact Matrix.map_mul
  have key : x • (E * (A ^ k).map C) + E * (A ^ (k + 1)).map C = M.det • (A ^ k).map C := by
    have h3 : (E * M) * (A ^ k).map C = M.det • (A ^ k).map C := by
      rw [hE, Matrix.smul_mul, Matrix.one_mul]
    rw [← h3, hp, hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_assoc]
  have h4 := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ[X] => ∑ a, ∑ b, B a b) key
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Matrix.map_apply] at h4
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [entrySum, map_sum]
  exact h4

theorem newton_closed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ[X]) (N : ℕ) :
    x ^ (N + 1) * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A 0
        - det (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)
          * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)
      = (-1) ^ N * x * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : ∑ k ∈ Finset.range (N + 1), C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k)
        = x * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)
          + C ((-1 : ℂ) ^ N * ∑ a, ∑ b, (A ^ N) a b) * x := by
      have h1 : ∀ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k)
          = x * (C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)) := by
        intro k hk
        have hk' : k ≤ N := (Finset.mem_range.1 hk).le
        rw [Nat.succ_sub hk', pow_succ]
        ring
      rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, ← Finset.mul_sum]
      simp
    have hstep := entrySum_step A x N
    rw [hs]
    simp only [map_mul, map_pow, map_neg, map_one] at ih hstep ⊢
    linear_combination x * ih + (-1) ^ N * x * hstep

theorem shift_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (X - C c : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C
      = (X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ).map C + (A - c • (1 : Matrix (Fin n) (Fin n) ℂ)).map C := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [Matrix.one_apply_ne h]

theorem natDegree_entrySum_le (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ) (k : ℕ) :
    (entrySum (adjugate ((X - C c : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + A.map C))
      A k).natDegree ≤ m := by
  rw [shift_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  rw [Matrix.mul_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
  exact (natDegree_mul_C_le _ _).trans (natDegree_adjugate_le m _ a d)

theorem entrySum_zero {n : ℕ} (l : Fin n → ℂ) (x : ℂ[X]) :
    entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C))
        (Formalism.REAL.Amat l) 0
      = ∏ s, (x + C (l s) + 1) - ∏ s, (x + C (l s)) := by
  have hM : x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C
      = (compRingHom x).mapMatrix
        ((X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C) := by
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have h0 := congrArg (compRingHom x) (GlobalTheory.CompanionTheory.AdjSum.adj_sum n l)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_sub, map_prod, map_add (f := _), map_one, coe_compRingHom_apply, X_comp, C_comp] at h0
  rw [← h0, hM, ← RingHom.map_adjugate]
  simp [entrySum]

theorem det_shift (m : ℕ) (χ : Fin (m + 1) → ℂ) :
    det ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
        + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C)
      = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := by
  rw [det_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun s _ => ?_
    have hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ) := by
      rw [← C_sub]
      congr 1
      push_cast
      ring
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.map_apply,
      Formalism.REAL.Amat, Matrix.of_apply, if_true, smul_eq_mul, mul_one]
    rw [hc]
    ring
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := ne_of_gt hij'
    simp [Formalism.REAL.Amat, Matrix.one_apply_ne hne, hne, not_lt.2 hij'.le]

theorem prod_monic (m : ℕ) (c : Fin (m + 1) → ℂ) :
    (∏ s, (X + C (c s))).coeff (m + 1) = 1 := by
  have hm : (∏ s, (X + C (c s))).Monic := monic_prod_of_monic _ _ fun s _ => monic_X_add_C _
  have hd : (∏ s, (X + C (c s))).natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
    simp
  have h1 := hm.coeff_natDegree
  rwa [hd] at h1

theorem gelfVal_newton : ∀ (m : ℕ) (χ : Fin (m + 1) → ℂ) (N : ℕ), ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).comp (Polynomial.X + 1) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2)))) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) = GlobalTheory.Dec.gelfVal χ N := by
  intro m χ N
  have hdet := det_shift m χ
  have hz := entrySum_zero (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) (X - C (m : ℂ))
  have hc := newton_closed (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N
  have hs := entrySum_step (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N
  have hdeg := natDegree_entrySum_le m (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (m : ℂ) (N + 1)
  have hterm : ∀ s : Fin (m + 1), (X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2)
      = X + C (χ s - (m : ℂ) / 2) := by
    intro s
    have hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ) := by
      rw [← C_sub]
      congr 1
      push_cast
      ring
    rw [hc]
    ring
  have hQ : (∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1)
      = ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) + 1) := by
    rw [prod_comp]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hterm s]
    simp
    ring
  have hP : ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2))
      = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := Finset.prod_congr rfl fun s _ => hterm s
  rw [hP, ← hQ] at hz
  rw [hz, hdet] at hc
  rw [hdet] at hs
  have hsq : (-1 : ℂ[X]) ^ N * (-1) ^ N = 1 := by
    rw [← mul_pow]
    simp
  change _ = ∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b
  have hgoal : (-1 : ℂ[X]) ^ N * ((X - C (m : ℂ)) ^ (N + 1) * ((∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1) - (∏ s, (X + C (χ s - (m : ℂ) / 2)))) - (∏ s, (X + C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (X - C (m : ℂ)) ^ (N - k))
      = C (∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b) * (∏ s, (X + C (χ s - (m : ℂ) / 2)))
        - entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
            + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C))
          (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (N + 1) := by
    have hc' := hc
    simp only [GlobalTheory.Dec.gelfVal] at *
    linear_combination (-1 : ℂ[X]) ^ N * hc' + hs + (X - C (m : ℂ)) * entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
            + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C))
          (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) N * hsq
  rw [hgoal, coeff_sub, coeff_C_mul, prod_monic m (fun s => χ s - (m : ℂ) / 2),
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hdeg)]
  simp

end GlobalTheory.CompanionTheory.GelfRec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniqOfWaveSpeed
section
noncomputable section

open Matrix
open scoped ContDiff
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Uniq

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Eu_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := fun X : Mat n => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simp only [Epow, if_neg hab]
      exact contDiffOn_const (c := (0 : V))
  | succ m ih =>
    intro a b
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      ext x
      simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => Eu_smooth (ih c b) s a c

theorem Epow_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (f - f')) (Epow s m a b f - Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact GlobalTheory.CompanionTheory.WaveAll.Eu_sub (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem gel_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f - f')) (gel s m f - gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_sub hf hf' s m a a hx

theorem Om_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f - f')) (Om f - Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, gel_sub hf hf' _ _ hx, smul_sub, smul_add]
  abel

theorem wave_sub {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E (u - v) := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · exact hu.1.sub hv.1
  · exact (hu.2.1 t).1.sub (hv.2.1 t).1
  · intro g hg k
    simp only [Pi.sub_apply, (hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_sub]
  · have h1 := (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).contDiffAt (x := t)
    have h2 := (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).contDiffAt (x := t)
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, iteratedDeriv_sub (h1.of_le (WithTop.coe_le_coe.2 le_top)) (h2.of_le (WithTop.coe_le_coe.2 le_top)),
      hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_sub (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, deriv_sub h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, sub_zero]

theorem waveUniq_of_waveSpeed : WaveSpeed → WaveUniq := by
  intro hS n E u v hu hv h0 t x hx
  obtain ⟨c, hc⟩ := hS n
  have hw := wave_sub hu hv
  have h := hc E (u - v) hw t x hx fun y hy _ => by
    simp only [Pi.sub_apply]
    exact sub_eq_zero.2 (h0 _ (GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx hy))
  exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.WaveK.Uniq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpSmooth
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
open GlobalTheory.CompanionTheory.WaveAll

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Swap

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_csmul {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (X : Mat n) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro x hx
  have h1 : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  have h3 : fderiv ℝ (c • f) x = c • fderiv ℝ f x := (h1.hasFDerivAt.const_smul c).fderiv
  simp only [Rd, Pi.smul_apply, h3]
  rfl

theorem Eu_csmul {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_csmul hf c _ hx]
  rw [smul_comm c (1 / 2 : ℂ), smul_add c, smul_comm c]

theorem Epow_csmul (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (c • f)) (c • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Eu_congr isOpen_GLs (ih d b) s a d hx]
    exact Eu_csmul (Epow_smooth hR hf s m d b) c s a d hx

theorem gel_csmul (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (c • f)) (c • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_csmul hR hf c s m a a hx

theorem gel_add (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  have e : f + f' = f - (-1 : ℂ) • f' := by
    ext y
    simp
  have hm : ContDiffOn ℝ ∞ ((-1 : ℂ) • f') (GLs n) := hf'.const_smul (-1 : ℂ)
  have h := gel_sub hR hf hm s m hx
  rw [e, h]
  simp only [Pi.sub_apply, Pi.add_apply, gel_csmul hR hf' (-1) s m hx, Pi.smul_apply]
  simp

theorem gel_zero (hR : RCalc) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (0 : Mat n → V)) 0 (GLs n) := by
  intro x hx
  have h := gel_csmul hR (contDiffOn_const (c := (0 : V)) : ContDiffOn ℝ ∞ (0 : Mat n → V) (GLs n)) 0 s m hx
  simpa using h

theorem gel_sum (hR : RCalc) {ι : Type} (S : Finset ι) {F : ι → Mat n → V}
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (∑ i ∈ S, F i)) (∑ i ∈ S, gel s m (F i)) (GLs n) := by
  classical
  intro x hx
  induction S using Finset.induction_on with
  | empty => simpa using gel_zero hR s m hx
  | insert i S hi ih =>
    have hS : ContDiffOn ℝ ∞ (∑ j ∈ S, F j) (GLs n) := by
      have e : (∑ j ∈ S, F j) = fun y => ∑ j ∈ S, F j y := by
        ext y
        simp only [Finset.sum_apply]
      rw [e]
      exact ContDiffOn.sum fun j _ => hF j
    rw [Finset.sum_insert hi, Finset.sum_insert hi, gel_add hR (hF i) hS s m hx, Pi.add_apply, Pi.add_apply, ih]

theorem gel_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ContDiffOn ℝ ∞ (gel s m f) (GLs n) := by
  have e : gel s m f = fun x => ∑ a, Epow s m a a f x := by
    ext x
    simp only [gel, Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun a _ => Epow_smooth hR hf s m a a

theorem zOp_smooth (hR : RCalc) (w : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (zOp w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact gel_smooth hR ih p.1 p.2

theorem Eu_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (a b : Fin n)
    (s : Bool) (m : ℕ) : Set.EqOn (Eu s' a b (gel s m f)) (gel s m (Eu s' a b f)) (GLs n) := by
  intro x hx
  have hc := (hR n).1 V f hf
  have hS := hc.1
  have hG := hc.2.2.1
  set d : ℂ := if s' then -Complex.I else Complex.I with hd
  have hdB : ContDiffOn ℝ ∞ (d • Rd (Matrix.single a b Complex.I) f) (GLs n) :=
    (hS _).const_smul d
  have hsum : ContDiffOn ℝ ∞ (Rd (Matrix.single a b 1) f + d • Rd (Matrix.single a b Complex.I) f) (GLs n) :=
    (hS _).add hdB
  have e : Eu s' a b f = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) f + d • Rd (Matrix.single a b Complex.I) f) := rfl
  rw [e, gel_csmul hR hsum _ s m hx, Pi.smul_apply, gel_add hR (hS _) hdB s m hx, Pi.add_apply,
    gel_csmul hR (hS _) d s m hx, Pi.smul_apply, ← hG s m _ x hx, ← hG s m _ x hx]
  rfl

theorem Epow_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (m' : ℕ)
    (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s' m' a b (gel s m f)) (gel s m (Epow s' m' a b f)) (GLs n) := by
  induction m' with
  | zero =>
    intro a b x hx
    by_cases hab : a = b
    · simp [Epow, hab]
    · simp only [Epow, if_neg hab]
      exact (gel_zero hR s m hx).symm
  | succ m' ih =>
    intro a b x hx
    have e : Epow s' (m' + 1) a b f = ∑ c, Eu s' a c (Epow s' m' c b f) := rfl
    rw [e, gel_sum hR _ (fun c => Eu_smooth hR (Epow_smooth hR hf s' m' c b) s' a c) s m hx]
    simp only [Epow, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Eu_congr isOpen_GLs (ih c b) s' a c hx]
    exact Eu_gel hR (Epow_smooth hR hf s' m' c b) s' a c s m hx

theorem gel_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (m' : ℕ)
    (s : Bool) (m : ℕ) : Set.EqOn (gel s' m' (gel s m f)) (gel s m (gel s' m' f)) (GLs n) := by
  intro x hx
  have e : gel s' m' f = ∑ a, Epow s' m' a a f := rfl
  rw [e, gel_sum hR _ (fun a => Epow_smooth hR hf s' m' a a) s m hx]
  simp only [gel, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := Epow_gel hR hf s' m' s m a a hx
  simpa only [gel, Finset.sum_apply] using h

theorem zOp_append (w w' : List (Bool × ℕ)) (f : Mat n → V) : zOp (w ++ w') f = zOp w (zOp w' f) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change gel p.1 p.2 (zOp (w ++ w') f) = gel p.1 p.2 (zOp w (zOp w' f))
    rw [ih]

theorem gel_zOp (hR : RCalc) (s : Bool) (m : ℕ) (w : List (Bool × ℕ)) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (gel s m (zOp w f)) (zOp w (gel s m f)) (GLs n) := by
  induction w with
  | nil => exact fun _ _ => rfl
  | cons p w ih =>
    intro x hx
    change gel s m (gel p.1 p.2 (zOp w f)) x = gel p.1 p.2 (zOp w (gel s m f)) x
    rw [gel_gel hR (zOp_smooth hR w hf) s m p.1 p.2 hx]
    exact gel_congr isOpen_GLs ih p.1 p.2 hx

theorem zOp_zOp (hR : RCalc) (w w' : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (zOp w (zOp w' f)) (zOp w' (zOp w f)) (GLs n) := by
  induction w with
  | nil => exact fun _ _ => rfl
  | cons p w ih =>
    intro x hx
    change gel p.1 p.2 (zOp w (zOp w' f)) x = zOp w' (gel p.1 p.2 (zOp w f)) x
    rw [gel_congr isOpen_GLs ih p.1 p.2 hx]
    exact gel_zOp hR p.1 p.2 w' (zOp_smooth hR w hf) hx

theorem zOp_swap : RCalc → ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w w' : List (Bool × ℕ)) (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ∀ x ∈ GLs n, zOp (w ++ w') f x = zOp (w' ++ w) f x := by
  intro hR n V _ _ w w' f hf x hx
  rw [zOp_append, zOp_append]
  exact zOp_zOp hR w w' hf hx

end GlobalTheory.CompanionTheory.WaveMult.Swap
end
end

