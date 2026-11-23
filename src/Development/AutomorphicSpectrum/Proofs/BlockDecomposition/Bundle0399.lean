module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedEigenvectorExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOneOfLowerParab
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInvOfPowEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CFin

abbrev Idx (r m : ℕ) : Type := Fin r ⊕ Fin m ⊕ Fin r

def frm {A : Type} {n r m : ℕ} (X : Matrix (Fin n) (Fin r) A) (Z : Matrix (Fin n) (Fin m) A)
    (Y : Matrix (Fin n) (Fin r) A) : Matrix (Fin n) (Idx r m) A :=
  Matrix.fromCols X (Matrix.fromCols Z Y)

def cnt {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : ℤ := ((S.filter (· < i)).card : ℤ)

def lev {r : ℕ} (m : ℕ) (S : Finset (Fin r)) : Idx r m → ℤ
  | .inl i => cnt S i - S.card
  | .inr (.inl _) => 0
  | .inr (.inr i) => S.card - cnt S i

def wt {r : ℕ} (m : ℕ) (t : Fin r → ℝ) : Idx r m → ℝ
  | .inl i => t i
  | .inr (.inl _) => 1
  | .inr (.inr i) => (t i)⁻¹

def bd {ι A : Type} [Zero A] (b : ι → ℤ) (M : Matrix ι ι A) : Matrix ι ι A :=
  Matrix.of fun u v => if b u = b v then M u v else 0


open Classical in
def deep {r : ℕ} (t₁ : ℝ) (t : Fin r → ℝ) : Finset (Fin r) :=
  Finset.univ.filter fun j => t₁ < t j ∧ ∀ j' : Fin r, j'.val = j.val + 1 → t₁ * t j' < t j

def StabUpTo {L : Type} [CommRing L] {n r : ℕ} (X : Matrix (Fin n) (Fin r) L) (g : Matrix (Fin n) (Fin n) L)
    (j : Fin r) : Prop :=
  ∀ l : Fin r, l ≤ j → ∃ b : Fin r → L, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0

theorem bd_map {ι A B : Type} [Zero A] [Zero B] (b : ι → ℤ) (φ : A → B) (h0 : φ 0 = 0) (M : Matrix ι ι A) :
    (bd b M).map φ = bd b (M.map φ) := by
  ext u v
  by_cases h : b u = b v <;> simp [bd, h, h0]

theorem bd_mul {ι A : Type} [Fintype ι] [CommRing A] {b : ι → ℤ} {M N : Matrix ι ι A}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) : bd b (M * N) = bd b M * bd b N := by
  ext u v
  simp only [bd, Matrix.of_apply, Matrix.mul_apply]
  by_cases h : b u = b v
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : b u = b w
    · rw [if_pos h1, if_pos (h1.symm.trans h)]
    · rw [if_neg h1]
      rcases lt_or_gt_of_ne h1 with h2 | h2
      · rw [show N w v = 0 from hN (by omega), mul_zero, zero_mul]
      · rw [show M u w = 0 from hM h2, zero_mul, zero_mul]
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun w _ => ?_).symm
    by_cases h1 : b u = b w
    · rw [if_neg (fun e => h (h1.trans e)), mul_zero]
    · rw [if_neg h1, zero_mul]

end GlobalTheory.CompanionTheory.CFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportOfExponentOfCasselman
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.PinLift

theorem gl_one_comm {k : Type} [Field k] (a b : GL (Fin 1) k) : a * b = b * a := by
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi
  subst hj
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one]
  exact mul_comm _ _

noncomputable def torusCharHom {k : Type} [Field k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) :
    (∀ _ : Fin n, GL (Fin 1) k) →* ℂ where
  toFun := PositivityTheory.Lbc.torusChar ξ
  map_one' := by simp [PositivityTheory.Lbc.torusChar]
  map_mul' a b := by simp [PositivityTheory.Lbc.torusChar, Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.PinLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorCharInjective
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev TorPt (n : ℕ) := {z : Fin n → ℂ // ∀ a, ‖z a‖ = 1}

def diagU (z : TorPt n) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨diagonal z.1, by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, z.2 a]
    simp⟩

def dualAct (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) : Module.End ℂ (E.V →L[ℂ] ℂ) where
  toFun ξ := ξ ∘L E.ρ k⁻¹
  map_add' x y := ContinuousLinearMap.add_comp _ _ _
  map_smul' c x := ContinuousLinearMap.smul_comp _ _ _

theorem diagU_comm (z w : TorPt n) : diagU z * diagU w = diagU w * diagU z := by
  apply Subtype.ext
  show diagonal z.1 * diagonal w.1 = diagonal w.1 * diagonal z.1
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem dualAct_comm (E : KMod n) (z w : TorPt n) : Commute (dualAct E (diagU z)) (dualAct E (diagU w)) := by
  apply LinearMap.ext
  intro ξ
  show (ξ ∘L E.ρ (diagU w)⁻¹) ∘L E.ρ (diagU z)⁻¹ = (ξ ∘L E.ρ (diagU z)⁻¹) ∘L E.ρ (diagU w)⁻¹
  rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
  congr 1
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul, ← _root_.mul_inv_rev,
    ← _root_.mul_inv_rev, diagU_comm]

def torChar (μ : Fin n → ℤ) (z : TorPt n) : ℂ := ∏ a, z.1 a ^ μ a

theorem torChar_injective : Function.Injective (torChar (n := n)) := by
  intro μ ν h
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := Function.ne_iff.1 hne
  have hd : (μ a - ν a : ℤ) ≠ 0 := sub_ne_zero.2 ha
  set w : ℂ := Complex.exp (((Real.pi / ((μ a - ν a : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) with hw
  have hw1 : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  let z : TorPt n := ⟨fun b => if b = a then w else 1, fun b => by by_cases hb : b = a <;> simp [hb, hw1]⟩
  have hval : ∀ m : Fin n → ℤ, torChar m z = w ^ m a := by
    intro m
    unfold torChar
    rw [Fintype.prod_eq_single a (fun b hb => by simp [z, hb])]
    simp [z]
  have h1 := congrFun h z
  rw [hval, hval] at h1
  have h2 : w ^ (μ a - ν a) = 1 := by
    rw [zpow_sub₀ hw0, h1, div_self (zpow_ne_zero _ hw0)]
  have h3 : w ^ (μ a - ν a) = -1 := by
    rw [hw, ← Complex.exp_int_mul]
    have hd' : ((μ a - ν a : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hd
    have : (((μ a - ν a : ℤ)) : ℂ) * (((Real.pi / ((μ a - ν a : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I := by
      push_cast at hd' ⊢
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  rw [h3] at h2
  norm_num at h2

theorem wtDual_le_joint (E : KMod n) (μ : Fin n → ℤ) :
    wtDual E μ ≤ ⨅ z : TorPt n, (dualAct E (diagU z)).maxGenEigenspace (torChar μ z) := by
  intro ξ hξ
  refine (Submodule.mem_iInf _).2 fun z => ?_
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  exact hξ (diagU z) z.1 rfl

theorem wtDual_iSupIndep : ∀ {n : ℕ} (E : KMod n), iSupIndep (wtDual E) := by
  intro n E
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun z : TorPt n => dualAct E (diagU z))
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (dualAct_comm E j i) φ)
  exact (hind.comp torChar_injective).mono fun μ => wtDual_le_joint E μ

end GlobalTheory.CompanionTheory.RealCount.Tope
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusExponentTail
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.TorusExpU

theorem torusExp : PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp := by
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp
  intro k _ _ _ _ n V _ _ π ϖ hϖ ξ c y hy hfix hx t
  have hord : ord k ϖ = 1 := by
    exact GlobalTheory.SmGL.ord_eq_one hϖ
  refine GlobalTheory.CompanionTheory.ExtCharU.extChar k n _ (jacB π) y ϖ ξ c hy hord ?_ ?_ t
  · intro s hs
    have h1 : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) s = 1 := by
      simpa using GlobalTheory.SmGL.UnramFixed.deltaHalf_torusO k hs
    have h2 : jacBU π s y = y := by simpa using hfix ⟨s, hs⟩
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, h1, h2]
    simp
  · intro x hxa
    have hD : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom)
        (fun i => ϖ ^ x i) = deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) := rfl
    have hne : ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) : ℂˣ) : ℂ) ≠ 0 :=
      Units.ne_zero _
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, hD, hx x hxa, smul_smul]
    congr 1
    rw [Units.val_inv_eq_inv_val, mul_comm, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rfl

end GlobalTheory.CompanionTheory.TorusExpU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementCapelliRecursion
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliEigen

open Formalism.REAL Finset Polynomial GlobalTheory.CapelliNewton

theorem etr_apply_of_eigen : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (P : Polynomial ℂ) (v : V), (∀ u : ℂ, Formalism.REAL.qdet E u v = P.eval u • v) → ∀ (N : ℕ) (t : ℕ → ℂ), (∀ k < N, Formalism.REAL.etr E k v = t k • v) → Formalism.REAL.etr E N v = ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((P).comp (Polynomial.X + 1) - (P)) - (P) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * t k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) • v := by
  intro V _ _ m E hE P v hP N t ht
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  obtain ⟨c, hc1, hc⟩ := _root_.GlobalTheory.qdet_polyMap_monic (Module.End ℂ V) (m + 1) E
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor E (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m E (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow E (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor E (Fin.succAbove j) (Fin.succAbove i) w
        * epow E (N + 1) j i = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := polyOf m Rc φ v with hRp
  set Pq := polyOf (m + 1) c φ (etr E N v) with hPq
  have hPqe : ∀ w : ℂ, Pq.eval w = φ (qdet E w (etr E N v)) := fun w => by rw [hPq, polyOf_eval, hc]
  have hPv : ∀ w : ℂ, φ (qdet E w v) = P.eval w * φ v := fun w => by
    rw [hP, map_smul, smul_eq_mul]
  have hsq : (((-1 : ℂ) ^ N) ^ 2) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * ((P.eval (w + 1) - P.eval w) * φ v) + (-1) ^ N * Rp.eval w
      = (∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k) * (P.eval w * φ v) + (-1) ^ N * Pq.eval w := by
    intro w
    have h1 := congrArg (fun T : Module.End ℂ V => φ (T v)) (_root_.GlobalTheory.TracedComatrix.traced_comatrix (Module.End ℂ V) m E hE w N)
    rw [← _root_.GlobalTheory.qdet_add_one_sub_eq_sum_qminor, hR] at h1
    have h2 : (qdet E w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
        = (∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k) • qdet E w v
          + ((-1 : ℂ) ^ N) • qdet E w (etr E N v) := by
      have h3 : ∀ k ∈ range N, (algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
          = ((-1) ^ k * (w - m) ^ (N - k) * t k) • v := by
        intro k hk
        rw [Module.End.mul_apply, ht k (mem_range.mp hk), Module.algebraMap_end_apply, smul_smul]
      rw [Module.End.mul_apply, sum_range_succ, LinearMap.add_apply, LinearMap.sum_apply, sum_congr rfl h3,
        ← sum_smul, map_add, map_smul, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
      simp
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add (f := _), map_smul,
      LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← polyOf_eval, ← hRp, ← hPqe] at h1
    simp only [hPv] at h1
    linear_combination h1
  have hpoly : C (φ v) * ((-1 : ℂ[X]) ^ N * ((X - C (m : ℂ)) ^ (N + 1) * (P.comp (X + 1) - P)
      - P * ∑ k ∈ range N, C ((-1) ^ k * t k) * (X - C (m : ℂ)) ^ (N - k))) = Pq - Rp := by
    refine Polynomial.funext fun w => ?_
    have h1 := hrec w
    simp only [eval_mul, eval_C, eval_pow, eval_neg, eval_one, eval_sub, eval_X, eval_comp, eval_add,
      eval_finsetSum]
    have h4 : ∑ k ∈ range N, (-1) ^ k * t k * (w - m) ^ (N - k)
        = ∑ k ∈ range N, (-1) ^ k * (w - m) ^ (N - k) * t k :=
      sum_congr rfl fun k _ => by ring
    rw [h4]
    linear_combination ((-1 : ℂ) ^ N) * h1 + (Pq.eval w - Rp.eval w) * hsq
  have hco := congrArg (fun p : ℂ[X] => p.coeff (m + 1)) hpoly
  simp only [coeff_C_mul, coeff_sub] at hco
  have hPc : Pq.coeff (m + 1) = φ (etr E N v) := by
    rw [hPq, polyOf_coeff, hc1]; simp
  have hRc : Rp.coeff (m + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((polyOf_natDegree _ _ _ _).trans_lt (Nat.lt_succ_self m))
  rw [hPc, hRc, sub_zero] at hco
  rw [map_sub, map_smul, smul_eq_mul, ← hco]
  ring

end GlobalTheory.CompanionTheory.CapelliEigen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceFactorTensorDecomp
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.HomTrace

theorem trace_pi_blocks {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Type)
    [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, FiniteDimensional ℂ (P i)]
    (S : ∀ i, P i →ₗ[ℂ] P i) :
    LinearMap.trace ℂ (∀ i, P i) (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) =
      ∑ i, LinearMap.trace ℂ (P i) (S i) := by
  have h : (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) =
      ∑ i, (LinearMap.single ℂ P i) ∘ₗ (S i ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x => funext fun j => ?_
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.sum_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij.symm]
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  have h2 : (S i ∘ₗ LinearMap.proj i) ∘ₗ LinearMap.single ℂ P i = S i := by
    refine LinearMap.ext fun x => ?_
    simp
  rw [h2]

theorem trace_of_block_sandwich : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (I : Type) (W H : ι → Type) [AddCommGroup I] [Module ℂ I] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)] [FiniteDimensional ℂ I] [∀ i, FiniteDimensional ℂ (W i)] [∀ i, Nontrivial (W i)] (R : I ≃ₗ[ℂ] ∀ i, W i →ₗ[ℂ] H i) (F : I →ₗ[ℂ] I) (a : ∀ i, H i →ₗ[ℂ] H i) (b : ∀ i, W i →ₗ[ℂ] W i), (∀ x i, R (F x) i = a i ∘ₗ R x i ∘ₗ b i) → (∀ i, FiniteDimensional ℂ (H i)) ∧ LinearMap.trace ℂ I F = ∑ i, LinearMap.trace ℂ (W i) (b i) * LinearMap.trace ℂ (H i) (a i) := by
  intro ι _ _ I W H _ _ _ _ _ _ _ _ _ R F a b hF
  haveI hP : FiniteDimensional ℂ (∀ i, W i →ₗ[ℂ] H i) := LinearEquiv.finiteDimensional R
  haveI hHom : ∀ i, FiniteDimensional ℂ (W i →ₗ[ℂ] H i) := fun i =>
    Module.Finite.of_surjective (LinearMap.proj (R := ℂ) (φ := fun i => W i →ₗ[ℂ] H i) i)
      (fun y => ⟨Pi.single i y, by simp⟩)
  haveI hH : ∀ i, FiniteDimensional ℂ (H i) := fun i => finiteDimensional_of_hom (W i) (H i)
  refine ⟨hH, ?_⟩
  have hconj : R.conj F =
      LinearMap.pi fun i => sandwich (a i) (b i) ∘ₗ LinearMap.proj i := by
    rw [LinearEquiv.conj_apply]
    refine LinearMap.ext fun f => funext fun i => ?_
    have := hF (R.symm f) i
    simpa [sandwich] using this
  rw [← LinearMap.trace_conj' F R, hconj, trace_pi_blocks]
  exact Finset.sum_congr rfl fun i _ => trace_sandwich (a i) (b i)

end GlobalTheory.CompanionTheory.HomTrace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriFirstIdentity
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc.Contraction

theorem e1 : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.E1 k := by
  intro k _ _ _ _ N J θ l t hA hT g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  have hθJ : J.map θ.toMonoidHom = J := hA.2.2.2.2.2.2.1
  have hθa : θ a ∈ J := by
    rw [← hθJ]
    exact Subgroup.mem_map_of_mem _ ha
  obtain ⟨j₁, hj₁, n, hn, τ, hτ, h₁⟩ :=
    GlobalTheory.CompanionTheory.LbcKillN.killN N J θ l t hA hT (b * θ a) (J.mul_mem hb hθa)
  obtain ⟨j₂, hj₂, κ, hκ, h₂⟩ := GlobalTheory.CompanionTheory.Lbc.KillNlo.killNlo N J θ l t hA hT n hn τ hτ
  refine ⟨(a * j₁ * j₂)⁻¹, J.inv_mem (J.mul_mem (J.mul_mem ha hj₁) hj₂), κ, hκ, ?_⟩
  rw [← h₂, ← h₁]
  simp only [inv_inv, map_inv, map_mul]
  group

end GlobalTheory.CompanionTheory.Lbc.Contraction
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundOfArchimedeanLipschitzStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_of_archimedean_lipschitz : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) (f₀ f₁ : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ), 0 < r → r < n → UFam f₁ →
  (∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧ ∀ i g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R →
    (∀ q ∈ Q₀, ‖f₀ i (g * q)‖ ≤ M) → ‖f₁ i (g * CuspidalSpectrum.archExp Y) - f₁ i g‖ ≤ C * ‖Y‖ * M) →
  UBnd f₀ m → UBnd (fun i g => f₁ i g - An.ctn r (f₁ i) g) (Function.update m r (m r - 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.diffStepU | exact GlobalTheory.CompanionTheory.Conc.diffStepU | (intros; apply GlobalTheory.CompanionTheory.Conc.diffStepU <;> assumption)
end

