module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianTwoPointCombination
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def selL {D E : ℕ} (σ : Fin E → Fin D) : (Fin D → ℂ) →L[ℂ] (Fin E → ℂ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (σ a)

theorem selL_apply {D E : ℕ} (σ : Fin E → Fin D) (z : Fin D → ℂ) (a : Fin E) :
    selL σ z a = z (σ a) := rfl

theorem jacC_selL {D E : ℕ} (σ : Fin E → Fin D) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.A.jacC (selL σ) z = Matrix.of fun a k => if σ a = k then (1 : ℂ) else 0 := by
  ext a k
  simp [ReciprocityTheory.AnForm.A.jacC, ContinuousLinearMap.fderiv, selL_apply, Pi.single_apply]

theorem hessC_selL_apply {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (i j : Fin D) :
    hessC (φ ∘ selL σ) z i j = ∑ b, (∑ a, (if σ a = i then (1 : ℂ) else 0) *
      hessC φ (selL σ z) a b) * (if σ b = j then (1 : ℂ) else 0) := by
  rw [ReciprocityTheory.AnForm.A.hessC_comp φ (selL σ) z ((selL σ).analyticAt z) hφ, jacC_selL]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  split_ifs <;> simp

theorem hessC_selL_inj {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) {σ : Fin E → Fin D}
    (hσ : Function.Injective σ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (a b : Fin E) :
    hessC (φ ∘ selL σ) z (σ a) (σ b) = hessC φ (selL σ z) a b := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hσ.eq_iff]

theorem hessC_selL_left {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) {i : Fin D} (hi : ∀ a, σ a ≠ i) (j : Fin D) :
    hessC (φ ∘ selL σ) z i j = 0 := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hi]

theorem hessC_selL_right {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (i : Fin D) {j : Fin D} (hj : ∀ a, σ a ≠ j) :
    hessC (φ ∘ selL σ) z i j = 0 := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hj]

theorem contDiffAt_comp_selL {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) : ContDiffAt ℝ 2 (φ ∘ selL σ) z :=
  ContDiffAt.comp z hφ ((selL σ).restrictScalars ℝ).contDiff.contDiffAt

def selA {d : ℕ} (c : Fin (d + 2)) : Fin (d + 1) → Fin (d + 2) :=
  Fin.cons c fun i : Fin d => i.succ.succ

def selT {d : ℕ} : Fin d → Fin (d + 2) := fun i => i.succ.succ

theorem selT_injective {d : ℕ} : Function.Injective (selT (d := d)) := fun a b h =>
  Fin.succ_injective _ (Fin.succ_injective _ h)

theorem selA_injective {d : ℕ} {c : Fin (d + 2)} (hc : ∀ i : Fin d, i.succ.succ ≠ c) :
    Function.Injective (selA c) := by
  intro a b h
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => rfl
    | succ b => exact absurd h.symm (by simpa [selA] using hc b)
  | succ a =>
    induction b using Fin.cases with
    | zero => exact absurd h (by simpa [selA] using hc a)
    | succ b =>
      have : a.succ.succ = b.succ.succ := by simpa [selA] using h
      rw [Fin.succ_injective _ (Fin.succ_injective _ this)]

theorem selA_eq_cons {d : ℕ} (c : Fin (d + 2)) (z : Fin (d + 2) → ℂ) :
    selL (selA c) z = Fin.cons (z c) (Fin.tail (Fin.tail z)) := by
  funext a
  induction a using Fin.cases with
  | zero => simp [selL_apply, selA]
  | succ a => simp [selL_apply, selA, Fin.tail]

theorem selT_eq_tail {d : ℕ} (z : Fin (d + 2) → ℂ) :
    selL selT z = Fin.tail (Fin.tail z) := rfl

theorem blk_zero_zero {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : blk e B 0 0 = e := rfl

theorem blk_zero_succ {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (q : Fin d) :
    blk e B 0 q.succ = 0 := rfl

theorem blk_succ_zero {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (p : Fin d) :
    blk e B p.succ 0 = 0 := rfl

theorem blk_succ_succ {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d) :
    blk e B p.succ q.succ = B p q := rfl

theorem blk_assemble {d : ℕ} (T₀ T₁ T₂ : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ) (e₀ e₁ s t v : ℂ)
    (B₀ B₁ C : Matrix (Fin d) (Fin d) ℂ)
    (a₀ : ∀ a b, T₀ (selA 0 a) (selA 0 b) = blk e₀ B₀ a b)
    (l₀ : ∀ j, T₀ (Fin.succ 0) j = 0) (r₀ : ∀ i, T₀ i (Fin.succ 0) = 0)
    (a₁ : ∀ a b, T₁ (selA (Fin.succ 0) a) (selA (Fin.succ 0) b) = blk e₁ B₁ a b)
    (l₁ : ∀ j, T₁ 0 j = 0) (r₁ : ∀ i, T₁ i 0 = 0)
    (a₂ : ∀ a b, T₂ (selT a) (selT b) = C a b)
    (l₂ : ∀ j, T₂ 0 j = 0) (r₂ : ∀ i, T₂ i 0 = 0)
    (l₂' : ∀ j, T₂ (Fin.succ 0) j = 0) (r₂' : ∀ i, T₂ i (Fin.succ 0) = 0) :
    s • T₀ + t • T₁ + v • T₂ = blk (s * e₀) (blk (t * e₁) (s • B₀ + t • B₁ + v • C)) := by
  have p00 : T₀ 0 0 = e₀ := a₀ 0 0
  have p0k : ∀ k : Fin d, T₀ 0 k.succ.succ = 0 := fun k => a₀ 0 k.succ
  have pk0 : ∀ k : Fin d, T₀ k.succ.succ 0 = 0 := fun k => a₀ k.succ 0
  have pkl : ∀ k l : Fin d, T₀ k.succ.succ l.succ.succ = B₀ k l := fun k l => a₀ k.succ l.succ
  have q11 : T₁ (Fin.succ 0) (Fin.succ 0) = e₁ := a₁ 0 0
  have q1k : ∀ k : Fin d, T₁ (Fin.succ 0) k.succ.succ = 0 := fun k => a₁ 0 k.succ
  have qk1 : ∀ k : Fin d, T₁ k.succ.succ (Fin.succ 0) = 0 := fun k => a₁ k.succ 0
  have qkl : ∀ k l : Fin d, T₁ k.succ.succ l.succ.succ = B₁ k l := fun k l => a₁ k.succ l.succ
  have wkl : ∀ k l : Fin d, T₂ k.succ.succ l.succ.succ = C k l := fun k l => a₂ k l
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp only [p00, l₁, l₂, blk_zero_zero, mul_zero, add_zero]
    | succ j =>
      induction j using Fin.cases with
      | zero => simp only [r₀, l₁, l₂, blk_zero_succ, mul_zero, add_zero]
      | succ k => simp only [p0k, l₁, l₂, blk_zero_succ, mul_zero, add_zero]
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp only [l₀, r₁, l₂', blk_succ_zero, mul_zero, add_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => simp only [l₀, q11, l₂', blk_succ_succ, blk_zero_zero, mul_zero, add_zero, zero_add]
        | succ k => simp only [l₀, q1k, l₂', blk_succ_succ, blk_zero_succ, mul_zero, add_zero]
    | succ k =>
      induction j using Fin.cases with
      | zero => simp only [pk0, r₁, r₂, blk_succ_zero, mul_zero, add_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => simp only [r₀, qk1, r₂', blk_succ_succ, blk_succ_zero, mul_zero, add_zero]
        | succ l =>
          simp only [pkl, qkl, wkl, blk_succ_succ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem hessC_row_square : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p₀ p₁ e₀ e₁ : ℂ)
    (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) (s t v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p₀ y) → ContDiffAt ℝ 2 f (Fin.cons p₁ y) → ContDiffAt ℝ 2 α y →
    hessC f (Fin.cons p₀ y) = blk e₀ B₀ → hessC f (Fin.cons p₁ y) = blk e₁ B₁ →
    hessC (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z)))
      (Fin.cons p₀ (Fin.cons p₁ y)) =
    blk ((s : ℂ) * e₀) (blk ((t : ℂ) * e₁) ((s : ℂ) • B₀ + (t : ℂ) • B₁ + (v : ℂ) • hessC α y)) := by
  intro d f α y p₀ p₁ e₀ e₁ B₀ B₁ s t v hf₀ hf₁ hα h₀ h₁
  have ho : (Fin.succ 0 : Fin (d + 2)) = 1 := by simp
  have hinj₀ : Function.Injective (selA (0 : Fin (d + 2))) :=
    selA_injective fun i => Fin.succ_ne_zero _
  have hinj₁ : Function.Injective (selA (Fin.succ 0 : Fin (d + 2))) :=
    selA_injective fun i h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  have q₀ : selL (selA 0) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) = Fin.cons p₀ y := by
    rw [selA_eq_cons]; simp [Fin.tail_cons]
  have q₁ : selL (selA (Fin.succ 0)) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) =
      Fin.cons p₁ y := by
    rw [selA_eq_cons]; simp [Fin.tail_cons]
  have q₂ : selL selT (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) = y := by
    rw [selT_eq_tail]; simp [Fin.tail_cons]
  have g₀ : ContDiffAt ℝ 2 f (selL (selA 0) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by
    rwa [q₀]
  have g₁ : ContDiffAt ℝ 2 f
      (selL (selA (Fin.succ 0)) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by rwa [q₁]
  have g₂ : ContDiffAt ℝ 2 α (selL selT (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by
    rwa [q₂]
  have c₀ := contDiffAt_comp_selL f _ _ g₀
  have c₁ := contDiffAt_comp_selL f _ _ g₁
  have c₂ := contDiffAt_comp_selL α _ _ g₂
  have E : (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z))) =
      fun z => (fun z => (fun z => s * (f ∘ selL (selA 0)) z) z +
        (fun z => t * (f ∘ selL (selA (Fin.succ 0))) z) z) z +
        (fun z => v * (α ∘ selL selT) z) z := by
    funext z
    simp only [Function.comp, selA_eq_cons, selT_eq_tail, ho]
  rw [E, hessC_add' _ _ _ ((contDiffAt_const.mul c₀).add (contDiffAt_const.mul c₁))
      (contDiffAt_const.mul c₂),
    hessC_add' _ _ _ (contDiffAt_const.mul c₀) (contDiffAt_const.mul c₁),
    hessC_const_mul', hessC_const_mul', hessC_const_mul']
  refine blk_assemble _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b; rw [hessC_selL_inj f hinj₀ _ g₀, q₀, h₀]
  · intro j
    refine hessC_selL_left f _ _ g₀ ?_ j
    intro a
    induction a using Fin.cases with
    | zero => exact (Fin.succ_ne_zero _).symm
    | succ a => exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  · intro i
    refine hessC_selL_right f _ _ g₀ i ?_
    intro a
    induction a using Fin.cases with
    | zero => exact (Fin.succ_ne_zero _).symm
    | succ a => exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  · intro a b; rw [hessC_selL_inj f hinj₁ _ g₁, q₁, h₁]
  · intro j
    refine hessC_selL_left f _ _ g₁ ?_ j
    intro a
    induction a using Fin.cases with
    | zero => exact Fin.succ_ne_zero (0 : Fin (d + 1))
    | succ a => exact Fin.succ_ne_zero (Fin.succ a)
  · intro i
    refine hessC_selL_right f _ _ g₁ i ?_
    intro a
    induction a using Fin.cases with
    | zero => exact Fin.succ_ne_zero (0 : Fin (d + 1))
    | succ a => exact Fin.succ_ne_zero (Fin.succ a)
  · intro a b; rw [hessC_selL_inj α selT_injective _ g₂, q₂]
  · intro j; exact hessC_selL_left α _ _ g₂ (fun a => Fin.succ_ne_zero _) j
  · intro i; exact hessC_selL_right α _ _ g₂ i (fun a => Fin.succ_ne_zero _)
  · intro j
    exact hessC_selL_left α _ _ g₂ (fun a h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)) j
  · intro i
    exact hessC_selL_right α _ _ g₂ i (fun a h => Fin.succ_ne_zero _ (Fin.succ_injective _ h))

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt Filter Topology

def cxSimple {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : Prop :=
  ∃ (y : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ), IsSetSheet S Ψ y w γ ∧
    ∀ᶠ q in 𝓝 (y, w), q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorCommutation
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection

theorem exists_conj : ∀ (L : Type) [Field L] (N j : ℕ) (ca cb : Fin N) (U : Matrix (Fin N) (Fin N) L) (X' s : L), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → U ca ca + s * U ca cb ≠ 0 → X' * (U ca ca + s * U ca cb) = s * U cb cb → ∃ V : Matrix (Fin N) (Fin N) L, IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c, c ≠ cb → V c c ≠ 0) ∧ (1 + Matrix.single cb ca X') * V = U * (1 + Matrix.single cb ca s) := by
  intro L _ N j ca cb U X' s hcb hblk hU hT hd hne hX
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hne' : cb ≠ ca := hlt.ne'
  have hR : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (M * Matrix.single cb ca t) r c = if c = ca then M r cb * t else 0 := by
    intro M t r c
    by_cases h : c = ca
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hL : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (Matrix.single cb ca t * M) r c = if r = cb then t * M ca c else 0 := by
    intro M t r c
    by_cases h : r = cb
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hW : ∀ r c : Fin N, ((1 + Matrix.single cb ca (-X')) * U) r c
      = U r c + if r = cb then -X' * U ca c else 0 := by
    intro r c
    rw [add_mul, one_mul, Matrix.add_apply, hL]
  have hV : ∀ r c : Fin N,
      ((1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s)) r c
      = U r c + (if r = cb then -X' * U ca c else 0)
        + if c = ca then (U r cb + if r = cb then -X' * U ca cb else 0) * s else 0 := by
    intro r c
    rw [mul_add, mul_one, Matrix.add_apply, hR, hW, hW]
  have hTv : ∀ t : L, IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) L) := by
    intro t a b h
    have hab : a ≠ b := by
      rintro rfl
      exact h Iff.rfl
    rw [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, zero_add]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h hblk.symm
  refine ⟨(1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s),
    ((hTv _).mul hU).mul (hTv _), ?_, ?_, ?_⟩
  · intro r c hrc
    have hrc' : c < r := hrc
    rw [hV]
    by_cases hc : c = ca
    · subst hc
      by_cases hr : r = cb
      · subst hr
        have h0 : U r c = 0 := hT hrc
        simp only [if_true, h0]
        linear_combination -hX
      · have hcr : cb < r := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (r : ℕ) ≠ cb := fun h => hr (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U r cb = 0 := hT hcr
        simp [hr, h0, h1]
    · by_cases hr : r = cb
      · subst hr
        have hcca : c < ca := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (c : ℕ) ≠ ca := fun h => hc (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U ca c = 0 := hT hcca
        simp [hc, h0, h1]
      · have h0 : U r c = 0 := hT hrc
        simp [hc, hr, h0]
  · intro c hc
    rw [hV]
    by_cases hca : c = ca
    · subst hca
      simp only [if_true, if_neg hc, add_zero]
      intro h
      apply hne
      linear_combination h
    · simpa [hc, hca] using hd c
  · have hinv : (1 + Matrix.single cb ca X') * (1 + Matrix.single cb ca (-X'))
        = (1 : Matrix (Fin N) (Fin N) L) := by
      have h0 : Matrix.single cb ca X' * Matrix.single cb ca (-X')
          = (0 : Matrix (Fin N) (Fin N) L) := by
        ext r c
        rw [hL, Matrix.single_apply]
        simp [hne']
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h0, add_zero, add_assoc,
        ← Matrix.single_add]
      simp
    rw [← mul_assoc, ← mul_assoc, hinv, one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorizationOfNearTriangular
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Factor

theorem exists_upper_transvection_upper : ∀ (N j : ℕ) (ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j C → C.det ≠ 0 → (∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0) → ∃ (B U : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsBlockDiag j B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ C = B * (1 + Matrix.single cb ca t) * U := by
  intro N j ca cb C hcb hblk hC hdet hlow
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hne : ca ≠ cb := ne_of_lt hlt
  have hne' : cb ≠ ca := hne.symm
  have hx : C ca ca = 0 → C cb ca ≠ 0 := by
    intro ha hx
    apply hdet
    have hT : C.BlockTriangular id := by
      intro r c hrc
      by_cases h : r = cb ∧ c = ca
      · obtain ⟨rfl, rfl⟩ := h
        exact hx
      · exact hlow r c hrc h
    rw [Matrix.det_of_upperTriangular hT]
    exact Finset.prod_eq_zero (Finset.mem_univ ca) ha
  set s : ℂ := if C ca ca = 0 then -(C cb ca)⁻¹ else 0 with hs
  set C' : Matrix (Fin N) (Fin N) ℂ := Matrix.transvection ca cb (-s) * C with hC'
  have hC'o : ∀ r c, r ≠ ca → C' r c = C r c := fun r c hr =>
    Matrix.transvection_mul_apply_of_ne ca cb r c hr (-s) C
  have hC'a : ∀ c, C' ca c = C ca c + -s * C cb c := fun c =>
    Matrix.transvection_mul_apply_same ca cb c (-s) C
  have hC'blk : IsBlockDiag j C' := by
    intro a b hab
    by_cases ha : a = ca
    · subst ha
      rw [hC'a, hC a b hab, hC cb b (by rw [← hblk]; exact hab)]
      ring
    · rw [hC'o a b ha, hC a b hab]
  have hC'low : ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C' r c = 0 := by
    intro r c hrc h
    by_cases hr : r = ca
    · subst hr
      have hcb' : c < cb := lt_trans hrc hlt
      rw [hC'a, hlow _ c hrc (fun h' => hne h'.1),
        hlow cb c hcb' (fun h' => (ne_of_lt hrc) h'.2)]
      ring
    · rw [hC'o r c hr]
      exact hlow r c hrc h
  have hdiag : C' ca ca ≠ 0 := by
    rw [hC'a]
    by_cases ha : C ca ca = 0
    · have hx' := hx ha
      rw [hs, if_pos ha, ha, neg_neg, inv_mul_cancel₀ hx']
      simp
    · rw [hs, if_neg ha]
      simpa using ha
  set t : ℂ := C' cb ca / C' ca ca with ht
  set U : Matrix (Fin N) (Fin N) ℂ := Matrix.transvection cb ca (-t) * C' with hU
  have hUo : ∀ r c, r ≠ cb → U r c = C' r c := fun r c hr =>
    Matrix.transvection_mul_apply_of_ne cb ca r c hr (-t) C'
  have hUb : ∀ c, U cb c = C' cb c + -t * C' ca c := fun c =>
    Matrix.transvection_mul_apply_same cb ca c (-t) C'
  have hUtri : U.BlockTriangular id := by
    intro r c hrc
    change c < r at hrc
    by_cases hr : r = cb
    · subst hr
      rw [hUb]
      by_cases hc : c = ca
      · subst hc
        rw [ht, neg_mul, div_mul_cancel₀ _ hdiag]
        ring
      · have hca : c < ca := by
          rw [Fin.lt_def] at hrc ⊢
          have : (c : ℕ) ≠ ca := fun h => hc (Fin.ext h)
          omega
        rw [hC'low _ c hrc (fun h => hc h.2), hC'low ca c hca (fun h => hne h.1)]
        ring
    · rw [hUo r c hr]
      exact hC'low r c hrc (fun h => hr h.1)
  have hdetU : U.det = C.det := by
    rw [hU, hC', Matrix.det_mul, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ hne',
      Matrix.det_transvection_of_ne _ _ hne, one_mul, one_mul]
  refine ⟨Matrix.transvection ca cb s, U, t, ?_, ?_, ?_, ?_, hUtri, ?_, ?_⟩
  · intro a b hab
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hab' : a ≠ b := fun h => hab (by rw [h])
    rw [if_neg hab']
    by_cases h : ca = a ∧ cb = b
    · obtain ⟨rfl, rfl⟩ := h
      exact absurd hblk hab
    · rw [if_neg h]
      simp
  · intro r c hrc
    change c < r at hrc
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      if_neg (ne_of_gt hrc)]
    have h : ¬ (ca = r ∧ cb = c) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans hrc hlt) (lt_irrefl _)
    rw [if_neg h]
    simp
  · rw [Matrix.det_transvection_of_ne _ _ hne]
    exact one_ne_zero
  · intro a b hab
    by_cases ha : a = cb
    · subst ha
      rw [hUb, hC'blk _ b hab, hC'blk ca b (by rw [hblk]; exact hab)]
      ring
    · rw [hUo a b ha, hC'blk a b hab]
  · intro c
    have hp : ∏ i, U i i ≠ 0 := by
      rw [← Matrix.det_of_upperTriangular hUtri, hdetU]
      exact hdet
    exact Finset.prod_ne_zero_iff.mp hp c (Finset.mem_univ c)
  · change C = Matrix.transvection ca cb s * Matrix.transvection cb ca t * U
    rw [hU, hC', Matrix.mul_assoc (Matrix.transvection ca cb s), ← Matrix.mul_assoc (Matrix.transvection cb ca t),
      Matrix.transvection_mul_transvection_same cb ca hne' t (-t), add_neg_cancel, Matrix.transvection_zero, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.transvection_mul_transvection_same ca cb hne s (-s), add_neg_cancel,
      Matrix.transvection_zero, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.Factor
end
end

