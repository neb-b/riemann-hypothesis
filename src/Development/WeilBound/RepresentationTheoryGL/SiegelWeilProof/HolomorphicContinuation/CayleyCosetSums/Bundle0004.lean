module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyK
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AnalyticAtInverseFirstBlock
section
noncomputable section

open Matrix Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem analyticAt_entryM {ι κ : Type} [Fintype ι] [Fintype κ] (i : ι) (j : κ) (x0 : Matrix ι κ ℂ) :
    AnalyticAt ℂ (fun x : Matrix ι κ ℂ => x i j) x0 := by
  let L : Matrix ι κ ℂ →ₗ[ℂ] ℂ := { toFun := fun x => x i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).analyticAt x0

theorem analyticAt_matrix {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι κ : Type} [Fintype ι] [Fintype κ]
    {F : E → Matrix ι κ ℂ} {x0 : E} (h : ∀ i j, AnalyticAt ℂ (fun x => F x i j) x0) : AnalyticAt ℂ F x0 := by
  exact (analyticAt_pi_iff (f := fun i x => F x i)).mpr fun i =>
    (analyticAt_pi_iff (f := fun j x => F x i j)).mpr fun j => h i j

theorem analyticAt_det_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : E → Matrix ι ι ℂ} {x0 : E} (h : AnalyticAt ℂ F x0) : AnalyticAt ℂ (fun x => (F x).det) x0 := by
  have he : ∀ i j, AnalyticAt ℂ (fun x => F x i j) x0 := fun i j =>
    (analyticAt_entryM i j (F x0)).comp h
  have hs := Finset.analyticAt_sum (c := x0) (Finset.univ : Finset (Equiv.Perm ι))
    (f := fun σ x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, F x (σ i) i)
    (fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i))
  have hfun : (fun x => (F x).det) =
      ∑ σ : Equiv.Perm ι, fun x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, F x (σ i) i := by
    funext x
    simp [Matrix.det_apply', Finset.sum_apply]
  rw [hfun]
  exact hs

theorem analyticAt_inv_entry (x0 : M2 n) (h : x0.det ≠ 0) (i j : Fin n ⊕ Fin n) :
    AnalyticAt ℂ (fun x : M2 n => x⁻¹ i j) x0 := by
  have hadj : AnalyticAt ℂ (fun x : M2 n => x.adjugate i j) x0 := by
    simp only [Matrix.adjugate_apply]
    apply analyticAt_det_comp
    apply analyticAt_matrix
    intro a b
    by_cases ha : a = j
    · subst ha
      simp only [Matrix.updateRow_self]
      exact analyticAt_const
    · simp only [Matrix.updateRow_ne ha]
      exact analyticAt_entryM a b x0
  have hdet : AnalyticAt ℂ (fun x : M2 n => x.det) x0 :=
    analyticAt_det_comp (F := fun x : M2 n => x) analyticAt_id
  have h2 := (hdet.inv h).mul hadj
  have hfun : (fun x : M2 n => x⁻¹ i j) =
      (fun x : M2 n => x.det)⁻¹ * fun x : M2 n => x.adjugate i j := by
    funext x
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hfun]
  exact h2

theorem analyticAt_first_cayley_block (x0 : M2 n) : AnalyticAt ℂ (fun x : M2 n => u1 x) x0 := by
  refine analyticAt_matrix fun a b => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact (analyticAt_const.mul (analyticAt_entryM _ _ x0)).add (analyticAt_entryM _ _ x0)

theorem analyticAt_inverse_first_block (x0 : M2 n) (h : x0.det ≠ 0) : AnalyticAt ℂ (fun x : M2 n => ub1 x) x0 := by
  refine analyticAt_matrix fun a b => ?_
  simp only [ub1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.of_apply, smul_eq_mul]
  exact (analyticAt_inv_entry x0 h _ _).add (analyticAt_const.mul (analyticAt_inv_entry x0 h _ _))

theorem continuousOn_pf : ContinuousOn (fun x : M2 n => (u1 x).det * (ub1 x).det) (Dom n) := by
  intro x hx
  have hd : x.det ≠ 0 := hx.1.ne_zero
  exact ((analyticAt_det_comp (analyticAt_first_cayley_block x)).mul (analyticAt_det_comp (analyticAt_inverse_first_block x hd))).continuousAt.continuousWithinAt

theorem isOpen_domZ : IsOpen (DomZ n) := by
  exact continuousOn_pf.isOpen_inter_preimage isOpen_dom Complex.isOpen_slitPlane

theorem gset_sub_domZ : GSet n ⊆ DomZ n := by
  intro g hg
  have hG : InG g := hg
  have hu : (u1 g).det ≠ 0 := det_first_cayley_block_ne_zero hG
  have hub : ub1 g = (u1 g)ᴴ := inverse_first_block_eq_of_group hG
  have hp : (u1 g).det * (ub1 g).det = ((Complex.normSq (u1 g).det : ℝ) : ℂ) := by
    rw [hub, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj]
  show (IsUnit (det g) ∧ (u1 g).det ≠ 0 ∧ (u2 g).det ≠ 0 ∧ (ub1 g).det ≠ 0) ∧
    (u1 g).det * (ub1 g).det ∈ Complex.slitPlane
  refine ⟨⟨isUnit_det_of_inG hG, hu, det_second_cayley_block_ne_zero hG, ?_⟩, ?_⟩
  · rw [hub, Matrix.det_conjTranspose]
    exact star_ne_zero.mpr hu
  · rw [hp, Complex.ofReal_mem_slitPlane]
    exact Complex.normSq_pos.mpr hu

theorem fzHol : FzHol := by
  intro n m e
  refine ⟨isOpen_domZ, gset_sub_domZ, ?_⟩
  rintro ⟨z, x⟩ ⟨-, hx⟩
  have hx' : (IsUnit (det x) ∧ (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0 ∧ (ub1 x).det ≠ 0) ∧
      (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := hx
  have hdet : x.det ≠ 0 := hx'.1.1.ne_zero
  have hsn : AnalyticAt ℂ (Prod.snd : ℂ × M2 n → M2 n) (z, x) := analyticAt_snd
  have hu1' := AnalyticAt.comp (g := fun y : M2 n => u1 y) (analyticAt_first_cayley_block x) hsn
  have hub1' := AnalyticAt.comp (g := fun y : M2 n => ub1 y) (analyticAt_inverse_first_block x hdet) hsn
  have hu1 : AnalyticAt ℂ (fun q : ℂ × M2 n => u1 q.2) (z, x) := hu1'
  have hub1 : AnalyticAt ℂ (fun q : ℂ × M2 n => ub1 q.2) (z, x) := hub1'
  have hD : AnalyticAt ℂ (fun q : ℂ × M2 n => q.2.det) (z, x) :=
    analyticAt_det_comp (F := fun q : ℂ × M2 n => q.2) hsn
  have hU : AnalyticAt ℂ (fun q : ℂ × M2 n => (u1 q.2).det) (z, x) := analyticAt_det_comp hu1
  have hUb : AnalyticAt ℂ (fun q : ℂ × M2 n => (ub1 q.2).det) (z, x) := analyticAt_det_comp hub1
  have h1 : AnalyticAt ℂ (fun q : ℂ × M2 n => q.2.det ^ e) (z, x) := hD.zpow hdet
  have h2 : AnalyticAt ℂ (fun q : ℂ × M2 n => (u1 q.2).det ^ (-(m : ℤ))) (z, x) :=
    hU.zpow hx'.1.2.1
  have h3 : AnalyticAt ℂ
      (fun q : ℂ × M2 n => ((u1 q.2).det * (ub1 q.2).det) ^ (-q.1)) (z, x) :=
    (hU.mul hUb).cpow analyticAt_fst.neg hx'.2
  exact (h1.mul h2).mul h3

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdProps
section
noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Fd (m : ℕ) (y : M2 n) : ℂ := deriv (fun z : ℂ => fz m 0 z y) 0

def Crux0 : Prop :=
  ∀ (n m : ℕ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∃ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n),
      IsSingTest ψ ∧ InG a ∧ InG b ∧ InG x ∧ deriv (fun z => tOp μ ι (rhoP ι m 0 P) ψ a b (fz m 0 z) x) 0 ≠ 0

def ERed : Prop := Crux0 → Crux

def FdProps : Prop :=
  ∀ (n m : ℕ), ContDiffOn ℂ ⊤ (Fd (n := n) m) (DomZ n) ∧
    ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
      [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
      (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ (ρ : Kg → ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), Continuous ρ →
      Continuous ψ → HasCompactSupport ψ → InG a → InG b → InG x →
      deriv (fun z => tOp μ ι ρ ψ a b (fz m 0 z) x) 0 = tOp μ ι ρ ψ a b (Fd m) x

def DjFd : Prop :=
  ∀ (n m j : ℕ) (x : M2 n), 1 ≤ j → j ≤ n → x ∈ DomZ n →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      Fd m (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
    deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0 *
      hF j m 0 x

def KSplit : Prop :=
  ∀ (n m : ℕ) (a0 b0 : Fin n) (Kg : Type) [Group Kg] (ι : Kg →* M2 n), (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∃ (L : ℕ) (c : Fin L → ℂ) (kl : Fin L → Kg), ∀ k,
      fV m 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k)) b0 a0 = ∑ l, c l * rhoP ι m 0 1 (k * kl l)

def SphU : Prop :=
  ∀ (n : ℕ) (F : M2 n → ℂ) (U : Set (M2 n)), IsOpen U → ContDiffOn ℂ ⊤ F U →
    ∀ {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n), Continuous ι →
    ∀ (c : Kg → ℂ), Continuous c → ∀ {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (LA : M2 n → Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : M2 n → Matrix ιB ιB ℂ →L[ℂ] M2 n),
    (∀ M x T, LA (M * x) T = M * LA x T) → (∀ M x S, LB (M * x) S = M * LB x S) →
    ∀ (g : M2 n), (∀ k, ι k * g ∈ U) →
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ)) =
      ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k ∂μ

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FderivDeterminantPowerColumnNeg
section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CKC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK

variable {N : ℕ}

def Hc (N : ℕ) (t : ℂ) (T : Matrix (Fin N) (Fin N) ℂ) : ℂ := (1 + T).det ^ t

theorem analyticAt_Hc (N : ℕ) (t : ℂ) (T0 : Matrix (Fin N) (Fin N) ℂ) (h : (1 + T0).det ∈ Complex.slitPlane) :
    AnalyticAt ℂ (Hc N t) T0 := by
  unfold Hc
  have h1 : AnalyticAt ℂ (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det) T0 :=
    (CK.analyticAt_det (1 + T0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.cpow analyticAt_const h

theorem one_det_slit : (1 + (0 : Matrix (Fin N) (Fin N) ℂ)).det ∈ Complex.slitPlane := by
  simpa using Complex.one_mem_slitPlane

theorem analyticAt_determinant_power_zero (N : ℕ) (t : ℂ) : AnalyticAt ℂ (Hc N t) 0 := analyticAt_Hc N t 0 one_det_slit

theorem det_phiF_slit (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane) :
    (1 + phiF X).det ∈ Complex.slitPlane := by rw [det_phiF]; exact hX

theorem fderiv_determinant_power_corner (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane) :
    fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 0 1) = t * Hc N t (piF X) := by
  have hD := det_phiF_slit X hX
  have h1 := fderiv_line (Hc (N + 1) t) (phiF X) (Matrix.single 0 0 1) (analyticAt_Hc _ t _ hD).differentiableAt
  have hD0 : (1 + piF X).det ≠ 0 := Complex.slitPlane_ne_zero hX
  have hfun : (fun s : ℂ => Hc (N + 1) t (phiF X + s • Matrix.single 0 0 1))
      = fun s : ℂ => ((1 + s) * (1 + piF X).det) ^ t := by
    funext s
    simp only [Hc]
    rw [← add_assoc, det_corner_perturbation]
  rw [hfun] at h1
  have hf : HasDerivAt (fun s : ℂ => (1 + s) * (1 + piF X).det) (1 * (1 + piF X).det) 0 :=
    ((hasDerivAt_id' (0 : ℂ)).const_add 1).mul_const _
  have h2 := hf.cpow_const (c := t) (by simpa using hX)
  refine (h1.unique h2).trans ?_
  simp only [Hc, add_zero, one_mul]
  rw [Complex.cpow_sub _ _ hD0, Complex.cpow_one]
  field_simp

theorem fderiv_determinant_power_column_neg (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane)
    (c : Fin N) :
    fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = -fderiv ℂ (Hc N t) (piF X) (colQ X c) := by
  have hA : AnalyticAt ℂ (Hc (N + 1) t) (phiF X) := analyticAt_Hc _ t _ (det_phiF_slit X hX)
  have h1 := fderiv_line (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) hA.differentiableAt
  have e : (fun s : ℂ => Hc (N + 1) t (phiF X + s • Matrix.single 0 c.succ 1)) =
      fun s : ℂ => Hc N t (piF X + s • (-colQ X c)) := by
    funext s
    simp only [Hc]
    rw [← add_assoc, det_column_perturbation, smul_neg, ← sub_eq_add_neg, add_sub_assoc]
  rw [e] at h1
  have hB : AnalyticAt ℂ (Hc N t) (piF X) := analyticAt_Hc _ t _ hX
  have h2 := fderiv_line (Hc N t) (piF X) (-colQ X c) hB.differentiableAt
  exact (h1.unique h2).trans (map_neg _ _)

theorem ev_piFc (N : ℕ) :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin N) (Fin (N + 1)) ℂ), (1 + piF X).det ∈ Complex.slitPlane := by
  have hc : ContinuousAt (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => (1 + piF X).det) 0 :=
    ((PositivityTheory.Rg.Sw.LVs.CK.analyticAt_det _).comp (analyticAt_const.add (analyticAt_piF 0))).continuousAt
  have h0 : (1 + piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)).det ∈ Complex.slitPlane := by
    rw [piF_zero, add_zero, Matrix.det_one]
    exact Complex.one_mem_slitPlane
  exact hc.eventually_mem (Complex.isOpen_slitPlane.mem_nhds h0)

theorem iterated_derivative_corner_case (t : ℂ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      t * iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
  set G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → ℂ :=
    fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 0 1) with hG
  have hGa : AnalyticAt ℂ G 0 := analyticAt_fderiv_apply (Hc (N + 1) t) 0 _ (analyticAt_determinant_power_zero (N + 1) t)
  have e1 := icompL G phiF phiF_add phiF_smul 0 0 phiF_zero hGa N
    (fun k => Matrix.single k (e k).succ 1) (fun k => Matrix.single k.succ (e k).succ 1)
    (fun i => phiF_single _ _)
  rw [← e1]
  have hev : (G ∘ phiF) =ᶠ[𝓝 0] (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => t * Hc N t (piF X)) := by
    filter_upwards [ev_piFc N] with X hX
    exact fderiv_determinant_power_corner t X hX
  rw [(hev.iteratedFDeriv ℂ N).eq_of_nhds]
  have hHa : AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => Hc N t (piF X)) 0 := by
    have h0 : AnalyticAt ℂ (Hc N t) (piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)) := by
      rw [piF_zero]
      exact analyticAt_determinant_power_zero N t
    exact h0.comp (analyticAt_piF 0)
  rw [iconst_mul _ 0 t hHa N]
  congr 1
  exact icompL (Hc N t) piF piF_add piF_smul 0 0 piF_zero (analyticAt_determinant_power_zero N t) N
    (fun k => Matrix.single k (e k).succ 1) (fun k => Matrix.single k (e k) 1)
    (fun i => piF_single_succ _ _)

def fsumc (t : ℂ) (c : Fin N) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : ℂ :=
  -∑ k, X k 0 * fderiv ℂ (Hc N t) (piF X) (Matrix.single k c 1)

theorem fderiv_determinant_power_column (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane)
    (c : Fin N) : fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsumc t c X := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fderiv_determinant_power_column_neg t X hX c, colQ_expand, map_sum]
  simp only [map_smul, smul_eq_mul, fsumc]

theorem analyticAt_fsumc (t : ℂ) (c : Fin N) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ)
    (h : (1 + piF X0).det ∈ Complex.slitPlane) : AnalyticAt ℂ (fsumc t c) X0 := by
  have hs := Finset.analyticAt_sum
    (f := fun k (X : Matrix (Fin N) (Fin (N + 1)) ℂ) => X k 0 * fderiv ℂ (Hc N t) (piF X) (Matrix.single k c 1))
    Finset.univ (fun k _ => (analyticAt_entry k 0 X0).mul
      ((analyticAt_fderiv_apply (Hc N t) (piF X0) _ (analyticAt_Hc N t _ h)).comp (analyticAt_piF X0)))
  rw [Finset.sum_fn] at hs
  exact hs.neg

theorem fsum_linec (t : ℂ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    fsumc t c (y + s • Matrix.single k0 0 1) =
      fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
  simp only [fsumc]
  rw [piF_add, piF_smul, piF_single_zero, smul_zero, add_zero]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply, and_true, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem fderiv_fsumc (t : ℂ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ)
    (hy : (1 + piF y).det ∈ Complex.slitPlane) :
    fderiv ℂ (fsumc t c) y (Matrix.single k0 0 1) = -fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
  have h1 := fderiv_line (fsumc t c) y (Matrix.single k0 0 1) (analyticAt_fsumc t c y hy).differentiableAt
  have hfun : (fun s : ℂ => fsumc t c (y + s • Matrix.single k0 0 1))
      = fun s : ℂ => fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
    funext s
    exact fsum_linec t c k0 y s
  rw [hfun] at h1
  have h2 : HasDerivAt (fun s : ℂ => fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1))
      (0 - 1 * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1)) 0 :=
    (hasDerivAt_const _ _).sub ((hasDerivAt_id' (0 : ℂ)).mul_const _)
  refine (h1.unique h2).trans ?_
  ring

end PositivityTheory.Rg.Sw.HSt.CKC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqConjTranspose
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

theorem inv_of_inG {x : M2 n} (hx : InG x) : x⁻¹ = -(JJ n * xᴴ * JJ n) := by
  refine Matrix.inv_eq_left_inv ?_
  have h : xᴴ * JJ n * x = JJ n := hx
  calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
    _ = 1 := by rw [h, JJ_sq]; simp

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x := by
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have h : xᴴ * JJ n * x = JJ n := hx
    calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
      _ = 1 := by rw [h, JJ_sq]; simp
  exact (Matrix.isUnit_iff_isUnit_det x).mpr (Matrix.isUnit_det_of_left_inverse h)

theorem isUnit_det_of_inG {x : M2 n} (hx : InG x) : IsUnit x.det :=
  (Matrix.isUnit_iff_isUnit_det x).mp (isUnit_of_inG hx)

theorem inverse_first_block_eq_conjTranspose {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ := by
  rw [ub1, inv_of_inG hx, u1]
  conv_lhs => rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁]
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, sub_eq_add_neg]
  abel

theorem det_first_block_ne_zero_group {x : M2 n} (hx : InG x) : (u1 x).det ≠ 0 := by
  have := PositivityTheory.Rg.Sw.AbsSt.IwaPf.det_ne x hx Complex.I (by simp [Complex.ext_iff]; norm_num)
  simpa [u1] using this

def Nq (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks 0 Q 0 0 * Cmi n

theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.mp cm_mul_cmi

theorem Nq_sq (Q : Matrix (Fin n) (Fin n) ℂ) : Nq Q * Nq Q = 0 := by
  have : fromBlocks 0 Q 0 0 * fromBlocks 0 Q 0 0 = (0 : M2 n) := by
    rw [fromBlocks_multiply]; simp [fromBlocks_zero]
  calc Nq Q * Nq Q = Cm n * fromBlocks 0 Q 0 0 * (Cmi n * Cm n) * fromBlocks 0 Q 0 0 * Cmi n := by
        simp only [Nq, Matrix.mul_assoc]
    _ = 0 := by rw [cmi_mul_cm, Matrix.mul_one, Matrix.mul_assoc (Cm n), this]; simp

theorem mX_eq (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : mX (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 = 1 + s • Nq Q := by
  have e : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 : M2 n) = 1 + s • (fromBlocks 0 Q 0 0 : M2 n) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  rw [mX, cm_inv, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, Nq, Matrix.mul_smul, Matrix.smul_mul]

theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Nq Q := by
  have := mX_eq Q 1
  rw [one_smul, one_smul] at this
  rw [lowQ, this]; abel

theorem Nq_blocks (Q : Matrix (Fin n) (Fin n) ℂ) :
    Nq Q = fromBlocks (-(1 / 2 : ℂ) • Q) ((Complex.I / 2) • Q) ((Complex.I / 2) • Q) ((1 / 2 : ℂ) • Q) := by
  rw [Nq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem inv_mul_lower {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    (x * (1 + s • Nq Q))⁻¹ = (1 - s • Nq Q) * x⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  have hN := Nq_sq Q
  have e : (1 + s • Nq Q) * (1 - s • Nq Q) = (1 : M2 n) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN]
    simp
  have hx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x ((Matrix.isUnit_iff_isUnit_det x).mp hx)
  calc x * (1 + s • Nq Q) * ((1 - s • Nq Q) * x⁻¹) = x * ((1 + s • Nq Q) * (1 - s • Nq Q)) * x⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e, Matrix.mul_one, hx']

theorem upper_left_block_sub (A B : M2 n) : (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
theorem lower_left_block_sub (A B : M2 n) : (A - B).toBlocks₂₁ = A.toBlocks₂₁ - B.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
theorem upper_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
theorem lower_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₂₁ = c • A.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
theorem upper_left_block_mul_eq (A B : M2 n) : (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem inverse_first_block_lowering {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    ub1 (x * (1 + s • Nq Q)) = ub1 x - s • (Q * ub2 x) := by
  rw [ub1, inv_mul_lower hx, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, upper_left_block_sub, lower_left_block_sub, upper_left_block_smul,
    lower_left_block_smul, upper_left_block_mul_eq, toBlocks₂₁_mul, Nq_blocks, ub1, ub2]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.smul_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, smul_add, smul_sub, smul_neg, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem first_block_lowering_invariant (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : u1 (x * (1 + s • Nq Q)) = u1 x := by
  have := (uAct n x 1 (s • Q) 0 1).1
  rw [mX_eq] at this
  rw [this]; simp

theorem det_lower (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : (x * (1 + s • Nq Q)).det = x.det := by
  rw [← mX_eq, det_mul, mX, cm_inv, det_mul, det_mul, det_fromBlocks_zero₂₁]
  have : (Cm n).det * (Cmi n).det = 1 := by rw [← det_mul, cm_mul_cmi, det_one]
  simp only [det_one, mul_one]
  linear_combination x.det * this

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
end
end

