module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSliceSmoothAndMatrixUnitAction
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Matrix Topology
open scoped ContDiff

namespace GlobalTheory.LeviSliceGA

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

def lowL (hr : r ≤ a) : Lie E (a - r) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr) (GlobalTheory.LeviGA.blkEquiv hr)
        (Matrix.fromBlocks 0 0 0 (Matrix.of y)))
      map_add' := fun y z => by
        funext i j
        obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
        obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
        rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply]
      map_smul' := fun c y => by
        funext i j
        obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
        obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
        rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply] }

theorem lowL_apply (hr : r ≤ a) (y : Lie E (a - r)) : lowL hr y = toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr)
    (GlobalTheory.LeviGA.blkEquiv hr) (Matrix.fromBlocks 0 0 0 (Matrix.of y))) := rfl

def affA (hr : r ≤ a) (y : Lie E (a - r)) : Lie E a :=
  lowL hr y + toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr) (GlobalTheory.LeviGA.blkEquiv hr) (Matrix.fromBlocks 1 0 0 0))

theorem affA_val (hr : r ≤ a) (u : GL (Fin (a - r)) (Cinf E)) :
    affA hr (toL u.val) = toL (GlobalTheory.LeviGA.blkGL hr (1, u)).val := by
  rw [affA, lowL_apply, GlobalTheory.LeviGA.blkGL_val]
  funext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply]

theorem infGL_apply {n : ℕ} (g : GL (Fin n) (Cinf E)) (i j : Fin n) :
    (infGL E n g : Matrix (Fin n) (Fin n) (Ad E)) i j = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j -
      sInf E ((1 : Matrix (Fin n) (Fin n) (Cinf E)) i j) + sInf E ((g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := rfl

theorem blkGL_infGL (hr : r ≤ a) (u : GL (Fin (a - r)) (Cinf E)) :
    GlobalTheory.LeviGA.blkGL hr ((1 : GA E r), infGL E (a - r) u) = infGL E a (GlobalTheory.LeviGA.blkGL hr (1, u)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rw [GlobalTheory.LeviGA.blkGL_apply, infGL_apply, GlobalTheory.LeviGA.blkGL_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, (GlobalTheory.LeviGA.blkEquiv hr).injective.eq_iff, infGL_apply]

theorem chart_slice (hr : r ≤ a) (m₁ : GA E r) (φ : GA E a → ℂ) (m₂ : GA E (a - r)) {y : Lie E (a - r)}
    (hy : y ∈ invSet E (a - r)) :
    chart (fun m : GA E (a - r) => φ (GlobalTheory.LeviGA.blkGL hr (m₁, m))) m₂ y =
      chart φ (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) (affA hr y) := by
  obtain ⟨u, hu⟩ := hy
  have e : y = toL u.val := hu.symm
  subst e
  rw [chart_val, affA_val, chart_val, ← blkGL_infGL, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem affA_one (hr : r ≤ a) : affA hr (oneL E (a - r)) = oneL E a := by
  have h := affA_val (E := E) hr 1
  rw [show ((1 : GL (Fin r) (Cinf E)), (1 : GL (Fin (a - r)) (Cinf E))) = 1 from rfl, map_one] at h
  exact h

theorem hasFDerivAt_affA (hr : r ≤ a) (y : Lie E (a - r)) : HasFDerivAt (affA hr) (lowL (E := E) hr) y :=
  (lowL hr).hasFDerivAt.add_const _

theorem lowL_single (hr : r ≤ a) (p p' : Fin (a - r)) (x : Cinf E) :
    lowL hr (toL (Matrix.single p p' x)) =
      toL (Matrix.single (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) x) := by
  rw [lowL_apply]
  funext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [toL, Matrix.reindex_apply, Matrix.single_apply, (GlobalTheory.LeviGA.blkEquiv hr).injective.eq_iff] <;>
    by_cases hi : i = p <;> by_cases hj : j = p' <;> simp [hi, hj, Pi.single_apply] <;> intros <;> simp_all

theorem slice_mem_Sm (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a) :
    (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) := fun m₂ =>
  ((f.2 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))).comp ((lowL (E := E) hr).contDiff.add contDiff_const).contDiffOn
    (fun y hy => by
      obtain ⟨u, hu⟩ := hy
      have e : y = toL u.val := hu.symm
      subst e
      show affA hr _ ∈ _
      rw [affA_val]
      exact val_mem_invSet _)).congr fun y hy => chart_slice hr m₁ f.1 m₂ hy

theorem lieS_slice (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a) (p p' : Fin (a - r)) (ψ : Sm E (a - r))
    (hψ : ψ.1 = fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) (x : Cinf E) (m₂ : GA E (a - r)) :
    (lieS E (a - r) p p' x ψ).1 m₂ =
      (lieS E a (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) x f).1
        (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  rw [GlobalTheory.CuspRep.lieS_apply, GlobalTheory.CuspRep.lieS_apply, GlobalTheory.CuspRep.lie_apply, GlobalTheory.CuspRep.lie_apply, lieD, lieD, hψ]
  have ev : chart (fun m : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m))) m₂ =ᶠ[𝓝 (oneL E (a - r))]
      chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) ∘ affA hr :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun y hy => chart_slice hr m₁ f.1 m₂ hy
  have hd : HasFDerivAt (chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)))
      (fderiv ℝ (chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) (oneL E a)) (affA hr (oneL E (a - r))) := by
    rw [affA_one]; exact (differentiableAt_chart f.2 _).hasFDerivAt
  rw [ev.fderiv_eq, (hd.comp (oneL E (a - r)) (hasFDerivAt_affA hr _)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, lowL_single]

theorem slice_smooth_Eop : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    (m₁ : GA E r) (f : Sm E a),
    (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) ∧
      ∀ (τ : E →+* ℂ) (p p' : Fin (a - r)) (ψ : Sm E (a - r)),
        ψ.1 = (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) →
        (Eop τ p p' ψ).1 = fun m₂ : GA E (a - r) =>
          (Eop τ (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) f).1
            (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  intro E _ _ _ a r hr m₁ f
  refine ⟨slice_mem_Sm hr m₁ f, fun τ p p' ψ hψ => funext fun m₂ => ?_⟩
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, lieS_slice hr m₁ f p p' ψ hψ]

end GlobalTheory.LeviSliceGA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLe
section
open Formalism.BasicNotions

namespace GlobalTheory.BranchBound

theorem branching_D1_le_weight_difference (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ lam.w 0 - lam.w (Fin.last n) := by
  let g : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0
  have h1 : Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ ∑ i : Fin n, (g i - g (i + 1)) := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.D1
    refine Finset.sum_le_sum fun i _ => ?_
    have a : g i = lam.w ⟨i.1, by omega⟩ := by simp [g, show i.1 < n + 1 by omega]
    have b : g (i + 1) = lam.w ⟨i.1 + 1, by omega⟩ := by simp [g, show i.1 + 1 < n + 1 by omega]
    rw [a, b]
    exact min_le_left _ _
  have h2 : ∑ i : Fin n, (g i - g (i + 1)) = g 0 - g n := by
    rw [Fin.sum_univ_eq_sum_range (fun k => g k - g (k + 1)) n]
    exact Finset.sum_range_sub' g n
  have a0 : g 0 = lam.w 0 := by simp [g]
  have an : g n = lam.w (Fin.last n) := by simp [g]; rfl
  rw [h2, a0, an] at h1
  exact h1

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

theorem finrank_delSq_le (N : ℕ) (lam : DomWeight N) (B : ℝ) (hB : 1 ≤ B)
    (hw : ∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) :
    (Module.finrank ℂ (delSq ℂ N lam) : ℝ) ≤ (6 * B) ^ (N * N) := by
  have hq := GlobalTheory.WeylDimGL.finrank_delSq ℂ N lam
  rw [GlobalTheory.WeylDimGL.weylDim_eq_prod_Ioi] at hq
  have hr : (Module.finrank ℂ (delSq ℂ N lam) : ℝ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) := by
    have := congrArg (Rat.cast : ℚ → ℝ) hq
    push_cast at this
    exact this
  rw [hr]
  have h6 : (1 : ℝ) ≤ 6 * B := by linarith
  have hf : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i,
      0 ≤ ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ∧
      ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ≤ 6 * B := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hlt : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have hanti : (lam.w j : ℝ) ≤ lam.w i := by exact_mod_cast lam.anti hij.le
    have hbi := abs_le.mp (hw i)
    have hbj := abs_le.mp (hw j)
    have hk : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by linarith
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_iff₀ hk]
      nlinarith
  calc ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ ∏ _i : Fin N, (6 * B) ^ N := by
          refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j hj => (hf i j hj).1) fun i _ => ?_
          calc _ ≤ ∏ _j ∈ Finset.Ioi i, (6 * B) :=
                Finset.prod_le_prod₀ (fun j hj => (hf i j hj).1) fun j hj => (hf i j hj).2
            _ = (6 * B) ^ (Finset.Ioi i).card := Finset.prod_const _
            _ ≤ (6 * B) ^ N := by
                apply pow_le_pow_right₀ h6
                simpa using Finset.card_le_univ (Finset.Ioi i)
      _ = (6 * B) ^ (N * N) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

theorem log_brBd_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B →
    (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) →
    Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  intro n N h lam sg B hB hN hw
  subst h
  have hNB : ((n + 1 : ℕ) : ℝ) ≤ B := hN
  have hN0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hL : 0 < Real.log (6 * B) := Real.log_pos (by linarith)
  have hR : 0 ≤ 5 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity

  have hsp : lam.spread = lam.w 0 - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℤ) := by
    unfold DomWeight.spread
    rw [dite_eq_left (Nat.succ_pos n)]
    rfl
  have h0 := abs_le.mp (hw 0)
  have hl := abs_le.mp (hw (Fin.last n))
  have hanti : (lam.w (Fin.last n) : ℝ) ≤ lam.w 0 := by exact_mod_cast lam.anti (Fin.zero_le _)
  set s : ℝ := (((2 * lam.spread : ℤ)) : ℝ) with hs
  have hsR : s = 2 * ((lam.w 0 : ℝ) - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℝ)) := by
    rw [hs, hsp]; push_cast; ring
  have hs2 : 2 ≤ s := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hs6 : s ≤ 6 * B := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hls0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hls : Real.log s ≤ Real.log (6 * B) := Real.log_le_log (by linarith) hs6

  have hD := branching_D1_le_weight_difference n lam sg
  have hDR : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ 2 * B := by
    have : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ (lam.w 0 : ℝ) - lam.w (Fin.last n) := by exact_mod_cast hD
    linarith
  set e : ℝ := ((((n + 1 : ℕ) : ℤ) * Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) with he
  have heR : e = ((n + 1 : ℕ) : ℝ) * ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) := by rw [he]; push_cast; ring
  have hel : e * Real.log s ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    rcases le_or_gt e 0 with he0 | he0
    · have : e * Real.log s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he0 hls0
      have : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity
      linarith
    · have he2 : e ≤ 2 * ((n + 1 : ℕ) : ℝ) * B := by
        rw [heR]; nlinarith
      calc e * Real.log s ≤ (2 * ((n + 1 : ℕ) : ℝ) * B) * Real.log (6 * B) :=
            mul_le_mul he2 hls hls0 (by positivity)
        _ = _ := by ring

  have hc : Formalism.MainNotions.PrimeDegreeVariant.cBd rfl lam sg = s ^ e := rfl
  have hcpos : 0 < s ^ e := Real.rpow_pos_of_pos (by linarith) e
  set d : ℝ := (Module.finrank ℂ (delSq ℂ (n + 1) lam) : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  have hb2 : Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 = (s ^ e) ^ 2 * d := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.brBd
    rw [hc, mul_pow, Real.sq_sqrt hd0]
  rw [hb2]
  rcases eq_or_lt_of_le hd0 with hd0' | hdpos
  · rw [← hd0', mul_zero, Real.log_zero]; exact hR
  have hdle := finrank_delSq_le (n + 1) lam B hB hw
  have hlogd : Real.log d ≤ (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (6 * B) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hdpos hdle
  have hlogd' : Real.log d ≤ ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    refine hlogd.trans ?_
    push_cast
    have : (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * B := by
      push_cast at hNB hN0
      exact mul_le_mul_of_nonneg_left hNB hN0
    nlinarith
  rw [Real.log_mul (by positivity) hdpos.ne', Real.log_pow, Real.log_rpow (by linarith)]
  push_cast at hel hlogd' ⊢
  nlinarith

end GlobalTheory.BranchBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitOpUpperBlockLeviEqZero
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviGA

open Matrix

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem mul_mul_upper {R : Type} [CommRing R] (A N B : Matrix (Fin a) (Fin a) R)
    (hA : ∀ k p : Fin a, ((k : ℕ) < r ↔ (p : ℕ) < r) ∨ A k p = 0)
    (hB : ∀ q l : Fin a, ((q : ℕ) < r ↔ (l : ℕ) < r) ∨ B q l = 0)
    (hN : ∀ p q : Fin a, ¬((p : ℕ) < r ∧ r ≤ (q : ℕ)) → N p q = 0)
    (k l : Fin a) (hkl : ¬((k : ℕ) < r ∧ r ≤ (l : ℕ))) : (A * N * B) k l = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hpq : (p : ℕ) < r ∧ r ≤ (q : ℕ)
  · rcases hA k p with h1 | h1
    · rcases hB q l with h2 | h2
      · exact absurd ⟨h1.2 hpq.1, by by_contra h; exact absurd (h2.2 (by omega)) (by omega)⟩ hkl
      · rw [h2, mul_zero]
    · rw [h1, zero_mul, zero_mul]
  · rw [hN p q hpq, mul_zero, zero_mul]

theorem lieD_single_blkGL (hr : r ≤ a) (f : Sm E a)
    (hf : ∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g)
    (i j : Fin a) (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) (p : GA E r × GA E (a - r)) (x : Cinf E) :
    lieD (toL (Matrix.single i j x)) f.1 (blkGL hr p) = 0 := by
  set m : GA E a := blkGL hr p with hm
  set S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.single i j x with hS
  have hij : j ≠ i := fun h => by rw [h] at hj; omega
  have hSS : S * S = 0 := by rw [hS]; simp [hij, hij.symm]
  let c : ℝ → GL (Fin a) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by simp [mul_sub, add_mul, smul_mul_smul_comm, hSS],
      by simp [sub_mul, mul_add, smul_mul_smul_comm, hSS]⟩
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hc : HasDerivAt (fun t => toL (c t).val) (toL S) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add (toL (1 : Matrix (Fin a) (Fin a) (Cinf E)))
    rw [one_smul] at this
    exact this
  have hd := hasDerivAt_curve f m c (toL S) h0 hc

  have hconst : ∀ t, f.1 (m * infGL E a (c t)) = f.1 m := by
    intro t
    set N : Matrix (Fin a) (Fin a) (Ad E) := matN a (sInf E) (t • S) with hN
    have hinf : (infGL E a (c t)).val = 1 + N := by
      change 1 - matN a (sInf E) 1 + matN a (sInf E) (1 + t • S) = 1 + N
      rw [map_add (f := _)]; abel
    have hNsupp : ∀ p q : Fin a, ¬((p : ℕ) < r ∧ r ≤ (q : ℕ)) → N p q = 0 := by
      intro p q hpq
      have : (t • S) p q = 0 := by
        rw [hS, Matrix.smul_apply]
        by_cases e : p = i ∧ q = j
        · exact absurd (by rw [e.1, e.2]; exact ⟨hi, hj⟩) hpq
        · rw [Matrix.single_apply_of_ne (h := by tauto), smul_zero]
      change sInf E ((t • S) p q) = 0
      rw [this, map_zero]
    have hinv : m⁻¹ = blkGL hr p⁻¹ := by rw [hm, map_inv]
    let y : BlockIx a r → Ad E := fun q => (m.val * N * (m⁻¹).val) q.1.1 q.1.2
    have hy : nilM y = m.val * N * (m⁻¹).val := by
      ext k l
      simp only [nilM, Matrix.of_apply, y]
      split_ifs with h
      · rfl
      · exact (mul_mul_upper _ _ _ (blkGL_block hr p) (by rw [hinv]; exact blkGL_block hr _) hNsupp k l h).symm
    have e : m * infGL E a (c t) = unip y * m := by
      apply Units.ext
      change m.val * (infGL E a (c t)).val = (1 + nilM y) * m.val
      rw [hinf, hy, add_mul, one_mul, mul_add, mul_one, mul_assoc _ _ m.val,
        Units.inv_mul, mul_one]
    rw [e, hf]
  have hfun : (fun t => f.1 (m * infGL E a (c t))) = fun _ => f.1 m := funext hconst
  rw [hfun] at hd
  exact hd.unique (hasDerivAt_const 0 _)

theorem Eop_upper_blkGL_eq_zero :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a),
        (i : ℕ) < r → r ≤ (j : ℕ) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)),
          (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  intro E _ _ _ a r hr f hf τ i j hi hj m₁ m₂
  have key : ∀ x : Cinf E, (lieS E a i j x f).1 (blkGL hr (m₁, m₂)) = 0 := fun x =>
    lieD_single_blkGL hr f hf i j hi hj (m₁, m₂) x
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, key, smul_zero, sub_zero]

end GlobalTheory.LeviGA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfDuplicationEq
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_duplication_eq :
    ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W →
      W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V →
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) →
      x ∈ V ∧ y ∈ V := by
  intro V W x y δ hW hE hl hδ h
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  have hr : ∀ z : ℂ, z ∈ V → z ∈ (algebraMap V ℂ).range := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have hr' : ∀ z : ℂ, z ∈ (algebraMap V ℂ).range → z ∈ V := by
    rintro z ⟨w, rfl⟩; exact w.2
  have hb₄ : W.b₄ ∈ V := by
    rw [WeierstrassCurve.b₄]
    exact add_mem (mul_mem (ofNat_mem V 2) h₄) (mul_mem h₁ h₃)
  have hb₆ : W.b₆ ∈ V := by
    rw [WeierstrassCurve.b₆]
    exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem V 4) h₆)
  have hb₈ : W.b₈ ∈ V := by
    rw [WeierstrassCurve.b₈]
    refine sub_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · exact mul_mem (pow_mem h₁ 2) h₆
    · exact mul_mem (mul_mem (ofNat_mem V 4) h₂) h₆
    · exact mul_mem (mul_mem h₁ h₃) h₄
    · exact mul_mem h₂ (pow_mem h₃ 2)
    · exact pow_mem h₄ 2
  set l := 2 * y + W.a₁ * x + W.a₃ with hl_def
  have hx : x ∈ V := by
    refine hr' x (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := -(W.b₈ + l ^ 2 * δ))
      (c₁ := -(2 * W.b₆ + l ^ 2)) (c₂ := -W.b₄) (c₃ := 0) (hr _ ?_) (hr _ ?_) (hr _ ?_) (hr _ ?_) ?_)
    · exact neg_mem (add_mem hb₈ (mul_mem (pow_mem hl 2) hδ))
    · exact neg_mem (add_mem (mul_mem (ofNat_mem V 2) hb₆) (pow_mem hl 2))
    · exact neg_mem hb₄
    · exact zero_mem V
    · linear_combination h
  refine ⟨hx, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  refine hr' y (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := 0) (c₁ := 0)
    (c₂ := -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) (c₃ := W.a₁ * x + W.a₃)
    (hr _ (zero_mem V)) (hr _ (zero_mem V)) (hr _ ?_) (hr _ ?_) ?_)
  · exact neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3)
      (mul_mem h₂ (pow_mem hx 2))) (mul_mem h₄ hx)) h₆)
  · exact add_mem (mul_mem h₁ hx) h₃
  · linear_combination y ^ 2 * hE

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortTwistFourMulAddOne
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem modelAt_shortTwist_four_mul_add_one : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  intro V F a₄ a₆ D k _ _ h
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  set d : ℂ := 4 * (k : ℂ) + 1 with hd
  have hkV : (k : ℂ) ∈ V := intCast_mem V k
  have hdV : d ∈ V := add_mem (mul_mem (by exact_mod_cast intCast_mem V 4 : (4 : ℂ) ∈ V) hkV) (one_mem V)
  have hkF : (k : ℂ) ∈ F := by simpa using IntermediateField.intCast_mem F k
  have hdF : d ∈ F := F.add_mem (F.mul_mem (by simpa using IntermediateField.intCast_mem F 4) hkF) F.one_mem
  let W₀ : WeierstrassCurve ℂ := ⟨0, 0, 0, a₄, a₆⟩
  let C' : VariableChange ℂ := ⟨C.u, d * C.r, C.s, d * C.t⟩
  refine ⟨C', hu, F.mul_mem hdF hr, hs, F.mul_mem hdF ht, ?_, ?_⟩
  · have e1 : (C' • shortTwist d a₄ a₆).a₁ = (C • W₀).a₁ := by
      simp only [variableChange_a₁, shortTwist, W₀, C']
    have e2 : (C' • shortTwist d a₄ a₆).a₂ = d * (C • W₀).a₂ + k * (C • W₀).a₁ ^ 2 := by
      simp only [variableChange_a₁, variableChange_a₂, shortTwist, W₀, C', hd]; ring
    have e3 : (C' • shortTwist d a₄ a₆).a₃ = d * (C • W₀).a₃ := by
      simp only [variableChange_a₃, shortTwist, W₀, C']; ring
    have e4 : (C' • shortTwist d a₄ a₆).a₄ = d ^ 2 * (C • W₀).a₄ + 2 * k * d * (C • W₀).a₁ * (C • W₀).a₃ := by
      simp only [variableChange_a₁, variableChange_a₃, variableChange_a₄, shortTwist, W₀, C', hd]; ring
    have e6 : (C' • shortTwist d a₄ a₆).a₆ = d ^ 3 * (C • W₀).a₆ + k * d ^ 2 * (C • W₀).a₃ ^ 2 := by
      simp only [variableChange_a₃, variableChange_a₆, shortTwist, W₀, C', hd]; ring
    have h2V : (2 : ℂ) ∈ V := by simpa using intCast_mem V 2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e1]; exact h1
    · rw [e2]; exact add_mem (mul_mem hdV h2) (mul_mem hkV (pow_mem h1 2))
    · rw [e3]; exact mul_mem hdV h3
    · rw [e4]; exact add_mem (mul_mem (pow_mem hdV 2) h4)
        (mul_mem (mul_mem (mul_mem (mul_mem h2V hkV) hdV) h1) h3)
    · rw [e6]; exact add_mem (mul_mem (pow_mem hdV 3) h6)
        (mul_mem (mul_mem hkV (pow_mem hdV 2)) (pow_mem h3 2))
  · have eΔ : (C' • shortTwist d a₄ a₆).Δ = d ^ 6 * (C • W₀).Δ := by
      rw [variableChange_Δ, variableChange_Δ]
      simp only [C', W₀, shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [eΔ, map_mul, map_mul, hΔ]

end GlobalTheory.CMModel
end

