module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0174
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0063
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0181
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationEstimateExpansionTensorBdRComponent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModule

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIff
section
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK.XiTriv
theorem frobA : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := _root_.GlobalTheory.BK.frob_mem_R_of_mem_invE_A
theorem limR : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧), (∀ n, s n ∈ R O K l k) → (∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n) → Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0) → f ∈ R O K l k := GlobalTheory.T.mem_rigidFunctionsClosedDisc_of_adic_limit
theorem growth : ∀ (C r : ℝ) (l : ℕ), 0 ≤ C → 0 ≤ r → r < 1 → 2 ≤ l → Tendsto (fun n : ℕ => C ^ n * r ^ (l ^ n)) atTop (𝓝 0) := _root_.GlobalTheory.tendsto_const_pow_mul_pow_pow_zero
theorem decay : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := _root_.GlobalTheory.BK.frob_recursion_decay

theorem convB : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧) (Y : ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ n τ i j, (X : K⟦X⟧) ^ (n + 1) ∣ Y τ i j - Z n τ i j) → ∀ τ i j, Y τ i j ∈ R O K l k := by
  intro O K _ _ _ _ _ l a _ _ ι _ _ k hk B c Z Y hB h0 hs hY τ i j
  have h1 : ∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j := fun τ i j => by
    have a1 := hY 0 τ i j
    have a2 := (pow_dvd_pow (X : K⟦X⟧) (by omega : 1 ≤ 2)).trans (hY 1 τ i j)
    rw [pow_one] at a1 a2
    have := dvd_sub a1 a2
    rwa [sub_sub_sub_cancel_left] at this
  obtain ⟨M, β, hβ, hD⟩ := decay O K l a ι k hk B c Z hB h0 hs h1
  have hr0 : 0 ≤ rad l k := rad_nonneg l k
  have hr1 : rad l k < 1 := rad_lt_one l hk
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  refine limR O K l k (Y τ i j) (fun n => Z n τ i j) (fun n => (hD n τ i j).1) (fun n => hY n τ i j) ?_
  have hg := (growth β (rad l k) l hβ hr0 hr1 hl2).const_mul M
  rw [mul_zero] at hg
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hg
  · have hm := sub_mem (hD (n + 1) τ i j).1 (hD n τ i j).1
    exact (mul_nonneg (norm_nonneg _) (pow_nonneg hr0 0)).trans (le_normR hm 0)
  · rw [← mul_assoc]; exact (hD n τ i j).2
end GlobalTheory.BK.XiTriv

noncomputable section

namespace GlobalTheory.BK.XiTriv

open PowerSeries Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]

theorem frob_map_mul (M N : Matrix ι ι K⟦X⟧) :
    (M * N).map (frob K l) = M.map (frob K l) * N.map (frob K l) :=
  Matrix.map_mul (f := (frob K l).toRingHom)

theorem frob_map_one : (1 : Matrix ι ι K⟦X⟧).map (frob K l) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem dvd_mul_mul_apply {c : K⟦X⟧} (M D N : Matrix ι ι K⟦X⟧) (h : ∀ i j, c ∣ D i j) (i j : ι) :
    c ∣ (M * D * N) i j := by
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun m _ => (h m k).mul_left _

namespace Seq

variable (P : PhiMod O K l e a ι)

def Ws (n : ℕ) : ZMod a → Matrix ι ι K⟦X⟧ :=
  (fun W τ => (P.mx0 τ).map C * (W (τ - 1)).map (frob K l) * P.mxInv τ)^[n] fun _ => 1

theorem Ws_zero (τ : ZMod a) : Ws P 0 τ = 1 := rfl

theorem Ws_succ (n : ℕ) (τ : ZMod a) : Ws P (n + 1) τ =
    (P.mx0 τ).map C * (Ws P n (τ - 1)).map (frob K l) * P.mxInv τ := by
  rw [Ws, Function.iterate_succ_apply']
  rfl

theorem Ws_mul (n : ℕ) (τ : ZMod a) : Ws P n τ * P.xiSeq n τ = 1 := by
  induction n generalizing τ with
  | zero => rw [Ws_zero, PhiMod.xiSeq_zero, Matrix.one_mul]
  | succ n ih =>
    have h1 := P.mxInv_mul_mx τ
    have h3 : (P.mx0 τ).map C * ((P.mxInv τ).map constantCoeff).map C = 1 := by
      rw [← Matrix.map_mul, P.matrix_mul_inv_const_eq_one τ, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [PhiMod.xiSeq_succ, Ws_succ]
    calc _ = (P.mx0 τ).map C * (Ws P n (τ - 1)).map (frob K l) * (P.mxInv τ * P.mx τ) *
          (P.xiSeq n (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C := by
          simp only [Matrix.mul_assoc]
      _ = (P.mx0 τ).map C * ((Ws P n (τ - 1) * P.xiSeq n (τ - 1)).map (frob K l)) *
          ((P.mxInv τ).map constantCoeff).map C := by
          rw [h1, frob_map_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [ih, frob_map_one, Matrix.mul_one, h3]

theorem xiMat_mul_inv (τ : ZMod a) : P.xiMat τ * (P.xiMat τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)

theorem inv_sub_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 2) ∣ ((P.xiMat τ)⁻¹ - Ws P (n + 1) τ) i j := by
  have h : (P.xiMat τ)⁻¹ - Ws P (n + 1) τ =
      Ws P (n + 1) τ * (P.xiSeq (n + 1) τ - P.xiMat τ) * (P.xiMat τ)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Ws_mul, Matrix.one_mul, Matrix.mul_assoc,
      xiMat_mul_inv, Matrix.mul_one]
  rw [h]
  refine dvd_mul_mul_apply _ _ _ (fun i j => ?_) i j
  rw [Matrix.sub_apply, ← neg_sub]
  exact (dvd_neg).2 (P.xiMat_sub_dvd (n + 1) τ i j)

end Seq

variable [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

theorem mulVec_mem {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B)
    {v : ι → K⟦X⟧} (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem _ fun j _ => mul_mem (hM i j) (hv j)

theorem Y_mem (P : PhiMod O K l e a ι) {k : ℝ} (hk : 1 / ((e : ℝ) * l) < k) (τ : ZMod a) (i j : ι) :
    (P.mxInv τ * P.xiMat τ) i j ∈ R O K l k := by
  have hk0 : 0 < k := by
    have h1 := NeZero.pos e
    have h2 := (Fact.out : l.Prime).pos
    exact lt_trans (by positivity) hk
  refine convB O K l a ι k hk0 (fun τ => (P.mx (τ - 1)).map (frob K l))
    (fun τ => (P.mxInv τ).map constantCoeff) (fun n τ => P.mxInv τ * P.xiSeq (n + 1) τ)
    (fun τ => P.mxInv τ * P.xiMat τ) (fun τ i j => frobA O K l e k hk _ (P.mx_mem _ i j))
    (fun τ => ?_) (fun n τ => ?_) (fun n τ i j => ?_) τ i j
  · rw [PhiMod.xiSeq_succ, PhiMod.xiSeq_zero, frob_map_one, Matrix.mul_one, ← Matrix.mul_assoc,
      PhiMod.mxInv_mul_mx, Matrix.one_mul]
  · rw [PhiMod.xiSeq_succ P (n + 1), ← frob_map_mul, ← Matrix.mul_assoc (P.mx (τ - 1)),
      PhiMod.mx_mul_mxInv, Matrix.one_mul, ← Matrix.mul_assoc (P.mxInv τ), ← Matrix.mul_assoc (P.mxInv τ),
      PhiMod.mxInv_mul_mx, Matrix.one_mul]
  · have h : P.mxInv τ * P.xiMat τ - P.mxInv τ * P.xiSeq (n + 1) τ =
        P.mxInv τ * (P.xiMat τ - P.xiSeq (n + 1) τ) * 1 := by
      rw [Matrix.mul_one, Matrix.mul_sub]
    rw [← Matrix.sub_apply, h]
    exact dvd_mul_mul_apply _ _ _ (fun i j => (pow_dvd_pow _ (by omega)).trans
      (P.xiMat_sub_dvd (n + 1) τ i j)) i j

theorem Yi_mem (P : PhiMod O K l e a ι) {k : ℝ} (hk : 1 / ((e : ℝ) * l) < k) (τ : ZMod a) (i j : ι) :
    ((P.xiMat τ)⁻¹ * P.mx τ) i j ∈ R O K l k := by
  have hk0 : 0 < k := by
    have h1 := NeZero.pos e
    have h2 := (Fact.out : l.Prime).pos
    exact lt_trans (by positivity) hk
  have key := convB O K l a ι k hk0 (fun τ => ((P.mxInv (τ - 1)).map (frob K l))ᵀ)
    (fun τ => (P.mx0 τ)ᵀ) (fun n τ => (Seq.Ws P (n + 1) τ * P.mx τ)ᵀ)
    (fun τ => ((P.xiMat τ)⁻¹ * P.mx τ)ᵀ) (fun τ i j => frobA O K l e k hk _ (P.mxInv_mem _ j i))
    (fun τ => ?_) (fun n τ => ?_) (fun n τ i j => ?_) τ j i
  · simpa using key
  · show (Seq.Ws P (0 + 1) τ * P.mx τ)ᵀ = ((P.mx0 τ)ᵀ).map C
    rw [Seq.Ws_succ, Seq.Ws_zero, frob_map_one, Matrix.mul_one, Matrix.mul_assoc,
      PhiMod.mxInv_mul_mx, Matrix.mul_one, Matrix.transpose_map]
  · show (Seq.Ws P (n + 2) τ * P.mx τ)ᵀ = ((P.mxInv (τ - 1)).map (frob K l))ᵀ *
        ((Seq.Ws P (n + 1) (τ - 1) * P.mx (τ - 1))ᵀ).map (frob K l) * ((P.mx0 τ)ᵀ).map C
    rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul,
      ← Matrix.transpose_mul]
    congr 1
    rw [Seq.Ws_succ P (n + 1), Matrix.mul_assoc _ (P.mxInv τ), PhiMod.mxInv_mul_mx, Matrix.mul_one,
      ← frob_map_mul,
      Matrix.mul_assoc (Seq.Ws P (n + 1) (τ - 1)), PhiMod.mx_mul_mxInv, Matrix.mul_one]
  · rw [Matrix.transpose_apply, Matrix.transpose_apply, ← Matrix.sub_apply, ← Matrix.sub_mul,
      ← Matrix.one_mul ((P.xiMat τ)⁻¹ - Seq.Ws P (n + 1) τ)]
    exact dvd_mul_mul_apply _ _ _ (fun i j => (pow_dvd_pow _ (by omega)).trans
      (Seq.inv_sub_dvd P n τ i j)) j i

end GlobalTheory.BK.XiTriv

end

open PowerSeries GlobalTheory.BK in
theorem GlobalTheory.BK.xiExt_mem_Lk_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ w : Vec K a ι, P.xiExt w ∈ P.Lk k ↔ w ∈ P.Mext (R O K l k) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P k hk w
  have hprod (τ : ZMod a) : ((P.xiMat τ)⁻¹ * P.mx τ) * (P.mxInv τ * P.xiMat τ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.mx τ), PhiMod.mx_mul_mxInv, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ)]
  constructor
  · intro h
    refine mem_tot.2 fun τ => ?_
    have h1 := P.mem_extc_iff.1 (mem_tot.1 h τ)
    rw [PhiMod.xiExt_apply, Matrix.mulVec_mulVec] at h1
    have h2 := XiTriv.mulVec_mem (XiTriv.Yi_mem P hk τ) h1
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h2
  · intro h
    refine mem_tot.2 fun τ => P.mem_extc_iff.2 ?_
    rw [PhiMod.xiExt_apply, Matrix.mulVec_mulVec]
    exact XiTriv.mulVec_mem (XiTriv.Y_mem P hk τ) (mem_tot.1 h τ)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
section
open Matrix

namespace GlobalTheory.UnitDiscAlg

section Basic
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem integ_mul {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x * y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun k _ => by rw [norm_mul]; exact mul_le_one₀ (hx i k) (norm_nonneg _) (hy k j))

theorem integ_add {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x + y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (hy i j))

theorem integ_sub {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x - y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (by rw [norm_neg]; exact hy i j))

theorem integ_one : ∀ i j, ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem integ_zero : ∀ i j, ‖(0 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  simp

theorem integ_pow {x : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (k : ℕ) :
    ∀ i j, ‖(x ^ k) i j‖ ≤ 1 := by
  induction k with
  | zero => simpa using integ_one
  | succ k ih => rw [pow_succ]; exact integ_mul ih hx

theorem integ_smul {x : Matrix (Fin n) (Fin n) E} {a : E} (ha : ‖a‖ ≤ 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ∀ i j, ‖(a • x) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i j)

end Basic

theorem comm_of_bezout {E : Type} [Field E] {n : ℕ} {N a b : Matrix (Fin n) (Fin n) E}
    (h : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (ha : a * N = N * a) (hb : b * N = N * b) : a * b = b * a := by
  obtain ⟨u, v, huv⟩ := h
  have hs : N.charpoly.Separable := ⟨u, v, huv⟩
  obtain ⟨w, hw⟩ := GlobalTheory.RegSS.cyclicField E (Fin n) N hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N w hw).2.2
  have ha' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij ha
  have hb' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij hb
  exact congrArg Subtype.val
    (mul_comm (⟨a, ha'⟩ : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg N) ⟨b, hb'⟩)

end GlobalTheory.UnitDiscAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
section
noncomputable section

namespace GlobalTheory.SenLines

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct PowerSeries

section Series

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def serAct (f : F⟦X⟧) (y : ℤ → M) : ℤ → M := fun m => ∑ᶠ j : ℕ, coeff j f • y (m - j)

def serLine (u : ℤ) (d : M) (c : F⟦X⟧) : ℤ → M :=
  fun m => if 0 ≤ m + u then coeff (m + u).toNat c • d else 0

theorem serAct_one (y : ℤ → M) : serAct (1 : F⟦X⟧) y = y := by
  funext m
  rw [serAct, finsum_eq_single _ 0 (fun j hj => by rw [coeff_one, ite_eq_right hj, zero_smul])]
  simp

def SpanIsLines {N : Type} (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (F : Type) [Field F]
    [Module F M] : Prop :=
  ∀ y : ℤ → M, (∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j))) ↔
    ∃ c : Fin r → F⟦X⟧, y = ∑ k, serLine (u k) (d k) (c k)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def LinesAt (i : ZMod n) (ζ : LL) (U : Multiset ℤ) : Prop :=
  ∃ (u : Fin (Module.finrank LL T.V) → ℤ) (d : Fin (Module.finrank LL T.V) → T.V ⊗[Qp] BdR),
    Finset.univ.val.map u = U ∧ LinearIndependent LL d ∧ SpanIsLines (W.levN T i ζ) u d LL

def QFrame (g : W.Gam) (J : O⟦X⟧ →ₐ[O] O⟦X⟧) : Prop :=
  Function.Injective J ∧
  (∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  J X = W.π₀₁ + ((PD.p : ℕ) : O⟦X⟧) ∧
  (∀ c, constantCoeff (J c) = 0 → X - ((PD.p : ℕ) : O⟦X⟧) ∣ c) ∧
  (∃ s : (O⟦X⟧)ˣ, W.γ₀ g (J X) = J X * J s ∧ X - ((PD.p : ℕ) : O⟦X⟧) ∣ (s : O⟦X⟧) - 1) ∧
  Associated (J X) W.q₀ ∧
  IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n)))

end Generic

end GlobalTheory.SenLines
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasisStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), CompactSpace O → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → IsLatticeIn D.T → PerfectRight D.bT → T2Space VT' → ∀ ϖ : O, Irreducible ϖ → CompactSpace ↥D.T' ∧ (∀ n : ℕ, IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T')) ∧ ∀ U ∈ nhds (0 : ↥D.T'), ∃ n : ℕ, ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') ⊆ U := by
  first | exact @GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds | exact GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds | (intros; apply GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerDerivationPreservesBreuilKisinSumSubmodule
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL.Tconn

theorem N_vpow {K : Type} [NormedField K] (e A' : ℕ) :
    N K (((X : K⟦X⟧) ^ e) ^ A') = ((e * A' : ℕ) : K⟦X⟧) * ((X : K⟦X⟧) ^ e) ^ A' := by
  ext n
  rw [coeff_N, ← pow_mul, ← map_natCast (C (R := K)), coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

theorem N_lpow {K : Type} [NormedField K] (l b : ℕ) : N K ((l : K⟦X⟧) ^ b) = 0 := by
  rw [← Nat.cast_pow]; exact Derivation.map_natCast _ _

theorem part_top {K O κ : Type} {a : ℕ} [NormedField K] [CommRing O] [Algebra O K]
    (V : Submodule O (Vec K a κ)) : GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ V = V := by
  ext v; simp [GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part]

end GlobalTheory.CokerL.Tconn

theorem GlobalTheory.CokerL.Tsub_conn : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F A' b hred x hx
  have hIS := (hred.2.2 ι κ η H D₁ D₂ F).2.1
  have hMH := (hred.2.1 κ η H D₂).1
  have hvS : ((X : K⟦X⟧) ^ e) ^ A' ∈ S O K e := pow_mem (pow_mem HasU.X_mem e) A'
  have hHigh : ∀ (f : K⟦X⟧), f ∈ S O K e → ∀ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod,
      f • q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod := fun f hf q hq =>
    (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • D₂.MM).smul_mem (⟨f, hf⟩ : S O K e) hq
  have hnat : ∀ (n : ℕ) (q : Vec K a κ) (V : Submodule O (Vec K a κ)), q ∈ V → ((n : K⟦X⟧)) • q ∈ V :=
    fun n q V hq => by
      rw [Nat.cast_smul_eq_nsmul]; exact V.nsmul_mem hq n
  obtain ⟨x12, h12, x3, h3, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨x1, h1, x2, h2, rfl⟩ := Submodule.mem_sup.1 h12
  rw [map_add (f := _), map_add (f := _)]
  refine add_mem (add_mem ?_ ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := h1
    change D₂.toPhiMod.conn (((X : K⟦X⟧) ^ e) ^ A' • y) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_vpow, mul_smul]
    refine add_mem ?_ ?_
    · have : ((e * A' : ℕ) : K⟦X⟧) • y ∈ (F.imL.restrictScalars O) := hnat _ _ _ hy
      rw [smul_comm]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, this, rfl⟩)
    · have hc := hIS y (by
        rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top]
        exact Submodule.mem_sup_left hy)
      rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
      rw [← hpq, smul_add]
      exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨p, hp, rfl⟩))
        (Submodule.mem_sup_right (hHigh _ hvS q hq))
  · obtain ⟨z, hz, rfl⟩ := h2
    change D₂.toPhiMod.conn (((l : K⟦X⟧) ^ b) • z) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_lpow, zero_smul, zero_add]
    have hzM : z ∈ D₂.MM := PhiMod.ext_mono _ (A_le_S l e) hz
    have hc : D₂.conn z ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O) := by
      rw [GlobalTheory.CokerL.Tconn.part_top]
      exact BKDat.conn_mem_MM D₂ hzM
    rw [hMH.MM_eq, GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
    change (l : K⟦X⟧) ^ b • D₂.toPhiMod.conn z ∈ _
    rw [← hpq, smul_add]
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨p, hp, rfl⟩)) ?_
    refine Submodule.mem_sup_right ?_
    rw [← Nat.cast_pow]
    exact hnat _ _ _ hq
  · have := hMH.conn_high x3 (by rw [GlobalTheory.CokerL.Tconn.part_top]; exact h3)
    rw [GlobalTheory.CokerL.Tconn.part_top] at this
    exact Submodule.mem_sup_right this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCocycleLiftOfCompatibleStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  first | exact @GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible | exact GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible | (intros; apply GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticePairingEqInvUniformizerStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), IsLatticeIn D.T → PerfectRight D.bT → ∀ ϖ : O, Irreducible ϖ → ∀ x : VT ⧸ D.T, x ≠ 0 → ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  first | exact @GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif | exact GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif | (intros; apply GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionPairingEqInvUniformizerStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  first | exact @GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif | exact GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif | (intros; apply GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationEstimateExpansionTensorBdRComponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]  (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (tS pk : BdR), IsUnit tS → tS ∈ PD.Fil 1 → ∀ (r w : ℕ) (z : T.V ⊗[Qp] BdR) (D : Fin r → T.V ⊗[Qp] BdR) (b : Fin r → BdR) (e : Fin r → PowerSeries LL) (L : ℤ → T.V ⊗[Qp] BdR), mulVR T (tS ^ w) z - ∑ j, mulVR T (b j) (D j) ∈ compKer T ι → (∀ (j : Fin r) (m : ℕ), b j - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (e j)) * tS ^ k ∈ PD.Fil (m : ℤ)) → (∀ k : ℤ, L k - ∑ j, cz (e j) (k + (w : ℤ)) • D j ∈ compKer T ι) → ∀ a : ℕ, (∀ k : ℤ, k < -(a : ℤ) → L k = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS ^ a) (mulVR T pk z) - mulVR T pk (∑ k ∈ Finset.range M, mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  first | exact @GlobalTheory.HWL.Cmp.filt_expansion_component | exact GlobalTheory.HWL.Cmp.filt_expansion_component | (intros; apply GlobalTheory.HWL.Cmp.filt_expansion_component <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModuleStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M], FiniteDimensional ℚ_[p] K → (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ ϖ : O, Irreducible ϖ → (∀ n : ℕ, IsOpen ((powSub (M := M) ϖ n : Submodule O M) : Set M)) → ∀ n : ℕ, (Z1 (quotRep ρ ϖ n) : Set (G → M ⧸ powSub (M := M) ϖ n)).Finite := by
  first | exact @GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module | exact GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module | (intros; apply GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module <;> assumption)
end

