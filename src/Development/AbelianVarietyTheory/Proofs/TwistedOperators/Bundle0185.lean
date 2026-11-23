module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalDoublingSectionGraphDiagonalEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UGraph

open GlobalTheory.Doubling Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_GLint_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {x : GL ι L}
    (h1 : ∀ i j, x.1 i j ∈ Formalism.UG.intL L) (h2 : ∀ i j, (x⁻¹).1 i j ∈ Formalism.UG.intL L) :
    x ∈ Formalism.UG.GLint ι (Formalism.UG.intL L) := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem unif_mem_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
  omega

theorem exp_rev {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i)) (i : Fin n) : d (Fin.rev i) = -d i := by
  have h : Formalism.UG.cT σ t.1.1 * Formalism.UG.antiJ L n * t.1.1 = Formalism.UG.antiJ L n := t.2
  have h1 := congrFun (congrFun h i) (Fin.rev i)
  have hJ : Formalism.UG.antiJ L n i (Fin.rev i) = 1 := by
    simp only [Formalism.UG.antiJ, Fin.val_rev]
    rw [if_pos (by omega)]
  rw [hJ, ht, Formalism.UG.cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, hJ] at h1
  rw [map_zpow₀, hU.2.2.1, mul_one, ← zpow_add₀ ϖ.ne_zero] at h1
  have h2 := congrArg Formalism.UG.ordL h1
  rw [Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1, ← zpow_zero (ϖ : L), Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1] at h2
  omega

theorem antiJ_mul_diagonal {n : ℕ} (f g : Fin n → L) (h : ∀ i, f (Fin.rev i) = g i) :
    Formalism.UG.antiJ L n * Matrix.diagonal f = Matrix.diagonal g * Formalism.UG.antiJ L n := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Formalism.UG.antiJ]
  split_ifs with hij
  · have : j = Fin.rev i := Fin.ext (by rw [Fin.val_rev]; omega)
    subst this
    rw [h]
    ring
  · simp

theorem exists_kappa {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (d : Fin n → ℤ)
    (hd : ∀ i, d (Fin.rev i) = -d i) :
    ∃ κ : GL (Fin (n + n)) L, κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n ∧ κ ∈ Formalism.UG.GLint (Fin (n + n)) (Formalism.UG.intL L) ∧
      GlobalTheory.Doubling.KeepsDiag finSumFinEquiv (GlobalTheory.Doubling.blkMat finSumFinEquiv (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1) ∧
      GlobalTheory.Doubling.leviMat finSumFinEquiv (GlobalTheory.Doubling.blkMat finSumFinEquiv (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1) =
        Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
  set e := finSumFinEquiv (m := n) (n := n)
  set J := Formalism.UG.antiJ L n
  set u : Fin n → L := fun i => (ϖ : L) ^ (-d i).toNat - 1 with hu
  set w : Fin n → L := fun i => (ϖ : L) ^ (d i).toNat - 1 with hw
  have huw : ∀ i, u i * w i = 0 := fun i => by
    rcases le_total (d i) 0 with h | h
    · simp [hw, Int.toNat_of_nonpos h]
    · simp [hu, Int.toNat_of_nonpos (neg_nonpos.2 h)]
  set B : Matrix (Fin n) (Fin n) L := Matrix.diagonal u with hB
  set C : Matrix (Fin n) (Fin n) L := Matrix.diagonal w with hC
  have hBC : B * C = 0 := by rw [hB, hC, diagonal_mul_diagonal]; simp [huw]
  have hCB : C * B = 0 := by rw [hB, hC, diagonal_mul_diagonal]; simp [mul_comm (w _), huw]
  have hJB : J * B = C * J := antiJ_mul_diagonal u w fun i => by simp [hu, hw, hd]
  have hJC : J * C = B * J := antiJ_mul_diagonal w u fun i => by simp [hu, hw, hd]
  have hσu : B.map σ = B := by
    rw [hB, diagonal_map (map_zero σ)]
    congr 1; funext i
    simp [hu, map_sub, map_pow, hU.2.2.1]
  have hσw : C.map σ = C := by
    rw [hC, diagonal_map (map_zero σ)]
    congr 1; funext i
    simp [hw, map_sub, map_pow, hU.2.2.1]
  let κ : GL (Fin (n + n)) L := ⟨(fromBlocks 1 B C 1).submatrix e.symm e.symm,
    (fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm,
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB],
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB]⟩
  have hint : ∀ i j, (fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1) i j ∈ Formalism.UG.intL L ∧
      (fromBlocks (1 : Matrix (Fin n) (Fin n) L) (-B) (-C) 1) i j ∈ Formalism.UG.intL L := by
    have h1 : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) L) a b ∈ Formalism.UG.intL L := fun a b => by
      rw [Matrix.one_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h2 : ∀ (f : Fin n → ℕ) (a b : Fin n),
        (Matrix.diagonal fun i => (ϖ : L) ^ f i - 1) a b ∈ Formalism.UG.intL L := fun f a b => by
      rw [diagonal_apply]; split_ifs
      · exact sub_mem (pow_mem (unif_mem_int hU) _) (one_mem _)
      · exact zero_mem _
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, neg_apply]
    all_goals first
      | exact ⟨h1 _ _, h1 _ _⟩
      | exact ⟨h2 _ _ _, neg_mem (h2 _ _ _)⟩
  have hM : (GlobalTheory.Doubling.blkMat e (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1).submatrix e e =
      fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) ((Matrix.diagonal fun i => (ϖ : L) ^ d i) * B) C 1 := by
    show ((fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) 0 0 1).submatrix e.symm e.symm *
      (fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _
    rw [submatrix_mul_equiv, submatrix_submatrix]
    simp [fromBlocks_multiply]
  have h1 : (Matrix.diagonal fun i => (ϖ : L) ^ d i) + (Matrix.diagonal fun i => (ϖ : L) ^ d i) * B =
      Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
    rw [hB, diagonal_mul_diagonal, diagonal_add]
    congr 1; funext i
    simp only [hu]
    rw [mul_sub, mul_one, add_sub_cancel, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ϖ.ne_zero]
    congr 1
    omega
  have h2 : C + 1 = Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
    rw [hC, ← diagonal_one, diagonal_add]
    congr 1; funext i
    simp [hw]
  refine ⟨κ, ?_, mem_GLint_of_entries (fun i j => (hint _ _).1) (fun i j => (hint _ _).2), ?_, ?_⟩
  · show Formalism.UG.cT σ ((fromBlocks 1 B C 1).submatrix e.symm e.symm) * GlobalTheory.Doubling.blkMat e J (-J) *
      (fromBlocks 1 B C 1).submatrix e.symm e.symm = GlobalTheory.Doubling.blkMat e J (-J)
    have hcT : Formalism.UG.cT σ ((fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1).submatrix e.symm e.symm) =
        (fromBlocks 1 C B 1).submatrix e.symm e.symm := by
      rw [Formalism.UG.cT, ← submatrix_map, transpose_submatrix, fromBlocks_map, fromBlocks_transpose, hσu, hσw]
      simp [hB, hC, diagonal_transpose]
    rw [hcT, GlobalTheory.Doubling.blkMat, submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    have e1 : C * J * C = 0 := by rw [Matrix.mul_assoc, hJC, ← Matrix.mul_assoc, hCB, Matrix.zero_mul]
    have e2 : B * J * B = 0 := by rw [Matrix.mul_assoc, hJB, ← Matrix.mul_assoc, hBC, Matrix.zero_mul]
    simp [Matrix.mul_neg, Matrix.neg_mul, hJB, hJC, e1, e2]
  · rw [GlobalTheory.Doubling.KeepsDiag, GlobalTheory.Doubling.leviMat, hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, h1, h2]
  · rw [GlobalTheory.Doubling.leviMat, hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, h1]

theorem secVal_unif_pow {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ)
    (k : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ k := by
  have h := Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val,
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem sphericalDoublingSection_graph_diagonal_cartan [CompleteSpace L] {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q)
    {χ : Lˣ →* ℂˣ} (hχ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ) {s : ℂ} {Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ}
    (hΦ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ) (d : Fin n → ℤ) (t : GU σ n)
    (ht : t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i)) (k₁ : GU σ n) (hk₁ : k₁ ∈ KU σ n) (k₂ : GU σ n)
    (hk₂ : k₂ ∈ KU σ n) :
    Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  obtain ⟨κ, hκG, hκI, hkeep, hlev⟩ := exists_kappa hU d (exp_rev hU ht)
  set e := finSumFinEquiv (m := n) (n := n)
  let K : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := ⟨κ, hκG⟩
  have hK : K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n := ⟨hκG, hκI⟩
  obtain ⟨x₁, hx₁⟩ := hk₁.2
  obtain ⟨x₂, hx₂⟩ := hk₂.2
  obtain ⟨y₁, hy₁⟩ := (inv_mem hk₁).2
  let p0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁)
  let r : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)
  have hp0P : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n :=
    GlobalTheory.Doubling.mem_siegelOf.2 ((GlobalTheory.Doubling.keepsDiag_blkMat e).2 rfl)
  have hp0K : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n :=
    ⟨p0.2, GlobalTheory.Doubling.blkGL e (x₁, x₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₁]; rfl⟩
  have hrK : r ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n :=
    ⟨r.2, GlobalTheory.Doubling.blkGL e (x₂, y₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₂, hy₁]; rfl⟩
  have hp1P : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := by
    refine GlobalTheory.Doubling.mem_siegelOf.2 ?_
    change GlobalTheory.Doubling.KeepsDiag e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)
    rw [ht]
    exact hkeep
  let P0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := ⟨p0, hp0P⟩
  let P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := ⟨_, hp1P⟩
  have hdec : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂) = ((P0 * P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n) :
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n) * (K⁻¹ * r) := by
    rw [Subgroup.coe_mul]
    change _ = p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r)
    rw [show p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r) = p0 * GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * r by group]
    change GlobalTheory.Doubling.ioU σ e rfl (k₁ * t * k₂, 1) = GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁) *
      GlobalTheory.Doubling.ioU σ e rfl (t, 1) * GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)
    rw [← map_mul, ← map_mul]
    congr 1
    ext1
    · rfl
    · simp
  have ha1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD σ n P1 = ϖ ^ (∑ i, (d i).toNat) := by
    apply Units.ext
    rw [GlobalTheory.Doubling.val_aOf, Units.val_pow_eq_pow_val]
    change (GlobalTheory.Doubling.leviMat e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)).det = _
    rw [ht, hlev, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [hdec, hΦ _ _ (mul_mem (inv_mem hK) hrK), map_mul, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_mul hq,
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_unit q hχ _ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.v_aD_eq P0 hp0K), one_mul, ha1, secVal_unif_pow hU]
  rw [show ∑ i, max (d i) 0 = ((∑ i, (d i).toNat : ℕ) : ℤ) by push_cast; simp [Int.toNat_eq_max], zpow_natCast]

theorem sphSec_io_diag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (χ : Lˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (d : Fin n → ℤ) (t : GU σ n), t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  intro L _ _ _ ϖ σ q n hU χ hχ s Φ hΦ d t ht k₁ hk₁ k₂ hk₂
  exact sphericalDoublingSection_graph_diagonal_cartan hU hχ hΦ d t ht k₁ hk₁ k₂ hk₂

end GlobalTheory.UGraph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.SubstDeg

theorem totalDegree_aeval_le {σ κ : Type*} (f : σ → MvPolynomial κ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (AddMonoidAlgebra.coeff P s)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  rw [h0, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * (f i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = s i := mul_one _

theorem totalDegree_subst_le : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k P).totalDegree ≤ P.totalDegree := by
  intro D a b τ ε ε' g k P
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst
  refine totalDegree_aeval_le _ (fun v => ?_) P
  split_ifs with h
  · refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
    refine MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le
  all_goals first
    | exact (MvPolynomial.totalDegree_X _).le
    | (refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
       refine MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_
       exact (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le)

end GlobalTheory.Chain.RealIt.SubstDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def thPDatum (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (e : AE D) : WO S T → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
      omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
    else 0

def indL {S T : HSp D} (L : AddSubgroup (WO S T)) : WO S T → ℂ := fun x => if x ∈ L then 1 else 0

def partAt {S T : HSp D} (a : AE D) (w : WO S T) : WO S T := w.map fun z => a * z

abbrev LvCls {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) : Type :=
  tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ) ⧸
    (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ)).addSubgroupOf _

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSubgroupConjugacyClassEqTsumWeighted
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.Twist.ClassSumReindex

theorem tsum_ratClass_eq_tsum_weighted (H : Type) [Group H] (Γ : Subgroup H) (γ : H) (_hγ : γ ∈ Γ)
    (α : H → ℝ≥0∞) (hα : ∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1)
    (G : H → ℝ≥0∞) (x : H) :
    ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) =
      ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) := by
  classical
  set C := Γ.subgroupOf (cent γ)
  let R := GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ
  let s : R → H := fun δ => Classical.choose δ.2
  have hs : ∀ δ : R, s δ ∈ Γ ∧ (δ : H) = (s δ)⁻¹ * γ * s δ := fun δ => Classical.choose_spec δ.2
  have hcomm : ∀ h : C, ((h : cent γ) : H) * γ = γ * ((h : cent γ) : H) := fun h =>
    (Subgroup.mem_centralizer_singleton_iff).1 (h : cent γ).2
  have hΓ : ∀ h : C, ((h : cent γ) : H) ∈ Γ := fun h => Subgroup.mem_subgroupOf.1 h.2
  have hconj : ∀ (h : C) (δ : R), (((h : cent γ) : H) * s δ)⁻¹ * γ * (((h : cent γ) : H) * s δ) = δ := by
    intro h δ
    rw [(hs δ).2]
    have := hcomm h
    calc (((h : cent γ) : H) * s δ)⁻¹ * γ * (((h : cent γ) : H) * s δ)
        = (s δ)⁻¹ * (((h : cent γ) : H)⁻¹ * (((h : cent γ) : H) * γ)) * s δ := by rw [this]; group
      _ = (s δ)⁻¹ * γ * s δ := by group
  let p : Γ → R := fun g => ⟨(g : H)⁻¹ * γ * g, g, g.2, rfl⟩
  have hq : ∀ g : Γ, (g : H) * (s (p g))⁻¹ ∈ cent γ := by
    intro g
    have h1 := (hs (p g)).2
    change (g : H)⁻¹ * γ * g = (s (p g))⁻¹ * γ * s (p g) at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : γ = (g : H) * ((s (p g))⁻¹ * γ * s (p g)) * (g : H)⁻¹ := by rw [← h1]; group
    calc (g : H) * (s (p g))⁻¹ * γ = (g : H) * ((s (p g))⁻¹ * γ * s (p g)) * (g : H)⁻¹ * ((g : H) * (s (p g))⁻¹) := by
          group
      _ = γ * ((g : H) * (s (p g))⁻¹) := by rw [← h2]
  let e : Γ ≃ R × C :=
    { toFun := fun g => (p g, ⟨⟨(g : H) * (s (p g))⁻¹, hq g⟩,
        Subgroup.mem_subgroupOf.2 (mul_mem g.2 (inv_mem (hs (p g)).1))⟩)
      invFun := fun q => ⟨((q.2 : cent γ) : H) * s q.1, mul_mem (hΓ q.2) (hs q.1).1⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun q => by
        obtain ⟨δ, h⟩ := q
        have hp : p ⟨((h : cent γ) : H) * s δ, mul_mem (hΓ h) (hs δ).1⟩ = δ := Subtype.ext (hconj h δ)
        refine Prod.ext hp (Subtype.ext (Subtype.ext ?_))
        simp only [hp]
        group }
  rw [← e.symm.tsum_eq]
  refine Eq.trans ?_ (ENNReal.tsum_prod (f := fun (δ : R) (h : C) => α (((e.symm (δ, h) : Γ) : H) * x) *
      G ((((e.symm (δ, h) : Γ) : H) * x)⁻¹ * γ * (((e.symm (δ, h) : Γ) : H) * x)))).symm
  refine tsum_congr fun δ => ?_
  have key : ∀ h : C, α (((e.symm (δ, h) : Γ) : H) * x) *
      G ((((e.symm (δ, h) : Γ) : H) * x)⁻¹ * γ * (((e.symm (δ, h) : Γ) : H) * x)) =
      α (((h : cent γ) : H) * (s δ * x)) * G (x⁻¹ * δ * x) := by
    intro h
    change α (((h : cent γ) : H) * s δ * x) * G ((((h : cent γ) : H) * s δ * x)⁻¹ * γ * (((h : cent γ) : H) * s δ * x)) = _
    rw [mul_assoc ((h : cent γ) : H) (s δ) x]
    congr 1
    congr 1
    rw [← hconj h δ]
    group
  rw [tsum_congr key, ENNReal.tsum_mul_right, hα, one_mul]

end GlobalTheory.Twist.ClassSumReindex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UniformlyNegDefiniteNearOfContinuousQuadFormFami
section
open MeasureTheory

namespace GlobalTheory

theorem quadForm_eventually_unif_negDef {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hc : Continuous (fun p : ℝ × V => M p.1 p.2 p.2))
    (hneg : ∀ t v, v ≠ 0 → (M t v v).re < 0) (t₀ : ℝ) :
    ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
  have hF : Continuous (fun p : ℝ × V => (M p.1 p.2 p.2).re) := Complex.continuous_re.comp hc
  have hscale : ∀ t (c : ℝ) (u : V), (M t (c • u) (c • u)).re = c ^ 2 * (M t u u).re := by
    intro t c u
    simp only [map_smul, LinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
    ring
  have key : ∀ (ε : ℝ) (t : ℝ), (∀ u ∈ Metric.sphere (0:V) 1, (M t u u).re < -ε) →
      ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
    intro ε t ht x
    by_cases hx : x = 0
    · subst hx; simp
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0:V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have h1 := ht _ hu
      have hx' : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      have h2 : (M t x x).re = ‖x‖ ^ 2 * (M t (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := by
        conv_lhs => rw [hx']
        exact hscale t _ _
      rw [h2]
      have hp : 0 ≤ ‖x‖ ^ 2 := by positivity
      nlinarith
  have hS : IsCompact (Metric.sphere (0:V) 1) := isCompact_sphere 0 1
  rcases (Metric.sphere (0:V) 1).eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, Filter.Eventually.of_forall fun t => key 1 t ?_⟩
    intro u hu
    rw [hE] at hu
    exact absurd hu (Set.notMem_empty _)
  · have hcont0 : ContinuousOn (fun u : V => (M t₀ u u).re) (Metric.sphere 0 1) :=
      (hF.comp (Continuous.prodMk_right t₀)).continuousOn
    obtain ⟨u₀, hu₀, hmax⟩ := hS.exists_isMaxOn hNE hcont0
    have hu₀0 : u₀ ≠ 0 := by
      rintro rfl
      simp at hu₀
    have hm : (M t₀ u₀ u₀).re < 0 := hneg t₀ u₀ hu₀0
    refine ⟨-(M t₀ u₀ u₀).re / 2, by linarith, ?_⟩
    have hev : ∀ᶠ t in nhds t₀, ∀ u ∈ Metric.sphere (0:V) 1,
        (M t u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
      apply hS.eventually_forall_of_forall_eventually
      intro u hu
      have hlt : (M t₀ u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
        have := hmax hu
        simp only [Set.mem_setOf_eq] at this
        linarith
      exact hF.continuousAt.eventually_lt continuousAt_const hlt
    exact hev.mono fun t ht => key _ t ht

theorem quadForm_unif_target : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    Continuous (fun p : ℝ × V => M p.1 p.2 p.2) → (∀ t v, v ≠ 0 → (M t v v).re < 0) →
    ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) :=
  fun M hc hneg t₀ => quadForm_eventually_unif_negDef M hc hneg t₀

end GlobalTheory
end

