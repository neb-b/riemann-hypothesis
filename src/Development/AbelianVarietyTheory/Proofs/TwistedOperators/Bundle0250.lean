module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSource
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}

structure NodeAgree (N : GlobalTheory.Grid.Node D) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (X : GlobalTheory.ChiGrid.Node) :
    Prop where

  sp : N.V = G'.V X

  lat : HEq N.Λ (G'.Λ X)

  cart : HEq (Formalism.IndefR.Links.cart N.M) (W.cart X)

  onb : HEq (Formalism.IndefR.Links.onb N.M) (W.onb X)

structure SpAgree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  vert : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → NodeAgree (G.V i j) W (.grid i j)

  core : ∀ i, i ≤ D.R.m → NodeAgree (G.P i) W (.core i)

  top : ∀ j, j ≤ D.R.m → NodeAgree (G.Xp j) W (.top j)

  q0 : G.q0 = GlobalTheory.ChiGrid.q0 D

  w0 : G.w0 = G'.pl.w G'.pl.v0

  e0 : G.e0 = G'.pl.depth sc G'.pl.v0

  places : G.toPlaceDat.W R.Pg = G'.pl.W0

  lvl : G.lvl R = G'.modul

  chiH : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chiH i = G'.ch.chiH i

  chi : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chi i = G'.ch.chi i

structure ArrAgree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  omX : ∀ i j, i < D.R.m → j ≤ D.R.m → HEq ((G.X i j).ω.toSgn true) (W.om (.chi i j))

  omT : ∀ t i j, i ≤ D.R.m → j < D.R.m → HEq (G.th t i j).ω (W.om (.mu t i j))

  omC : ∀ t j, j < D.R.m → HEq (G.col t j).ω (W.om (.top t j))

  omD : ∀ i, i < D.R.m → HEq ((G.dn i).ω.toSgn true) (W.om (.core i))

  vacX : ∀ i, i < D.R.m → HEq (G.X i 0).vac (W.vac i)

  cos : ∀ i, i < D.R.m → (∀ c, ∃ κ, HEq (G.vC i c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (G.vC i c) (W.cosVec i κ)

def Agree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop :=
  SpAgree G W ∧ ArrAgree G W

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def withArr (G : GridPre R) (X : ∀ i j, ArrS (G.V (i + 1) j) (G.V i j))
    (ωT : T → ∀ i j, WRep (G.nV i j).V (G.nV i (j + 1)).V) (vacT : ∀ i j, WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ)
    (ItT : ∀ i j, Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M)
    (ωC : T → ∀ j, WRep (G.Xp j).V (G.nX j).V) (vacC : ∀ j, WO (G.Xp j).V (G.nX j).V → ℂ)
    (ItC : ∀ j, Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M)
    (dn : ∀ i, ArrT (G.P (i + 1)) (G.P i))
    (ItU : ∀ i, Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M)
    (vC : ∀ i, G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ)) : GridPre R :=
  { G with X := X, ωT := ωT, vacT := vacT, ItT := ItT, ωC := ωC, vacC := vacC, ItC := ItC, dn := dn, ItU := ItU, vC := vC }

def withMeas (G : GridPre R) (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat) (mP : ∀ i, (G.P i).MeasDat)
    (mX : ∀ j, (G.nX j).MeasDat) : GridPre R :=
  { G with m00 := m00, mV := mV, mP := mP, mX := mX }

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGLZetaSumTrivialParameterSubOneLe
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

namespace GlobalTheory.GLZetaBound

theorem norm_mul_sub_one_le {a b : ℂ} {c : ℝ} (hc : 0 ≤ c) {m k : ℕ}
    (ha : ‖a - 1‖ ≤ (1 + c) ^ m - 1) (hb : ‖b - 1‖ ≤ (1 + c) ^ k - 1) :
    ‖a * b - 1‖ ≤ (1 + c) ^ (m + k) - 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [e, pow_add]
  have h1 : ‖(a - 1) * (b - 1)‖ ≤ ((1 + c) ^ m - 1) * ((1 + c) ^ k - 1) := by
    rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)
  calc ‖(a - 1) * (b - 1) + (a - 1) + (b - 1)‖
      ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ + ‖b - 1‖ := norm_add₃_le
    _ ≤ ((1 + c) ^ m - 1) * ((1 + c) ^ k - 1) + ((1 + c) ^ m - 1) + ((1 + c) ^ k - 1) := by
        gcongr
    _ = (1 + c) ^ m * (1 + c) ^ k - 1 := by ring

theorem norm_inv_one_sub_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have h1 : 1 - ‖y‖ ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    rwa [norm_one] at this
  have h2 : (1 : ℂ) - y ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have e : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
  rw [e, norm_div, div_le_iff₀ (norm_pos_iff.2 h2)]
  nlinarith [norm_nonneg y]

theorem norm_eulerFac_sub_one_le {B : Multiset ℂˣ} {x : ℂ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ ≤ δ) : ‖GlobalTheory.LFun.eulerFac B x - 1‖ ≤ (1 + 2 * δ) ^ B.card - 1 := by
  rw [GlobalTheory.LFun.eulerFac_eq_prod]
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih =>
    have h1 := ih fun c hc => h c (Multiset.mem_cons_of_mem hc)
    have h2 := h b (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm B.card 1]
    refine norm_mul_sub_one_le (by linarith) ?_ h1
    rw [pow_one]
    have := norm_inv_one_sub_sub_one_le (h2.trans hδ)
    linarith

theorem norm_prod_one_sub_sub_one_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h : ∀ i ∈ s, ‖z i‖ ≤ δ) : ‖∏ i ∈ s, (1 - z i) - 1‖ ≤ (1 + 2 * δ) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := ih fun c hc => h c (Finset.mem_insert_of_mem hc)
    have h2 := h a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm s.card 1]
    refine norm_mul_sub_one_le (by linarith) ?_ h1
    rw [pow_one]
    have e : (1 - z a) - 1 = -z a := by ring
    rw [e, norm_neg]
    linarith

theorem one_add_two_mul_pow_sub_one_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (m : ℕ) :
    (1 + 2 * δ) ^ m - 1 ≤ 3 ^ m * δ := by
  have key : (1 + 2 * δ) ^ m - 1 ≤ (3 ^ m - 1) * δ := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h3 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      have hf : 0 ≤ (1 + 2 * δ) ^ m - 1 := by
        have : (1 : ℝ) ≤ (1 + 2 * δ) ^ m := one_le_pow₀ (by linarith)
        linarith
      have e : (1 + 2 * δ) ^ (m + 1) - 1 = (1 + 2 * δ) * ((1 + 2 * δ) ^ m - 1) + 2 * δ := by ring
      rw [e, pow_succ]
      have : (1 + 2 * δ) * ((1 + 2 * δ) ^ m - 1) ≤ (3 / 2) * ((3 ^ m - 1) * δ) := by
        have : 1 + 2 * δ ≤ 3 / 2 := by linarith
        exact mul_le_mul this ih hf (by norm_num)
      nlinarith
  have : (3 ^ m - 1) * δ ≤ 3 ^ m * δ := by nlinarith
  linarith

theorem norm_trivial_sub_one_le : ∀ (q : ℕ), 2 ≤ q → ∀ (r t : ℕ), r + 5 ≤ t → ∀ (B : Multiset ℂˣ), B.card = r → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ X : ℂ, ‖X‖ = (q : ℝ) ^ (-((1 + (t : ℝ)) / 2)) → ‖eulerFac B X * eulerFac (B.map fun β => β⁻¹) X * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℂ) ^ i)⁻¹) - 1‖ ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro q hq r t hrt B hB hβ X hX
  set δ : ℝ := ((q : ℝ) ^ 2)⁻¹ with hδdef
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : δ ≤ 1 / 4 := by
    rw [hδdef]
    have : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hrt' : (r : ℝ) + 5 ≤ t := by exact_mod_cast hrt
  have hbx : (q : ℝ) ^ (((r : ℝ) - 1) / 2) * ‖X‖ ≤ δ := by
    rw [hX, ← Real.rpow_add hq0]
    have e : δ = (q : ℝ) ^ (-(2 : ℝ)) := by
      rw [hδdef, Real.rpow_neg hq0.le, Real.rpow_two]
    rw [e]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    linarith
  have hB1 : ∀ b ∈ B, ‖(b : ℂ) * X‖ ≤ δ := by
    intro b hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ b hb).1 (norm_nonneg _)).trans hbx
  have hB2 : ∀ b ∈ B.map (fun β : ℂˣ => β⁻¹), ‖(b : ℂ) * X‖ ≤ δ := by
    intro b hb
    obtain ⟨β, hβB, rfl⟩ := Multiset.mem_map.1 hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ β hβB).2 (norm_nonneg _)).trans hbx
  have h1 := norm_eulerFac_sub_one_le hδ0 (by linarith) hB1
  have h2 := norm_eulerFac_sub_one_le hδ0 (by linarith) hB2
  have h3 := norm_prod_one_sub_sub_one_le (Finset.Ioc t (r + t)) (fun i => ((q : ℂ) ^ i)⁻¹) hδ0
    (by
      intro i hi
      have hi2 : 2 ≤ i := by
        have := (Finset.mem_Ioc.1 hi).1; omega
      rw [norm_inv, norm_pow, Complex.norm_natCast, hδdef]
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ hq1 hi2)
  rw [Multiset.card_map] at h2
  rw [Nat.card_Ioc, show r + t - t = r by omega] at h3
  rw [hB] at h1 h2
  have h12 := norm_mul_sub_one_le (by linarith) h1 h2
  have h123 := norm_mul_sub_one_le (by linarith) h12 h3
  have h4 := one_add_two_mul_pow_sub_one_le hδ0 hδ (r + r + r)
  have e27 : (3 : ℝ) ^ (r + r + r) = 27 ^ r := by
    rw [show r + r + r = 3 * r by ring, pow_mul]; norm_num
  rw [e27] at h4
  exact h123.trans h4

end GlobalTheory.GLZetaBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormUnitaryZetaSumTrivialBoundSubOneLe
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

namespace GlobalTheory.FinZeta.UnitaryBound

open GlobalTheory.LFun

theorem norm_prod_sub_one_le (c : ℝ) (M : Multiset ℂ) (h : ∀ z ∈ M, ‖z - 1‖ ≤ c) :
    ‖M.prod - 1‖ ≤ (1 + c) ^ M.card - 1 := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have h1 := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
    have h2 := h a (Multiset.mem_cons_self _ _)
    have hc : 0 ≤ c := (norm_nonneg _).trans h2
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have e : a * M.prod - 1 = (a - 1) * (M.prod - 1) + (a - 1) + (M.prod - 1) := by ring
    rw [e]
    have h3 : ‖(a - 1) * (M.prod - 1)‖ ≤ c * ((1 + c) ^ M.card - 1) := by
      rw [norm_mul]; exact mul_le_mul h2 h1 (norm_nonneg _) hc
    have h4 : ‖(a - 1) * (M.prod - 1) + (a - 1) + (M.prod - 1)‖ ≤
        ‖(a - 1) * (M.prod - 1)‖ + ‖a - 1‖ + ‖M.prod - 1‖ :=
      by
        linarith [norm_add_le ((a - 1) * (M.prod - 1) + (a - 1)) (M.prod - 1), norm_add_le ((a - 1) * (M.prod - 1)) (a - 1)]
    nlinarith

theorem norm_inv_one_sub_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) : ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have h1 : 1 / 2 ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    rw [norm_one] at this
    linarith
  have hne : (1 - y) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    norm_num at h1
  have hm : (1 - y) * (1 - y)⁻¹ = 1 := mul_inv_cancel₀ hne
  have e : (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by linear_combination hm
  rw [e, norm_mul, norm_inv]
  have hpos : 0 < ‖1 - y‖ := by linarith
  rw [mul_inv_le_iff₀ hpos]
  nlinarith [norm_nonneg y]

theorem one_add_pow_sub_one_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    (1 + c) ^ n - 1 ≤ (2 ^ n - 1) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    rw [pow_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + c),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) hc0) (sub_nonneg.2 hc1)]

theorem norm_zetaSum_sub_one_le : ∀ (q r t : ℕ), 2 ≤ q → r + 5 ≤ t → ∀ α : Fin (r / 2) → ℂˣ,
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ‖eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) *
      ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1‖ ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro q r t hq hrt α hα
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  set δ : ℝ := ((q : ℝ) ^ 2)⁻¹ with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ, inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have key : ∀ a b : ℕ, a + 2 ≤ b → (q : ℝ) ^ a * ((q : ℝ) ^ b)⁻¹ ≤ δ := by
    intro a b hab
    obtain ⟨k, rfl⟩ : ∃ k, b = a + 2 + k := ⟨b - (a + 2), by omega⟩
    have hpa : (0 : ℝ) < (q : ℝ) ^ a := by positivity
    rw [show (q : ℝ) ^ (a + 2 + k) = (q : ℝ) ^ a * ((q : ℝ) ^ 2 * (q : ℝ) ^ k) by ring, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hpa.ne', one_mul, hδ]
    apply inv_anti₀ (by positivity)
    have : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_pow₀ hq1
    nlinarith [show (0 : ℝ) < (q : ℝ) ^ 2 by positivity]
  have hbound : ((q : ℝ) ^ 2) ^ (((r : ℝ) - 1) / 2) ≤ (q : ℝ) ^ r := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hent : ∀ b ∈ bcParam r α, ‖(b : ℂ)‖ ≤ (q : ℝ) ^ r := by
    intro b hb
    simp only [bcParam, Multiset.mem_add, Multiset.mem_map, Finset.mem_univ_val, true_and,
      Multiset.mem_replicate] at hb
    have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    rcases hb with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨_, rfl⟩
    · exact (hα i).2.trans hbound
    · rw [Units.val_inv_eq_inv_val, norm_inv]
      have hpos : 0 < ((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hq2 _
      calc ‖(α i : ℂ)‖⁻¹ ≤ (((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)))⁻¹ := inv_anti₀ hpos (hα i).1
        _ = ((q : ℝ) ^ 2) ^ (((r : ℝ) - 1) / 2) := by rw [Real.rpow_neg hq2.le, inv_inv]
        _ ≤ _ := hbound
    · simp only [Units.val_one, norm_one]
      exact one_le_pow₀ hq1
  set x : ℂ := ((q : ℂ) ^ (t + 1))⁻¹ with hx
  have hxn : ‖x‖ = ((q : ℝ) ^ (t + 1))⁻¹ := by rw [hx, norm_inv, norm_pow, Complex.norm_natCast]
  set M1 : Multiset ℂ := (bcParam r α).map fun b : ℂˣ => (1 - (b : ℂ) * x)⁻¹ with hM1
  set M2 : Multiset ℂ := (Finset.range r).val.map fun j => 1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹ with hM2
  have heq : eulerFac (bcParam r α) x * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) =
      (M1 + M2).prod := by
    rw [Multiset.prod_add, eulerFac_eq_prod]
    rfl
  have hcard : (M1 + M2).card = r + r := by
    simp [hM1, hM2, GlobalTheory.LGrp.card_bcParam]
  have hfac : ∀ z ∈ M1 + M2, ‖z - 1‖ ≤ 2 * δ := by
    intro z hz
    rcases Multiset.mem_add.1 hz with hz | hz
    · obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hz
      have hbx : ‖(b : ℂ) * x‖ ≤ δ := by
        rw [norm_mul, hxn]
        exact (mul_le_mul_of_nonneg_right (hent b hb) (by positivity)).trans (key r (t + 1) (by omega))
      exact (norm_inv_one_sub_sub_one_le (by linarith)).trans (by linarith)
    · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hz
      have hj' : j < r := Finset.mem_range.1 hj
      have : ‖(1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1‖ = (q : ℝ) ^ j * ((q : ℝ) ^ (r + t))⁻¹ := by
        rw [sub_sub_cancel_left, norm_neg, norm_mul, norm_inv, norm_pow, norm_pow, norm_neg, Complex.norm_natCast]
      rw [this]
      linarith [key j (r + t) (by omega)]
  rw [heq]
  refine (norm_prod_sub_one_le _ _ hfac).trans ?_
  rw [hcard]
  refine (one_add_pow_sub_one_le (by linarith) (by linarith) _).trans ?_
  have h4 : (2 : ℝ) ^ (r + r) = 4 ^ r := by rw [← two_mul, pow_mul]; norm_num
  have ha : (1 : ℝ) ≤ 4 ^ r := one_le_pow₀ (by norm_num)
  have h16 : (16 : ℝ) ^ r = (4 ^ r) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h27 : (16 : ℝ) ^ r ≤ 27 ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
  have hk : 2 * ((4 : ℝ) ^ r - 1) ≤ 27 ^ r := by nlinarith
  rw [h4]
  calc ((4 : ℝ) ^ r - 1) * (2 * δ) = (2 * ((4 : ℝ) ^ r - 1)) * δ := by ring
    _ ≤ 27 ^ r * δ := mul_le_mul_of_nonneg_right hk hδ0

end GlobalTheory.FinZeta.UnitaryBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin)
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LowerMembers

theorem pairing_eq_zero : ∀ (X : ProvA), Formalism.MainNotions.SchurIrreducible.admQ5 X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → ∀ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de → (∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → ∀ i : ℕ, 1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (e : Ix (al.length + be.length - i) (ga.length + de.length - i) ≃ Fin V.rank) (e' : Ix (al.length + de.length + t) (ga.length + be.length) ≃ Fin W.rank) (m' : ℤ) (aS : ℚ) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] (X.ds _ _ (lamA' t al be ga de)).U.H) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (b : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] ℂ), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat (M'.ε τ) e' → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches (X.ds _ _ (lamA' t al be ga de)) M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → GlobalTheory.Chain.IoLift.IsKAct M' τ a' → (∀ Y ∈ lieAt W τ, ∀ P y, b (locT ε (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y + b P (a' Y y) = 0) → b = 0 := by
  intro X h5 hAR t al be ga de hd hbig i hi hip hiq D V W S' M' τ ε e e' m' aS U' a' b he he' hm' h₂ ha hb
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ ε (M'.ε τ) e e' he he'
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm ((X.ds _ _ (lamA' t al be ga de)).ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm ((X.ds _ _ (lamA' t al be ga de)).ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = (X.ds _ _ (lamA' t al be ga de)).ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  let B' : Pol _ _ _ _ →ₗ[ℂ] (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] ℂ :=
    { toFun := fun P => (b (κ.symm P)).comp j
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have hB' : ∀ P v, B' (κ P) v = b P (j v) := fun P v => by simp [B']
  have h0 : B' = 0 := _root_.GlobalTheory.NoInvPairing.no_pairing_smaller_source X h5 hAR t al be ga de hd hbig i hi hip hiq B' (fun Y hY P y => by
    obtain ⟨P, rfl⟩ := κ.surjective P
    have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
    have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
    have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j ((X.ds _ _ (lamA' t al be ga de)).HK.act Y y) -
        ((aS : ℂ) * Y.trace) • j y := by
      have h7 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
          j ((X.ds _ _ (lamA' t al be ga de)).HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
        refine Subtype.ext (U'.injective ?_)
        rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
      rw [h7, map_add (f := _), LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
        sub_eq_add_neg, ← neg_smul]
      congr 2
      ring
    have h := hb _ hY' P (j y)
    rw [h6, fr_toFrame, trace_toFrame, h4] at h
    rw [← hκ.2, hB', hB', ← h]
    simp [plainMat])
  refine LinearMap.ext fun P => LinearMap.ext fun z => ?_
  obtain ⟨v, rfl⟩ := hsurj z
  rw [← hB', h0]
  rfl

end GlobalTheory.LowerMembers

end
end

