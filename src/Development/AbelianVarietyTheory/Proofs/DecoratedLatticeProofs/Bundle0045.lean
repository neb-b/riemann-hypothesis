module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPattern
section
namespace GlobalTheory.SymResCount

open Formalism.L2.DIV

theorem mem_unipSym_iff {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) :
    g ∈ unipSym K r ρ κ ↔ ∀ a b : Fin r, ¬ (a.val < b.val ∧ ¬ (ρ ≤ a.val ∧ a.val < ρ + κ ∧ b.val = ρ + κ)) →
      (g : Matrix (Fin r) (Fin r) K) a b = (1 : Matrix (Fin r) (Fin r) K) a b := by
  constructor
  · rintro ⟨⟨hl, hd⟩, hc⟩ a b hab
    by_cases e : a = b
    · subst e; rw [hd a, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne e]
      have hne : a.val ≠ b.val := fun h => e (Fin.ext h)
      by_cases h1 : b.val < a.val
      · exact hl (show b.val < a.val from h1)
      · exact hc a b (by omega) (by omega) (by omega)
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (by omega), Matrix.one_apply_eq]
    · rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

def permFn (ρ κ i : ℕ) : ℕ := if i < κ then ρ + i else if i < κ + ρ then i - κ else i

def permInv (ρ κ a : ℕ) : ℕ := if a < ρ then κ + a else if a < ρ + κ then a - ρ else a

def perm (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : Fin r ≃ Fin r where
  toFun i := ⟨permFn ρ κ i.val, by unfold permFn; split_ifs <;> omega⟩
  invFun a := ⟨permInv ρ κ a.val, by unfold permInv; split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega
  right_inv a := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega

theorem perm_val {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (i : Fin r) : (perm r ρ κ hr i).val = permFn ρ κ i.val := rfl

theorem freePos_iff (ρ κ i j : ℕ) :
    GlobalTheory.SymRes.FreePos ρ κ i j ↔ (permFn ρ κ i < permFn ρ κ j ∧
      ¬ (ρ ≤ permFn ρ κ i ∧ permFn ρ κ i < ρ + κ ∧ permFn ρ κ j = ρ + κ)) := by
  unfold GlobalTheory.SymRes.FreePos permFn; split_ifs <;> omega

def reidx {K : Type} [CommRing K] (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : GL (Fin r) K ≃* GL (Fin r) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (perm r ρ κ hr)).toMulEquiv

theorem reidx_apply {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) (i j : Fin r) :
    ((reidx r ρ κ hr g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) (perm r ρ κ hr i) (perm r ρ κ hr j) =
      (g : Matrix (Fin r) (Fin r) K) i j := by
  simp [reidx, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem reidx_mem_iff {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) :
    reidx r ρ κ hr g ∈ unipSym K r ρ κ ↔ GlobalTheory.SymRes.IsPat ρ κ g := by
  rw [mem_unipSym_iff]
  constructor
  · intro h i j hf
    have := h (perm r ρ κ hr i) (perm r ρ κ hr j) (by rw [perm_val, perm_val, ← freePos_iff]; exact hf)
    rw [reidx_apply] at this
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]
  · intro h a b hab
    obtain ⟨i, rfl⟩ := (perm r ρ κ hr).surjective a
    obtain ⟨j, rfl⟩ := (perm r ρ κ hr).surjective b
    rw [reidx_apply, h i j (by rw [freePos_iff, ← perm_val hr, ← perm_val hr]; exact hab)]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]

end GlobalTheory.SymResCount

namespace GlobalTheory.SymResCount
open Formalism.L2.DIV

theorem conj_pat_onto : ∀ (K : Type) [CommRing K] [Finite K] (r ρ κ : ℕ), r = κ + (2 * ρ + 1) →
    ∀ m : GL (Fin r) K, (∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ) →
    ∀ g : GL (Fin r) K, m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ → GlobalTheory.SymRes.IsPat ρ κ g := by
  intro K _ _ r ρ κ hr m hm g hg
  have hr' : κ + ρ ≤ r := by omega
  haveI : Finite (GL (Fin r) K) := Finite.of_injective (fun u : GL (Fin r) K => (u : Matrix (Fin r) (Fin r) K)) Units.val_injective
  set S : Set (GL (Fin r) K) := {g | GlobalTheory.SymRes.IsPat ρ κ g} with hS
  set U : Set (GL (Fin r) K) := (unipSym K r ρ κ : Set (GL (Fin r) K)) with hU
  have hSU : (reidx (K := K) r ρ κ hr') '' S = U := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (reidx_mem_iff hr' x).2 hx
    · intro hh
      refine ⟨(reidx r ρ κ hr').symm h, (reidx_mem_iff hr' _).1 (by rw [MulEquiv.apply_symm_apply]; exact hh), by simp⟩
  have hinj : Function.Injective (fun x : GL (Fin r) K => m * x * m⁻¹) := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hc : (fun x : GL (Fin r) K => m * x * m⁻¹) '' S = U := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨x, hx, rfl⟩; exact hm x hx
    · rw [Set.ncard_image_of_injective S hinj, ← hSU, Set.ncard_image_of_injective S (reidx r ρ κ hr').injective]
    · exact Set.toFinite U
  have hg' : m * g * m⁻¹ ∈ U := hg
  rw [← hc] at hg'
  obtain ⟨x, hx, he⟩ := hg'
  have : x = g := hinj he
  rw [← this]; exact hx

end GlobalTheory.SymResCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetRepsMaximalIdealMatrixModMulStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open GlobalTheory.LowerHecke.MaxReps in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_reps_maximalIdealMatrix_mod_mul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ),
      valuation k (ϖ : k) = uniformizer k →
      ∀ (s : Finset D) (g : GL D k),
        (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D,
          g = κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := D) ϖ (indic s) * κ') →
        ∃ N : Finset (Matrix D A k), (∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧
          ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) →
            ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k,
              (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s g hg
  classical
  have existsRightInverse :
      ∃ Q : Matrix D D k, GlobalTheory.StepData.IntM Q ∧
        g.1 * Q = (ϖ : k) • (1 : Matrix D D k) := by
    obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
    have hϖ1 : (ϖ : k) ∈ 𝒪[k] := (hϖ ▸ uniformizer_lt_one).le
    have inverseIntegral (u : GL D k) (hu : u ∈ KO k D) :
        GlobalTheory.StepData.IntM u⁻¹.1 := by
      obtain ⟨v, rfl⟩ := hu
      rw [← map_inv]
      exact fun i j => (v⁻¹.1 i j).2
    have mulIntegral (X Y : Matrix D D k) (hX : GlobalTheory.StepData.IntM X)
        (hY : GlobalTheory.StepData.IntM Y) : GlobalTheory.StepData.IntM (X * Y) :=
      fun i j => sum_mem fun l _ => mul_mem (hX i l) (hY l j)
    let t := GlobalTheory.GLDoubling.torusElt (k := k) (n := D) ϖ (indic s)
    have ht : t.1 = diagonal fun i => (ϖ : k) ^ indic s i := by
      exact GlobalTheory.GLDoubling.val_torusElt ϖ (indic s)
    let D0 : Matrix D D k := diagonal fun i => (ϖ : k) ^ (1 - indic s i)
    have hD0 : t.1 * D0 = (ϖ : k) • (1 : Matrix D D k) := by
      rw [ht, diagonal_mul_diagonal, smul_one_eq_diagonal]
      congr 1
      funext i
      rw [← zpow_add₀ ϖ.ne_zero]
      simp
    refine ⟨(κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1, ?_, ?_⟩
    · refine mulIntegral _ _ (mulIntegral _ _ (inverseIntegral κ' hκ') ?_) (inverseIntegral κ hκ)
      intro i j
      simp only [D0, diagonal_apply]
      split_ifs
      · by_cases hi : i ∈ s <;> simp [indic, hi, hϖ1]
      · exact zero_mem _
    · have e1 : κ'.1 * (κ'⁻¹ : GL D k).1 = 1 := Units.mul_inv κ'
      have e2 : κ.1 * (κ⁻¹ : GL D k).1 = 1 := Units.mul_inv κ
      simp only [Units.val_mul]
      calc κ.1 * t.1 * κ'.1 * ((κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1)
          = κ.1 * (t.1 * (κ'.1 * (κ'⁻¹ : GL D k).1) * D0) * (κ⁻¹ : GL D k).1 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1, Matrix.mul_one, hD0, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e2]
  obtain ⟨Q, hQ, hgQ⟩ := existsRightInverse
  let M : AddSubgroup (Matrix D A k) := maxLat k A D
  let H := (mulLat (A := A) g.1).addSubgroupOf M
  have scaleMem {x : k} (hx : valuation k x < 1) : (ϖ : k)⁻¹ * x ∈ 𝒪[k] := by
    change valuation k _ ≤ 1
    have h0 : valuation k (ϖ : k) ≠ 0 := by simp
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one, hϖ, le_uniformizer_iff]
    exact hx
  let redMap : M →+ (D → A → 𝓀[k]) :=
    { toFun := fun ν i a =>
        IsLocalRing.residue 𝒪[k] ⟨(ϖ : k)⁻¹ * (ν : Matrix D A k) i a, scaleMem (ν.2 i a)⟩
      map_zero' := by
        funext i a
        simp only [AddSubgroup.coe_zero, Matrix.zero_apply, mul_zero, Pi.zero_apply]
        exact map_zero _
      map_add' := by
        intro ν ν'
        funext i a
        simp only [Pi.add_apply]
        rw [← map_add (f := _)]
        congr 1
        ext
        simp [mul_add] }
  have hK : redMap.ker ≤ H := by
    intro ν hν
    rw [AddMonoidHom.mem_ker] at hν
    rw [AddSubgroup.mem_addSubgroupOf]
    have hμ : ∀ i a, valuation k ((ϖ : k)⁻¹ * (ν : Matrix D A k) i a) < 1 := fun i a => by
      have := congrFun (congrFun hν i) a
      simp only [redMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one] at this
      exact this
    refine ⟨Q * ((ϖ : k)⁻¹ • (ν : Matrix D A k)), ?_, ?_⟩
    · intro i a
      rw [Matrix.mul_apply]
      refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
      rw [map_mul]
      calc
        _ ≤ 1 * valuation k (((ϖ : k)⁻¹ • (ν : Matrix D A k)) l a) :=
          mul_le_mul_of_nonneg_right (hQ i l) zero_le
        _ < 1 := by simpa using hμ l a
    · rw [← Matrix.mul_assoc, hgQ, Matrix.smul_mul, Matrix.one_mul, smul_smul,
        mul_inv_cancel₀ ϖ.ne_zero, one_smul]
  have : Finite (M ⧸ redMap.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).symm.toEquiv
  have : redMap.ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have : H.FiniteIndex := AddSubgroup.finiteIndex_of_le hK
  have : Finite (M ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ := Fintype.ofFinite (M ⧸ H)
  refine ⟨Finset.univ.image fun q : M ⧸ H => ((Quotient.out q : M) : Matrix D A k), ?_, ?_⟩
  · intro ν hν
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hν
    exact (Quotient.out q).2
  · intro ν hν
    have key : ∀ q : M ⧸ H, q = (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) ↔
        ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ((Quotient.out q : M) : Matrix D A k) = g.1 * μ := by
      intro q
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine exists_congr fun μ => and_congr_right fun _ => ?_
      show -((Quotient.out q : M) : Matrix D A k) + ν = g.1 * μ ↔ _
      rw [neg_add_eq_sub]
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) : M) : Matrix D A k),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).1 rfl⟩, ?_⟩
    rintro y ⟨hy, hyμ⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(key q).2 hyμ]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLattice
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

theorem homotheticLattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair,
    (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧
    (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧
      L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧
    ∀ d, HasCMBy d L → HasCMBy d L' := by
  intro L c hc
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  obtain ⟨hmem, -, -, hwp, -, -, -, -, -, hg2, hg3⟩ := Formalism.L2.Th1.F.homogeneity L c⁻¹ hc'
  refine ⟨Formalism.L2.Th1.F.scalePair L c⁻¹ hc', ?_, ?_, ?_, ?_, ?_⟩
  · intro z; rw [hmem, inv_inv]
  · rw [hg2, inv_pow, inv_inv]
  · rw [hg3, inv_pow, inv_inv]
  · intro z
    constructor
    · have := hwp (c * z)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, inv_pow, inv_inv] at this
      exact this
    · unfold PeriodPair.derivWeierstrassP
      rw [Formalism.L2.Th1.F.Homog.tsum_scale L c⁻¹ hc' (fun l => 2 / (z - l) ^ 3), mul_neg,
        ← tsum_mul_left]
      congr 1
      refine tsum_congr fun l => ?_
      have : z - c⁻¹ * (l : ℂ) = c⁻¹ * (c * z - l) := by field_simp
      rw [this, mul_pow, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
  · intro d hd
    exact Formalism.L2.Th1.F.hasCMByScale d L c⁻¹ hc' hd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnramifiedNearIntegralComplexPadic
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.ResidueUnr

open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_padicInt (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact z.norm_le_one

theorem norm_aeval_le (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) (g : ℤ_[l][X]) : ‖aeval x g‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro i _
  rw [Algebra.smul_def, norm_mul, norm_pow]
  exact mul_le_one₀ (norm_algebraMap_padicInt _) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hx)

theorem norm_aeval_lt (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) (g : ℤ_[l][X])
    (hg : g.map (PadicInt.toZMod (p := l)) = 0) : ‖aeval x g‖ < 1 := by
  have hd : ∀ n, (Polynomial.C (l : ℤ_[l])) ∣ Polynomial.C (g.coeff n) := by
    intro n
    have h0 : PadicInt.toZMod (g.coeff n) = 0 := by
      have := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f n) hg
      simpa [Polynomial.coeff_map] using this
    have hm : g.coeff n ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [← PadicInt.ker_toZMod]; exact h0
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
    exact map_dvd Polynomial.C hm
  obtain ⟨h, rfl⟩ : (Polynomial.C (l : ℤ_[l])) ∣ g := (Polynomial.C_dvd_iff_dvd_coeff _ _).2
    (fun n => by simpa using (Polynomial.C_dvd_iff_dvd_coeff _ _).1 (hd n) 0)
  rw [map_mul, aeval_C, norm_mul]
  have hl : ‖algebraMap ℤ_[l] (PadicAlgCl l) (l : ℤ_[l])‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  calc _ ≤ ‖algebraMap ℤ_[l] (PadicAlgCl l) (l : ℤ_[l])‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_aeval_le x hx h) (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hl

theorem exists_monic (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) : ∃ q : ℤ_[l][X], q.Monic ∧ aeval x q = 0 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at hx
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hx n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem exists_pow_near_one (x : PadicAlgCl l) (hx : ‖x‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ‖x ^ m - 1‖ < 1 := by
  obtain ⟨q, hqm, hq⟩ := exists_monic x hx.le
  have hq1 : q ≠ 1 := by rintro rfl; simp at hq
  set d := q.natDegree
  let r : ℕ → ℤ_[l][X] := fun k => (Polynomial.X ^ k) %ₘ q
  have hr : ∀ k, aeval x (r k) = x ^ k := by
    intro k
    have h := congrArg (aeval x) (modByMonic_add_div (Polynomial.X ^ k : ℤ_[l][X]) q)
    simpa [hq] using h
  have hdeg : ∀ k, (r k).natDegree < d := fun k => natDegree_modByMonic_lt _ hqm hq1
  let F : ℕ → (Fin d → ZMod l) := fun k i => PadicInt.toZMod ((r k).coeff i)
  obtain ⟨i, j, hij, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  have key : ∀ a b : ℕ, F a = F b → a < b → ∃ m : ℕ, 0 < m ∧ ‖x ^ m - 1‖ < 1 := by
    intro a b hab hlt
    have hsm : ‖x ^ b - x ^ a‖ < 1 := by
      rw [← hr b, ← hr a, ← map_sub]
      apply norm_aeval_lt x hx.le
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_sub, map_sub, Polynomial.coeff_zero]
      by_cases hn : n < d
      · have := congrFun hab ⟨n, hn⟩
        rw [sub_eq_zero]
        exact this.symm
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg b) (not_lt.1 hn)),
          coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg a) (not_lt.1 hn))]
        simp
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
    rw [e, norm_mul, norm_pow, hx, one_pow, one_mul] at hsm
    exact hsm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j hF h
  · exact key j i hF.symm h

theorem frob_inj (z : PadicAlgCl l) (hz : ‖z‖ ≤ 1) (h : ‖z ^ l - 1‖ < 1) : ‖z - 1‖ < 1 := by
  have hp := (Fact.out : l.Prime)
  have hpoly : (((Polynomial.X - 1) ^ l - (Polynomial.X ^ l - 1) : ℤ_[l][X])).map (PadicInt.toZMod (p := l)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, sub_pow_char, one_pow, sub_self]
  have h1 := norm_aeval_lt z hz _ hpoly
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at h1
  have h2 : ‖(z - 1) ^ l‖ < 1 := by
    have e : (z - 1) ^ l = ((z - 1) ^ l - (z ^ l - 1)) + (z ^ l - 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 h2

theorem frob_pow (a : ℕ) : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖z ^ (l ^ a) - 1‖ < 1 → ‖z - 1‖ < 1 := by
  induction a with
  | zero => intro z _ h; simpa using h
  | succ a ih =>
    intro z hz h
    apply frob_inj z hz
    apply ih (z ^ l) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz)
    rw [← pow_mul, ← pow_succ']
    exact h

theorem one_le_norm_prod (s : Multiset ℂ_[l]) (h : ∀ a ∈ s, 1 ≤ ‖a‖) : 1 ≤ ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun b hb => h b (Multiset.mem_cons_of_mem hb)
    nlinarith

theorem exists_root_near (x : ℂ_[l]) (m : ℕ) (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[l], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  set P : ℂ_[l][X] := Polynomial.X ^ m - Polynomial.C 1
  have hPm : P.Monic := by
    simpa [P] using (monic_X_pow_sub_C (1 : ℂ_[l]) hm.ne')
  have hcard : Multiset.card P.roots = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm hcard
  have hev := congrArg (eval x) hprod
  rw [eval_multiset_prod, Multiset.map_map] at hev
  by_contra hne
  push_neg at hne
  have hall : ∀ a ∈ P.roots, 1 ≤ ‖x - a‖ := by
    intro a ha
    apply hne a _
    have := (mem_roots hPm.ne_zero).1 ha
    simpa [P, sub_eq_zero] using this
  have := one_le_norm_prod (P.roots.map fun a => x - a) (by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    exact hall a ha)
  have e : (Multiset.map (eval x ∘ fun a => Polynomial.X - Polynomial.C a) P.roots).prod = (P.roots.map fun a => x - a).prod := by
    congr 1
    exact Multiset.map_congr rfl (fun a _ => by simp)
  rw [e] at hev
  rw [hev] at this
  simp [P] at this
  linarith

theorem exists_near_kur : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]), ‖x‖ ≤ 1 →
    ∃ y ∈ MaximalUnramifiedExtension l, ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1 := by
  intro l _ x hx
  obtain ⟨x', hx'⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hx'
  set X0 : ℂ_[l] := (x' : ℂ_[l]) with hX0
  have hn' : ‖X0‖ ≤ 1 := by
    have e : X0 = (X0 - x) + x := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_sub_rev]; exact hx'.le) hx)
  by_cases h0 : ‖X0‖ < 1
  · refine ⟨0, zero_mem _, by simp, ?_⟩
    rw [sub_zero]
    have e : x = (x - X0) + X0 := by ring
    rw [e]; exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx' h0)
  have h1 : ‖x'‖ = 1 := by rw [← PadicComplex.norm_extends]; exact le_antisymm hn' (not_lt.1 h0)
  obtain ⟨m0, hm0, hsm⟩ := exists_pow_near_one x' h1
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' l (Fact.out : l.Prime).ne_one
  have hz : ‖x' ^ m - 1‖ < 1 :=
    frob_pow a (x' ^ m) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1.le) (by rw [← pow_mul, mul_comm]; exact hsm)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
  have hz' : ‖X0 ^ m - 1‖ < 1 := by
    have e : X0 ^ m - 1 = ((x' ^ m - 1 : PadicAlgCl l) : ℂ_[l]) := by simp [hX0, PadicComplex.coe_eq]
    rw [e, PadicComplex.norm_extends]; exact hz
  obtain ⟨ζ, hζ, hd⟩ := exists_root_near X0 m hmpos hz'
  refine ⟨ζ, ?_, ?_, ?_⟩
  · unfold MaximalUnramifiedExtension
    exact Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hmpos, hm, hζ⟩)
  · have : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hmpos.ne').1 this).le
  · have e : x - ζ = (x - X0) + (X0 - ζ) := by ring
    rw [e]; exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx' hd)

end GlobalTheory.ResidueUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralHondaLogarithmPairShortWeierstrassStatement
section
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralHondaLogarithmPair_shortWeierstrass : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K), ‖(2 : K)‖ = 1 → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  first | exact @GlobalTheory.Honda.intLog_shortW | exact GlobalTheory.Honda.intLog_shortW | (intros; apply GlobalTheory.Honda.intLog_shortW <;> assumption)
end

