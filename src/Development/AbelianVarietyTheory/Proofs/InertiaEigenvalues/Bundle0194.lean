module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0190
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor
section
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

theorem norm_natCast_eq_rpow_padicValNat (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] (N : ℕ) (hN : N ≠ 0) :
    ‖(N : K)‖ = (l : ℝ) ^ (-(padicValNat l N : ℝ)) := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap',
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast,
    ← Real.rpow_intCast]
  congr 1
  push_cast
  simp [padicValRat.of_nat, Nat.padicValNat_def]

theorem wS_le_rpow (K : Type) [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) :
    wS K e n ≤ (l : ℝ) ^ (1 / ((l : ℝ) - 1)) * ((n : ℝ) + 1) *
      (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set m := n / e with hmdef
  have hv := GlobalTheory.DetPowContent.padicValNat_factorial_ge l (Fact.out : l.Prime) m
  have hm : (n : ℝ) / e - 1 ≤ m := by
    have h1 : n < (m + 1) * e := by
      have := Nat.lt_div_mul_add (a := n) (Nat.pos_of_ne_zero (NeZero.ne e))
      rw [hmdef]; linarith
    have h2 : (n : ℝ) < ((m : ℝ) + 1) * e := by exact_mod_cast h1
    rw [div_sub_one he.ne', div_le_iff₀ he]; linarith
  have hm1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have : m ≤ n := Nat.div_le_self n e
    exact_mod_cast Nat.add_le_add_right this 1
  unfold wS
  rw [← hmdef, norm_natCast_eq_rpow_padicValNat l K _ (Nat.factorial_ne_zero m)]
  have hexp : -(padicValNat l m.factorial : ℝ) ≤ Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
      -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) := by
    have h3 : (n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) = ((n : ℝ) / e) / ((l : ℝ) - 1) := by
      field_simp
    have h4 : ((n : ℝ) / e) / ((l : ℝ) - 1) ≤ (m : ℝ) / ((l : ℝ) - 1) + 1 / ((l : ℝ) - 1) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hq.le
    nlinarith
  calc (l : ℝ) ^ (-(padicValNat l m.factorial : ℝ))
      ≤ (l : ℝ) ^ (Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
          -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := Real.rpow_le_rpow_of_exponent_le hl.le hexp
    _ = ((m : ℝ) + 1) * (l : ℝ) ^ (1 / ((l : ℝ) - 1)) *
          (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
      rw [Real.rpow_add hl0, Real.rpow_add hl0, Real.rpow_logb hl0 hl.ne' (by positivity)]
    _ ≤ _ := by
      rw [mul_comm ((m : ℝ) + 1)]
      gcongr

end GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem R_le_invL_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    (k : ℝ) (hk : k < 1 / ((e : ℝ) * (l - 1))) : R O K l k ≤ invL l (S O K e) := by
  intro f hf
  rw [mem_invL_S_iff_tendsto O K l e f]
  have hR := mem_R.1 hf
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  set k0 := 1 / ((e : ℝ) * (l - 1)) with hk0
  set q := (l : ℝ) ^ (k - k0) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hl0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)
  set C := (l : ℝ) ^ (1 / ((l : ℝ) - 1)) with hC
  have hg : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * q ^ n)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [add_zero] at h1
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    exact h2.congr fun n => by ring
  have hprod := hR.mul hg
  rw [zero_mul] at hprod
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) (fun n => ?_) hprod
  have hw := wS_le_rpow K l e n
  have hrad : rad l k ^ n * q ^ n = (l : ℝ) ^ (-(n : ℝ) * k0) := by
    rw [rad, hqdef, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_mul_natCast hl0.le,
      ← Real.rpow_add hl0]
    congr 1; ring
  calc ‖coeff n f‖ * wS K e n ≤ ‖coeff n f‖ * (C * ((n : ℝ) + 1) * (l : ℝ) ^ (-(n : ℝ) * k0)) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖coeff n f‖ * rad l k ^ n * (C * (((n : ℝ) + 1) * q ^ n)) := by
        rw [← hrad]; ring

theorem mulVec_mem_vecs {ι : Type} [Fintype ι] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B) {v : ι → K⟦X⟧}
    (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i =>
  Subalgebra.sum_mem _ fun j _ => B.mul_mem (hM i j) (hv j)

end GlobalTheory.BK

open GlobalTheory.BK in
theorem GlobalTheory.BK.xi_trivialises_invL_S : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  refine ⟨fun k hk => R_le_invL_S O K l e k hk, fun w => ?_⟩
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set k : ℝ := (1 / ((e : ℝ) * l) + 1 / ((e : ℝ) * (l - 1))) / 2 with hkdef
  have hlt : 1 / ((e : ℝ) * l) < 1 / ((e : ℝ) * (l - 1)) :=
    one_div_lt_one_div_of_lt (by nlinarith) (by nlinarith)
  have hk1 : 1 / ((e : ℝ) * l) < k := by rw [hkdef]; linarith
  have hk2 : k < 1 / ((e : ℝ) * (l - 1)) := by rw [hkdef]; linarith
  have hRB := R_le_invL_S O K l e k hk2
  have hT := _root_.GlobalTheory.BK.xiExt_mem_Lk_iff O K l e a ι P k hk1
  set Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ with hY
  have hext : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι),
      P.xiExt v ∈ P.ext B ↔ ∀ τ, Y τ *ᵥ v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, PhiMod.xiExt_apply, Matrix.mulVec_mulVec, hY]
  have hM : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι), v ∈ P.Mext B ↔ ∀ τ, v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.Mext, mem_tot]
  have hYu : ∀ τ, IsUnit (Y τ).det := by
    intro τ
    rw [hY, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (P.mx_mul_mxInv τ)).mul (P.isUnit_det_xiMat τ)

  have hYR : ∀ τ i j, Y τ i j ∈ R O K l k := by
    intro τ i j
    have h0 : (fun _ : ZMod a => (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Mext (R O K l k) := by
      rw [hM]; intro τ' i'
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hext _ _).1 ((hT _).2 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1

  have hZR : ∀ τ i j, (Y τ)⁻¹ i j ∈ R O K l k := by
    intro τ i j
    have h0 : P.xiExt (fun τ' => (Y τ')⁻¹ *ᵥ (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Lk k := by
      rw [PhiMod.Lk, hext]; intro τ' i'
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hYu τ'), Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hM _ _).1 ((hT _).1 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1
  rw [PhiMod.MMl, hext, hM]
  constructor
  · intro h τ
    have := mulVec_mem_vecs (fun i j => hRB (hZR τ i j)) (h τ)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec] at this
  · intro h τ
    exact mulVec_mem_vecs (fun i j => hRB (hYR τ i j)) (h τ)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOfPowerTraces
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CharpolyNewton

open Polynomial Finset

variable {k : Type} [Field k]

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → k) (j : ℕ) :
    (j : k) * (univ.val.map f).esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ k j)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset k) (j : ℕ) :
    (j : k) * s.esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) j
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq [CharZero k] (s t : Multiset k)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) : ∀ j, s.esymm j = t.esymm j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hj0 : (j : k) ≠ 0 := by exact_mod_cast hj.ne'
      apply mul_left_cancel₀ hj0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq [CharZero k] (s t : Multiset k) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext j
  by_cases hj : j ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hj, Multiset.prod_X_sub_C_coeff t (hc ▸ hj), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hj
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

theorem charpoly_eq_prod_of_trace_pow : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (a : ℕ) (M : Matrix (Fin a) (Fin a) k) (B : Multiset k), Multiset.card B = a → (∀ n : ℕ, 1 ≤ n → (M ^ n).trace = (B.map (· ^ n)).sum) → M.charpoly = (B.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro k _ _ _ a M B hB h
  have hR : Multiset.card M.charpoly.roots = a := GlobalTheory.CharpolyPow.card_roots_charpoly M
  have hsplit : M.charpoly = (M.charpoly.roots.map fun b => X - C b).prod := by
    have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq M.charpoly_monic
      (by rw [hR, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
    exact this.symm
  rw [hsplit]
  refine prod_eq_of_psum_eq _ _ (by rw [hR, hB]) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hR, hB]
  · rw [← h n hn, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow]

end GlobalTheory.CharpolyNewton
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantOfLinear
section
noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.JHMatch

section Mod
variable {R : Type} [Ring R]

def HasFactors (M : Type) [AddCommGroup M] [Module R M] {ι : Type} (F : ι → ModuleCat.{0} R) : Prop :=
  ∃ r : CompositionSeries (Submodule R M), r.head = ⊥ ∧ r.last = ⊤ ∧
    ∃ e : ι ≃ Fin r.length, ∀ i, Nonempty (F i ≃ₗ[R] factor r (e i))

variable {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {ι κ : Type}

theorem HasFactors.finiteLength {F : ι → ModuleCat.{0} R} (h : HasFactors M F) : IsFiniteLength R M := by
  obtain ⟨r, h1, h2, -⟩ := h
  exact isFiniteLength_of_exists_compositionSeries ⟨r, h1, h2⟩

theorem HasFactors.of_same {F : ι → ModuleCat.{0} R} (h : HasFactors M F) (h' : SameFactors R M N) :
    HasFactors N F := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  obtain ⟨s, t, h3, h4, h5, h6, e', he'⟩ := h'
  obtain ⟨c, hc⟩ := CompositionSeries.jordan_holder r s (h1.trans h3.symm) (h2.trans h4.symm)
  refine ⟨t, h5, h6, (e.trans c).trans e', fun i => ?_⟩
  obtain ⟨f⟩ := he i
  obtain ⟨g⟩ := he' (c (e i))
  exact ⟨(f.trans (JordanHolderLattice.Iso.linearEquiv (hc (e i)))).trans g⟩

theorem HasFactors.of_equiv {F : ι → ModuleCat.{0} R} (h : HasFactors M F) (e : M ≃ₗ[R] N) :
    HasFactors N F := h.of_same (SameFactors.of_equiv h.finiteLength e)

theorem HasFactors.unique {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (h' : HasFactors M F') : ∃ e : ι ≃ κ, ∀ i, Nonempty (F i ≃ₗ[R] F' (e i)) := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  obtain ⟨s, h3, h4, e', he'⟩ := h'
  obtain ⟨c, hc⟩ := CompositionSeries.jordan_holder r s (h1.trans h3.symm) (h2.trans h4.symm)
  refine ⟨(e.trans c).trans e'.symm, fun i => ?_⟩
  obtain ⟨j, hj⟩ := e'.surjective (c (e i))
  have hj' : ((e.trans c).trans e'.symm) i = j := by
    simp [← hj]
  rw [hj']
  obtain ⟨f⟩ := he i
  obtain ⟨g⟩ := he' j
  rw [hj] at g
  exact ⟨(f.trans (JordanHolderLattice.Iso.linearEquiv (hc (e i)))).trans g.symm⟩

theorem HasFactors.reindex {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (c : ι ≃ κ) (hc : ∀ i, F' (c i) = F i) : HasFactors M F' := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  refine ⟨r, h1, h2, c.symm.trans e, fun j => ?_⟩
  obtain ⟨i, rfl⟩ := c.surjective j
  rw [hc, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact he i

theorem HasFactors.simple [IsSimpleModule R M] : HasFactors M (fun _ : Unit => ModuleCat.of R M) := by
  let r : CompositionSeries (Submodule R M) :=
    { length := 1
      toFun := ![⊥, ⊤]
      step := fun i => by
        fin_cases i
        exact bot_covBy_top }
  refine ⟨r, rfl, rfl, Equiv.ofUnique Unit (Fin 1), fun i => ⟨?_⟩⟩
  change M ≃ₗ[R] (↥(⊤ : Submodule R M) ⧸ (⊥ : Submodule R M).comap (⊤ : Submodule R M).subtype)
  exact Submodule.topEquiv.symm.trans (Submodule.quotEquivOfEqBot _ (by simp)).symm

theorem HasFactors.prod {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (h' : HasFactors N F') : HasFactors (M × N) (Sum.elim F F') := by
  obtain ⟨t, h1, h2, a, ha⟩ := h
  obtain ⟨s, h3, h4, c, hc⟩ := h'
  obtain ⟨r, h5, h6, e, he1, he2⟩ := exists_series_of_exact (R := R) (A := M) (C := N)
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd t h1 h2 s h3 h4
  refine ⟨r, h5, h6, (a.sumCongr c).trans e, ?_⟩
  rintro (i | j)
  · obtain ⟨u⟩ := ha i
    obtain ⟨v⟩ := he1 (a i)
    exact ⟨u.trans v⟩
  · obtain ⟨u⟩ := hc j
    obtain ⟨v⟩ := he2 (c j)
    exact ⟨u.trans v⟩

theorem HasFactors.zero [Subsingleton M] [IsEmpty ι] (F : ι → ModuleCat.{0} R) : HasFactors M F := by
  refine ⟨RelSeries.singleton _ ⊥, rfl, Subsingleton.elim _ _, Equiv.equivOfIsEmpty ι (Fin 0), fun i => ?_⟩
  exact isEmptyElim i

def succEquiv (m : ℕ) (ι : Type) : ι ⊕ (Fin m × ι) ≃ Fin (m + 1) × ι where
  toFun := Sum.elim (fun i => (0, i)) (fun p => (p.1.succ, p.2))
  invFun := fun p => Fin.cases (motive := fun _ => ι ⊕ (Fin m × ι)) (Sum.inl p.2) (fun j => Sum.inr (j, p.2)) p.1
  left_inv := by rintro (i | ⟨j, i⟩) <;> simp
  right_inv := by
    rintro ⟨j, i⟩
    induction j using Fin.cases <;> simp

theorem HasFactors.pi : ∀ {m : ℕ} {N : Fin m → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    {F : Fin m → ι → ModuleCat.{0} R}, (∀ j, HasFactors (N j) (F j)) →
    HasFactors (∀ j, N j) (fun p : Fin m × ι => F p.1 p.2)
  | 0, _, _, _, _, _ => HasFactors.zero _
  | m + 1, N, _, _, F, h =>
    (((h 0).prod (HasFactors.pi (F := fun j => F j.succ) fun j => h (Fin.succ j))).of_equiv
      (Fin.consLinearEquiv R N)).reindex (succEquiv m ι) (by rintro (i | ⟨j, i⟩) <;> rfl)

end Mod

section Rep
variable {k G : Type} [Field k] [Group G]

theorem equivariant_of_linear {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {π : Representation k G M} {π' : Representation k G N}
    (f : π.asModule →ₗ[MonoidAlgebra k G] π'.asModule) :
    ∃ f' : M →ₗ[k] N, (∀ g x, f' (π g x) = π' g (f' x)) ∧
      ∀ x, f' (π.asModuleEquiv x) = π'.asModuleEquiv (f x) := by
  let u := (Representation.IntertwiningMap.equivLinearMapAsModule π π').symm f
  exact ⟨u.toLinearMap, fun g x => LinearMap.congr_fun (u.isIntertwining' g) x, fun _ => rfl⟩

theorem chr_simple (χ : G →* kˣ) : IsSimpleModule (MonoidAlgebra k G) (chr χ).ρ.asModule := by
  have h : IsSimpleModule k (chr χ).ρ.asModule := by
    rw [isSimpleModule_iff_finrank_eq_one, (chr χ).ρ.asModuleEquiv.finrank_eq]
    simp
  have := IsSimpleModule.nontrivial k (chr χ).ρ.asModule
  refine { eq_bot_or_eq_top := fun S => ?_ }
  rcases eq_bot_or_eq_top (S.restrictScalars k) with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

def prodAsModule {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (π : Representation k G M) (π' : Representation k G N) :
    (π.prod π').asModule ≃ₗ[MonoidAlgebra k G] π.asModule × π'.asModule :=
  LinearEquiv.ofBijective
    (LinearMap.prod (asModuleMap (π := π.prod π') (π' := π) (LinearMap.fst k M N) fun _ _ => rfl)
      (asModuleMap (π := π.prod π') (π' := π') (LinearMap.snd k M N) fun _ _ => rfl))
    (Function.bijective_id (α := M × N))

theorem exists_subquot (T C : Ob k G) (Y : Submodule (MonoidAlgebra k G) T.ρ.asModule)
    (q : Y →ₗ[MonoidAlgebra k G] C.ρ.asModule) (hq : Function.Surjective q) :
    ∃ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom A₁ T j ∧ Function.Injective j ∧ IsHom A₁ C p ∧ Function.Surjective p := by
  have : Module.Finite k T.ρ.asModule := Module.Finite.equiv T.ρ.asModuleEquiv.symm
  have : Module.Finite k Y :=
    Module.Finite.of_injective (Y.subtype.restrictScalars k) Y.subtype_injective
  obtain ⟨A, e, he⟩ := exists_ob (Representation.ofModule' (k := k) (G := G) Y)
  have key : ∀ g x, e.symm (A.ρ g x) = MonoidAlgebra.of k G g • e.symm x := fun g x => by
    apply e.injective
    rw [e.apply_symm_apply]
    have := he g (e.symm x)
    rw [e.apply_symm_apply] at this
    rw [← this]
    congr 1
  refine ⟨A, T.ρ.asModuleEquiv.toLinearMap ∘ₗ Y.subtype.restrictScalars k ∘ₗ e.symm.toLinearMap,
    C.ρ.asModuleEquiv.toLinearMap ∘ₗ q.restrictScalars k ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    T.ρ.asModuleEquiv.injective.comp (Y.subtype_injective.comp e.symm.injective), fun g x => ?_,
    C.ρ.asModuleEquiv.surjective.comp (hq.comp e.symm.surjective)⟩
  · simp [key, Representation.asModuleEquiv_map_smul]
    rfl
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.restrictScalars_apply, key, map_smul]
    simp [Representation.asModuleEquiv_map_smul]
    rfl

theorem jh_match : ∀ {k G : Type} [Field k] [Group G] (T : Ob k G) (ω : G →* kˣ) (t μ s : ℕ) (C : Fin s → Ob k G), (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) → SameSS (piRep fun a => (C a).ρ) (piRep fun _ : Fin μ => refSum T ω t) → ∃ c : Fin s → Option (Fin t), (∀ a e, c a = some e → ∃ f, IsHom (C a) (chr (ω ^ (-(e.val : ℤ)))) f ∧ Function.Bijective f) ∧ (∀ a, c a = none → ∃ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin (C a).m → k)), IsHom A₁ T j ∧ Function.Injective j ∧ IsHom A₁ (C a) p ∧ Function.Surjective p) ∧ ∀ e, (Finset.univ.filter fun a => c a = some e).card = μ := by
  intro k G _ _ T ω t μ s C hC h
  have hT : IsFiniteLength (MonoidAlgebra k G) T.ρ.asModule :=
    finiteLength_asModule T.ρ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  obtain ⟨r, hr1, hr2⟩ := isFiniteLength_iff_exists_compositionSeries.mp hT
  have fT : HasFactors T.ρ.asModule (fun i : Fin r.length => ModuleCat.of (MonoidAlgebra k G) (factor r i)) :=
    ⟨r, hr1, hr2, Equiv.refl _, fun _ => ⟨LinearEquiv.refl _ _⟩⟩
  have fL := (HasFactors.pi (N := fun e : Fin t => (chr (ω ^ (-(e.val : ℤ)))).ρ.asModule) fun e =>
    @HasFactors.simple _ _ _ _ _ (chr_simple (ω ^ (-(e.val : ℤ))))).of_equiv
      (piAsModule fun e : Fin t => (chr (ω ^ (-(e.val : ℤ)))).ρ).symm
  have fR := (fT.prod fL).of_equiv (prodAsModule _ _).symm
  have fS := (HasFactors.pi (N := fun _ : Fin μ => (refSum T ω t).asModule) fun _ => fR).of_equiv
    (piAsModule fun _ : Fin μ => refSum T ω t).symm
  have fC := ((HasFactors.pi (N := fun a => (C a).ρ.asModule) fun a =>
    @HasFactors.simple _ _ _ _ _ (hC a)).of_equiv (piAsModule fun a => (C a).ρ).symm).of_same h
  obtain ⟨e, he⟩ := fC.unique fS
  refine ⟨fun a => Sum.elim (fun _ => none) (fun p => some p.1) (e (a, ())).2, fun a x hx => ?_,
    fun a hx => ?_, fun x => ?_⟩
  · obtain ⟨u⟩ := he (a, ())
    beta_reduce at hx
    generalize e (a, ()) = z at hx u
    rcases z with ⟨b, i | ⟨y, w⟩⟩
    · simp at hx
    · obtain rfl : y = x := by simpa using hx
      obtain ⟨f, hf1, hf2⟩ := equivariant_of_linear (π := (C a).ρ) (π' := (chr (ω ^ (-(y.val : ℤ)))).ρ) u.toLinearMap
      refine ⟨f, hf1, ?_⟩
      have : ⇑f ∘ (C a).ρ.asModuleEquiv = (chr (ω ^ (-(y.val : ℤ)))).ρ.asModuleEquiv ∘ u := funext hf2
      rw [← Function.Bijective.of_comp_iff _ (C a).ρ.asModuleEquiv.bijective, this]
      exact (LinearEquiv.bijective _).comp u.bijective
  · obtain ⟨u⟩ := he (a, ())
    beta_reduce at hx
    generalize e (a, ()) = z at hx u
    rcases z with ⟨b, i | ⟨y, w⟩⟩
    · let u' : (C a).ρ.asModule ≃ₗ[MonoidAlgebra k G] factor r i := u
      exact exists_subquot T (C a) (r i.succ) (u'.symm.toLinearMap ∘ₗ Submodule.mkQ _)
        (u'.symm.surjective.comp (Submodule.mkQ_surjective _))
    · simp at hx
  · refine Eq.trans ?_ (Finset.card_fin μ)
    symm
    refine Finset.card_bij (fun b _ => (e.symm (b, Sum.inr (x, ()))).1) (fun b _ => ?_) (fun b _ b' _ hb => ?_)
      (fun a ha => ?_)
    · have : ((e.symm (b, Sum.inr (x, ()))).1, ()) = e.symm (b, Sum.inr (x, ())) := rfl
      simp [this]
    · have : e.symm (b, Sum.inr (x, ())) = e.symm (b', Sum.inr (x, ())) := Prod.ext hb rfl
      simpa using this
    · refine ⟨(e (a, ())).1, Finset.mem_univ _, ?_⟩
      have h2 : (e (a, ())).2 = Sum.inr (x, ()) := by
        have := (Finset.mem_filter.mp ha).2
        beta_reduce at this
        generalize (e (a, ())).2 = z at this
        rcases z with i | ⟨y, w⟩
        · simp at this
        · simpa using this
      rw [← h2]
      simp

end Rep
end GlobalTheory.JHMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem isGauss_gC_of_le (l : ℕ) [Fact l.Prime] (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    IsGauss l ρ (gC l ρ) := by
  have h : ∃ N, IsGauss l ρ N := GlobalTheory.GaussExt.exists_gauss_acris l ρ h0 h1
  have e : gC l ρ = Classical.choose h := by
    funext x
    simp only [gC, dif_pos h]
  rw [e]
  exact Classical.choose_spec h

theorem isGauss_gC_target : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ (gC l ρ) :=
  fun l _ ρ h0 h1 => isGauss_gC_of_le l ρ h0 h1

end GlobalTheory.PMon.Gauss

end
end

