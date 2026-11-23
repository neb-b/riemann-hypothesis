module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiMemInvertedLattice
section
open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK

namespace PhiMod

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NeZero a]

theorem exists_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {v : Vec K a ι} (hv : v ∈ P.MMl) :
    ∃ N : ℕ, (l : K) ^ N • v ∈ P.MM := by
  have hc : ∀ p : ZMod a × ι, ∃ n : ℕ,
      (l : K⟦X⟧) ^ n * (P.mxInv p.1 *ᵥ v p.1) p.2 ∈ S O K e := by
    intro p
    obtain ⟨n, hn⟩ := mem_away.1 (mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 hv p.1)) p.2)
    exact ⟨n, by simpa using hn⟩
  choose n hn using hc
  refine ⟨Finset.univ.sup n, mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => ?_)⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, hc, smul_eq_C_mul, map_pow, map_natCast,
    pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem _ l) c) (hn (τ, i))

theorem mem_MMl_of_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {w : Vec K a ι} (N : ℕ)
    (h : (l : K) ^ N • w ∈ P.MM) : w ∈ P.MMl := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => mem_away.2 ⟨N, ?_⟩)
  have h1 := mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 h τ)) i
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_C_mul, map_pow, map_natCast] at h1
  simpa using h1

end PhiMod

theorem BKDat.phi_mem_MMl : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ v ∈ D.MMl, D.phi v ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D v hv
  obtain ⟨N, hN⟩ := D.toPhiMod.exists_lpow_smul_mem_MM hv
  have h := PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper _ hN
  rw [map_smul, smul_smul, ← pow_add] at h
  exact D.toPhiMod.mem_MMl_of_lpow_smul_mem_MM _ h

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiMemInvertedPrimeLatticeOfMemEisensteinInvaria
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem phi_mem_MMl_of_mem_Y : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.phi y ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  have hl : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero (algebraMap ℚ_[l] K)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
  have hE : E K l e ^ η • y ∈ D.M := hy.1
  have h0 : (l : K) ^ η • D.phi y ∈ D.MM := D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hE)
  have h1 : (l : K) ^ η • D.phi y ∈ D.MMl := D.ext_mono (le_away _ _) h0
  have hc : (C ((l : K)⁻¹ ^ η) : K⟦X⟧) ∈ invL l (S O K e) := by
    refine ⟨η, ?_⟩
    have : ((l : S O K e) : K⟦X⟧) ^ η * C ((l : K)⁻¹ ^ η) = 1 := by
      rw [show ((l : S O K e) : K⟦X⟧) = C (l : K) by simp, ← map_pow, ← map_mul, ← mul_pow,
        mul_inv_cancel₀ hl, one_pow, map_one]
    rw [this]; exact one_mem _
  have h2 := D.MMl.smul_mem ⟨_, hc⟩ h1
  convert h2 using 1
  rw [Subalgebra.smul_def]
  funext τ i
  simp only [Pi.smul_apply, smul_eq_mul, Subtype.coe_mk]
  rw [PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hl, one_pow,
    map_one, one_mul]

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatum
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem l_pow_eq (n : ℕ) : ((l : K⟦X⟧)) ^ n =
    E K l e ^ n - (X : K⟦X⟧) ^ e * ∑ i ∈ Finset.range n, (l : K⟦X⟧) ^ i * E K l e ^ (n - 1 - i) := by
  have h := (Commute.all ((l : K⟦X⟧)) (E K l e)).geom_sum₂_mul n
  have hE : (l : K⟦X⟧) - E K l e = -((X : K⟦X⟧) ^ e) := by simp [E]
  rw [hE] at h
  linear_combination -h

theorem l_pow_smul (n : ℕ) (y : Vec K a ι) : (l : K) ^ n • y =
    E K l e ^ n • y - (X : K⟦X⟧) ^ e • ∑ i ∈ Finset.range n, ((l ^ i : ℕ)) • (E K l e ^ (n - 1 - i) • y : Vec K a ι) := by
  have h1 : (l : K) ^ n • y = ((l : K⟦X⟧)) ^ n • y := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h1, l_pow_eq (e := e), sub_smul, mul_smul, Finset.sum_smul]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

variable (D : BKDat O K l e a ι η H)

theorem E_pow_smul_mem_M (j : ℕ) {m : Vec K a ι} (hm : m ∈ D.M) : E K l e ^ j • m ∈ D.M := by
  have := D.M.smul_mem (EIn l e (A O K) ^ j) hm
  simpa [Subalgebra.smul_def] using this

theorem E_pow_smul_mem_EM (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η) : E K l e ^ j • y ∈ D.EM η := by
  rw [mem_divE] at hy ⊢
  rw [smul_comm]
  exact E_pow_smul_mem_M D j hy

theorem E_pow_smul_mem_Y (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.Y) : E K l e ^ j • y ∈ D.Y := by
  rw [BKDat.Y, Descent.mem_invOf] at hy ⊢
  exact ⟨E_pow_smul_mem_EM D j hy.1, fun g => by rw [Descent.act_E_pow_smul, hy.2 g]⟩

theorem cls_E_pow_smul_mem_Z (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η)
    (h : ∀ g, D.desc.actPol g (D.cls y) = D.cls y) : D.cls (E K l e ^ j • y) ∈ D.Z := by
  refine ⟨⟨_, E_pow_smul_mem_EM D j hy, rfl⟩, fun g => ?_⟩
  have h' := congrArg (D.mulPol ⟨_, pow_mem (E_mem l e (Rpi O K l e)) j⟩) (h g)
  rw [Descent.actPol_cls] at h'
  change D.desc.actPol g (D.cls (E K l e ^ j • y)) = D.cls (E K l e ^ j • y)
  rw [Descent.actPol_cls, Descent.act_E_pow_smul]
  exact h'

end GlobalTheory.NgalDivisible

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  (D : BKDat O K l e a ι η H)

theorem l_pow_smul_Z {w : D.Pol} (hw : w ∈ D.Z) : ∃ z ∈ D.Z, (l : K) ^ η • w = D.vPol z := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := D.desc.mem_Z.1 hw
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsZ : D.cls s ∈ D.Z := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (cls_E_pow_smul_mem_Z D _ hy h)
  refine ⟨-D.cls s, neg_mem hsZ, ?_⟩
  have h0 : D.cls (E K l e ^ η • y) = 0 := D.cls_eq_zero_iff.2 (D.M_le_Man hy)
  rw [← map_smul, l_pow_smul (e := e) η y, ← hs, map_sub, h0, zero_sub, map_neg, PhiMod.vPol_cls]

theorem l_pow_smul_Y {y : Vec K a ι} (hy : y ∈ D.Y) : (l : K) ^ η • y ∈ D.Y' ⊔ D.Minv := by
  have hy' := hy
  rw [BKDat.Y, Descent.mem_invOf] at hy'
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsY : s ∈ D.Y := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (E_pow_smul_mem_Y D _ hy)
  have h1 : -((X : K⟦X⟧) ^ e • s) ∈ D.Y' :=
    D.desc.mem_Y'.2 ⟨-s, neg_mem hsY, smul_neg _ _⟩
  have h2 : E K l e ^ η • y ∈ D.Minv := by
    rw [BKDat.Minv, Descent.mem_invOf]
    exact ⟨hy'.1, fun g => by rw [Descent.act_E_pow_smul, hy'.2 g]⟩
  rw [l_pow_smul (e := e) η y, ← hs, sub_eq_neg_add]
  exact Submodule.add_mem_sup h1 h2

end GlobalTheory.NgalDivisible

theorem GlobalTheory.divisible_of_BKDat : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact ⟨fun _ hw => NgalDivisible.l_pow_smul_Z D hw, fun _ hy => NgalDivisible.l_pow_smul_Y D hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulConnectionSeriesTermMemLattice
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem lphi_pow_conn_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → E K l e ^ η • y₀ ∈ D.M → ∀ n : ℕ, ∃ w ∈ D.MM, (l : K) ^ (H + 2 * η + n * (η - 1)) • (D.lphi ^ (n + 1)) (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hy n
  have key (w : Vec K a ι) (hw : w ∈ D.MM) : (l : K) ^ η • D.phi w ∈ D.MM :=
    PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper w hw
  induction n with
  | zero =>
    have hE : E K l e ∈ S O K e := E_mem l e _
    have hNE : N K (E K l e) ∈ S O K e := by
      rw [N_apply]; exact mul_mem HasU.X_mem (derivative_mem_S hE)

    have h0 : (l : K) ^ η • D.phi y₀ ∈ D.MM :=
      D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hy)
    have hA : (l : K) ^ (H + 2 * η + 1) • D.phi y₀ ∈ D.MM := by
      have := D.l_pow_smul_mem_MM (H + η + 1) h0
      rwa [smul_smul, ← pow_add, show H + η + 1 + η = H + 2 * η + 1 by ring] at this

    have hk : E K l e ^ (H + η) • y₀ ∈ D.MM := by
      rw [pow_add, mul_smul]
      exact D.ext_mono (A_le_S l e) (D.lower _ hy)
    have h1 : E K l e ^ (H + η + 1) • D.conn y₀ ∈ D.MM := by
      have h2 := sub_mem (D.smul_mem_MM hE (D.conn_mem_MM hk))
        (D.smul_mem_MM (mul_mem (natCast_mem _ (H + η)) hNE) hk)
      convert h2 using 1
      rw [PhiMod.conn_smul, N_apply, derivative_pow]
      generalize H + η = k
      ext τ i : 2
      simp only [smul_eq_mul, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, N_apply]
      cases k with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel]; ring
    have h3 := D.smul_mem_Mext (A_le_S l e) h1
    rw [smul_smul, ← pow_add] at h3
    have hB := D.l_pow_smul_phi_mem_MM h3
    rw [show η + (H + η + 1) = H + 2 * η + 1 by ring] at hB
    refine ⟨(e : K⟦X⟧) • ((l : K) ^ (H + 2 * η + 1) • D.phi y₀) +
      (l : K) ^ (H + 2 * η + 1) • D.phi (D.conn y₀),
      add_mem (D.smul_mem_MM (natCast_mem _ e) hA) hB, ?_⟩
    have hc : D.conn ((X : K⟦X⟧) ^ e • y₀) = (X : K⟦X⟧) ^ e • ((e : K⟦X⟧) • y₀ + D.conn y₀) := by
      rw [PhiMod.conn_smul, smul_add, smul_smul]
      congr 2
      ext n
      rw [coeff_N, ← map_natCast (C : K →+* K⟦X⟧), coeff_mul_C, coeff_X_pow]
      split_ifs with h <;> simp [h]
    rw [zero_mul, add_zero, zero_add, pow_one, pow_one, hc, PhiMod.lphi_apply, PhiMod.phi_smul, map_add (f := _),
      PhiMod.phi_smul, map_pow, frob_X, ← pow_mul, map_natCast, mul_comm l e]
    simp only [smul_add, smul_smul, pow_succ]
    congr 1 <;> exact smul_comm _ _ _
  | succ n ih =>
    obtain ⟨w, hw, h⟩ := ih
    refine ⟨_, key w hw, ?_⟩
    rw [show H + 2 * η + (n + 1) * (η - 1) = (η - 1) + (H + 2 * η + n * (η - 1)) by ring, pow_add,
      mul_smul, pow_succ', Module.End.mul_apply, ← map_smul, h, PhiMod.lphi_apply, PhiMod.phi_smul,
      map_pow, frob_X, ← pow_mul, smul_smul, ← pow_succ, Nat.sub_add_cancel hη, smul_comm]
    congr 2
    ring

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulPhiMemLatticeOfMemFiltration
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem padicValNat_factorial_le_sub (l i j : ℕ) [hp : Fact l.Prime] (hji : j ≤ i) (hjl : j < l) :
    padicValNat l i.factorial ≤ i - j := by
  have hL : (l - 1) * padicValNat l i.factorial = i - (l.digits i).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := i) hp.out)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [_root_.Nat.padicValNat_def (n := 1)]
  have hpos : 0 < (l.digits i).sum := by
    rcases Nat.eq_zero_or_pos (l.digits i).sum with h0 | h0
    · exfalso
      have hne : l.digits i ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hi.ne'
      have h1 := Nat.getLast_digit_ne_zero l hi.ne'
      have h2 := List.sum_eq_zero_iff.1 h0 _ (List.getLast_mem hne)
      exact h1 h2
    · exact h0
  have hsum : (l.digits i).sum ≤ i := Nat.digit_sum_le l i
  have hl2 := hp.out.two_le
  set v := padicValNat l i.factorial
  rcases Nat.eq_zero_or_pos v with hv | hv
  · omega
  · have : (l - 1) * v ≤ i - 1 := by omega
    clear_value v
    have h3 : v + (l - 1) ≤ (l - 1) * v + 1 := by
      obtain ⟨L, hLe⟩ : ∃ L, l - 1 = L + 1 := ⟨l - 2, by omega⟩
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      rw [hLe]
      nlinarith
    omega

section Padic

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]


omit [IsUltrametricDist K] in
theorem norm_pow_sub_le_norm_factorial {i j : ℕ} (hji : j ≤ i) (hjl : j < l) :
    ‖(l : K)‖ ^ (i - j) ≤ ‖(i.factorial : K)‖ := by
  rw [norm_l, norm_natCast_eq l, Padic.norm_eq_zpow_neg_valuation (by
    exact_mod_cast i.factorial_ne_zero), Padic.valuation_natCast, inv_pow, zpow_neg, zpow_natCast]
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  exact inv_anti₀ (by positivity)
    (pow_le_pow_right₀ h1 (by
      simpa only [Nat.padicValNat_def] using padicValNat_factorial_le_sub l i j hji hjl))

theorem C_mem_S {e : ℕ} {c : K} (hc : ‖c‖ ≤ 1) : C c ∈ S O K e := by
  rw [← monomial_zero_eq_C_apply]
  exact monomial_mem_S (mul_le_one₀ hc (wS_nonneg _ _) (wS_le_one _ _))

theorem exists_frob_E_eq (e : ℕ) [NeZero e] : ∃ d ∈ S O K e, frob K l (E K l e) = C (l : K) * d := by
  refine ⟨1 + monomial (e * l) ((l : K)⁻¹), add_mem (one_mem _) (monomial_mem_S ?_), ?_⟩
  · rw [wS, Nat.mul_div_cancel_left _ (NeZero.pos e), norm_inv]
    have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    rw [inv_mul_le_one₀ h0]
    exact norm_natCast_le_of_dvd (Nat.dvd_factorial (Fact.out : l.Prime).pos le_rfl)
  · rw [E, map_add (f := _), map_pow, frob_X, map_natCast, monomial_eq_C_mul_X_pow, mul_add, mul_one,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ (l_ne_zero l), map_one, one_mul, ← pow_mul,
      mul_comm l e, add_comm, map_natCast]

theorem exists_frob_Ediv_eq (e : ℕ) [NeZero e] {i j : ℕ} (hji : j ≤ i) (hjl : j < l) :
    ∃ s ∈ S O K e, frob K l (Ediv K l e i) = C ((l : K) ^ j) * s := by
  obtain ⟨d, hd, hE⟩ := exists_frob_E_eq (O := O) (K := K) l e
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  refine ⟨C ((l : K) ^ (i - j) / (i.factorial : K)) * d ^ i, mul_mem (C_mem_S ?_) (pow_mem hd i), ?_⟩
  · rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ (norm_pow_sub_le_norm_factorial l hji hjl) (norm_nonneg _)
  · have key : (i.factorial : K)⁻¹ * (l : K) ^ i = (l : K) ^ j * ((l : K) ^ (i - j) / (i.factorial : K)) := by
      rw [mul_div_assoc', ← pow_add, Nat.add_sub_cancel' hji, div_eq_inv_mul]
    rw [Ediv, map_mul, frob_C, map_pow, hE, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, key,
      map_mul, mul_assoc]

theorem exists_frob_eq_of_mem_Fil (e : ℕ) [NeZero e] {j : ℕ} (hjl : j < l) {r : S O K e}
    (hr : r ∈ Fil O K l e j) : ∃ s ∈ S O K e, frob K l (r : K⟦X⟧) = C ((l : K) ^ j) * s := by
  obtain ⟨g, hg, h, rfl⟩ := (mem_Fil l).1 hr j
  have key : ∀ x ∈ FilPre O K l e j, ∃ s ∈ S O K e, frob K l (x : K⟦X⟧) = C ((l : K) ^ j) * s := by
    intro x hx
    have hx' : x ∈ Submodule.span (S O K e) {x : S O K e | ∃ i, j ≤ i ∧ (x : K⟦X⟧) = Ediv K l e i} := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, hxi⟩ := hx
      rw [hxi]
      exact exists_frob_Ediv_eq l e hi hjl
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨t, ht, h2⟩ := hy
      exact ⟨s + t, add_mem hs ht, by rw [Subalgebra.coe_add, map_add (f := _), h1, h2, mul_add]⟩
    | smul c x _ hx =>
      obtain ⟨s, hs, h1⟩ := hx
      exact ⟨frob K l c * s, mul_mem (frob_mem_S l c.2) hs, by
        rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, h1]; ring⟩
  obtain ⟨s, hs, h1⟩ := key g hg
  refine ⟨s + frob K l h, add_mem hs (frob_mem_S l h.2), ?_⟩
  rw [Subalgebra.coe_add, Subalgebra.coe_mul, map_add (f := _), map_mul, h1, mul_add]
  congr 2
  simp

end Padic

theorem phi_FilMM_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℕ), j < l → ∀ v ∈ D.FilMM j, ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v' := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j hjl v hv
  refine Submodule.smul_induction_on (p := fun v => ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v')
    hv (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨s, hs, hfs⟩ := exists_frob_eq_of_mem_Fil l e hjl hr
    have h3 := D.l_pow_smul_phi_mem_MM (k := η) (D.smul_mem_Mext (A_le_S l e) hn)
    refine ⟨s • ((l : K) ^ η • D.phi n), PhiMod.smul_mem_MM _ hs h3, ?_⟩
    rw [Subalgebra.smul_def, PhiMod.phi_smul, hfs, ← smul_eq_C_mul, smul_assoc,
      smul_comm ((l : K) ^ η) ((l : K) ^ j), smul_comm ((l : K) ^ η) s]
  · obtain ⟨v₁, h₁, e₁⟩ := hx
    obtain ⟨v₂, h₂, e₂⟩ := hy
    exact ⟨v₁ + v₂, add_mem h₁ h₂, by rw [map_add (f := _), smul_add, e₁, e₂, smul_add]⟩

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterEqZeroOfIsNilpotentStatement
section
open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ x : R, IsNilpotent x → T x = 0 := by
  first | exact @GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent | exact GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent | (intros; apply GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationUniqueUpToConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

noncomputable def bnMatRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) :
    Γ →* GL (Fin a) k :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom).comp s)

theorem bnMatRep_val {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
      = LinearMap.toMatrix b b (s g) := rfl

theorem bnMatRep_mulVec {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ)
    (v : W) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).mulVec (b.equivFun v)
      = b.equivFun (s g v) := by
  rw [bnMatRep_val]
  exact LinearMap.toMatrix_mulVec_repr b b (s g) v

theorem bnMatRep_isSSRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W)
    (hs : IsSS s) : IsSSRep (bnMatRep b s) := by
  intro U hU
  obtain ⟨U', hU', hc⟩ := hs (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) (by
    intro g v hv
    have := hU g _ hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at this ⊢
    rw [← bnMatRep_mulVec]
    exact this)
  refine ⟨U'.map (b.equivFun : W →ₗ[k] (Fin a → k)), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    refine ⟨s g v, hU' g v hv, ?_⟩
    exact (bnMatRep_mulVec b s g v).symm
  · have h := (Submodule.orderIsoMapComap b.equivFun).isCompl hc
    have h1 : (Submodule.orderIsoMapComap b.equivFun)
        (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) = U :=
      Submodule.map_comap_eq_of_surjective b.equivFun.surjective U
    rw [h1] at h
    exact h

theorem brauerNesbitt_abstract_of_matrix : (∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹) → ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ V), IsSS s → IsSS s' → (∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (s' g)) → ∃ e : W ≃ₗ[k] V, ∀ g v, e (s g v) = s' g (e v) := by
  intro H k Γ _ _ W _ _ _ V _ _ _ s s' hs hs' hc
  have hdim : Module.finrank k V = Module.finrank k W := by
    rw [← LinearMap.charpoly_natDegree (s 1), ← LinearMap.charpoly_natDegree (s' 1), hc]
  let b : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W
  let b' : Module.Basis (Fin (Module.finrank k W)) k V := Module.finBasisOfFinrankEq k V hdim
  obtain ⟨h, hh⟩ := H Γ k _ (bnMatRep b s) (bnMatRep b' s') (bnMatRep_isSSRep b s hs)
    (bnMatRep_isSSRep b' s' hs') (by
      intro g
      rw [bnMatRep_val, bnMatRep_val, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hc])
  let m : (Fin (Module.finrank k W) → k) ≃ₗ[k] (Fin (Module.finrank k W) → k) :=
    (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
  have hm : ∀ x, m x = (h : Matrix _ _ k).mulVec x := fun x => rfl
  refine ⟨b.equivFun.trans (m.trans b'.equivFun.symm), fun g v => ?_⟩
  apply b'.equivFun.injective
  rw [← bnMatRep_mulVec]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hm]
  rw [← bnMatRep_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
    ← Units.val_mul, hh g, inv_mul_cancel_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XPowSmulMemPrimePowAddFiltrationPhiModuleStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (j : ℕ), j ≤ l → ∀ w ∈ P.MM, ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j, (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  first | exact @GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | exact GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | (intros; apply GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM <;> assumption)
end

