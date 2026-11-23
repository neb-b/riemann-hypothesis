module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationQPowerMemFrobeniusSpan

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootsActFaithfullyLaurent
section
noncomputable section
namespace GlobalTheory.DeltaInv
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.PsiShiftProof GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters

theorem root_eq {l : ℕ} [hl : Fact l.Prime] {z w : ℤ_[l]} (hz : z ^ (l - 1) = 1) (hw : w ^ (l - 1) = 1)
    (h : PadicInt.toZMod z = PadicInt.toZMod w) : z = w :=
  by
  have hn : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  have key : (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) * (z - w) = 0 := by
    rw [geom_sum₂_mul, hz, hw, sub_self]
  have hres : PadicInt.toZMod (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) =
      ((l - 1 : ℕ) : ZMod l) * PadicInt.toZMod z ^ (l - 1 - 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl (g := fun _ => PadicInt.toZMod z ^ (l - 1 - 1))]
    · simp
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
      congr 1
      omega
  have hz0 : PadicInt.toZMod z ≠ 0 := by
    intro h0
    have h1 := congrArg PadicInt.toZMod hz
    rw [map_pow, h0, zero_pow hn.ne', map_one] at h1
    exact zero_ne_one h1
  have hl0 : ((l - 1 : ℕ) : ZMod l) ≠ 0 := by
    intro h0
    have := Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff (ZMod l) l _).mp h0)
    omega
  have hs : (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) ≠ 0 := by
    intro h0
    apply mul_ne_zero hl0 (pow_ne_zero _ hz0)
    rw [← hres, h0, map_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hs)

theorem exists_mul_pow {k : Type} [Field k] (c : k⸨X⸩) (t : k⟦X⟧) :
    ∃ (N : ℕ) (b : k⟦X⟧), (vv k * (t : k⸨X⸩)) ^ N * c = (b : k⸨X⸩) :=
  by
  refine ⟨(-c.order).toNat, PowerSeries.X ^ c.order.toNat * t ^ (-c.order).toNat * c.powerSeriesPart, ?_⟩
  have hc := LaurentSeries.single_order_mul_powerSeriesPart c
  have hN : ((-c.order).toNat : ℤ) + c.order = (c.order.toNat : ℤ) := by omega
  have hs : ∀ n : ℕ, (HahnSeries.single (1 : ℤ) (1 : k)) ^ n = HahnSeries.single (n : ℤ) 1 := by
    intro n
    rw [HahnSeries.single_pow]
    simp
  conv_lhs => arg 2; rw [← hc]
  rw [vv_eq_coe_X, map_mul, map_mul, map_pow, map_pow, HahnSeries.ofPowerSeries_X, mul_pow, hs, hs]
  calc (HahnSeries.single ((-c.order).toNat : ℤ) (1 : k) * (t : k⸨X⸩) ^ (-c.order).toNat) *
        (HahnSeries.single c.order 1 * (c.powerSeriesPart : k⸨X⸩))
      = (HahnSeries.single ((-c.order).toNat : ℤ) (1 : k) * HahnSeries.single c.order 1) *
          (t : k⸨X⸩) ^ (-c.order).toNat * (c.powerSeriesPart : k⸨X⸩) := by ring
    _ = _ := by rw [HahnSeries.single_mul_single, hN, one_mul]

theorem coeff_one_opp (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (z : ℤ_[l]) :
    PowerSeries.coeff 1 (onePlusPow k l z) = ZMod.castHom (dvd_refl l) k (PadicInt.toZMod z) :=
  by
  unfold onePlusPow
  rw [PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, Ring.choose_one_right, smul_eq_mul, mul_one]
  rfl

theorem main (l : ℕ) [hl : Fact l.Prime] (k : Type) [Field k] [CharP k l] (R : RingPG k l)
    (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) :
    ∃ σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩),
      (∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩)) ∧
      Function.Injective σ ∧ ∀ c, (∀ z, σ z c = c) ↔ ∃ c₀, ι c₀ = c :=
  by
  have hne : l - 1 ≠ 0 := (Nat.sub_pos_of_lt hl.out.one_lt).ne'
  set σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩) :=
    fun z => GlobalTheory.PsiShiftProof.delPi k (Units.ofPowEqOne z.1 (l - 1) z.2 hne) with hσ
  have hσc : ∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩) := by
    intro z b
    rw [hσ, GlobalTheory.PsiShiftProof.delPi_coe]
    rfl
  have hinj : Function.Injective (fun b : k⟦X⟧ => (b : k⸨X⸩)) := HahnSeries.ofPowerSeries_injective
  have hfix : ∀ z (a : k⟦X⟧), σ z (ι (a : k⸨X⸩)) = ι (a : k⸨X⸩) := by
    intro z a
    obtain ⟨b, hb⟩ := H.2.1 a
    rw [hb, hσc, (H.2.2.1 b).2 ⟨a, hb⟩ z.1 z.2]
  have hιv : ∀ z, σ z (ι (vv k)) = ι (vv k) := by
    intro z
    rw [vv_eq_coe_X, hfix]
  have hv0 : ι (vv k) ≠ 0 := by
    exact (map_ne_zero ι).mpr (vv_ne_zero k)
  refine ⟨σ, hσc, ?_, ?_⟩
  · intro z w hzw
    have h1 := congrArg (fun f : k⸨X⸩ →+* k⸨X⸩ => f (1 + vv k)) hzw
    simp only [hσ, GlobalTheory.PsiShiftProof.del_one_add] at h1
    have h2 := congrArg (PowerSeries.coeff 1) (hinj h1)
    simp only [Units.val_ofPowEqOne, coeff_one_opp] at h2
    exact Subtype.ext (root_eq z.2 w.2 ((ZMod.castHom (dvd_refl l) k).injective h2))
  · intro c
    constructor
    · intro hc
      obtain ⟨u, hu⟩ := H.1
      obtain ⟨N, b, hb⟩ := exists_mul_pow c ((u : k⟦X⟧) * PowerSeries.X ^ (l - 2))
      have hv : vv k * (((u : k⟦X⟧) * PowerSeries.X ^ (l - 2) : k⟦X⟧) : k⸨X⸩) = ι (vv k) := by
        rw [hu, map_mul, map_pow, ← vv_eq_coe_X]
        have : l - 1 = (l - 2) + 1 := by have := hl.out.two_le; omega
        rw [this, pow_succ]
        ring
      rw [hv] at hb
      have hbinv : ∀ z : ℤ_[l], z ^ (l - 1) = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z b = b := by
        intro z hz
        apply hinj
        show ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z b : k⟦X⟧) : k⸨X⸩) = (b : k⸨X⸩)
        have e := hσc ⟨z, hz⟩ b
        dsimp only at e
        rw [← e, ← hb, map_mul, map_pow, hc, hιv]
      obtain ⟨a, ha⟩ := (H.2.2.1 b).1 hbinv
      refine ⟨(a : k⸨X⸩) * (vv k ^ N)⁻¹, ?_⟩
      rw [map_mul, map_inv₀, map_pow, ha, ← hb]
      field_simp
    · rintro ⟨c₀, rfl⟩ z
      obtain ⟨N, b, hb⟩ := exists_mul_pow c₀ 1
      rw [map_one, mul_one] at hb
      have h1 := congrArg ι hb
      rw [map_mul, map_pow] at h1
      have h2 := congrArg (σ z) h1
      rw [map_mul, map_pow, hfix, ← h1, show σ z (ι (vv k)) = ι (vv k) from hιv z] at h2
      exact mul_left_cancel₀ (pow_ne_zero N hv0) h2

end GlobalTheory.DeltaInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLe
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem tiltUntilt_add_estimate_of_norm_le (l : ℕ) [Fact l.Prime] (x y : Fl l) (hxy : ‖sh x‖ ≤ ‖sh y‖) :
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * ‖sh y‖ ∧ ‖sh (x + y)‖ ≤ ‖sh y‖ := by
  obtain ⟨h1, -, hmul, -, hle1, -, hadd, -⟩ := _root_.GlobalTheory.PSer.Laws.sh_laws l
  obtain ⟨u, rfl⟩ := (_root_.GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le l).2 x y hxy
  have hsum : y * u + y = y * (u + 1) := by ring
  rw [hsum, hmul, hmul]
  constructor
  · have key : sh y * sh (u + 1) - sh y * sh u - sh y
        = sh y * (sh (u + 1) - sh u - sh (1 : Fl l)) := by rw [h1]; ring
    rw [key, norm_mul, mul_comm ‖(l : ℂ_[l])‖]
    exact mul_le_mul_of_nonneg_left (hadd u 1) (norm_nonneg _)
  · rw [norm_mul]
    calc ‖sh y‖ * ‖sh (u + 1)‖ ≤ ‖sh y‖ * 1 :=
          mul_le_mul_of_nonneg_left (hle1 _) (norm_nonneg _)
      _ = ‖sh y‖ := mul_one _

theorem sh_add_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r →
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  intro l _ r x y hx hy
  have hl : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  rcases le_total ‖sh x‖ ‖sh y‖ with h | h
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l x y h
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hy hl), h2.trans hy⟩
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l y x h
    rw [add_comm x y]
    refine ⟨?_, h2.trans hx⟩
    have e : sh (y + x) - sh x - sh y = sh (y + x) - sh y - sh x := by ring
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left hx hl)

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeTwentyFiveMul
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

open NumberField IsDedekindDomain Module in
private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

open NumberField IsDedekindDomain Module in
private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith


open NumberField IsDedekindDomain Module in
theorem _root_.GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul :
    ∀ (l N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ N → 1 ≤ L →
      ((5 + Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1)) +
        N * (4 + 2 * Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1))) : ℕ) : ℝ) ≤ 25 * N * L := by
  intro l N L hl hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have he : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
  have hm : ((2 * (⌊2 * Real.exp L⌋₊ + 1) : ℕ) : ℝ) ≤ 2 ^ 3 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1)) : ℝ)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hNL : (1 : ℝ) ≤ N * L := one_le_mul_of_one_le_of_one_le hN' hL
  have hL1 : L ≤ N * L := by nlinarith
  have hN1 : (N : ℝ) ≤ N * L := by nlinarith
  have hA : (N : ℝ) * K ≤ N * (3 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetAverageEqHarishChandraRestricti
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

namespace GlobalTheory.ResTr
variable {g : ℕ} [Fact g.Prime]
open Formalism.MainNotions.ArithmeticCylinders

open Classical in
theorem coeff_mirEl {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) (h : Gn g r) :
    (mirEl θ a b).coeff h = if mirSet a b h then ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) else 0 := by
  unfold mirEl
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem sum_gl1 (M : Mt g 1) (d : (ZMod g)ˣ) (hM : M.det = d) (F : (ZMod g)ˣ → ℂ) :
    (∑ x : Gn g 1, if M = (x : Mt g 1) then F (Matrix.GeneralLinearGroup.det x) else 0) = F d := by
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hM]; exact d.isUnit)
  have key : ∀ x : Gn g 1, (M = (x : Mt g 1)) ↔ x = hU.unit := by
    intro x
    rw [Units.ext_iff, IsUnit.unit_spec]
    exact eq_comm
  simp_rw [key]
  rw [Finset.sum_ite_eq' Finset.univ hU.unit, if_pos (Finset.mem_univ _)]
  congr 1
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, hM]

theorem tl_last {n : ℕ} (M : Mt g (n + 1)) (i j : Fin n) : tl n M i j = M i.castSucc j.castSucc := by
  unfold tl entN
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem br_last {n : ℕ} (M : Mt g (n + 1)) (i j : Fin 1) : br n 1 M i j = M (Fin.last n) (Fin.last n) := by
  unfold br entN
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [Fin.fin_one_eq_zero]

theorem br_succ {n : ℕ} (M : Mt g (n + 1)) (i j : Fin n) : br 1 n M i j = M i.succ j.succ := by
  unfold br entN
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [add_comm]

theorem tl_zero {n : ℕ} (M : Mt g (n + 1)) (i j : Fin 1) : tl 1 M i j = M 0 0 := by
  unfold tl entN
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [Fin.fin_one_eq_zero]

def ColsId {n : ℕ} (M : Mt g (n + 1)) : Prop :=
  ∀ i j : Fin (n + 1), j ≠ Fin.last n → M i j = if i = j then 1 else 0

def RowsId {n : ℕ} (M : Mt g (n + 1)) : Prop :=
  ∀ i j : Fin (n + 1), i ≠ 0 → M i j = if i = j then 1 else 0

theorem mulVec_of_id {N : ℕ} (M : Mt g N) (x : Fin N → ZMod g) (i : Fin N)
    (h : ∀ j, x j ≠ 0 → M i j = if i = j then 1 else 0) : M.mulVec x i = x i := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hx : x i = 0
    · rw [hx, mul_zero]
    · rw [h i hx, if_pos rfl, one_mul]
  · intro j _ hji
    by_cases hx : x j = 0
    · rw [hx, mul_zero]
    · rw [h j hx, if_neg (Ne.symm hji), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem mirSet_last_iff {n : ℕ} (h : Gn g (n + 1)) :
    mirSet (Pi.single (Fin.last n) 1) false h ↔ ColsId (h : Mt g (n + 1)) := by
  unfold mirSet
  simp only [Bool.false_eq_true, if_false]
  constructor
  · intro H i j hj
    have := congrFun (H (Pi.single j 1) (by simp [single_dotProduct, Pi.single_apply, Ne.symm hj])) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply] using this
  · intro H x hx
    have hx' : x (Fin.last n) = 0 := by simpa [single_dotProduct] using hx
    funext i
    apply mulVec_of_id
    intro j hj
    exact H i j (fun e => hj (e ▸ hx'))

theorem mirSet_zero_iff {n : ℕ} (h : Gn g (n + 1)) :
    mirSet (Pi.single 0 1) true h ↔ RowsId (h : Mt g (n + 1)) := by
  unfold mirSet
  simp only [if_true]
  constructor
  · intro H i j hi
    obtain ⟨c, hc⟩ := H (Pi.single j 1)
    have := congrFun hc i
    rw [Matrix.mulVec_single_one] at this
    simp [Pi.single_apply, hi] at this
    rw [sub_eq_zero] at this
    simpa [Pi.single_apply] using this
  · intro H x
    refine ⟨((h : Mt g (n + 1)).mulVec x - x) 0, ?_⟩
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · have : (h : Mt g (n + 1)).mulVec x i = x i := mulVec_of_id _ _ _ (fun j _ => H i j hi)
      simp [this, hi]

theorem parTl_iff {n : ℕ} (M : Mt g (n + 1)) : (InPar n M ∧ tl n M = 1) ↔ ColsId M := by
  constructor
  · rintro ⟨hP, hT⟩ i j hj
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj
    induction i using Fin.lastCases with
    | last =>
      rw [if_neg (Fin.castSucc_ne_last j).symm]
      exact hP _ _ (by simp) (by simp)
    | cast i =>
      have := congrFun (congrFun hT i) j
      rw [tl_last] at this
      rw [this, Matrix.one_apply]
      simp [Fin.castSucc_inj]
  · intro H
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · have hne : j ≠ Fin.last n := fun e => by rw [e] at hj; simp at hj
      rw [H i j hne, if_neg]
      intro e; rw [e] at hi; omega
    · ext i j
      rw [tl_last, H _ _ (Fin.castSucc_ne_last j), Matrix.one_apply]
      simp [Fin.castSucc_inj]

theorem parBr_iff {n : ℕ} (M : Mt g (n + 1)) : (InPar 1 M ∧ br 1 n M = 1) ↔ RowsId M := by
  constructor
  · rintro ⟨hP, hB⟩ i j hi
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hi
    induction j using Fin.cases with
    | zero =>
      rw [if_neg (Fin.succ_ne_zero i)]
      exact hP _ _ (by simp) (by simp)
    | succ j =>
      have := congrFun (congrFun hB i) j
      rw [br_succ] at this
      rw [this, Matrix.one_apply]
      simp [Fin.succ_inj]
  · intro H
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · have hne : i ≠ 0 := fun e => by rw [e] at hi; simp at hi
      rw [H i j hne, if_neg]
      intro e; rw [e] at hi; omega
    · ext i j
      rw [br_succ, H _ _ (Fin.succ_ne_zero i), Matrix.one_apply]
      simp [Fin.succ_inj]

theorem det_colsId {n : ℕ} (M : Mt g (n + 1)) (H : ColsId M) : M.det = M (Fin.last n) (Fin.last n) := by
  have hT : M.BlockTriangular id := by
    intro i j hij
    have hj : j ≠ Fin.last n := fun e => by
      rw [e] at hij; exact absurd hij (not_lt.2 (Fin.le_last i))
    simp only [id] at hij
    rw [H i j hj, if_neg (ne_of_gt hij)]
  rw [Matrix.det_of_upperTriangular hT, Fin.prod_univ_castSucc]
  rw [Finset.prod_eq_one, one_mul]
  intro i _
  rw [H _ _ (Fin.castSucc_ne_last i), if_pos rfl]

theorem det_rowsId {n : ℕ} (M : Mt g (n + 1)) (H : RowsId M) : M.det = M 0 0 := by
  have hT : M.BlockTriangular id := by
    intro i j hij
    have hi : i ≠ 0 := fun e => by
      rw [e] at hij; exact absurd hij (not_lt.2 (Fin.zero_le j))
    simp only [id] at hij
    rw [H i j hi, if_neg (ne_of_gt hij)]
  rw [Matrix.det_of_upperTriangular hT, Fin.prod_univ_succ]
  rw [Finset.prod_eq_one, mul_one]
  intro i _
  rw [H _ _ (Fin.succ_ne_zero i), if_pos rfl]

theorem det_br_last {n : ℕ} (h : Gn g (n + 1)) (H : ColsId (h : Mt g (n + 1))) :
    (br n 1 (h : Mt g (n + 1))).det = ((Matrix.GeneralLinearGroup.det h : (ZMod g)ˣ) : ZMod g) := by
  rw [Matrix.det_unique, br_last, Matrix.GeneralLinearGroup.val_det_apply, det_colsId _ H]

theorem det_tl_zero {n : ℕ} (h : Gn g (n + 1)) (H : RowsId (h : Mt g (n + 1))) :
    (tl 1 (h : Mt g (n + 1))).det = ((Matrix.GeneralLinearGroup.det h : (ZMod g)ˣ) : ZMod g) := by
  rw [Matrix.det_unique, tl_zero, Matrix.GeneralLinearGroup.val_det_apply, det_rowsId _ H]


open Classical in
theorem trace_mir (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (θ : (ZMod g)ˣ →* ℂˣ) :
    tr (mirEl θ (Pi.single (Fin.last n) 1) false) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ∧
      tr (mirEl θ (Pi.single 0 1) true) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 := by
  have hg : (g : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)
  have hc : ∀ a t : ℂ, (g : ℂ) ^ n * (a * (((g : ℂ) ^ n)⁻¹ * t)) = a * t := fun a t => by
    rw [mul_left_comm, mul_inv_cancel_left₀ hg]
  constructor
  · unfold tr res
    simp_rw [coeff_mirEl, mul_one, Finset.mul_sum, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases H : ColsId (h : Mt g (n + 1))
    · obtain ⟨hP, hT⟩ := (parTl_iff _).2 H
      rw [if_pos ((mirSet_last_iff h).2 H)]
      simp only [Units.val_one, hP, hT, true_and, mul_ite, mul_zero]
      rw [sum_gl1 _ _ (det_br_last h H) (fun d => ((θ d : ℂˣ) : ℂ) * ψ h)]
    · rw [if_neg (fun e => H ((mirSet_last_iff h).1 e)), zero_mul]
      refine (Finset.sum_eq_zero (fun x _ => ?_)).symm
      rw [if_neg (fun e => H ((parTl_iff _).1 ⟨e.1, by simpa using e.2.1⟩)), mul_zero]
  · unfold tr res
    simp_rw [coeff_mirEl, one_mul, Finset.mul_sum, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases H : RowsId (h : Mt g (n + 1))
    · obtain ⟨hP, hB⟩ := (parBr_iff _).2 H
      rw [if_pos ((mirSet_zero_iff h).2 H)]
      simp only [Units.val_one, hP, hB, true_and, and_true, mul_ite, mul_zero]
      rw [sum_gl1 _ _ (det_tl_zero h H) (fun d => ((θ d : ℂˣ) : ℂ) * ψ h)]
    · rw [if_neg (fun e => H ((mirSet_zero_iff h).1 e)), zero_mul]
      refine (Finset.sum_eq_zero (fun x _ => ?_)).symm
      rw [if_neg (fun e => H ((parBr_iff _).1 ⟨e.1, by simpa using e.2.2⟩)), mul_zero]
end GlobalTheory.ResTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationGammaStableAndSubOneMemPiSmulStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturation_gamma_stable_of_good : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  first | exact @GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul | exact GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul | (intros; apply GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationQPowerMemFrobeniusSpanStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachSaturation_Q_power_mem_frobenius_span : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) → IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype → ∀ y ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) := by
  first | exact @GlobalTheory.NL.SatPhiSpan.satM_Qpow_mem_φspan | exact GlobalTheory.NL.SatPhiSpan.satM_Qpow_mem_φspan | (intros; apply GlobalTheory.NL.SatPhiSpan.satM_Qpow_mem_φspan <;> assumption)
end

