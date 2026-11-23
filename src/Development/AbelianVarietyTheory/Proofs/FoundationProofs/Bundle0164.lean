module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPrimCharMulRootPowModPow
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem zpow_eq_zpow_of_intCast_eq {K : Type} [Field K] {ξ : K} {N : ℕ} (h0 : ξ ≠ 0)
    (h : ξ ^ N = 1) {k j : ℤ} (hkj : (k : ZMod N) = (j : ZMod N)) : ξ ^ k = ξ ^ j := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hkj
  obtain ⟨q, hq⟩ := hkj
  have hj : j = k + (N : ℤ) * q := by linarith
  rw [hj, zpow_add₀ h0, zpow_mul, zpow_natCast, h, one_zpow, mul_one]

theorem sum_zmod_val_eq_sum_range {K : Type} [Field K] (N : ℕ) [NeZero N] (G : ℕ → K) :
    ∑ r : ZMod N, G r.val = ∑ k ∈ Finset.range N, G k := by
  refine Finset.sum_nbij' (fun f => f.val) (fun v => (v : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro f _; simpa using ZMod.val_lt f
  · intro v _; simp
  · intro f _; simp
  · intro v hv; exact ZMod.val_cast_of_lt (by simpa using hv)
  · intro f _; rfl

theorem sum_range_mul_split {K : Type} [Field K] (G : ℕ → K) (b c : ℕ) :
    ∑ k ∈ Finset.range (b * c), G k = ∑ t ∈ Finset.range c, ∑ a ∈ Finset.range b, G (a + b * t) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [add_comm]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

theorem sum_primChar_mul_rootPow_mod_pow : ∀ (K : Type) [Field K] [CharZero K] (l m n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ m)] (ζ : K) (ψ : DirichletCharacter K (l ^ m)), l.Prime → 1 ≤ m → m ≤ n → IsPrimitiveRoot ζ (l ^ n) → ψ.IsPrimitive → ∀ X : ℤ, ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X) = if (l : ℤ) ^ (n - m) ∣ X then (l : K) ^ (n - m) * (∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val)) * ψ⁻¹ ((X / (l : ℤ) ^ (n - m) : ℤ) : ZMod (l ^ m)) else 0 := by
  intro K _ _ l m n _ _ ζ ψ hl hm hmn hζ hψ X
  have hl0 : 0 < l := hl.pos
  have hN : l ^ n = l ^ (n - m) * l ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  have hN' : l ^ n = l ^ m * l ^ (n - m) := by rw [hN, mul_comm]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
  set F : ℕ → K := fun k => ψ (k : ZMod (l ^ m)) * ζ ^ ((k : ℤ) * X) with hF
  have h1 : ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X)
      = ∑ k ∈ Finset.range (l ^ n), F k := sum_zmod_val_eq_sum_range (l ^ n) F
  set y : K := ζ ^ (((l ^ m : ℕ) : ℤ) * X) with hy
  have h3 : ∀ a t : ℕ, F (a + l ^ m * t) = F a * y ^ t := by
    intro a t
    simp only [hF, hy]
    have hc : ((a + l ^ m * t : ℕ) : ZMod (l ^ m)) = (a : ZMod (l ^ m)) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [hc, mul_assoc]
    congr 1
    have he : ((a + l ^ m * t : ℕ) : ℤ) * X = (a : ℤ) * X + (((l ^ m : ℕ) : ℤ) * X) * (t : ℤ) := by
      push_cast; ring
    rw [he, zpow_add₀ hζ0, zpow_mul ζ (((l ^ m : ℕ) : ℤ) * X) (t : ℤ), zpow_natCast]
  have h2 : ∑ k ∈ Finset.range (l ^ n), F k
      = (∑ a ∈ Finset.range (l ^ m), F a) * ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t := by
    rw [hN', sum_range_mul_split, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h3]
  have hω : IsPrimitiveRoot (ζ ^ (l ^ m)) (l ^ (n - m)) := hζ.pow (by positivity) hN'
  have hyω : y = (ζ ^ (l ^ m)) ^ X := by
    rw [hy, zpow_mul, zpow_natCast]
  have h4 : ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t
      = if (l : ℤ) ^ (n - m) ∣ X then ((l : K) ^ (n - m)) else 0 := by
    split_ifs with hd
    · have : y = 1 := by
        rw [hyω]; exact (hω.zpow_eq_one_iff_dvd X).2 (by exact_mod_cast hd)
      simp [this]
    · have hy1 : y ≠ 1 := by
        rw [hyω]; intro h
        exact hd (by exact_mod_cast (hω.zpow_eq_one_iff_dvd X).1 h)
      rw [geom_sum_eq hy1]
      have : y ^ (l ^ (n - m)) = 1 := by
        rw [hyω, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.pow_eq_one,
          one_zpow]
      rw [this, sub_self, zero_div]
  have h5 : ∑ a ∈ Finset.range (l ^ m), F a = ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * X) := by
    rw [← sum_zmod_val_eq_sum_range (l ^ m) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hF, ZMod.natCast_zmod_val]
  rw [h1, h2, h4, h5]
  split_ifs with hd
  · obtain ⟨Y, rfl⟩ := hd
    have hL0 : (l : ℤ) ^ (n - m) ≠ 0 := by positivity
    rw [Int.mul_ediv_cancel_left _ hL0]
    have hξ : IsPrimitiveRoot (ζ ^ (l ^ (n - m))) (l ^ m) := hζ.pow (by positivity) hN
    have hξ0 : ζ ^ (l ^ (n - m)) ≠ 0 := pow_ne_zero _ hζ0
    let e : AddChar (ZMod (l ^ m)) K := AddChar.zmodChar (l ^ m) hξ.pow_eq_one
    have key := gaussSum_mulShift_of_isPrimitive e hψ (Y : ZMod (l ^ m))
    have hG : gaussSum ψ e = ∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.zmodChar_apply, pow_mul]
    have hS : ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y))
        = gaussSum ψ (e.mulShift Y) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.mulShift_apply, AddChar.zmodChar_apply]
      congr 1
      have he : (a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y) = ((l ^ (n - m) : ℕ) : ℤ) * ((a.val : ℤ) * Y) := by
        push_cast; ring
      rw [he, zpow_mul, zpow_natCast, ← zpow_natCast (ζ ^ l ^ (n - m)) ((Y : ZMod (l ^ m)) * a).val]
      refine zpow_eq_zpow_of_intCast_eq hξ0 hξ.pow_eq_one ?_
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id', mul_comm]
    rw [hS, key, ← hG]
    ring
  · simp
end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableRegularizedEisensteinLatticeTerm
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LatSumZ

theorem difdif (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    dif L v (dif L v F) x = ((L : ℂ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (F x - F (x + (r : ℤ) • v) - F (x + (r' : ℤ) • v) + F (x + (r' : ℤ) • v + (r : ℤ) • v)) := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set S := ∑ r ∈ Finset.range L, F (x + (r : ℤ) • v)
  set T := ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L, F (x + (r' : ℤ) • v + (r : ℤ) • v)
  have e : ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (F x - F (x + (r : ℤ) • v) - F (x + (r' : ℤ) • v) + F (x + (r' : ℤ) • v + (r : ℤ) • v))
      = (L : ℂ) * L * F x - L * S - L * S + T := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, S, T]
    rw [← Finset.mul_sum]; ring
  have e2 : ∑ r' ∈ Finset.range L, (F (x + (r' : ℤ) • v) - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, F (x + (r' : ℤ) • v + (r : ℤ) • v))
      = S - (L : ℂ)⁻¹ * T := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e]
  simp only [dif]
  rw [e2]
  field_simp
  ring

theorem trm_zero (j : ℕ) (y : ℂ) : trm j 0 y = (y ^ j)⁻¹ := by
  simp [trm]

theorem lin_shift (τ : ℍ) (x v : ℤ × ℤ) (r : ℕ) :
    (((x + (r : ℤ) • v).1 : ℤ) : ℂ) * (τ : ℂ) + (((x + (r : ℤ) • v).2 : ℤ) : ℂ)
      = ((x.1 : ℂ) * τ + x.2) + (r : ℂ) * ((v.1 : ℂ) * τ + v.2) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast; ring

theorem lin_shift2 (τ : ℍ) (x v : ℤ × ℤ) (r' r : ℕ) :
    (((x + (r' : ℤ) • v + (r : ℤ) • v).1 : ℤ) : ℂ) * (τ : ℂ) + (((x + (r' : ℤ) • v + (r : ℤ) • v).2 : ℤ) : ℂ)
      = ((x.1 : ℂ) * τ + x.2) + (r' : ℂ) * ((v.1 : ℂ) * τ + v.2) + (r : ℂ) * ((v.1 : ℂ) * τ + v.2) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast; ring

theorem difdif_bound (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ) (hj : 1 ≤ j) (hL : 0 < L) (C : ℝ)
    (hC : ∀ z a b : ℂ, z ≠ 0 → 4 * ‖a‖ ≤ ‖z‖ → 4 * ‖b‖ ≤ ‖z‖ →
      ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹‖ ≤ C * ‖a‖ * ‖b‖ / ‖z‖ ^ (j + 2))
    (x : ℤ × ℤ)
    (h1 : 1 ≤ ‖(x.1 : ℂ) * τ + x.2‖) (h4 : 4 * (L * ‖(v.1 : ℂ) * τ + v.2‖) ≤ ‖(x.1 : ℂ) * τ + x.2‖) :
    ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖
      ≤ max C 0 * (L * ‖(v.1 : ℂ) * τ + v.2‖) ^ 2 / ‖(x.1 : ℂ) * τ + x.2‖ ^ 3 := by
  set z : ℂ := (x.1 : ℂ) * τ + x.2 with hz
  set w : ℂ := (v.1 : ℂ) * τ + v.2 with hw
  set B : ℝ := max C 0 * (L * ‖w‖) ^ 2 / ‖z‖ ^ 3 with hB
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hterm : ∀ r' ∈ Finset.range L, ∀ r ∈ Finset.range L,
      ‖trm j 0 z - trm j 0 (z + (r : ℂ) * w) - trm j 0 (z + (r' : ℂ) * w)
        + trm j 0 (z + (r' : ℂ) * w + (r : ℂ) * w)‖ ≤ B := by
    intro r' hr' r hr
    have hr'L : (r' : ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hr').le
    have hrL : (r : ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hr).le
    have na : ‖(r' : ℂ) * w‖ ≤ L * ‖w‖ := by
      rw [norm_mul, Complex.norm_natCast]; exact mul_le_mul_of_nonneg_right hr'L (norm_nonneg _)
    have nb : ‖(r : ℂ) * w‖ ≤ L * ‖w‖ := by
      rw [norm_mul, Complex.norm_natCast]; exact mul_le_mul_of_nonneg_right hrL (norm_nonneg _)
    have key := hC z ((r' : ℂ) * w) ((r : ℂ) * w) hz0 (by linarith) (by linarith)
    simp only [trm_zero]
    have eq : (z ^ j)⁻¹ - ((z + (r : ℂ) * w) ^ j)⁻¹ - ((z + (r' : ℂ) * w) ^ j)⁻¹
        + ((z + (r' : ℂ) * w + (r : ℂ) * w) ^ j)⁻¹
        = (z ^ j)⁻¹ - ((z + (r' : ℂ) * w) ^ j)⁻¹ - ((z + (r : ℂ) * w) ^ j)⁻¹
        + ((z + (r' : ℂ) * w + (r : ℂ) * w) ^ j)⁻¹ := by ring
    rw [eq]
    refine key.trans ?_
    have hpow : ‖z‖ ^ 3 ≤ ‖z‖ ^ (j + 2) := pow_le_pow_right₀ h1 (by omega)
    have hp3 : 0 < ‖z‖ ^ 3 := by positivity
    have hM : 0 ≤ max C 0 := le_max_right _ _
    calc C * ‖(r' : ℂ) * w‖ * ‖(r : ℂ) * w‖ / ‖z‖ ^ (j + 2)
        ≤ max C 0 * ‖(r' : ℂ) * w‖ * ‖(r : ℂ) * w‖ / ‖z‖ ^ (j + 2) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (L * ‖w‖) * (L * ‖w‖) / ‖z‖ ^ (j + 2) := by gcongr
      _ ≤ max C 0 * (L * ‖w‖) * (L * ‖w‖) / ‖z‖ ^ 3 := by
          apply div_le_div_of_nonneg_left (by positivity) hp3 hpow
      _ = B := by rw [hB]; ring
  rw [difdif L hL v _ x]
  simp only [lin_shift τ, lin_shift2 τ]
  rw [← hz, ← hw]
  calc ‖((L : ℂ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L,
        (trm j 0 z - trm j 0 (z + (r : ℂ) * w) - trm j 0 (z + (r' : ℂ) * w)
          + trm j 0 (z + (r' : ℂ) * w + (r : ℂ) * w))‖
      ≤ ((L : ℝ) ^ 2)⁻¹ * ∑ r' ∈ Finset.range L, ∑ r ∈ Finset.range L, B := by
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r' hr' => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => hterm r' hr' r hr)
    _ = B := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

theorem latsum_summable : ∀ (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ), 1 ≤ j → 0 < L →
    Summable fun x => ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖ := by
  intro j L v τ hj hL
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.EisM.SecondDiff.second_diff_inv_pow j
  set w : ℂ := (v.1 : ℂ) * τ + v.2 with hw
  set R : ℝ := max (4 * (L * ‖w‖)) 1 with hR
  have hrτ : 0 < EisensteinSeries.r τ := EisensteinSeries.r_pos τ
  set M : ℝ := R / EisensteinSeries.r τ + 1 with hM
  set K : ℝ := max C 0 * (L * ‖w‖) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  rw [← (finTwoArrowEquiv ℤ).summable_iff]
  have hs : Summable fun y : Fin 2 → ℤ => K * (EisensteinSeries.r τ ^ 3)⁻¹ * ‖y‖ ^ (-(3 : ℝ)) :=
    (EisensteinSeries.summable_one_div_norm_rpow (by norm_num : (2 : ℝ) < 3)).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  have hev : ∀ᶠ y : Fin 2 → ℤ in cofinite, M ≤ ‖y‖ := by
    rw [← cocompact_eq_cofinite]
    exact tendsto_norm_cocompact_atTop.eventually_ge_atTop M
  filter_upwards [hev] with y hy
  have hR1 : 1 ≤ R := le_max_right _ _
  have hMpos : 0 < M := by positivity
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  have hlow := EisensteinSeries.r_mul_max_le τ hy0
  have hRle : R ≤ EisensteinSeries.r τ * ‖y‖ := by
    have : EisensteinSeries.r τ * M ≤ EisensteinSeries.r τ * ‖y‖ := mul_le_mul_of_nonneg_left hy hrτ.le
    have h2 : EisensteinSeries.r τ * M = R + EisensteinSeries.r τ := by
      rw [hM]; field_simp
    linarith
  have hxe : (((finTwoArrowEquiv ℤ y).1 : ℤ) : ℂ) * (τ : ℂ) + (((finTwoArrowEquiv ℤ y).2 : ℤ) : ℂ)
      = (y 0 : ℂ) * τ + y 1 := by simp
  have hzR : R ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ := by
    rw [hxe]; linarith
  have h1 : 1 ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ :=
    le_trans (le_max_right _ _) hzR
  have h4 : 4 * (L * ‖w‖) ≤ ‖((finTwoArrowEquiv ℤ y).1 : ℂ) * τ + ((finTwoArrowEquiv ℤ y).2 : ℂ)‖ :=
    le_trans (le_max_left _ _) hzR
  have hb := difdif_bound j L v τ hj hL C hC (finTwoArrowEquiv ℤ y) h1 h4
  rw [Function.comp_apply, norm_norm]
  refine hb.trans ?_
  rw [hxe] at h1 ⊢
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hprod : 0 < EisensteinSeries.r τ * ‖y‖ := mul_pos hrτ hypos
  have hrp : ‖y‖ ^ (-(3 : ℝ)) = (‖y‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg _), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrp, ← hw]
  calc max C 0 * (L * ‖w‖) ^ 2 / ‖(y 0 : ℂ) * τ + y 1‖ ^ 3
      ≤ K / (EisensteinSeries.r τ * ‖y‖) ^ 3 := by
        rw [hK]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hprod.le hlow 3
    _ = K * (EisensteinSeries.r τ ^ 3)⁻¹ * (‖y‖ ^ 3)⁻¹ := by
        rw [mul_pow]; field_simp

end GlobalTheory.LatSumZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionKaehlerSpanDlogIndep
section
open GlobalTheory.AlmostEt GlobalTheory.K5

namespace GlobalTheory.K5.TorsionDiff

theorem dlog_descend {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (a ai b bi P : S) (da db : M) (ha : a * ai = 1) (hb : b * bi = 1)
    (h : b • da = (P * a) • db) : (P * bi) • db = ai • da := by
  have h2 := congrArg (fun m => (ai * bi) • m) h
  simp only [smul_smul] at h2
  have e1 : ai * bi * b = ai := by linear_combination ai * hb
  have e2 : ai * bi * (P * a) = P * bi := by linear_combination (P * bi) * ha
  rw [e1, e2] at h2
  exact h2.symm

theorem exists_inv_zS {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : ∃ zi, zS T n * zi = 1 := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine ⟨zS T n ^ (p ^ n - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel hpos]
  exact Subtype.ext (T.prim n).pow_eq_one

theorem exists_inv_qS {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : ∃ qi, qS T n * qi = 1 := by
  have hne : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have h1 : qS T n ^ (p ^ n) = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
    Subtype.ext (GlobalTheory.AlmostEt.qq_pow T n)
  have h2 : IsUnit (qS T n ^ (p ^ n)) := by
    rw [h1]; exact (GlobalTheory.K5.Basic.isUnit_qO p).map _
  exact ((isUnit_pow_iff hne).1 h2).exists_right_inv

theorem span_core {S M : Type*} [CommRing S] [IsDomain S] [AddCommGroup M] [Module S M]
    (P : S) (hP : P ≠ 0) (n k : ℕ) (hn : 1 ≤ n) (η dz dq dzm dqm : M)
    (zi qi zm qm zim qim x y : S) (hz : zm * zim = 1) (hq : qm * qim = 1)
    (hη : P ^ n • η = 0) (hs : P ^ 2 • η = x • dzm + y • dqm)
    (hdz : (P ^ k * zim) • dzm = zi • dz) (hdq : (P ^ k * qim) • dqm = qi • dq)
    (hind : ∀ x y : S, (x * zim) • dzm + (y * qim) • dqm = 0 →
      (∃ t, P ^ 3 * x = P ^ (n + k - 1) * t) ∧ (∃ t, P ^ 3 * y = P ^ (n + k) * t)) :
    ∃ x y : S, P ^ 6 • η = (x * zi) • dz + (y * qi) • dq := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 : (P ^ (n + 1) * x * zm * zim) • dzm + (P ^ (n + 1) * y * qm * qim) • dqm = 0 := by
    rw [mul_assoc _ zm, hz, mul_assoc _ qm, hq, mul_one, mul_one, mul_smul, mul_smul, ← smul_add,
      ← hs, smul_comm, hη, smul_zero]
  obtain ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ := hind _ _ h0
  have e : n + 1 + k - 1 = n + k := by omega
  rw [e] at ht
  have hx : P ^ 4 * x = t * (P ^ k * zim) := by
    apply mul_left_cancel₀ (pow_ne_zero n hP)
    linear_combination zim * ht - P ^ (n + 4) * x * hz
  have hy : P ^ 4 * y = P * u * (P ^ k * qim) := by
    apply mul_left_cancel₀ (pow_ne_zero n hP)
    linear_combination qim * hu - P ^ (n + 4) * y * hq
  refine ⟨t, P * u, ?_⟩
  have e6 : P ^ 6 = P ^ 4 * P ^ 2 := by ring
  rw [e6, mul_smul, hs, smul_add, smul_smul, smul_smul, hx, hy, mul_smul t, mul_smul (P * u),
    hdz, hdq, smul_smul, smul_smul]

theorem torsion_span_and_indep : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ z qn zi qi : integralClosure (O0 p) Ω,
  (z : Ω) = T.ζ n → (qn : Ω) = T.qq n → z * zi = 1 → qn * qi = 1 →
  (∀ η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω), (p ^ n : ℕ) • η = 0 →
     ∃ x y : integralClosure (O0 p) Ω, (p ^ c : ℕ) • η =
       (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn) ∧
  (∀ x y : integralClosure (O0 p) Ω,
     (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn = 0 →
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * x = (p : integralClosure (O0 p) Ω) ^ (n - 1) * t) ∧
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * y = (p : integralClosure (O0 p) Ω) ^ n * t)) := by
  intro p _ hp2
  refine ⟨6, ?_⟩
  intro Ω _ _ hΩ T n hn z qn zi qi hz hq hzi hqi
  obtain rfl : z = zS T n := Subtype.ext hz
  obtain rfl : qn = qS T n := Subtype.ext hq
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hΩ
  have hP : (p : integralClosure (O0 p) Ω) ≠ 0 := by
    intro h
    have h2 : (p : Ω) = 0 := by simpa using congrArg Subtype.val h
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h2)
  refine ⟨?_, ?_⟩
  · intro η hη
    obtain ⟨m, hm, x, y, hs⟩ := GlobalTheory.AlmostEt.p_sq_smul_kaehler_mem_span p Ω hp2 hΩ T η n
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨zim, hzim⟩ := exists_inv_zS T (n + k)
    obtain ⟨qim, hqim⟩ := exists_inv_qS T (n + k)
    obtain ⟨hdz, hdq⟩ := GlobalTheory.AlmostEt.dlog_transition p Ω T n k
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), Nat.cast_pow] at hη ⊢
    exact span_core _ hP n k hn η _ _ _ _ zi qi _ _ zim qim x y hzim hqim hη hs
      (dlog_descend _ _ _ _ _ _ _ hzi hzim hdz) (dlog_descend _ _ _ _ _ _ _ hqi hqim hdq)
      (fun x y h => GlobalTheory.AlmostEt.dlog_indep_pow_three p Ω hp2 hΩ T (n + k) (by omega) x y zim qim hzim hqim h)
  · intro x y h
    obtain ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ := GlobalTheory.AlmostEt.dlog_indep_pow_three p Ω hp2 hΩ T n hn x y zi qi hzi hqi h
    exact ⟨⟨(p : integralClosure (O0 p) Ω) ^ 3 * t, by linear_combination (p : integralClosure (O0 p) Ω) ^ 3 * ht⟩,
      ⟨(p : integralClosure (O0 p) Ω) ^ 3 * u, by linear_combination (p : integralClosure (O0 p) Ω) ^ 3 * hu⟩⟩

end GlobalTheory.K5.TorsionDiff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitRootSplit
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem unitRoot_split : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (t D : ℂ),
    ‖ι.symm t‖ = 1 → ‖ι.symm D‖ < 1 →
    ∃ α β : ℂ, α + β = t ∧ α * β = D ∧ ‖ι.symm α‖ = 1 ∧ ‖ι.symm β‖ = ‖ι.symm D‖ := by
  intro l _ ι t D ht hD
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4 * D) (n := 2) (by norm_num)
  have hsum : (t + s) / 2 + (t - s) / 2 = t := by ring
  have hprod : (t + s) / 2 * ((t - s) / 2) = D := by
    have : (t + s) / 2 * ((t - s) / 2) = (t ^ 2 - s ^ 2) / 4 := by ring
    rw [this, hs]; ring
  have key : ∀ a b : ℂ, a + b = t → a * b = D → 1 ≤ ‖ι.symm a‖ →
      ‖ι.symm a‖ = 1 ∧ ‖ι.symm b‖ = ‖ι.symm D‖ := by
    intro a b hab hmul ha
    have hmulN : ‖ι.symm a‖ * ‖ι.symm b‖ = ‖ι.symm D‖ := by
      rw [← norm_mul, ← map_mul, hmul]
    have hb : ‖ι.symm b‖ < 1 := by
      by_contra h
      push_neg at h
      have : 1 ≤ ‖ι.symm a‖ * ‖ι.symm b‖ := by nlinarith
      linarith
    have hta : ι.symm a = ι.symm t + (-ι.symm b) := by
      rw [← hab, map_add (f := _)]; ring
    have hne : ‖ι.symm t‖ ≠ ‖-ι.symm b‖ := by rw [norm_neg, ht]; exact (ne_of_lt hb).symm
    have ha1 : ‖ι.symm a‖ = 1 := by
      rw [hta, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, ht]
      exact max_eq_left hb.le
    refine ⟨ha1, ?_⟩
    rw [← hmulN, ha1, one_mul]
  have hmax : 1 ≤ max ‖ι.symm ((t + s) / 2)‖ ‖ι.symm ((t - s) / 2)‖ := by
    have := IsUltrametricDist.norm_add_le_max (ι.symm ((t + s) / 2)) (ι.symm ((t - s) / 2))
    rw [← map_add (f := _), hsum, ht] at this
    exact this
  rcases le_max_iff.mp hmax with h | h
  · obtain ⟨h1, h2⟩ := key _ _ hsum hprod h
    exact ⟨_, _, hsum, hprod, h1, h2⟩
  · have hsum' : (t - s) / 2 + (t + s) / 2 = t := by rw [add_comm]; exact hsum
    have hprod' : (t - s) / 2 * ((t + s) / 2) = D := by rw [mul_comm]; exact hprod
    obtain ⟨h1, h2⟩ := key _ _ hsum' hprod' h
    exact ⟨_, _, hsum', hprod', h1, h2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZsEqMulDepEis
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem zs_eq_mul_dep_eis : ∀ (k l j : ℕ) (u v A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zs k l u v (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c A u)) (dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1)) := by
  intro k l j u v A A' c c' hjk
  funext n
  unfold Zs mul
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : l ∣ p.1 ∨ l ∣ p.2
  · have hz : dep l (eis (k - 1 - j) c A u) p.1 * dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1) p.2 = 0 := by
      rcases h with h | h <;> simp [dep, h]
    rw [hz]
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have p1 : p.1 ≠ 0 := fun e => h1 (e ▸ dvd_zero l)
    have p2 : p.2 ≠ 0 := fun e => h2 (e ▸ dvd_zero l)
    simp only [dep, eis, h1, h2, p1, p2, if_false, or_self]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    have hx0 : (x.1 : ℂ) ≠ 0 := by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have : x.1 ≠ 0 := fun e => p1 (by rw [← this, e, zero_mul])
      exact_mod_cast this
    have hk : k - 2 = (k - 1 - j - 1) + j := by omega
    have hj : j + 1 - 1 = j := by omega
    rw [hk, hj, pow_add, div_pow]
    field_simp

end GlobalTheory
end

