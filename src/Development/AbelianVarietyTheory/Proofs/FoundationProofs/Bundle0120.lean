module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelMassDegreeTypeLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassDegTypeLeCycleType
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem mass_degType_le_cycleType : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (A : Multiset ℕ → Prop),
    (mass g N fun f => A (degType g f)) ≤
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card : ℝ) / (N.factorial : ℝ) := by
  intro g _ N A
  set S : Finset (Multiset ℕ) :=
    ((sqSet g N).filter fun f => A (degType g f)).image (degType g) with hS
  have hmem : ∀ μ ∈ S, A μ ∧ (∀ d ∈ μ, 0 < d) ∧ μ.sum = N := by
    intro μ hμ
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hμ
    rw [Finset.mem_filter] at hf
    obtain ⟨-, -, hsum, hpos⟩ := (_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 N f hf.1
    exact ⟨hf.2, hpos, hsum⟩
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hμ : ∀ μ ∈ S, (mass g N fun f => degType g f = μ) ≤
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card : ℝ) /
        (N.factorial : ℝ) := by
    intro μ hμS
    obtain ⟨-, hpos, hsum⟩ := hmem μ hμS
    have hc := congrArg (Nat.cast : ℕ → ℝ) (_root_.GlobalTheory.BadShare.card_perm_partition_parts_mul N μ hpos hsum)
    push_cast at hc
    have hprod : (0 : ℝ) < ∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * ((μ.count d).factorial : ℝ)) := by
      refine Finset.prod_pos fun d hd => ?_
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hpos d (Multiset.mem_toFinset.1 hd)
      have hf0 : (0 : ℝ) < ((μ.count d).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      positivity
    have hP := hprod.ne'
    have hcard : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        σ.partition.parts = μ).card : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hc
      exact hfac.ne' hc.symm
    refine (_root_.GlobalTheory.BadShare.mass_degType_le g N μ).trans (le_of_eq ?_)
    rw [← hc]
    field_simp
  have hsplit : (mass g N fun f => A (degType g f)) =
      ∑ μ ∈ S, (mass g N fun f => degType g f = μ) := by
    unfold mass
    rw [← Finset.sum_fiberwise_of_maps_to (s := (sqSet g N).filter fun f => A (degType g f))
      (t := S) (g := degType g) (fun f hf => Finset.mem_image_of_mem _ hf)]
    refine Finset.sum_congr rfl fun μ hμS => Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hf, -⟩, h⟩
      exact ⟨hf, h⟩
    · rintro ⟨hf, h⟩
      exact ⟨⟨hf, h ▸ (hmem μ hμS).1⟩, h⟩
  have hperm : ∑ μ ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        σ.partition.parts = μ).card : ℝ) =
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      σ.partition.parts ∈ S) (t := S) (f := fun σ => σ.partition.parts)
      (fun σ hσ => (Finset.mem_filter.1 hσ).2)]
    push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 2
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl
      exact ⟨‹_›, rfl⟩
    · rintro ⟨-, h⟩
      exact h
  have hsub : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S).card ≤
      (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card := by
    refine Finset.card_le_card fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨hσ.1, (hmem _ hσ.2).1⟩
  rw [hsplit]
  calc ∑ μ ∈ S, (mass g N fun f => degType g f = μ)
      ≤ ∑ μ ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
          σ.partition.parts = μ).card : ℝ) / (N.factorial : ℝ) := Finset.sum_le_sum hμ
    _ = ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S).card : ℝ) /
          (N.factorial : ℝ) := by rw [← Finset.sum_div, hperm]
    _ ≤ _ := by
        gcongr

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinOfGaloisFixed
section
noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.TowerFix

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_eq_of_isIntegral_div (h : IsClo p Ω) (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n)
    (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (wb wc : On p n) (hc : ι wc ≠ 0) {x : Ω}
    (hx : IsIntegral (O0 p) x) (hxe : x = ι wb / ι wc) : ∃ w : On p n, ι w = x := by
  have hinj : Function.Injective ι := _root_.GlobalTheory.K5.EmbInj.emb_injective p Ω h T n hn ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  let K := FractionRing (On p n)
  let φ : K →+* Ω := IsFractionRing.lift (g := ι.toRingHom) hinj
  have hφ : ∀ w : On p n, φ (algebraMap (On p n) K w) = ι w := fun w =>
    IsFractionRing.lift_algebraMap _ _
  let φa : K →ₐ[O0 p] Ω :=
    { φ with
      commutes' := fun r => by
        have : algebraMap (O0 p) K r = algebraMap (On p n) K (algebraMap (O0 p) (On p n) r) :=
          IsScalarTower.algebraMap_apply _ _ _ r
        show φ (algebraMap (O0 p) K r) = _
        rw [this, hφ, AlgHom.commutes] }
  have hwc0 : wc ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
  let z : K := algebraMap (On p n) K wb / algebraMap (On p n) K wc
  have hz : φa z = x := by
    show φ z = x
    simp only [z, map_div₀, hφ, hxe]
  have hzi : IsIntegral (O0 p) z := by
    rw [← isIntegral_algHom_iff φa φa.toRingHom.injective, hz]; exact hx
  have hzi' : IsIntegral (On p n) z := hzi.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi'
  refine ⟨w, ?_⟩
  rw [← hφ, hw]
  exact hz

end GlobalTheory.K5.TowerFix

theorem GlobalTheory.K5.mem_towerAlg_of_fixed :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
      ∀ (T : Tower p Ω) (x : (integralClosure (O0 p) Ω)),
        (∀ g ∈ ⨅ n, Gn T n, g (x : Ω) = x) → x ∈ towerAlg T := by
  intro p _ Ω _ _ h T x hx
  haveI := h.clo
  haveI := h.alg
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  rw [_root_.GlobalTheory.towerAlg_mem_iff p Ω T x]
  set B := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)
  obtain ⟨b, hb, c, hc, hc0, hbc⟩ := GlobalTheory.mem_adjoin_div_of_fixed (O0 p) Ω h.inj
    (Set.range T.ζ ∪ Set.range T.qq) (x : Ω) (fun g hg => hx g (by
      rw [Subgroup.mem_iInf]
      intro n
      exact ⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩))
  obtain ⟨m, hm⟩ := GlobalTheory.K5.Level.exists_mem_bn T hb
  obtain ⟨k, hk⟩ := GlobalTheory.K5.Level.exists_mem_bn T hc
  set N := max m k + 1
  have hN : 1 ≤ N := Nat.le_add_left 1 _
  have hbN : b ∈ GlobalTheory.K5.Level.Bn T N :=
    GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_left m k) (Nat.le_succ _)) hm
  have hcN : c ∈ GlobalTheory.K5.Level.Bn T N :=
    GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_right m k) (Nat.le_succ _)) hk
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T N
  obtain ⟨wb, hwb⟩ := GlobalTheory.K5.Level.bn_le_range T N ι hι hbN
  obtain ⟨wc, hwc⟩ := GlobalTheory.K5.Level.bn_le_range T N ι hι hcN
  obtain ⟨w, hw⟩ := GlobalTheory.K5.TowerFix.exists_eq_of_isIntegral_div h T hN ι hι wb wc
    (by rw [show ι wc = c from hwc]; exact hc0) x.2
    (by rw [hbc, show ι wb = b from hwb, show ι wc = c from hwc])
  rw [← hw]
  exact GlobalTheory.K5.Level.bn_le_B T N (GlobalTheory.K5.Level.range_le_bn T N ι hι w)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowPrimeStep
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.LamEq

theorem pow_prime_step (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) (t : ℤ) :
    (p : ℤ) ^ (2 * n + 1) ∣ (1 + (p : ℤ) ^ n * t) ^ p - 1 - (p : ℤ) ^ (n + 1) * t := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  set P : ℤ := ((q + 2 : ℕ) : ℤ) with hP
  have hexp : (1 + P ^ n * t) ^ (q + 2) =
      ∑ i ∈ Finset.range (q + 1), (P ^ n * t) ^ (i + 2) * ((q + 2).choose (i + 2) : ℤ) + (q + 2 : ℕ) * (P ^ n * t) + 1 := by
    rw [add_comm (1 : ℤ), add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_one]
    push_cast; ring
  rw [hexp]
  have hPP : (q + 2 : ℕ) * (P ^ n * t) = P ^ (n + 1) * t := by rw [hP]; ring
  rw [hPP, show ∀ a b : ℤ, a + b + 1 - 1 - b = a from fun a b => by ring]
  apply Finset.dvd_sum
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hc : ((q + 2 : ℕ) : ℤ) ∣ ((q + 2).choose 2 : ℤ) := by
      exact_mod_cast hp.dvd_choose_self (by norm_num) (by omega)
    rw [← hP] at hc
    obtain ⟨c, hc⟩ := hc
    exact ⟨t ^ 2 * c, by rw [hc]; ring⟩
  · have h3 : 2 * n + 1 ≤ n * (i + 2) := by nlinarith
    refine Dvd.dvd.mul_right ?_ _
    rw [mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ h3) _

theorem pow_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (j n : ℕ), 1 ≤ n → ∀ t : ℤ,
      (p : ℤ) ^ (2 * n + j) ∣ (1 + (p : ℤ) ^ n * t) ^ (p ^ j) - 1 - (p : ℤ) ^ (n + j) * t := by
  intro j
  induction j with
  | zero => intro n _ t; simp
  | succ j ih =>
    intro n hn t
    obtain ⟨w, hw⟩ := pow_prime_step p hp hp2 n hn t
    have h1 : (1 + (p : ℤ) ^ n * t) ^ p = 1 + (p : ℤ) ^ (n + 1) * (t + (p : ℤ) ^ n * w) := by
      linear_combination hw + (0 : ℤ) * w
    obtain ⟨w', hw'⟩ := ih (n + 1) (by omega) (t + (p : ℤ) ^ n * w)
    rw [pow_succ', pow_mul, h1]
    refine ⟨(p : ℤ) * w' + w, ?_⟩
    linear_combination hw'
end GlobalTheory.LamEq

namespace GlobalTheory.LamEq

theorem aut_pow_apply {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (z : Ω) (c : ℕ) (hc : s z = z ^ c) :
    ∀ k : ℕ, (s ^ k) z = z ^ (c ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hc, map_pow, ih, ← pow_mul, pow_succ]

theorem lam_eq : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ s : Ω ≃ₐ[ℚ] Ω, s (zt ε p m) = zt ε p m →
  ∀ tt tt' : ZMod (p ^ n), IsLamG ε p n m s tt → (s ^ (p ^ (L - m))) (zt ε p (L + n)) = zt ε p n ^ tt'.val * zt ε p (L + n) → tt = tt' := by
  intro Ω _ _ _ ε p hpf hp2 L n m hm1 hmn hnL s _ tt tt' hlam hL
  have hp : p.Prime := hpf.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨e, rfl⟩ : ∃ e, L = n + e := ⟨L - n, by omega⟩
  set z := zt ε p (n + e + n) with hzdef
  have hz : IsPrimitiveRoot z (p ^ (n + e + n)) := IsNTr.isPrimitiveRoot_zt ε p _
  obtain ⟨c, -, hc⟩ := hz.eq_pow_of_pow_eq_one (ξ := s z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  have hs := aut_pow_apply s z c hc.symm
  have h2n : zt ε p (2 * n) = z ^ (p ^ e) := by
    rw [hzdef, ← IsNTr.zt_pow ε p (2 * n) e]; congr 2; omega
  have hn : zt ε p n = z ^ (p ^ (n + e)) := by
    rw [hzdef, ← IsNTr.zt_pow ε p n (n + e)]; congr 2; omega

  have E1 : z ^ (c ^ (p ^ (n - m)) * p ^ e) = z ^ (p ^ (n + e) * tt.val + p ^ e) := by
    have := hlam
    unfold IsLamG at this
    change (s ^ (p ^ (n - m))) (zt ε p (2 * n)) = zt ε p n ^ tt.val * zt ε p (2 * n) at this
    rw [h2n, hn, map_pow, hs, ← pow_mul, ← pow_mul, ← pow_add] at this
    exact this
  have E2 : z ^ (c ^ (p ^ (n + e - m))) = z ^ (p ^ (n + e) * tt'.val + 1) := by
    rw [← hs, hL, hn, ← pow_mul, pow_succ]
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, hz.pow_eq_one⟩
  have hmod : ∀ a b : ℕ, z ^ a = z ^ b ↔ a ≡ b [MOD p ^ (n + e + n)] := by
    intro a b; rw [hz.eq_orderOf]; exact hfin.pow_eq_pow_iff_modEq
  rw [hmod, Nat.modEq_iff_dvd] at E1 E2
  obtain ⟨w1, hw1⟩ := E1
  obtain ⟨w3, hw3⟩ := E2
  push_cast at hw1 hw3
  set P : ℤ := (p : ℤ) with hP
  have hP0 : P ≠ 0 := by rw [hP]; exact_mod_cast hp.ne_zero
  set a : ℤ := (c : ℤ) ^ (p ^ (n - m)) with ha
  set v : ℤ := ((tt.val : ℕ) : ℤ)
  set v' : ℤ := ((tt'.val : ℕ) : ℤ)
  have h1 : a = 1 + P ^ n * (v - P ^ n * w1) := by
    apply mul_left_cancel₀ (pow_ne_zero e hP0)
    linear_combination (-1 : ℤ) * hw1
  obtain ⟨w2, hw2⟩ := pow_prime_pow p hp hp2 e n (by omega) (v - P ^ n * w1)
  rw [← h1, ← hP] at hw2
  have hce : (c : ℤ) ^ (p ^ (n + e - m)) = a ^ (p ^ e) := by
    rw [ha, ← pow_mul, ← pow_add]; congr 2; omega
  rw [hce] at hw3
  have hd : v' - v = P ^ n * (w3 - w1 + w2) := by
    apply mul_left_cancel₀ (pow_ne_zero (n + e) hP0)
    linear_combination hw3 + hw2
  have hv : ((v : ℤ) : ZMod (p ^ n)) = ((v' : ℤ) : ZMod (p ^ n)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ⟨w3 - w1 + w2, by push_cast; rw [hd]⟩
  simpa [v, v', ZMod.natCast_zmod_val] using hv

end GlobalTheory.LamEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeNotIntertwineOutside
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem not_intertwine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ y ∈ KO k (Fin n), y ∉ grp ψ → ∃ j ∈ grp ψ, y * j * y⁻¹ ∈ grp ψ ∧ theta ψ j ≠ theta ψ (y * j * y⁻¹) := by
  intro k _ _ _ _ n ψ hord y hy hny
  classical

  have hbad : ∃ a b : Fin n, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b) := by
    by_contra h
    push_neg at h
    exact hny ⟨hy, fun i j hij => h i j hij⟩
  let S : Finset (Fin n) := Finset.univ.filter (fun a => ∃ b, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hS : S.Nonempty := by
    obtain ⟨a, b, hab, h⟩ := hbad
    exact ⟨a, by simp [S]; exact ⟨b, hab, h⟩⟩
  set a := S.min' hS with ha_def
  have haS : a ∈ S := S.min'_mem hS
  have hamin : ∀ i ∈ S, a ≤ i := fun i hi => S.min'_le i hi
  let T : Finset (Fin n) := Finset.univ.filter (fun b => a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hT : T.Nonempty := by
    have := haS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by simp [T]; exact hb⟩
  set b := T.max' hT with hb_def
  have hbT : b ∈ T := T.max'_mem hT
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hbT
  obtain ⟨hab, hbad_ab⟩ := hbT
  have hbmax : ∀ j, b < j → Triv (ψ a / ψ j) (y.val a j) := by
    intro j hj
    by_contra hc
    have : j ∈ T := by simp [T]; exact ⟨lt_trans hab hj, hc⟩
    exact absurd (T.le_max' j this) (not_le.mpr hj)
  obtain ⟨j, hj, u, s, hu, hs, hsu, hne, hθj, hKO, hval⟩ :=
    _root_.GlobalTheory.PsType.corner_rankOne k n ψ hord y hy a b hab hbad_ab hbmax
  have hprops := GlobalTheory.PsType.triv_ev_props k
  refine ⟨j, hj, ⟨hKO, ?_⟩, ?_⟩
  · intro i i' hii'
    rw [hval]
    by_cases hi' : i' = a
    · subst hi'
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_same, mul_one,
        if_neg (ne_of_lt hii'), zero_add]

      have hiS : i ∉ S := fun h => absurd (hamin i h) (not_le.mpr hii')
      have hib : Triv (ψ i / ψ b) (y.val i b) := by
        by_contra hc
        exact hiS (by simp [S]; exact ⟨b, lt_trans hii' hab, hc⟩)
      have h2 : Triv (ψ i / ψ a) (y.val i b) := hord i i a b le_rfl hii'.le hab.le _ hib
      refine hprops.1 _ _ _ ?_ h2
      rw [map_mul]
      first
        | exact mul_le_of_le_one_left' hs
        | exact (mul_le_mul' hs le_rfl).trans_eq (one_mul _)
        | exact mul_le_of_le_one_left (zero_le _) hs
    · simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hi', mul_zero,
        if_neg (ne_of_lt hii'), add_zero]
      exact hprops.2.2.1 _
  · have hθ : theta ψ (y * j * y⁻¹) = (ψ a u : ℂ) := by
      refine _root_.GlobalTheory.PsType.theta_rankOne k n ψ (y * j * y⁻¹) (fun i => s * y.val i b) (Pi.single a 1) a u hu hval ?_
      intro i
      by_cases hi : i = a
      · subst hi; simp [hsu]
      · simp [Pi.single_eq_of_ne hi, hi]
    rw [hθj, hθ]
    intro h
    exact hne (Units.ext h).symm

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubst
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNPole

theorem qAll_monomial (E : Subring ℂ) (M k : ℕ) :
    QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  refine ⟨fun n => if n = k then 1 else 0, fun τ => ?_, fun n => ?_⟩
  · have := hasSum_single (f := fun n : ℕ => (if n = k then (1 : ℂ) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / M)) k (fun n hn => by simp [hn])
    simpa using this
  · dsimp only; split_ifs
    · exact E.one_mem
    · exact E.zero_mem

theorem qAll_of_int (E : Subring ℂ) {f : ℍ → ℂ} (h : ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 f fun n => (c n : ℂ)) :
    QAll (· ∈ E) 1 f := by
  obtain ⟨c, -, hc⟩ := h
  exact ⟨_, hc, fun n => intCast_mem E (c n)⟩

theorem qAll_congr {p : ℂ → Prop} {N : ℕ} {f g : ℍ → ℂ} (hf : QAll p N f) (h : ∀ τ, f τ = g τ) :
    QAll p N g := by
  have : f = g := funext h
  exact this ▸ hf

theorem qAll_pole_affine : ∀ (E : Subring ℂ) (N w a d : ℕ) (b : ℤ) (φ : ℍ → ℂ),
    (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d →
    QAll (· ∈ E) N (fun τ => DD τ ^ w * φ τ) →
    QAll (· ∈ E) (N * (a * d)) fun τ => DD τ ^ (w * (a * d)) * up φ (((a : ℂ) * τ + b) / d) := by
  intro E N w a d b φ hE hN ha hd hφ
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hM : 0 < N * (a * (d' + 1)) := by positivity
  have RC := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed E (N * (a * (d' + 1))) hM
  obtain ⟨hDq, hqD⟩ := _root_.GlobalTheory.FN.dd_div_q_and_q_div_dd
  have h1 := QAll.of_dvd hM ⟨a, by ring⟩ E.zero_mem
    (_root_.GlobalTheory.FNQ.qAll_affine E N a (d' + 1) b _ hE hN ha (by omega) hφ)
  have h2 := QAll.of_dvd hM ⟨N * a, by ring⟩ E.zero_mem
    (_root_.GlobalTheory.FNQ.qAll_affine E 1 a (d' + 1) b _ hE one_pos ha (by omega) (qAll_of_int E hqD))
  have h3 := QAll.of_dvd hM (one_dvd _) E.zero_mem (qAll_of_int E hDq)
  have h2w := RC.2.2.2.2.1 _ w h2
  have h3w := RC.2.2.2.2.1 _ (w * (a * (d' + 1))) h3
  have h4 := RC.1 _ (hE (-((w : ℚ) * b) / (d' + 1)))
  have h5 := qAll_monomial E (N * (a * (d' + 1))) (N * w * a * a * (d' * (d' + 2)))
  have hP := RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ h1 h2w) h3w) h4) h5
  refine qAll_congr hP fun τ => ?_
  simp only [up]
  set U := UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)) with hUdef
  have him : 0 < (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)).im := by
    have : (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)).im = a * τ.im / (d' + 1) := by
      rw [Complex.div_natCast_im]; simp
    rw [this]; have := τ.im_pos; positivity
  have hU : (U : ℂ) = ((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ) := by
    rw [hUdef, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have key : Complex.exp (2 * Real.pi * Complex.I * (U : ℂ)) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * (((-((w : ℚ) * b) / (d' + 1) : ℚ)) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((N * w * a * a * (d' * (d' + 2)) : ℕ) : ℂ) * τ /
        ((N * (a * (d' + 1)) : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (w * (a * (d' + 1))) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hU]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hd' : (d' : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d')
    push_cast
    field_simp
    ring
  have hDU := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero U
  have hDτ := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have e1 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (U : ℂ))
  have e2 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))
  have e3 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (((-((w : ℚ) * b) / (d' + 1) : ℚ)) : ℂ))
  have e4 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * ((N * w * a * a * (d' * (d' + 2)) : ℕ) : ℂ) * τ /
        ((N * (a * (d' + 1)) : ℕ) : ℂ))
  rw [div_pow, div_pow, ← key]
  field_simp

end GlobalTheory.FNPole
end

