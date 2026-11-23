module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0243
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0147
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0245
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0250

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerLogMultiplicative
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
namespace GlobalTheory.CompanionTheory.TruncLog

variable {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J)

theorem mul_dpow_eq_succ {x : A} (hx : x ∈ J) (a : ℕ) :
    x * δ.dpow a x = ((a : A) + 1) * δ.dpow (a + 1) x := by
  have h := δ.mul_dpow (m := 1) (n := a) hx
  rw [δ.dpow_one hx] at h
  rw [h, Nat.choose_one_right, add_comm 1 a]
  push_cast
  ring

theorem factorial_mul_dpow_eq_zero {N : ℕ} {x : A}
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) {a k : ℕ} (ha : N < a)
    (hk : a ≤ k + 1) : (k.factorial : A) * δ.dpow a x = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, hd⟩ := Nat.factorial_dvd_factorial (show c ≤ k by omega)
  rw [hd]
  push_cast
  rw [mul_comm (c.factorial : A), mul_assoc, hN c (by omega), mul_zero]

theorem one_add_mul_sum_succ {x : A} (hx : x ∈ J) (m n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + (m + 1)).factorial : A) * δ.dpow a x =
      ((m : A) + 1) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x
      + (-1) ^ n * ((n + (m + 1)).factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    have e : (((m + 1).factorial : ℕ) : A) = ((m : A) + 1) * (m.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, e, Nat.cast_zero]
    ring
  | succ n ih =>
    have e1 : ((n + 1 + (m + 1)).factorial : A)
        = ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + (m + 1) = (n + (m + 1)) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    have e2 : ((n + 1 + m).factorial : A) = ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + m = n + (m + 1) by omega]
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ _ (n + 1), e1, e2]
    push_cast at hxp ⊢
    linear_combination
      (-1 : A) ^ (n + 1) * ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) * hxp

theorem one_add_mul_sum_zero {x : A} (hx : x ∈ J) (n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1), (-1 : A) ^ a * (a.factorial : A) * δ.dpow a x =
      1 + (-1) ^ n * (n.factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero]
  | succ n ih =>
    have e1 : ((n + 1).factorial : A) = ((n : A) + 1) * (n.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, e1]
    push_cast at hxp ⊢
    linear_combination (-1 : A) ^ (n + 1) * ((n : A) + 1) * (n.factorial : A) * hxp

theorem one_add_pow_mul_sum {N : ℕ} {x : A} (hx : x ∈ J)
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) (m : ℕ) :
    (1 + x) ^ (m + 1) * ∑ a ∈ Finset.range (N + 1),
      (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x = (m.factorial : A) := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one, add_zero, Nat.factorial_zero, Nat.cast_one]
    rw [one_add_mul_sum_zero δ hx N]
    have := hN N le_rfl
    linear_combination ((-1 : A) ^ N * ((N : A) + 1)) * this
  | succ m ih =>
    have z := factorial_mul_dpow_eq_zero δ hN (a := N + 1) (k := N + (m + 1)) (by omega) (by omega)
    rw [pow_succ, mul_assoc, one_add_mul_sum_succ δ hx m N, Nat.factorial_succ]
    push_cast
    linear_combination ((m : A) + 1) * ih
      + (1 + x) ^ (m + 1) * (-1 : A) ^ N * ((N : A) + 1) * z

theorem sum_antidiagonal_eq_sum_box (g : ℕ → ℕ → A) {N M : ℕ} (hM : 2 * N ≤ M)
    (hg : ∀ a b, N < a ∨ N < b → g a b = 0) :
    ∑ k ∈ Finset.range (M + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, g p.1 p.2 =
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b := by
  rw [← Finset.sum_product' (f := g),
    ← Finset.sum_fiberwise_of_maps_to
      (s := Finset.range (N + 1) ×ˢ Finset.range (N + 1)) (t := Finset.range (M + 1))
      (g := fun p => p.1 + p.2)
      (by intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2
  · intro p hp hp'
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and] at hp'
    apply hg
    by_contra hc
    exact hp' (by omega) hp

theorem dlog_mul {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ)
    (h : ∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) (v w : A)
    (hv : v - 1 ∈ J) (hw : w - 1 ∈ J) :
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  obtain ⟨x, rfl⟩ : ∃ x, v = 1 + x := ⟨v - 1, by ring⟩
  obtain ⟨y, rfl⟩ : ∃ y, w = 1 + y := ⟨w - 1, by ring⟩
  have hx : x ∈ J := by simpa using hv
  have hy : y ∈ J := by simpa using hw
  have hvy : (1 + x) * y ∈ J := J.mul_mem_left _ hy
  have hz : x + (1 + x) * y ∈ J := J.add_mem hx hvy
  have dl : ∀ t : A, B.dlog δ N (1 + t) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) t := by
    intro t; simp [B.dlog]
  have dz : B.dlog δ N ((1 + x) * (1 + y)) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    have : (1 + x) * (1 + y) = 1 + (x + (1 + x) * y) := by ring
    rw [this, dl]
  let g : ℕ → ℕ → A := fun a b => (-1 : A) ^ (a + b + 1) * ((a + b - 1).factorial : A) *
    δ.dpow a x * ((1 + x) ^ b * δ.dpow b y)
  have hg : ∀ a b, N < a ∨ N < b → g a b = 0 := by
    intro a b hab
    rcases hab with hab | hab
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk x hx) (a := a) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      rw [mul_assoc ((-1 : A) ^ (a + b + 1)), this]
      ring
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk y hy) (a := b) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      linear_combination
        ((-1 : A) ^ (a + b + 1) * δ.dpow a x * (1 + x) ^ b) * this
  have s1 : B.dlog δ N ((1 + x) * (1 + y)) = ∑ k ∈ Finset.range (2 * N),
      (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    rw [dz]
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [mul_assoc, h k hk _ hz, mul_zero]
  have s2 : ∀ k, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), g p.1 p.2 := by
    intro k
    rw [δ.dpow_add hx hvy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = k + 1 := by simpa using hp
    simp only [g]
    rw [hp', δ.dpow_mul hy, show k + 1 - 1 = k by omega]
    ring
  have s3 := sum_antidiagonal_eq_sum_box g (N := N) (M := 2 * N) le_rfl hg
  rw [Finset.sum_range_succ'] at s3
  have s4 : ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b =
      g 0 0 + (B.dlog δ N (1 + x) + B.dlog δ N (1 + y)) := by
    rw [Finset.sum_comm, Finset.sum_range_succ', Finset.sum_range_succ' (fun a => g a 0), dl, dl]
    have t1 : ∀ k, g (k + 1) 0 = (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) x := by
      intro k
      simp only [g, add_zero, pow_zero, δ.dpow_zero hy, show k + 1 - 1 = k by omega]
      ring
    have t2 : ∀ b, ∑ a ∈ Finset.range (N + 1), g a (b + 1) =
        (-1 : A) ^ b * (b.factorial : A) * δ.dpow (b + 1) y := by
      intro b
      rw [← one_add_pow_mul_sum δ hx (fun k hk => h k hk x hx) b]
      simp only [g]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show a + (b + 1) - 1 = a + b by omega]
      ring
    simp only [t1, t2]
    ring
  have s5 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0, g p.1 p.2 = g 0 0 := by simp
  rw [s5, s4] at s3
  simp only [← s2] at s3
  rw [s1]
  linear_combination s3

end GlobalTheory.CompanionTheory.TruncLog
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousEpsilonPower
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv.EtaFn

section Var

variable {S : Type} [CommRing S] {l : ℕ} [Fact l.Prime] {ϖ x : S}

theorem pow_sub_one_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) (m : ℕ) :
    x ^ l ^ m - 1 ∈ Ideal.span {ϖ ^ l ^ m} := by
  rcases subsingleton_or_nontrivial S with h | h
  · rw [Subsingleton.elim (x ^ l ^ m - 1) 0]
    exact zero_mem _
  · haveI : CharP S l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl
    haveI : ExpChar S l := ExpChar.prime Fact.out
    have e : x ^ l ^ m - 1 = (x - 1) ^ l ^ m := by
      rw [sub_pow_char_pow, one_pow]
    rw [e, ← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hx _

theorem pow_sub_pow_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) {a b m : ℕ}
    (h : a ≡ b [MOD l ^ m]) : x ^ a - x ^ b ∈ Ideal.span {ϖ ^ l ^ m} := by
  have key : ∀ a b : ℕ, a ≤ b → a ≡ b [MOD l ^ m] → x ^ b - x ^ a ∈ Ideal.span {ϖ ^ l ^ m} := by
    intro a b hab h
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hab).1 h
    have hb : b = a + l ^ m * c := by omega
    obtain ⟨d, hd⟩ : x ^ l ^ m - 1 ∣ (x ^ l ^ m) ^ c - 1 := by
      simpa using sub_dvd_pow_sub_pow (x ^ l ^ m) 1 c
    have e : x ^ b - x ^ a = (x ^ l ^ m - 1) * (d * x ^ a) := by
      rw [hb, pow_add, pow_mul]
      linear_combination x ^ a * hd
    rw [e]
    exact Ideal.mul_mem_right _ _ (pow_sub_one_mem hl hx m)
  rcases le_total a b with hab | hab
  · rw [← neg_sub]
    exact neg_mem (key a b hab h)
  · exact key b a hab h.symm

theorem span_pow_le {k n : ℕ} (h : k ≤ n) : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ k} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ h)

theorem le_pow (k : ℕ) : k ≤ l ^ k := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem exists_lim [IsAdicComplete (Ideal.span {ϖ}) S] (hl : (l : S) = 0)
    (hx : x - 1 ∈ Ideal.span {ϖ}) (a : ℕ → ℕ) (ha : ∀ m m', m ≤ m' → a m' ≡ a m [MOD l ^ m]) :
    ∃ L, ∀ m, L - x ^ a m ∈ Ideal.span {ϖ ^ l ^ m} := by
  obtain ⟨L, hL⟩ := exists_tends (ϖ := ϖ) (fun m => x ^ a m) fun k =>
    ⟨k, fun m hm => span_pow_le (le_pow (l := l) k) (pow_sub_pow_mem hl hx (ha k m hm))⟩
  refine ⟨L, fun m => ?_⟩
  obtain ⟨M, hM⟩ := hL (l ^ m)
  have h1 := hM (max M m) (le_max_left _ _)
  have h2 := pow_sub_pow_mem (ϖ := ϖ) hl hx (ha m (max M m) (le_max_right _ _))
  have := sub_mem h2 h1
  convert this using 1
  ring

theorem eq_of_forall_mem [IsHausdorff (Ideal.span {ϖ}) S] {a b : S}
    (h : ∀ m, a - b ∈ Ideal.span {ϖ ^ l ^ m}) : a = b :=
  Tends.unique (ϖ := ϖ) (x := fun _ => a) (tends_const a)
    fun k => ⟨0, fun _ _ => span_pow_le (le_pow (l := l) k) (h k)⟩

end Var

variable {l : ℕ} [Fact l.Prime]

theorem val_modEq {m m' : ℕ} (h : m ≤ m') (z : ℤ_[l]) :
    (PadicInt.toZModPow m' z).val ≡ (PadicInt.toZModPow m z).val [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val,
    PadicInt.cast_toZModPow _ _ h]

theorem val_add_one (m : ℕ) (z : ℤ_[l]) :
    (PadicInt.toZModPow m (z + 1)).val ≡ (PadicInt.toZModPow m z).val + 1 [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    map_add, map_one, Nat.cast_one]

theorem exists_fn (A : PAlg l) (x : A.A) (hx : x - 1 ∈ Ideal.span {A.pi}) :
    ∃ η : (A.cont ℤ_[l]).A,
      (∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) η - x ^ (PadicInt.toZModPow m z).val ∈
        Ideal.span {A.pi ^ (l ^ m)}) ∧
      ∀ z : ℤ_[l], Hom.f (A.evCont (z + 1)) η = x * Hom.f (A.evCont z) η := by
  haveI hc : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  have hl : (l : A.A) = 0 := A.natCast_l
  choose L hL using fun z : ℤ_[l] => exists_lim (ϖ := A.pi) hl hx
    (fun m => (PadicInt.toZModPow m z).val) (fun m m' h => val_modEq h z)
  refine ⟨⟨L, fun k => ?_⟩, fun m z => hL z m, fun z => ?_⟩
  · have e : (Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L =
        (fun c : ZMod (l ^ k) => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (x ^ c.val)) ∘
          PadicInt.toZModPow k := funext fun z =>
      Ideal.Quotient.eq.2 (span_pow_le (le_pow (l := l) k) (hL z k))
    have h : IsLocallyConstant ((Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L) := by
      rw [e]
      exact (GlobalTheory.CompanionTheory.PadicShift.isLocallyConstant_toZModPow l k).comp _
    exact h
  · refine eq_of_forall_mem (ϖ := A.pi) (l := l) fun m => ?_
    have h1 := hL (z + 1) m
    have h2 := Ideal.mul_mem_left _ x (hL z m)
    have h3 := pow_sub_pow_mem (ϖ := A.pi) hl hx (val_add_one m z)
    have := add_mem h1 (sub_mem h3 h2)
    change L (z + 1) - x * L z ∈ _
    convert this using 1
    ring

theorem exists_eta (ε : Eps l) : ∃ η : ((base l).cont ℤ_[l]).A,
    (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
    Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  have hx : (base l).s (ε.e 0) - 1 ∈ Ideal.span {(base l).pi} :=
    ((RL.sharp_cong (base l)).2.1 _ 1).1 (by
      rw [ε.sharp_e (base l), map_one, sub_self]
      exact zero_mem _)
  obtain ⟨η, h1, h2⟩ := exists_fn (base l) _ hx
  refine ⟨η, h1, cont_ext fun z => ?_⟩
  have e : Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) = (base l).s (ε.e 0) :=
    RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  rw [map_mul, e]
  exact h2 z

end GlobalTheory.CompanionTheory.ContUniv.EtaFn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGradedFormOnAffineChart
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech.Omega
open GlobalTheory.CompanionTheory.GrForm GlobalTheory.CompanionTheory.GrVB

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem evLift_mul_sub {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hP : ∀ T, P T → InU W T) (z x : Γ(X, W))
    (T : P.FullSubcategory) :
    (show T.obj.B from evLift hP z T) * lft W T.obj x - lft W T.obj (z * x) ∈ T.obj.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, mk_evLift, lft_spec _ (hP _ T.property), lft_spec _ (hP _ T.property), map_mul]

theorem rp_fAct {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hF : IsFil (sP P) (sFil P))
    (hP : ∀ T, P T → InU W T) {d r : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (z : Γ(X, W)) (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r)
    (hc : Rp (W := W) P u x c) : Rp (W := W) P u (fun I => z * x I) (fAct hF hP r z c) := by
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulMor hF r (evLift hP z) (evLift_nat hP z)).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from evLift hP z (s.obj (Fin.last r))) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have := J_mul_sFil P r _ (evLift_mul_sub hP z (x I) (s.obj (Fin.last r))) hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (evLift hP z (s.obj (Fin.last r))) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

theorem basis : KH.LocGr → KH.PolyTf → ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {W₀ : X.Opens} {d : ℕ}
    (c : Coord q W₀ d) (r : ℕ) (hr : r < s),
    ∃ ω : Idx r d → HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) (St (TF l s) {W₀}) r,
      ∀ (W : X.Opens) (hW : IsAffineOpen W) (hle : W ≤ W₀) (Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))))
        (hQ : Q = St (TF l s) {W}) (hQ₀ : Q ≤ St (TF l s) {W₀}) (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InU W T)
        (h : HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r),
        ∃! f : Idx r d → Γ(X, W), h = ∑ k, GlobalTheory.CompanionTheory.GrCech.fAct hF hQW r (f k) ((resU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) hQ₀).pull r (ω k)) := by
  classical
  intro hLoc hPoly O _ l s hb X q W₀ d c r hr
  have hL : StLoc := stLoc stFrame hLoc hPoly
  have hE : StExists := exists_of_cocycle stCocycle
  let u : Fin d → ∀ T : Thick (LL q), T.B := fun k T => lft W₀ T (c.t k)
  have hu : IsLift W₀ c.t u := fun k T h => lft_spec T h _
  choose ω hω using fun k : Idx r d => hE W₀ c.t u hu (SS q l s W₀) (ss_inU l s W₀) r (Pi.single k 1)
  refine ⟨ω, ?_⟩
  intro W hW hle Q hQ hQ₀ hF hQW h
  have hFree : Free W Q r u := free_at hL hb hle hW c hu hr hQ
  have hu' : IsLift W (fun i => rs hle (c.t i)) u := isLift_res hle hu fun _ => rfl
  have hrep : ∀ f : Idx r d → Γ(X, W), Rp (W := W) Q u f
      (∑ k, fAct hF hQW r (f k) ((resU (GF q r) hQ₀).pull r (ω k))) := by
    intro f
    have s1 := rp_sum hE stAdd hu' hQW Finset.univ
      (fun k I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(X, W₀)) I)) _
      (fun k _ => rp_fAct hF hQW hu' (f k) _ _
        (stRes W₀ W hle c.t u hu (SS q l s W₀) Q hQ₀ (ss_inU l s W₀) hQW r _ _ (hω k)))
    have e : (∑ k, fun I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(X, W₀)) I)) = f := by
      funext I
      rw [Finset.sum_apply, Finset.sum_eq_single I]
      · simp
      · intro b _ hb'
        simp [Pi.single_eq_of_ne (Ne.symm hb')]
      · simp
    rwa [e] at s1
  obtain ⟨x, hx⟩ := hFree.1 h
  refine ⟨x, rp_class hx (hrep x), fun y hy => ?_⟩
  have hy' : Rp (W := W) Q u y h := by
    rw [hy]
    exact hrep y
  exact rp_coef stAdd hu' hQW hFree hy' hx

end GlobalTheory.CompanionTheory.GrCech.Omega
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceTopIdeal
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Unit

theorem eq_top_of_killed_top {X : Scheme.{0}} {E : X.Modules} (S : Subobject E)
    (h : Killed (⊤ : X.IdealSheafData) S) : S = ⊤ := by
  refine top_le_iff.mp ((GlobalTheory.CompanionTheory.GE.le_iff_secs_subset ⊤ S).mpr fun U x _ => ?_)
  have hx := h U 1 (by simp [Scheme.IdealSheafData.ideal_top]) x
  rwa [one_smul] at hx

theorem statement_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] : Statement I (⊤ : X.IdealSheafData) := by
  intro E _ S hS hann hprop
  have htop : ∀ e, S e = ⊤ := fun e => GlobalTheory.CompanionTheory.GE.Unit.eq_top_of_killed_top (S e) (hann e)
  obtain ⟨hqc, -, -⟩ := hS
  unfold GlobalTheory.CompanionTheory.GE.Alg
  refine ⟨S 0, hqc 0, hprop, fun e => ?_⟩
  rw [htop 0, htop e, top_sup_eq]

end GlobalTheory.CompanionTheory.GE.Unit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisActionPeriodProductStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_period_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l) (s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l)),
    (∀ μ, μ ∈ s) → (∀ μ, PrePer K χ μ (t μ)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), g (μ x) = μ x) →
      actB g (∏ μ ∈ s, t μ) =
        algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * ∏ μ ∈ s, t μ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.actB_prod_periods | exact GlobalTheory.CompanionTheory.LTPer.actB_prod_periods | (intros; apply GlobalTheory.CompanionTheory.LTPer.actB_prod_periods <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasicoherent_sup_sections : ∀ {X : Scheme.{0}} {E : X.Modules}, E.IsQuasicoherent → ∀ (S T : Subobject E), (S : X.Modules).IsQuasicoherent → (T : X.Modules).IsQuasicoherent → ((S ⊔ T : Subobject E) : X.Modules).IsQuasicoherent ∧ ∀ V : X.Opens, IsAffineOpen V → secs (S ⊔ T) V = {x | ∃ s ∈ secs S V, ∃ t ∈ secs T V, x = s + t} := by
  first | exact @GlobalTheory.CompanionTheory.GE.supsecs | exact GlobalTheory.CompanionTheory.GE.supsecs | (intros; apply GlobalTheory.CompanionTheory.GE.supsecs <;> assumption)
end

