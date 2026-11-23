module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogEx

theorem mul_pred_lt_pow (l v : ℕ) (hl : 1 ≤ l) : v * (l - 1) + 1 ≤ l ^ v := by
  obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    nlinarith [Nat.zero_le (v * d * d)]

theorem exists_term {R : Type} [CommRing R] (l : ℕ) (hl : l.Prime)
    (hu : ∀ a : ℕ, ¬ l ∣ a → IsUnit (a : R)) (m w : R) (hw : (l : R) * w = m ^ (l - 1))
    (hwl : (l : R) ∣ w ^ l) (k : ℕ) :
    ∃ c : R, ((k + 1 : ℕ) : R) * c = m ^ k ∧ (l : R) ^ (k / (l - 1) / l) ∣ c ∧
      (k ≠ 0 → c ∈ (Ideal.span {(l : R)}).radical) := by
  obtain ⟨v, a, ha, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) l hl.ne_one
  obtain ⟨b, hb⟩ := (hu a ha).exists_right_inv
  have hl2 := hl.two_le
  have ha0 : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; exact ha (dvd_zero _))
  have hv : v ≤ k / (l - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 := mul_pred_lt_pow l v hl.one_le
    have h2 : l ^ v ≤ l ^ v * a := Nat.le_mul_of_pos_right _ ha0
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hv
  have hqr := Nat.div_add_mod k (l - 1)
  set q := k / (l - 1) with hq
  set r := k % (l - 1) with hr
  have hwr : w ∈ (Ideal.span {(l : R)}).radical := ⟨l, Ideal.mem_span_singleton.2 hwl⟩
  have hmr : m ∈ (Ideal.span {(l : R)}).radical := ⟨l - 1, Ideal.mem_span_singleton.2 ⟨w, hw.symm⟩⟩
  refine ⟨b * (l : R) ^ d * m ^ r * w ^ q, ?_, ?_, fun hk0 => ?_⟩
  · have e : m ^ k = ((l : R) * w) ^ q * m ^ r := by
      rw [hw, ← pow_mul, ← pow_add, hqr]
    have e2 : ((k + 1 : ℕ) : R) = (l : R) ^ v * a := by
      rw [show k + 1 = l ^ v * a from hk]; push_cast; rfl
    rw [e, e2, mul_pow]
    have e3 : (l : R) ^ q = (l : R) ^ v * (l : R) ^ d := by rw [hd, pow_add]
    rw [e3]
    linear_combination ((l : R) ^ v * (l : R) ^ d * m ^ r * w ^ q) * hb
  · refine Dvd.dvd.mul_left ?_ _
    refine (pow_dvd_pow_of_dvd hwl _).trans ?_
    rw [← pow_mul]
    exact pow_dvd_pow _ (Nat.mul_div_le q l)
  · rcases Nat.eq_zero_or_pos q with h | h
    · have : 0 < r := by
        rw [h] at hqr
        omega
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hmr _ this))
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hwr _ h)

theorem exists_sum {A : Type} [CommRing A] (p : A) [IsAdicComplete (Ideal.span {p}) A]
    (c : ℕ → A) (N : ℕ → ℕ) (hN : Monotone N) (hc : ∀ r k, N r ≤ k → p ^ r ∣ c k) :
    ∃ u : A, ∀ r n, N r ≤ n → p ^ r ∣ u - ∑ k ∈ Finset.range n, c k := by
  have key : ∀ r n, N r ≤ n →
      p ^ r ∣ ∑ k ∈ Finset.range n, c k - ∑ k ∈ Finset.range (N r), c k := by
    intro r n h
    rw [← Finset.sum_Ico_eq_sub _ h]
    exact Finset.dvd_sum fun k hk => hc r k (Finset.mem_Ico.1 hk).1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {p}) (M := A) inferInstance
    (f := fun r => ∑ k ∈ Finset.range (N r), c k) (fun {a b} hab => by
      rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact key a _ (hN hab))
  refine ⟨L, fun r n h => ?_⟩
  have h1 := hL r
  rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h1
  have := dvd_sub h1 (key r n h)
  rwa [sub_sub_sub_cancel_right] at this

theorem exists_unit {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (l : ℕ) (hl : l.Prime)
    (hA : IsAdicComplete (Ideal.span {(l : A)}) A)
    (hu : ∀ a : ℕ, ¬ l ∣ a → IsUnit (a : R)) (m w : R) (hw : (l : R) * w = m ^ (l - 1))
    (hwl : (l : R) ∣ w ^ l) :
    ∃ (c : ℕ → R) (u : A), (∀ k, ((k + 1 : ℕ) : R) * c k = m ^ k) ∧ IsUnit u ∧
      ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N,
        (l : A) ^ r ∣ u - f (∑ k ∈ Finset.range n, (-1) ^ k * c k) := by
  choose c h1 h2 h3 using exists_term l hl hu m w hw hwl
  have hl2 := hl.two_le
  obtain ⟨u, hs⟩ := exists_sum (l : A) (fun k => f ((-1) ^ k * c k)) (fun r => r * l * (l - 1))
    (fun a b hab => Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hab)) (fun r k hk => by
      have hr : r ≤ k / (l - 1) / l := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by omega)]
        exact hk
      have := map_dvd f (((pow_dvd_pow (l : R) hr).trans (h2 k)).mul_left ((-1) ^ k))
      rwa [map_pow, map_natCast] at this)
  refine ⟨c, u, h1, ?_, fun r => ⟨_, fun n hn => by rw [map_sum]; exact hs r n hn⟩⟩
  have hc0 : c 0 = 1 := by simpa using h1 0
  have hrad : u - 1 ∈ (Ideal.span {(l : A)}).radical := by
    have h := hs 1 (1 * l * (l - 1) + 1) (Nat.le_succ _)
    rw [Finset.sum_range_succ', pow_one, hc0, pow_zero, mul_one, map_one] at h
    have h' := Ideal.le_radical (Ideal.mem_span_singleton.2 h)
    have h'' : ∑ k ∈ Finset.range (1 * l * (l - 1)), f ((-1) ^ (k + 1) * c (k + 1)) ∈
        (Ideal.span {(l : A)}).radical := by
      refine Ideal.sum_mem _ fun k _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      obtain ⟨n, hn⟩ := h3 (k + 1) (Nat.succ_ne_zero k)
      refine ⟨n, Ideal.mem_span_singleton.2 ?_⟩
      have := map_dvd f (Ideal.mem_span_singleton.1 hn)
      rwa [map_pow, map_natCast] at this
    have := add_mem h' h''
    convert this using 1
    ring
  have hj : u - 1 ∈ Ideal.jacobson (⊥ : Ideal A) := by
    have h := Ideal.radical_le_jacobson hrad
    have h' := Ideal.jacobson_mono (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : A)})) h
    rwa [Ideal.jacobson_idem] at h'
  exact Ideal.isUnit_of_sub_one_mem_jacobson_bot u hj

theorem isUnit_nat_acris0 (l : ℕ) [Fact l.Prime] (a : ℕ) (ha : ¬ l ∣ a) :
    IsUnit (a : Per.Acris0 l) := by
  have h : IsUnit (a : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 ha
  have := h.map ((algebraMap (Per.Ainf l) (Per.Acris0 l)).comp (Per.zA l))
  rwa [map_natCast] at this

theorem algebraMap_acris (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

theorem factorial_mul_sum {P : Type} [CommRing P] (m : P) (c : ℕ → P)
    (h : ∀ k, ((k + 1 : ℕ) : P) * c k = m ^ k) (n : ℕ) :
    ((n.factorial : ℕ) : P) * (m * ∑ k ∈ Finset.range n, (-1) ^ k * c k) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : P) * m ^ (k + 1) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hd : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
  have e : ((n.factorial : ℕ) : P) = ((n.factorial / (k + 1) : ℕ) : P) * ((k + 1 : ℕ) : P) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
  rw [pow_succ m, ← h k]
  linear_combination (m * (-1) ^ k * c k) * e

end GlobalTheory.MemLoc.LogEx

namespace GlobalTheory.MemLoc
open LogEx

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem exists_isLogA : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ (t u : Per.Acris l), IsLogA e t ∧ IsUnit u ∧
      t = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * u := by
  intro l _ e he
  obtain ⟨w, hw, hwl⟩ := _root_.GlobalTheory.MemLoc.exists_mu_pow_div l e he
  obtain ⟨c, u, h1, hu, h2⟩ := exists_unit (algebraMap (Per.Acris0 l) (Per.Acris l)) l Fact.out
    (acris_basic l).1 (isUnit_nat_acris0 l) (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) w
    (Subtype.ext (by simpa using hw)) hwl
  refine ⟨_, u, fun r => ?_, hu, rfl⟩
  obtain ⟨N, hN⟩ := h2 r
  refine ⟨N, fun n hn => ⟨algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) *
    ∑ k ∈ Finset.range n, (-1) ^ k * c k, ?_, ?_⟩⟩
  · have := congrArg (Per.Acris0 l).val
      (factorial_mul_sum (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) c h1 n)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_natCast, map_sum] at this
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_neg, map_one, AlgHom.commutes]
  · obtain ⟨z, hz⟩ := hN n hn
    refine ⟨algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * z, ?_⟩
    rw [map_mul, ← algebraMap_acris, ← mul_sub, hz]
    ring

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientComplete
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.XiSat

section general
variable {R : Type} [CommRing R]

theorem smodEq_iff (p : R) (k : ℕ) (a b : R) :
    (a ≡ b [SMOD (Ideal.span {p} ^ k • ⊤ : Submodule R R)]) ↔ p ^ k ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem sat_pow [IsDomain R] (p x : R) (h : ∀ a, x ∣ p * a → x ∣ a) (n : ℕ) :
    ∀ a, x ^ n ∣ p * a → x ^ n ∣ a := by
  by_cases hx : x = 0
  · cases n with
    | zero => intro a _; simp
    | succ n => subst hx; simpa using h
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a ha
    obtain ⟨b, rfl⟩ := h a ((dvd_pow_self x n.succ_ne_zero).trans ha)
    rw [pow_succ'] at ha ⊢
    rw [mul_left_comm, mul_dvd_mul_iff_left hx] at ha
    exact mul_dvd_mul_left x (ih b ha)

theorem sat_ppow (p y : R) (h : ∀ a, y ∣ p * a → y ∣ a) (k : ℕ) :
    ∀ a, y ∣ p ^ k * a → y ∣ a := by
  induction k with
  | zero => intro a ha; simpa using ha
  | succ k ih =>
    intro a ha
    rw [pow_succ', mul_assoc] at ha
    exact ih a (h _ ha)

theorem quot_dvd_iff (p y : R) (k : ℕ) (a : R) :
    (Ideal.Quotient.mk (Ideal.span {y}) p) ^ k ∣ Ideal.Quotient.mk (Ideal.span {y}) a ↔
      ∃ b c, a = y * b + p ^ k * c := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
    obtain ⟨b, hb⟩ := hc
    exact ⟨b, c, by linear_combination hb⟩
  · rintro ⟨b, c, rfl⟩
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨b, by ring⟩

theorem complete_quot [IsDomain R] (p y : R) [hc : IsAdicComplete (Ideal.span {p}) R]
    (h : ∀ a, y ∣ p * a → y ∣ a) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {y}) p}) (R ⧸ Ideal.span {y}) := by
  refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [smodEq_iff, sub_zero, quot_dvd_iff] at hx
    choose b c hbc using hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    by_cases hy : y = 0
    · subst hy
      have : a = 0 := IsHausdorff.haus' (I := Ideal.span {p}) a fun k => by
        rw [smodEq_iff]
        exact ⟨c k, by linear_combination hbc k⟩
      simp [this]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) b fun {m n} hmn => by
      rw [smodEq_iff]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have e : y * (b m - b (m + d)) = p ^ m * (p ^ d * c (m + d) - c m) := by
        linear_combination hbc (m + d) - hbc m
      obtain ⟨w, hw⟩ := sat_ppow p y h m _ ⟨_, e.symm⟩
      refine ⟨w, mul_left_cancel₀ hy ?_⟩
      rw [e, hw]; ring
    have : a - y * L = 0 := IsHausdorff.haus' (I := Ideal.span {p}) _ fun k => by
      obtain ⟨w, hw⟩ := (smodEq_iff p k _ _).1 (hL k)
      rw [smodEq_iff]
      exact ⟨c k + y * w, by linear_combination hbc k + y * hw⟩
    exact ⟨L, by linear_combination this⟩
  · intro f hf
    choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)
    have h1 : ∀ n, ∃ b c, g n - g (n + 1) = y * b + p ^ n * c := fun n => by
      have := (smodEq_iff _ n _ _).1 (hf (Nat.le_succ n))
      rwa [← hg, ← hg, ← map_sub, quot_dvd_iff] at this
    choose b c hbc using h1
    let u : ℕ → R := fun n => g n + y * ∑ i ∈ Finset.range n, b i
    have hu : ∀ n, p ^ n ∣ u n - u (n + 1) := fun n =>
      ⟨c n, by simp only [u, Finset.sum_range_succ]; linear_combination hbc n⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) u fun {m n} hmn => by
      rw [smodEq_iff]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := dvd_add ih ((pow_dvd_pow p hmn).trans (hu n))
        rwa [sub_add_sub_cancel] at this
    refine ⟨Ideal.Quotient.mk _ L, fun n => ?_⟩
    obtain ⟨w, hw⟩ := (smodEq_iff p n _ _).1 (hL n)
    rw [smodEq_iff, ← hg, ← map_sub, quot_dvd_iff]
    exact ⟨-∑ i ∈ Finset.range n, b i, w, by simp only [u] at hw; linear_combination hw⟩

end general

theorem xi_sat : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ (l : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ IsAdicComplete (Ideal.span {(l : Per.Ainf l ⧸ Ideal.span {xi e ^ n})}) (Per.Ainf l ⧸ Ideal.span {xi e ^ n}) := by
  intro l _ e he n
  have := (_root_.GlobalTheory.MemLoc.ainf_isDomain_and_injective l).1
  have hk := _root_.GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd l e he
  have h1 : ∀ a : Per.Ainf l, xi e ∣ (l : Per.Ainf l) * a → xi e ∣ a := fun a ha => by
    rw [← hk] at ha ⊢
    rw [map_mul, map_natCast, mul_eq_zero] at ha
    refine ha.resolve_left fun h0 => GlobalTheory.RingBasics.p_ne_zero (p := l) ?_
    simpa using congrArg Subtype.val h0
  have h2 := sat_pow _ _ h1 n
  refine ⟨h2, ?_⟩
  have : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  have := complete_quot (l : Per.Ainf l) (xi e ^ n) h2
  rwa [map_natCast] at this

end GlobalTheory.MemLoc.XiSat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Imports
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqHaarRight

theorem isMulRightInvariant :
    ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant :=
  fun P Q μ hμ => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q μ hμ

end GlobalTheory.UpqHaarRight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralConj
section
open NumberField

namespace GlobalTheory.HermDen

open ReciprocityTheory.ChartRestriction.G.FD

theorem isIntegral_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {x : E}
    (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom

theorem exists_den (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ ((den : E) * ReciprocityTheory.ChartRestriction.G.FD.herm G x y) := by
  classical
  obtain ⟨k, hk, hi⟩ := GlobalTheory.LatFin.exists_common_den Λ hΛ
  obtain ⟨l, hl, hG⟩ := GlobalTheory.LatFin.exists_common_den
    (Submodule.span (𝓞 E) (Set.range fun a : Fin r => (G a : Fin r → E)))
    (Submodule.fg_span (Set.finite_range _))
  have hG' : ∀ a b, IsIntegral ℤ ((l : E) * G a b) := fun a b =>
    hG _ (Submodule.subset_span ⟨a, rfl⟩) b
  refine ⟨((k * k * l : ℤ) : 𝓞 E), Int.cast_ne_zero.2 (mul_ne_zero (mul_ne_zero hk hk) hl),
    fun x hx y hy => ?_⟩
  have e : ((((k * k * l : ℤ) : 𝓞 E)) : E) * herm G x y
      = ∑ a, ∑ b, ((k : E) * x a) * ((l : E) * G a b) * cc ((k : E) * y b) := by
    have h1 : ((((k * k * l : ℤ) : 𝓞 E)) : E) = (k : E) * k * l := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast]
      push_cast
      ring
    rw [h1, herm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h2 : cc ((k : E) * y b) = k * cc (y b) := by simp [cc]
    rw [h2]
    ring
  rw [e]
  exact IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ =>
    ((hi x hx a).mul (hG' a b)).mul (isIntegral_conj (hi y hy b))

end GlobalTheory.HermDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ τ : L →+* ℂ, IsPolyRep (fun B => evM P (evPt τ B)) := by
  first | exact @GlobalTheory.AlgWtHW.isPolyRep_evPt | exact GlobalTheory.AlgWtHW.isPolyRep_evPt | (intros; apply GlobalTheory.AlgWtHW.isPolyRep_evPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ker_localizedTheta_eq_span_of_dvd (l : ℕ) [Fact l.Prime] (x : Per.Ainf l)
    (hx : ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ x ∣ a) :
    Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) x} := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    have hy' : Per.θP l y = 0 := GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l y (by rwa [pow_one])
    have h0 : Per.θ l a = 0 := by
      have h1 := GlobalTheory.RingIface.fontaineTheta_algebraMap (l := l) a
      rw [← ha, map_mul, hy', zero_mul] at h1
      exact Subtype.ext h1.symm
    obtain ⟨c, rfl⟩ := (hx a).1 h0
    have hu : IsUnit (algebraMap (Per.Ainf l) (Per.AinfP l) ((l : ℕ) : Per.Ainf l) ^ n) :=
      (IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)).pow n
    rw [← Ideal.mul_unit_mem_iff_mem _ hu, ha, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact GlobalTheory.RingIface.alg_mem_kerP (l := l) ((hx x).2 dvd_rfl)

theorem ker_localizedTheta_eq_span_xi : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} :=
  fun l _ e he => ker_localizedTheta_eq_span_of_dvd l (xi e) (theta_eq_zero_iff_xi_dvd l e he)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqDefiniteCompact
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory

theorem Jpq_zero_left_eq_neg_one (q : ℕ) : Formalism.UG.Jpq 0 q = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact i.elim0
  · exact i.elim0
  · exact j.elim0
  · simp [Formalism.UG.Jpq, Matrix.one_apply]

theorem isCompact_Upq_zero_left (q : ℕ) :
    IsCompact (Formalism.UG.Upq 0 q : Set (GL (Fin 0 ⊕ Fin q) ℂ)) := by
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Fin 0 ⊕ Fin q)
    (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const) (fun _ h => h)
  convert hc using 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  rw [Formalism.UG.P.mem_Upq_iff, Jpq_zero_left_eq_neg_one, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, neg_inj]

theorem compactSpace_UpqT_definite :
    ∀ N : ℕ, CompactSpace (UpqT N 0) ∧ CompactSpace (UpqT 0 N) := fun N =>
  ⟨(isCompact_iff_compactSpace.1 (Formalism.UG.P.indefinite_unitary_compact N) :
      CompactSpace (Formalism.UG.Upq N 0 : Set (GL (Fin N ⊕ Fin 0) ℂ))),
    (isCompact_iff_compactSpace.1 (isCompact_Upq_zero_left N) :
      CompactSpace (Formalism.UG.Upq 0 N : Set (GL (Fin 0 ⊕ Fin N) ℂ)))⟩

end GlobalTheory
end

