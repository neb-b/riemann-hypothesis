module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEq
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Values

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

theorem zeta_pow (m i : ℕ) : P.ζQ (m + i) ^ (l ^ i) = P.ζQ m := by
  induction i with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, P.ζQ_succ, ih]

theorem cycVal_single {s e j : ℕ} (hj : 1 ≤ j) (hjs : j ≤ s) (μ : ℕ → ℤ) (V : Om l)
    (hμ : ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (μ a : Om l) * P.ζQ i ^ a = if i = j then V else 0)
    (x : ↥(K0 K)) :
    cycVal P K s e (fun a => (μ a : ↥(K0 K)) * x) 0 =
      (l : Om l) ^ (e * (s - j)) * (((frK P K ^ (s - j)) x : ↥(K0 K)) : Om l) * V := by
  have key : ∀ i ∈ Finset.range s,
      ∑ a ∈ primeTo l s, (((frK P K ^ i) ((μ a : ↥(K0 K)) * x) : ↥(K0 K)) : Om l) *
        P.ζQ s ^ (a * l ^ i) =
      (((frK P K ^ i) x : ↥(K0 K)) : Om l) * (if s - i = j then V else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [← hμ (s - i) (by omega) (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hz : P.ζQ s ^ (l ^ i) = P.ζQ (s - i) := by
      have := zeta_pow P (s - i) i
      rwa [Nat.sub_add_cancel hi'.le] at this
    rw [map_mul, map_intCast, mul_comm a, pow_mul, hz]
    push_cast
    ring
  unfold cycVal
  rw [Finset.sum_congr rfl fun i hi => by rw [key i hi], Finset.sum_eq_single (s - j)]
  · rw [if_pos (by omega)]
    simp [mul_assoc]
  · intro i hi hne
    have hi' := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem cycVal_add (s e : ℕ) (f g : ℕ → ↥(K0 K)) (d : ↥(K0 K)) :
    cycVal P K s e (fun a => f a + g a) d =
      cycVal P K s e f 0 + cycVal P K s e g 0 + (l : Om l) ^ (s * e) * (d : Om l) := by
  unfold cycVal
  simp only [map_add (f := _), IntermediateField.coe_add, add_mul, Finset.sum_add_distrib, mul_add,
    IntermediateField.coe_zero, mul_zero, add_zero]

theorem exists_pre (k : ℕ) (y : ↥(K0 K)) :
    ∃ x : ↥(K0 K), (frK P K ^ k) x = y ∧ ‖(x : Om l)‖ = ‖(y : Om l)‖ := by
  induction k generalizing y with
  | zero => exact ⟨y, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨z, rfl⟩ := (P.PD K).σ_bij.2 y
    obtain ⟨x, hx, hn⟩ := ih z
    refine ⟨x, ?_, ?_⟩
    · rw [pow_succ', AlgHom.mul_apply, hx]
    · rw [hn]
      exact ((_root_.GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective l P K).1 z).symm

theorem norm_int_mul {z : ℤ} {x : ↥(K0 K)} (hx : ‖(x : Om l)‖ ≤ 1) :
    ‖(((z : ↥(K0 K)) * x : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  push_cast
  rw [norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ z) (norm_nonneg _) hx

theorem norm_pow_mul (k : ℕ) {x : ↥(K0 K)} (hx : ‖(x : Om l)‖ ≤ 1) :
    ‖(((l : ↥(K0 K)) ^ k * x : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  have := norm_int_mul K (z := (l : ℤ) ^ k) hx
  simpa using this

theorem sum_zeta : ∑ r ∈ Finset.Ico 1 l, P.ζQ 1 ^ r = -1 := by
  have h1 : P.ζQ 1 ^ l = 1 := (P.ζQ_succ 0).trans P.ζQ_zero
  have h2 := mul_geom_sum (P.ζQ 1) l
  rw [h1, sub_self, mul_eq_zero] at h2
  have h3 := h2.resolve_left (sub_ne_zero.mpr P.ζQ_one)
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : l.Prime).pos] at h3
  simp only [pow_zero, zero_add] at h3
  linear_combination h3

theorem exists_minus_one {s : ℕ} (hs : 1 ≤ s) : ∃ ν : ℕ → ℤ,
    ∑ a ∈ primeTo l s, ν a = ((l : ℤ) - 1) * (l : ℤ) ^ (s - 1) ∧ ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (ν a : Om l) * P.ζQ i ^ a =
        if i = 1 then -(l : Om l) ^ (s - 1) else 0 := by
  have h : ∀ r : ℕ, ∃ μ : ℕ → ℤ, r ∈ Finset.Ico 1 l →
      (∑ a ∈ primeTo l s, μ a = (l : ℤ) ^ (s - 1) ∧ ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (μ a : Om l) * P.ζQ i ^ a =
        if i = 1 then (l : Om l) ^ (s - 1) * P.ζQ 1 ^ r else 0) := by
    intro r
    by_cases hr : r ∈ Finset.Ico 1 l
    · have hr' := Finset.mem_Ico.mp hr
      obtain ⟨μ, h1, h2⟩ := _root_.GlobalTheory.LevelSums.exists_weights l P.ζQ P.ζQ_zero P.ζQ_one P.ζQ_succ s 1 r le_rfl hs
        (Nat.not_dvd_of_pos_of_lt hr'.1 hr'.2)
      exact ⟨μ, fun _ => ⟨by simpa using h1, by simpa using h2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose μ hμ using h
  refine ⟨fun a => ∑ r ∈ Finset.Ico 1 l, μ r a, ?_, fun i hi his => ?_⟩
  · rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr => (hμ r hr).1, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (Fact.out : l.Prime).one_lt.le, Nat.cast_one]
  · push_cast
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr => (hμ r hr).2 i hi his]
    split_ifs
    · rw [← Finset.mul_sum, sum_zeta]
      ring
    · simp

theorem exists_cycVal_eq (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e j n : ℕ)
    (hj : 1 ≤ j) (hjs : j ≤ s) (hn : ¬ l ∣ n) (c : Om l) (hc : c ∈ K0 K) (hc1 : ‖c‖ ≤ 1) :
    ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧
      d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧
      cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * (c * P.ζQ j ^ n) := by
  obtain ⟨c, rfl⟩ : ∃ c' : ↥(K0 K), (c' : Om l) = c := ⟨⟨c, hc⟩, rfl⟩
  obtain ⟨μ, h1, h2⟩ := _root_.GlobalTheory.LevelSums.exists_weights l P.ζQ P.ζQ_zero P.ζQ_one P.ζQ_succ s j n hj hjs hn
  by_cases hj1 : j = 1
  · subst hj1
    simp only [if_true] at h1 h2
    obtain ⟨ν, g1, g2⟩ := exists_minus_one P hjs
    obtain ⟨d, hd, hdc⟩ := (_root_.GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective l P K).2 (e + 1) (by omega) (frK P K c)
      (by rw [(_root_.GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective l P K).1]; exact hc1)
    obtain ⟨x, hx, hxn⟩ := exists_pre P K (s - 1) c
    obtain ⟨y, hy, hyn⟩ := exists_pre P K (s - 1) ((l : ↥(K0 K)) ^ e * d)
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at *
    refine ⟨fun a => (μ a : ↥(K0 K)) * x + (ν a : ↥(K0 K)) * y, (l : ↥(K0 K)) ^ t * d,
      fun a => ?_, norm_pow_mul K t hd, ?_, ?_⟩
    · rw [IntermediateField.coe_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        (norm_int_mul K (hxn ▸ hc1)) (norm_int_mul K (hyn ▸ norm_pow_mul K e hd)))
    · rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Int.cast_sum,
        ← Int.cast_sum, h1, g1, pow_succ' (frK P K), AlgHom.mul_apply, map_add, map_mul, map_mul,
        map_mul, map_intCast, map_intCast, hx, hy]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_intCast]
      push_cast
      linear_combination (l : ↥(K0 K)) ^ t * hdc
    · rw [cycVal_add, cycVal_single P K le_rfl hjs μ _ h2, cycVal_single P K le_rfl hjs ν _ g2]
      simp only [Nat.add_sub_cancel]
      rw [hx, hy]
      push_cast
      ring
  · simp only [if_neg hj1] at h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = k + 2 + t := ⟨s - (k + 2), by omega⟩
    obtain ⟨x, hx, hxn⟩ := exists_pre P K t ((l : ↥(K0 K)) ^ ((e + 1) * k + e) * c)
    refine ⟨fun a => (μ a : ↥(K0 K)) * x, 0,
      fun a => norm_int_mul K (hxn ▸ norm_pow_mul K _ hc1), by simp, ?_, ?_⟩
    · rw [← Finset.sum_mul, ← Int.cast_sum, h1]
      simp
    · rw [cycVal_single P K hj hjs μ _ h2, Nat.add_sub_cancel_left, hx,
        show k + 2 + t - 1 = k + t + 1 by omega]
      push_cast
      ring

end GlobalTheory.ExpImage.Values
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiagonalRingHomOfLetterwiseReductions
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory

theorem exists_diagonal_ringHom_of_letterwise_reductions :
    ∀ (I E F R : Type) [Fintype I] [CommRing E] [CommRing F] [CommRing R] (e : I → E), (∀ i, e i * e i = e i) → (∀ i j, i ≠ j → e i * e j = 0) → ∑ i, e i = 1 → ∀ (p : I → (E →+* F)) (r : E →+* R), (∀ i, Function.Surjective (p i)) → (∀ i x, p i x = 0 → r (e i) * r x = 0) → ∃ κ : F →+* R, ∀ i x, r (e i) * κ (p i x) = r (e i) * r x := by
  intro I E F R _ _ _ _ e hid hort hsum p r hsurj hker
  classical
  choose s hs using hsurj
  have key : ∀ i x y, p i x = p i y → r (e i) * r x = r (e i) * r y := by
    intro i x y h
    have := hker i (x - y) (by rw [map_sub, h, sub_self])
    rw [map_sub, mul_sub] at this
    exact sub_eq_zero.mp this
  have hext : ∀ a b : R, (∀ i, r (e i) * a = r (e i) * b) → a = b := by
    intro a b h
    have h1 : ∑ i, r (e i) = 1 := by rw [← map_sum, hsum, map_one]
    calc a = (∑ i, r (e i)) * a := by rw [h1, one_mul]
      _ = (∑ i, r (e i)) * b := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => h i
      _ = b := by rw [h1, one_mul]
  have hidR : ∀ i, r (e i) * r (e i) = r (e i) := fun i => by rw [← map_mul, hid]
  let k : F → R := fun c => ∑ i, r (e i) * r (s i c)
  have hk0 : ∀ i c, r (e i) * k c = r (e i) * r (s i c) := by
    intro i c
    show r (e i) * ∑ j, r (e j) * r (s j c) = _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [← mul_assoc, hidR]
    · intro j _ hj
      rw [← mul_assoc, ← map_mul, hort i j (Ne.symm hj), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : ∀ i x, r (e i) * k (p i x) = r (e i) * r x := by
    intro i x
    rw [hk0]
    exact key i _ _ (hs i _)
  refine ⟨{ toFun := k, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hk⟩
  · apply hext
    intro i
    have := hk i 1
    rwa [map_one, map_one] at this
  · intro a b
    apply hext
    intro i
    have h := hk i (s i a * s i b)
    rw [map_mul, hs, hs, map_mul] at h
    have ha := hk0 i a
    have hb := hk0 i b
    have hi := hidR i
    rw [h]
    linear_combination (-(k b)) * ha - (r (s i a)) * hb
  · apply hext
    intro i
    have := hk i 0
    rwa [map_zero, map_zero] at this
  · intro a b
    apply hext
    intro i
    have h := hk i (s i a + s i b)
    rw [map_add (f := _), hs, hs, map_add (f := _)] at h
    rw [h, mul_add, mul_add, hk0, hk0]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.FilCount

theorem exists_eq_of_exhaustive {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hle : ∀ a, F a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ F a) : ∃ b : ℤ, ∀ a ≤ b, F a = D := by
  obtain ⟨s, hs⟩ : D.FG := (Submodule.fg_iff_finiteDimensional D).2 inferInstance
  have hsD : ∀ x ∈ s, x ∈ D := fun x hx => hs ▸ Submodule.subset_span hx
  choose! f hf using hex
  obtain ⟨b, hb⟩ := (s.image f).bddBelow
  refine ⟨b, fun a ha => le_antisymm (hle a) ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  have hbx : b ≤ f x := hb (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx))
  exact hF (ha.trans hbx) (hf x (hsD x hx))

theorem telescope (d : ℤ → ℤ) (c : ℤ) (b : ℤ) (hb : ∀ a ≤ b, d a = c) (J : Finset ℤ)
    (hJ : ∀ a, a ∉ J → d a - d (a + 1) = 0) :
    c - d 0 = ∑ a ∈ J.filter (· < 0), (d a - d (a + 1)) := by
  have tel : ∀ n : ℕ, ∑ a ∈ Finset.Ico (-(n : ℤ)) 0, (d a - d (a + 1)) = d (-n) - d 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : Finset.Ico (-((n + 1 : ℕ) : ℤ)) 0
          = insert (-((n + 1 : ℕ) : ℤ)) (Finset.Ico (-(n : ℤ)) 0) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        push_cast
        omega
      rw [e, Finset.sum_insert (by simp only [Finset.mem_Ico]; push_cast; omega), ih]
      have e2 : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      rw [e2]; ring
  obtain ⟨m, hm⟩ := J.bddBelow
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, -(n : ℤ) ≤ m ∧ -(n : ℤ) ≤ b :=
    ⟨m.natAbs + b.natAbs, by omega, by omega⟩
  rw [← hb _ hn2, ← tel n]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_Ico.2 ⟨hn1.trans (hm (Finset.mem_coe.2 hx.1)), hx.2⟩
  · intro x hx hx'
    refine hJ x fun h => hx' (Finset.mem_filter.2 ⟨h, (Finset.mem_Ico.1 hx).2⟩)

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem tmul_mem_filV (a : ℤ) (v : V) (b : BdR) (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] ⟨b, hb⟩, rfl⟩

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) := by
  have hA : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
  rintro a b hab _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v c => exact tmul_mem_filV PD a v c.1 (hA hab c.2)
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem filV_exhaustive (x : V ⊗[Qp] BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v c =>
    obtain ⟨a, ha⟩ := PD.Fil_exh c
    exact ⟨a, tmul_mem_filV PD a v c ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem codim_fil_zero (ρ : Representation LL G V) [FiniteDimensional LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (J : Finset ℤ) (hJ : ∀ a, a ∉ J → multV PD ρ τ a = 0) :
    (Module.finrank LL ↥(DdRE PD ρ τ) : ℤ) - Module.finrank LL ↥(FildR PD ρ τ 0)
      = ∑ a ∈ J.filter (· < 0), multV PD ρ τ a := by
  have : FiniteDimensional LL ↥(DdRE PD ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  obtain ⟨b, hb⟩ := exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ)
    (fun a b hab => inf_le_inf_left _ (filV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (filV_exhaustive PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
  exact telescope (fun a => (Module.finrank LL ↥(FildR PD ρ τ a) : ℤ)) _ b
    (fun a ha => by rw [hb a ha]) J hJ

end

theorem fil_count : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
      (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (J : Finset ℤ), (∀ a, a ∉ J → multV (P.PD K) ρ τ a = 0) →
      (Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) : ℤ) - Module.finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ 0)
        = ∑ a ∈ J.filter (· < 0), multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ J hJ
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  exact codim_fil_zero (P.PD K) ρ τ J hJ

end GlobalTheory.Per.FilCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalTwoCocycleOfLocalTateDuality
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

theorem exists_fundamental_cocycle_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), CompactSpace ↥(GK K) ∧
      ∃ (χ : ↥(GK K) →* ℤ_[l]ˣ) (c : ↥(GK K) × ↥(GK K) → ℤ_[l]),
        Continuous (fun g => (χ g : ℤ_[l])) ∧
        (∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) ∧
        (∀ r, GlobalTheory.TateTop.Gen χ r c) ∧
        ∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep
          ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ))) := by
  intro l _ P K
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  refine ⟨Φ.symm.surjective.compactSpace hΦ1, χZ.comp Φ.toMonoidHom, _, hχc.comp hΦ2,
    fun g => ?_, fun r => (hc r).transport Φ hΦ2 hΦ1, fun r hr => ?_⟩
  · have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    exact h1
  · have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hfin := (_root_.GlobalTheory.finite_H1_H2_of_localTateDuality hT l K.1 K.2 r (ZMod (l ^ r))
      (ReciprocityTheory.Gal.charRep (redChar χZ r)) hr
      (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
    obtain ⟨e⟩ := (GlobalTheory.contCohomology_transport_mulEquiv (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1)
      ↥(GK K) (ZMod (l ^ r)) Φ hΦ2 hΦ1 (ReciprocityTheory.Gal.charRep (redChar χZ r))
      (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
        (χZ.comp Φ.toMonoidHom))) (fun g m => rfl)).1
    exact Finite.of_equiv _ e

end GlobalTheory.TateTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLetterBijection
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_letter_bijection {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) :
    ∃ τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K)),
      Function.Bijective τ ∧ (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ∀ i, τ (i - 1) = τ i - 1 := by
  obtain ⟨-, -, -, hSb, hSσ, -⟩ := S.hyp.1
  have hWb := (S.W H).emb_bij
  have hWσ := (S.W H).emb_σ
  have key : ∀ j, (S.W H).emb ((Equiv.ofBijective _ hWb).symm j) = j :=
    Equiv.ofBijective_apply_symm_apply _ hWb
  refine ⟨fun i => (Equiv.ofBijective _ hWb).symm (S.emb i),
    (Equiv.ofBijective _ hWb).symm.bijective.comp hSb, fun i => key _, fun i => hWb.1 ?_⟩
  calc (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb (i - 1)))
      = S.emb (i - 1) := key _
    _ = (S.emb (i - 1 + 1)).comp (P.PD S.K).σ := (hSσ _).symm
    _ = ((S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i))).comp (P.PD S.K).σ := by
        rw [sub_add_cancel, key]
    _ = (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1) := by
        rw [← hWσ ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1), sub_add_cancel]

end GlobalTheory.RedFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOne
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem exists_lifts_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : ↥(K0 K)), ‖(c : Om l)‖ ≤ 1 → ∃ w : Ainf l, Lifts AI K w c := by
  intro l _ P AI T K c hc
  obtain ⟨n, z, ω, hω, hsum⟩ := _root_.GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c c.2 hc
  have h1 : ∀ i, ∃ w : Ainf l, Lifts AI K w ⟨ω i, (hω i).1⟩ := by
    intro i
    obtain ⟨hK, m, hm, hl, hx⟩ := hω i
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (ω i) m hm hl hx
    exact ⟨_, AI.ιA_teich ⟨ω i, hK.2⟩ m hm hl hx xb hxb⟩
  choose w hw using h1
  have h2 : c = ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * ⟨ω i, (hω i).1⟩ := by
    apply Subtype.ext
    rw [hsum]
    push_cast
    rfl
  refine ⟨∑ i, algebraMap ℤ_[l] (Ainf l) (z i) * w i, ?_⟩
  unfold Lifts at hw ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hw, ιA_zl AI T, ← IsScalarTower.algebraMap_apply]

end GlobalTheory.ExpImage
end

