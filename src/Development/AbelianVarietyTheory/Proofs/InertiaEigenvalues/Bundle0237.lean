module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc


open PowerSeries in
theorem algHom_sub_dvd {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧) (hf : (X : O⟦X⟧) ∣ f X)
    (a : O⟦X⟧) : f X - X ∣ f a - a := by
  set y := f X with hy
  let g : ℕ → O⟦X⟧ := fun n => ∑ i ∈ Finset.range n, y ^ i * X ^ (n - 1 - i)
  have hg : ∀ n, g n * (y - X) = y ^ n - X ^ n := fun n => geom_sum₂_mul y X n
  have hgd : ∀ n, (X : O⟦X⟧) ^ (n - 1) ∣ g n := by
    intro n
    refine Finset.dvd_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have e : n - 1 = i + (n - 1 - i) := by omega
    conv_lhs => rw [e, pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd hf i) dvd_rfl
  let P : ℕ → O⟦X⟧ := fun N => ∑ n ∈ Finset.range N, C (coeff n a) * g n
  have hP : ∀ m k, (X : O⟦X⟧) ^ m ∣ P (m + 1 + k) - P (m + 1) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : P (m + 1 + (k + 1)) - P (m + 1)
          = (P (m + 1 + k) - P (m + 1)) + C (coeff (m + 1 + k) a) * g (m + 1 + k) := by
        simp only [P, ← add_assoc, Finset.sum_range_succ _ (m + 1 + k)]; ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_left ((pow_dvd_pow _ (by omega)).trans (hgd _)) _)
  let b : O⟦X⟧ := PowerSeries.mk fun m => coeff m (P (m + 2))
  have hb : ∀ N, (X : O⟦X⟧) ^ N ∣ P (N + 1) - b := by
    intro N
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
    have := X_pow_dvd_iff.mp (hP (m + 1) k) m (by omega)
    rw [map_sub] at this ⊢
    rw [coeff_mk, show m + k + 1 + 1 = m + 1 + 1 + k by omega]
    exact this
  have hr : ∀ N, ∃ r : O⟦X⟧, a = ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n + X ^ N * r := by
    intro N
    have : (X : O⟦X⟧) ^ N ∣ a - ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp [coeff_X_pow, hm]
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr]; ring⟩
  have hN : ∀ N, (X : O⟦X⟧) ^ N ∣ f a - a - (y - X) * P N := by
    intro N
    obtain ⟨r, hr⟩ := hr N
    have h1 : f a = ∑ n ∈ Finset.range N, C (coeff n a) * y ^ n + y ^ N * f r := by
      conv_lhs => rw [hr]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_mul, map_pow, ← hy]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      exact f.commutes _
    have h2 : (y - X) * P N = ∑ n ∈ Finset.range N, C (coeff n a) * y ^ n
        - ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n := by
      simp only [P, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← mul_sub, ← hg]; ring
    have h3 : f a - a - (y - X) * P N = y ^ N * f r - X ^ N * r := by
      rw [h2, h1]; linear_combination -hr
    rw [h3]
    exact dvd_sub (Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hf N) _) (dvd_mul_right _ _)
  refine ⟨b, ?_⟩
  ext m
  have : (X : O⟦X⟧) ^ (m + 1) ∣ f a - a - (y - X) * b := by
    have e : f a - a - (y - X) * b
        = (f a - a - (y - X) * P (m + 1 + 1)) + (y - X) * (P (m + 1 + 1) - b) := by ring
    rw [e]
    exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hN _)) (Dvd.dvd.mul_left (hb _) _)
  have := X_pow_dvd_iff.mp this m (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.mp this

theorem geom_sum_one_add_prime {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (x : R) :
    ∃ r, ∑ k ∈ Finset.range p, (1 + x) ^ k = x ^ (p - 1) + (p : R) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (Polynomial.X : Polynomial ℤ) 1
  have h1 : (∑ k ∈ Finset.range p, (1 + Polynomial.X : Polynomial ℤ) ^ k)
      = Polynomial.X ^ (p - 1) + (p : Polynomial ℤ) * r := by
    apply mul_right_cancel₀ (Polynomial.X_ne_zero (R := ℤ))
    have h := geom_sum_mul (1 + Polynomial.X : Polynomial ℤ) p
    have e : (Polynomial.X : Polynomial ℤ) ^ p = Polynomial.X ^ (p - 1) * Polynomial.X := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
    rw [add_comm Polynomial.X, one_pow, e] at hr
    rw [hr] at h
    linear_combination h
  refine ⟨Polynomial.aeval x r, ?_⟩
  have := congrArg (Polynomial.aeval x) h1
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum] using this

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem act_X_eq (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := (GlobalTheory.Cyc.act_laws l O).1 c

theorem act_comm' (c c' : ℤ_[l]) (a) : act l O c (act l O c' a) = act l O c' (act l O c a) := by
  rw [(GlobalTheory.Cyc.act_laws l O).2.1, (GlobalTheory.Cyc.act_laws l O).2.1, mul_comm]

theorem act_nat_X (k : ℕ) : act l O (k : ℤ_[l]) PowerSeries.X = (1 + PowerSeries.X) ^ k - 1 := by
  rw [act_X_eq, (GlobalTheory.Cyc.act_laws l O).2.2.2.1]

theorem cyc_eq_X_mul (c : ℤ_[l]) :
    ∃ b, cyc l O c = PowerSeries.X * (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) := by
  have : (PowerSeries.X : PowerSeries O) ^ 2 ∣
      cyc l O c - PowerSeries.C (algebraMap ℤ_[l] O c) * PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [cyc_const]
    · simp [(GlobalTheory.Cyc.act_laws l O).2.2.2.2.1]
  obtain ⟨b, hb⟩ := this
  exact ⟨b, by linear_combination hb⟩

theorem XX_mul_QQ (s : ℕ) : XX l O s * QQ l O s = (1 + XX l O s) ^ l - 1 := by
  have h := geom_sum_mul (1 + XX l O s) l
  unfold QQ
  linear_combination h

theorem XX_mul_QQ' (s : ℕ) (hs : 1 ≤ s) :
    XX l O s * QQ l O s = (1 + PowerSeries.X) ^ l ^ s - 1 := by
  rw [XX_mul_QQ, XX, add_sub_cancel, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hs]

theorem phi_pow_X (n : ℕ) :
    (phi l O ^ n) PowerSeries.X = (1 + PowerSeries.X) ^ l ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgHom.mul_apply, ih]
    simp only [map_sub, map_pow, map_add (f := _), map_one, phi, act_nat_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ']

theorem act_C (c : ℤ_[l]) (x : O) : act l O c (PowerSeries.C x) = PowerSeries.C x :=
  (act l O c).commutes x

theorem act_QQ_one (c : ℤ_[l]ˣ) :
    ∃ b, act l O c (QQ l O 1) = QQ l O 1 * (1 + PowerSeries.X * b) := by
  obtain ⟨b, hb⟩ := cyc_eq_X_mul l O c
  have h1 : PowerSeries.X * QQ l O 1 = act l O (l : ℤ_[l]) PowerSeries.X := by
    have := XX_mul_QQ' l O 1 le_rfl
    rw [act_nat_X]
    simpa [XX] using this
  have h2 := act_comm' l O c l PowerSeries.X
  rw [← h1, map_mul, act_X_eq, hb] at h2
  simp only [map_mul, map_add (f := _), act_C, ← h1] at h2
  have hU : IsUnit (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using c.isUnit.map (algebraMap ℤ_[l] O)
  obtain ⟨v, hv⟩ := hU.exists_right_inv
  have h3 : (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) * act l O c (QQ l O 1)
      = QQ l O 1 * (PowerSeries.C (algebraMap ℤ_[l] O c)
        + PowerSeries.X * QQ l O 1 * act l O (l : ℤ_[l]) b) := by
    apply PowerSeries.X_mul_cancel
    linear_combination h2
  refine ⟨v * (QQ l O 1 * act l O (l : ℤ_[l]) b - b), ?_⟩
  linear_combination v * h3 + (QQ l O 1 - act l O c (QQ l O 1)) * hv

theorem XX_QQ_properties : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], ∀ s : ℕ, 1 ≤ s → phi l O (XX l O s) = XX l O s * QQ l O s ∧ (phi l O ^ (s - 1)) PowerSeries.X = XX l O s ∧ PowerSeries.constantCoeff (QQ l O s) = (l : O) ∧ (∃ b, QQ l O s = PowerSeries.X ^ (l ^ (s - 1) * (l - 1)) + (l : PowerSeries O) * b) ∧ (∃ b, QQ l O s = (l : PowerSeries O) + XX l O s * b) ∧ (∀ c : ℤ_[l]ˣ, (∃ b, act l O c (XX l O s) = XX l O s * (PowerSeries.C (algebraMap ℤ_[l] O c) + XX l O s * b)) ∧ ∃ b, act l O c (QQ l O s) = QQ l O s * (1 + XX l O s * b)) ∧ ∀ (u w : ℤ_[l]), u = 1 + (l : ℤ_[l]) ^ s * w → ∀ a, ∃ b, act l O u a - a = XX l O s * QQ l O s * b := by
  intro l _ O _ _ s hs
  have hp : l.Prime := Fact.out
  have hψ : act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) PowerSeries.X = XX l O s := act_nat_X l O _
  have hψQ : act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) (QQ l O 1) = QQ l O s := by
    have : XX l O 1 = PowerSeries.X := by simp [XX]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [QQ, this, map_sum, map_pow, map_add (f := _), map_one, hψ]
  have h0 : PowerSeries.constantCoeff (XX l O s) = 0 := by simp [XX]
  refine ⟨?_, phi_pow_X l O _, ?_, ?_, ?_, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [XX_mul_QQ' l O s hs, XX]
    simp only [map_sub, map_pow, map_add (f := _), map_one, phi, act_nat_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [QQ, map_sum, h0]
  · obtain ⟨r, hr⟩ := geom_sum_one_add_prime hp (XX l O s)
    obtain ⟨t, ht⟩ := exists_add_pow_prime_pow_eq hp (PowerSeries.X : PowerSeries O) 1 (s - 1)
    have h1 : (l : PowerSeries O) ∣ XX l O s - PowerSeries.X ^ l ^ (s - 1) :=
      ⟨PowerSeries.X * t, by rw [XX, add_comm, ht]; ring⟩
    obtain ⟨q, hq⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ (l - 1))
    refine ⟨q + r, ?_⟩
    rw [QQ, hr, pow_mul]
    linear_combination hq
  · have : XX l O s ∣ QQ l O s - l := by
      have e : QQ l O s - l = ∑ k ∈ Finset.range l, ((1 + XX l O s) ^ k - 1) := by
        simp [QQ, Finset.sum_sub_distrib]
      rw [e]
      refine Finset.dvd_sum fun k _ => ?_
      simpa using sub_one_dvd_pow_sub_one (1 + XX l O s) k
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by linear_combination hb⟩
  · obtain ⟨b, hb⟩ := cyc_eq_X_mul l O c
    refine ⟨act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) b, ?_⟩
    conv_lhs => rw [← hψ, act_comm', act_X_eq, hb]
    simp only [map_mul, map_add (f := _), act_C, hψ]
  · obtain ⟨b, hb⟩ := act_QQ_one l O c
    refine ⟨act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) b, ?_⟩
    conv_lhs => rw [← hψQ, act_comm', hb]
    simp only [map_mul, map_add (f := _), map_one, hψ, hψQ]
  · intro u w hu a
    have hX : PowerSeries.X ∣ act l O u PowerSeries.X := by
      rw [act_X_eq, PowerSeries.X_dvd_iff]; exact cyc_const l O u
    refine Dvd.dvd.trans ?_ (algHom_sub_dvd (act l O u) hX a)
    obtain ⟨b, hb⟩ := cyc_eq_X_mul l O w
    have h1 : cyc l O (((l ^ s : ℕ) : ℤ_[l]) * w) = XX l O s * QQ l O s *
        act l O ((l ^ s : ℕ) : ℤ_[l]) (PowerSeries.C (algebraMap ℤ_[l] O w) + PowerSeries.X * b) := by
      rw [← act_X_eq, ← (GlobalTheory.Cyc.act_laws l O).2.1, act_X_eq l O w, hb, map_mul, act_nat_X,
        XX_mul_QQ' l O s hs]
    have h2 : cyc l O u + 1 = (cyc l O ((1 : ℕ) : ℤ_[l]) + 1) * (cyc l O (((l ^ s : ℕ) : ℤ_[l]) * w) + 1) := by
      simp only [cyc, sub_add_cancel]
      rw [← map_mul, ← PowerSeries.binomialSeries_add, hu]
      push_cast
      rfl
    rw [(GlobalTheory.Cyc.act_laws l O).2.2.2.1, h1] at h2
    rw [act_X_eq]
    exact ⟨(1 + PowerSeries.X) * act l O ((l ^ s : ℕ) : ℤ_[l])
      (PowerSeries.C (algebraMap ℤ_[l] O w) + PowerSeries.X * b), by linear_combination h2⟩

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightNonnegOfIdempotentGlnPr
section
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace CompanionTheory.Member.TraceCoefficientSum

variable {G : Type} [Group G] [Fintype G]

theorem coeff_zOf (χ : G → ℂ) (x : G) : (zOf χ).coeff x = χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ := by
  simp [zOf, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem eq_sum_single (a : MonoidAlgebra ℂ G) : a = ∑ x, MonoidAlgebra.single x (a.coeff x) := by
  ext y
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem coeff_mul_zOf (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * ∑ x, a.coeff x * χ x := by
  conv_lhs => rw [eq_sum_single a]
  rw [Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.coeff_single_mul_apply, coeff_zOf, mul_one, inv_inv]
  ring

theorem trace_alg (a : MonoidAlgebra ℂ G) (V : FDRep ℂ G) :
    ∑ x, a.coeff x * V.character x =
      LinearMap.trace ℂ V (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
  conv_rhs => rw [eq_sum_single a]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul]
  rfl

theorem trace_nat (a : MonoidAlgebra ℂ G) (ha : a * a = a) (V : FDRep ℂ G) :
    ∃ m : ℕ, ∑ x, a.coeff x * V.character x = m := by
  have hi : IsIdempotentElem (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
    unfold IsIdempotentElem
    rw [← map_mul, ha]
  rw [trace_alg]
  exact ⟨_, (LinearMap.IsIdempotentElem.isProj_range _ hi).trace⟩

theorem re_nonneg (a : MonoidAlgebra ℂ G) (ha : a * a = a) (χ : G → ℂ) (hχ : IsIrr χ) :
    0 ≤ ((a * zOf χ).coeff 1).re := by
  obtain ⟨V, -, hV⟩ := hχ
  obtain ⟨m, hm⟩ := trace_nat a ha V
  rw [coeff_mul_zOf, ← hV 1, FDRep.char_one]
  simp only [← hV]
  rw [hm, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast m,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

end CompanionTheory.Member.TraceCoefficientSum

theorem CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  intro g _ L n a ha h1 f
  refine div_nonneg ?_ h1
  unfold eSerC
  refine finsum_mem_induction (fun b => 0 ≤ ((a * b).coeff 1).re) (by simp) ?_ ?_
  · intro x y hx hy
    rw [mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Complex.add_re]
    exact add_nonneg hx hy
  · intro χ hχ
    exact CompanionTheory.Member.TraceCoefficientSum.re_nonneg a ha χ hχ.1

end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | exact CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | (intros; apply CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateBasisOfIsDecompletionAtLevel
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem htBasis_of_isDec : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  intro l _ act χ _ _ K m d M U Dm g J hD hH
  obtain ⟨hdet, -, -, -, hrel⟩ := hD
  obtain ⟨e, u, hli, hu, hfix⟩ := hH
  have hDe : ∀ v : Fin d → PadicComplex l, Dm.mulVec (Dm⁻¹.mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hinj : ∀ v w : Fin d → PadicComplex l, Dm.mulVec v = Dm.mulVec w → v = w := by
    intro v w h
    have h2 := congrArg (fun x => Dm⁻¹.mulVec x) h
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] using h2
  refine ⟨fun k => Dm⁻¹.mulVec (e k), u, ?_, hu, ?_⟩
  · refine LinearIndependent.of_comp Dm.mulVecLin ?_
    have : (Dm.mulVecLin ∘ fun k => Dm⁻¹.mulVec (e k)) = e := by
      funext k
      exact hDe (e k)
    rw [this]
    exact hli
  · intro σ hσ k
    apply hinj
    have hmap : (Dm.map (act σ)).mulVec (fun a => act σ (Dm⁻¹.mulVec (e k) a)) =
        fun a => act σ (e k a) := by
      funext a
      conv_rhs => rw [← hDe (e k)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    have h1 := hfix σ hσ k
    unfold twAct at h1 ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hrel σ hσ, ← Matrix.mulVec_mulVec, hmap, h1, hDe]

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPoly
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPoly

theorem aeval_mem_of_stable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (p : L[X]) : ∀ x ∈ D, Polynomial.aeval f p x ∈ D := by
  induction p using Polynomial.induction_on with
  | C a => intro x hx; simpa [Module.algebraMap_end_apply] using D.smul_mem a hx
  | add p q hp hq => intro x hx; simpa using D.add_mem (hp x hx) (hq x hx)
  | monomial n a ih =>
    intro x hx
    have := ih _ (hD x hx)
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact this

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ (g * h) x = actVB PC.PD ρ g (actVB PC.PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actVB_one' (x : V ⊗[Qp] B) : actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actVB_resH (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_Dpcris_iff (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ g ∈ PC.H, actVB PC.PD ρ g x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, actVB_resH, Subtype.forall]

theorem Dpcris_stable (g : G) : ∀ x ∈ PC.Dpcris ρ, actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  intro x hx
  rw [mem_Dpcris_iff] at hx ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ PC.H := by simpa using PC.normal.conj_mem h hh g⁻¹
  rw [← actVB_mul', show h * g = g * (g⁻¹ * h * g) by group, actVB_mul', hx _ h1]

end

end GlobalTheory.PassPoly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCocTmulOne
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter

namespace GlobalTheory.TensorOneCoc

theorem isCoc_tmul_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (G : Subgroup (GQ l)) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥G →* (Y →ₗ[ℤ_[l]] Y)) (b : ℤ) (f : ↥G → Y), (∀ g h, f (g * h) = f g + ρ g (f h)) → (∀ (n : ℕ) (g : ↥G), ∀ᶠ h in nhds g, ∃ y : Y, f h - f g = (l ^ n : ℕ) • y) → ∀ one : ↥(Mxi (AinfSub l) (xiU AI) 0), (one : WCb l) = 1 → letI : TopologicalSpace (TensorProduct ℤ_[l] Y (Qab (AinfSub l) (xiU AI) 0 b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; IsCoc (repQ AI G ρ 0 b) (fun g => f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b)) := by
  intro l _ P AI G Y _ _ ρ b f hf hc one h1
  refine ⟨(GlobalTheory.continuous_adicModule_iff (l : ℤ_[l]) _).2 fun g n => ?_, fun g h => ?_⟩
  · filter_upwards [hc n g] with h ⟨y, e⟩
    refine ⟨y ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b), ?_⟩
    rw [← TensorProduct.sub_tmul, e, TensorProduct.smul_tmul', ← Nat.cast_pow,
      Nat.cast_smul_eq_nsmul]
  · have hq : actQab (xiOK AI) 0 b (g : GQ l)
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b) = Submodule.Quotient.mk one := by
      rw [actQab, Submodule.mapQ_apply]
      congr 1
      apply Subtype.ext
      change AI.actWCbHom (g : GQ l) (one : WCb l) = one
      rw [h1, map_one]
    have : repQ AI G ρ 0 b g (f h ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b))
        = ρ g (f h) ⊗ₜ[ℤ_[l]] actQab (xiOK AI) 0 b (g : GQ l) (Submodule.Quotient.mk one) := rfl
    beta_reduce
    rw [this, hq, hf, TensorProduct.add_tmul]

end GlobalTheory.TensorOneCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowPrimePowSubOneStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (k : ℕ), 2 ≤ k → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∀ n : ℕ, ‖u ^ l ^ n - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := by
  first | exact @GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one | exact GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one | (intros; apply GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUnitTeichmullerPrincipalUnitSplitStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Fl l), IsUnit x → ∃ (ω x₁ : Per.Fl l) (N : ℕ), x = ω * x₁ ∧ GlobalTheory.LogU.InJ (Per.tm (x₁ ^ (l ^ N)) - 1) ∧ ∀ (g : Per.Gq l) (e : Per.Fl l), e.untilt = 1 → Per.σF g x = x * e → Per.σF g ω = ω := by
  first | (exact @GlobalTheory.LogU.teich_split) | (exact GlobalTheory.LogU.teich_split) | (intros; apply GlobalTheory.LogU.teich_split  <;> assumption)
end

