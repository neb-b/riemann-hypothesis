module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0510
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubGoodIdempotentEqBadTupleSums
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module Polynomial

namespace GlobalTheory.BadCount

open Classical

variable (D : D7)

theorem neZeroG (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem factG (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

attribute [local instance] neZeroG factG

def allTup (k : Fin 2) : Finset (Tup D k) :=
  Finset.univ.image fun a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) => fun v => Formalism.CyclotomicNorms.monicOf (a v)

theorem monicOf_injective (k : Fin 2) :
    Function.Injective (Formalism.CyclotomicNorms.monicOf : (Fin D.R.r → ZMod (D.host.g k)) → (ZMod (D.host.g k))[X]) := by
  intro a b h
  funext i
  rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt a i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]

theorem tupOf_injective (k : Fin 2) :
    Function.Injective fun a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) => fun v => Formalism.CyclotomicNorms.monicOf (a v) := by
  intro a b h
  funext v
  exact monicOf_injective D k (congrFun h v)

theorem badElt_coeff (k : Fin 2) (S : Finset (Tup D k)) (g : G0g D.nd) :
    (badElt D k S).coeff g = if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
      ∑ t ∈ S, ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0 := by
  unfold badElt
  rfl

theorem sum_eSer_monicOf (k : Fin 2) :
    ∑ b : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf b) = 1 := by
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
  rw [← hsum, ← Finset.sum_image (fun a _ b _ h => monicOf_injective D k h)]
  symm
  apply Finset.sum_subset
  · intro f hf
    obtain ⟨h1, h2, -⟩ := (hS f).1 hf
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f h1 h2⟩
  · intro f _ hf
    exact D.ntypes.eSer_zero k f fun h => hf ((hS f).2 h)

theorem badElt_all (k : Fin 2) : badElt D k (allTup D k) = 1 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [badElt_coeff, allTup, Finset.sum_image (fun a _ b _ h => tupOf_injective D k h)]
  have e : ∑ a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)),
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (a v))).coeff (g ⟨k, v⟩) =
      ∏ v, (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))).coeff (g ⟨k, v⟩) := by
    refine (Fintype.prod_sum (fun v (b : Fin D.R.r → ZMod (D.host.g k)) =>
      (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf b)).coeff (g ⟨k, v⟩))).symm.trans ?_
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← sum_eSer_monicOf D k, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.one_def]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h1 : g = 1
  · subst h1; simp
  · rw [if_neg (Ne.symm h1)]
    split_ifs with hs
    · obtain ⟨kv, hkv⟩ := Function.ne_iff.1 h1
      obtain ⟨k', v⟩ := kv
      by_cases hk : k' = k
      · subst hk
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg fun h => hkv h.symm)
      · exact absurd (hs ⟨k', v⟩ hk) hkv
    · rfl

def goodSet (k : Fin 2) : Finset (Tup D k) := (allTup D k).filter (goodAt D k)

def badSet (k : Fin 2) : Finset (Tup D k) := (allTup D k).filter fun t => ¬ goodAt D k t

theorem badElt_good_add_bad (k : Fin 2) : badElt D k (goodSet D k) + badElt D k (badSet D k) = 1 := by
  rw [← badElt_all D k]
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, badElt_coeff, badElt_coeff, badElt_coeff]
  split_ifs
  · exact Finset.sum_filter_add_sum_filter_not _ _ _
  · simp

theorem badElt_coeff_off (k : Fin 2) (S : Finset (Tup D k)) (h : G0g D.nd)
    (hh : ∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k ∧ h kv ≠ 1) : (badElt D k S).coeff h = 0 := by
  rw [badElt_coeff, if_neg]
  obtain ⟨kv, h1, h2⟩ := hh
  exact fun hs => h2 (hs kv h1)

theorem coeff_mul_factors (x y : MonoidAlgebra ℂ (G0g D.nd))
    (hx : ∀ h : G0g D.nd, (∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 0 ∧ h kv ≠ 1) → x.coeff h = 0)
    (hy : ∀ h : G0g D.nd, (∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 1 ∧ h kv ≠ 1) → y.coeff h = 0)
    (g : G0g D.nd) :
    (x * y).coeff g = x.coeff (fun kv => if kv.1 = 0 then g kv else 1) *
      y.coeff (fun kv => if kv.1 = 0 then 1 else g kv) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
  rw [Finsupp.sum_eq_single (fun kv => if kv.1 = 0 then g kv else 1)]
  · congr 2
    funext kv
    by_cases h0 : kv.1 = 0
    · simp [h0]
    · simp [h0]
  · intro b hb hne
    have hb0 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 0 → b kv = 1 := by
      intro kv hkv
      by_contra hc
      exact hb (hx b ⟨kv, hkv, hc⟩)
    obtain ⟨kv, hkv⟩ := Function.ne_iff.1 hne
    by_cases h0 : kv.1 = 0
    · rw [hy _ ⟨kv, by rw [h0]; decide, ?_⟩, mul_zero]
      intro hc
      apply hkv
      simp only [h0, if_true]
      have : (b⁻¹ * g) kv = 1 := hc
      rw [Pi.mul_apply, Pi.inv_apply, inv_mul_eq_one] at this
      exact this
    · exact absurd (by simp [h0, hb0 kv h0]) hkv
  · intro _
    exact zero_mul _

theorem e0_eq : D.ntypes.e0 = badElt D 0 (goodSet D 0) * badElt D 1 (goodSet D 1) := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_factors D _ _ (fun h hh => badElt_coeff_off D 0 _ h hh) (fun h hh => badElt_coeff_off D 1 _ h hh),
    badElt_coeff, badElt_coeff, if_pos, if_pos]
  rotate_left
  · rintro ⟨k, v⟩ hk
    fin_cases k
    · simp
    · exact absurd rfl hk
  · rintro ⟨k, v⟩ hk
    fin_cases k
    · exact absurd rfl hk
    · simp
  have he : D.ntypes.e0.coeff g =
      ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
        (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
          ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0) := rfl
  rw [he, finsum_eq_sum_of_fintype, goodSet, goodSet, Finset.sum_filter, Finset.sum_filter, allTup, allTup,
    Finset.sum_image (fun a _ b _ h => tupOf_injective D 0 h),
    Finset.sum_image (fun a _ b _ h => tupOf_injective D 1 h),
    Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.piCurry fun k (_ : D.nd.PlG k) => Fin D.R.r → ZMod (D.host.g k)).trans
    (piFinTwoEquiv _)) _ _ fun a => ?_
  have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
      goodAt D 0 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) ∧ goodAt D 1 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) :=
    Fin.forall_fin_two
  rw [Fintype.prod_sigma, Fin.prod_univ_two]
  by_cases h0 : goodAt D 0 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
  by_cases h1 : goodAt D 1 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
  simp [hg, h0, h1, piFinTwoEquiv_apply, Equiv.piCurry_apply, Sigma.curry]

theorem one_sub_goodTypeIdempotent_eq_badTupleSums : ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧
    1 - D.ntypes.e0 = badElt D 0 (S 0) + badElt D 1 (S 1) - badElt D 0 (S 0) * badElt D 1 (S 1) := by
  refine ⟨badSet D, fun k t ht => (Finset.mem_filter.1 ht).2, ?_⟩
  rw [e0_eq, ← sub_eq_iff_eq_add'.2 (badElt_good_add_bad D 0).symm,
    ← sub_eq_iff_eq_add'.2 (badElt_good_add_bad D 1).symm]
  noncomm_ring

end GlobalTheory.BadCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarJacLeExp
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.PolarJacBound

open MvPolynomial in
private lemma shc_nonneg' (x : ℝ) : 0 ≤ _root_.Formalism.MainNotions.SchurIrreducible.shc x := by
  unfold _root_.Formalism.MainNotions.SchurIrreducible.shc
  split_ifs with hx
  · norm_num
  · rcases lt_or_gt_of_ne hx with h | h
    · exact (div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h) h).le
    · exact (div_pos (Real.sinh_pos_iff.mpr h) h).le

open MvPolynomial in
private lemma sinh_div_le_exp_of_pos {y : ℝ} (hy : 0 < y) : Real.sinh y / y ≤ Real.exp y := by
  rw [div_le_iff₀ hy, Real.sinh_eq]
  have h1 : -(2 * y) + 1 ≤ Real.exp (-(2 * y)) := Real.add_one_le_exp _
  have h2 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 0 < Real.exp y := Real.exp_pos y
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]

open MvPolynomial in
private lemma shc_le_exp_abs (x : ℝ) : _root_.Formalism.MainNotions.SchurIrreducible.shc x ≤ Real.exp |x| := by
  unfold _root_.Formalism.MainNotions.SchurIrreducible.shc
  split_ifs with hx
  · simp [hx]
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [abs_of_neg h]
      have := sinh_div_le_exp_of_pos (neg_pos.mpr h)
      rwa [Real.sinh_neg, neg_div_neg_eq] at this
    · rw [abs_of_pos h]
      exact sinh_div_le_exp_of_pos h

open MvPolynomial in
private lemma sum_sum_ite_lt_four_mul_add_eq (m : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (if i < j then 4 * (a i + a j) else 0) =
      4 * (((m : ℝ) - 1) * ∑ i ∈ Finset.range m, a i) := by
  have e : ∀ i j, (if i < j then 4 * (a i + a j) else 0) =
      4 * ((if i < j then a i else 0) + (if i < j then a j else 0)) := by
    intro i j; split_ifs <;> ring
  simp_rw [e, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then a j else 0), ← Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  have t : ∀ j, ((if i < j then a i else 0) + (if j < i then a i else 0)) =
      a i - (if i = j then a i else 0) := by
    intro j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, not_lt.mpr hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt.mpr hij.le]
  simp_rw [t, Finset.sum_sub_distrib, Finset.sum_ite_eq, hi, Finset.sum_const, Finset.card_range]
  simp; ring

open MvPolynomial in
private lemma sum_norm_sq_diag_eq_sum_range_min (p q : ℕ) (h : ℕ → ℝ) :
    ∑ a : Fin p, ∑ b : Fin q, ‖if (a : ℕ) = b then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
      ∑ i ∈ Finset.range (min p q), h i ^ 2 := by
  have hrow : ∀ a : Fin p, ∑ b : Fin q, ‖if (a : ℕ) = b then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
      if (a : ℕ) < q then h a ^ 2 else 0 := by
    intro a
    rw [Fin.sum_univ_eq_sum_range (fun j => ‖if (a : ℕ) = j then ((h a : ℝ) : ℂ) else 0‖ ^ 2) q]
    have : ∀ j, ‖if (a : ℕ) = j then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
        if (a : ℕ) = j then h a ^ 2 else 0 := by
      intro j; split_ifs <;> simp
    simp_rw [this, Finset.sum_ite_eq, Finset.mem_range]
  simp_rw [hrow]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < q then h i ^ 2 else 0) p, ← Finset.sum_filter]
  congr 1
  ext i; simp [lt_min_iff]

open MvPolynomial in
private lemma hsNorm_aOf_eq_sqrt_two_mul_sum_sq (p q : ℕ) (h : ℕ → ℝ) :
    _root_.Formalism.BasicNotions.TH.hsNorm (_root_.Formalism.MainNotions.SchurIrreducible.aOf p q h) = Real.sqrt (2 * ∑ i ∈ Finset.range (min p q), h i ^ 2) := by
  simp only [_root_.Formalism.BasicNotions.TH.hsNorm, _root_.Formalism.MainNotions.SchurIrreducible.aOf, _root_.Formalism.MainNotions.SchurIrreducible.pOf]
  simp
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))), sum_norm_sq_diag_eq_sum_range_min, ← two_mul,
    Real.sqrt_mul (by norm_num)]


open MvPolynomial in
theorem _root_.GlobalTheory.PolarJacBound.polarJac_le_exp : ∀ (p q : ℕ) (h : ℕ → ℝ), (∏ i ∈ Finset.range (min p q), _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * (max p q - min p q))) * (∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2 else 1) ≤ Real.exp (((p + q : ℕ) : ℝ) * Real.sqrt (2 * (min p q : ℕ)) * _root_.Formalism.BasicNotions.TH.hsNorm (_root_.Formalism.MainNotions.SchurIrreducible.aOf p q h)) := by
  intro p q h
  set r := Finset.range (min p q) with hr
  set k := max p q - min p q with hk
  have hA : ∏ i ∈ r, _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * k) ≤
      ∏ i ∈ r, Real.exp ((2 + 2 * (k : ℝ)) * |h i|) := by
    refine Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (shc_nonneg' _) (pow_nonneg (shc_nonneg' _) _)) fun i _ => ?_
    calc _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * k)
        ≤ Real.exp |2 * h i| * Real.exp |h i| ^ (2 * k) :=
          mul_le_mul (shc_le_exp_abs _)
            (pow_le_pow_left₀ (shc_nonneg' _) (shc_le_exp_abs _) _)
            (pow_nonneg (shc_nonneg' _) _) (Real.exp_pos _).le
      _ = Real.exp ((2 + 2 * (k : ℝ)) * |h i|) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, abs_mul, abs_two]; push_cast; ring_nf
  have hB : (∏ i ∈ r, ∏ j ∈ r,
        if i < j then (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2 else 1) ≤
      ∏ i ∈ r, ∏ j ∈ r, Real.exp (if i < j then 4 * (|h i| + |h j|) else 0) := by
    refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => ?_) fun i _ =>
      Finset.prod_le_prod₀ (fun j _ => ?_) fun j _ => ?_
    · split_ifs
      · exact sq_nonneg _
      · exact zero_le_one
    · split_ifs
      · exact sq_nonneg _
      · exact zero_le_one
    · split_ifs
      · have h1 : _root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j) ≤
            Real.exp (2 * (|h i| + |h j|)) := by
          calc _root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)
              ≤ Real.exp |h i - h j| * Real.exp |h i + h j| :=
                mul_le_mul (shc_le_exp_abs _) (shc_le_exp_abs _) (shc_nonneg' _)
                  (Real.exp_pos _).le
            _ = Real.exp (|h i - h j| + |h i + h j|) := (Real.exp_add _ _).symm
            _ ≤ Real.exp (2 * (|h i| + |h j|)) := by
                gcongr
                linarith [abs_sub (h i) (h j), abs_add_le (h i) (h j)]
        calc (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2
            ≤ Real.exp (2 * (|h i| + |h j|)) ^ 2 :=
              pow_le_pow_left₀ (mul_nonneg (shc_nonneg' _) (shc_nonneg' _)) h1 2
          _ = Real.exp (4 * (|h i| + |h j|)) := by rw [← Real.exp_nat_mul]; ring_nf
      · simp
  set S := ∑ i ∈ r, |h i| with hS
  set Q := ∑ i ∈ r, h i ^ 2 with hQ
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCS : S ^ 2 ≤ (min p q : ℕ) * Q := by
    have := Finset.sum_mul_sq_le_sq_mul_sq r (fun _ => (1 : ℝ)) (fun i => |h i|)
    simpa [hr, sq_abs] using this
  have hkey : 2 * S ≤ Real.sqrt (2 * (min p q : ℕ)) * Real.sqrt (2 * Q) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hn : ((p + q : ℕ) : ℝ) = (max p q : ℕ) + (min p q : ℕ) := by
    rw [← Nat.cast_add, max_add_min]
  have hkR : (k : ℝ) = (max p q : ℕ) - (min p q : ℕ) := by
    rw [hk, Nat.cast_sub min_le_max]
  calc _ ≤ (∏ i ∈ r, Real.exp ((2 + 2 * (k : ℝ)) * |h i|)) *
        ∏ i ∈ r, ∏ j ∈ r, Real.exp (if i < j then 4 * (|h i| + |h j|) else 0) :=
        mul_le_mul hA hB (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
          split_ifs
          · exact sq_nonneg _
          · exact zero_le_one) (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
    _ = Real.exp ((2 + 2 * (k : ℝ)) * S + 4 * (((min p q : ℕ) : ℝ) - 1) * S) := by
        simp_rw [← Real.exp_sum]
        rw [← Real.exp_add]
        congr 1
        rw [hS, hr, sum_sum_ite_lt_four_mul_add_eq, ← Finset.mul_sum]
        ring
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [hsNorm_aOf_eq_sqrt_two_mul_sum_sq, mul_assoc, hn]
        have hm0 : (0 : ℝ) ≤ (min p q : ℕ) := Nat.cast_nonneg _
        have hM0 : (0 : ℝ) ≤ (max p q : ℕ) := Nat.cast_nonneg _
        rw [hkR]
        nlinarith [mul_le_mul_of_nonneg_left hkey (add_nonneg hM0 hm0)]

end GlobalTheory.PolarJacBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolariseIntegral
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial MeasureTheory

namespace GlobalTheory.SchurPol

theorem polarise_integral {G H : Type*} [MeasurableSpace G] [AddCommGroup H] [Module ℂ H]
    (μ : Measure G) (F : H → H → G → ℂ) (R : H → H → ℂ) (c : ℂ)
    (hF : ∀ x y g, F x y g = (1 / 4 : ℂ) * ((F (x + y) (x + y) g - F (x - y) (x - y) g) +
      c * (F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g)))
    (hR : ∀ x y, R x y = (1 / 4 : ℂ) * ((R (x + y) (x + y) - R (x - y) (x - y)) +
      c * (R (x + Complex.I • y) (x + Complex.I • y) -
        R (x - Complex.I • y) (x - Complex.I • y))))
    (hd : ∀ x, Integrable (F x x) μ ∧ ∫ g, F x x g ∂μ = R x x) (x y : H) :
    Integrable (F x y) μ ∧ ∫ g, F x y g ∂μ = R x y := by
  have e : F x y = fun g => (1 / 4 : ℂ) * ((F (x + y) (x + y) g - F (x - y) (x - y) g) +
      c * (F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g)) := funext (hF x y)
  have h1 : Integrable (fun g => F (x + y) (x + y) g - F (x - y) (x - y) g) μ :=
    (hd _).1.sub (hd _).1
  have h2 : Integrable (fun g => F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g) μ := (hd _).1.sub (hd _).1
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (h1.add (h2.const_mul c)).const_mul _
  · rw [hR x y]
    simp only [hF x y]
    rw [integral_const_mul, integral_add h1 (h2.const_mul c), integral_const_mul,
      integral_sub (hd _).1 (hd _).1, integral_sub (hd _).1 (hd _).1,
      (hd _).2, (hd _).2, (hd _).2, (hd _).2]

theorem schur_half {p q : ℕ} {T : GrpData p q} (D : DSRep T) (w u₁ u₂ : D.U.H) :
    Integrable (fun g => inner ℂ w (D.U.π g u₁) * star (inner ℂ w (D.U.π g u₂))) T.haar ∧
      ∫ g, inner ℂ w (D.U.π g u₁) * star (inner ℂ w (D.U.π g u₂)) ∂T.haar =
        ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ w w) := by
  refine polarise_integral T.haar
    (fun x y g => inner ℂ w (D.U.π g x) * star (inner ℂ w (D.U.π g y)))
    (fun x y => ((D.fdeg : ℂ))⁻¹ * inner ℂ y x * star (inner ℂ w w)) Complex.I ?_ ?_ ?_ u₁ u₂
  · intro x y g
    simp only [map_add (f := _), map_sub, map_smul, inner_add_right, inner_sub_right, inner_smul_right,
      star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * (inner ℂ w (D.U.π g x) * (starRingEnd ℂ) (inner ℂ w (D.U.π g y))
      - inner ℂ w (D.U.π g y) * (starRingEnd ℂ) (inner ℂ w (D.U.π g x))) * Complex.I_mul_I
  · intro x y
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, inner_sub_left,
      inner_smul_left, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * ((D.fdeg : ℂ))⁻¹ * star (inner ℂ w w) *
      (inner ℂ y x - inner ℂ x y) * Complex.I_mul_I
  · intro x
    have e : ∀ g, inner ℂ w (D.U.π g x) * star (inner ℂ w (D.U.π g x)) =
        ((‖inner ℂ w (D.U.π g x)‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e]
    refine ⟨(D.schur x w).1.ofReal, ?_⟩
    rw [integral_complex_ofReal, (D.schur x w).2, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K]
    simp only [Complex.star_def, map_pow, Complex.coe_algebraMap, Complex.conj_ofReal]
    push_cast
    ring

theorem schur_polarised (p q : ℕ) (T : GrpData p q) (D : DSRep T) (u₁ w₁ u₂ w₂ : D.U.H) :
    Integrable (fun g => inner ℂ w₁ (D.U.π g u₁) * star (inner ℂ w₂ (D.U.π g u₂))) T.haar ∧
      ∫ g, inner ℂ w₁ (D.U.π g u₁) * star (inner ℂ w₂ (D.U.π g u₂)) ∂T.haar =
        ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ w₂ w₁) := by
  refine polarise_integral T.haar
    (fun x y g => inner ℂ x (D.U.π g u₁) * star (inner ℂ y (D.U.π g u₂)))
    (fun x y => ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ y x)) (-Complex.I) ?_ ?_
    (fun x => schur_half D x u₁ u₂) w₁ w₂
  · intro x y g
    simp only [inner_add_left, inner_sub_left, inner_smul_left, map_add (f := _), map_sub, map_mul, map_neg,
      star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I, neg_neg]
    linear_combination (1 / 2 : ℂ) *
      (inner ℂ x (D.U.π g u₁) * (starRingEnd ℂ) (inner ℂ y (D.U.π g u₂))
      - inner ℂ y (D.U.π g u₁) * (starRingEnd ℂ) (inner ℂ x (D.U.π g u₂))) * Complex.I_mul_I
  · intro x y
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, inner_sub_left,
      inner_smul_left, Complex.conj_I, Complex.star_def, map_add, map_sub, map_mul, map_neg,
      neg_neg]
    linear_combination (1 / 2 : ℂ) * ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ *
      ((starRingEnd ℂ) (inner ℂ y x) - (starRingEnd ℂ) (inner ℂ x y)) * Complex.I_mul_I

end GlobalTheory.SchurPol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionComparisonStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalars_resolution_comparison : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S), ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) ∧ ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n) := by
  first
  | exact @GlobalTheory.EtC.restrRes_comparison
  | exact GlobalTheory.EtC.restrRes_comparison
  | (intros; apply GlobalTheory.EtC.restrRes_comparison <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearResolutionMapCohomologyEqZeroOfKillStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearResolutionMap_cohomology_eq_zero_of_kill : ∀ (S R : Type) [CommRing S] [CommRing R] (F : Shv S) (G : Shv R) (δ : SemiMap (res S F) (res R G)), (∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) → ∀ (E : Spc) (n : ℤ) (x : H S E F n), δ.op.app E n x = 0 := by
  first
  | exact @GlobalTheory.EtC.semiMap_op_eq_zero_of_kill
  | exact GlobalTheory.EtC.semiMap_op_eq_zero_of_kill
  | (intros; apply GlobalTheory.EtC.semiMap_op_eq_zero_of_kill <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwistedStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n := by
  first | (exact @GlobalTheory.Shin.shLift_hc_eq_hcTw) | (exact GlobalTheory.Shin.shLift_hc_eq_hcTw) | (intros; apply GlobalTheory.Shin.shLift_hc_eq_hcTw  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroLaurentSurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_zero_laurent_surjective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T], IsUnit (q : T) → ∀ (i : ℤ) (y : Ht q (sp (LaurentPolynomial T)) 0 i), ∃ z : Ht q (sp T) 0 i, pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) _ 0 z = y := by
  first | (exact @GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (exact GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (intros; apply GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq  <;> assumption)
end

