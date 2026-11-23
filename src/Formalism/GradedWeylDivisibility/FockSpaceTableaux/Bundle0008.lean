module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0005
public import Formalism.GradedWeylDivisibility.Bundle0001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0003
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0004
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0006

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_initW_eq_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) :
    (∑ k : Fin K, initW n (sz k)) = shapeDeg sz := by
  funext t
  rw [Finset.sum_apply]
  simp only [initW, shapeDeg, Finset.card_filter]

theorem bideterminantMem : BideterminantMem := by
  intro R _ r n K sz hsz I
  exact dualWeyl_of_eq
    (dualWeyl_prod Finset.univ (fun k => initW n (sz k))
      (fun k => initMinor R (I k) (hsz k))
      (fun k _ => initMinor_mem (I k) (hsz k)))
    (sum_initW_eq_shapeDeg sz)

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.CompDeg
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem componentDegree : CompDeg := by
  intro B _ r n l j ω s f hf
  rw [← lccomp_component_colAddGen]
  exact (lccomp_degreeOf_component_le _ _ _ _).trans hf

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_fin_filter_lt_eq_range {N : ℕ} (G : ℕ → ℕ) (k : ℕ) :
    ∑ a : Fin N with a.val < k, G a.val = ∑ i ∈ Finset.range (min N k), G i := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_eq_sum_range (fun i => if i < k then G i else 0) N).trans ?_
  show ∑ i ∈ Finset.range N, (if i < k then G i else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem rowNu_partial_sum {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (k : ℕ) :
    (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) = ∑ t : Fin n with t.val < k, ν t := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ, G = fun i => if h : i < n then ν ⟨i, h⟩ else 0 := ⟨_, rfl⟩
  have h1 : (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) =
      ∑ a : Fin r with a.val < k, G a.val :=
    Finset.sum_congr rfl fun a _ => by subst hG; rfl
  have h2 : (∑ t : Fin n with t.val < k, ν t) = ∑ t : Fin n with t.val < k, G t.val :=
    Finset.sum_congr rfl fun t _ => by subst hG; simp [t.isLt]
  rw [h1, h2, sum_fin_filter_lt_eq_range, sum_fin_filter_lt_eq_range]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    have hin : ¬ i < n := by omega
    rw [hG]
    simp [hin]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylIntRat
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem isWeightedHomogeneous_of_map_of_injective {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) {σ M : Type*} [AddCommMonoid M] {w : σ → M}
    {m : M} {f : MvPolynomial σ R} (hf : IsWeightedHomogeneous w (map φ f) m) :
    IsWeightedHomogeneous w f m := by
  intro d hd
  apply hf
  rw [MvPolynomial.coeff_map]
  intro h0
  exact hd (hφ (h0.trans (map_zero φ).symm))

theorem dualWeylModuleIntRat : DualWeylIntRat := by
  intro r n ν f
  have hφ : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  constructor
  · exact dualWeylModuleMap ℤ ℚ (Int.castRingHom ℚ) r n ν f
  · intro h
    rw [lsat_mem_dualWeyl] at h ⊢
    obtain ⟨hw, hc⟩ := h
    refine ⟨isWeightedHomogeneous_of_map_of_injective hφ hw, ?_⟩
    intro l j hlj
    apply MvPolynomial.map_injective (f := Int.castRingHom ℚ) hφ
    rw [lsat_map_colAddGen, MvPolynomial.map_rename]
    exact hc l j hlj

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.EvalDeg
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem evalDegree : EvalDeg := by
  intro B _ τ _ x y c _ _ _ p
  apply lcdeg_degreeOf_aeval_le
  intro m hm
  have hf : ∀ v, degreeOf c ((fun v : τ => if v = x then (1 : MvPolynomial τ B)
      else if v = y then -X c else X v) v) ≤ (if v = y then 1 else 0) + (if v = c then 1 else 0) := by
    intro v
    by_cases hvx : v = x
    · subst hvx
      simp only [if_true]
      have h1 : degreeOf c (1 : MvPolynomial τ B) = 0 := by rw [← C_1, degreeOf_C]
      rw [h1]
      exact Nat.zero_le _
    · by_cases hvy : v = y
      · subst hvy
        simp only [hvx, if_false, if_true, degreeOf_neg]
        have h2 := lcdeg_degreeOf_X_le (R := B) c c
        simp only [if_true] at h2
        omega
      · simp only [hvx, hvy, if_false, zero_add]
        exact lcdeg_degreeOf_X_le (R := B) c v
  refine le_trans (Finset.sum_le_sum (g := fun v => m v * (if v = y then 1 else 0) +
    m v * (if v = c then 1 else 0)) fun v _ => ?_) ?_
  · rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (hf v)
  · rw [Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hy := monomial_le_degreeOf y hm
    have hc := monomial_le_degreeOf c hm
    split_ifs <;> omega

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQBilin
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerRatBilinear : FockQBilin := fun _ f f' g c =>
  ⟨lfockq_add_left f f' g, lfockq_smul_left c f g⟩

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQPos
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerRatPos : FockQPos :=
  fun _ f g => ⟨lfockq_symm f g, fun hf => lfockq_self_pos f hf⟩

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
section
open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

def LFocks_rowMat {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ :=
  fun v w => if v.2 = w.2 then g v.1 w.1 else 0

lemma LFocks_rowAct_eq_sub {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    rowAct ℂ (n := n) g = sub (LFocks_rowMat g) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, sub, aeval_X, LFocks_rowMat]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single v.2]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

lemma LFocks_rowMat_conjTranspose {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    (LFocks_rowMat (n := n) g).conjTranspose = LFocks_rowMat g.conjTranspose := by
  ext v w
  simp only [Matrix.conjTranspose_apply, LFocks_rowMat]
  by_cases h : v.2 = w.2
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem fischerInnerRowActionAdjoint : FockRowAdj := by
  intro r n g f h
  rw [LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWInClosed
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem hwInClosed_of (h1 : HWLine) (h2 : RowDivClosedGraded) : HWInClosed := by
  intro r n hn ν hν M hMle hM hne
  obtain ⟨v, hvM, hv0, hkill⟩ := lhwin_exists_killed h2 M hM hne
  obtain ⟨c, hc⟩ := h1 ℚ r n hn ν hν v (hMle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℚ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e]
  exact M.smul_mem _ hvM

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelDecomp
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem peelDecomposition : PeelDecomp := by
  intro B _ r n l j hlj a0 ω g hg
  have key : ∀ m ∈ g.support, m (a0, l) + m (a0, j) = ω (a0, l) := by
    intro m hm
    have hw := hg (mem_support_iff.1 hm)
    have := lcpeel_weight_apply l j hlj m a0 l
    rw [hw] at this
    simpa using this.symm
  have hterm : ∀ k, X (a0, l) ^ k * X (a0, j) ^ (ω (a0, l) - k) * peel l j a0 k g =
      ∑ m ∈ g.support.filter (fun m => m (a0, l) = k), monomial m (AddMonoidAlgebra.coeff g m) := by
    intro k
    unfold peel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    have hkey := key m hm1
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul, one_mul, one_mul]
    refine congrArg (fun e => monomial e (AddMonoidAlgebra.coeff g m)) ?_
    ext ⟨b, t⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply, Prod.mk.injEq]
    rcases eq_or_ne b a0 with rfl | hb
    · rcases eq_or_ne t l with rfl | ht
      · simp only [hlj, hlj.symm, and_true, and_false, if_true, if_false]
        omega
      · rcases eq_or_ne t j with rfl | ht'
        · simp only [ht, Ne.symm ht, and_true, and_false, if_true, if_false]
          omega
        · simp [ht, ht', Ne.symm ht, Ne.symm ht']
    · simp [hb, Ne.symm hb]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hmaps : ∀ m ∈ g.support, (fun m : Fin r × Fin n →₀ ℕ => m (a0, l)) m ∈ Finset.range (ω (a0, l) + 1) := by
    intro m hm
    have := key m hm
    show m (a0, l) ∈ _
    rw [Finset.mem_range]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun m => monomial m (AddMonoidAlgebra.coeff g m))
  exact (hfib.trans (as_sum g).symm).symm

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelHomog
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcpeel_support {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (a0 : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) B) (d : Fin r × Fin n →₀ ℕ)
    (hd : AddMonoidAlgebra.coeff (peel l j a0 k g) d ≠ 0) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ d = (m.erase (a0, l)).erase (a0, j) := by
  unfold peel at hd
  rw [coeff_sum] at hd
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
  refine ⟨m, hm1, hm2, ?_⟩
  rw [coeff_monomial] at hne
  split_ifs at hne with h
  · exact h.symm
  · exact absurd rfl hne

private theorem weight_single_eq_nsmul {σ M : Type*} [AddCommMonoid M] (w : σ → M) (s : σ) (c : ℕ) :
    Finsupp.weight w (Finsupp.single s c) = c • w s := by
  first
    | (rw [Finsupp.weight_apply, Finsupp.sum_single_index]; exact zero_smul ℕ (w s))
    | simp [Finsupp.weight_apply]

private theorem eq_erase_erase_add_single_add_single {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m : Fin r × Fin n →₀ ℕ) :
    m = (m.erase (a0, l)).erase (a0, j) + Finsupp.single (a0, l) (m (a0, l)) +
      Finsupp.single (a0, j) (m (a0, j)) := by
  ext ⟨b, t⟩
  simp only [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply, Prod.mk.injEq]
  by_cases hb : b = a0
  · subst hb
    by_cases hl : t = l
    · subst hl
      simp [hlj, Ne.symm hlj]
    · by_cases hj : t = j
      · subst hj
        simp [hl, Ne.symm hl]
      · simp [hl, hj, Ne.symm hl, Ne.symm hj]
  · simp [hb, Ne.symm hb]

private theorem weight_pairW_apply_eq_zero_of_vanish {r n : ℕ} (l j : Fin n) (a0 : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (hl : d (a0, l) = 0) (hj : d (a0, j) = 0) :
    Finsupp.weight (pairW l j) d (a0, l) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  dsimp only
  have hi0 : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  obtain ⟨b, t⟩ := i
  by_cases ht : t = j
  · have hne : ¬ ((b, l) = (a0, l)) := by
      intro h
      simp only [Prod.mk.injEq] at h
      rw [h.1, ht] at hi0
      exact hi0 hj
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, l) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]
  · have hne : ¬ ((b, t) = (a0, l)) := by
      intro h
      rw [h] at hi0
      exact hi0 hl
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, t) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]

private theorem weight_pairW_eq_erase_of_split {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m d ω : Fin r × Fin n →₀ ℕ) (hdl : d (a0, l) = 0) (hdj : d (a0, j) = 0)
    (hsplit : m = d + Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (m (a0, j)))
    (hw : Finsupp.weight (pairW l j) m = ω) :
    Finsupp.weight (pairW l j) d = ω.erase (a0, l) := by
  have hpl : pairW (r := r) l j (a0, l) = Finsupp.single (a0, l) 1 := by
    simp [pairW, hlj]
  have hpj : pairW (r := r) l j (a0, j) = Finsupp.single (a0, l) 1 := by
    simp [pairW]
  have key : ω = Finsupp.weight (pairW l j) d +
      Finsupp.single (a0, l) (m (a0, l) + m (a0, j)) := by
    rw [← hw]
    conv_lhs => rw [hsplit]
    rw [map_add (f := _), map_add (f := _), weight_single_eq_nsmul, weight_single_eq_nsmul, hpl, hpj]
    first
      | (rw [add_assoc, ← add_smul, Finsupp.smul_single, smul_eq_mul, mul_one])
      | (ext y
         simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
         split_ifs <;> ring)
  ext x
  by_cases hx : x = (a0, l)
  · rw [hx, Finsupp.erase_same]
    exact weight_pairW_apply_eq_zero_of_vanish l j a0 d hdl hdj
  · rw [Finsupp.erase_ne hx, key, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hx),
      add_zero]

theorem sliceHomogeneous : PeelHomog := by
  intro B _ r n l j hlj a0 ω k g hg
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨m, hm, -, rfl⟩ := lcpeel_support l j a0 k g d hd
    exact weight_pairW_eq_erase_of_split l j hlj a0 m _ ω
      (by simp [Finsupp.erase_apply, hlj]) (by simp [Finsupp.erase_apply])
      (eq_erase_erase_add_single_add_single l j hlj a0 m) (hg (mem_support_iff.mp hm))
  · intro d hd
    obtain ⟨m, -, -, rfl⟩ :=
      lcpeel_support l j a0 k g d (mem_support_iff.mp hd)
    exact ⟨by simp [Finsupp.erase_apply, hlj], by simp [Finsupp.erase_apply]⟩

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivClosedGraded
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_divided_closed_graded : RowDivClosedGraded := by
  intro r n M hM f hf μ
  obtain ⟨h, hhM, hh⟩ := lgraded_multi M hM μ Finset.univ f hf
  convert hhM using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hh]
  congr 1
  apply propext
  constructor
  · intro hm a _
    rw [← lgraded_weight_rowW, hm]
  · intro hm
    funext a
    rw [lgraded_weight_rowW]
    exact hm a (Finset.mem_univ a)

end Formalism.GradedWeylDivisibility
end
end

