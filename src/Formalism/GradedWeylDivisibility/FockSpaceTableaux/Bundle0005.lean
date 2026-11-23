module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001
public import Formalism.GradedWeylDivisibility.Bundle0001

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def initW (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

theorem sum_single_castLE {n s : ℕ} (hs : s ≤ n) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hs q) 1 : Fin n → ℕ)) = initW n s := by
  funext t
  rw [Finset.sum_apply]
  simp only [initW]
  by_cases h : t.val < s
  · rw [if_pos h, Finset.sum_eq_single ⟨t.val, h⟩]
    · have e : Fin.castLE hs ⟨t.val, h⟩ = t := Fin.ext rfl
      rw [e, Pi.single_eq_same]
    · intro q _ hq
      rw [Pi.single_apply, if_neg]
      intro htq
      apply hq
      subst htq
      exact Fin.ext rfl
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Pi.single_apply, if_neg]
    intro htq
    apply h
    subst htq
    exact q.isLt

theorem initMinor_isWeightedHomogeneous {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (colW r n) (initMinor R I hs) (initW n s) := by
  rw [← mem_weightedHomogeneousSubmodule]
  unfold initMinor
  rw [Matrix.det_apply]
  refine _root_.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← sum_single_castLE hs]
  apply IsWeightedHomogeneous.prod
  intro q _
  exact isWeightedHomogeneous_X (R := R) (colW r n) (I (σ q), Fin.castLE hs q)

theorem algHom_det_of {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) {s : ℕ} (M : Fin s → Fin s → A) :
    φ (Matrix.of M).det = (Matrix.of fun p q => φ (M p q)).det := by
  rw [AlgHom.map_det]
  rfl

theorem colAddGen_X {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    colAddGen R l j (X v) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by
  simp only [colAddGen, aeval_X]

theorem initMinor_invariant {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) (l j : Fin n) (hlj : l < j) :
    colAddGen R l j (initMinor R I hs) = rename some (initMinor R I hs) := by
  unfold initMinor
  rw [algHom_det_of, algHom_det_of]
  simp only [colAddGen_X, rename_X]
  by_cases hj : j.val < s
  · have hl : l.val < s := Nat.lt_trans (show l.val < j.val from hlj) hj
    have hjl : (⟨j.val, hj⟩ : Fin s) ≠ ⟨l.val, hl⟩ := by
      intro h
      exact hlj.ne' (Fin.ext (Fin.mk.inj_iff.mp h))
    rw [← Matrix.det_updateCol_add_smul_self
      (Matrix.of fun p q : Fin s =>
        (X (some (I p, Fin.castLE hs q)) : MvPolynomial (Option (Fin r × Fin n)) R)) hjl (X none)]
    congr 1
    ext p q
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    by_cases hq : q = ⟨j.val, hj⟩
    · subst hq
      have e1 : Fin.castLE hs ⟨j.val, hj⟩ = j := Fin.ext rfl
      have e2 : Fin.castLE hs ⟨l.val, hl⟩ = l := Fin.ext rfl
      rw [e1, e2]
      simp
    · have hne : Fin.castLE hs q ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        exact hq (Fin.ext hv)
      rw [if_neg hne, if_neg hq]
  · congr 1
    ext p q
    simp only [Matrix.of_apply]
    have hne : Fin.castLE hs q ≠ j := by
      intro h
      apply hj
      rw [← h]
      exact q.isLt
    rw [if_neg hne]

theorem initMinor_mem {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (initW n s) := by
  unfold dualWeyl
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact initMinor_isWeightedHomogeneous I hs
  · simp only [Submodule.mem_iInf]
    intro l j hlj
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact initMinor_invariant I hs l j hlj

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCcompLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lccompW {r n : ℕ} (l j : Fin n) : Option (Fin r × Fin n) → (Fin r × Fin n →₀ ℕ) :=
  fun o => match o with
    | none => 0
    | some v => pairW l j v

theorem lccomp_pairW_col {r n : ℕ} (l j : Fin n) (b : Fin r) :
    pairW (r := r) l j (b, l) = Finsupp.single (b, l) 1 := by
  unfold pairW
  split_ifs <;> rfl

theorem lccomp_image_var_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    IsWeightedHomogeneous (lccompW l j)
      ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) (pairW l j v) := by
  split_ifs with h
  · refine IsWeightedHomogeneous.add (isWeightedHomogeneous_X B (lccompW l j) (some v)) ?_
    have hm := (isWeightedHomogeneous_X B (lccompW l j) none).mul
      (isWeightedHomogeneous_X B (lccompW l j) (some (v.1, l)))
    convert hm using 1
    show pairW l j v = 0 + pairW l j (v.1, l)
    rw [lccomp_pairW_col, zero_add]
    simp only [pairW, if_pos h]
  · exact isWeightedHomogeneous_X B (lccompW l j) (some v)

theorem lccomp_colAddGen_monomial_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (a : B) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j (monomial d a))
      (Finsupp.weight (pairW l j) d) := by
  classical
  have hp : IsWeightedHomogeneous (lccompW l j)
      (∏ v ∈ d.support, ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) ^ d v)
      (∑ v ∈ d.support, d v • pairW l j v) :=
    IsWeightedHomogeneous.prod _ _ _ fun v _ => (lccomp_image_var_homog l j v).pow _
  have hc : IsWeightedHomogeneous (lccompW l j) (C a : MvPolynomial (Option (Fin r × Fin n)) B) 0 :=
    isWeightedHomogeneous_C _ a
  have h := hc.mul hp
  rw [zero_add] at h
  rw [colAddGen, aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.weight_apply]
  exact h

theorem lccomp_colAddGen_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B)
    (hf : IsWeightedHomogeneous (pairW l j) f ω) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j f) ω := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have h := lccomp_colAddGen_monomial_homog (B := B) l j d (AddMonoidAlgebra.coeff f d)
  rwa [hf (mem_support_iff.mp hd)] at h

theorem lccomp_sum_components {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : σ → M) (f : MvPolynomial σ R) (T : Finset M)
    (hT : ∀ d ∈ f.support, Finsupp.weight w d ∈ T) :
    f = ∑ ω' ∈ T, weightedHomogeneousComponent w ω' f := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hT d (mem_support_iff.mpr hne))

private lemma weightedHomogeneousComponent_self_of_isWH_ring {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hne
    exact hd (h (Ne.symm hne))

private lemma weightedHomogeneousComponent_eq_zero_of_ne_isWH {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m n : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) (hn : n ≠ m) :
    weightedHomogeneousComponent w n p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with hd
  · by_contra hne
    exact hn (hd.symm.trans (h hne))
  · rfl

theorem lccomp_component_colAddGen {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B) :
    weightedHomogeneousComponent (lccompW l j) ω (colAddGen B l j f) =
      colAddGen B l j (weightedHomogeneousComponent (pairW l j) ω f) := by
  classical
  have hf := lccomp_sum_components (pairW l j) f (f.support.image (Finsupp.weight (pairW l j)))
    (fun d hd => Finset.mem_image_of_mem _ hd)
  conv_lhs => rw [hf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  by_cases hω : ω ∈ f.support.image (Finsupp.weight (pairW l j))
  · rw [Finset.sum_eq_single ω]
    · exact weightedHomogeneousComponent_self_of_isWH_ring
        (lccomp_colAddGen_homog l j ω _ (weightedHomogeneousComponent_isWeightedHomogeneous ω f))
    · intro b _ hb
      exact weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f))
        (Ne.symm hb)
    · intro h
      exact absurd hω h
  · rw [Finset.sum_eq_zero]
    · have h0 : weightedHomogeneousComponent (pairW l j) ω f = 0 := by
        ext d
        rw [coeff_weightedHomogeneousComponent]
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        split_ifs with h
        · by_contra hne
          exact hω (h ▸ Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
        · rfl
      rw [h0, map_zero]
    · intro b hb
      refine weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f)) ?_
      rintro rfl
      exact hω hb

theorem lccomp_degreeOf_component_le {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M]
    (w : σ → M) (ω : M) (p : MvPolynomial σ R) (i : σ) :
    degreeOf i (weightedHomogeneousComponent w ω p) ≤ degreeOf i p := by
  classical
  rw [degreeOf_le_iff]
  intro m hm
  apply monomial_le_degreeOf i
  rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact mem_support_iff.mpr hm
  · exact absurd rfl hm

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCpleadLemmas
section
open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

private lemma pairW_apply {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) (b : Fin r)
    (t : Fin n) :
    pairW l j v (b, t) = if v.2 = j then (if (v.1, l) = (b, t) then 1 else 0)
      else (if v = (b, t) then 1 else 0) := by
  classical
  unfold pairW
  split_ifs <;> simp_all [Finsupp.single_apply]

theorem lcplead_weight_apply {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ)
    (b : Fin r) (t : Fin n) :
    Finsupp.weight (pairW l j) d (b, t) =
      if t = l then d (b, l) + d (b, j) else if t = j then 0 else d (b, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, pairW_apply, smul_eq_mul]
  split_ifs with h1 h2
  · subst h1
    rw [Fintype.sum_eq_add (b, t) (b, j) (by simp [hlj])]
    · simp [hlj]
    · rintro ⟨a, s⟩ ⟨ha1, ha2⟩
      by_cases hs : s = j <;> simp_all [Prod.ext_iff]
  · subst h2
    refine Finset.sum_eq_zero fun x _ => ?_
    obtain ⟨a, s⟩ := x
    by_cases hs : s = t <;> simp_all [Prod.ext_iff]
  · rw [Fintype.sum_eq_single (b, t)]
    · simp [h2]
    · rintro ⟨a, s⟩ hx
      have h1' : l ≠ t := Ne.symm h1
      by_cases hs : s = j <;> simp_all [Prod.ext_iff]

section
variable {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n}

theorem lcplead_hom_row (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) : m (b, l) + m (b, j) = ω (b, l) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b l, if_pos rfl]

theorem lcplead_hom_off (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) (t : Fin n) (htl : t ≠ l) (htj : t ≠ j) : m (b, t) = ω (b, t) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b t, if_neg htl, if_neg htj]

private lemma support_eq_of_pairW_homogeneous_of_erase_eq (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m m' : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (hm' : m' ∈ g.support) (h1 : m' (a0, l) = m (a0, l))
    (h2 : (m'.erase (a0, l)).erase (a0, j) = (m.erase (a0, l)).erase (a0, j)) : m' = m := by
  ext v
  by_cases hv1 : v = (a0, l)
  · rw [hv1, h1]
  by_cases hv2 : v = (a0, j)
  · have e1 := lcplead_hom_row hlj hg hm a0
    have e2 := lcplead_hom_row hlj hg hm' a0
    rw [hv2]; omega
  have := congrArg (fun f => f v) h2
  simpa [Finsupp.erase_ne hv1, Finsupp.erase_ne hv2] using this

theorem lcplead_coeff_peel (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    AddMonoidAlgebra.coeff (peel l j a0 (m (a0, l)) g) ((m.erase (a0, l)).erase (a0, j)) = AddMonoidAlgebra.coeff g m := by
  classical
  unfold peel
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' hm' hne
    rw [Finset.mem_filter] at hm'
    rw [if_neg]
    intro heq
    exact hne (support_eq_of_pairW_homogeneous_of_erase_eq hlj a0 hg hm hm'.1 hm'.2 heq)
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hm, rfl⟩)).elim

theorem lcplead_mem_support_peel (a0 : Fin r) (k : ℕ) {g : MvPolynomial (Fin r × Fin n) B}
    {p : Fin r × Fin n →₀ ℕ} (hp : p ∈ (peel l j a0 k g).support) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ p = (m.erase (a0, l)).erase (a0, j) := by
  classical
  unfold peel at hp
  obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hp)
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, hm.2, Finset.mem_singleton.mp (support_monomial_subset hpm)⟩

theorem lcplead_recon (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    m = Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (ω (a0, l) - m (a0, l)) +
      (m.erase (a0, l)).erase (a0, j) := by
  have h := lcplead_hom_row hlj hg hm a0
  have hne : ((a0, l) : Fin r × Fin n) ≠ (a0, j) := by simp [hlj]
  ext v
  simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply]
  by_cases h1 : v = (a0, l)
  · subst h1; simp [hne, Ne.symm hlj]
  · by_cases h2 : v = (a0, j)
    · subst h2; simp [hne]; omega
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

end

theorem lcplead_cmIdx_val {r n : ℕ} (b : Fin r) (t : Fin n) :
    ((cmIdx r n (b, t) : Fin (n * r)) : ℕ) = b + r * t := by
  simp [cmIdx, finProdFinEquiv]

theorem lcplead_cmIdx_lt {r n : ℕ} {b a0 : Fin r} {t l : Fin n}
    (h : cmIdx r n (b, t) < cmIdx r n (a0, l)) : t < l ∨ (t = l ∧ b < a0) := by
  have h' : (b : ℕ) + r * t < a0 + r * l := by
    have := Fin.lt_def.mp h
    rwa [lcplead_cmIdx_val, lcplead_cmIdx_val] at this
  rcases lt_trichotomy (t : ℕ) l with h1 | h1 | h1
  · exact Or.inl (Fin.lt_def.mpr h1)
  · refine Or.inr ⟨Fin.ext h1, Fin.lt_def.mpr ?_⟩
    rw [h1] at h'
    exact Nat.lt_of_add_lt_add_right h'
  · exfalso
    have h2 := Nat.mul_le_mul_left r (show (l : ℕ) + 1 ≤ t from h1)
    have h3 := a0.isLt
    rw [Nat.mul_add, mul_one] at h2
    omega

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCssytLemmas
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcssyt_shapeDeg_cons {n K : ℕ} (h : ℕ) (sz : Fin K → ℕ) (t : Fin n) :
    shapeDeg (Fin.cons h sz : Fin (K + 1) → ℕ) t = (if t.val < h then 1 else 0) + shapeDeg sz t := by
  unfold shapeDeg
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem lcssyt_consSz {n K h : ℕ} (hh : h ≤ n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) :
    ∀ k : Fin (K + 1), (Fin.cons h sz : Fin (K + 1) → ℕ) k ≤ n := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using hh
  · simpa using hsz i

def lcssyt_consI {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r) :
    ∀ k : Fin (K + 1), Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r :=
  fun k => Fin.cases (motive := fun k => Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r) c I k

theorem lcssyt_bidetExp_cons {r n K h : ℕ} (hh : h ≤ n) (c : Fin h → Fin r) (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    bidetExp (Fin.cons h sz : Fin (K + 1) → ℕ) (lcssyt_consSz hh sz hsz) (lcssyt_consI sz c I) =
      colExp c hh + bidetExp sz hsz I := by
  unfold bidetExp
  rw [Fin.sum_univ_succ]
  rfl

theorem lcssyt_consI_strictMono {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r)
    (hc : StrictMono c) (hI : ∀ k, StrictMono (I k)) : ∀ k, StrictMono (lcssyt_consI sz c I k) := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · exact hc
  · exact hI i

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadComp
section
open MvPolynomial

open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem leadingComponent : LeadComp := by
  intro R _ r n M _ w f
  classical
  by_cases hf : f = 0
  · subst hf; simp
  have hd : (colLex r n).degree f ∈
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f).support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact (colLex r n).coeff_degree_ne_zero_iff.mpr hf
  have hg0 : weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  have h1 := (colLex r n).le_degree hd
  have h2 : (colLex r n).toSyn ((colLex r n).degree
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f)) ≤
      (colLex r n).toSyn ((colLex r n).degree f) := by
    apply (colLex r n).le_degree
    have h3 := (colLex r n).degree_mem_support hg0
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at h3
    split_ifs at h3 with h
    · exact mem_support_iff.mpr h3
    · exact absurd rfl h3
  exact (colLex r n).toSyn.injective (le_antisymm h2 h1)

end Formalism.GradedWeylDivisibility
end
end

