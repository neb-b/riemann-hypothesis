module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveCountA
section
namespace Formalism.L2.Pj.CurveCount

open MvPolynomial

theorem eval₂_mul_homog {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (c : S) (g : σ → S)
    {P : MvPolynomial σ R} {k : ℕ} (hP : P.IsHomogeneous k) :
    P.eval₂ f (fun i => c * g i) = c ^ k * P.eval₂ f g := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = k := by
    have h := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem aeval_div_homog {K L σ : Type*} [Field K] [Field L] [Algebra K L] (g : σ → L) (c : L)
    {P : MvPolynomial σ K} {k : ℕ} (hP : P.IsHomogeneous k) :
    aeval (fun i => g i / c) P = c⁻¹ ^ k * aeval g P := by
  have h := eval₂_mul_homog (algebraMap K L) c⁻¹ g hP
  show MvPolynomial.eval₂ (algebraMap K L) (fun i => g i / c) P =
    c⁻¹ ^ k * MvPolynomial.eval₂ (algebraMap K L) g P
  rw [← h]
  congr 1
  funext i
  rw [div_eq_mul_inv, mul_comm]

theorem exists_indep_ratios {K κ : Type*} [Field K] [Field κ] [Algebra K κ] {N D : ℕ} (x : Fin N → κ) (a : Fin N)
    (hxa : x a ≠ 0) (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1) :
    ∃ s : Finset κ, s.card = D ∧ (↑s : Set κ) ⊆ Set.range (fun i => x i / x a) ∧
      AlgebraicIndepOn K id (↑s : Set κ) := by
  classical
  have : FaithfulSMul K κ := (faithfulSMul_iff_algebraMap_injective K κ).mpr (algebraMap K κ).injective
  set r : Fin N → κ := fun i => x i / x a with hr
  let t2 : Fin (D + 1) × ↥(Finset.univ.erase a) → κ := fun p => t (p.1, p.2.1)
  set T2 : Set κ := insert (x a)⁻¹ (Set.range t2) with hT2
  set S : Set κ := Set.range r ∪ T2 with hS
  have hc : ∀ i : Fin (D + 1), ∑ k, t (i, k) * x k = if i = 0 then 1 else 0 := by
    intro i
    cases i using Fin.cases with
    | zero => simpa using hlin0
    | succ i => simpa [Fin.succ_ne_zero] using hlin i
  have hrS : ∀ k, r k ∈ Algebra.adjoin K S := fun k => Algebra.subset_adjoin (Or.inl ⟨k, rfl⟩)
  have hzS : (x a)⁻¹ ∈ Algebra.adjoin K S := Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))
  have htS : ∀ i k, k ≠ a → t (i, k) ∈ Algebra.adjoin K S := fun i k hk =>
    Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _
      ⟨(i, ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩⟩), rfl⟩))
  have hmem : ∀ p, t p ∈ Algebra.adjoin K S := by
    rintro ⟨i, k⟩
    by_cases hk : k = a
    · rw [hk]
      have e : t (i, a) = (if i = 0 then 1 else 0) * (x a)⁻¹ - ∑ l ∈ Finset.univ.erase a, t (i, l) * r l := by
        have h := hc i
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h
        rw [← h, add_mul, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
        simp only [hr, div_eq_mul_inv, mul_assoc, sub_self, Finset.sum_const_zero, add_zero,
          mul_inv_cancel₀ hxa, mul_one]
      rw [e]
      refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ?_ hzS)
        (Subalgebra.sum_mem _ fun l hl => Subalgebra.mul_mem _ (htS i l (Finset.ne_of_mem_erase hl)) (hrS l))
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · exact htS i k hk
  let M := AlgebraicIndependent.matroid K κ
  have hI : M.Indep (Set.range t) := AlgebraicIndependent.matroid_indep_iff.mpr ht.to_subtype_range
  have hIS : Set.range t ⊆ M.closure S := by
    rintro _ ⟨p, rfl⟩
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact isAlgebraic_algebraMap (⟨t p, hmem p⟩ : Algebra.adjoin K S)
  have h1 := hI.encard_le_eRk_of_subset hIS
  rw [M.eRk_closure_eq] at h1
  have h2 := M.eRk_union_le_eRk_add_eRk (Set.range r) T2
  have h3 : M.eRk T2 ≤ ((D + 1) * (N - 1) + 1 : ℕ) := by
    refine (M.eRk_le_encard T2).trans ((Set.encard_insert_le _ _).trans ?_)
    have h4 : (Set.range t2).encard ≤ ((D + 1) * (N - 1) : ℕ) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add h4 le_rfl
  have h5 : (((D + 1) * N : ℕ) : ℕ∞) ≤ (Set.range t).encard := by
    have := ht.injective.encard_range
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    exact this.ge
  have hfin : M.eRk (Set.range r) ≠ ⊤ :=
    ne_top_of_le_ne_top (Set.finite_range r).encard_lt_top.ne (M.eRk_le_encard _)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hineq : (D + 1) * N ≤ n + ((D + 1) * (N - 1) + 1) := by
    have := h5.trans (h1.trans (h2.trans (add_le_add le_rfl h3)))
    rw [← hn, ← Nat.cast_add, Nat.cast_le] at this
    exact this
  have hN : (D + 1) * N = (D + 1) * (N - 1) + (D + 1) := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by have := a.2; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hDn : D ≤ n := by
    rw [hN] at hineq
    generalize (D + 1) * (N - 1) = X at hineq
    omega
  obtain ⟨B, hB⟩ := M.exists_isBasis (Set.range r) (Set.subset_univ _)
  have hDB : ((D : ℕ) : ℕ∞) ≤ B.encard := by
    rw [hB.encard_eq_eRk, ← hn]
    exact_mod_cast hDn
  obtain ⟨B', hB'sub, hB'card⟩ := Set.exists_subset_encard_eq hDB
  have hB'fin : B'.Finite := Set.finite_of_encard_eq_coe hB'card
  refine ⟨hB'fin.toFinset, ?_, ?_, ?_⟩
  · have := Set.encard_coe_eq_coe_finsetCard hB'fin.toFinset
    rw [Set.Finite.coe_toFinset, hB'card] at this
    exact_mod_cast this.symm
  · rw [Set.Finite.coe_toFinset]
    exact hB'sub.trans hB.subset
  · rw [Set.Finite.coe_toFinset]
    exact AlgebraicIndependent.matroid_indep_iff.mp (hB.indep.subset hB'sub)

theorem countCore {K κ Ω : Type*} [Field K] [Field κ] [Field Ω] [Algebra K κ] [Algebra K Ω] {N D : ℕ}
    (v : Fin N → Ω) (x : Fin N → κ) (a : Fin N) (hva : v a ≠ 0) (hxa : x a ≠ 0)
    (htr : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun i => v i / v a)) ≤ D)
    (htrans : ∀ Q : MvPolynomial (Fin N) K, aeval (fun i => v i / v a) Q = 0 → aeval (fun i => x i / x a) Q = 0)
    (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1)
    (P : MvPolynomial (Fin N) K) {k : ℕ} (hP : P.IsHomogeneous k) (hPv : aeval v P ≠ 0) :
    aeval x P ≠ 0 := by
  classical
  intro hxP
  set ρ : Fin N → Ω := fun i => v i / v a with hρ
  set σ : Fin N → κ := fun i => x i / x a with hσ
  have hα0 : aeval ρ P ≠ 0 := by
    rw [hρ, aeval_div_homog v (v a) hP]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hva)) hPv
  have hσP : aeval σ P = 0 := by
    rw [hσ, aeval_div_homog x (x a) hP, hxP, mul_zero]
  obtain ⟨s, hscard, hsub, hind⟩ := exists_indep_ratios (K := K) x a hxa t ht hlin hlin0
  have hf : ∀ e : s, ∃ i, σ i = (e : κ) := fun e => hsub e.2
  choose f hfe using hf
  have hy : AlgebraicIndependent K (fun e : s => (e : κ)) := hind
  have h3 : (σ ∘ f) = fun e : s => (e : κ) := funext hfe
  have huind : AlgebraicIndependent K (ρ ∘ f) := by
    rw [algebraicIndependent_iff]
    intro Q hQ
    have h1 : aeval ρ (rename f Q) = 0 := by rw [aeval_rename]; exact hQ
    have h2 := htrans (rename f Q) h1
    rw [aeval_rename, h3] at h2
    exact (algebraicIndependent_iff.mp hy) Q h2
  have hρA : ∀ i, ρ i ∈ IntermediateField.adjoin K (Set.range ρ) :=
    fun i => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  let ρA : Fin N → IntermediateField.adjoin K (Set.range ρ) := fun i => ⟨ρ i, hρA i⟩
  have hvalρ : ∀ Q : MvPolynomial (Fin N) K,
      IntermediateField.val _ (aeval ρA Q) = aeval ρ Q := by
    intro Q
    induction Q using MvPolynomial.induction_on
    next c =>
      simp only [MvPolynomial.aeval_C, AlgHom.commutes]
    next p q hp hq =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    next p i hp =>
      rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      rfl
  have hnot : ¬ AlgebraicIndependent K (fun o : Option s => o.elim (aeval ρ P) (ρ ∘ f)) := by
    intro hI
    let w : Option s → IntermediateField.adjoin K (Set.range ρ) :=
      fun o => o.elim (aeval ρA P) (fun e => ρA (f e))
    have hcomp : (IntermediateField.val _) ∘ w = fun o : Option s => o.elim (aeval ρ P) (ρ ∘ f) := by
      funext o
      cases o with
      | none => exact hvalρ P
      | some e => rfl
    have hw : AlgebraicIndependent K w := by
      apply AlgebraicIndependent.of_comp (IntermediateField.val _)
      rw [hcomp]
      exact hI
    have hcard := hw.lift_cardinalMk_le_trdeg.trans (Cardinal.lift_le.mpr htr)
    simp [Cardinal.mk_fintype, Fintype.card_option, hscard] at hcard
  have halg : IsAlgebraic (Algebra.adjoin K (Set.range (ρ ∘ f))) (aeval ρ P) := by
    by_contra hna
    exact hnot ((huind.option_iff_transcendental _).mpr hna)
  set α := aeval ρ P with hαdef
  have hex : ∃ n, ∃ p : Polynomial (Algebra.adjoin K (Set.range (ρ ∘ f))),
      p ≠ 0 ∧ Polynomial.aeval α p = 0 ∧ p.natDegree = n := by
    obtain ⟨p, hp0, hp⟩ := halg
    exact ⟨_, p, hp0, hp, rfl⟩
  obtain ⟨p, hp0, hpα, hpn⟩ := Nat.find_spec hex
  have hc0 : p.coeff 0 ≠ 0 := by
    intro hc
    have hdec : Polynomial.X * p.divX = p := by
      have h0 := Polynomial.X_mul_divX_add p
      rw [hc, map_zero, add_zero] at h0
      exact h0
    have hd0 : p.divX ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdec
      exact hp0 hdec.symm
    have hdα : Polynomial.aeval α p.divX = 0 := by
      have h1 : Polynomial.aeval α p = α * Polynomial.aeval α p.divX := by
        conv_lhs => rw [← hdec]
        rw [map_mul, Polynomial.aeval_X]
      rw [hpα] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hα0
    have hdeg : p.divX.natDegree < p.natDegree := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      have hn0 : p.natDegree ≠ 0 := by
        intro h0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero] at hp0
        exact hp0 rfl
      omega
    exact Nat.find_min hex (hpn ▸ hdeg) ⟨p.divX, hd0, hdα, rfl⟩
  have hQ : ∀ c : Algebra.adjoin K (Set.range (ρ ∘ f)), ∃ Q : MvPolynomial s K,
      aeval (ρ ∘ f) Q = (c : Ω) := by
    intro c
    have hc : (c : Ω) ∈ (MvPolynomial.aeval (R := K) (ρ ∘ f)).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨Q, hQ⟩ := hc
    exact ⟨Q, hQ⟩
  choose Qc hQc using hQ
  have hT : aeval ρ (∑ j ∈ Finset.range (p.natDegree + 1), rename f (Qc (p.coeff j)) * P ^ j) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, map_pow, aeval_rename, hQc]
    rw [← hpα, Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  have hT2 := htrans _ hT
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_range_succ'] at hT2
  simp only [map_mul, map_pow, aeval_rename, hσP, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, mul_one] at hT2
  rw [h3] at hT2
  have h4 := (algebraicIndependent_iff.mp hy) _ hT2
  have h5 := hQc (p.coeff 0)
  rw [h4, map_zero] at h5
  apply hc0
  apply Subtype.ext
  simpa using h5.symm

end Formalism.L2.Pj.CurveCount
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
section
noncomputable section

namespace Formalism.L2.Pj

section Graded

variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)

def incG (w : W) : C w →ₗ[K] AddMonoidAlgebra R M where
  toFun F := AddMonoidAlgebra.single (key w) (F : R)
  map_add' F F' := by simp [AddMonoidAlgebra.single_add]
  map_smul' a F := by simp [AddMonoidAlgebra.smul_single]

theorem incG_apply (w : W) (F : C w) : incG key C w F = AddMonoidAlgebra.single (key w) (F : R) := rfl

def cfG (K : Type) [Field K] [Algebra K R] (m : M) : AddMonoidAlgebra R M →ₗ[K] R where
  toFun x := x.coeff m
  map_add' x y := by simp
  map_smul' a x := by simp

open Classical in
theorem coeff_incG (m : M) (w : W) (F : C w) :
    (incG key C w F).coeff m = if key w = m then (F : R) else 0 := by
  rw [incG_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem incG_inj (w : W) : Function.Injective (incG key C w) := fun F F' h => by
  have h1 := congrArg (fun x : AddMonoidAlgebra R M => x.coeff (key w)) h
  simp only [coeff_incG, if_true] at h1
  exact Subtype.ext h1

theorem incG_indep (hkey : Function.Injective key) :
    iSupIndep fun w : W => LinearMap.range (incG key C w) := by
  intro w
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨F, rfl⟩ := LinearMap.mem_range.mp hx
  have hle : (⨆ (u) (_ : u ≠ w), LinearMap.range (incG key C u)) ≤ LinearMap.ker (cfG K (key w)) := by
    refine iSup₂_le fun u hu => ?_
    rintro _ ⟨G', rfl⟩
    rw [LinearMap.mem_ker]
    change (incG key C u G').coeff (key w) = 0
    rw [coeff_incG, if_neg (fun h => hu (hkey h))]
  have h0 : (incG key C w F).coeff (key w) = 0 := hle hx'
  rw [coeff_incG, if_pos rfl] at h0
  rw [show F = 0 from Subtype.ext h0, map_zero]

theorem incG_mul {w w' u : W} (hu : key u = key w + key w') (F : C w) (F' : C w')
    (h : (F : R) * (F' : R) ∈ C u) : incG key C w F * incG key C w' F' = incG key C u ⟨_, h⟩ := by
  rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, hu]

def vG (v : R → EReal) (x : AddMonoidAlgebra R M) : EReal := ⨅ m, v (x.coeff m)

variable {v : R → EReal}

theorem vG_zero (h0 : v 0 = ⊤) : vG v (0 : AddMonoidAlgebra R M) = ⊤ := by simp [vG, h0]

theorem vG_single (h0 : v 0 = ⊤) (m : M) (r : R) : vG v (AddMonoidAlgebra.single m r) = v r := by
  classical
  apply le_antisymm
  · exact (iInf_le _ m).trans (by rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same])
  · refine le_iInf fun u => ?_
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact le_rfl
    · rw [h0]; exact le_top

theorem vG_incG (h0 : v 0 = ⊤) (w : W) (F : C w) : vG v (incG key C w F) = v F := vG_single h0 _ _

theorem vG_add (ha : ∀ r s, min (v r) (v s) ≤ v (r + s)) (x y : AddMonoidAlgebra R M) :
    min (vG v x) (vG v y) ≤ vG v (x + y) := by
  refine le_iInf fun m => ?_
  have : (x + y).coeff m = x.coeff m + y.coeff m := by simp
  rw [this]
  exact (min_le_min (iInf_le _ m) (iInf_le _ m)).trans (ha _ _)

theorem ereal_add_iInf {ι : Type} (c : ℝ) (f : ι → EReal) :
    (c : EReal) + ⨅ i, f i = ⨅ i, ((c : EReal) + f i) := by
  have hc : ∀ x : EReal, ((-c : ℝ) : EReal) + ((c : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  have hc' : ∀ x : EReal, (c : EReal) + (((-c : ℝ) : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  apply le_antisymm
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le f i)
  · have h1 : ((-c : ℝ) : EReal) + ⨅ i, ((c : EReal) + f i) ≤ ⨅ i, f i :=
      le_iInf fun i => (add_le_add le_rfl (iInf_le (fun i => (c : EReal) + f i) i)).trans (hc (f i)).le
    have h2 := add_le_add (le_refl (c : EReal)) h1
    rwa [hc'] at h2

theorem vG_smul {a : K} {t : ℝ} (hs : ∀ r, v (a • r) = (t : EReal) + v r) (x : AddMonoidAlgebra R M) :
    vG v (a • x) = (t : EReal) + vG v x := by
  unfold vG
  rw [ereal_add_iInf]
  refine iInf_congr fun m => ?_
  have : (a • x).coeff m = a • x.coeff m := by simp
  rw [this, hs]

theorem vG_ne_bot (h0 : v 0 = ⊤) (hb : ∀ r, v r ≠ ⊥) (x : AddMonoidAlgebra R M) : vG v x ≠ ⊥ := by
  classical
  have hT : x.coeff.support.inf (fun m => v (x.coeff m)) ≤ vG v x := by
    refine le_iInf fun m => ?_
    by_cases hm : m ∈ x.coeff.support
    · exact Finset.inf_le hm
    · rw [Finsupp.notMem_support_iff.mp hm, h0]; exact le_top
  have hne : x.coeff.support.inf (fun m => v (x.coeff m)) ≠ ⊥ := by
    rw [Ne, Finset.inf_eq_bot_iff]; push Not
    exact fun m _ => hb _
  intro h
  exact hne (le_bot_iff.mp (h ▸ hT))

theorem vG_mul (h0 : v 0 = ⊤) (hm : ∀ r s, v (r * s) = v r + v s) (w w' : W) (F : C w) (F' : C w') :
    vG v (incG key C w F * incG key C w' F') = vG v (incG key C w F) + vG v (incG key C w' F') := by
  rw [incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, vG_single h0, vG_single h0, vG_single h0, hm]

end Graded

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPfB
section
namespace Formalism.L2.Pj.TranscendenceDegreeLemmas

open AlgebraicGeometry CategoryTheory

theorem primeIdealOf_mem_minimalPrimes {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : hZ.1.genericPoint ∈ V) :
    (hV.primeIdealOf ⟨_, hx⟩).asIdeal ∈ minimalPrimes Γ(X, V) := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZ.1.genericPoint Z := by
    have := hZ.1.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  refine ⟨⟨(hV.primeIdealOf ⟨_, hx⟩).isPrime, bot_le⟩, fun q hq hle => ?_⟩
  let y : PrimeSpectrum Γ(X, V) := ⟨q, hq.1⟩
  have hsp : y ⤳ hV.primeIdealOf ⟨_, hx⟩ := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  have hsp' : hV.fromSpec y ⤳ hZ.1.genericPoint := by
    have := hsp.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  have hirr : IsIrreducible (closure {hV.fromSpec y}) := isIrreducible_singleton.closure
  have hZle : Z ⊆ closure {hV.fromSpec y} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp')) isClosed_closure
  have heq : closure {hV.fromSpec y} = Z := (hZ.2 hirr hZle).antisymm hZle
  have hmem : hV.fromSpec y ∈ Z := heq ▸ subset_closure rfl
  have hxy : hV.fromSpec y = hZ.1.genericPoint := (hsp'.antisymm (hgen.specializes hmem)).eq
  have hy : y = hV.primeIdealOf ⟨_, hx⟩ :=
    hV.fromSpec.isOpenEmbedding.injective (hxy.trans (hV.fromSpec_primeIdealOf ⟨_, hx⟩).symm)
  have := congrArg PrimeSpectrum.asIdeal hy
  exact le_of_eq this.symm

theorem fg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    (⊤ : IntermediateField K (X.residueField hZ.1.genericPoint)).FG := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hfx : f hZ.1.genericPoint ∈ U := e hxV
    rwa [Subsingleton.elim y (f hZ.1.genericPoint)]
  subst hUtop
  let e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (e0 : K →+* _)
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) :=
    hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)
  have hmin := primeIdealOf_mem_minimalPrimes hV hZ hxV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩
  let eL := IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)
  let eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have hc1 : CharZero (X.residueField hZ.1.genericPoint) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have f00 : Algebra.IsStandardSmooth K Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have f01 : Algebra.FinitePresentation K Γ(X, V) := inferInstance
  have f0 : Algebra.EssFiniteType K Γ(X, V) := inferInstance
  have f1 : Algebra.EssFiniteType K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp K Γ(X, V) _
  have f2 : Algebra.EssFiniteType ℚ K := inferInstance
  have f3 : Algebra.EssFiniteType ℚ (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp ℚ K _
  have f4 : Algebra.EssFiniteType ℚ (X.residueField hZ.1.genericPoint) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eR.toRatAlgEquiv).1 f3
  have f5 : Algebra.EssFiniteType K (X.residueField hZ.1.genericPoint) := Algebra.EssFiniteType.of_comp ℚ K _
  exact IntermediateField.fg_top K _

end Formalism.L2.Pj.TranscendenceDegreeLemmas
end

