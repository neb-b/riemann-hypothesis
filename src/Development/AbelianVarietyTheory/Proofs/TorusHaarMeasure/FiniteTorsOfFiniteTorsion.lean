module

public import Mathlib
public import ReciprocityTheory.DualLattices.FormalChartAtZero
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015

@[expose] public section

noncomputable section

open IsLocalRing TensorProduct ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2 GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts

namespace GlobalTheory.ChartCompare

variable {R₀ : Type} [CommRing R₀]

section Eval

open MvPowerSeries

variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S]

open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.hasSubst_C (a : σ → S) (ha : ∀ i, IsNilpotent (a i)) :
    HasSubst (fun i => (C (a i) : MvPowerSeries Empty S)) :=
  hasSubst_of_constantCoeff_nilpotent fun i => by simpa using ha i

open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
private theorem nilpotent_eval_eq_finsum (f : MvPowerSeries σ R₀) (a : σ → S)
    (ha : ∀ i, IsNilpotent (a i)) : _root_.ReciprocityTheory.PGsh.Be2.nEval f a = ∑ᶠ d, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm f a d := by
  obtain ⟨N, -, hN⟩ := _root_.GlobalTheory.evBasic_exists_pow a ha
  rw [_root_.GlobalTheory.evBasic_nEval_eq_tEval f a N hN, _root_.GlobalTheory.evBasic_tEval_eq_sum]
  have hsupp : Function.support (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm f a) ⊆
      (((Fintype.piFinset fun _ : σ => Finset.range N).map
        Finsupp.equivFunOnFinite.symm.toEmbedding : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ)) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_map_equiv, Fintype.mem_piFinset]
    intro i
    simp only [Equiv.symm_symm, Finsupp.equivFunOnFinite_apply, Finset.mem_range]
    by_contra hi
    apply hd
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finset.prod_eq_zero (f := fun k => a k ^ d k) (Finset.mem_univ i)
        (pow_eq_zero_of_le (not_lt.mp hi) (hN i)),
      smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm, Algebra.smul_def, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp

open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.subst_C_eq (f : MvPowerSeries σ R₀) (a : σ → S)
    (ha : ∀ i, IsNilpotent (a i)) :
    subst (fun i => (C (a i) : MvPowerSeries Empty S)) f = C (_root_.ReciprocityTheory.PGsh.Be2.nEval f a) := by
  ext e
  obtain rfl : e = 0 := Subsingleton.elim _ _
  rw [coeff_subst (_root_.GlobalTheory.ChartCompare.hasSubst_C a ha), nilpotent_eval_eq_finsum f a ha,
    coeff_zero_C]
  refine finsum_congr fun d => ?_
  have hC : (d.prod fun s n => (C (a s) : MvPowerSeries Empty S) ^ n) =
      C (d.prod fun s n => a s ^ n) := by
    simp [map_finsuppProd]
  rw [hC, coeff_zero_C, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm]

open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.nEval_X (a : σ → S) (ha : ∀ i, IsNilpotent (a i)) (s : σ) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval (X s : MvPowerSeries σ R₀) a = a s := by
  have h := congrArg (coeff 0) (_root_.GlobalTheory.ChartCompare.subst_C_eq (X s : MvPowerSeries σ R₀) a ha)
  rw [subst_X (_root_.GlobalTheory.ChartCompare.hasSubst_C a ha), coeff_zero_C, coeff_zero_C] at h
  exact h.symm

open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.nEval_zero (a : σ → S) (ha : ∀ i, IsNilpotent (a i)) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval (0 : MvPowerSeries σ R₀) a = 0 := by
  rw [nilpotent_eval_eq_finsum _ a ha]
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm]

open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.isNilpotent_nEval (f : MvPowerSeries σ R₀)
    (hf : constantCoeff f = 0) (a : σ → S)
    (ha : ∀ i, IsNilpotent (a i)) : IsNilpotent (_root_.ReciprocityTheory.PGsh.Be2.nEval f a) := by
  have h := _root_.GlobalTheory.evBasic_nEval_sub_coeff_mem f a ha
  rw [coeff_zero_eq_constantCoeff_apply, hf, map_zero, sub_zero] at h
  have hle : Ideal.span (Set.range a) ≤ nilradical S :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact mem_nilradical.mpr (ha i))
  exact mem_nilradical.mp (hle h)


open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.nEval_subst (b : σ → MvPowerSeries τ R₀)
    (hb : ∀ s, constantCoeff (b s) = 0)
    (f : MvPowerSeries σ R₀) (a : τ → S) (ha : ∀ i, IsNilpotent (a i)) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval (subst b f) a = _root_.ReciprocityTheory.PGsh.Be2.nEval f (fun s => _root_.ReciprocityTheory.PGsh.Be2.nEval (b s) a) := by
  have hbS : HasSubst b := hasSubst_of_constantCoeff_nilpotent fun s => by simp [hb s]
  have hab : ∀ s, IsNilpotent (_root_.ReciprocityTheory.PGsh.Be2.nEval (b s) a) := fun s =>
    _root_.GlobalTheory.ChartCompare.isNilpotent_nEval (b s) (hb s) a ha
  have h := _root_.GlobalTheory.ChartCompare.subst_C_eq (subst b f) a ha
  rw [subst_comp_subst_apply hbS (_root_.GlobalTheory.ChartCompare.hasSubst_C a ha)] at h
  simp_rw [_root_.GlobalTheory.ChartCompare.subst_C_eq _ a ha] at h
  rw [_root_.GlobalTheory.ChartCompare.subst_C_eq f _ hab] at h
  simpa using (congrArg (coeff 0) h).symm


open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
private theorem finsupp_prod_pow_eq_toMultiset_map_prod (a : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i n => a i ^ n) = ((Finsupp.toMultiset d).map a).prod := by
  rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
private theorem multiset_map_prod_sub_mem_of_sub_mem (a b : σ → S) (J : Ideal S) (hJ : ∀ i, a i - b i ∈ J)
    (m : Multiset σ) : (m.map a).prod - (m.map b).prod ∈ J := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons i m ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
    have e : a i * (m.map a).prod - b i * (m.map b).prod =
        a i * ((m.map a).prod - (m.map b).prod) + (a i - b i) * (m.map b).prod := by ring
    rw [e]
    exact J.add_mem (J.mul_mem_left _ ih) (J.mul_mem_right _ (hJ i))

open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
private theorem multiset_map_prod_sub_mem_mul_of_two_le_card (a b : σ → S) (I J : Ideal S) (ha : ∀ i, a i ∈ I)
    (hb : ∀ i, b i ∈ I) (hJ : ∀ i, a i - b i ∈ J) (m : Multiset σ)
    (hm : 2 ≤ Multiset.card m) : (m.map a).prod - (m.map b).prod ∈ I * J := by
  obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card m)
  obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hi
  rw [Multiset.card_cons] at hm
  have hB : (m'.map b).prod ∈ I := by
    obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card m')
    obtain ⟨m'', rfl⟩ := Multiset.exists_cons_of_mem hj
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact I.mul_mem_right _ (hb j)
  have e : ((i ::ₘ m').map a).prod - ((i ::ₘ m').map b).prod =
      a i * ((m'.map a).prod - (m'.map b).prod) + (m'.map b).prod * (a i - b i) := by
    simp only [Multiset.map_cons, Multiset.prod_cons]
    ring
  rw [e]
  exact add_mem (Ideal.mul_mem_mul (ha i) (multiset_map_prod_sub_mem_of_sub_mem a b J hJ _))
    (Ideal.mul_mem_mul hB (hJ i))


open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.nEval_sub_mem (f : MvPowerSeries σ R₀) (a b : σ → S)
    (hna : ∀ i, IsNilpotent (a i))
    (hnb : ∀ i, IsNilpotent (b i)) (I J : Ideal S) (ha : ∀ i, a i ∈ I) (hb : ∀ i, b i ∈ I)
    (hJ : ∀ i, a i - b i ∈ J) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval f a - _root_.ReciprocityTheory.PGsh.Be2.nEval f b - ∑ j, coeff (Finsupp.single j 1) f • (a j - b j) ∈ I * J := by
  set t : (σ →₀ ℕ) → S := fun d => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm f a d - _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm f b d
    with ht
  have hfa := _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm_finite f a hna
  have hfb := _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm_finite f b hnb
  have key : _root_.ReciprocityTheory.PGsh.Be2.nEval f a - _root_.ReciprocityTheory.PGsh.Be2.nEval f b = ∑ᶠ d, t d := by
    rw [nilpotent_eval_eq_finsum f a hna, nilpotent_eval_eq_finsum f b hnb,
      finsum_sub_distrib hfa hfb]
  have lin : ∑ j, coeff (Finsupp.single j 1) f • (a j - b j) =
      ∑ᶠ d, (Set.range fun j => Finsupp.single j 1).indicator t d := by
    rw [← finsum_mem_def, finsum_mem_range (Finsupp.single_left_injective one_ne_zero),
      finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [t, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm]
    rw [Finsupp.prod_single_index (h := fun i n => a i ^ n) (pow_zero _),
      Finsupp.prod_single_index (h := fun i n => b i ^ n) (pow_zero _), pow_one, pow_one, smul_sub]
  have hft : (Function.support t).Finite := (hfa.union hfb).subset (Function.support_sub _ _)
  have hfi : (Function.support ((Set.range fun j => Finsupp.single j 1).indicator t)).Finite :=
    (Set.finite_range _).subset Set.support_indicator_subset
  rw [key, lin, ← finsum_sub_distrib hft hfi]
  refine finsum_induction (fun x => x ∈ I * J) (zero_mem _) (fun _ _ => add_mem) fun d => ?_
  by_cases hd : d ∈ Set.range fun j : σ => Finsupp.single j 1
  · rw [Set.indicator_of_mem hd, sub_self]
    exact zero_mem _
  · rw [Set.indicator_of_notMem hd, sub_zero, ht]
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm, ← smul_sub, finsupp_prod_pow_eq_toMultiset_map_prod]
    rw [Algebra.smul_def]
    apply Ideal.mul_mem_left
    rcases Nat.lt_or_ge (Multiset.card (Finsupp.toMultiset d)) 2 with h | h
    · obtain h0 | h1 : Multiset.card (Finsupp.toMultiset d) = 0 ∨
          Multiset.card (Finsupp.toMultiset d) = 1 := by omega
      · rw [Multiset.card_eq_zero.mp h0]
        simp
      · obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp h1
        have hdj : Finsupp.single j 1 = d := by
          rw [← Finsupp.toMultiset_toFinsupp d, hj, Multiset.toFinsupp_singleton]
        exact absurd ⟨j, hdj⟩ hd
    · exact multiset_map_prod_sub_mem_mul_of_two_le_card a b I J ha hb hJ _ h

end Eval

section Law

open MvPowerSeries

variable {g : ℕ}

end Law

section Nil

variable {K : LAlg R₀}

end Nil

section Chart

variable {B : BX R₀} {K : LAlg R₀} {g : ℕ}

end Chart

section Torsion

universe v

variable {B : BX R₀} {k : LAlg R₀} {p g : ℕ} {O : ResAlg k}

variable {C : Type v} [Field C] [Algebra (O.alg : Type) C] [IsFractionRing (O.alg : Type) C]


namespace OfFin

variable (F : FIN B O.alg p)




end OfFin


end Torsion

section Bundle

universe v

variable {B : BX R₀} {g : ℕ} {p : ℕ} [Fact p.Prime] {k : LAlg R₀} {O : ResAlg k} {W : NilAlg k}
  {C : Type v} [Field C] [Algebra (O.alg : Type) C] [IsFractionRing (O.alg : Type) C]


end Bundle

universe v

end GlobalTheory.ChartCompare
