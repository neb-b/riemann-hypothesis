module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdPLinIsHomogeneous
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section
namespace GlobalTheory.InducedPBW.Onto

private lemma UgF_mono {p q j k : ℕ} (h : j ≤ k) : UgF p q j ≤ UgF p q k :=
  Submodule.span_mono fun _ ⟨l, hl, hu⟩ => ⟨l, hl.trans h, hu⟩

theorem indF_mono {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {j k : ℕ} (h : j ≤ k) : indF act j ≤ indF act k := by
  refine Submodule.span_mono ?_
  rintro z ⟨u, hu, v, rfl⟩
  exact ⟨u, UgF_mono h hu, v, rfl⟩

theorem indFlt_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (k : ℕ) : indFlt act k ≤ indF act k := by
  unfold indFlt
  exact iSup₂_le fun j hj => indF_mono act hj.le

theorem le_indFlt {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {j k : ℕ} (h : j < k) : indF act j ≤ indFlt act k := by
  unfold indFlt
  exact le_iSup₂ (f := fun i (_ : i < k) => indF act i) j h

theorem pLin_isHomogeneous {p q : ℕ} (Z : Mat p q) : (pLin Z).IsHomogeneous 1 := by
  unfold pLin
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun ab _ => MvPolynomial.isHomogeneous_C_mul_X _ _

theorem prod_pLin_isHomogeneous {p q : ℕ} (l : List (Mat p q)) :
    (l.map pLin).prod.IsHomogeneous l.length := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.length_nil]
    exact MvPolynomial.isHomogeneous_one _ _
  | cons Z l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm]
    exact (pLin_isHomogeneous Z).mul ih

theorem prod_mem_UgF {p q k : ℕ} (l : List (Mat p q)) (h : l.length ≤ k) :
    (l.map (ugι p q)).prod ∈ UgF p q k := Submodule.subset_span ⟨l, h, rfl⟩

theorem symProd_mem_UgF {p q k m : ℕ} (x : Fin m → Mat p q) (h : m ≤ k) :
    symProd (fun i => ugι p q (x i)) ∈ UgF p q k := by
  unfold symProd
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => ?_)
  have hmem := prod_mem_UgF (k := k) (List.ofFn fun i => x (σ i)) (by rw [List.length_ofFn]; exact h)
  rw [List.map_ofFn] at hmem
  exact hmem

theorem symU_mem_UgF {p q k : ℕ} (f : MvPolynomial (PIx p q) ℂ) (hf : f.IsHomogeneous k) :
    symU p q f ∈ UgF p q k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = k := by
    by_contra hne
    exact MvPolynomial.mem_support_iff.mp hd (hf.coeff_eq_zero hne)
  have e : MvPolynomial.monomial d (f.coeff d) =
      f.coeff d • (MvPolynomial.basisMonomials (PIx p q) ℂ) d := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [symU, Module.Basis.constr_basis]
  refine symProd_mem_UgF _ (le_of_eq ?_)
  rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hdeg]
  rfl

private lemma mkQ_tmul_prod_mem_indFlt_sup {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hc : SymbolCongr act) (k : ℕ)
    (l : List (Mat p q)) (hl : l.length ≤ k) (v : V) :
    (indRel act).mkQ (TensorProduct.tmul ℂ (l.map (ugι p q)).prod v) ∈ indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
  rcases lt_or_eq_of_le hl with hlt | heq
  · refine Submodule.mem_sup_left (le_indFlt act hlt ?_)
    exact Submodule.subset_span ⟨_, prod_mem_UgF l le_rfl, v, rfl⟩
  · subst heq
    have hP : (l.map pLin).prod ∈ homog (PIx p q) l.length :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (prod_pLin_isHomogeneous l)
    have hs : (indRel act).mkQ (TensorProduct.tmul ℂ (symU p q (l.map pLin).prod) v) ∈
        (symTens p q V l.length).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
      refine ⟨LinearMap.rTensor V (homog (PIx p q) l.length).subtype
        (TensorProduct.tmul ℂ (⟨_, hP⟩ : homog (PIx p q) l.length) v), LinearMap.mem_range_self _ _, ?_⟩
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    have hsum := Submodule.add_mem_sup (hc l v) hs
    rw [sub_add_cancel] at hsum
    exact hsum

theorem indF_eq_sup (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hc : SymbolCongr act) (k : ℕ) :
    indF act k = indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨u, hu, v, rfl⟩
    have key : UgF p q k ≤ (indFlt act k ⊔
        (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q))).comap
        ((indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v) := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨l, hl, rfl⟩
      exact mkQ_tmul_prod_mem_indFlt_sup act hc k l hl v
    exact key hu
  · refine sup_le (indFlt_le act k) ?_
    rintro _ ⟨z, ⟨w, rfl⟩, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f v =>
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply]
      exact Submodule.subset_span
        ⟨_, symU_mem_UgF f.1 ((MvPolynomial.mem_homogeneousSubmodule _ _).mp f.2), v, rfl⟩
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem ha hb

end GlobalTheory.InducedPBW.Onto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdXEqMonomial
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section

namespace GlobalTheory.InducedPBW.Symbol

variable {p q : ℕ}

def prodU (l : List (Mat p q)) : Ug p q := (l.map (ugι p q)).prod

theorem prodU_cons (x : Mat p q) (l : List (Mat p q)) : prodU (x :: l) = ugι p q x * prodU l := by
  simp only [prodU, List.map_cons, List.prod_cons]

theorem prodU_append (l l' : List (Mat p q)) : prodU (l ++ l') = prodU l * prodU l' := by
  simp only [prodU, List.map_append, List.prod_append]

def below (p q k : ℕ) : Submodule ℂ (Ug p q) :=
  Submodule.span ℂ {u | ∃ l : List (Mat p q), l.length < k ∧ u = prodU l}

section
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem ug_bracket (x y : Mat p q) :
    ugι p q (x * y - y * x) = ugι p q x * ugι p q y - ugι p q y * ugι p q x := by
  have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℂ : Mat p q →ₗ⁅ℂ⁆ Ug p q) x y
  simpa only [ugι, LieHom.coe_toLinearMap, Ring.lie_def] using h
end

theorem mul_mem_below (x : Mat p q) {k : ℕ} {u : Ug p q} (hu : u ∈ below p q k) :
    ugι p q x * u ∈ below p q (k + 1) := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    refine Submodule.subset_span ⟨x :: l, ?_, (prodU_cons x l).symm⟩
    simp only [List.length_cons]
    omega
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add w w' _ _ hw hw' => rw [mul_add]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hw

theorem perm_sub_mem_below {l l' : List (Mat p q)} (h : l.Perm l') :
    prodU l - prodU l' ∈ below p q l.length := by
  induction h with
  | nil => rw [sub_self]; exact Submodule.zero_mem _
  | cons x _ ih =>
    rw [prodU_cons, prodU_cons, ← mul_sub, List.length_cons]
    exact mul_mem_below x ih
  | swap x y l =>
    have e : prodU (y :: x :: l) - prodU (x :: y :: l) = prodU ((y * x - x * y) :: l) := by
      simp only [prodU_cons, ug_bracket, sub_mul, mul_assoc]
    rw [e]
    exact Submodule.subset_span ⟨(y * x - x * y) :: l, by simp, rfl⟩
  | @trans l₁ l₂ l₃ h₁ _ ih₁ ih₂ =>
    rw [← sub_add_sub_cancel (prodU l₁) (prodU l₂) (prodU l₃)]
    exact Submodule.add_mem _ ih₁ (h₁.length_eq ▸ ih₂)

variable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)

def cls (v : V) : Ug p q →ₗ[ℂ] Ind act :=
  (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v

theorem cls_apply (v : V) (u : Ug p q) :
    cls act v u = (indRel act).mkQ (TensorProduct.tmul ℂ u v) := rfl

private lemma indF_le_indFlt_of_lt {j k : ℕ} (h : j < k) : indF act j ≤ indFlt act k := by
  unfold indFlt
  exact le_iSup₂_of_le (f := fun i (_ : i < k) => indF act i) j h le_rfl

private lemma cls_prodU_mem_indF (v : V) (l : List (Mat p q)) :
    cls act v (prodU l) ∈ indF act l.length :=
  Submodule.subset_span ⟨prodU l, Submodule.subset_span ⟨l, le_rfl, rfl⟩, v, cls_apply act v _⟩

theorem cls_mem_of_below (v : V) {k : ℕ} {u : Ug p q} (hu : u ∈ below p q k) :
    cls act v u ∈ indFlt act k := by
  have hle : below p q k ≤ (indFlt act k).comap (cls act v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    exact indF_le_indFlt_of_lt act hl (cls_prodU_mem_indF act v l)
  exact hle hu

theorem cls_mul_kc (v : V) (u : Ug p q) {Y : Mat p q} (hY : IsKC Y) :
    cls act v (u * ugι p q Y) = cls act (act Y v) u := by
  rw [cls_apply, cls_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨u, Y, v, hY, rfl⟩)

theorem cls_mem_of_kc (v : V) (l l' : List (Mat p q)) {Y : Mat p q} (hY : IsKC Y) :
    cls act v (prodU (l ++ Y :: l')) ∈ indFlt act (l.length + (l'.length + 1)) := by
  have hperm : (l ++ Y :: l').Perm ((l ++ l') ++ [Y]) :=
    List.perm_middle.trans (List.perm_append_singleton Y (l ++ l')).symm
  have hlen : (l ++ Y :: l').length = l.length + (l'.length + 1) := by simp
  have h₁ := cls_mem_of_below act v (perm_sub_mem_below hperm)
  rw [hlen] at h₁
  have h₂ : cls act v (prodU ((l ++ l') ++ [Y])) ∈ indFlt act (l.length + (l'.length + 1)) := by
    have e : prodU ((l ++ l') ++ [Y]) = prodU (l ++ l') * ugι p q Y := by
      rw [prodU_append, prodU_cons]
      simp [prodU]
    rw [e, cls_mul_kc act v _ hY]
    refine indF_le_indFlt_of_lt act (j := (l ++ l').length) ?_ (cls_prodU_mem_indF act _ _)
    simp only [List.length_append]
    omega
  have e : cls act v (prodU (l ++ Y :: l')) =
      cls act v (prodU (l ++ Y :: l') - prodU ((l ++ l') ++ [Y])) + cls act v (prodU ((l ++ l') ++ [Y])) := by
    rw [map_sub, sub_add_cancel]
  rw [e]
  exact Submodule.add_mem _ h₁ h₂

def unitP (ab : PIx p q) : Mat p q := Eab ab.1.1 ab.1.2

theorem prod_X_eq_monomial (a : List (PIx p q)) :
    (a.map (MvPolynomial.X : PIx p q → MvPolynomial (PIx p q) ℂ)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp (a : Multiset (PIx p q))) 1 := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.map_cons, List.prod_cons, ih, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
      ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

theorem symProd_sub_mem (b : List (Mat p q)) {k : ℕ} (x : Fin k → Mat p q)
    (h : b.Perm (List.ofFn x)) :
    prodU b - symProd (fun i => ugι p q (x i)) ∈ below p q b.length := by
  have hk : ((k.factorial : ℂ)⁻¹) • ∑ _σ : Equiv.Perm (Fin k), prodU b = prodU b := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]
  have e : prodU b - symProd (fun i => ugι p q (x i)) =
      ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), (prodU b - prodU (List.ofFn fun i => x (σ i))) := by
    rw [Finset.sum_sub_distrib, smul_sub, hk]
    simp only [symProd, prodU, List.map_ofFn]
    rfl
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => perm_sub_mem_below ?_)
  exact h.trans (Equiv.Perm.ofFn_comp_perm σ x).symm

theorem units_sub_mem (a : List (PIx p q)) :
    prodU (a.map unitP) - symU p q (a.map MvPolynomial.X).prod ∈ below p q a.length := by
  rw [prod_X_eq_monomial]
  have hb : MvPolynomial.monomial (Multiset.toFinsupp (a : Multiset (PIx p q))) (1 : ℂ) =
      MvPolynomial.basisMonomials (PIx p q) ℂ (Multiset.toFinsupp (a : Multiset (PIx p q))) := by
    rw [MvPolynomial.coe_basisMonomials]
  rw [hb, symU, Module.Basis.constr_basis, Multiset.toFinsupp_toMultiset]
  have hlen : (a.map unitP).length = a.length := List.length_map _
  rw [← hlen]
  refine symProd_sub_mem (a.map unitP) (fun i => unitP ((a : Multiset (PIx p q)).toList.get i)) ?_
  have hL : ((a : Multiset (PIx p q)).toList).Perm a :=
    Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList])
  have hf : List.ofFn (fun i => unitP ((a : Multiset (PIx p q)).toList.get i)) =
      ((a : Multiset (PIx p q)).toList).map unitP :=
    List.ext_get (by simp) (by simp)
  rw [hf]
  exact (hL.map unitP).symm

private lemma sum_unitP_apply (x : Mat p q) (c d : Ix p q) :
    (∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab) c d = if sameBlock c d then 0 else x c d := by
  rw [Matrix.sum_apply]
  split_ifs with h
  · refine Finset.sum_eq_zero fun ab _ => ?_
    have hne : ¬ (ab.1.1 = c ∧ ab.1.2 = d) := by
      rintro ⟨h₁, h₂⟩
      exact ab.2 (h₁ ▸ h₂ ▸ h)
    simp [unitP, Eab, Matrix.single_apply_of_ne (h := hne)]
  · rw [Finset.sum_eq_single (⟨(c, d), h⟩ : PIx p q)]
    · simp [unitP, Eab]
    · intro ab _ hab
      have hne : ¬ (ab.1.1 = c ∧ ab.1.2 = d) := fun e => hab (Subtype.ext (Prod.ext e.1 e.2))
      simp [unitP, Eab, Matrix.single_apply_of_ne (h := hne)]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

private lemma isKC_sub_sum_unitP (x : Mat p q) : IsKC (x - ∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab) := by
  intro c d h
  rw [Matrix.sub_apply, sum_unitP_apply, if_neg h, sub_self]

theorem mixed_mem (v : V) (l : List (Mat p q)) : ∀ a : List (PIx p q),
    cls act v (prodU (a.map unitP) * prodU l) -
      cls act v (symU p q ((a.map MvPolynomial.X).prod * (l.map pLin).prod)) ∈
      indFlt act (a.length + l.length) := by
  induction l with
  | nil =>
    intro a
    have h1 : prodU ([] : List (Mat p q)) = 1 := by simp [prodU]
    simp only [h1, mul_one, List.map_nil, List.prod_nil, List.length_nil, add_zero]
    rw [← map_sub]
    exact cls_mem_of_below act v (units_sub_mem a)
  | cons x l ih =>
    intro a
    set P : Mat p q := ∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab with hP
    have hY : IsKC (x - P) := isKC_sub_sum_unitP x
    have hx : ugι p q x = ∑ ab : PIx p q, x ab.1.1 ab.1.2 • ugι p q (unitP ab) + ugι p q (x - P) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hP, map_sum]
      simp only [map_smul]
      abel
    have hpl : pLin x = ∑ ab : PIx p q, x ab.1.1 ab.1.2 • MvPolynomial.X ab := by
      simp only [pLin, MvPolynomial.smul_eq_C_mul]
    have hL : prodU (a.map unitP) * prodU (x :: l) =
        ∑ ab : PIx p q, x ab.1.1 ab.1.2 • (prodU ((a ++ [ab]).map unitP) * prodU l) +
          prodU (a.map unitP ++ (x - P) :: l) := by
      rw [prodU_cons, hx, add_mul, Finset.sum_mul, mul_add, Finset.mul_sum, prodU_append, prodU_cons]
      congr 1
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [List.map_append, prodU_append, List.map_singleton, prodU_cons]
      simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
      simp [prodU]
    have hR : (a.map MvPolynomial.X).prod * ((x :: l).map pLin).prod =
        ∑ ab : PIx p q, x ab.1.1 ab.1.2 •
          (((a ++ [ab]).map MvPolynomial.X).prod * (l.map pLin).prod) := by
      rw [List.map_cons, List.prod_cons, hpl, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        smul_mul_assoc, mul_smul_comm, mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hL, hR, map_add (f := _), map_sum, map_sum, map_sum]
    simp only [map_smul]
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun ab _ => ?_) ?_
    · rw [← smul_sub]
      refine Submodule.smul_mem _ _ ?_
      have h := ih (a ++ [ab])
      have e : (a ++ [ab]).length + l.length = a.length + (x :: l).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rwa [e] at h
    · have h := cls_mem_of_kc act v (a.map unitP) l hY
      have e : a.length + (l.length + 1) = a.length + (x :: l).length := by simp
      rw [List.length_map, e] at h
      exact h

end GlobalTheory.InducedPBW.Symbol

namespace GlobalTheory.InducedPBW

theorem symbolCongr (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : SymbolCongr act := by
  intro l v
  have h := Symbol.mixed_mem act v l []
  simp only [Symbol.prodU, List.map_nil, List.prod_nil, one_mul, List.length_nil, zero_add,
    Symbol.cls_apply] at h
  exact h

end GlobalTheory.InducedPBW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedParametersBounded
section
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

theorem v_bounds_of_mem (G : GridData) {i : ℕ} (h2 : 2 ≤ i) (hk : i ≤ G.k) : G.v G.k ≤ G.v i ∧ G.v i ≤ G.v 2 := by
  constructor
  · rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt (G.v_anti i G.k h2 h le_rfl)
  · rcases eq_or_lt_of_le h2 with h | h
    · rw [← h]
    · exact le_of_lt (G.v_anti 2 i le_rfl h hk)

theorem b_bounds_of_mem (G : GridData) {l : ℕ} (h1 : 1 ≤ l) (hm : l ≤ G.m) : G.b 1 ≤ G.b l ∧ G.b l ≤ G.b G.m := by
  constructor
  · rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]
    · exact le_of_lt (G.b_mono 1 l le_rfl h hm)
  · rcases eq_or_lt_of_le hm with h | h
    · rw [h]
    · exact le_of_lt (G.b_mono l G.m h1 h le_rfl)

theorem abs_le_a_zero_of_mem_lam (G : GridData) (hv : 0 ≤ G.v G.k) {x : ℚ × Bool} (hx : x ∈ G.lam) :
    |x.1| ≤ G.a 0 := by
  have hv2 : (0 : ℚ) ≤ G.v 2 := by
    have := (G.v_bounds_of_mem le_rfl G.two_le_k).1
    exact_mod_cast hv.trans this
  have hga : (0 : ℚ) ≤ G.ga := by positivity
  rcases G.mem_lam.1 hx with ⟨l, hl, rfl⟩ | ⟨hc, -⟩
  · have e := G.a_sub_a 0 l
    simp only [Nat.cast_zero, sub_zero] at e
    have hm := G.a_m
    have e2 := G.a_sub_a l G.m
    have hl' : (l : ℚ) ≤ G.m := by exact_mod_cast hl
    have hl0 : (0 : ℚ) ≤ l := by positivity
    have h1 : (0 : ℚ) ≤ (l : ℚ) * G.ga := mul_nonneg hl0 hga
    have h2 : (0 : ℚ) ≤ ((G.m : ℚ) - l) * G.ga := mul_nonneg (by linarith) hga
    simp only
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, h2, hk, e⟩ := G.mem_cloudHalf.1 hc
    obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk
    have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo
    have hhi' : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hhi
    have ha0 : G.a 0 = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1) * G.ga := by simp [a]
    have h3 : (0 : ℚ) ≤ ((G.m : ℚ) + 1) * G.ga := by positivity
    rw [e, vHalf, abs_le]; constructor <;> linarith

theorem abs_le_of_mem_D0 (G : GridData) (hv : 0 ≤ G.v G.k) (hb : 0 < G.b 1) {x : ℚ × Bool} (hx : x ∈ G.parD0) :
    |x.1| ≤ G.a 0 ∨ |x.1| ≤ G.b G.m := by
  rcases G.mem_discrete_parameter_iff.1 hx with ⟨hc, -⟩ | ⟨l, h1, hm, rfl⟩
  · left
    obtain ⟨i, h2, hk, e⟩ := G.mem_cloud.1 hc
    obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk
    have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo
    have hhi' : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hhi
    have ha0 : G.a 0 = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1) * G.ga := by simp [a]
    have h3 : (0 : ℚ) ≤ ((G.m : ℚ) + 1) * G.ga := by positivity
    rw [e, abs_le]; constructor <;> linarith
  · right
    obtain ⟨hlo, hhi⟩ := G.b_bounds_of_mem h1 hm
    have hlo' : (0 : ℚ) < G.b l := by exact_mod_cast hb.trans_le hlo
    have hhi' : (G.b l : ℚ) ≤ G.b G.m := by exact_mod_cast hhi
    simp only
    rw [abs_le]; constructor <;> linarith

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.Twist

open GlobalTheory.SignedHC

theorem parPi_parD0_entries_bounded : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {B : ℝ}, 0 ≤ G.v G.k → 0 < G.b 1 →
    ((G.a 0 : ℚ) : ℝ) ≤ B → (G.b G.m : ℝ) ≤ B → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B := by
  intro G n lam ε mu ε' B hv hb hA hBm hP hD
  obtain ⟨-, q, hq, hS⟩ := hP
  obtain ⟨-, q', hq', hS'⟩ := hD
  constructor
  · intro a
    have hmem : (q a, ε a) ∈ G.lam := by
      rw [← G.parPi_zero, hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    have h := G.abs_le_a_zero_of_mem_lam hv hmem
    rw [hq a]
    have h' : |((q a : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ) := by rw [← Rat.cast_abs]; exact_mod_cast h
    exact h'.trans hA
  · intro i
    have hmem : (q' i, ε' i) ∈ G.parD0 := by
      rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [hq' i]
    rcases G.abs_le_of_mem_D0 hv hb hmem with h | h
    · have h' : |((q' i : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ) := by rw [← Rat.cast_abs]; exact_mod_cast h
      exact h'.trans hA
    · have h' : |((q' i : ℚ) : ℝ)| ≤ ((G.b G.m : ℤ) : ℝ) := by
        rw [← Rat.cast_abs]
        have : ((G.b G.m : ℤ) : ℝ) = (((G.b G.m : ℤ) : ℚ) : ℝ) := by push_cast; rfl
        rw [this]; exact_mod_cast h
      exact h'.trans hBm

end GlobalTheory.Twist
end

