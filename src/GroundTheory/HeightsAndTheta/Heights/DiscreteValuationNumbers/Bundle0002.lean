module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section Local

variable {A : Type*} [CommRing A]

theorem mem_minimalPrimes_of_mul_mem {J J' W : Ideal A} {s t : A} (hs : s ∉ W) (ht : t ∉ W)
    (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) (hW : W ∈ J.minimalPrimes) :
    W ∈ J'.minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  refine ⟨⟨hWp, fun x hx => ?_⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, fun x hx => ?_⟩ hQW⟩
  · exact (hWp.mem_or_mem (hW.1.2 (htJ x hx))).resolve_left ht
  · exact (hQ.1.mem_or_mem (hQ.2 (hsJ x hx))).resolve_left (fun h => hs (hQW h))

theorem length_localized_eq_of_le {J J'' W : Ideal A} [W.IsPrime] (hle : J ≤ J'')
    (h : ∀ x ∈ J'', ∃ t ∉ W, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J'')) := by
  let q : (A ⧸ J) →ₗ[A] (A ⧸ J'') := Submodule.factor hle
  let f := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)
  let g := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J'')
  let m := IsLocalizedModule.map W.primeCompl f g q
  have hinj : Function.Injective m := by
    apply IsLocalizedModule.injective_of_map_zero W.primeCompl f
    intro x hx
    rw [IsLocalizedModule.map_apply] at hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective J x
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff W.primeCompl g).mp hx
    have hsy : (s : A) * y ∈ J'' := by
      have : (s : A) • (Submodule.mkQ J'' y) = 0 := hs
      rwa [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul] at this
    obtain ⟨t, ht, hty⟩ := h _ hsy
    refine (IsLocalizedModule.eq_zero_iff W.primeCompl f).mpr ⟨⟨t * s, W.primeCompl.mul_mem ht s.2⟩, ?_⟩
    show ((t * s : A)) • (Submodule.mkQ J y) = 0
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      mul_assoc]
    exact hty
  have hsurj : Function.Surjective m :=
    IsLocalizedModule.map_surjective W.primeCompl f g q (Submodule.factor_surjective hle)
  exact ((LinearEquiv.ofBijective m ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

theorem length_localized_eq_of_mul_mem {J J' W : Ideal A} [W.IsPrime] {s t : A} (hs : s ∉ W)
    (ht : t ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J')) := by
  have key : ∀ {J J' : Ideal A} {t : A}, t ∉ W → (∀ x ∈ J', t * x ∈ J) →
      ∀ x ∈ J ⊔ J', ∃ t ∉ W, t * x ∈ J := by
    intro J J' t ht htJ x hx
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨t, ht, by rw [mul_add]; exact J.add_mem (J.mul_mem_left t ha) (htJ a' ha')⟩
  rw [length_localized_eq_of_le le_sup_left (key ht htJ),
    length_localized_eq_of_le le_sup_left (key hs hsJ), sup_comm]

end Local

section Divisors

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_eq_of_mul_sub_mem {P : Ideal (MRing ι R)} {f g u v : MRing ι R}
    {W : Ideal (MRing ι R)} (hu : u ∉ W) (hv : v ∉ W) (h : u * f - v * g ∈ P) :
    divCycle P f W = divCycle P g W := by
  have h1 : ∀ x ∈ P ⊔ Ideal.span {f}, u * x ∈ P ⊔ Ideal.span {g} := by
    intro x hx
    obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g := by ring
    rw [e]
    exact Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
      (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)
  have h2 : ∀ x ∈ P ⊔ Ideal.span {g}, v * x ∈ P ⊔ Ideal.span {f} := by
    intro x hx
    obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have e : v * (p + c * g) = (v * p - c * (u * f - v * g)) + (c * u) * f := by ring
    rw [e]
    exact Submodule.add_mem_sup (P.sub_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
      (Ideal.mem_span_singleton'.mpr ⟨c * u, rfl⟩)
  unfold divCycle
  by_cases hf : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · have hg : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W :=
      ⟨mem_minimalPrimes_of_mul_mem hu hv h1 h2 hf.1, hf.2⟩
    rw [dite_eq_left hf, dite_eq_left hg]
    have : W.IsPrime := hf.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hu hv h1 h2]
  · have hg : ¬ (W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W) := fun hg =>
      hf ⟨mem_minimalPrimes_of_mul_mem hv hu h2 h1 hg.1, hg.2⟩
    rw [dite_eq_right hf, dite_eq_right hg]

theorem le_and_isRelevant_of_divCycle_ne_zero {P : Ideal (MRing ι R)} {f : MRing ι R}
    {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact ⟨hW.1.1.1, le_sup_left.trans hW.1.1.2, hW.2⟩
  · exact absurd rfl h

end Divisors

section Vertical

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem IsVerticalDivisor.of_unit_off_special {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ}
    {f g : MRing ι O}
    (degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
      (fun k => (bf k : ℤ) - bg k) = b)
    (hf : f ∉ P) (hg : g ∉ P)
    (hunit : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
      (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    IsVerticalDivisor P ϖ b f g := by
  refine ⟨degrees, hf, hg, ?_, hunit⟩
  intro W hW
  by_contra hϖ
  have hsupp : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
    by_cases h1 : divCycle P f W = 0
    · have h2 : divCycle P g W ≠ 0 := by
        intro h2; apply hW; unfold ratDiv; rw [h1, h2, sub_zero]
      exact le_and_isRelevant_of_divCycle_ne_zero h2
    · exact le_and_isRelevant_of_divCycle_ne_zero h1
  obtain ⟨u, v, hu, hv, h⟩ := hunit W hsupp.1 hsupp.2.1 hsupp.2.2 hϖ
  apply hW
  unfold ratDiv
  rw [divCycle_eq_of_mul_sub_mem hu hv h, sub_self]

end Vertical

section Graded

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R] {τ : Type*}

end Graded

section BlowUp

variable {O : Type*} [CommRing O]

end BlowUp

section BlowUpModel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end BlowUpModel

section Nodal

variable {O : Type*} [CommRing O] [IsDomain O]

end Nodal

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Algebra Cardinal Set

noncomputable section

theorem AdjoinTrdegAdd.trdeg_adjoin_eq_of_family {R L κ : Type} [CommRing R] [CommRing L] [IsDomain L]
    [Algebra R L] (u : Set L) (w : κ → L) (hwu : range w ⊆ u) (hw : AlgebraicIndependent R w)
    (halg : ∀ a ∈ u, IsAlgebraic (adjoin R (range w)) a) :
    trdeg R (adjoin R u) = #κ := by
  have := (algebraMap R L).domain_nontrivial
  let v : κ → adjoin R u := fun i => ⟨w i, subset_adjoin (hwu ⟨i, rfl⟩)⟩
  have hv : AlgebraicIndependent R v := AlgebraicIndependent.of_comp (adjoin R u).val hw
  have heq : (adjoin R (range v)).map (adjoin R u).val = adjoin R (range w) := by
    rw [AlgHom.map_adjoin, ← range_comp]
    rfl
  let e := ((adjoin R (range v)).equivMapOfInjective (adjoin R u).val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ heq)
  have hval : Algebra.IsAlgebraic (adjoin R (range v)) (adjoin R u) := by
    refine ⟨fun a => ?_⟩
    have h0 : IsAlgebraic (adjoin R u) (a : L) := isAlgebraic_algebraMap a
    have h1 : IsAlgebraic (adjoin R (range w)) ((adjoin R u).val a) :=
      h0.adjoin_of_forall_isAlgebraic fun y hy => halg y hy.1
    exact (isAlgebraic_ringHom_iff_of_comp_eq e (adjoin R u).val Subtype.val_injective
      (by ext; rfl)).mp h1
  exact ((isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    ⟨hv, hval⟩).cardinalMk_eq_trdeg).symm

theorem AdjoinTrdegAdd.proof : AdjoinTrdegAdd.Statement := by
  intro R _ L _ _ _ hinj s t ι _ x hxt hx hxalg
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hinj
  obtain ⟨b, hb⟩ := (AlgebraicIndependent.matroid R L).exists_isBasis s (by simp)
  obtain ⟨hbi, hbs, hbalg⟩ := AlgebraicIndependent.matroid_isBasis_iff.mp hb
  have hbi' : AlgebraicIndependent R ((↑) : b → L) := hbi

  have h1 : trdeg R (adjoin R s) = #b :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family s ((↑) : b → L) (by rw [Subtype.range_coe]; exact hbs) hbi'
      (by rw [Subtype.range_coe]; exact hbalg)

  let _ : Algebra (adjoin R b) (adjoin R s) := (Subalgebra.inclusion (adjoin_mono hbs)).toAlgebra
  have : IsScalarTower (adjoin R b) (adjoin R s) L := .of_algebraMap_eq fun _ => rfl
  have hxb : AlgebraicIndependent (adjoin R (range ((↑) : b → L))) x := by
    rw [Subtype.range_coe]
    exact hx.restrictScalars (Subalgebra.inclusion_injective _)
  have hsum : AlgebraicIndependent R (Sum.elim x ((↑) : b → L)) :=
    AlgebraicIndependent.sumElim_iff.mpr ⟨hbi', hxb⟩
  have hrange : range (Sum.elim x ((↑) : b → L)) = range x ∪ b := by
    rw [Set.Sum.elim_range, Subtype.range_coe]

  have hs : ∀ a ∈ s, IsAlgebraic (adjoin R (range x ∪ b)) a := fun a ha =>
    (hbalg a ha).adjoin_of_forall_isAlgebraic fun y hy => (hy.2 (Or.inr hy.1)).elim
  have hst : ∀ a ∈ s ∪ t, IsAlgebraic (adjoin R (range (Sum.elim x ((↑) : b → L)))) a := by
    rw [hrange]
    rintro a (ha | ha)
    · exact hs a ha
    · refine (hxalg a ha).adjoin_of_forall_isAlgebraic fun y hy => ?_
      rcases hy.1 with hy1 | hy1
      · exact hs y hy1
      · exact (hy.2 (Or.inl hy1)).elim
  have h2 : trdeg R (adjoin R (s ∪ t)) = #(ι ⊕ b) :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family (s ∪ t) (Sum.elim x ((↑) : b → L))
      (by rw [hrange]; exact union_subset (hxt.trans subset_union_right) (hbs.trans subset_union_left))
      hsum hst
  rw [h2, h1, mk_sum, lift_id, lift_id, mk_fintype, add_comm]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequality
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Cardinal

theorem DimensionInequality.tower_step {A : Type u} {C B : Type v} [CommRing A] [CommRing C]
    [CommRing B] [IsDomain A] [IsDomain C] [IsDomain B] [Algebra A C] [Algebra C B] [Algebra A B]
    [IsScalarTower A C B] (hAC : Function.Injective (algebraMap A C))
    (hCB : Function.Injective (algebraMap C B)) (P : Ideal B) [P.IsPrime] (Q : Ideal C) [Q.IsPrime]
    (p : Ideal A) [p.IsPrime] [P.LiesOver Q] [Q.LiesOver p] [P.LiesOver p]
    (e₁ : ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q) ≤ ofENat p.height + Algebra.trdeg A C)
    (e₂ : ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P) ≤ ofENat Q.height + Algebra.trdeg C B) :
    ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B := by
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hAC
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective C B).mpr hCB
  have : IsScalarTower (A ⧸ p) (C ⧸ Q) (B ⧸ P) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]
  have t₁ := trdeg_add_eq A C (A := B)
  have t₂ := trdeg_add_eq (A ⧸ p) (C ⧸ Q) (A := B ⧸ P)
  calc ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P)
      = (ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P)) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by
        rw [← t₂]; ring
    _ ≤ (ofENat Q.height + Algebra.trdeg C B) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by gcongr
    _ = (ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q)) + Algebra.trdeg C B := by ring
    _ ≤ (ofENat p.height + Algebra.trdeg A C) + Algebra.trdeg C B := by gcongr
    _ = ofENat p.height + Algebra.trdeg A B := by rw [add_assoc, t₁]

theorem DimensionInequality.proof (h₁ : DimensionInequalityOneGenerator.Statement.{u, v})
    (h₂ : DimensionInequalityOneGenerator.Statement.{v, v}) :
    DimensionInequality.Statement.{u, v} := by
  classical
  intro A B _ _ _ _ _ _ _ hinj P _

  suffices key : ∀ (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] (x : Fin n → B),
      Algebra.adjoin A (Set.range x) = ⊤ → Function.Injective (algebraMap A B) →
      ∀ (P : Ideal B) [P.IsPrime] (p : Ideal A) [p.IsPrime] [P.LiesOver p],
        ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B by
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
    refine key s.card B (fun i ↦ (s.equivFin.symm i : B)) ?_ hinj P (P.under A)
    rw [← hs]
    congr 1
    ext b
    refine ⟨?_, fun hb ↦ ⟨s.equivFin ⟨b, hb⟩, by simp⟩⟩
    rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  intro n
  induction n with
  | zero =>
    intro B _ _ _ x hx hinj P _ p _ _
    obtain rfl : p = P.under A := Ideal.LiesOver.over
    refine h₁ A B 0 ?_ hinj P
    rw [eq_top_iff, ← hx]
    exact Algebra.adjoin_mono (by simp [Set.range_eq_empty])
  | succ n ih =>
    intro B _ _ _ x hx hinj P _ p _ _
    set C : Subalgebra A B := Algebra.adjoin A (Set.range (x ∘ Fin.succ)) with hC
    let y : Fin n → C := fun i ↦ ⟨x i.succ, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    have hy : Algebra.adjoin A (Set.range y) = ⊤ := by
      apply Subalgebra.map_injective (f := C.val) Subtype.val_injective
      rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
      rfl
    have hAC : Function.Injective (algebraMap A C) := fun a b hab ↦
      hinj (congrArg Subtype.val hab :)
    have hCB : Function.Injective (algebraMap C B) := Subtype.val_injective
    have : Algebra.FiniteType A C :=
      ⟨⟨Finset.univ.image y, by simpa [Finset.coe_image] using hy⟩⟩
    have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
    have hB : Algebra.adjoin C {x 0} = ⊤ := by
      apply Subalgebra.restrictScalars_injective A
      rw [Subalgebra.restrictScalars_top, ← Algebra.adjoin_union_eq_adjoin_adjoin, eq_top_iff, ← hx]
      apply Algebra.adjoin_mono
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact Or.inr rfl
      | succ j => exact Or.inl ⟨j, rfl⟩
    have : (P.under C).LiesOver p := Ideal.LiesOver.tower_bot P (P.under C) p
    exact DimensionInequality.tower_step hAC hCB P (P.under C) p
      (ih C y hy hAC (P.under C) p) (h₂ C B (x 0) hB hCB P)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequalityOneGenerator
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Polynomial Cardinal

theorem DimensionInequalityOneGenerator.proof (h₁ : PolynomialDimensionInequality.Statement.{u})
    (h₂ : QuotientHeightAddOne.Statement.{u}) : DimensionInequalityOneGenerator.Statement.{u, v} := by
  intro A B _ _ _ _ _ _ x hx hinj P _

  let φ : A[X] →ₐ[A] B := aeval x
  have hφ : Function.Surjective φ := by
    intro b
    have hb : b ∈ (aeval x : A[X] →ₐ[A] B).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]; exact Algebra.mem_top
    exact hb

  let P' : Ideal A[X] := P.comap (φ : A[X] →+* B)
  have hP' : P.under A = P'.under A := by
    ext a; simp [P', φ, Ideal.under, Ideal.mem_comap]
  have : P'.LiesOver (P.under A) := ⟨hP'⟩

  have H₁ : ofENat P'.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P') ≤
      ofENat (P.under A).height + 1 := by
    have key : ∀ (q : Ideal A) [q.IsPrime] [P'.LiesOver q],
        ofENat P'.height + Algebra.trdeg (A ⧸ q) (A[X] ⧸ P') ≤ ofENat q.height + 1 := by
      intro q _ _
      obtain rfl : q = P'.under A := Ideal.LiesOver.over
      exact h₁ A P'
    exact key _

  have htr : lift.{v} (Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P')) =
      lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
    let f : A[X] ⧸ P' →+* B ⧸ P := Ideal.quotientMap P (φ : A[X] →+* B) le_rfl
    have hf : Function.Bijective f :=
      ⟨Ideal.quotientMap_injective' le_rfl, Ideal.quotientMap_surjective hφ⟩
    refine AlgEquiv.lift_trdeg_eq
      (AlgEquiv.ofRingEquiv (f := (RingEquiv.ofBijective f hf : A[X] ⧸ P' ≃+* B ⧸ P)) ?_)
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp [f, φ, Ideal.Quotient.algebraMap_mk_of_liesOver]

  have H₁' : ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) ≤
      ofENat (P.under A).height + 1 := by
    have := Cardinal.lift_le.{v}.mpr H₁
    simpa only [lift_add, lift_ofENat, lift_one, htr] using this
  rw [← Cardinal.lift_le.{u}]
  simp only [lift_add, lift_ofENat]
  by_cases hker : RingHom.ker φ = ⊥
  ·
    have hinjφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot _).mpr hker
    let e : A[X] ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hinjφ, hφ⟩
    have hh : P'.height = P.height := RingEquiv.height_comap (e : A[X] ≃+* B) P
    have ht : lift.{u} (Algebra.trdeg A B) = 1 := by
      rw [← e.lift_trdeg_eq, Polynomial.trdeg_of_isDomain, lift_one]
    rw [ht, ← hh]
    exact H₁'
  ·
    let e := Ideal.quotientKerAlgEquivOfSurjective hφ
    let Q : Ideal (A[X] ⧸ RingHom.ker φ) := P.comap (e : A[X] ⧸ RingHom.ker φ ≃+* B)
    have hQ : Q.comap (Ideal.Quotient.mk (RingHom.ker φ)) = P' := by
      ext f; simp [Q, P', e, Ideal.mem_comap]
    have H₂ := h₂ A[X] (RingHom.ker φ) hker Q
    rw [hQ, RingEquiv.height_comap] at H₂
    have H : ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1 ≤
        ofENat (P.under A).height + 1 :=
      calc ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1
          = ofENat (P.height + 1) + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
            rw [ofENat_add, ofENat_one]; ring
        _ ≤ ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) :=
            add_le_add (ofENat_le_ofENat.mpr H₂) le_rfl
        _ ≤ _ := H₁'
    exact (Cardinal.add_one_le_add_one_iff.mp H).trans le_self_add

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem height_eq_of_isMaximal_mvPolynomial_fin (F : Type u) [Field F] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) F)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simp at h
    simpa [h]
  | succ n ih =>
    intro M hM
    let e := (finSuccEquiv F n).toRingEquiv
    rw [← e.height_map M]
    set P : Ideal (Polynomial (MvPolynomial (Fin n) F)) := M.map e with hPdef
    have hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hc : (P.comap (Polynomial.C : MvPolynomial (Fin n) F →+* _)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have hlo : P.LiesOver (P.under (MvPolynomial (Fin n) F)) := ⟨rfl⟩
    rw [Polynomial.height_eq_height_add_one (P.under (MvPolynomial (Fin n) F)) P,
      ih (P.under (MvPolynomial (Fin n) F)) hc]
    norm_cast

theorem MaximalIdealHeightFG.proof : MaximalIdealHeightFG.Statement.{u} := by
  intro F _ A _ _ _ _ m hm
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg F A
  let _ : Algebra (MvPolynomial (Fin s) F) A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) F) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) F) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : m.IsPrime := hm.isPrime
  have hR : ringKrullDim (MvPolynomial (Fin s) F) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdim : ringKrullDim A ≤ s := by
    rw [← hR]
    refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin s) F) A)) fun p q hpq => ?_
    exact Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin s) F) hpq
  let n := m.under (MvPolynomial (Fin s) F)
  have : n.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown n m
  rw [height_eq_of_isMaximal_mvPolynomial_fin F s n inferInstance] at h1
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) (hdim.trans ?_)
  rw [h1]
  exact_mod_cast le_self_add

end GroundTheory.Heights₂.Heights.NumbersDVR
end

