module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FZEqConstMulIrreduciblePow

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem good_primes_properties (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    (∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton) ∧
    (∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p)) ∧
    (∀ (G : WT) (ta : A c), ta ∈ 𝒜 c G → ta ≠ 0 →
      {p | p ∈ d.HtOne ∧ d.nP h c G ta p ≠ 0}.Finite) ∧
    (∀ ta : A c, ta ∈ 𝒜 c d.wL → ta ≠ 0 → {p | p ∈ d.HtOne ∧ d.nPMM h c ta p ≠ 0}.Finite) := by
  classical
  have hgoodI : ∀ {p : Ideal (KTp K d.D d.N)}, p ∈ d.HtOne →
      ∀ {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)}, w ∈ d.GoodP c p →
        d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) := by
    intro p hp w hw
    rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with h1 | ⟨hadm, htriv, -⟩
    · obtain ⟨a, ha, hne⟩ := hw.2
      exact absurd (h1 a ha) hne
    · exact ⟨hadm, htriv⟩

  have hcover : ∀ (V : Set (AddValuation (Ω c) (WithTop ℤ))), V.Finite →
      ∀ S : Set (Ideal (KTp K d.D d.N)),
        (∀ p ∈ S, p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w ∈ V) → S.Finite := by
    intro V hV S hS
    have hfin : (⋃ v ∈ V, {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}).Finite := by
      refine hV.biUnion fun v _ => ?_
      by_cases hv' : d.admitted c v ∧ IsTrivOn K v
      · exact (d.AdmissibleValuationPrimeUnique hd h c v hv'.1 hv'.2).finite
      · refine Set.Subsingleton.finite ?_
        rintro p ⟨hp, w, hw, rfl⟩
        exact absurd (hgoodI hp hw) hv'
    refine hfin.subset ?_
    intro p hpS
    obtain ⟨hp, w, hw, hwV⟩ := hS p hpS
    exact Set.mem_biUnion hwV ⟨hp, w, hw, rfl⟩
  refine ⟨d.AdmissibleValuationPrimeUnique hd h c, d.GeneratorMultiHomogeneous hd h c, ?_, ?_⟩
  · intro G ta hta hta0
    refine hcover {v | d.admitted c v ∧ d.ord c v G ta ≠ 0} (hd.a3' c hta hta0) _ ?_
    rintro p ⟨hp, hne⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hne
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    have := hcon w hw
    simp only [Set.mem_setOf_eq, not_and, not_not] at this
    rw [this (hgoodI hp hw).1, mul_zero]
  · intro ta hta hta0
    let V : Set (AddValuation (Ω c) (WithTop ℤ)) :=
      {v | d.admitted c v ∧ d.ord c v d.wL ta ≠ 0} ∪
        ⋃ j : {j // d.w j c ≠ 0}, {v | d.admitted c v ∧ d.ord c v d.wL (d.w j c) ≠ 0}
    have hV : V.Finite := (hd.a3' c hta hta0).union
      (Set.finite_iUnion fun j => hd.a3' c (hd.w_mem j c) j.2)
    refine hcover V hV _ ?_
    rintro p ⟨hp, hne⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hne
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    have hnot := hcon w hw
    have hadm := (hgoodI hp hw).1
    have h1 : d.ord c (d.Wres c w) d.wL ta = 0 := by
      by_contra h0
      exact hnot (Or.inl ⟨hadm, h0⟩)
    have h2 : ∀ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c) = 0 := by
      intro j
      by_contra h0
      exact hnot (Or.inr (Set.mem_iUnion.mpr ⟨j, hadm, h0⟩))
    haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩
    unfold ordMM
    rw [h1, show (⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c)) = 0 by
      simp only [h2, ciInf_const]]
    simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SubstitutionVanishesOfRelation
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem ratio_self' {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V} (hf : f ≠ 0) :
    ratio (Ω := Ω) f f = 1 := by
  have hex : ∃ a : Ω, f = a • f := ⟨1, (one_smul Ω f).symm⟩
  unfold ratio
  rw [dite_eq_left hex]
  have hs := hex.choose_spec
  have h0 : (hex.choose - 1) • f = 0 := by rw [sub_smul, ← hs, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hf

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def affineRowCombination (c : ι) (a : Fin (d.D + 2)) : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  ∑ k, X (a, k) * C (d.affineCoord c k)

noncomputable def pluckerSubstitution (c : ι) :
    MvPolynomial (TVar d.D d.N) (Ω c) →ₐ[Ω c] MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  aeval fun t => d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2)

theorem substitution_comp_relation (hd : d.AxH 𝒜) (c : ι) :
    (d.linearSubstitution c).comp (MvPolynomial.aeval (fun t : TVar d.D d.N =>
      (MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
        MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2)) :
          MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K))) =
      ((d.pluckerSubstitution c).restrictScalars K).comp (d.relationEliminateColumn c) := by
  have hy : d.affineCoord c (d.jc c) = 1 := ratio_self' (hd.w_base c)
  have hs : ∀ a, d.affineRowCombination c a = ∑ k, X (a, k) * C (d.affineCoord c k) := fun a => rfl
  have hphi_inl : ∀ p, d.linearSubstitution c (X (Sum.inl p)) = X p := by
    intro p
    simp [Data.linearSubstitution]
  have hphi_inr : ∀ i, d.linearSubstitution c (X (Sum.inr i)) = d.affineRowCombination c i := by
    intro i
    simp [Data.linearSubstitution, Data.affineRowCombination]
  have hrho : ∀ t : TVar d.D d.N, d.pluckerSubstitution c (X t) =
      d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2) := by
    intro t
    simp [Data.pluckerSubstitution]
  apply MvPolynomial.algHom_ext
  intro t
  simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, hphi_inl, hphi_inr,
    AlgHom.restrictScalars_apply]
  simp only [Data.relationEliminateColumn, aeval_X]
  split_ifs with ht
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum]
    simp only [map_mul, hrho, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

    have htot : ∑ k, (d.affineRowCombination c 0 * X (t.1.succ, k) - d.affineRowCombination c t.1.succ * X (0, k)) *
        C (d.affineCoord c k) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ← hs]
      ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (d.jc c)), hy, map_one, mul_one] at htot
    have hC : ∀ r, d.pluckerSubstitution c (C r) = C r := fun r => by simp [Data.pluckerSubstitution]
    have hyd : ∀ k, ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c) = d.affineCoord c k := fun k => rfl
    simp only [hC, hyd]
    rw [ht]
    linear_combination htot
  · rw [hrho]

theorem substitution_vanishes_of_relation (hd : d.AxH 𝒜) (c : ι) (Q : KTp K d.D d.N) (hQ : d.relationEliminateColumn c Q = 0) :
    d.linearSubstitution c (bilinearSubstitution Q) = 0 := by
  have h := congrArg (fun φ => φ Q) (d.substitution_comp_relation hd c)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hQ, map_zero] at h
  exact h

theorem substitution_split_irreducible (hd : d.AxH 𝒜) (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := d.substitution_split_irreducible_of c F0 hirr d0 hmh hker

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

