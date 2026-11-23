module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0016
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopCountLowerBoundsOfOccurrence

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantMultihomogeneous
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem degAt_ph_detPl {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (j x : ℤ) (t : Fin n') :
    DegAt t (∑ a : Fin r, if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)
      (phSeg R K p X.F j (plEmb R r K (X.detPl R j x))) := by
  have key : ∀ σ : Equiv.Perm (Fin r), DegAt t
      (∑ a : Fin r, if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)
      (∏ i : Fin r, phSeg R K p X.F j (plEmb R r K (MvPolynomial.X (X.row j x (σ i), i)))) := by
    intro σ
    rw [← Equiv.sum_comp σ (fun a => if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)]
    apply degAt_prod
    intro i _
    simp only [plEmb, phSeg, rename_X, aeval_X]
    have h := degAt_pow (R := R) (degAt_X (x := t) (posOf n' (X.row j x (σ i)), Fin.castAdd K i))
      (p ^ X.F.dist j (X.row j x (σ i)))
    convert h using 2
    split_ifs <;> simp
  unfold Dat.detPl
  rw [Matrix.det_apply']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, Matrix.of_apply, map_intCast]
  apply degAt_sum
  intro σ _
  have e : ((Equiv.Perm.sign σ : ℤ) : RRing R n' (r + K)) = C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  rw [e]
  exact degAt_C_mul _ (key σ)

theorem discriminant_multihomogeneous : DiscriminantMultihomogeneous := by
  intro p n' r K _ _ _ X O _
  rw [RRdeg, mem_restrictSupport_iff]
  intro m hm t
  have hdeg : DegAt t (X.Et p K t) (X.Dl p K O) := by
    unfold Dat.Dl Dat.DlSeg Dat.Et
    simp only [map_prod, map_pow]
    apply degAt_prod
    intro j _
    apply degAt_prod
    intro x _
    exact degAt_pow (degAt_ph_detPl X p K j x t) _
  exact hdeg m hm

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopOccursInAtMostTwoSegments
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Occ

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

open Classical in
theorem occ_Ioc (hV : F.Valid L₁ N₁) (c : ℤ) (t : Fin n') :
    ∑ j ∈ Finset.range F.J, ((Finset.Ioc (eFr F ((j : ℤ) + c)) (eFr F (((j + 1 : ℕ) : ℤ) + c))).filter
      fun y => posOf n' y = t).card ≤ 1 := by
  have hm := eFr_strictMono hV
  have h3 := sum_card_Ioc (fun i : ℕ => eFr F ((i : ℤ) + c)) (fun a b hab => hm.monotone (by omega))
    (fun y => posOf n' y = t) F.J
  rw [h3]
  have h2 : eFr F ((F.J : ℤ) + c) = eFr F (((0 : ℕ) : ℤ) + c) + n' := by
    have := hV.2.1 c (r - 1)
    simp only [eFr]
    rw [show (F.J : ℤ) + c = c + F.J by ring, show ((0 : ℕ) : ℤ) + c = c by simp, this]
  simp only [h2]
  rw [Finset.card_le_one]
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact posOf_injOn _ (Finset.mem_Ioc.mp ha'.1) (Finset.mem_Ioc.mp hb'.1) (ha'.2.trans hb'.2.symm)

end Occ

theorem top_occurs_in_at_most_two_segments : LeadingLetterInAtMostTwoSegments := by
  intro p n' r K _ _ _ X hX t
  classical
  have hV := hX.valid
  have h1 := occ_Ioc hV (-2) t
  have h2 := occ_Ioc hV (-1) t
  have key : ∀ j ∈ Finset.range X.F.J, ((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card ≤
      ((Finset.Ioc (eFr X.F ((j : ℤ) + -2)) (eFr X.F (((j + 1 : ℕ) : ℤ) + -2))).filter fun y => posOf n' y = t).card +
      ((Finset.Ioc (eFr X.F ((j : ℤ) + -1)) (eFr X.F (((j + 1 : ℕ) : ℤ) + -1))).filter fun y => posOf n' y = t).card := by
    intro j _
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro y hy
    obtain ⟨hyl, hyt⟩ := Finset.mem_filter.mp hy
    have hb := mem_letters_bounds hyl
    have e1 : ((j + 1 : ℕ) : ℤ) + -2 = (j : ℤ) - 1 := by push_cast; ring
    have e2 : ((j + 1 : ℕ) : ℤ) + -1 = (j : ℤ) := by push_cast; ring
    have e3 : (j : ℤ) + -1 = (j : ℤ) - 1 := by ring
    have h4 := hV.2.2.2.1 ((j : ℤ) + -2)
    have e4 : (j : ℤ) + -2 + 1 = (j : ℤ) - 1 := by ring
    rw [e4] at h4
    rw [e1, e2, e3, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
    simp only [eFr]
    by_cases hc : y ≤ X.F.fr ((j : ℤ) - 1) (r - 1)
    · exact Or.inl ⟨⟨lt_of_lt_of_le h4 hb.1, hc⟩, hyt⟩
    · exact Or.inr ⟨⟨not_le.mp hc, hb.2.1⟩, hyt⟩
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [Finset.sum_add_distrib]
  omega

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

