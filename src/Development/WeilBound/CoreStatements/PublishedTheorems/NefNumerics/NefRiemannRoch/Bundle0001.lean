module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.IntersectionNefAmpleNonnegStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.IntersectionNumberNonnegEffective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmpleNefCombinationBound
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefLower

theorem topSelf_lower : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (A N L : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hL : IsAmpleLB L), (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) → ∀ a b : ℕ, cls L hL.isLB = a • cls N hN.isLB + b • cls A hA.isLB → (b : ℤ) ^ (d + 1) * topSelfIntersection k A (d + 1) ≤ topSelfIntersection k L (d + 1) := by
  intro k _ _ X _ hX d hdim A N L hA hN hL hyp a b hcls
  have hsupp : suppDim (GlobalTheory.structureModule X) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (QCoh.suppDim_le _).trans hdim
  have hDV : DiffVanish (d + 1 + 1) (chiPic k (GlobalTheory.structureModule X)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hX hsupp
  have hALB : A.IsLB := hA.isLB
  have hNLB : N.IsLB := hN.isLB
  have hLLB : L.IsLB := hL.isLB
  set R : Fin d → LB X := fun _ => L with hR
  have hL0 : (fun _ : Fin (d + 1) => L) = (Fin.cons L R : Fin (d + 1) → LB X) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hconsLB : ∀ M : LB X, M.IsLB → ∀ i, ((Fin.cons M R : Fin (d + 1) → LB X) i).IsLB :=
    fun M hM i => Fin.cases hM (fun _ => hLLB) i
  have hadd := DiffVanish.interNum_update_of_cls_eq_add hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB L hLLB) 0 hLLB (isLB_lbPow hNLB a) (isLB_lbPow hALB b)
    (by rw [cls_lbPow hNLB, cls_lbPow hALB]; exact hcls)
  simp only [Fin.update_cons_zero] at hadd
  have hsN := DiffVanish.interNum_update_of_cls_eq_zsmul hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB N hNLB) 0 (isLB_lbPow hNLB a) hNLB (a : ℤ) (by rw [cls_lbPow hNLB]; simp)
  have hsA := DiffVanish.interNum_update_of_cls_eq_zsmul hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB A hALB) 0 (isLB_lbPow hALB b) hALB (b : ℤ) (by rw [cls_lbPow hALB]; simp)
  simp only [Fin.update_cons_zero] at hsN hsA
  have hNpos : 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons N R : Fin (d + 1) → LB X) :=
    T.intersection_nef_ample_nonneg k X hX d _ hsupp N R hN (fun _ => hL)
  have hfam : ∀ j, ((![A, N] : Fin 2 → LB X) j).IsLB := fun j => by
    fin_cases j
    · exact hALB
    · exact hNLB
  have hQLB : ∀ i, ((Fin.cons A R : Fin (d + 1) → LB X) i).IsLB := hconsLB A hALB
  let n : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![1, 0] (fun _ => ![(b : ℤ), (a : ℤ)])
  have hexp := DiffVanish.interNum_of_cls_eq_sum hDV hfam hQLB n (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [n, Fin.sum_univ_two]
    · simp only [n, Fin.sum_univ_two, Fin.cons_succ]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, natCast_zsmul]
      show cls L _ = _
      rw [hcls, add_comm])
  have hterm : ∀ α : Fin (d + 1) → Fin 2,
      0 ≤ (∏ i, n i (α i)) * interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α) := by
    intro α
    have hprod : 0 ≤ ∏ i, n i (α i) := by
      refine Finset.prod_nonneg fun i _ => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [n, Fin.cons_zero]
        generalize α 0 = t
        fin_cases t <;> simp
      · simp only [n, Fin.cons_succ]
        generalize α j.succ = t
        fin_cases t <;> simp
    rcases Fin.exists_fin_two.mp ⟨α 0, rfl⟩ with h0 | h0
    · refine mul_nonneg hprod ?_
      have hcomp : ((![A, N] : Fin 2 → LB X) ∘ α) =
          Fin.cons A (fun j : Fin d => (![A, N] : Fin 2 → LB X) (α j.succ)) := by
        funext i
        refine Fin.cases ?_ (fun j => rfl) i
        simp [h0]
      rw [hcomp]
      refine hyp _ (fun j => ?_)
      generalize α j.succ = t
      fin_cases t
      · exact hA.isNef
      · exact hN
    · have hz : (∏ i, n i (α i)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ 0) ?_
        simp [n, h0]
      rw [hz, zero_mul]
  let α0 : Fin (d + 1) → Fin 2 := fun _ => 0
  have hsingle : (∏ i, n i (α0 i)) *
      interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α0) ≤
      interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) := by
    rw [hexp]
    exact Finset.single_le_sum (fun α _ => hterm α) (Finset.mem_univ α0)
  have hprod0 : (∏ i, n i (α0 i)) = (b : ℤ) ^ d := by
    rw [Fin.prod_univ_succ]
    simp [n, α0]
  have hA0 : interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α0) =
      topSelfIntersection k A (d + 1) := by
    rw [topSelf_def]; rfl
  rw [hprod0, hA0] at hsingle
  rw [topSelf_def k L, hL0, hadd, hsN, hsA]
  have hb : (0 : ℤ) ≤ b := by positivity
  have ha : (0 : ℤ) ≤ a := by positivity
  calc (b : ℤ) ^ (d + 1) * topSelfIntersection k A (d + 1)
      = (b : ℤ) * ((b : ℤ) ^ d * topSelfIntersection k A (d + 1)) := by ring
    _ ≤ (b : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) :=
        mul_le_mul_of_nonneg_left hsingle hb
    _ ≤ (a : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons N R : Fin (d + 1) → LB X) +
        (b : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) := by
        have := mul_nonneg ha hNpos
        linarith

end GlobalTheory.NefLower
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegInduction
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.KleimanDim

theorem interNum_nonneg_of_ample_tens_nef : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ),
    (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) →
      ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) →
    ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) →
      (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X,
        (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) := by
  intro k _ _ d H X _ hX E _ hE P hP
  refine SheafCycle.interNum_nonneg_of_interNumRed_nonneg k X hX d E hE P (fun i => (hP i).isLB) ?_
  intro Z hZirr hZdim
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
    ((redι Z).appTop.hom.comp (algebraMap k Γ(X, ⊤))).toAlgebra
  have hcompat : ∀ r : k, (redι Z).appTop.hom (algebraMap k Γ(X, ⊤) r) =
      algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r => rfl
  rw [InterModel.interNumRed_eq_interNumOn k (redι Z) Z (range_redι Z) P,
    interNumOn_eq_interNum_pull hcompat (fun i => (hP i).isLB)]
  have hYproj : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom hcompat]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion (redι Z) hX
  have hYdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (d : WithBot ℕ∞) := by
    have hmem : ∀ y, (redι Z) y ∈ (Z : Set X) := fun y => by
      rw [← range_redι Z]; exact Set.mem_range_self y
    have hind := ((redι Z).isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le
    rw [hZdim] at hind
    exact hind
  have hsupp : suppDim (QCoh.structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ≤ (d : WithBot ℕ∞) :=
    (QCoh.suppDim_le _).trans hYdim
  exact T.intersectionNumber_nonneg_of_nef_ample_add_nef k _ hYproj (fun A N hA hN => H _ hYproj hYdim A N hA hN) d _ hsupp
    (fun i => (P i).pull (redι Z)) (fun i => (hP i).pull_of_isClosedImmersion (redι Z) hcompat)

end GlobalTheory.KleimanDim
end

