module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GLTransitiveSplitSetOfStableRangeLe

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInSuccUnionTranslateOfNeNil
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem uniM_map_equiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    {τ : List M} (hτ : τ ∈ uniM R M) : τ.map ψ ∈ uniM R M := by
  exact ((T.subClosed_and_perm_and_linearEquiv_invariant_uniM R M).2.2 ψ τ).mpr hτ

theorem linkExact_low_union_aff_of_ne_nil : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, s ≤ n →
    LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), τ ≠ [] → ∀ p : ℕ,
    p + s + τ.length ≤ n + 2 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  intro R _ s hs n hn hL j hj τ hτ hne p hp
  obtain ⟨v, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hv : [v] ∈ uniM R (ℕ →₀ R) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1 _ hτ [v] (by simp)
  obtain ⟨ψ, hlow, haff, hψv⟩ := T.exists_automorphism_preserving_translates_coord_one R s hs n hn v hv
  refine T.exactAt_linkIn_uniM_of_exactAt_map_linearEquiv R (ℕ →₀ R) ψ (low R (n + 1) ∪ aff R (n + 1) j) ?_ _ p ?_
  · intro x
    simp only [Set.mem_union, hlow, haff]
  · refine T.exactAt_link_succ_union_translate_of_coord_one R s n hL j hj _ (uniM_map_equiv ψ hτ) (ψ v) (by simp) hψv p ?_
    simpa using hp

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_linkIn_succ_union_translate_of_ne_nil : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, s ≤ n → LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), τ ≠ [] → ∀ p : ℕ, p + s + τ.length ≤ n + 2 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  first
  | exact @GlobalTheory.linkExact_low_union_aff_of_ne_nil
  | exact @GlobalTheory.uniM_map_equiv
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSeqFirstPageIsoAndDifferential
section
noncomputable section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem stab_smul_stdSeq (R : Type) [CommRing R] (n p : ℕ) (h : p ≤ n) (x : GL (Fin (n - p)) R) :
    stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p h = stdSeq R n p h := by
  have hmem : stab R (n - p) n (Nat.sub_le n p) x ∈ (stab R (n - p) n (Nat.sub_le n p)).range := ⟨x, rfl⟩
  rw [(GlobalTheory.T.stabilizer_stdSeq_iso_GL_of_complement R n p h).2] at hmem
  exact hmem

theorem firstPage_split : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ,
    ∃ e : ∀ p q, grpH (GL (Fin (n - p)) R) q ⟶ groupHomology (splitRep R n p) q,
      (∀ p q, p + s ≤ n → IsIso (e p q)) ∧
      ∀ p q, p + 1 ≤ n → e (p + 1) q ≫ hMap (splitD R n p) q =
        if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ e p q else 0 := by
  intro R _ s hs n
  refine ⟨fun p q => if h : p ≤ n then
      ptH (k := ℤ) (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p h) (stab_smul_stdSeq R n p h) q else 0, ?_, ?_⟩
  · intro p q hp
    have h : p ≤ n := by omega
    simp only [dif_pos h]
    exact (GlobalTheory.T.shapiro_lemma_transitive_groupHomology ℤ (GL (Fin n) R) (GL (Fin (n - p)) R) (SplitSet R n p)
      (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p h) (stab_smul_stdSeq R n p h)
      (GlobalTheory.T.stabilizer_stdSeq_iso_GL_of_complement R n p h).1 (GlobalTheory.T.stabilizer_stdSeq_iso_GL_of_complement R n p h).2
      (fun y => GlobalTheory.T.GL_transitive_splitSet_of_stableRangeLe R s hs n p h hp y)).2 q
  · intro p q hp
    have h0 : p ≤ n := by omega
    simp only [dif_pos hp, dif_pos h0]
    exact GlobalTheory.T.standardSeqPoint_comp_splitSeqDifferential R n p q hp (stab_smul_stdSeq R n (p + 1) hp) (stab_smul_stdSeq R n p h0)

end GlobalTheory.HomStab

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSeq_firstPage_iso_and_differential : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, ∃ e : ∀ p q, grpH (GL (Fin (n - p)) R) q ⟶ groupHomology (splitRep R n p) q, (∀ p q, p + s ≤ n → IsIso (e p q)) ∧ ∀ p q, p + 1 ≤ n → e (p + 1) q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ e p q else 0 := by
  first
  | exact @GlobalTheory.HomStab.firstPage_split
  | exact @GlobalTheory.HomStab.stab_smul_stdSeq
end
end

