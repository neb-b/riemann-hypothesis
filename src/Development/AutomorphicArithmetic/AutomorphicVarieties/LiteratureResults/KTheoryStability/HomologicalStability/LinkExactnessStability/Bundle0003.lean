module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainExactAtMapIff
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxMap

theorem bd_mapDomain {V W : Type} (e : V → W) (c : List V →₀ ℤ) :
    bd W (Finsupp.lmapDomain ℤ ℤ (List.map e) c) = Finsupp.lmapDomain ℤ ℤ (List.map e) (bd V c) := by
  have key : (bd W).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) =
      (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V) := by
    apply Finsupp.lhom_ext
    intro l n
    simp [bd, Finsupp.linearCombination_single, Finsupp.mapDomain_single, Finset.smul_sum,
      Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_smul, List.eraseIdx_map,
      ← Finsupp.single_mul]
  exact LinearMap.congr_fun key c

theorem chains_map {V W : Type} (e : V → W) (F : Set (List V)) (q : ℕ) :
    chains (List.map e '' F) q = (chains F q).map (Finsupp.lmapDomain ℤ ℤ (List.map e)) := by
  unfold chains
  rw [Finsupp.lmapDomain_supported]
  congr 1
  ext l
  constructor
  · rintro ⟨⟨l', hl', rfl⟩, hlen⟩
    exact ⟨l', ⟨hl', by simpa using hlen⟩, rfl⟩
  · rintro ⟨l', ⟨hl', hlen⟩, rfl⟩
    exact ⟨⟨l', hl', rfl⟩, by simpa using hlen⟩

end GlobalTheory.SeqCxMap

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_exactAt_map_iff : ∀ (V W : Type) (e : V → W), Function.Injective e → ∀ (F : Set (List V)) (p : ℕ), ExactAt (List.map e '' F) p ↔ ExactAt F p := by
  intro V W e he F p
  have hinj : Function.Injective (Finsupp.lmapDomain ℤ ℤ (List.map e)) := by
    intro x y hxy
    exact Finsupp.mapDomain_injective (List.map_injective_iff.mpr he) hxy
  unfold GlobalTheory.SeqCx.ExactAt
  constructor
  · intro h c hc hbc
    obtain ⟨b, hb, hbb⟩ := h (Finsupp.lmapDomain ℤ ℤ (List.map e) c)
      (by rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hc)
      (by rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero])
    rw [GlobalTheory.SeqCxMap.chains_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨b', hb', hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain]; exact hbb)⟩
  · intro h c hc hbc
    rw [GlobalTheory.SeqCxMap.chains_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨b', hb', hbb⟩ := h c' hc'
      (hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero]))
    refine ⟨Finsupp.lmapDomain ℤ ℤ (List.map e) b', ?_, ?_⟩
    · rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hb'
    · rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbb]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ShapiroIsIsoGroupHomologyZero
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.ShapiroZero

theorem H0π_smul {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) (v : B.V) :
    (groupHomology.H0π B).hom (B.ρ g v) = (groupHomology.H0π B).hom v := by
  have e : ∀ w : B.V, (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom w) =
      Representation.Coinvariants.mk B.ρ w :=
    fun w => congrArg (fun f => ModuleCat.Hom.hom f w) (groupHomology.H0π_comp_H0Iso_hom B)
  have hinj : Function.Injective (groupHomology.H0Iso B).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [e, e, Representation.Coinvariants.mk_self_apply]

theorem linkExactnessStability_hom_fact {k G : Type} [CommRing k] [Group G] (B : Rep k G) (v : B.V) :
    (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom v) = Representation.Coinvariants.mk B.ρ v := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_H0Iso_hom B)
  exact h

end GlobalTheory.HomStab.ShapiroZero


open GlobalTheory.HomStab.ShapiroZero in
theorem GlobalTheory.HomStab.isIso_map_ptMap_zero : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X)
    (hx : ∀ h, φ h • x = x), φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) →
    ∀ A : Rep k G, IsIso (groupHomology.map φ (ptMap φ x hx A) 0) := by
  intro k G H X _ _ _ _ φ x hx hrange htrans A
  choose s hs using htrans
  have stab : ∀ g : G, g • x = x → ∃ h : H, φ h = g := fun g hg => by
    have hmem : g ∈ φ.range := by
      rw [hrange]
      exact hg
    exact hmem
  have key : ∀ v : A.V, (groupHomology.map φ (ptMap φ x hx A) 0).hom
      ((groupHomology.H0π (Rep.res φ A)).hom v) =
      (groupHomology.H0π (permT X A)).hom (Finsupp.single x v) :=
    fun v => congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_map φ (ptMap φ x hx A))
  have resInv : ∀ (h : H) (b : A.V), (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (φ h) b) =
      (groupHomology.H0π (Rep.res φ A)).hom b :=
    fun h b => GlobalTheory.HomStab.ShapiroZero.H0π_smul (Rep.res φ A) h b
  have permInv : ∀ (g : G) (w : (permT X A).V), (groupHomology.H0π (permT X A)).hom ((permT X A).ρ g w) =
      (groupHomology.H0π (permT X A)).hom w :=
    fun g w => GlobalTheory.HomStab.ShapiroZero.H0π_smul (permT X A) g w
  have piRes : Function.Surjective (groupHomology.H0π (Rep.res φ A)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have piPerm : Function.Surjective (groupHomology.H0π (permT X A)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have act : ∀ (g : G) (y : X) (a : A.V),
      (permT X A).ρ g (Finsupp.single y a) = Finsupp.single (g • y) (A.ρ g a) := by
    intro g y a
    simp [permT, permRep]
  let L : (X →₀ A.V) →ₗ[k] groupHomology (Rep.res φ A) 0 :=
    Finsupp.lsum k (fun y => (groupHomology.H0π (Rep.res φ A)).hom ∘ₗ (A.ρ (s y)⁻¹))
  have Lsingle : ∀ y a, L (Finsupp.single y a) = (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a) := by
    intro y a
    simp [L]
  have hL : ∀ g : G, L ∘ₗ (permT X A).ρ g = L := by
    intro g
    ext y a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [act, Lsingle, Lsingle]
    have ht : ((s (g • y))⁻¹ * g * s y) • x = x := by
      rw [mul_smul, mul_smul, hs y, inv_smul_eq_iff, hs]
    obtain ⟨h, hh⟩ := stab _ ht
    have e : A.ρ (s (g • y))⁻¹ (A.ρ g a) = A.ρ (φ h) (A.ρ (s y)⁻¹ a) := by
      rw [hh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, resInv]
  let N : groupHomology (permT X A) 0 →ₗ[k] groupHomology (Rep.res φ A) 0 :=
    Representation.Coinvariants.lift (permT X A).ρ L hL ∘ₗ (groupHomology.H0Iso (permT X A)).hom.hom
  have NM : ∀ v : A.V, N ((groupHomology.map φ (ptMap φ x hx A) 0).hom
      ((groupHomology.H0π (Rep.res φ A)).hom v)) = (groupHomology.H0π (Rep.res φ A)).hom v := by
    intro v
    rw [key]
    simp only [N, LinearMap.comp_apply]
    rw [GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact, Representation.Coinvariants.lift_mk, Lsingle]
    obtain ⟨h, hh⟩ := stab (s x)⁻¹ (by rw [inv_smul_eq_iff, hs])
    rw [← hh, resInv]
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (groupHomology.map φ (ptMap φ x hx A) 0).hom
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨v, rfl⟩ := piRes a
    obtain ⟨w, rfl⟩ := piRes b
    have hN := congrArg N hab
    rw [NM, NM] at hN
    exact hN
  · intro z
    obtain ⟨w, rfl⟩ := piPerm z
    induction w using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add u w hu hw =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩
    | single y a =>
      refine ⟨(groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a), ?_⟩
      rw [key, ← permInv (s y), act, hs, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.shapiro_isIso_groupHomology_zero : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → ∀ A : Rep k G, IsIso (groupHomology.map φ (ptMap φ x hx A) 0) := by
  first
  | exact @GlobalTheory.HomStab.isIso_map_ptMap_zero
  | exact @GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact
  | exact @GlobalTheory.HomStab.ShapiroZero.H0π_smul
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedSplitSeqAndUniSeqWithMemIff
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem mem_splitSeq_iff_pairwise (R : Type) [CommRing R] (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))) :
    l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧
      l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0 := by
  simp only [splitSeq, Set.mem_setOf_eq, List.pairwise_iff_get]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun i j hij => ⟨?_, ?_⟩⟩
    · obtain ⟨i, rfl⟩ := List.get_of_mem hy
      simpa using h i i
    · simpa [hij.ne] using h i j
    · simpa [hij.ne'] using h j i
  · rintro ⟨h1, h2⟩ i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_neg hij.ne]
      exact (h2 i j hij).1
    · rw [if_pos rfl]
      exact h1 _ (List.get_mem _ _)
    · rw [if_neg hij.ne']
      exact (h2 j i hij).2

theorem splitSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (splitSeq R n) := by
  intro l hl l' hs
  rw [mem_splitSeq_iff_pairwise] at hl ⊢
  exact ⟨fun y hy => hl.1 y (hs.subset hy), hl.2.sublist hs⟩

theorem mem_uniSeq_iff_exists_split (R : Type) [CommRing R] (n : ℕ) (w : List (Fin n → R)) :
    w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨List.ofFn fun i => (w.get i, f i), ?_, ?_⟩
    · intro i j
      have hi : (i : ℕ) < w.length := by simpa using i.2
      have hj : (j : ℕ) < w.length := by simpa using j.2
      have := hf ⟨i, hi⟩ ⟨j, hj⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn] at this ⊢
      simpa [Fin.ext_iff] using this
    · simp [List.map_ofFn]
      exact List.ofFn_get w
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun i => (l.get ⟨i, by simpa using i.2⟩).2, fun i j => ?_⟩
    have := hl ⟨i, by simpa using i.2⟩ ⟨j, by simpa using j.2⟩
    simp only [List.get_eq_getElem, List.getElem_map] at this ⊢
    simpa [Fin.ext_iff] using this

theorem uniSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (uniSeq R n) := by
  intro w hw w' hs
  rw [mem_uniSeq_iff_exists_split] at hw ⊢
  obtain ⟨l, hl, rfl⟩ := hw
  obtain ⟨l', hl', rfl⟩ := List.sublist_map_iff.mp hs
  exact ⟨l', splitSeq_sublist_closed R n l hl l' hl', rfl⟩

end GlobalTheory.SeqCx

theorem GlobalTheory.SeqCx.split_uni_closed : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) :=
  fun R _ n => ⟨splitSeq_sublist_closed R n, uniSeq_sublist_closed R n, mem_splitSeq_iff_pairwise R n, mem_uniSeq_iff_exists_split R n⟩

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) := by
  first
  | exact @GlobalTheory.SeqCx.split_uni_closed
  | exact @GlobalTheory.SeqCx.uniSeq_sublist_closed
  | exact @GlobalTheory.SeqCx.mem_uniSeq_iff_exists_split
  | exact @GlobalTheory.SeqCx.splitSeq_sublist_closed
  | exact @GlobalTheory.SeqCx.mem_splitSeq_iff_pairwise
end
end

