module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqDoubleComplexBoundaryRelations
section
open GlobalTheory.SeqCx

namespace GlobalTheory.SeqCx.DblBd

theorem single_eq_smul {α : Type} (a : α) (r : ℤ) :
    Finsupp.single a r = r • Finsupp.single a (1 : ℤ) := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem hbd_single (V W : Type) (z : List V × List W) :
    hbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.1.length, (-1 : ℤ) ^ i • Finsupp.single (z.1.eraseIdx i, z.2) (1 : ℤ) := by
  simp only [hbd, bd, Finsupp.linearCombination_single, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single, one_smul]

theorem vbd_single (V W : Type) (z : List V × List W) :
    vbd V W (Finsupp.single z 1) =
      ∑ j ∈ Finset.range z.2.length, (-1 : ℤ) ^ j • Finsupp.single (z.1, z.2.eraseIdx j) (1 : ℤ) := by
  simp only [vbd, bd, Finsupp.linearCombination_single, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single, one_smul]

theorem hbd_mapDomain (V W : Type) (w : List W) (c : List V →₀ ℤ) :
    hbd V W (Finsupp.mapDomain (fun x => (x, w)) c) = Finsupp.mapDomain (fun x => (x, w)) (bd V c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add]
  | single l r =>
    rw [Finsupp.mapDomain_single, single_eq_smul, map_zsmul, single_eq_smul l r, map_zsmul,
      Finsupp.mapDomain_smul]
    simp [hbd, Finsupp.linearCombination_single]

theorem vbd_mapDomain (V W : Type) (x : List V) (c : List W →₀ ℤ) :
    vbd V W (Finsupp.mapDomain (fun w => (x, w)) c) = Finsupp.mapDomain (fun w => (x, w)) (bd W c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add]
  | single l r =>
    rw [Finsupp.mapDomain_single, single_eq_smul, map_zsmul, single_eq_smul l r, map_zsmul,
      Finsupp.mapDomain_smul]
    simp [vbd, Finsupp.linearCombination_single]

theorem hbd_hbd (V W : Type) (x : List V × List W →₀ ℤ) : hbd V W (hbd V W x) = 0 := by
  have h : hbd V W ∘ₗ hbd V W = 0 := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul]
    have e : hbd V W (Finsupp.single z 1) =
        Finsupp.mapDomain (fun x => (x, z.2)) (bd V (Finsupp.single z.1 1)) := by
      simp [hbd, Finsupp.linearCombination_single]
    rw [e, hbd_mapDomain, bd_bd, Finsupp.mapDomain_zero, smul_zero]
  exact congrArg (fun f => f x) h

theorem vbd_vbd (V W : Type) (x : List V × List W →₀ ℤ) : vbd V W (vbd V W x) = 0 := by
  have h : vbd V W ∘ₗ vbd V W = 0 := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul]
    have e : vbd V W (Finsupp.single z 1) =
        Finsupp.mapDomain (fun w => (z.1, w)) (bd W (Finsupp.single z.2 1)) := by
      simp [vbd, Finsupp.linearCombination_single]
    rw [e, vbd_mapDomain, bd_bd, Finsupp.mapDomain_zero, smul_zero]
  exact congrArg (fun f => f x) h

theorem hbd_vbd (V W : Type) (x : List V × List W →₀ ℤ) : hbd V W (vbd V W x) = vbd V W (hbd V W x) := by
  have h : hbd V W ∘ₗ vbd V W = vbd V W ∘ₗ hbd V W := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [vbd_single, hbd_single, map_sum, map_sum]
    simp only [map_zsmul, hbd_single, vbd_single, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  exact congrArg (fun f => f x) h

end GlobalTheory.SeqCx.DblBd

namespace GlobalTheory.SeqCx

theorem dbl_bd : ∀ (V W : Type), (∀ x, hbd V W (hbd V W x) = 0) ∧ (∀ x, vbd V W (vbd V W x) = 0) ∧
    (∀ x, hbd V W (vbd V W x) = vbd V W (hbd V W x)) :=
  fun V W => ⟨DblBd.hbd_hbd V W, DblBd.vbd_vbd V W, DblBd.hbd_vbd V W⟩

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqDoubleComplex_boundary_relations : ∀ (V W : Type), (∀ x, hbd V W (hbd V W x) = 0) ∧ (∀ x, vbd V W (vbd V W x) = 0) ∧ (∀ x, hbd V W (vbd V W x) = vbd V W (hbd V W x)) := by
  first
  | exact @GlobalTheory.SeqCx.dbl_bd
  | exact @GlobalTheory.SeqCx.DblBd.hbd_vbd
  | exact @GlobalTheory.SeqCx.DblBd.vbd_vbd
  | exact @GlobalTheory.SeqCx.DblBd.hbd_hbd
  | exact @GlobalTheory.SeqCx.DblBd.vbd_mapDomain
  | exact @GlobalTheory.SeqCx.DblBd.hbd_mapDomain
  | exact @GlobalTheory.SeqCx.DblBd.vbd_single
  | exact @GlobalTheory.SeqCx.DblBd.hbd_single
  | exact @GlobalTheory.SeqCx.DblBd.single_eq_smul
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqHorizontalCycleIsBoundaryOfSlicesExact
section
noncomputable section

open Classical

namespace GlobalTheory.SeqCx

namespace DblRow

variable {V W : Type}

theorem pair_injective (w : List W) : Function.Injective (fun l : List V => (l, w)) :=
  fun _ _ h => (Prod.mk.inj h).1

def proj (w : List W) (x : List V × List W →₀ ℤ) : List V →₀ ℤ :=
  Finsupp.comapDomain (fun l : List V => (l, w)) x (pair_injective w).injOn

theorem proj_apply (w : List W) (x : List V × List W →₀ ℤ) (l : List V) :
    proj w x l = x (l, w) := rfl

def incl (w : List W) : (List V →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun l : List V => (l, w))

theorem incl_apply (w w' : List W) (z : List V →₀ ℤ) (l : List V) :
    incl w z (l, w') = if w = w' then z l else 0 := by
  by_cases h : w = w'
  · subst h
    rw [if_pos rfl]
    exact Finsupp.mapDomain_apply_of_injective (pair_injective w) z l
  · rw [if_neg h]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨l', hl'⟩
    exact h (congrArg Prod.snd hl')

theorem hbd_incl (w : List W) (z : List V →₀ ℤ) : hbd V W (incl w z) = incl w (bd V z) := by
  have : (hbd V W).comp (incl w) = (incl w).comp (bd V) := by
    apply Finsupp.lhom_ext
    intro l c
    simp only [LinearMap.comp_apply]
    rw [show Finsupp.single l c = c • Finsupp.single l (1 : ℤ) by simp, map_smul, map_smul, map_smul,
      map_smul]
    congr 1
    simp only [incl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hbd,
      Finsupp.linearCombination_single, one_smul]
  exact LinearMap.congr_fun this z

theorem decomp (x : List V × List W →₀ ℤ) :
    x = ∑ w ∈ x.support.image Prod.snd, incl w (proj w x) := by
  ext ⟨l, w'⟩
  rw [Finsupp.finsetSum_apply]
  simp only [incl_apply, proj_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    exact h (Finset.mem_image.2 ⟨(l, w'), Finsupp.mem_support_iff.2 (Ne.symm hne), rfl⟩)

end DblRow

open DblRow

theorem dblRow_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ),
    (∀ w : List W, w.length = b → (∃ l, (l, w) ∈ D) → ExactAt {l | (l, w) ∈ D} a) →
    ∀ x ∈ chains2 D a b, hbd V W x = 0 → ∃ y ∈ chains2 D (a + 1) b, hbd V W y = x := by
  intro V W D a b hex x hx h0
  have hsupp : ∀ z ∈ x.support, z ∈ D ∧ z.1.length = a ∧ z.2.length = b := fun z hz => hx hz
  set T := x.support.image Prod.snd with hT
  have h1 : hbd V W x = ∑ w ∈ T, incl w (bd V (proj w x)) := by
    conv_lhs => rw [decomp x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hbd_incl]
    rfl
  have hbd0 : ∀ w ∈ T, bd V (proj w x) = 0 := by
    intro w hw
    ext l
    have := congrArg (fun z => z (l, w)) h1
    simp only [h0, Finsupp.coe_zero, Pi.zero_apply, Finsupp.finsetSum_apply, incl_apply] at this
    rw [Finset.sum_ite_eq', if_pos hw] at this
    simpa using this.symm
  have hslice : ∀ w ∈ T, ∃ y ∈ chains {l | (l, w) ∈ D} (a + 1), bd V y = proj w x := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hzD, -, hzb⟩ := hsupp z hz
    refine hex z.2 hzb ⟨z.1, hzD⟩ (proj z.2 x) ?_ (hbd0 z.2 hw)
    intro l hl
    have hl' : (l, z.2) ∈ x.support := by
      have hl2 := Finset.mem_coe.1 hl
      rw [Finsupp.mem_support_iff] at hl2 ⊢
      exact hl2
    obtain ⟨h2, h3, -⟩ := hsupp _ hl'
    exact ⟨h2, h3⟩
  choose! yw hyw hywb using hslice
  refine ⟨∑ w ∈ T, incl w (yw w), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun w hw => ?_
    intro z hz
    have hz' := Finsupp.mapDomain_support hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hz'
    obtain ⟨h2, h3⟩ := hyw w hw hl
    obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨h2, h3, (hsupp z0 hz0).2.2⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hbd_incl]
    conv_rhs => rw [decomp x]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hywb w hw]

end GlobalTheory.SeqCx

end

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqHorizontalCycle_is_boundary_of_slices_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ w : List W, w.length = b → (∃ l, (l, w) ∈ D) → ExactAt {l | (l, w) ∈ D} a) → ∀ x ∈ chains2 D a b, hbd V W x = 0 → ∃ y ∈ chains2 D (a + 1) b, hbd V W y = x := by
  first
  | exact @GlobalTheory.SeqCx.dblRow_exact
  | exact @GlobalTheory.SeqCx.DblRow.decomp
  | exact @GlobalTheory.SeqCx.DblRow.hbd_incl
  | exact @GlobalTheory.SeqCx.DblRow.incl_apply
  | exact @GlobalTheory.SeqCx.DblRow.proj_apply
  | exact @GlobalTheory.SeqCx.DblRow.pair_injective
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqVerticalCycleIsBoundaryOfSlicesExact
section
open GlobalTheory.SeqCx

namespace GlobalTheory.SeqCx.ColDecomp

lemma inj_pair {V W : Type} (l : List V) : Function.Injective (fun w : List W => (l, w)) := by
  intro u v h
  exact (Prod.mk.inj h).2

open Classical in
lemma sum_apply_pair {V W : Type} (T : Finset (List V)) (g : List V → List W →₀ ℤ) (l : List V) (w : List W) :
    (∑ l' ∈ T, Finsupp.mapDomain (fun w => (l', w)) (g l')) (l, w) = if l ∈ T then g l w else 0 := by
  rw [Finsupp.finsetSum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single l]
    · exact Finsupp.mapDomain_apply_of_injective (inj_pair l) _ _
    · intro l' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨w', hw'⟩
      exact hne (congrArg Prod.fst hw')
    · intro hl
      exact absurd h hl
  · apply Finset.sum_eq_zero
    intro l' hl'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨w', hw'⟩
    obtain rfl : l' = l := congrArg Prod.fst hw'
    exact h hl'

lemma vbd_mapDomain {V W : Type} (l : List V) (c : List W →₀ ℤ) :
    vbd V W (Finsupp.mapDomain (fun w => (l, w)) c) = Finsupp.mapDomain (fun w => (l, w)) (bd W c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add]
  | single w k =>
    rw [Finsupp.mapDomain_single]
    simp only [vbd, bd, Finsupp.linearCombination_single]
    rw [one_smul, Finsupp.mapDomain_smul]

end GlobalTheory.SeqCx.ColDecomp


open GlobalTheory.SeqCx.ColDecomp in
theorem GlobalTheory.SeqCx.vertical_exact_of_columns : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ l : List V, l.length = a → (∃ w, (l, w) ∈ D) → ExactAt {w | (l, w) ∈ D} b) → ∀ x ∈ chains2 D a b, vbd V W x = 0 → ∃ y ∈ chains2 D a (b + 1), vbd V W y = x := by
  classical
  intro V W D a b hex x hx hvx
  set T : Finset (List V) := x.support.image Prod.fst with hT
  set g : List V → List W →₀ ℤ := fun l => x.curry l with hg
  have hgapp : ∀ l w, g l w = x (l, w) := fun l w => Finsupp.curry_apply x l w
  have hsupp : ∀ z ∈ x.support, z ∈ D ∧ z.1.length = a ∧ z.2.length = b := fun z hz => hx hz
  have hdec : x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (g l) := by
    ext ⟨l, w⟩
    rw [sum_apply_pair]
    split_ifs with h
    · rw [hgapp]
    · by_contra hne
      exact h (Finset.mem_image.2 ⟨(l, w), Finsupp.mem_support_iff.2 hne, rfl⟩)
  have hvdec : vbd V W x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (bd W (g l)) := by
    conv_lhs => rw [hdec]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => vbd_mapDomain l (g l))
  have hcyc : ∀ l ∈ T, bd W (g l) = 0 := by
    intro l hl
    ext w
    have := congrArg (fun f => f (l, w)) hvdec
    simp only [hvx, sum_apply_pair, if_pos hl] at this
    simpa using this.symm
  have hchain : ∀ l ∈ T, g l ∈ chains {w | (l, w) ∈ D} b := by
    intro l hl
    rw [chains, Finsupp.mem_supported]
    intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hgapp] at hw
    have := hsupp (l, w) (Finsupp.mem_support_iff.2 hw)
    exact ⟨this.1, this.2.2⟩
  have hpre : ∀ l ∈ T, l.length = a ∧ ∃ w, (l, w) ∈ D := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hl
    have := hsupp z hz
    exact ⟨this.2.1, z.2, this.1⟩
  have hy : ∀ l ∈ T, ∃ y ∈ chains {w | (l, w) ∈ D} (b + 1), bd W y = g l := by
    intro l hl
    exact hex l (hpre l hl).1 (hpre l hl).2 (g l) (hchain l hl) (hcyc l hl)
  choose! y hymem hybd using hy
  refine ⟨∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (y l), ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun l hl => ?_)
    rw [chains2, Finsupp.mem_supported]
    intro z hz
    have hz' := Finsupp.mapDomain_support (Finset.mem_coe.1 hz)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz'
    have hyl := hymem l hl
    rw [chains, Finsupp.mem_supported] at hyl
    have := hyl (Finset.mem_coe.2 hw)
    exact ⟨this.1, (hpre l hl).1, this.2⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, hdec]
      exact Finset.sum_congr rfl (fun l hl => by rw [vbd_mapDomain, hybd l hl])

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqVerticalCycle_is_boundary_of_slices_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ l : List V, l.length = a → (∃ w, (l, w) ∈ D) → ExactAt {w | (l, w) ∈ D} b) → ∀ x ∈ chains2 D a b, vbd V W x = 0 → ∃ y ∈ chains2 D a (b + 1), vbd V W y = x := by
  first
  | exact @GlobalTheory.SeqCx.vertical_exact_of_columns
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosed2SplitPairs
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem splitPairs_subClosed2 : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed2 (splitPairs R n) := by
  intro R _ n z hz x w hx hw
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hw
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [hf i, hf j, h1 (f i) (f j)]
    simp only [f.eq_iff_eq]
  · obtain ⟨F, hF⟩ := h2
    refine ⟨fun i => F (g i), fun i j => ?_⟩
    rw [hg j, hF]
    simp only [g.eq_iff_eq]
  · intro y hy u hu
    exact h3 y (hx.subset hy) u (hw.subset hu)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.subClosed2_splitPairs : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed2 (splitPairs R n) := by
  first
  | exact @GlobalTheory.SeqCx.splitPairs_subClosed2
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SurjectiveHMapZeroOfStaircase
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Staircase

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hd0 hexC hexH
  have ses : ∀ (W X Y : Rep.{0, 0, 0} k G) (u : W ⟶ X) (v : X ⟶ Y) (huv : u ≫ v = 0),
      Function.Exact u.hom v.hom →
      (ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp)).ShortExact := by
    intro W X Y u v huv hex
    have hS' : (ShortComplex.mk (kernel.ι u) u (kernel.condition u)).Exact :=
      ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel u)
    let φ : ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp) ⟶
        ShortComplex.mk (kernel.ι u) u (kernel.condition u) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι v, comm₁₂ := by simp, comm₂₃ := by simp }
    have hinj : Function.Injective (kernel.ι v).hom := (Rep.mono_iff_injective _).mp inferInstance
    refine { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS',
             mono_f := inferInstance, epi_g := ?_ }
    rw [Rep.epi_iff_surjective]
    intro z
    have hz : v.hom ((kernel.ι v).hom z) = 0 := by
      have h := congrArg (fun f => f.hom z) (kernel.condition v)
      simpa using h
    obtain ⟨y, hy⟩ := (hex _).mp hz
    refine ⟨y, hinj ?_⟩
    have h := congrArg (fun f => f.hom y) (kernel.lift_ι v u huv)
    exact h.trans hy
  have epi0 : ∀ (X Y : Rep.{0, 0, 0} k G) (f : X ⟶ Y), Function.Surjective f.hom →
      Function.Surjective (hMap f 0).hom := by
    intro X Y f hf
    haveI : Epi f := (Rep.epi_iff_surjective f).mpr hf
    exact (ModuleCat.epi_iff_surjective _).mp (groupHomology.epi_map_0_of_epi f)
  have liftSurj : ∀ p, p + 1 ≤ i →
      Function.Surjective (kernel.lift (d p) (d (p + 1)) (hd p)).hom := by
    intro p hp
    exact (Rep.epi_iff_surjective _).mp (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p hp)).epi_g
  have R : ∀ q p, p + 1 + q = i →
      Function.Surjective (hMap (kernel.lift (d p) (d (p + 1)) (hd p)) q).hom := by
    intro q
    induction q with
    | zero =>
      intro p hp
      exact epi0 _ _ _ (liftSurj p (by omega))
    | succ q ih =>
      intro p hp
      have hab : d (p + 3) ≫ kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) = 0 := by
        rw [← cancel_mono (kernel.ι (d (p + 1)))]
        simp [hd]
      have hbι : kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1)) =
          d (p + 2) := kernel.lift_ι _ _ _
      have hE : Function.Exact (hMap (d (p + 3)) q).hom
          (hMap (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1))) q).hom := by
        rw [hbι]
        exact hexH (p + 2) q (by omega) (by omega)
      exact homStab_step k G (C (p + 4)) (C (p + 3)) (kernel (d (p + 1))) (C (p + 2)) (kernel (d p))
        (d (p + 3)) (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1))) (kernel.ι (d (p + 1)))
        (kernel.lift (d p) (d (p + 1)) (hd p)) _
        (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p (by omega))) hab q (ih (p + 1) (by omega)) hE
  cases i with
  | zero => exact epi0 _ _ _ hd0
  | succ q =>
    have ses0 : (ShortComplex.mk (kernel.ι (d 0)) (d 0) (kernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (d 0))
        mono_f := inferInstance
        epi_g := (Rep.epi_iff_surjective _).mpr hd0 }
    have hab : d 2 ≫ kernel.lift (d 0) (d 1) (hd 0) = 0 := by
      rw [← cancel_mono (kernel.ι (d 0))]
      simp [hd]
    have hbι : kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0) = d 1 := kernel.lift_ι _ _ _
    have hE : Function.Exact (hMap (d 2) q).hom
        (hMap (kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0)) q).hom := by
      rw [hbι]
      exact hexH 1 q (by omega) (by omega)
    exact homStab_step k G (C 3) (C 2) (kernel (d 0)) (C 1) (C 0) (d 2)
      (kernel.lift (d 0) (d 1) (hd 0)) (kernel.ι (d 0)) (d 0) _ ses0 hab q (R q 0 (by omega)) hE

end GlobalTheory.HomStab.Staircase

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.surjective_hMap_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.Staircase.main
end
end

