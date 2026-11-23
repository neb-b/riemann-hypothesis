module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0030

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertRIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField

noncomputable section

namespace VerticalIndex

variable {T : Type} [Fintype T] {K' : Type} [Field K']

theorem aeval_mem_sectionMod (y : (Σ _ : Unit, T) → K') {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) : aeval y s ∈ sectionMod y :=
  HilbertSamuel.NormCountBounded.secM_le_chartLat y 1 (Submodule.subset_span ⟨s, hs, rfl⟩)


omit [Fintype T] in
theorem span_toAddSubgroup (y : (Σ _ : Unit, T) → K') (x : K') :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩


omit [Fintype T] in
theorem genIndex_eq_card (y : (Σ _ : Unit, T) → K') {x : K'} (hx : x ∈ sectionMod y) :
    genIndex (chartLat y (fun _ => 1) 1) (curveMul y x) = Nat.card (sectionQuot y x) := by
  have hle : curveMul y x ≤ chartLat y (fun _ => 1) 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end VerticalIndex


open IndefiniteRowSideFullHecke.HeightsSet in
theorem VertRIndex.proof (hL : LogCardLength.Statement) (hF : SectionQuotFinite.Statement)
    (hV : VertPointLength.Statement) (hR : VertPointResidue.Statement) : VertRIndex.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  have := hF T K' y s hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV T K' y s hP hs hsP
  rw [VerticalIndex.genIndex_eq_card y (VerticalIndex.aeval_mem_sectionMod y hs),
    hL (curveRing y) (sectionQuot y (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s, (locLen (curvePtIdeal y W) (sectionQuot y (aeval y s)) : ℝ) *
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (CurveDivVertical.full Unit (fun _ => T) _ s _ hP hs hsP W hW), hmult W hW,
          ← hR T K' y s hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) | m.IsMaximal ∧ locLen m (sectionQuot y (aeval y s)) ≠ 0},
          (locLen m (sectionQuot y (aeval y s)) : ℝ) * Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedDiag {T : Type} [DecidableEq T] (a : T → ℤ) : ∀ _ : Unit, T → T → ℤ :=
  fun _ t s => if t = s then a t else 0

abbrev stackedBlocks (T : Type) : Unit ⊕ Unit → Type := Sum.elim (dualBlocks T) (dualBlocks T)

def stackedGraph {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  graphIdeal (dualIdeal b') (linForm (stackedDiag a))

def graphFirst {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inl (), t⟩

def graphSecond {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inr (), t⟩

def degFirst : Unit ⊕ Unit → ℤ := pullDeg (Sum.inl : Unit → Unit ⊕ Unit) fun _ => 1

def degSecond : Unit ⊕ Unit → ℤ := pullDeg (Sum.inr : Unit → Unit ⊕ Unit) fun _ => 1

def DualStackedGraphImage.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    imageZ inrV (stackedGraph b' a) = dualIdeal b ∧
      ∀ (G : GenFibre inrV (stackedGraph b' a))
        (J : IFamily G.Φ (fibreIdx (stackedBlocks T) (Sum.inr : Unit → Unit ⊕ Unit))),
        IsFieldIntersection J → J (fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

def DualStackedGraphHorizontal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (W : Ideal (MRing (stackedBlocks T))), IsHorizontal W →
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) ↔
        W ∈ divSupp (stackedGraph b' a) (C (a t) * graphFirst t)) ∧
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) →
        multAt (stackedGraph b' a ⊔ Ideal.span {graphSecond t}) W =
          multAt (stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t}) W)

def DualStackedGraphFibre.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (L : Fin (i - 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (stackedBlocks T)),
      (∀ j, (L j).a = degFirst ∨ (L j).a = degSecond) →
      ((∀ j, (L j).a = degSecond) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) =
          -∑ s, Real.log |(a s : ℝ)|) ∧
      ((∃ j, (L j).a = degFirst) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) = 0)

theorem degFirst_inr : degFirst (Sum.inr ()) = 0 := by
  rw [degFirst, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inl_ne_inr hu)]
  rfl

theorem degSecond_inr : degSecond (Sum.inr ()) = 1 := by
  rw [degSecond, pullDeg, Sum.inr_injective.extend_apply]

end

end GroundTheory.Heights₂.Heights
end

