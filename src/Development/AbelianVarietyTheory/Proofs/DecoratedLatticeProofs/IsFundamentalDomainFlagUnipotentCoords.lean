module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.ThreeLayers

section Abstract

open scoped Pointwise

variable {A B U X G : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [AddGroup B] [MeasurableSpace B]
  [Group U] [MeasurableSpace U] [MeasurableSpace X] [Group G] [MulAction G X]
  {mA : Measure A} {mB : Measure B} {ν : Measure U} [SFinite mA] [SFinite mB] [SFinite ν]


omit [AddCommGroup A] [MeasurableAdd₂ A] [AddGroup B] [Group U] in
theorem null_last {N : Set U} (hN : ν N = 0) : (mA.prod (mB.prod ν)) {p | p.2.2 ∈ N} = 0 := by
  have h : {p : A × (B × U) | p.2.2 ∈ N} = Set.univ ×ˢ (Set.univ ×ˢ N) := by
    ext p; simp
  rw [h, Measure.prod_prod, Measure.prod_prod, hN]
  simp


omit [AddCommGroup A] [MeasurableAdd₂ A] [AddGroup B] [Group U] in
theorem null_mid {β : B → B} (hβ : Measure.QuasiMeasurePreserving β mB mB) {N : Set B} (hN : mB N = 0) :
    (mA.prod (mB.prod ν)) {p | β p.2.1 ∈ N} = 0 := by
  have h : {p : A × (B × U) | β p.2.1 ∈ N} = Set.univ ×ˢ ((β ⁻¹' N) ×ˢ Set.univ) := by
    ext p; simp
  rw [h, Measure.prod_prod, Measure.prod_prod, MeasureTheory.QuasiMeasurePreserving.preimage_null hβ hN]
  simp


omit [AddGroup B] [Group U] in
theorem null_first [mA.IsAddLeftInvariant] {α : A → A} (hα : Measure.QuasiMeasurePreserving α mA mA) {φ : B → A}
    (hφ : Measurable φ) {N : Set A} (hN : mA N = 0) :
    (mA.prod (mB.prod ν)) {p | α p.1 + φ p.2.1 ∈ N} = 0 := by
  let α' := (MeasureTheory.QuasiMeasurePreserving.aemeasurable hα).mk α
  have hαeq : ∀ᵐ x ∂mA, α x = α' x := (MeasureTheory.QuasiMeasurePreserving.aemeasurable hα).ae_eq_mk
  have hbad : (mA.prod (mB.prod ν)) {p : A × (B × U) | α p.1 ≠ α' p.1} = 0 := by
    have heq : {p : A × (B × U) | α p.1 ≠ α' p.1} = {x | α x ≠ α' x} ×ˢ Set.univ := by ext p; simp
    rw [heq, Measure.prod_prod, (ae_iff.mp hαeq)]
    simp
  refine measure_mono_null (t := {p : A × (B × U) | α p.1 ≠ α' p.1} ∪ {p : A × (B × U) | α' p.1 + φ p.2.1 ∈ N}) (fun p hp => ?_) ?_
  · by_cases he : α p.1 = α' p.1
    · apply Or.inr
      simpa only [Set.mem_setOf_eq, ← he] using hp
    · exact Or.inl he
  apply measure_union_null hbad
  have hα' : MeasureTheory.QuasiMeasurePreserving α' mA mA := (MeasureTheory.QuasiMeasurePreserving.congr hα hαeq)
  have hM : MeasurableSet (toMeasurable mA N) := measurableSet_toMeasurable _ _
  have hM0 : mA (toMeasurable mA N) = 0 := by rw [measure_toMeasurable, hN]
  have hs : MeasurableSet {p : A × (B × U) | α' p.1 + φ p.2.1 ∈ toMeasurable mA N} :=
    (((MeasureTheory.QuasiMeasurePreserving.aemeasurable hα).measurable_mk.comp measurable_fst).add (hφ.comp (measurable_fst.comp measurable_snd))) hM
  refine measure_mono_null (t := {p : A × (B × U) | α' p.1 + φ p.2.1 ∈ toMeasurable mA N})
    (fun p hp => subset_toMeasurable mA N hp) ?_
  rw [Measure.prod_apply_symm hs]
  have h0 : ∀ y : B × U, mA ((fun x => (x, y)) ⁻¹' {p : A × (B × U) | α' p.1 + φ p.2.1 ∈ toMeasurable mA N}) = 0 := fun y => by
    have h1 : (fun x : A => (x, y)) ⁻¹' {p : A × (B × U) | α' p.1 + φ p.2.1 ∈ toMeasurable mA N} =
        α' ⁻¹' ((fun x => φ y.1 + x) ⁻¹' toMeasurable mA N) := by
      ext x; simp [add_comm]
    rw [h1]
    exact MeasureTheory.QuasiMeasurePreserving.preimage_null hα' (by rw [measure_preimage_add, hM0])
  exact (lintegral_congr h0).trans lintegral_zero

theorem isFundamentalDomain_three [mA.IsAddLeftInvariant] (ΓA : AddSubgroup A) (ΓB : AddSubgroup B) (ΓU : Subgroup U)
    [Countable ΓB] [Countable ΓU] (α : U → A → A) (β : U → B → B)
    (hα : ∀ u, Measure.QuasiMeasurePreserving (α u) mA mA) (hβ : ∀ u, Measure.QuasiMeasurePreserving (β u) mB mB)
    (κ : B → B → A) (hκ : ∀ b', Measurable (κ b')) (e : A × (B × U) ≃ᵐ X)
    (hfree : ∀ (g g' : G) (x : X), g • x = g' • x → g = g')
    (hG : ∀ g : G, ∃ (c' : ΓA) (b' : ΓB) (u' : ΓU), ∀ p,
      g • e p = e (c'.1 + α u'.1 p.1 + κ b'.1 (β u'.1 p.2.1), b'.1 + β u'.1 p.2.1, u'.1 * p.2.2))
    (hG' : ∀ (c' : ΓA) (b' : ΓB) (u' : ΓU), ∃ g : G, ∀ p,
      g • e p = e (c'.1 + α u'.1 p.1 + κ b'.1 (β u'.1 p.2.1), b'.1 + β u'.1 p.2.1, u'.1 * p.2.2))
    {𝓒 : Set A} {𝓕 : Set B} {𝓤 : Set U} (hC : IsAddFundamentalDomain ΓA 𝓒 mA) (hF : IsAddFundamentalDomain ΓB 𝓕 mB)
    (hU : IsFundamentalDomain ΓU 𝓤 ν) :
    IsFundamentalDomain G (e '' (𝓒 ×ˢ (𝓕 ×ˢ 𝓤))) ((mA.prod (mB.prod ν)).map e) := by
  have hmem : ∀ q, e q ∈ e '' (𝓒 ×ˢ (𝓕 ×ˢ 𝓤)) ↔ q ∈ 𝓒 ×ˢ (𝓕 ×ˢ 𝓤) :=
    fun q => e.injective.mem_set_image
  have hmp := (e.measurable.measurePreserving (mA.prod (mB.prod ν))).symm e
  have hφ : ∀ (b' : B) (u : U) {N : Set A}, mA N = 0 →
      (mA.prod (mB.prod ν)) {p | α u p.1 + κ b' (β u p.2.1) ∈ N} = 0 := by
    intro b' u N hN
    let β' := (MeasureTheory.QuasiMeasurePreserving.aemeasurable (hβ u)).mk (β u)
    have heq : ∀ᵐ b ∂mB, β u b = β' b := (MeasureTheory.QuasiMeasurePreserving.aemeasurable (hβ u)).ae_eq_mk
    have hbad : (mA.prod (mB.prod ν)) {p : A × (B × U) | β u p.2.1 ≠ β' p.2.1} = 0 :=
      null_mid (MeasureTheory.QuasiMeasurePreserving.id mB) (ae_iff.mp heq)
    refine measure_mono_null (t := {p : A × (B × U) | β u p.2.1 ≠ β' p.2.1} ∪ {p | α u p.1 + κ b' (β' p.2.1) ∈ N}) (fun p hp => ?_) ?_
    · by_cases he : β u p.2.1 = β' p.2.1
      · apply Or.inr
        simpa only [Set.mem_setOf_eq, ← he] using hp
      · exact Or.inl he
    exact measure_union_null hbad (null_first (hα u) ((hκ b').comp (MeasureTheory.QuasiMeasurePreserving.aemeasurable (hβ u)).measurable_mk) hN)
  refine ⟨?_, ?_, ?_⟩
  · have hS : NullMeasurableSet (𝓒 ×ˢ (𝓕 ×ˢ 𝓤)) (mA.prod (mB.prod ν)) :=
      hC.nullMeasurableSet.prod (hF.nullMeasurableSet.prod hU.nullMeasurableSet)
    rw [e.image_eq_preimage_symm]
    exact hS.preimage hmp.quasiMeasurePreserving
  · rw [e.measurableEmbedding.ae_map_iff]
    have h0 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∃ g : ΓU, g • p.2.2 ∈ 𝓤 :=
      ae_iff.2 (null_last (mA := mA) (mB := mB) (ae_iff.1 hU.ae_covers))
    have h1 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∀ u' : ΓU, ∃ g : ΓB, g +ᵥ β u'.1 p.2.1 ∈ 𝓕 := by
      rw [ae_all_iff]
      intro u'
      exact ae_iff.2 (null_mid (mA := mA) (ν := ν) (hβ u'.1) (ae_iff.1 hF.ae_covers))
    have h2 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∀ (u' : ΓU) (b' : ΓB), ∃ g : ΓA,
        g +ᵥ (α u'.1 p.1 + κ b'.1 (β u'.1 p.2.1)) ∈ 𝓒 := by
      rw [ae_all_iff]
      intro u'
      rw [ae_all_iff]
      intro b'
      exact ae_iff.2 (hφ b'.1 u'.1 (ae_iff.1 hC.ae_covers))
    filter_upwards [h0, h1, h2] with p hp0 hp1 hp2
    obtain ⟨u', hu⟩ := hp0
    obtain ⟨b', hb⟩ := hp1 u'
    obtain ⟨c', hc⟩ := hp2 u' b'
    obtain ⟨g, hg⟩ := hG' c' b' u'
    refine ⟨g, ?_⟩
    rw [hg p, hmem]
    refine ⟨?_, hb, hu⟩
    rw [AddSubgroup.vadd_def, vadd_eq_add] at hc
    simpa only [add_assoc] using hc
  · intro g₁ g₂ hne
    obtain ⟨c₁, b₁, u₁, h₁⟩ := hG g₁⁻¹
    obtain ⟨c₂, b₂, u₂, h₂⟩ := hG g₂⁻¹
    change (mA.prod (mB.prod ν)).map e (g₁ • (e '' _) ∩ g₂ • (e '' _)) = 0
    rw [e.map_apply]
    have hin : ∀ p, p ∈ e ⁻¹' (g₁ • (e '' (𝓒 ×ˢ (𝓕 ×ˢ 𝓤))) ∩ g₂ • (e '' (𝓒 ×ˢ (𝓕 ×ˢ 𝓤)))) →
        (c₁.1 + α u₁.1 p.1 + κ b₁.1 (β u₁.1 p.2.1) ∈ 𝓒 ∧ b₁.1 + β u₁.1 p.2.1 ∈ 𝓕 ∧ u₁.1 * p.2.2 ∈ 𝓤) ∧
        (c₂.1 + α u₂.1 p.1 + κ b₂.1 (β u₂.1 p.2.1) ∈ 𝓒 ∧ b₂.1 + β u₂.1 p.2.1 ∈ 𝓕 ∧ u₂.1 * p.2.2 ∈ 𝓤) := by
      rintro p ⟨hp1, hp2⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, h₁, hmem] at hp1
      rw [Set.mem_smul_set_iff_inv_smul_mem, h₂, hmem] at hp2
      exact ⟨⟨hp1.1, hp1.2.1, hp1.2.2⟩, ⟨hp2.1, hp2.2.1, hp2.2.2⟩⟩
    by_cases hu : u₁ = u₂
    · subst hu
      by_cases hb : b₁ = b₂
      · subst hb
        by_cases hc : c₁ = c₂
        · subst hc
          refine measure_mono_null (t := ∅) (fun p hp => ?_) (measure_empty)
          have : g₁⁻¹ • e p = g₂⁻¹ • e p := by rw [h₁, h₂]
          exact absurd (inv_injective (hfree _ _ _ this)) hne
        · have hd := hC.aedisjoint (i := -c₁) (j := -c₂) (fun h => hc (neg_injective h))
          have hd' : mA ((-c₁ +ᵥ 𝓒) ∩ (-c₂ +ᵥ 𝓒)) = 0 := hd
          refine measure_mono_null (fun p hp => ?_) (hφ b₁.1 u₁.1 hd')
          obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hin p hp
          refine ⟨?_, ?_⟩
          · rw [Set.mem_neg_vadd_set_iff]
            simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc] using h1
          · rw [Set.mem_neg_vadd_set_iff]
            simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc] using h2
      · have hd := hF.aedisjoint (i := -b₁) (j := -b₂) (fun h => hb (neg_injective h))
        have hd' : mB ((-b₁ +ᵥ 𝓕) ∩ (-b₂ +ᵥ 𝓕)) = 0 := hd
        refine measure_mono_null (fun p hp => ?_) (null_mid (mA := mA) (ν := ν) (hβ u₁.1) hd')
        obtain ⟨⟨-, h1, -⟩, ⟨-, h2, -⟩⟩ := hin p hp
        exact ⟨Set.mem_neg_vadd_set_iff.2 h1, Set.mem_neg_vadd_set_iff.2 h2⟩
    · have hd := hU.aedisjoint (i := u₁⁻¹) (j := u₂⁻¹) (fun h => hu (inv_injective h))
      have hd' : ν ((u₁⁻¹ • 𝓤) ∩ (u₂⁻¹ • 𝓤)) = 0 := hd
      refine measure_mono_null (fun p hp => ?_) (null_last (mA := mA) (mB := mB) hd')
      obtain ⟨⟨-, -, h1⟩, ⟨-, -, h2⟩⟩ := hin p hp
      exact ⟨Set.mem_inv_smul_set_iff.2 h1, Set.mem_inv_smul_set_iff.2 h2⟩

end Abstract

theorem act_coords {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c' c : skewA D ρ) (b' b : Mx D ρ S₀.rank)
    (u' u : GL (Fin ρ) (AE D)) :
    d.nC c' * (d.nB b' * d.levi u') * (d.nC c * (d.nB b * d.levi u)) =
      d.nC (c' + skewConj u'.1 c + cComm S₀ b' (u'.1 ⬝ b)) * (d.nB (b' + u'.1 ⬝ b) * d.levi (u' * u)) := by
  rw [← GlobalTheory.Layers.act_coords, map_mul]
  calc d.nC c' * (d.nB b' * d.levi u') * (d.nC c * (d.nB b * d.levi u))
      = d.nC c' * d.nB b' * ((d.levi u' * d.nC c) * (d.nB b * d.levi u)) := by simp only [mul_assoc]
    _ = d.nC c' * d.nB b' * (d.nC (skewConj u'.1 c) * ((d.levi u' * d.nB b) * d.levi u)) := by
        rw [d.levi_mul_nC]; simp only [mul_assoc]
    _ = _ := by rw [d.levi_mul_nB]; simp only [mul_assoc]

theorem fundDomain_coords : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)) (𝓤 : Set (UX D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → IsFundamentalDomain (UXQ D ρ) 𝓤 vU.ν → IsFundamentalDomain (NFlagQ V d.e) (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ 𝓤))) ((lC.prod (vb.μ.prod vU.ν)).map e) := by
  intro D V V₀ ρ d vb vU e he lC 𝓒 𝓤 hlC _ hC hU
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  haveI : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).1
  haveI : LocallyCompactSpace (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.1
  haveI : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.2.2.1
  haveI : Countable (ratMx D ρ V₀.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  haveI hca : ContinuousAdd (skewA D ρ) := IsTopologicalAddGroup.toContinuousAdd
  haveI : MeasurableAdd₂ (skewA D ρ) := @ContinuousAdd.measurableMul₂ (skewA D ρ) _ _ _ _ _ hca
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : Countable (UXQ D ρ) := (GlobalTheory.UnitU.rational D ρ).1
  haveI := vU.unit.1
  haveI := vb.covol.1
  haveI : SigmaFinite vb.μ := inferInstance
  haveI : SigmaFinite vU.ν := inferInstance
  have hκ : ∀ b' : Mx D ρ V₀.rank, Measurable (cComm V₀ b') := by
    intro b'
    have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
    have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
    have h1 : Continuous fun b : Mx D ρ V₀.rank => half D • (b ⬝ plus V₀ b' - b' ⬝ plus V₀ b) :=
      ((continuous_id.matrix_mul continuous_const).sub (continuous_const.matrix_mul hp)).const_smul (half D)
    exact (h1.subtype_mk _).measurable
  have key : ∀ (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) (u' : UX D ρ) (p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ)),
      d.nC c' * (d.nB b' * d.levi u'.1) * (e p : GA D V) =
        (e (c' + skewConj u'.1.1 p.1 + cComm V₀ b' (u'.1.1 ⬝ p.2.1), b' + u'.1.1 ⬝ p.2.1, u' * p.2.2) : GA D V) := by
    intro c' b' u' p
    rw [he p, he (c' + skewConj u'.1.1 p.1 + cComm V₀ b' (u'.1.1 ⬝ p.2.1), b' + u'.1.1 ⬝ p.2.1, u' * p.2.2)]
    exact act_coords d c' p.1 b' p.2.1 u'.1 p.2.2.1
  have hsm : ∀ (g : NFlagQ V d.e) (x : flagN d),
      ((g • x : flagN d) : GA D V) = ((g : flagN d) : GA D V) * (x : GA D V) := fun _ _ => rfl
  refine isFundamentalDomain_three (mA := lC) (mB := vb.μ) (ν := vU.ν) ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ))
    (ratMx D ρ V₀.rank) (UXQ D ρ) (fun u => skewConj u.1.1) (fun u b => u.1.1 ⬝ b)
    (_root_.GlobalTheory.Unf.SkewConjQmp.quasiMeasurePreserving_skewConj D ρ lC hlC) (_root_.GlobalTheory.LeftUniQmp.qmp_left_uni D ρ V₀.rank vb.μ vb.covol.1) (cComm V₀) hκ e ?_ ?_ ?_ hC vb.covol.2.1 hU
  · intro g g' x h
    rw [Subgroup.smul_def, Subgroup.smul_def] at h
    exact Subtype.ext (mul_right_cancel h)
  · intro g
    obtain ⟨c, b, u, hg, hc, hb, hu⟩ := _root_.GlobalTheory.RatCoord.rat_coords_of_mem_flagN D V V₀ ρ d g.1.1 (Subgroup.mem_subgroupOf.1 g.2) g.1.2
    refine ⟨⟨c, AddSubgroup.mem_addSubgroupOf.2 hc⟩, ⟨b, hb⟩, ⟨u, hu⟩, fun p => Subtype.ext ?_⟩
    rw [hsm, hg]
    exact key c b u p
  · rintro ⟨c', hc'⟩ ⟨b', hb'⟩ ⟨u', hu'⟩
    have hQ : d.nC c' * (d.nB b' * d.levi u'.1) ∈ GQ V :=
      mul_mem (d.nC_mem_GQ (AddSubgroup.mem_addSubgroupOf.1 hc')) (mul_mem (d.nB_mem_GQ hb') (d.levi_mem_GQ hu'.1 hu'.2))
    have h1 := he (c', b', u')
    let g : NFlagQ V d.e := ⟨e (c', b', u'), Subgroup.mem_subgroupOf.2 (by rw [h1]; exact hQ)⟩
    refine ⟨g, fun p => Subtype.ext ((hsm g (e p)).trans ?_)⟩
    rw [show ((g : flagN d) : GA D V) = _ from h1]
    exact key c' b' u' p

end GlobalTheory.ThreeLayers

end
