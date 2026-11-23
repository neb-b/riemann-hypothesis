module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.GlobalComplexCoefficients
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.AllLeavesMono
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F

namespace PositivityTheory.Rg.BcB.F.F0

def xΩ₁ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] :=
  (hR E).choose_spec.choose_spec.choose
def xΩ₂ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] :=
  (hR E).choose_spec.choose_spec.choose_spec.choose

def WEx : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : HChar E)
  (e : InfinitePlace E → ℤ) (lam : InfinitePlace E → DomWeight n) (C : Chain μ e lam)
  (A : ∀ i : C.ι, Arch E (C.a i) (n - C.a i) (C.l₁ i) (C.l₂ i) (C.μG (C.a i)) (C.μG (n - C.a i)) (C.νC (C.a i))
    (C.νC (n - C.a i))),
  ∃ W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ), (∀ N, FiniteDimensional ℂ (W N)) ∧
    ∀ (i : C.ι) (s₁ : Tr E (C.a i)) (s₂ : Tr E (n - C.a i)) Pa Pb (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ xΩ₁ hR E _ _ (A i).Ma (A i).Mb M, HasType K' W' V) →
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ xΩ₂ hR E _ _ (A i).Ma (A i).Mb M, HasType K' W' V) →
    ∀ j, HasKType (W (D.N j)) (D.V j)

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → t.AllLeaves Q
  | _, .leaf V _, hp => h _ V hp
  | _, .node t₁ t₂, hp => ⟨allLeaves_mono h t₁ hp.1, allLeaves_mono h t₂ hp.2⟩

theorem wEx_of (hJ : JoinType) : WEx := by
  intro hR E _ _ _ n μ e lam C A
  let Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)) := fun M =>
    ⋃ i : C.ι, (xΩ₁ hR E _ _ (A i).Ma (A i).Mb M ∪ xΩ₂ hR E _ _ (A i).Ma (A i).Mb M)
  have hx := (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  have hK : KTypes E Ω := by
    intro M
    refine ⟨Set.finite_iUnion fun i =>
      ((hx _ _ (A i).Ma (A i).Mb).2.2.1 M).1.union ((hx _ _ (A i).Ma (A i).Mb).2.2.2.1 M).1, ?_⟩
    intro W' hW'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hW'
    rcases hi with h | h
    · exact ((hx _ _ (A i).Ma (A i).Mb).2.2.1 M).2 W' h
    · exact ((hx _ _ (A i).Ma (A i).Mb).2.2.2.1 M).2 W' h
  obtain ⟨W, hW, hj⟩ := hJ E n μ Ω hK
  refine ⟨W, hW, fun i s₁ s₂ Pa Pb D hc h₁ h₂ =>
    hj (C.a i) (n - C.a i) (Nat.add_sub_of_le (C.le i)) s₁ s₂ Pa Pb D hc ?_ ?_⟩
  · exact allLeaves_mono (fun M V hv => hv.elim Or.inl fun ⟨K', W', hW', ht⟩ =>
      Or.inr ⟨K', W', Set.mem_iUnion.2 ⟨i, Or.inl hW'⟩, ht⟩) s₁ h₁
  · exact allLeaves_mono (fun M V hv => hv.elim Or.inl fun ⟨K', W', hW', ht⟩ =>
      Or.inr ⟨K', W', Set.mem_iUnion.2 ⟨i, Or.inr hW'⟩, ht⟩) s₂ h₂

end PositivityTheory.Rg.BcB.F.F0

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.InfinitesimalWeightZero
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem haarGA_ex (E : Type) [Field E] [NumberField E] (a : ℕ) : ∃ μ : Measure (GA E a), μ.IsHaarMeasure := by
  open scoped GlobalTheory.CuspRep.CuspidalL2GL in
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem haarG_ex (a : ℕ) : ∃ ν : Measure (G a), ν.IsHaarMeasure := by
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (G a) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

def dw0 (N : ℕ) : DomWeight N := ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

theorem infinitesimal_weight_zero (n : ℕ) : infOfWeight (dw0 (n - n)) = 0 := by
  haveI : IsEmpty (Fin (n - n)) := by rw [Nat.sub_self]; infer_instance
  simp [infOfWeight]

theorem chainEx_of (h2 : G8.GlobalComplexCoefficients) (h3 : G8.G3) (h4 : G8.G4) : ChainEx := by
  intro E _ _ _ hE n hn μ e hμ lam
  obtain ⟨ι, hι, a, l₁, l₂, sg, hsg, hgeo⟩ := h2 E hE n hn μ e hμ lam
  choose μG hG using haarGA_ex E
  choose νC hC using haarG_ex
  have c4 : ∀ a b : ℕ, ∃ c : ℂ, c ≠ 0 ∧ _ := fun a b =>
    @h4 E _ _ _ hE a b _ ⟨rfl⟩ _ ⟨rfl⟩ _ ⟨rfl⟩ _ ⟨rfl⟩ (μG a) (hG a) (μG b) (hG b) (νC a) (hC a) (νC b) (hC b)
  choose c hc0 hc using c4
  let K : ℕ := n * Fintype.card (InfinitePlace E)
  refine ⟨{
    ι := Option ι
    a := fun o => o.elim n a
    l₁ := fun o => match o with | none => lam | some i => l₁ i
    l₂ := fun o => match o with | none => fun _ => dw0 (n - n) | some i => l₂ i
    le := fun o => match o with | none => le_rfl | some i => (hsg i).2.1
    inf := fun o v => match o with
      | none => by simp [infinitesimal_weight_zero]
      | some i => (hsg i).2.2 v
    μG := μG
    hG := hG
    νC := νC
    hC := hC
    c := fun o => match o with | none => 0 | some i => sg i / (c (a i) (n - a i) * 2 ^ K)
    eq := ?_ }⟩
  intro S hS K' f hK' hf u₁ u₂ hu φ₁ φ₂ hφ hreg val ψ hlef z hz
  rw [Fintype.sum_option]
  simp only [zero_mul, zero_add]
  have hstep : ∀ i : ι, sg i / (c (a i) (n - a i) * 2 ^ K) *
      ellSum2 (μG (a i)) (μG (n - a i)) (adel S (u₁ (a i)) (u₂ (a i)) (ψ (some i)) (φ₁ (a i)) (φ₂ (a i))) =
      z * (sg i * geomSt2 S (l₁ i) (l₂ i) (seen (φ₁ (a i)) (φ₂ (a i)))) := by
    intro i
    have hai := (hsg i).2.1
    obtain ⟨t₁, t₂, t₃, -⟩ := hφ (a i) hai
    rw [hc (a i) (n - a i) S hS (u₁ (a i)) (u₂ (a i)) (hu (a i)).1 (hu (a i)).2 (l₁ i) (l₂ i) (val (some i))
      (ψ (some i)) (φ₁ (a i)) (φ₂ (a i)) (hlef (some i)) t₁ t₂, hz (some i),
      h3 E hE (a i) (n - a i) S hS (l₁ i) (l₂ i) _ t₃ (hreg (some i))]
    have hK : (a i + (n - a i)) * Fintype.card (InfinitePlace E) = K := by
      simp only [K, Nat.add_sub_of_le hai]
    rw [hK]
    have h2K : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero _ two_ne_zero
    have hc' := hc0 (a i) (n - a i)
    field_simp
  calc z * geomU S lam f = ∑ i, z * (sg i * geomSt2 S (l₁ i) (l₂ i) (seen (φ₁ (a i)) (φ₂ (a i)))) := by
        rw [← Finset.mul_sum]
        exact congrArg (z * ·) (hgeo S hS K' f (fun a' => seen (φ₁ a') (φ₂ a')) hK' hf fun a' ha' =>
          ⟨(hφ a' ha').2.2.1, (hφ a' ha').2.2.2⟩)
    _ = _ := Finset.sum_congr rfl fun i _ => (hstep i).symm

end PositivityTheory.Rg.BcB.F.F0

end
end

