module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.InfMatchOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.GReadOf
section
noncomputable section

namespace UpperTheory.BaseChangeIdentities.GelfandReading

open PositivityTheory.Rg.BcB.F

theorem exists_transport {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S T : StarSubalgebra ℂ A}
    (h : S = T) (χ : S →⋆ₐ[ℂ] ℂ) : ∃ χ' : T →⋆ₐ[ℂ] ℂ, (∀ y : T, ∃ z : S, z.1 = y.1 ∧ χ' y = χ z) ∧
      ∀ x (hx : x ∈ T) (hx' : x ∈ S), χ' ⟨x, hx⟩ = χ ⟨x, hx'⟩ := by
  subst h
  exact ⟨χ, fun y => ⟨y, rfl, rfl⟩, fun _ _ _ => rfl⟩

theorem gRead_of {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
    [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type} (gen : Γ → Prod' H d)
    (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (a₀ : Γ) (c : Γ → ℂ)
    (hc : ∀ x, (gen x).2 v = c x • v) (h₀ : c a₀ = 1) (Q : Prop)
    (hQ : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      ((∀ y, ‖χ y‖ ≤ ‖(y : H s →L[ℂ] H s)‖) ∧
        (∀ x, χ ⟨(gen x).1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = c x) ∧
        χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0) → Q) : GRead gen β m v Q := by
  intro s χ hn heig hX
  obtain ⟨χ', h1, h2⟩ := exists_transport (Rd.projAdjoin gen s (star (β s ^ m) * β s ^ m)) χ
  have ha : (gen a₀).2 v = v := by rw [hc, h₀, one_smul]
  refine hQ s χ' ⟨fun y => ?_, fun x => ?_, fun h => hX ((h2 _ _ _).symm.trans h)⟩
  · obtain ⟨z, e1, e2⟩ := h1 y
    rw [e2, ← e1]
    exact hn z
  · exact (h2 _ _ _).trans
      (R3.chi_pin gen a₀ v hv ha s _ χ heig ⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩ (c x) (hc x))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem chiTr : BC.ChiTr := fun _ _ _ _ _ _ _ _ _ _ G Q h1 hQ =>
  gRead_of (H := G.H) G.gen G.βop G.m G.v G.v_ne G.a₀ (fun x => G.c x G.i₀) (fun x => (G.vblk x).1) h1 Q hQ

end UpperTheory.BaseChangeIdentities.GelfandReading

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.IdentOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF PositivityTheory.Rg.BcB.F.borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities.GelfandReading

set_option maxHeartbeats 2000000 in
theorem ident_of (hD : DerVal) (hI : InfMatch) : BC.Ident := by
  intro hR E _ _ _ n π S T F₀ F i χ hχ O
  have e0 : (F.t₀ i).val O.χa O.χb = 1 := (O.eigArch (.inl ()) (F.t₀ i) rfl rfl).symm.trans (hχ.2.1 (.inl ()))
  have e1 : ∀ v s m side, (F.tD i v s m side).val O.χa O.χb = F.dval (i, v, s, m, side) := fun v s m side =>
    (O.eigArch (.inr (.inl (i, v, s, m, side))) (F.tD i v s m side) (if_pos rfl) rfl).symm.trans
      (hχ.2.1 (.inr (.inl (i, v, s, m, side))))
  have key := fun v s m => hD E _ _ _ _ _ _ _ _ (F₀.A i) F.κ (F.ψ i (F.d.eL _)) (F.ψ i (F.d.eL _))
    (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) v s m O.χa O.χb
  refine ⟨fun τ => congrFun (hI E _ O.χa (F₀.A i).χa fun v s m _ _ => ?_) τ,
    fun τ => congrFun (hI E _ O.χb (F₀.A i).χb fun v s m _ _ => ?_) τ⟩
  · have h1 := e1 v s m false
    have h2 := (key v s m).1
    have h3 : F.tD i v s m false = (F₀.A i).pt (fun v' => if v' = v then [(s, m)] else []) (fun _ => []) (F.ψ i (F.d.eL _))
        (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) := by
      unfold RunFrame.tD
      congr 1 <;> funext v' <;> simp
    rw [h3] at h1
    have h4 := h2.symm.trans h1
    erw [e0] at h4
    simpa [RunFrame.dval, zVal] using h4
  · have h1 := e1 v s m true
    have h2 := (key v s m).2
    have h3 : F.tD i v s m true = (F₀.A i).pt (fun _ => []) (fun v' => if v' = v then [(s, m)] else []) (F.ψ i (F.d.eL _))
        (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) := by
      unfold RunFrame.tD
      congr 1 <;> funext v' <;> simp
    rw [h3] at h1
    have h4 := h2.symm.trans h1
    erw [e0] at h4
    simpa [RunFrame.dval, zVal] using h4

end UpperTheory.BaseChangeIdentities.GelfandReading

end
end

