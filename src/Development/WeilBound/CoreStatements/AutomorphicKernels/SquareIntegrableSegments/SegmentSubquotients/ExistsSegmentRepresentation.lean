module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSocleSegmentProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkSegExists

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) := by
  exact GlobalTheory.T.parabolic_induction_finite_length k (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) _
    (piTensor fun a => (x a).rep)
    (isSmooth_piTensor fun a => (x a).snd.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem exists_isLSeg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  intro k _ _ _ _ hA Δ
  have hd : ∑ a, (Δ.term a).1 = Δ.deg := Δ.sum_term_fst
  obtain ⟨hd', ⟨φ⟩⟩ := _root_.GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term hA Δ hd
  obtain ⟨τ', hτ'⟩ := _root_.GlobalTheory.CompanionTheory.LkSegSocle.exists_isSocle_prodIrr_dec hA (segDual Δ) hd'
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr Δ.term hd)
    (isSmooth_prodIrr _ _) (hasFiniteLength_prodIrr hA _ _) τ' (hτ'.of_equiv (.refl _) φ.symm)
  exact ⟨τ, hd, hτ⟩

end GlobalTheory.CompanionTheory.LkSegExists

end
