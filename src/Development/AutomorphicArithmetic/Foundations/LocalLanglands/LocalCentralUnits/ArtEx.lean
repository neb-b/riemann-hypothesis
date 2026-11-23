module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335

@[expose] public section

theorem UpperTheory.Zero.LLC.artEx :
    UpperTheory.Zero.LLC.ArtEx := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨a, ha, fun b hb => ?_⟩
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds E Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w
  refine MonoidHom.ext fun σ => hinj ?_
  exact (hb.glob art hart σ).trans (ha.glob art hart σ).symm
