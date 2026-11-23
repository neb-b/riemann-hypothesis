module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DownNeOfHypNc
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.GlobalFormAtFrameLatNc
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.GlobalFormAnisoOfSiegelWeilFockAnisoNc
public import Mathlib

@[expose] public section

theorem ResidueKilled.sec_of_dm (h : ResidueKilled.DM) : GlobalTheory.Published.SiegelEisensteinContinuation :=
  fun D V h0 a ha hI μ b hμ hb s₁ φ hφ => (h D V h0 a ha hI μ b hμ hb s₁ φ hφ).1
