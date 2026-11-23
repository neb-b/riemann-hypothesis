module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SqrtDiscr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0038
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GenHost

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GdEx
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.gd_ex :
    GC.Hypotheses₂ → GdFrameEx := by
  intro hP Ω _ _ _ K _ _ _ _ l _ c _ N _ e ψ D B hB
  have hG := gen_gd Ω K l c N e ψ D B hB
  obtain ⟨Q, hQ, hS⟩ := seed_cl Ω l c _ _ _ B _ _ hG
  obtain ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, w, ⟨k, -⟩, hOk, hBig, hw, hwQ, hle⟩ :=
    frame_ex hP l _ _ _ B _ _ hG Q hQ
  refine ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, ⟨k⟩, hOk, hBig, hS L w k.ab k.gal hw hwQ hle ?_⟩
  obtain ⟨h, hg⟩ := k.g0
  refine ⟨g₁, ?_, ?_⟩
  · rw [k.gal]
    refine ⟨h, ?_⟩
    have h1 := k.del ⟨g₁, h⟩
    rw [hg] at h1
    exact h1.symm.trans Φ.g0.2
  · have h1 := k.psi ⟨g₁, h⟩
    rw [hg] at h1
    exact h1 ▸ hOk.baseSubgroup_spec
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HostEx
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.host_ex :
    GC.Hypotheses₂ → HostFrameEx := by
  intro hP Ω _ _ _ l _ c _ N _ e ψ o₁ hD σ hσ B hB
  obtain ⟨Hb, hG⟩ := gen_host Ω l c N e ψ o₁ hD σ hσ B hB
  obtain ⟨Q, hQ, hS⟩ := seed_cl Ω l c _ _ σ B _ Hb hG
  obtain ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, w, ⟨k, -⟩, hok, hbig, hw, hwQ, hle⟩ := frame_ex hP l _ _ σ B _ Hb hG Q hQ
  refine ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, ⟨k⟩, hok, hbig, hS L w k.ab k.gal hw hwQ hle ?_⟩
  obtain ⟨h, hg⟩ := k.g0
  refine ⟨g₁, ?_, ?_⟩
  · rw [k.gal]
    refine ⟨h, ?_⟩
    have h1 := k.del ⟨g₁, h⟩
    rw [hg] at h1
    exact h1.symm.trans Φ.g0.2
  · have h1 := k.psi ⟨g₁, h⟩
    rw [hg] at h1
    have h2 := hok.baseSubgroup_spec
    rw [h1] at h2
    exact h2
end

