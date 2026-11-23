module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIrr
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.algIrr :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), IsMultiGl (eEnd Ξ) ∧ ∀ W, Stab (eEnd Ξ) W → W = ⊥ ∨ W = ⊤ := by
  intro E _ _ _ a Ξ
  refine ⟨?_, fun W hW => ?_⟩
  · obtain ⟨h1, h2⟩ := eLRel E a _ Ξ.dmat (GlobalTheory.AlgInfChar.dmat_bracket Ξ)
    let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
    have hf : ∀ τ i j, eEnd Ξ τ i j = f (eL Ξ.dmat τ i j) := fun _ _ _ => rfl
    refine ⟨fun τ i j k l => ?_, fun s t hst i j k l => ?_⟩
    · have h := congrArg f (h1 τ i j k l)
      simpa only [hf, map_sub, map_mul, apply_ite f, map_zero] using h
    · rw [hf, hf, ← map_mul, ← map_mul, h2 s t hst]
  · let S : Subalgebra ℂ (Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ × Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) :=
      { carrier := {p | ∀ w ∈ W, p.1 *ᵥ w ∈ W}
        mul_mem' := fun {p q} hp hq w hw => by
          rw [Prod.fst_mul, ← Matrix.mulVec_mulVec]
          exact hp _ (hq w hw)
        add_mem' := fun {p q} hp hq w hw => by
          rw [Prod.fst_add, Matrix.add_mulVec]
          exact W.add_mem (hp w hw) (hq w hw)
        algebraMap_mem' := fun c w hw => by
          rw [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.fst_one, Matrix.smul_mulVec, Matrix.one_mulVec]
          exact W.smul_mem c hw }
    exact Ξ.irred W fun y v hv => (pairAlg E a Ξ Ξ S fun τ i j w hw => hW τ i j w hw).2 y v hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Wigner
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.wigner : GlobalTheory.Published.WignerVanishingGL := by
  intro E _ _ _ a π Ξ m m' hm hm' hne
  obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hne
  obtain ⟨u, hu⟩ : ∃ u : ℂ, ((m τ).map (u + ·)).prod ≠ ((m' τ).map (u + ·)).prod := by
    by_contra h
    exact hτ (msetSep _ _ fun u => not_not.1 fun h' => h ⟨u, h'⟩)
  obtain ⟨a1, a2, a3⟩ := tensA E a π Ξ
  obtain ⟨b1, b2, b3⟩ := tensB E a π Ξ
  obtain ⟨α, hα⟩ := alphaReal E a _ (tensorK π Ξ) (lieA π Ξ) (lieB π Ξ) a1 b1 (lieA_commute π Ξ) a2 b2 τ _ _ _
    (a3 τ _ (hm τ) u) (b3 τ _ (hm' τ) u) hu
  exact homot E a _ (tensorK π Ξ) (tensorLie π Ξ) α hα (infAbs E a _ _ _ (tensDer E a π Ξ))
end

