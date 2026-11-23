module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.PowSat
section
noncomputable section

open NumberField IsDedekindDomain
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph.PW

variable {K : Type} [Field K] [NumberField K]

private theorem ideleModule_localIdele (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule K (Neutral.B1.localIdele K v x)).1 : ℝ) =
      ‖(x : v.adicCompletion K)‖ := by
  have e : Neutral.B1.localIdele K v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x :=
    Units.ext rfl
  rw [e]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_eq_zpow (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℤ)
    (h : Valued.v x = WithZero.exp n) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  change (Ideal.absNorm v.asIdeal : ℝ) ^ (WithZero.exp n).log = _
  rw [WithZero.log_exp]

private theorem loc_eq {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← ideleModule_localIdele]
  exact h _

end UpperTheory.ConvolutionTheory.Sph.PW

open UpperTheory.ConvolutionTheory.Sph.PW in
theorem UpperTheory.ConvolutionTheory.Sph.powSat :
    UpperTheory.ConvolutionTheory.Sph.PowSat := by
  intro K _ _ χ s h v
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · rw [loc_eq h, norm_eq_zpow v _ 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]
    simp
  · have e : χ.val v = χ.loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) := rfl
    rw [e, loc_eq h, norm_eq_zpow v _ (-1) (Formalism.L2.Host.unif_spec v), zpow_neg_one,
      Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]
        exact Real.pi_pos.ne), Complex.cpow_neg]
    simp
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
section
noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

def RamSph : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [_root_.NumberField.IsTotallyComplex K]
    [_root_.NumberField.IsTotallyComplex M], (Module.finrank K M).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub M n),
    WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
      ∀ B, (Cusp.cx π).sat (w.under (𝓞 K)) B → (Cusp.cx P).sat w B

def NormRam : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], (Module.finrank K M).Prime →
    ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
      normV w = normV (w.under (𝓞 K)) ∧ (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w) ∧
        ∀ η : HChar K, IsNormChar M η → ¬ η.UnrAt (w.under (𝓞 K))

def Unlinked : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) (v : HeightOneSpectrum (𝓞 K)) B,
    (Cusp.cx π).sat v B → ∀ a ∈ B, ∀ b ∈ B, (a : ℂ) ≠ (Ideal.absNorm v.asIdeal : ℂ) * b

structure IsLiftUnr {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
    [Algebra K M] {a : ℕ} (π : CuspSub K a) (P : CuspSub M a) : Prop where
  weak : WeakBC (CG.mk π).HasSat (CG.mk P).HasSat
  sat : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (B : Multiset ℂˣ), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
    normV w = normV (w.under (𝓞 K)) ^ f → (CG.mk π).HasSat (w.under (𝓞 K)) B → (CG.mk P).HasSat w (B.map (· ^ f))
  inf : ∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M))
  loc : SplitLift (Cusp.cx π) (Cusp.cx P)

def LiftUnr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub K a,
    (∀ η : HChar K, IsNormChar M η → (CG.mk π).twist η ≠ CG.mk π) → ∃ P : CuspSub M a, IsLiftUnr π P

def QuadLiftUnr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub K a,
    (∃ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 K)) B) →
    ∃ P : CuspSub M a, IsLiftUnr π P

end UpperTheory.ConvolutionTheory.Sph
end
end

