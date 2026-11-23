module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalRingCardinality.DataRows

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AgreementAtAlmostAllSplitPrimes
section
open Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes

def AgreeAtAlmostAllSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) : Prop :=
  {w : PlE H | IsSplitPl H w ∧ A.locG χ w ≠ A.locG χ' w}.Finite

def HeckeCharEqOfSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ χ χ' : A.CG 1, AgreeAtAlmostAllSplit A χ χ' → χ = χ'

theorem agreeAtAlmostAllSplit_iff {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) :
    AgreeAtAlmostAllSplit A χ χ' ↔
      ∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w := by
  simp only [AgreeAtAlmostAllSplit, Filter.eventually_cofinite, Classical.not_imp]

end GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.NoLocalInvariants
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def eps (i : N.Loc) : G H.E N.Om →* (N.O i)ˣ :=
  (Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom).comp
    (cycZ (F := H.E) (Ω := N.Om) (N.l i))

end GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.SmallRowEigenvalues
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

def RowEigSmall {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) :
    Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
    ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
      ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ < ((normV w : ℕ) : ℝ) ^ (((R.t : ℝ) - 1) / 2)

theorem one_lt_normV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    1 < normV w := by
  unfold normV
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact Finite.one_lt_card

theorem rowEigSmall_of_le {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N)
    (h : ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
      ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
        ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)) :
    RowEigSmall N A := by
  intro i σ hσ w hw hu α hα
  have hrt : R.r < R.t := by have := R.rank_add_five_le; unfold Ranks.r; omega
  refine lt_of_le_of_lt (h i σ hσ w hw hu α hα) ?_
  have h1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have h2 : (R.r : ℝ) < (R.t : ℝ) := by exact_mod_cast hrt
  exact Real.rpow_lt_rpow_of_exponent_lt h1 (by linarith)

end GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaEigenspaceImage
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage

open Formalism.BasicNotions Formalism.MainNotions.N

def ThetaTMapsIntoEig {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSig N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

def MjSigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (Sig : List (Part A.CG)) : Submodule ℂ (what₂.Mj (N.j i)) :=
  ⨆ σ ∈ {σ | ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w}, what₂.isot (N.j i) σ

def ThetaTMapsIntoEigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSigOut N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem mjSig_le_mjSigOut (i : N.Loc) (Sig : List (Part A.CG)) :
    MjSig N A i Sig ≤ MjSigOut N A i Sig := by
  unfold MjSig MjSigOut
  exact biSup_mono fun σ hσ w hw => hσ.2.2 w hw.1

theorem thetaTMapsIntoEig_of_out (h : ThetaTMapsIntoEigOut N A) : ThetaTMapsIntoEig N A :=
  fun i x Sig hx hp f hf => h i x Sig hx hp f (mjSig_le_mjSigOut N A i Sig hf)

theorem thetaTMapsIntoEig_iff_map_le : ThetaTMapsIntoEig N A ↔
    ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
      x ∈ ZgoodN N A i → HasParamX N A i x Sig →
        (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x := by
  unfold ThetaTMapsIntoEig
  simp only [Submodule.map_le_iff_le_comap]
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaGramMatrix
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix

open Formalism.BasicNotions Formalism.MainNotions.N

noncomputable def thetaGram {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) :
    what₂.Mj j →ₗ[ℂ] what₂.Mj j :=
  what₂.thetaP μ j ∘ₗ what₂.thetaT μ j

def ThetaGramPositiveScalar {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) (_A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT),
    (∀ f ∈ what₂.isot (N.j i) σ,
      thetaGram what₂ (N.mu i) (N.j i) f = ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) • f) ∧
    (what₂.isot (N.j i) σ ≠ ⊥ → 0 < what₂.lamP (N.mu i) (N.j i) σ)

theorem ThetaGramPositiveScalar.norm_sq {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} {A : NAut N} (h : ThetaGramPositiveScalar N A) (i : N.Loc) (σ : what₂.FT)
    (f : what₂.Mj (N.j i)) (hf : f ∈ what₂.isot (N.j i) σ) :
    ‖what₂.thetaT (N.mu i) (N.j i) f‖ ^ 2 = what₂.lamP (N.mu i) (N.j i) σ * ‖f‖ ^ 2 := by
  have hg := (h i σ).1 f hf
  simp only [thetaGram, LinearMap.comp_apply] at hg
  have key : inner ℂ (what₂.thetaT (N.mu i) (N.j i) f) (what₂.thetaT (N.mu i) (N.j i) f)
      = ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) * inner ℂ f f := by
    show inner ℂ (LinearMap.adjoint (what₂.thetaP (N.mu i) (N.j i)) f)
      (what₂.thetaT (N.mu i) (N.j i) f) = _
    rw [LinearMap.adjoint_inner_left, hg, inner_smul_right]
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]
  simp

theorem ThetaGramPositiveScalar.eq_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} {A : NAut N} (h : ThetaGramPositiveScalar N A) (i : N.Loc) (σ : what₂.FT)
    (f : what₂.Mj (N.j i)) (hf : f ∈ what₂.isot (N.j i) σ)
    (h0 : what₂.thetaT (N.mu i) (N.j i) f = 0) : f = 0 := by
  by_contra hne
  have hpos : 0 < what₂.lamP (N.mu i) (N.j i) σ := by
    apply (h i σ).2
    intro hb
    rw [hb] at hf
    exact hne ((Submodule.mem_bot ℂ).1 hf)
  have e := h.norm_sq i σ f hf
  rw [h0, norm_zero] at e
  have e2 : what₂.lamP (N.mu i) (N.j i) σ * ‖f‖ ^ 2 = 0 := by rw [← e]; norm_num
  rcases mul_eq_zero.1 e2 with h1 | h1
  · exact absurd h1 hpos.ne'
  · exact hne (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftUniqueness
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness

open Formalism.BasicNotions Formalism.MainNotions.N

def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem eachRowHasThetaLift_iff :
    EachRowHasThetaLift N A ↔
      ∀ (i : N.Loc) (σ : what₂.FT), (∃ f ∈ what₂.isot (N.j i) σ, f ≠ 0) → ∃ P : A.AV i,
        (∃ f ∈ what₂.isot (N.j i) σ, what₂.thetaT (N.mu i) (N.j i) f ≠ 0) ∧
        ∀ f ∈ what₂.isot (N.j i) σ, what₂.thetaT (N.mu i) (N.j i) f ∈ A.typeV i P := by
  unfold EachRowHasThetaLift thetaOf
  refine forall_congr' fun i => forall_congr' fun σ => ?_
  rw [Submodule.ne_bot_iff]
  refine imp_congr_right fun _ => exists_congr fun P => and_congr ?_ ?_
  · rw [Submodule.ne_bot_iff]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, h⟩
      exact ⟨f, hf, h⟩
    · rintro ⟨f, hf, h⟩
      exact ⟨_, ⟨f, hf, rfl⟩, h⟩
  · rw [Submodule.map_le_iff_le_comap]
    rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness
end
end

