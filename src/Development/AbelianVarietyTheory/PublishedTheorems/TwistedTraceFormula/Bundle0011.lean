module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
section
namespace I195MixedCoordinates_c8055b1c0896c062cd00c0d6

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_c8055b1c0896c062cd00c0d6

@[expose] public section

noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW

variable {D : D7}

section SlopeTestRemainingChoices

variable {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r)

def stab : Subgroup (GA D T) where
  carrier := {q | ∃ α : GL (Fin r) (AE D), mt T q ⬝ d.jX = d.jX ⬝ α.1}
  one_mem' := ⟨1, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := fun ⟨α, h⟩ ⟨β, h'⟩ => ⟨α * β, by
    rw [mt_mul, Matrix.mul_assoc, h', cancel₂ h, Units.val_mul, Matrix.mul_assoc]⟩
  inv_mem' := fun {q} ⟨α, h⟩ => ⟨α⁻¹, by
    have e := cancel₂ h (α⁻¹).1
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at e
    conv_lhs => rw [← e, cancel₂ (mt_inv_mul T q), Matrix.one_mul]⟩

theorem eq_of_mul_jX {q : GA D T} {α : Mx D r r} (h : mt T q ⬝ d.jX = d.jX ⬝ α) : α = d.pX ⬝ (mt T q ⬝ d.jX) := by
  rw [h, cancel₂ d.pX_jX, Matrix.one_mul]

def onX : stab d →* GL (Fin r) (AE D) :=
  MonoidHom.mk' (fun q => q.2.choose) fun p q => Units.ext <| by
    have h1 := p.2.choose_spec
    have h2 := q.2.choose_spec
    have h3 := (p * q).2.choose_spec
    generalize p.2.choose = α, q.2.choose = β, (p * q).2.choose = γ at *
    rw [eq_of_mul_jX d h3, Subgroup.coe_mul, mt_mul, Matrix.mul_assoc, h2, cancel₂ h1, Matrix.mul_assoc,
      cancel₂ d.pX_jX, Matrix.one_mul, Units.val_mul]

theorem mul_jX (q : stab d) : mt T q ⬝ d.jX = d.jX ⬝ (onX d q).1 := q.2.choose_spec

theorem levi_mem (α : GL (Fin r) (AE D)) : d.levi α ∈ stab d := ⟨α, d.levi_jX α⟩

def absDet : stab d →* ℝ≥0 := (absA D).comp (Matrix.GeneralLinearGroup.det.comp (onX d))

def HasIw (K : Subgroup (GA D T)) : Prop := ∀ h : GA D T, ∃ q : stab d, ∃ k ∈ K, h = q * k

theorem continuous_onX : Continuous (onX d) := by
  have h : Continuous fun q : stab d => (onX d q).1 :=
    (continuous_const.matrix_mul (((continuous_mt T).comp continuous_subtype_val).matrix_mul continuous_const)).congr
      fun q => (eq_of_mul_jX d (mul_jX d q)).symm
  exact Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun q => by simp⟩

theorem continuous_absDet : Continuous (absDet d) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact continuous_absE.comp (Units.continuous_iff.2
    ⟨(Units.continuous_val.comp (continuous_onX d)).matrix_det,
      (Units.continuous_coe_inv.comp (continuous_onX d)).matrix_det.congr fun p => by
        rw [MonoidHom.comp_apply, ← map_inv]; rfl⟩)

theorem isClosed_stab : IsClosed (stab d : Set (GA D T)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have h1 : IsClosed {q : GA D T | mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt T q ⬝ d.jX))} :=
    isClosed_eq ((continuous_mt T).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_const.matrix_mul ((continuous_mt T).matrix_mul continuous_const)))
  have key : ∀ p q : GA D T, mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt T q ⬝ d.jX)) → mt T p * mt T q = 1 →
      d.pX ⬝ (mt T p ⬝ d.jX) * (d.pX ⬝ (mt T q ⬝ d.jX)) = 1 := fun p q hq e => by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hq, cancel₂ e, Matrix.one_mul, d.pX_jX]
  convert h1.inter (h1.preimage continuous_inv) using 1
  refine Set.ext fun q => ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨⟨_, _, key q q⁻¹ h.2 (mt_mul_inv T q),
    key q⁻¹ q h.1 (mt_inv_mul T q)⟩, h.1⟩⟩
  · obtain ⟨α, h⟩ := h
    exact h.trans (congrArg _ (eq_of_mul_jX d h))
  · obtain ⟨α, h⟩ := inv_mem h
    exact h.trans (congrArg _ (eq_of_mul_jX d h))

variable (b : GL (Fin T.rank) (AE D))

def rhoH (T : HSp D) (r : ℕ) : ℝ := ((T.rank : ℝ) - r) / 2

def sphericalSection (s : ℂ) : GA D T → ℂ := fun h => npow (iwAbs (absDet d) (Kmax T b) h) (s + rhoH T r)

def sphericalEisenstein (h : GA D T) : ℂ → ℂ := fun s => cosetSum (stab d) (GQ T) (sphericalSection d b s) h

def EisensteinRegularAt (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (ε : ℝ) (A : ℂ → GA D T → ℂ), 0 < ε ∧
    (∀ s ∈ Metric.ball s₀ ε, s ≠ s₀ → ∀ h, A s h = (s - s₀) ^ k * cont (sphericalEisenstein d b h) s) ∧
    (∀ h, DifferentiableOn ℂ (A · h) (Metric.ball s₀ ε)) ∧
    ContinuousOn (fun x : ℂ × GA D T => A x.1 x.2) (Metric.ball s₀ ε ×ˢ Set.univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ ε, ∀ h, ‖A s h‖ ≤ C * Grow.height T h ^ N

def eisensteinResidue : ℂ := laurent (sphericalEisenstein d b 1) (rhoH T r) (-1)

def EisensteinContinues : Prop :=
  (∀ s : ℂ, rhoH T r < s.re → ∀ h, CosetConv (stab d) (GQ T) (sphericalSection d b s) h) ∧ (∀ h, Continues (sphericalEisenstein d b h)) ∧
    (∀ s₀, ∃ k, EisensteinRegularAt d b s₀ k) ∧ eisensteinResidue d b ≠ 0 ∧
    ∀ h, PoleLE (sphericalEisenstein d b h) (rhoH T r) 1 ∧ ResidueAt (sphericalEisenstein d b h) (rhoH T r) (eisensteinResidue d b)

end SlopeTestRemainingChoices

section Schwartz

variable {S T T' : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))

def projK {K : Subgroup (GA D T)} (ν : Measure K) (φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ k, om (1, (k : GA D T)) φ w ∂ν

def ikeda (ψ : AddChar (AF D.host.F) ℂ) {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t S.rank))
    (𝓕 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) : WO S T' → ℂ := (_root_.I195MixedCoordinates_c8055b1c0896c062cd00c0d6.target d) S ψ μ 𝓕 φ 0

theorem ikeda_apply (ψ : AddChar (AF D.host.F) ℂ) {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t S.rank))
    (𝓕 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) (w : WO S T') :
    ikeda ψ d μ 𝓕 φ w = ∫ ξ in 𝓕, φ (d.jX ⬝ ξ + d.j0 ⬝ w) ∂μ := by
  refine integral_congr_ae (.of_forall fun ξ => (d.integrandT_eq φ 0 ξ w).trans ?_)
  rw [map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  rfl

variable (θ : InfFam D) (τ : D.what₂.Tau)

def centreAct (T : HSp D) (p : MvPolynomial ℕ ℂ) (f : GA D T → ℂ) : GA D T → ℂ := polyAct (gelf θ T τ) p f

def omCentreS (p : MvPolynomial ℕ ℂ) (φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => centreAct θ τ S p (fun g => om (g, 1) φ w) 1

def omCentreT (p : MvPolynomial ℕ ℂ) (φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => centreAct θ τ T p (fun h => om (1, h) φ w) 1

end Schwartz

section Integrals

variable {S T T₀ : HSp D} {r : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
  (m : Measure (GA D T))

def ThetaPairConv (φ : WO S T → ℂ) (E : GA D T → ℂ) (g : GA D S) : Prop :=
  Integrable (descend (GQ T) fun h => thetaKO om g h φ * E h) (autMeasure T m)

def thetaPair (φ : WO S T → ℂ) (E : GA D T → ℂ) (g : GA D S) : ℂ :=
  ⨍ q, descend (GQ T) (fun h => thetaKO om g h φ * E h) q ∂autMeasure T m

def thetaInt (φ : WO S T → ℂ) : GA D S → ℂ := thetaPair om m φ 1

variable (θ : InfFam D) (τ : D.what₂.Tau) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D))

def IsRegElt (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) : Prop :=
  (∀ φ, IsThetaFunO ψ S T φ → omCentreS om θ τ zG φ = omCentreT om θ τ zH φ) ∧
  (∀ φ, IsThetaFunO ψ S T φ → ∀ g, Grow.RapidDec T fun h => thetaKO om g h (omCentreT om θ τ zH φ)) ∧
  (∀ s, centreAct θ τ T zH (sphericalSection d b s) = P.eval s • sphericalSection d b s) ∧ P ≠ 0

def regInt (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) (φ : WO S T → ℂ) (g : GA D S) : ℂ → ℂ :=
  fun s => (eisensteinResidue d b * P.eval s)⁻¹ * thetaPair om m (omCentreT om θ τ zH φ) (fun h => sphericalEisenstein d b h s) g

def RegIntProps (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) (φ : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T (omCentreT om θ τ zH φ) ∧ ∀ g,
    Continues (regInt om m θ τ d b zH P φ g) ∧ PoleLE (regInt om m θ τ d b zH P φ g) (rhoH T r) 1 ∧
    ∀ (s : ℂ) (E : GA D T → ℂ), (∀ h, HolValueAt (sphericalEisenstein d b h) s (E h)) →
      ThetaPairConv om m (omCentreT om θ τ zH φ) E g ∧
      (P.eval s ≠ 0 → HolValueAt (regInt om m θ τ d b zH P φ g) s
        ((eisensteinResidue d b * P.eval s)⁻¹ * thetaPair om m (omCentreT om θ τ zH φ) E g))

def regRes (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) (φ : WO S T → ℂ) : GA D S → ℂ :=
  fun g => laurent (regInt om m θ τ d b zH P φ g) (rhoH T r) (-1)

end Integrals

end GlobalTheory.RegSW

namespace GlobalTheory.Published

open GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)

def RegularisedSiegelWeilFirstTerm : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * V.rank → T'.rank < T.rank → 0 < T'.rank →
  ∀ (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp V) × GA D T →* Module.End ℂ (WO (dblSp V) T → ℂ))
    (ω' : GA D (dblSp V) × GA D T' →* Module.End ℂ (WO (dblSp V) T' → ℂ)),
    IsWeilDatumO ψ (dblSp V) T 1 χ ω → IsWeilDatumO ψ (dblSp V) T' 1 χ ω' →
  ∀ (a : GL (Fin V.rank) (AE D)) (b : GL (Fin T.rank) (AE D)), IsMaj V a → IsMaj T b →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → HasIw d (Kmax T b) →
  ∀ (μ₀ : Measure (WO V T)) (𝓕₀ : Set (WO V T)), IsCovolOne (ratL T V) μ₀ 𝓕₀ →
  ∀ (μ₁ : Measure (Mx D t (dblSp V).rank)) (𝓕₁ : Set (Mx D t (dblSp V).rank)), IsCovolOne (ratMx D _ _) μ₁ 𝓕₁ →
  ∀ (ν : Measure (Kmax T b)), ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ (m : Measure (GA D T')), m.IsHaarMeasure →
    (∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsThetaFunO ψ (dblSp V) T (projK ω ν φ) ∧
      IsThetaFunO ψ (dblSp V) T' (ikeda ψ d μ₁ 𝓕₁ φ)) ∧
    (∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
      EisPoleLE V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) 1) ∧
    (IsAniso T' → (∀ φ', IsThetaFunO ψ (dblSp V) T' φ' → ∀ g, ThetaPairConv ω' m φ' 1 g) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
        EisCoeffAt V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) (-1)
          (κ • thetaInt ω' m (ikeda ψ d μ₁ 𝓕₁ (projK ω ν φ)))) ∧
    ∀ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r'), IsAniso T₀ → 0 < r' →
    ∀ b' : GL (Fin T'.rank) (AE D), IsMaj T' b' → HasIw d₀ (Kmax T' b') → ∀ θ : InfFam D, IsInfFam θ →
      EisensteinContinues d₀ b' ∧ (∀ τ, ∃ zG zH P, IsRegElt ψ ω' θ τ d₀ b' zG zH P) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ zG zH P, IsRegElt ψ ω' θ τ d₀ b' zG zH P →
        (∀ φ', IsThetaFunO ψ (dblSp V) T' φ' → RegIntProps ψ ω' m θ τ d₀ b' zH P φ') ∧
        ∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
          EisCoeffAt V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) (-1)
            (κ • regRes ω' m θ τ d₀ b' zH P (ikeda ψ d μ₁ 𝓕₁ (projK ω ν φ)))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMean

variable {D : D7} {A B : HSp D}

def thetaMean {S T : HSp D} (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D T))
    (f : WO S T → ℂ) : GA D S → ℂ :=
  fun g => ⨍ q, AutomorphicL2Unitary.descend (GQ T) (fun h => thetaKO ω g h f) q ∂autMeasure T ν

theorem lagr_add (z z' : WO A B) : lagr A B (z + z') = lagr A B z + lagr A B z' := Matrix.ext fun i k => by
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k <;>
    simp only [Matrix.add_apply, lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, neg_add]

theorem lagr_rat (γ : Matrix (Fin B.rank) (Fin A.rank) D.host.E) :
    lagr A B (rat γ) = ratW B (dblSp A) (Matrix.of fun i => pairVec finSumFinEquiv (γ i) (-(γ i))) :=
  Matrix.ext fun i k => by
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k <;>
      simp only [lagr, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, ratW, rat, Matrix.of_apply,
        Matrix.map_apply, pairVec_inl, pairVec_inr, Pi.neg_apply,
        map_neg]

theorem continuous_lagr : Continuous (lagr A B) := continuous_matrix fun i k => by
  obtain ⟨i1, -⟩ := lattice_Mx D B.rank A.rank
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k
  · simp only [lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    exact continuous_id.matrix_elem i j
  · simp only [lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    exact (continuous_neg (G := WO A B)).matrix_elem i j

theorem hO_lagr (z z' : WO A B) : hO (dblSp A) B (lagr A B z) (lagr A B z') = 0 := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, lagr, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg, neg_zero,
    Finset.sum_neg_distrib, add_neg_cancel]

theorem symplOH_lagr (z z' : WO A B) : symplOH (dblSp A) B (lagr A B z) (lagr A B z') = 0 := by
  rw [symplOH, symplO, hO_lagr, mul_zero, map_zero, mul_zero]

variable {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}

section Zero

variable {f : WO (dblSp A) B → ℂ} {μ μ' : Measure (WO A B)} {𝓨 𝓨' : Set (WO A B)}
  {ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)}

theorem periodic_lagr (hf : IsThetaFunO ψ (dblSp A) B f) :
    ∀ γ ∈ ratMx D B.rank A.rank, ∀ z, f (lagr A B (γ + z)) = f (lagr A B z) := by
  rintro _ ⟨γ, rfl⟩ z
  change f (lagr A B (rat γ + z)) = _
  rw [lagr_add, lagr_rat, hf.quasi, ← lagr_rat, symplOH_lagr, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem integrableOn_lagr (hμ : IsCovolOne (ratL B A) μ 𝓨) (hf : IsThetaFunO ψ (dblSp A) B f) :
    IntegrableOn (fun z => f (lagr A B z)) 𝓨 μ :=
  covolOne_integrableOn hμ _ (hf.cont.comp continuous_lagr) (periodic_lagr hf)

end Zero

variable {S T : HSp D} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}
  (hω : IsWeilDatumO ψ S T χ χ' ω) (hf : IsThetaFunO ψ S T f)
include hω hf

theorem leftInv_theta (g : GA D S) : LeftInv (GQ T) fun h => thetaKO ω g h f := fun γ hγ h => by
  have := hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres (g, h) f hf)
  rwa [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at this

variable {ν : Measure (GA D T)} [ν.IsHaarMeasure]

theorem thetaMean_eq {𝓕 : Set (GA D T)} (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) (g : GA D S) :
    thetaMean ω ν f g = ⨍ h in 𝓕, thetaKO ω g h f ∂ν := by
  rw [thetaMean, average_eq, setAverage_eq, integral_quotMeasure h𝓕, measureReal_def, quotMeasure_univ h𝓕]
  simp only [(leftInv_theta hω hf g).descend_mk, measureReal_def]

end GlobalTheory.ThetaMean

namespace GlobalTheory.Published

open GlobalTheory.ThetaMean

def SiegelWeilAnisotropicUnitary : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 1 ≤ B.rank → IsAniso B →
  ∀ (χB : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ (dblSp A) B 1 χB ω →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) →
  ∀ (μ : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) μ 𝓨 →
  ∀ ν : Measure (GA D B), ν.IsHaarMeasure →
  ∀ f : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B f → IsKFinVec ω (Khat A a) f →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B ν)) ∧
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B)
      ((if A.rank < B.rank then 1 else 2 : ℂ) • thetaMean ω ν f)

end GlobalTheory.Published

end
end

