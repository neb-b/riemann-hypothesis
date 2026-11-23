module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
public import GroundTheory.AutomorphicForms.Cartan
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.GaussBinomialTwistedSumIdentity
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSmulOfMapResidueEqZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open Formalism.UG (Tj Ov qV IsUnifV Hecke IsBiInv conv dosetInd IsCommensurated GLint hAct AMF)
open GlobalTheory.LFun (KGL heckeVec IsSatVecGL satEig seg)
open GlobalTheory.PRep (fixed rightReg)

namespace GlobalTheory.CompanionTheory.Ipf.Val.SphM

section Abs

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

def orb (ρ : Representation ℂ G V) : V →ₗ[ℂ] (G → V) where
  toFun x g := ρ g x
  map_add' x y := by funext g; simp
  map_smul' c x := by funext g; simp

theorem orb_heckeVec (ρ : Representation ℂ G V) (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (x : V) :
    orb ρ (heckeVec ρ K h x) = hAct K h (orb ρ x) := by
  rw [GlobalTheory.LFun.map_heckeVec hK hh (ρ' := rightReg ℂ G V) (orb ρ) ?_ x, GlobalTheory.LFun.heckeVec_rightReg hK hh]
  intro g y
  funext a
  simp [orb, rightReg]

theorem orb_injective (ρ : Representation ℂ G V) : Function.Injective (orb ρ) := fun a b e => by
  simpa [orb] using congrFun e 1

theorem orb_mem {ρ : Representation ℂ G V} {x : V} (hx : x ∈ fixed ρ K) :
    orb ρ x ∈ AMF ℂ (⊥ : Subgroup G) K (1 : Representation ℂ (⊥ : Subgroup G) V) := by
  rintro ⟨γ, hγ⟩ g ⟨κ, hκ⟩
  have : γ = 1 := hγ
  subst this
  simp [orb, GlobalTheory.LGrp.mem_fixed.1 hx κ hκ]

theorem heckeVec_conv (hK : IsCommensurated K) {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ Hecke ℂ K) (h₂ : f₂ ∈ Hecke ℂ K)
    (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K) :
    heckeVec ρ K (conv K f₁ f₂) x = heckeVec ρ K f₁ (heckeVec ρ K f₂ x) := by
  apply orb_injective ρ
  rw [orb_heckeVec ρ hK (Formalism.UG.Final.HeckeConvMem G K ℂ hK f₁ h₁ f₂ h₂),
    Formalism.UG.Final.HeckeActMul G ⊥ K ℂ V 1 hK f₁ h₁ f₂ h₂ _ (orb_mem hx), orb_heckeVec ρ hK h₁, orb_heckeVec ρ hK h₂]

theorem heckeVec_add (hK : IsCommensurated K) {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ Hecke ℂ K) (h₂ : f₂ ∈ Hecke ℂ K)
    (ρ : Representation ℂ G V) (x : V) :
    heckeVec ρ K (f₁ + f₂) x = heckeVec ρ K f₁ x + heckeVec ρ K f₂ x := by
  unfold heckeVec
  rw [← finsum_add_distrib (GlobalTheory.LFun.finite_heckeVec hK h₁ ρ x) (GlobalTheory.LFun.finite_heckeVec hK h₂ ρ x)]
  exact finsum_congr fun c => by simp [add_smul]

theorem heckeVec_smul (z : ℂ) (f : G → ℂ) (ρ : Representation ℂ G V) (x : V) :
    heckeVec ρ K (z • f) x = z • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum]
  exact finsum_congr fun c => by simp [mul_smul]

theorem heckeVec_smul_vec (z : ℂ) (f : G → ℂ) (ρ : Representation ℂ G V) (x : V) :
    heckeVec ρ K f (z • x) = z • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum]
  exact finsum_congr fun c => by rw [map_smul, smul_comm]

end Abs

section Loc

open GlobalTheory.Hk3.MinuscTopLocal (dU)

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {v}

variable (v)

theorem heckeVec_central {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {H : Subgroup G}
    (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ H) {z : G} (hz : ∀ g, z * g = g * z) :
    heckeVec ρ H (dosetInd ℂ H z) x = ρ z x := by
  classical
  have := GlobalTheory.LFun.heckeVec_dosetInd (ρ := ρ) (K := H) hx (a := z) (R := {z})
    (fun γ hγ => by
      rw [Finset.mem_singleton.1 hγ]
      exact DoubleCoset.mem_doubleCoset.2 ⟨1, H.one_mem, 1, H.one_mem, by simp⟩)
    (fun g hg => by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
      have e : z⁻¹ * (a * z * b) = a * b := by
        rw [← hz a]; group
      rw [e]
      exact H.mul_mem ha hb)
  simpa using this

theorem diagJ_self (n : ℕ) (ϖ : Cv v) : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (Cv v)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.diagJ]
  · simp [Formalism.UG.diagJ, h]

def sc (n : ℕ) {ϖ : Cv v} (h0 : ϖ ≠ 0) : GL (Fin n) (Cv v) where
  val := ϖ • 1
  inv := ϖ⁻¹ • 1
  val_inv := by simp [smul_smul, h0]
  inv_val := by simp [smul_smul, h0]

theorem sc_central (n : ℕ) {ϖ : Cv v} (h0 : ϖ ≠ 0) (g : GL (Fin n) (Cv v)) : sc v n h0 * g = g * sc v n h0 :=
  Units.ext (by simp [sc])

theorem Tj_self (n : ℕ) {ϖ : Cv v} (h0 : ϖ ≠ 0) : Tj ℂ n (Ov K v) ϖ n = dosetInd ℂ (KGL v (n := n)) (sc v n h0) :=
  Formalism.UG.Final.TjEq (Cv v) (Ov K v) ϖ ℂ n n (sc v n h0) (by rw [diagJ_self]; rfl)

end Loc

end GlobalTheory.CompanionTheory.Ipf.Val.SphM

end
