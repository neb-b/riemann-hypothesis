module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvOfNear
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0421
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepLocalWeilActionLineCharactersCancel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LineCancel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isComp_mul (p : Place D k) {χ χ' : (AE D)ˣ →* Circle} {μ μ' : kˣ →* ℂˣ} (h : p.IsComp χ μ)
    (h' : p.IsComp χ' μ') : p.IsComp (χ * χ') (μ * μ') := by
  intro x a ha
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, h x a ha, h' x a ha, Circle.coe_mul]

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ μ) :
    p.IsComp χ⁻¹ μ⁻¹ := by
  intro x a ha
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x a ha, Circle.coe_inv]

theorem om_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ ν : kˣ →* ℂˣ) (g : GL a k)
    (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om (μ * ν) g h Φ = (((ν (Matrix.GeneralLinearGroup.det g) * (ν (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ)) : ℂ) •
      om μ g h Φ := by
  funext t
  simp only [om, Pi.smul_apply, smul_eq_mul, MonoidHom.mul_apply, mul_inv, Units.val_mul]
  ring

theorem val_smul_inv {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ)
    (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (A : WO S.B.V S.J.W → ℂ) (B : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ)
    (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (z : ℂˣ) :
    S.val c₁ c₂ ((z : ℂ) • A) (((z⁻¹ : ℂˣ) : ℂ) • B) φ f g h₁ h₂ = S.val c₁ c₂ A B φ f g h₁ h₂ := by
  have e : S.con ((z : ℂ) • A) (((z⁻¹ : ℂˣ) : ℂ) • B) g h₁ h₂ = S.con A B g h₁ h₂ := by
    unfold Dbl2.con
    rw [map_smul, map_smul, GlobalTheory.HandHom.flatBF_smul, GlobalTheory.HandHom.flatFB_smul]
    funext u v
    unfold GlobalTheory.Unf.contr
    congr 1
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  unfold Dbl2.val
  rw [e]

end GlobalTheory.QPl.LineCancel

namespace GlobalTheory.QPl.LineCancel

theorem scal_one {G : Type} [Group G] (μ ζ : G →* ℂˣ) (a x : G) : ζ x = ((μ⁻¹ * ζ) * μ) a * (ζ⁻¹ a * (ζ⁻¹ x)⁻¹) := by
  rw [inv_mul_cancel_comm]
  simp only [MonoidHom.inv_apply, inv_inv, mul_inv_cancel_left]

theorem scal_two {G : Type} [Group G] (μ ζ : G →* ℂˣ) (x : G) : (ζ x)⁻¹ = (μ⁻¹ * (μ * ζ⁻¹)) x := by
  rw [inv_mul_cancel_left, MonoidHom.inv_apply]

end GlobalTheory.QPl.LineCancel

namespace GlobalTheory.QPl.LineCancel

theorem val_om_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ))
    (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)),
    (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ →
  ∀ (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ) (F : GA D S.B'.V → ℂ)
    (a : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) (x : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)
    (Φ₁ Φ₁' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k))
    (Φ₂ Φ₂' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k)),
    Φ₁'.1 = om Q.μ₁ a x Φ₁.1 → Φ₂'.1 = om Q.μ₂ x y Φ₂.1 →
    S.val c₁ c₂ (S.s₁.om (Q.gl₀ a, Q.gl₁ x) (T₁ Φ₁)) (S.s₂.om (Q.gl₁ x, Q.gl₂ y) (T₂ Φ₂)) φ F 1 1 1 =
      S.val c₁ c₂ (T₁ Φ₁') (T₂ Φ₂') φ F 1 1 1 := by
  intro D ψ hψ σ S Q T₁ T₂ h₁ h₂ c₁ c₂ φ F a x y Φ₁ Φ₁' Φ₂ Φ₂' e₁ e₂
  obtain ⟨ζ, hζ⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit Q.q) S.χz
  have k₁' : (ofSplit Q.q).IsComp S.χ₁ Q.μ₁⁻¹ := by simpa using isComp_inv _ Q.comp₁
  have k₂' : (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := by simpa using isComp_inv _ Q.comp₂
  have hV₁ : (ofSplit Q.q).IsComp S.s₁.χV (Q.μ₁⁻¹ * ζ) := by rw [S.V₁]; exact isComp_mul _ k₁' hζ
  have hW₁ : (ofSplit Q.q).IsComp S.s₁.χW Q.μ₁⁻¹ := by rw [S.W₁]; exact k₁'
  have hV₂ : (ofSplit Q.q).IsComp S.s₂.χV Q.μ₂⁻¹ := by rw [S.V₂]; exact k₂'
  have hW₂ : (ofSplit Q.q).IsComp S.s₂.χW (Q.μ₂⁻¹ * ζ) := by rw [S.W₂]; exact isComp_mul _ k₂' hζ
  have r₁ := _root_.GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil (Q.μ₁⁻¹ * ζ) Q.μ₁⁻¹ hV₁ hW₁
    (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.F.G₀ Q.F.G₁ T₁ h₁ (Q.gl₀ a) a (Q.gl₁ x) x (Q.loc₀ a)
    (Q.loc₁ x) Φ₁ (((ζ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) • Φ₁') (by
      rw [Submodule.coe_smul, e₁, mul_inv, inv_inv, om_mul, smul_smul, ← Units.val_mul]
      congr 2
      exact scal_one Q.μ₁ ζ _ _)
  have r₂ := _root_.GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil Q.μ₂⁻¹ (Q.μ₂⁻¹ * ζ) hV₂ hW₂
    (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.F.G₁ Q.F.G₂ T₂ h₂ (Q.gl₁ x) x (Q.gl₂ y) y (Q.loc₁ x)
    (Q.loc₂ y) Φ₂ ((((ζ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) • Φ₂') (by
      rw [Submodule.coe_smul, e₂, inv_inv, mul_inv, inv_inv]
      congr 2
      exact scal_two Q.μ₂ ζ _)
  rw [r₁, r₂, map_smul, map_smul]
  exact val_smul_inv S c₁ c₂ _ _ φ F 1 1 1 _

end GlobalTheory.QPl.LineCancel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepValueEqTrilinearTensorValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TriStep

theorem val_eq_tensorVal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ), (∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) → ∀ Φ₁ Φ₂ (f : GlobalTheory.TriStep.space Q), HasTensorVal (fun Ψ Φ₀ => app (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1) := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hCL T hT Φ₁ Φ₂ f
  have hcQ : Q.c + 1 + 1 = 2 * (σ + 1) := by have := Q.F.bes.1; omega
  obtain ⟨hψc, hψ1⟩ := GlobalTheory.hasConductor_one_continuous_ne_one Q.k Q.ψk Q.cond
  have hsd : IsSelfDual Q.ψk Q.ν := ((GlobalTheory.SplitWeil.selfDual_measure Q.k Q.ψk hψc hψ1).2.1 Q.cond Q.ν).1 Q.unitVol
  obtain ⟨hcol, hrow, hop, ⟨m, Ψ, Φ₀, hfl⟩, hsum⟩ :=
    GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum Q.k Q.ψk hψc hψ1 Q.ν hsd Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) hcQ Q.μ₁ Φ₁ Φ₂
  obtain ⟨Ξ, hΞ, hΛΞ⟩ := hCL ⟨_, hcol⟩ ⟨_, hrow⟩
  refine ⟨m, Ψ, Φ₀, hfl, ?_⟩
  have e1 : S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1 = valK S Q c₁ c₂ φ Λ Ξ f.1 := by
    unfold Dbl2.val Dbl2.con valK
    rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
      map_one, map_one, rTrans_one, Module.End.one_apply, Module.End.one_apply, hU₁ Φ₁ ⟨_, hcol⟩ rfl,
      hU₂ Φ₂ ⟨_, hrow⟩ rfl, hΛΞ]
  have e2 : Ξ = ∑ i, GlobalTheory.LocFlat.CFac.prodSB (Ψ i) ⟨_, hop (Φ₀ i)⟩ := by
    apply Subtype.ext
    funext x
    rw [hΞ, hsum m Ψ Φ₀ hfl x]
    simp [Submodule.coe_sum, Finset.sum_apply, GlobalTheory.LocFlat.CFac.prodSB_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, ← hT, e2, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) (Ψ i)) ⟨_, hop (Φ₀ i)⟩
  exact (LinearMap.congr_fun h f).symm

end GlobalTheory.TriStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EntryDatumTransportBadPrimeAnyTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.EntryAny

open GlobalTheory.Transport.Entry

theorem entry_transport_any : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 < B.R.m) (al : (I.idx a).β i) (be : (I.idx a).β (i + 1)) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀) =
        Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) := by
  intro B X I hI l u a i hm al be P p q p' q' k y k' y' hp hpN hp' hpN' hq hq'
  have hX := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hL := hI.idx_ok a
  have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.Transport.Entry.qOf_pos P.1).ne'
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · obtain ⟨M, hM, H⟩ := exists_modulus hp hp' hq hq' ⟨P.1, hP⟩ (pow_ne_zero (I.cst a).B hq0)
    refine ⟨M, hM, fun M₀ hM₀ x x₀ hx => ?_⟩
    obtain ⟨U, U', hU, hU', h⟩ := H M₀ hM₀ x x₀ hx
    have hu := exp_le_val_qOf (GlobalTheory.UnfoldTwoSided.degOne_bad hX.ok l.pr hI.sel_ok P)
    unfold Formalism.L2.Col.frsF
    simp only [dif_pos hP]
    refine (eq_of_near (P := P.1) _ hq0 (val_qOf_lt_one P.1) (pow_ne_zero (I.cst a).B hq0) (fun κ κ' hκ hκ' z => ?_)
      (hL.xiInv i (by omega) al be P) _ _ U U' (hU.mono hu) (hU'.mono hu) h).symm
    refine xiAt_inFr hX l.pr hI.ch_ok hI.sel_ok hL (by omega) al be P κ κ' ?_ ?_ z
    · rw [hL.depthG P hP, pow_one]
      exact hκ
    · rw [hL.depthG P hP, pow_one]
      exact hκ'
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    refine ⟨Formalism.L2.Col.qOf P.1 ^ (I.cst a).B, pow_pos (GlobalTheory.Transport.Entry.qOf_pos P.1) _, fun M₀ hM₀ x x₀ hx => ?_⟩
    have hd := GlobalTheory.Transport.TwistRead.qread I u a i P hQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I hI l a) p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hx
    set z₀ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ with hz₀
    set z₁ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x with hz₁
    have hMv : P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) ≤
        P.1.valuation B.fields.E (((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).B) := by
      obtain ⟨c, rfl⟩ := hM₀
      rw [Nat.cast_mul, map_mul, Nat.cast_pow]
      refine mul_le_of_le_one_right' ?_
      simpa using P.1.valuation_le_one (K := B.fields.E) (c : 𝓞 B.fields.E)
    have e : z₁ = z₀ + (z₁ - z₀) := by abel
    rw [e]
    refine (hL.xiInv i (by omega) al be P z₀ (z₁ - z₀) fun s l => ?_).symm
    refine intAt_inv_mul (pow_ne_zero _ hq0) ?_
    have e2 : (z₁ - z₀) (Pi.single s 1) l = (LinearMap.toMatrix' z₁ - LinearMap.toMatrix' z₀) l s := by
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, LinearMap.sub_apply, Pi.sub_apply]
    rw [e2]
    exact (hd l s).trans hMv

end GlobalTheory.Transport.EntryAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeCombinationMovesLastStepDatumToChart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl

theorem exchange_posOne_last : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m) (s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h)), s₁.χW = χ Q.s → ∀ α (Tm : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] (WO (c.V Q.s) (c.V (Q.s + 1)) → ℂ)), (ofSplit Q.q).IsModel c.ψ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 (by omega)) Tm → ∀ Φ Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k), Φ.1 = Q.T.Phi Q.s 0 rfl → Φα.1 = om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl) → ∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (Tm Φ) = Tm Φα := by
  intro D c v χ Q _ h s₁ hχ α Tm hTm Φ Φα hΦ hΦα
  obtain ⟨⟨ρ', hρ'⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep Q.k (Q.X Q.s ⊕ Fin (0 + 1)) (Q.X (Q.s + 1) ⊕ Fin 0)
    (Q.T.mu (Q.s + 1)) (Q.mu Q.s (by omega)).2
  have hsmooth := hsm ρ' hρ'
  obtain ⟨e, he, heL⟩ := Q.εL_at Q.s 0 h 0 rfl α
  obtain ⟨μS, hμS⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit Q.q) s₁.χV
  have hμT : (ofSplit Q.q).IsComp s₁.χW (Q.T.mu (Q.s + 1))⁻¹ := by
    intro x a hxa
    have := (Q.mu Q.s (by omega)).1 x a hxa
    rw [hχ, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this]
    simp
  have hloc1 : (ofSplit Q.q).IsLoc (Q.FY (Q.s + 1) 0 (by omega)) 1 1 := by
    have := Q.gl_loc (Q.s + 1) 0 (by omega) 1
    rwa [map_one] at this
  have key : ∀ g, s₁.om (Q.gl Q.s (0 + 1) (by omega) g, 1) (Tm Φ) = Tm (ρ' g Φ) := by
    intro g
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) c.ψ _ _ s₁.χV s₁.χW s₁.om s₁.weil μS _ hμS hμT _ _ _ _ Tm hTm
      _ g 1 1 (Q.gl_loc Q.s (0 + 1) (by omega) g) hloc1 Φ (ρ' g Φ) ?_
    rw [hρ']
    funext x
    have hu : (((μS * Q.T.mu (Q.s + 1)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((μS⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        = ((Q.T.mu (Q.s + 1) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
      rw [← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_comm (μS _), mul_assoc, mul_inv_cancel, mul_one]
    simp only [om, Pi.smul_apply, smul_eq_mul, map_one, inv_one, Units.val_one, inv_inv]
    rw [← hu]
    ring
  have hN : ∀ g ∈ N Q.k (Q.X Q.s) (0 + 1) (0 + 1), g = 1 := by
    intro g hg
    have hle : N Q.k (Q.X Q.s) (0 + 1) (0 + 1) ≤ ⊥ := by
      refine (Subgroup.closure_le _).2 fun g' hg' => ?_
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      ext r s
      refine hg' r s ?_
      rcases r with r | r <;> rcases s with s | s <;> simp [GlobalTheory.RootEx.lev, Fin.val_eq_zero]
    exact Subgroup.mem_bot.1 (hle hg)
  let lx : Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k →
      (SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] ℂ) :=
    fun x => (LinearMap.proj x).comp (SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k)).subtype
  have hsum : Φα = e.sum (fun g a => a • ρ' g Φ) := by
    apply Subtype.ext
    funext x
    have h1 := he _ ρ' hsmooth (lx x) (fun g hg w => by
        rw [hN g hg]
        simp [GlobalTheory.RootEx.simpleSum]) Φ (fun j => by
        apply Subtype.ext
        rw [hρ', Submodule.coe_smul, hΦ, (Q.laws.1 Q.s 0 rfl).1 j])
    have h2 : (Φα : Matrix _ _ _ → ℂ) x = lx x (ρ' (Q.rep Q.s 0 rfl α) Φ) := by
      simp only [lx, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, hΦα]
      rw [hρ', hΦ]
    have h3 : ((e.sum fun g a => a • ρ' g Φ : SB _) : Matrix _ _ _ → ℂ) x = lx x (e.sum fun g a => a • ρ' g Φ) := rfl
    rw [h2, h3, map_finsuppSum]
    refine h1.trans ?_
    simp [GlobalTheory.PosOne.comb, map_smul]
  rw [heL]
  show (Finsupp.mapDomain _ e).sum (fun g a => a • s₁.om (g, 1) (Tm Φ)) = Tm Φα
  rw [Finsupp.sum_mapDomain_index (h := fun g (a : ℂ) => a • s₁.om (g, 1) (Tm Φ)) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rw [hsum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, key]

end GlobalTheory.QPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.BasePoint

variable {D : D7}

theorem algebraMap_placeIdem_mem {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D (· = v) := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨hinf, hcomp⟩ := placeIdempotent_infinite_and_finite_components D v _ α rfl
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  refine ⟨hinf, fun w hw => ?_⟩
  rw [hcomp, h0 w hw, TensorProduct.zero_tmul]

theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  exact ⟨ha.1, fun w hw => ha.2 w (fun hp => hw (h w hp))⟩

theorem mulVec_mem' {I : Ideal (AE D)} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) : ∀ i, (A *ᵥ y) i ∈ I := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => I.mul_mem_left _ (hy j)

theorem mulVec_fix {V : HSp D} {e : AE D} {ε : AF D.host.F} {u v : Pl D} (hε : IsPlaceIdem D u ε)
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {h : GA D V} (hs : SuppAt e V h) (huv : v ≠ u)
    {y : Fin V.rank → AE D} (hy : ∀ l, y l ∈ idAt D (· = v)) : mt V h *ᵥ y = y := by
  have hz : ∀ l, algebraMap (AF D.host.F) (AE D) ε * y l = 0 := fun l =>
    (placeIdem_acts D u ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact huv) (hy l))
  have h1 : (mt V h - 1) *ᵥ y = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc (mt V h - 1) i j * y j = (algebraMap (AF D.host.F) (AE D) ε * (mt V h - 1) i j) * y j := by
          rw [← he, hs i j]
      _ = (mt V h - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring
      _ = 0 := by rw [hz j, mul_zero]
  calc mt V h *ᵥ y = ((mt V h - 1) + 1) *ᵥ y := by rw [sub_add_cancel]
    _ = y := by rw [Matrix.add_mulVec, h1, Matrix.one_mulVec, zero_add]

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem pr_e_mul (q : SplitPt D k) (a : AE D) : q.pr (q.e * a) = q.pr a := by
  rw [← q.sec_pr a, q.pr_sec]

theorem e_mul_eps (q : SplitPt D k) {ε : AF D.host.F} (he : q.e + cA D q.e = algebraMap (AF D.host.F) (AE D) ε) :
    q.e * algebraMap (AF D.host.F) (AE D) ε = q.e := by
  rw [← he, mul_add, q.split.1, q.split.2.1, add_zero]

theorem map_mt_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hne : q.v ≠ q'.v) {V : HSp D} {h : GA D V}
    (hs : SuppAt q'.e V h) : (mt V h).map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
  show (mt V h).map q.pr = 1
  obtain ⟨ε, hε, he⟩ := q.above
  obtain ⟨ε', hε', he'⟩ := q'.above
  have h0 : q.pr (algebraMap (AF D.host.F) (AE D) ε') = 0 := by
    rw [← pr_e_mul, ← e_mul_eps q he, mul_assoc,
      (placeIdem_acts D q.v ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact Ne.symm hne)
        (algebraMap_placeIdem_mem hε')), mul_zero, map_zero]
  ext i j
  have hij := hs i j
  rw [he'] at hij
  have h1 : q.pr ((mt V h - 1) i j) = 0 := by rw [← hij, map_mul, h0, zero_mul]
  have e2 : (mt V h) i j = (mt V h - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by simp
  rw [Matrix.map_apply, e2, map_add (f := _), h1, zero_add]
  by_cases hij' : i = j <;> simp [Matrix.one_apply, hij']

theorem xi_ne (q : SplitPt D k) : (GlobalTheory.LocMod.ofSplit q).xi ≠ 0 := by
  unfold GlobalTheory.LocMod.Place.xi GlobalTheory.LocMod.Place.pr
  intro h0
  have h1 : (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0) * (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem latV_iff_hat' (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hat L :=
  ⟨GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice D S L P y, GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice D S L P y hy⟩

theorem finE_mulVec' (S : HSp D) (x : GA D S) (y : Fin S.rank → AE D) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((mt S x *ᵥ y) i))) =
      (Formalism.IndefR.Lev.finE S x).val *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) := by
  have h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) := by
    ext i j
    rfl
  rw [h]
  ext i
  exact RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i

theorem exists_base (V : HSp D) (Λ L₀ : Lat V) (hΛ : IsSelfDualC V Λ) (hL₀ : IsSelfDualC V L₀) :
    ∃ t₀ ∈ GfC V, ∀ P, Moves V t₀ Λ L₀ P := by
  obtain ⟨t₀, ht₀, htr⟩ := (GlobalTheory.AdIsom.adelicIsometries D).2.2.1 V V (LinearEquiv.refl _ _) (fun _ _ => rfl) Λ L₀ hΛ hL₀
    ∅ (by intro w hw; simp at hw) 0 (fun _ => 0) (fun _ => 0) (by simp) (by simp)
  rw [LinearEquiv.refl_toLinearMap, GlobalTheory.AdIsomCorrection.mA_id, Matrix.mul_one] at htr
  refine ⟨t₀, ht₀, fun P y hy => ?_⟩
  rw [latV_iff_hat' V Λ P y hy, latV_iff_hat' V L₀ P _ (mulVec_mem' _ hy), finE_mulVec']
  exact htr.2.1 _

variable {J : Type} [Fintype J] {kk : J → Type} [∀ i, Field (kk i)] [∀ i, ValuativeRel (kk i)]
  [∀ i, TopologicalSpace (kk i)] [∀ i, IsNonarchimedeanLocalField (kk i)]

theorem exists_corr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (q : ∀ i, SplitPt D (kk i))
    (hinj : Function.Injective (fun i => (q i).v)) (M : ∀ i, GL (Fin V.rank) (kk i)) (t₀ : GA D V) (s : Finset J) :
    ∃ g ∈ GfC V, (∀ v, (∀ i, v ≠ (q i).v) → ∀ y : Fin V.rank → AE D, (∀ l, y l ∈ idAt D (· = v)) → mt V g *ᵥ y = y) ∧
      ∀ i ∈ s, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V (g * t₀) β (M i).val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, fun v _ y _ => by rw [mt_one, Matrix.one_mulVec], fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hfix, hmv⟩ := ih
    obtain ⟨h, hsupp, hmove⟩ :=
      (_root_.GlobalTheory.LocMod.normalFrames_and_basePoint_exist D (kk j) (GlobalTheory.LocMod.ofSplit (q j)) (xi_ne (q j))).2.2 V β (M j) (g * t₀)
    refine ⟨h * g, mul_mem (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (q j).split hsupp) hg, ?_, ?_⟩
    · intro v hv y hy
      rw [mt_mul, ← Matrix.mulVec_mulVec, hfix v hv y hy]
      obtain ⟨ε, hε, he⟩ := (q j).above
      exact mulVec_fix hε he hsupp (hv j) hy
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · rw [mul_assoc]; exact hmove
      · intro b hb
        have hij : (q i).v ≠ (q j).v := fun h' => hj (by rw [← (hinj h' : i = j)]; exact hi)
        rw [mul_assoc, mt_mul, Matrix.mul_assoc, Matrix.map_mul, map_mt_eq_one (q i) (q j) hij hsupp, Matrix.one_mul]
        exact hmv i hi b hb

end GlobalTheory.FinPl.BasePoint


open GlobalTheory.FinPl.BasePoint in
theorem GlobalTheory.FinPl.BasePoint.exists_move : ∀ (D : D7) (V : HSp D) (Λ L₀ : Lat V) (β : GL (Fin V.rank) (Lev.EAf D)), IsSelfDualC V Λ → IsSelfDualC V L₀ → ∀ (J : Type) [Fintype J] (k : J → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ M : ∀ i, GL (Fin V.rank) (k i), ∃ t ∈ GfC V, ∃ L : Lat V, IsSelfDualC V L ∧ (∀ P, Moves V t Λ L P) ∧ (∀ v, (∀ i, v ≠ (q i).v) → latV V L (· = v) = latV V L₀ (· = v)) ∧ ∀ i, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V t β (M i).val := by
  intro D V Λ L₀ β hΛ hL₀ J _ kk _ _ _ _ q hinj M
  obtain ⟨t₀, ht₀, hmv₀⟩ := exists_base V Λ L₀ hΛ hL₀
  obtain ⟨g, hg, hfix, hmv⟩ := exists_corr V β q hinj M t₀ Finset.univ
  obtain ⟨L, hL, hmoves⟩ := (_root_.GlobalTheory.FinPl.GlobImage.glob D V Λ hΛ).1 (g * t₀)
  refine ⟨g * t₀, mul_mem hg ht₀, L, hL, hmoves, ?_, fun i => hmv i (Finset.mem_univ i)⟩
  intro v hv
  ext y
  by_cases hy : ∀ l, y l ∈ idAt D (· = v)
  · have hz : ∀ l, (mt V t₀⁻¹ *ᵥ y) l ∈ idAt D (· = v) := mulVec_mem' _ hy
    have h1 : mt V t₀ *ᵥ (mt V t₀⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
    have h2 : mt V (g * t₀) *ᵥ (mt V t₀⁻¹ *ᵥ y) = y := by
      rw [mt_mul, ← Matrix.mulVec_mulVec, h1, hfix v hv y hy]
    have a1 := hmoves (· = v) _ hz
    have a2 := hmv₀ (· = v) _ hz
    rw [h2] at a1
    rw [h1] at a2
    exact a1.symm.trans a2
  · have hsupp : ∀ (N : Lat V), IsSelfDualC V N → y ∉ latV V N (· = v) := fun N hN hyN =>
      hy (((_root_.GlobalTheory.FinPl.localComponents D (· = v)).2 V).2.2.2 N y hN.1 |>.1 hyN).1
    exact iff_of_false (hsupp L hL) (hsupp L₀ hL₀)
end
end

