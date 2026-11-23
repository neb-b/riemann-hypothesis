module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0012
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutLat
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutProd
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem exists_fin (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (h1 : IsHeckeCharF η)
    (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) : ∃ of, IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of ∧
      ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε hε.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ) :=
  exists_fin_A C hO h1 h2 hε

theorem fin_inf_comm (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) :=
  fin_inf_comm_A C hO hof hi p q f hf

theorem datum_of_aut (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω :=
  datum_of_aut_A C hO h1 h2 hf hof hi haut

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSer
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem ser_vacuum (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) (a : IxF F nS nT → ℂ) :
    ∃ hf : IsThetaFunOF σ JS JT ξ₀ B.ψ (serF σ JS JT ξ₀ B θ ι s Λ w a),
      Fixes (opFF hc w) (latF F E nS nT Λ) (⟨_, hf⟩ : thetaSubF σ JS JT ξ₀ B.ψ) ∧
      IsVacF σ JS JT ξ₀ B.ψ ι s (serF σ JS JT ξ₀ B θ ι s Λ w a) :=
  SerA.main C hG hR hO hs a

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitCoef
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

theorem unit_coef : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))), μW.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (w₀ : WOF F E nS (nT + nT)) (f : WOF F E nS (nT + nT) → ℂ),
        IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h w₀) (ωd (1, h) f) w *
            starRingEnd ℂ (ωd (1, h) f w) ∂μW =
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w₀ f w * starRingEnd ℂ (f w) ∂μW := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS ωd hω μ 𝓕 hμ h𝓕 h w₀ f hf
  rw [← hω.om_heis 1 h w₀ f hf]
  exact GlobalTheory.ThetaSchurF.scalar_eq hω.std.1.2.1 μ 𝓕 hμ h𝓕 (ωd (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _
    (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ w₀ f hf) hf

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

