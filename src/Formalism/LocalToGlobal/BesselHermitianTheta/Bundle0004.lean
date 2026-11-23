module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

@[expose] public section

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsKinf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (g : GA D V) : Prop :=
  g ∈ GinfC V ∧ ∀ τ, ∃ b : Mat (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2, IsKC b ∧
    b * A τ = A τ * infMat D.sp.cm.sig V.gram (θ τ) g

def IsRealW (V W : HSp D) (x : WA V W) : Prop := x.map (finPart D) = 0

def IsRealDir (V W : HSp D) (L : ℝ →+ WA V W) : Prop := Continuous L ∧ ∀ t, IsRealW V W (L t)

def dRho (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  fun x => deriv (fun t : ℝ => Heisenberg₂ ψ V W (L t) f x) 0

def annOp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (J : WA V W →+ WA V W) (L : ℝ →+ WA V W)
    (f : WA V W → ℂ) : WA V W → ℂ :=
  fun x => dRho ψ V W L f x + Complex.I * dRho ψ V W (J.comp L) f x

def valTau (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) (a : AF D.host.F) : ℝ :=
  (θ τ (infPart D (algebraMap (AF D.host.F) (AE D) a))).re

structure IsFockCx (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V W : HSp D)
    (A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (B : ∀ τ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2) (Fin W.rank) ℂ)
    (J : WA V W →+ WA V W) : Prop where
  cont : Continuous J
  real : ∀ x, IsRealW V W x → IsRealW V W (J x)
  sq : ∀ x, IsRealW V W x → J (J x) = -x
  symp : ∀ x y, IsRealW V W x → IsRealW V W y → sympl V W (J x) (J y) = sympl V W x y
  kcomm : ∀ k k', IsKinf θ V A k → IsKinf θ W B k' → ∀ x, IsRealW V W x →
    J (actHom V W k k' x) = actHom V W k k' (J x)
  defin : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x, IsRealW V W x →
    (∀ τ, 0 ≤ ε * valTau θ τ (sympl V W (J x) x)) ∧ ((∀ τ, valTau θ τ (sympl V W (J x) x) = 0) → x = 0)

def IsPolFock (ψ : AddChar (AF D.host.F) ℂ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V W : HSp D)
    (A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (B : ∀ τ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2) (Fin W.rank) ℂ)
    (f : WA V W → ℂ) : Prop :=
  ∃ J : WA V W →+ WA V W, IsFockCx θ V W A B J ∧ ∃ N : ℕ, ∀ Ls : Fin N → (ℝ →+ WA V W),
    (∀ i, IsRealDir V W (Ls i)) → (List.ofFn Ls).foldr (fun L g => annOp ψ V W J L g) f = 0

structure KfinTied {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) where

  cpt : ∀ (V : HSp D) (τ : D.what₂.Tau),
    Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ
  cpt_gram : ∀ V : HSp D, V.SigOK → ∀ τ,
    (cpt V τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cpt V τ = gramAt D V τ

  bas : ∀ V : HSp D, Matrix (Fin V.rank) (Fin V.rank) D.host.E
  bas_unit : ∀ V : HSp D, V.SigOK → IsUnit (bas V).det

  bas_orth : ∀ V : HSp D, V.SigOK → ∀ i j, i ≠ j →
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (bas V) * V.gram * bas V) i j = 0

  cpt_bas : ∀ V : HSp D, V.SigOK → ∀ τ a i j,
    (cpt V τ * (bas V).map (tauE D τ)) a i ≠ 0 → (cpt V τ * (bas V).map (tauE D τ)) a j ≠ 0 → i = j

  kfin : AllSome (IsInfFam (D := D)) fun θ => ∀ (V W : HSp D), V.rank ≠ W.rank → V.SigOK → W.SigOK →
    ∀ Φ : X.Sch V W, Φ ∈ X.kfin V W ↔ IsPolFock Wl.ψ θ V W (cpt V) (cpt W) (Wl.evS V W Φ)

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure TwRuleEq {X : ThetaX D} (T : ThetaTied D X)
    (om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Prop where
  twW : ∀ (V W : HSp D) χ χ' ν, V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V g x →
      om V W χ (χ' * ν) (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • om V W χ χ' (g, h)
  twV : ∀ (V W : HSp D) χ χ' ν, V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot W h x →
      om V W (χ * ν) χ' (g, h) = ((T.eChr ν x : Circle) : ℂ) • om V W χ χ' (g, h)

structure WeilCompatibleEquivariance {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) : Prop where

  evS_range : ∀ V W : HSp D, V.rank = W.rank → Set.range (Wl.evS V W) = {f | IsThetaFun Wl.ψ V W f}

  om_heis : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ g h w₀ Φ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W w₀ (Wl.evS V W Φ) →
      Wl.evS V W (Wl.om V W χ χ' (g, h) Φ') = Heisenberg₂ Wl.ψ V W (actHom V W g h w₀) (Wl.evS V W (Wl.om V W χ χ' (g, h) Φ))

  om_aut : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ Φ, Wl.evS V W (Wl.om V W χ χ' (γ, γ') Φ) 0 = Wl.evS V W Φ 0

  om_cont : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ Φ w, Continuous fun p : GA D V × GA D W => Wl.evS V W (Wl.om V W χ χ' p Φ) w

  om_unit : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∀ p Φ, ∫ w in 𝓕, ‖Wl.evS V W (Wl.om V W χ χ' p Φ) w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖Wl.evS V W Φ w‖ ^ 2 ∂μ

  om_split : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : X.Sch V W →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) →
        ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (Wl.om V W χ χ' (g, h) Φ) = (r : ℂ) * (splitFac V W (T.eChr χ) (T.eChr χ') x y : ℂ) * ℓ Φ

  om_tw : TwRuleEq T Wl.om

  th : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → V.SigOK →
    ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ (Φ : X.Sch V W) (F : X.cusp V) (h : GA D W),
      T.ev W (X.th V W χ χ' Φ F) h =
        (T.petC V : ℂ) * ∫ g in 𝓕, Wl.evS V W (Wl.om V W χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def latVWS (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, (∀ v ∈ S, evalV D.host.F v α = 0) ∧
    ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ L0c D V, ∃ y ∈ L0c D W,
      w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (if V.rank ≤ W.rank then a * star (x i) * y j else a * x i * star (y j))}

def UnramOutside (D : D7) (χ : (AE D)ˣ →* Circle) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D →
    (∀ v ∈ S, Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D (x : AE D)) = 1) →
    χ x = 1

def WeilUnramifiedCondition {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) : Prop :=
  ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ S, UnramOutside D (T.eChr χ) S → UnramOutside D (T.eChr χ') S →
    ∀ k ∈ KsphC V S, ∀ k' ∈ KsphC W S, ∀ Φ : X.Sch V W,
      (∀ u ∈ latVWS V W S, Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) = Wl.evS V W Φ) →
      Wl.om V W χ χ' (k, k') Φ = Φ

end Formalism.L2.Theta

end
end

