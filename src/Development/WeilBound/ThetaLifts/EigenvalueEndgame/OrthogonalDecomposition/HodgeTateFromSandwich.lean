module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Notions

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}



def LocMap (om : Rep σ X W) (v : Pl F) (T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ)) : Prop :=
  (∀ φ ∈ SB _, IsRapid (Y := W) (T φ)) ∧ ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → T φ₁ = fun x => T φ (x * h)

def Comes (om : Rep σ X W) (v : Pl F) (f : UA σ W.J → ℂ) : Prop :=
  ∃ (m : ℕ) (T : Fin m → ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ)) (φ : Fin m → (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, LocMap om v (T i) ∧ φ i ∈ SB _) ∧ f = ∑ i, T i (φ i)

end Notions

def LocDecomp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', IsRapid (Y := G.W) f →
    ∀ v, X.Good v → v ≠ B.v₁ → Comes om v f ∧ Comes om' v f

def PairLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n' : ℕ) (X' : Spc F E n') (M' : Model σ X' W) (χX' χW' : Chr F E) (om' : Rep σ X' W) (r₁ s₁ : ℕ),
    IsPair B M' χX' χW' om' r₁ s₁ r' s' → n + n' = d → χW = χX / χX' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), chrW χW t (unifAt v) ≠ 1 →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, Comes om' v f → ∀ Ψ ∈ schA F _, ∀ u ∈ UAt σ X (evFin F v), ∀ g, th om μ D f Ψ (g * u) = th om μ D f Ψ g

def ThAut : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, IsRapid (Y := W) f → ∀ Ψ ∈ schA F _, Continuous (th om μ D f Ψ) ∧ ∀ γ ∈ ratU σ X.J, ∀ g, th om μ D f Ψ (γ * g) = th om μ D f Ψ g

def ThZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → 1 ≤ r → 1 ≤ s → 3 ≤ n → 1 ≤ d →
    (∀ t : E →ₐ[F] Fv F B.v₁, chrW χW t ≠ 1) →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, IsRapid (Y := W) f → (∀ Ψ ∈ schA F _, ∀ g, th om μ D f Ψ g = th om μ D f Ψ 1) → ∀ Ψ ∈ schA F _, ∀ g, th om μ D f Ψ g = 0

def ThPerp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ f, IsRapid (Y := W) f → ∀ Ψ ∈ schA F _, M.Conv om Ψ → (∃ (C : ℝ) (k : ℕ), ∀ h, ∫ g in M.dom, ‖theta om Ψ g h‖ ∂M.μ ≤ C * (ht h : ℝ) ^ k) →
    (∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ → ∀ g, th om μ D f Ψ g = 0) →
    Perp W (M.I om Ψ) f

end PositivityTheory.ThKEnd.Orth

end
