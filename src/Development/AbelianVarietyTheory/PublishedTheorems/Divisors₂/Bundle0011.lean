module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.Published

def ComplementaryThetaInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n a a' r : ℕ) (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (M : Model σ V W) (M' : Model σ V' W)
      (ψ : AddChar (AF F) ℂ) (χV χW χV' χW' : Chr F E) (om : Rep σ V W) (om' : Rep σ V' W),
      a + a' = 2 * n → a = a' + 2 * r → 0 < r → 0 < a' → IsStd ψ →
      (∀ i j, σ (V.J j i) = V.J i j) → V.J.det ≠ 0 → (∀ i j, σ (V'.J j i) = V'.J i j) → V'.J.det ≠ 0 →
      (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χV a →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χV' a' →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW (a + a') →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW' (a + a') →
      IsHecke F E χV → IsHecke F E χV' → IsHecke F E χW → IsHecke F E χW' →
      M.IsWeil ψ χV χW om → M'.IsWeil ψ χV' χW' om' →
    ∀ v : Pl (F := F), IsField (Fv F v ⊗[F] E) →
      (∃ Cy : Matrix (Fin (a + a')) (Fin n) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) W.J) Cy) →
      (∃ P : Matrix (Fin a) (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fv F v ⊗[F] E),
        Pᵀ * JR (F := F) (Fv F v) V.J * P.map (sigR (Fv F v) σ) =
          (Matrix.fromBlocks (JR (Fv F v) V'.J) 0 0 (Matrix.fromBlocks 0 1 1 0) :
            Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fv F v ⊗[F] E))) →
      (∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χV z = χV' z ∧ χW z = 1 ∧ χW' z = 1) →
      augAt om' v ≠ SB _ ∧
      (∀ N : Submodule ℂ (_ → ℂ), augAt om' v ≤ N → N ≤ SB _ → (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _,
        Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) → N = augAt om' v ∨ N = SB _) ∧
      ∃ p : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (((Fin a' × Fin (a + a') → Fv F v) → ℂ) ⧸ augAt om' v),
        (SB _).map p = (SB _).map (augAt om' v).mkQ ∧ augAt om v ≤ LinearMap.ker p ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
          Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
          p φ = (augAt om' v).mkQ φ' → p φ₁ = (augAt om' v).mkQ φ₁'

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published

def ThetaSubInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (om : Rep σ X W) (N : Submodule ℂ (SInf F (Fin n × Fin d))) : Prop :=
  N ≤ M.Pol ψ τ ∧
  (∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ N) ∧
  (∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f f₁ → f₁ - f ∈ N) ∧
  (∀ γ ∈ Lines σ W, ∀ f ∈ N, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → f₁ ∈ N) ∧
  ∀ k ∈ KInf σ W τ, ∀ f ∈ N, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ N

def HoweDualityReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ _), StrictMono N → (∀ i, ThetaSubInf M ψ τ om (N i)) → m ≤ L) ∧
        ∀ N N', ThetaSubInf M ψ τ om N → ThetaSubInf M ψ τ om N' → N ≠ M.Pol ψ τ → N' ≠ M.Pol ψ τ → N ⊔ N' ≠ M.Pol ψ τ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.Published

section Local

variable {G H Y V T : Type} [Group G] [Group H] [TopologicalSpace Y] [AddCommGroup V] [Module ℂ V] [AddCommGroup T]
  [Module ℂ T]

def IsLeftHom (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (f : SB Y →ₗ[ℂ] V) : Prop :=
  ∀ (g : G) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (g, 1) φ → f φ₁ = π g (f φ)

def IsPairHom (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (τ : Representation ℂ H T)
    (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T) : Prop :=
  ∀ (g : G) (h : H) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (g, h) φ → f φ₁ = TensorProduct.map (π g) (τ h) (f φ)

def IsBigTheta (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (Θ : Representation ℂ H T)
    (p : SB Y →ₗ[ℂ] V ⊗[ℂ] T) : Prop :=
  IsPairHom om π Θ p ∧ Function.Surjective p ∧ ∀ φ, p φ = 0 ↔ ∀ f, IsLeftHom om π f → f φ = 0

def HoweDualityFor [TopologicalSpace G] [TopologicalSpace H] (om : G × H →* Module.End ℂ (Y → ℂ)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible → GlobalTheory.PRep.IsAdmissible π →
    (∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℂ T) (Θ : Representation ℂ H T) (p : SB Y →ₗ[ℂ] V ⊗[ℂ] T),
      IsBigTheta om π Θ p ∧ GlobalTheory.PRep.IsSmooth Θ ∧ IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule ∧
        ∀ N N' : Subrepresentation Θ, IsCoatom N → IsCoatom N' → N = N') ∧
    ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ H T), τ.IsIrreducible → GlobalTheory.PRep.IsSmooth τ →
      ∀ f : SB Y →ₗ[ℂ] V ⊗[ℂ] T, IsPairHom om π τ f → f ≠ 0 →
        (∀ f' : SB Y →ₗ[ℂ] V ⊗[ℂ] T, IsPairHom om π τ f' → ∃ a : ℂ, f' = a • f) ∧
        ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ G V'), π'.IsIrreducible →
          GlobalTheory.PRep.IsAdmissible π' → ∀ f' : SB Y →ₗ[ℂ] V' ⊗[ℂ] T, IsPairHom om π' τ f' → f' ≠ 0 → Nonempty (π.Equiv π')

end Local

def HoweDualityUnitary : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E),
    IsHerm c JA → ξ ≠ 0 → (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ χA χB : Eˣ →* Circle, Continuous χA → Continuous χB → ResEtaPow (R := k) ⊥ χA n → ResEtaPow (R := k) ⊥ χB d →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)),
    IsUWeilPair c (sbClass k) ψ ξ JA JB co χA χB om →
    HoweDualityFor om ∧ HoweDualityFor (om.comp (MulEquiv.prodComm (M := UG c JB) (N := UG c JA)).toMonoidHom)

def ThetaSub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl (F := F)) (N : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ)) : Prop :=
  augAt om v ≤ N ∧ N ≤ SB _ ∧
    ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilRepresentationExists
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published

def WeilRepresentationExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om

end GlobalTheory.Published

end
end

