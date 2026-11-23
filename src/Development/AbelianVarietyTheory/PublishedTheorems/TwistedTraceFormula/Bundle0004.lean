module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
section
namespace GlobalTheory.Published

def GeometricLemmaFiltration : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.SmGL.JacquetOfInducedFiltration k

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.Published

def GrothendieckRingPolynomial : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)), IsSegmentClass k Z →
      ∃ Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ, Ψ (GrothGL.unit k) = 1 ∧
        (∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
          (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
          (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂), IsSmooth π₁ → IsSmooth π₂ →
            ∀ h : HasFiniteLength (prod₂ π₁ π₂), Ψ (clsGL (prod₂ π₁ π₂) h) = Ψ (clsGL π₁ h₁) * Ψ (clsGL π₂ h₂)) ∧
        ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix
open GlobalTheory.SmoothGlob (lieSet)
open scoped ContDiff

namespace GlobalTheory.GKModule

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

theorem isKStableOn_kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (kFinVec ε σ) := by
  rintro g hg v ⟨S, hS, hv, hSK⟩
  exact ⟨S, hS, hSK g hg v hv, hSK⟩

structure IsGKSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop where
  smooth : ∀ v ∈ V, SmoothVec (lieSet ε) σ v
  kFin : ∀ v ∈ V, IsKFin ε σ v
  kStable : IsKStableOn ε σ V
  lieStable : ∀ X ∈ lieSet ε, ∀ v ∈ V, dRep σ X v ∈ V

def IsAdmissibleSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop :=
  ∀ Λ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S | S ≤ V ∧ IsKTypeOf ε σ Λ S} : Submodule ℂ H)

def IsGKHom {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (ε : Fin n → Bool) (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁))
    (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) (e : kFinVec ε σ₁ →ₗ[ℂ] kFinVec ε σ₂) : Prop :=
  (∀ k ∈ Kset ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = σ₁ k v → (e w : H₂) = σ₂ k (e v)) ∧
    ∀ X ∈ lieSet ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = dRep σ₁ X v → (e w : H₂) = dRep σ₂ X (e v)

theorem isAdmissibleSub_of_finiteDimensional (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] : IsAdmissibleSub ε σ V :=
  fun _ => Submodule.finiteDimensional_of_le (sSup_le fun _ hS => hS.1)

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_det_expProd {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod).det := by
  have he : ∀ a b, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) a b := fun a b =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp
      (GlobalTheory.GardingVec.contDiff_expProd Xs)
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun s _ => contDiff_const.mul (contDiff_prod fun i _ => he _ _)

end

theorem isURepOn_det (ε : Fin n → Bool) : IsURepOn (UJset ε) (fun g => g.det • (1 : H →L[ℂ] H)) := by
  refine ⟨⟨by simp, fun a _ b _ => by ext; simp [smul_smul, mul_comm]⟩, fun g hg v => ?_, fun v => ?_⟩
  · have h1 : ‖g.det‖ = 1 := by simpa using (GlobalTheory.Published.det_isURepOn ε).1.2.1 g hg 1
    simp [norm_smul, h1]
  · have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.det • v :=
      (continuous_id.matrix_det).smul continuous_const
    simpa using this.continuousOn

theorem isGKSub_det (ε : Fin n → Bool) (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    IsGKSub ε (fun g => g.det • (1 : H →L[ℂ] H)) V ∧ IsAdmissibleSub ε (fun g => g.det • (1 : H →L[ℂ] H)) V := by
  have hK : IsKStableOn ε (fun g => g.det • (1 : H →L[ℂ] H)) V := fun g _ v hv => V.smul_mem _ hv
  refine ⟨⟨fun v _ k Xs _ => ?_, fun v hv => ⟨V, inferInstance, hv, hK⟩, hK, fun X _ v hv => ?_⟩,
    isAdmissibleSub_of_finiteDimensional _ _ _⟩
  · exact (contDiff_det_expProd Xs).smul contDiff_const
  · have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • X)).det := by
      have := (contDiff_det_expProd (fun _ : Fin 1 => X)).comp
        (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
      simpa [Function.comp_def] using this
    have h2 := ((h1.differentiable (by simp)) 0).hasDerivAt.smul_const v
    have h3 : dRep (fun g => g.det • (1 : H →L[ℂ] H)) X v = _ := h2.deriv
    rw [h3]
    exact V.smul_mem _ hv

theorem mem_UJset_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  change kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end GlobalTheory.GKModule

namespace GlobalTheory.Published

open GlobalTheory.GKModule

def AdmissibleClosure : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ V : Submodule ℂ H, IsGKSub ε σ V → IsAdmissibleSub ε σ V →
      (∀ g ∈ UJset ε, ∀ w ∈ V.topologicalClosure, σ g w ∈ V.topologicalClosure) ∧
        ∀ w ∈ V.topologicalClosure, IsKFin ε σ w → w ∈ V

def InfinitesimalEquivalence : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [Nontrivial H₁]
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [Nontrivial H₂]
    (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)),
    IsURepOn (UJset ε) σ₁ → IsIrredOn (UJset ε) σ₁ → IsURepOn (UJset ε) σ₂ → IsIrredOn (UJset ε) σ₂ →
    ∀ e : kFinVec ε σ₁ ≃ₗ[ℂ] kFinVec ε σ₂, IsGKHom ε σ₁ σ₂ e.toLinearMap →
      ∃ (U : H₁ ≃ₗᵢ[ℂ] H₂) (c : ℝ), 0 < c ∧ (∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) ∧
        ∀ v : kFinVec ε σ₁, U v = (c : ℂ) • (e v : H₂)

def GKGlobalisation : Prop := AdmissibleClosure ∧ InfinitesimalEquivalence

section Consequences

variable {n : ℕ} {ε : Fin n → Bool}

end Consequences

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
section
noncomputable section

open Matrix
open Formalism.REAL (Jm Kset inG)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsKTypeOf IsDS lowKSub UJset)
open Formalism.L2.Theta (SmoothVec dRep)

namespace GlobalTheory.KFinVec

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

theorem isKStableOn_kFinSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (kFinSub ε σ) := by
  rintro g hg v ⟨S, hS, hv, hK⟩
  exact ⟨S, hS, hK g hg v hv, hK⟩

def IsIrrKSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ IsKStableOn ε σ S ∧
    ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S

def IsKMapFrom (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (T : S →ₗ[ℂ] H) : Prop :=
  ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s)

def kIsotypic (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  ⨆ T : {T : S →ₗ[ℂ] H // IsKMapFrom ε σ S T}, LinearMap.range T.1

theorem range_le_kIsotypic {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
    {T : S →ₗ[ℂ] H} (hT : IsKMapFrom ε σ S T) : LinearMap.range T ≤ kIsotypic ε σ S :=
  le_iSup (fun T : {T : S →ₗ[ℂ] H // IsKMapFrom ε σ S T} => LinearMap.range T.1) ⟨T, hT⟩

def IsAdmissible (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsIrrKSub ε σ S → FiniteDimensional ℂ (kIsotypic ε σ S)

def IsLieStable (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  ∀ X, inG ε X → ∀ v ∈ S, dRep σ X v ∈ S

theorem isIrrKSub_of_isKTypeOf {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (h : IsKTypeOf ε σ Λ S) : IsIrrKSub ε σ S := by
  refine ⟨h.1, ?_, h.2.1, h.2.2.1⟩
  rintro rfl
  obtain ⟨v, hv, hv0, -⟩ := h.2.2.2.1
  exact hv0 ((Submodule.mem_bot ℂ).1 hv)

end GlobalTheory.KFinVec

namespace GlobalTheory.Published

open GlobalTheory.KFinVec

def KFiniteVectorsUnitary : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    IsAdmissible ε σ ∧
    (∀ v : H, IsKFin ε σ v → AnalyticOnUJ ε fun g => σ g v) ∧
    Dense (kFinSub ε σ : Set H) ∧
    IsLieStable ε σ (kFinSub ε σ) ∧
    ∀ S : Submodule ℂ H, S ≤ kFinSub ε σ → IsLieStable ε σ S → S = ⊥ ∨ S = kFinSub ε σ

namespace KFiniteVectorsUnitary

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem analytic [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : AnalyticOnUJ ε fun g => σ g v := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, analyticOnNhd_const, fun _ _ _ => Subsingleton.elim _ _⟩
  · exact (h n ε H σ hU hI).2.1 v hv

theorem smoothOnH [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) :
    Formalism.QuantumDeterminants.SmoothOnH (Jm ε) fun g => σ g v :=
  (h.analytic hU hI hv).smoothOnH

theorem hasDerivAt [CompleteSpace H] (h : KFiniteVectorsUnitary) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by simp [UJset, Formalism.REAL.inUJ]
  have := ((h.analytic hU hI hv).analytic_exp h1 hX 0).differentiableAt
  simp only [Matrix.one_mul] at this
  exact this.hasDerivAt

theorem of_isDS (h : KFiniteVectorsUnitary) {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) :
    IsAdmissible ε σ ∧
    (∀ v : H, IsKFin ε σ v → AnalyticOnUJ ε fun g => σ g v) ∧
    Dense (kFinSub ε σ : Set H) ∧
    IsLieStable ε σ (kFinSub ε σ) ∧
    ∀ S : Submodule ℂ H, S ≤ kFinSub ε σ → IsLieStable ε σ S → S = ⊥ ∨ S = kFinSub ε σ :=
  haveI := hσ.1
  haveI := hσ.2.1
  h n ε H σ hσ.2.2.1 hσ.2.2.2.1

end KFiniteVectorsUnitary

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.Published

def consecBlocks (l d : ℕ) : (Σ _ : Fin l, Fin d) ≃ Fin (l * d) :=
  (Equiv.sigmaEquivProd (Fin l) (Fin d)).trans finProdFinEquiv

theorem consecBlocks_val (l d : ℕ) (a : Fin l) (j : Fin d) : (consecBlocks l d ⟨a, j⟩ : ℕ) = j + d * a := rfl

def SegmentRepresentation : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d l : ℕ), 0 < d → 0 < l → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (consecBlocks l d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ l)))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SubsingletonIrrClZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.SmGL.SegModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem subsingleton_irrCl_zero : Subsingleton (IrrCl (GL (Fin 0) k)) := by
  have key : ∀ σ : IrrRep (GL (Fin 0) k),
      Nonempty ((ofChar (1 : GL (Fin 0) k →* ℂˣ)).Equiv σ.ρ) := by
    intro σ
    have := nontrivial_of_irreducible σ.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : σ.V)
    have h1 : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
    let f : (ofChar (1 : GL (Fin 0) k →* ℂˣ)).IntertwiningMap σ.ρ :=
      ⟨LinearMap.toSpanSingleton ℂ σ.V v, fun g => by rw [h1 g]; ext; simp⟩
    have hf : Function.Injective f := LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ hv)
    obtain ⟨φ⟩ := (IsSubquotient.of_injective f hf).nonempty_equiv (isIrreducible_ofChar _) σ.irr
    exact ⟨φ.symm⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨φ⟩ := key a.rep
  obtain ⟨ψ⟩ := key b.rep
  rw [← a.cl_rep, ← b.cl_rep]
  exact IrrRep.cl_eq_iff.2 ⟨φ.symm.trans ψ⟩

end GlobalTheory.SmGL.SegModel
end
end

