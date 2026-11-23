module

public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.SplitInv
section
noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def Kills0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 →
    ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      (R.p' f = 0 ∨ ∃ v, Rf.p' v (φ v) = 0) → G.M'.I om' (pure f φ) = 0

end PositivityTheory.ThKG.Loc

end
end

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.SplitInv2
section
noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def SplitInv2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∀ f, ((∃ Φ ∈ PolData B G.M, f = G.M.I om Φ) ∨
      ∃ Φ' ∈ PolData B G.M', (Φ' ∈ G.M'.So B.ψ B.τ₁ ∨ G.q = 0) ∧ f = G.M'.I om' Φ') →
    ∀ fa fb, Split2 W₁ H' X f fa fb → (∀ u ∈ unip σ G.W H', ∀ h, fa (u * h) = fa h ∧ fb (u * h) = fb h) ∧
      (f = 0 → fa = 0 ∧ fb = 0)

end PositivityTheory.ThKG.Loc

end
end

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedMultiplicityOneProportional
section
noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def UnramifiedMultiplicityOneProportional : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' a₁ a₁' : ℕ) (G : Geo σ a a') (G₁ : Geo σ a₁ a₁') (X : Chars F E) om om' om₁ om₁' R Rf R₁ Rf₁
    (H' : Plane E (a + a') (a₁ + a₁')) (i₀ i₁ : ℕ) χ r, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    StepTy G G₁ X χ r → H'.IsAdapted σ B G.W G₁.W i₀ i₁ → ∀ v ∉ X.T, ∀ lam lam', IsFiniteLocalEquivariantMap om om₁ H' v χ r (Rf.p v) (Rf₁.p v) lam → IsFiniteLocalEquivariantMap om om₁ H' v χ r (Rf.p v) (Rf₁.p v) lam' →
      ∀ c : ℂ, lam' (Rf.p v (G.M.vac v)) = c • lam (Rf.p v (G.M.vac v)) → lam' = c • lam

end PositivityTheory.ThKG.Loc

end
end

