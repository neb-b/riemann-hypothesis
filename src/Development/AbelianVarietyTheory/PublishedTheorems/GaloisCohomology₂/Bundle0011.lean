module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsEigenvalueGLOneEqCuspidalLabelGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def DepthZeroCuspidalLL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc →
    ∀ x : IrrGL (k := w.adicCompletion E), x.IsCusp →
      (fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def DepthZeroTypeInertia : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      (rc (cls σ)).mono0 ∧
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsSumMultiplicityOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

namespace GlobalTheory.Published

def LanglandsSumMultiplicityOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (𝔪 𝔫 : Multiset (Segment k)) (r t : ℕ) (π₁ : IrrRep (GL (Fin r) k)) (π₂ : IrrRep (GL (Fin t) k)),
    IsL 𝔪 π₁.ρ → IsL 𝔫 π₂.ρ →
      (∃ π : IrrRep (GL (Fin (r + t)) k), IsL (𝔪 + 𝔫) π.ρ) ∧
        ∀ π : IrrRep (GL (Fin (r + t)) k), IsL (𝔪 + 𝔫) π.ρ → jhMult π.ρ (prod₂ π₁.ρ π₂.ρ) = 1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  {𝔪 𝔫 : Multiset (Segment k)} {r t : ℕ} {π₁ : IrrRep (GL (Fin r) k)} {π₂ : IrrRep (GL (Fin t) k)}


end GlobalTheory.Published

namespace GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem IsRec.segment (H : IsRec h rc) {Δ : Segment (w.adicCompletion E)} {x : IrrGL (k := w.adicCompletion E)}
    (hx : IsLSeg Δ x.rep) :
    rc x = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  exact (H.langlands [Δ] x hx.isL).trans (WD.lpSum_zero _)

theorem IsRec.langlandsQuotient (H : IsRec h rc) {𝔪 : Multiset (Segment (w.adicCompletion E))} {s N : ℕ}
    {δ : Fin s → IrrGL (k := w.adicCompletion E)} (hδ : LFactors 𝔪 δ) (hd : ∑ i, (δ i).1 = N)
    {π : IrrRep (GL (Fin N) (w.adicCompletion E))} (hπ : IsCosocle π.ρ (prodIrr δ hd)) :
    rc (cls π) = sumList (List.ofFn fun i => rc (δ i)) := by
  have h1 : IsL 𝔪 (cls π).rep := IsL.of_equiv ⟨s, δ, hd, hδ, hπ⟩ (equivRep π)
  obtain ⟨Δ, ⟨hm, -⟩, hΔ⟩ := hδ
  simp only [fun i => H.segment (hΔ i)]
  obtain ⟨a, ha, ε, -, H⟩ := H
  rw [H.langlands (List.ofFn Δ) (cls π) (by rwa [← Fin.univ_val_map, hm]), List.map_ofFn]
  rfl

theorem IsRec.prod (H : IsRec h rc) {r t : ℕ} (σ : IrrRep (GL (Fin r) (w.adicCompletion E)))
    (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E)))
    (φ : π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) : rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) :=
  let ⟨_, _, _, _, H⟩ := H; H.prod r t σ τ π ⟨φ⟩

end GlobalTheory.LocLanglands

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalArtinExists
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalArtinExists : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalLanglandsExists : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ rc : IrrGL (k := w.adicCompletion E) → WD h, IsRecLit h rc

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def SquareIntegrableSegment : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (δ : IrrGL (k := k)), UnitaryDual.IsSquareIntegrable δ → ∃ Δ : Segment k, IsLSeg Δ δ.rep

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TauOneCharacter
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.DepthZeroModel
open GlobalTheory.SerSys.TameGen

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

abbrev tauOne (θ : (ZMod g)ˣ →* ℂˣ) : FDRep ℂ (Gn g 1) :=
  FDRep.of (GlobalTheory.GLp.Model.chRep (θ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1))))

theorem tauOne_character (θ : (ZMod g)ˣ →* ℂˣ) (y : Gn g 1) :
    (tauOne θ).character y = θ (Matrix.GeneralLinearGroup.det y) := by
  change LinearMap.trace ℂ ℂ (((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • LinearMap.id) = _
  simp

theorem exists_label (L : LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ) (u : (ZMod g)ˣ)
    (hu : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1) :
    ∃ P, IsCuspOf L P (tauOne θ).character ∧ liftPoly L.teich P = X - C (θ u : ℂ) := by
  obtain ⟨T, h1, -, h3⟩ := GlobalTheory.Published.GreenModel.green_one L
  have hc : GlobalTheory.GLq.IsCusp (tauOne θ).character := by
    refine ⟨one_pos, ?_, fun a h1 h2 => by omega⟩
    have := GlobalTheory.Published.GreenModel.isIrr_hom
      ((Units.coeHom ℂ).comp (θ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1) (R := ZMod g))))
    convert this using 1
    funext y
    exact tauOne_character θ y
  obtain ⟨P, hP, e⟩ := h3 _ hc
  have hP' : IsCuspOf L P (tauOne θ).character := e ▸ (h1 P hP).1
  refine ⟨P, hP', ?_⟩
  have hb : -P.coeff 0 ≠ 0 := neg_ne_zero.2 hP.2.2.1
  have hr : ∀ b : ZMod g, Formalism.CyclotomicNorms.rootsBar (X - C b) = {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) b} := fun b => by
    simp [Formalism.CyclotomicNorms.rootsBar]
  have hrP : Formalism.CyclotomicNorms.rootsBar P = {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)} :=
    (congrArg Formalism.CyclotomicNorms.rootsBar (GlobalTheory.Published.GreenModel.lab_eq hP)).trans (hr _)
  have hcp : ((Matrix.GeneralLinearGroup.scalar (Fin 1) u : Gn g 1) : Mt g 1).charpoly = X - C (u : ZMod g) := by
    simp [Matrix.charpoly, Matrix.GeneralLinearGroup.scalar]
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  have h4 := hP'.2.2 (algebraMap _ _ (-P.coeff 0)) (by rw [hrP]; simp) (Matrix.GeneralLinearGroup.scalar (Fin 1) u) (by rw [hcp]; exact irreducible_X_sub_C _)
      (L.gen 1) (by rw [hcp, hr, hu]; simp)
  have h5 := GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos (GlobalTheory.Published.GreenModel.alg_pow hb) 1
  rw [tauOne_character, hd] at h4
  simp only [pow_one] at h5
  simp only [Nat.sub_self, pow_zero, one_mul, Finset.range_one, Finset.sum_singleton, pow_one, h5] at h4
  rw [h4, liftPoly, hrP]
  simp

end GlobalTheory.Published.DepthZeroModel
end
end

