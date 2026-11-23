module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CaraianiTempered : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 2 ≤ n →
    ∀ π : CuspSub L n, π.IsCsd → GKCoh.IsCohomological π →
      ∀ (y : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (y.adicCompletion L))), π.IsLocComp y σ →
        LocGL.IsTemperedCoeff σ.ρ

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.Published

def ClozelCohomological : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a,
    (CG.mk π).IsRegAlg → GKCoh.IsCohomological π

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.Published

def ClozelPurity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a,
    (∀ τ, ∀ z ∈ (CG.mk π).infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) →
    ∃ w₀ : ℤ, ∀ τ : E →+* ℂ,
      (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace GlobalTheory.Published

def GaloisRepOfPolarizedPair : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalRepOf π χ ι r wt HT

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def LocalGlobalAboveL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → GKCoh.IsCohomological π →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
section
noncomputable section

namespace GlobalTheory.LocGL.TemperedTests

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GenericUnitary Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_ofChar (x : IrrGL (k := k)) (hx : x.1 = 1) : ∃ θ hθ, x = IrrGL.ofChar θ hθ := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.LocGL.TemperedTests

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GKCoh.Tests

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

theorem tempered_rank_one (L : Type) [Field L] [NumberField L] [IsCMField L] (π : CuspSub L 1) (hπ : π.IsCsd)
    (y : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin 1) (y.adicCompletion L))) (h : π.IsLocComp y σ) :
    LocGL.IsTemperedGL σ.ρ := by
  obtain ⟨ω, hω, hc⟩ := CsdUnitary.isUnitary_of_isCsd L 1 (CG.mk π) hπ
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨ψ, hψ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep _ (Fin 1) _ σ.ρ σ.smooth σ.irred
  refine ((LocGL.isTemperedGL_detRep_one hψ).2 ((isUnitarisable_ofChar_iff _).2 fun g => ?_)).of_equiv e.symm
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (LinearMap.ext hc)
  have h1 : σ.ρ g v = (detChar (Fin 1) ψ g : ℂ) • v := e.toLinearEquiv.injective (by
    rw [map_smul]
    exact (e.toIntertwiningMap.isIntertwining _ _ g v).trans (ofChar_apply _ _ _))
  have h2 := hf g v
  have h3 := hc (GeneralLinearGroup.det (locGL L 1 y g)) (f v)
  rw [RankLeOne.scalar_det_of_subsingleton] at h3
  rw [h1, map_smul] at h2
  rw [smul_left_injective ℂ hv (h2.trans h3)]
  exact hω _

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem dchi_absC_one (s : ℂ) : dchi (Model.absC E s) 1 = s * (2 * Fintype.card (InfinitePlace E)) := by
  let A : Cinf E →L[ℝ] ℂ := s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  rw [h]
  simp [A, mul_comm]

theorem prod_coord {M : Type} [CommMonoid M] (F : ℂ → M) (z : Cinf E) :
    ∏ τ : E →+* ℂ, F (coord τ z) = ∏ w, F (z w) * F (starRingEnd ℂ (z w)) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have e : Finset.univ.filter (fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.1 (h.trans (InfinitePlace.mk_embedding w).symm) with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← h]; ext x; simp)
    · rintro (rfl | rfl) <;> simp
  rw [e, Finset.prod_pair hne]
  simp [coord, hne]


theorem dchi_absC (s : ℂ) (z : Cinf E) : dchi (Model.absC E s) z = s * ∑ w, (2 * ((z w).re : ℝ) : ℂ) := by
  let A : Cinf E →L[ℝ] ℂ := s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  rw [h]
  simp [A]

end GlobalTheory.GKCoh.Tests
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def RegularAlgebraicPurity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, (CG.mk π).IsRegAlg →
    (∃ w₀ : ℤ, ∀ τ : E →+* ℂ,
      (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z) ∧
    GKCoh.IsCohomological π

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh

namespace GlobalTheory.WignerGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def dualS (Ξ : AlgRep E a) (i j : Fin a) (x : Cinf E) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  -(Ξ.dmat (toL (Matrix.single i j x)))ᵀ

def dualE (Ξ : AlgRep E a) (τ : E →+* ℂ) (i j : Fin a) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  (1 / 2 : ℂ) • (dualS Ξ i j (atEmb τ 1) - Complex.I • dualS Ξ i j (atEmb τ Complex.I))

def HasDualInfChar (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (dualE Ξ τ) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

end GlobalTheory.WignerGL

namespace GlobalTheory.Published

def WignerVanishingGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a)
    (m m' : (E →+* ℂ) → Multiset ℂ), (∀ τ, π.HasInfChar τ (m τ)) → (∀ τ, WignerGL.HasDualInfChar Ξ τ (m' τ)) →
    m ≠ m' → ¬ IsCohFor π Ξ

end GlobalTheory.Published

end
end

