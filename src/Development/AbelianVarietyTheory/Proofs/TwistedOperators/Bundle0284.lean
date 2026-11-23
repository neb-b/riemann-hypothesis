module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep
section
noncomputable section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.TrFinDense

theorem span_values_dense : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ hU : IsSubrep π ⊤, ∀ N : Subrepresentation (finPartDSSm M hU), N ≠ ⊥ → (Submodule.span ℂ {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}).topologicalClosure = ⊤ := by
  intro D V S M H _ _ _ π hπ hU N hN
  classical
  set Sv : Set H := {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}
    with hSv
  set W : Submodule ℂ H := Submodule.span ℂ Sv with hW

  let Mon : Submonoid (GA D V) :=
    { carrier := {g | Sv ⊆ W.comap (π g : H →ₗ[ℂ] H)}
      mul_mem' := by
        intro a b ha hb z hz
        have hbz : π b z ∈ W := hb hz
        have : W ≤ W.comap (π a : H →ₗ[ℂ] H) := Submodule.span_le.2 ha
        show π (a * b) z ∈ W
        rw [map_mul]
        exact this hbz
      one_mem' := by
        intro z hz
        show π 1 z ∈ W
        rw [map_one]
        exact Submodule.subset_span hz }
  have hfin : ∀ g : GfC V, (g : GA D V) ∈ Mon := by
    rintro g _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨finPartDSSm M hU g Φ, N.apply_mem_toSubmodule g hΦ, y, rfl⟩
  have hinf : ∀ w x, embW V w x ∈ Mon := by
    intro w x
    obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
    rintro _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨Φ, hΦ, Function.update y τ (dsRep M τ x (y τ)), ?_⟩
    exact (((Φ : homDS M π ⊤).2).2 τ x y).symm
  haveI : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  have htop : Mon = ⊤ := GlobalTheory.PlaceGen.eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) Mon ∅
    (fun v x => hfin (locFin V v x)) hinf (fun k hk => hfin ⟨k, (mem_levelOff.1 hk).1⟩)
  have hinvW : ∀ g, ∀ v ∈ W, π g v ∈ W := fun g v hv =>
    (Submodule.span_le.2 (show g ∈ Mon from htop ▸ trivial)) hv
  have hsub := isSubrep_topologicalClosure (π := π) hinvW
  rcases hπ.irred.2 _ hsub with h | h
  · exfalso
    obtain ⟨Φ, hΦ, hΦ0⟩ : ∃ Φ ∈ N.toSubmodule, Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hN (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun Φ hΦ => (Submodule.mem_bot ℂ).2 (hc Φ hΦ)))
    have : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) ≠ 0 := by
      intro e
      exact hΦ0 (Subtype.ext (Subtype.ext e))
    obtain ⟨y, hy⟩ : ∃ y, ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact this (ContinuousMultilinearMap.ext hc)
    have hmem : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ∈ W.topologicalClosure :=
      W.le_topologicalClosure (Submodule.subset_span ⟨Φ, hΦ, y, rfl⟩)
    rw [h] at hmem
    exact hy ((Submodule.mem_bot ℂ).1 hmem)
  · exact h

end GlobalTheory.TrFinDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFramesTransportLocalLatticeIsometry
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

namespace GlobalTheory.LatConjSplit

open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

noncomputable section

theorem toMatrix'_mul_symm {R : Type} [CommRing R] (a : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.toMatrix' (a : (Fin n → R) →ₗ[R] (Fin n → R)) * LinearMap.toMatrix' (a.symm : (Fin n → R) →ₗ[R] (Fin n → R)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.toMatrix'_id]

theorem toMatrix'_symm_mul {R : Type} [CommRing R] (a : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.toMatrix' (a.symm : (Fin n → R) →ₗ[R] (Fin n → R)) * LinearMap.toMatrix' (a : (Fin n → R) →ₗ[R] (Fin n → R)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.toMatrix'_id]

def compAt (τ : E →ₐ[F] Fv F v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    GL (Fin n) (Fv F v) where
  val := (LinearMap.toMatrix' (a : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ)
  inv := (LinearMap.toMatrix' (a.symm : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ)
  val_inv := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, toMatrix'_mul_symm, map_one]
  inv_val := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, toMatrix'_symm_mul, map_one]

theorem compAt_val (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    (compAt τ a).1 = (LinearMap.toMatrix' (a : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ) := rfl

theorem compAt_inv_val (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    ((compAt τ a)⁻¹).1 = (LinearMap.toMatrix' (a.symm : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ) := rfl

theorem splitVec_apply_equiv (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (a y) = (compAt τ a).1 *ᵥ splitVec τ y := by
  rw [compAt_val, ← splitVec_mulVec, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

theorem splitVec_symm_apply_equiv (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (a.symm y) = (compAt τ a)⁻¹.1 *ᵥ splitVec τ y := by
  rw [compAt_inv_val, ← splitVec_mulVec, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

theorem splitHom_conj (hc : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {J J' : Matrix (Fin n) (Fin n) E}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h3 : ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)) (g : GLoc σ J v) :
    splitHom σ J' τ (j g) = compAt τ a * splitHom σ J τ g * (compAt τ a)⁻¹ := by
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun u => ?_))
  obtain ⟨y, rfl⟩ : ∃ y, splitVec τ y = u := ⟨splitIncl hc τ u, splitVec_splitIncl hc τ u⟩
  simp only [Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [← splitVec_matHom_mulVec, ← splitVec_symm_apply_equiv, ← splitVec_matHom_mulVec, ← splitVec_apply_equiv, ← h3,
    LinearEquiv.apply_symm_apply]

theorem conj_mem_stabLoc_iff {J J' : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h2 : ∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v)
    (h3 : ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)) (g : GLoc σ J v) :
    j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v := by
  rw [mem_stabLoc, mem_stabLoc]
  constructor
  · intro H y
    have := H (a y)
    rwa [h3, h2, h2] at this
  · intro H y'
    obtain ⟨y, rfl⟩ := a.surjective y'
    rw [h3, h2, h2]
    exact H y

theorem isSplitBasis_conj {L L' : Submodule (𝓞 E) (Fin n → E)}
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h2 : ∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v) (τ : E →ₐ[F] Fv F v) {β : GL (Fin n) (Fv F v)}
    (hβ : IsSplitBasis τ L β) : IsSplitBasis τ L' (compAt τ a * β) := by
  intro u
  rw [hβ u, Units.val_mul, ← Matrix.mulVec_mulVec]
  generalize β.1 *ᵥ u = z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a y, (h2 y).2 hy, splitVec_apply_equiv τ a y⟩
  · rintro ⟨y', hy', e⟩
    refine ⟨a.symm y', (h2 _).1 (by rwa [a.apply_symm_apply]), ?_⟩
    rw [splitVec_symm_apply_equiv, e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem split_conj {J J' : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (hj : IsLatticeConj L L' j) (hJ' : IsHermND σ J')
    (hL' : IsSelfDualAt σ J' L' v) :
    (∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) ∧ ∀ s : SplitAt σ J L v, ∃ s' : SplitAt σ J' L' v,
      (∀ g, s'.equiv (j g) = s.equiv g) ∧
      ∀ (k : stabLoc σ J L v) (k' : stabLoc σ J' L' v), (k' : GLoc σ J' v) = j k → s'.red k' = s.red k := by
  obtain ⟨a, -, h2, h3⟩ := hj
  refine ⟨conj_mem_stabLoc_iff j a h2 h3, fun s => ⟨⟨s.emb, compAt s.emb a * s.basis, s.cm, hJ', hL',
    isSplitBasis_conj a h2 s.emb s.isBasis⟩, ?_⟩⟩
  have he : ∀ g, splitEquivIn s.cm hJ' s.emb (compAt s.emb a * s.basis) (j g) = s.equiv g := fun g => by
    rw [splitEquivIn_apply, splitHom_conj s.cm s.emb j a h3, SplitAt.equiv, splitEquivIn_apply]
    group
  refine ⟨he, fun k k' hk => ?_⟩
  apply Units.ext
  simp only [SplitAt.red, splitRed_val]
  congr 1
  ext i l
  rw [coe_stabLocEquiv, coe_stabLocEquiv, hk]
  exact congrArg _ (congrArg (fun x => x.1 i l) (he k))

theorem split_conj_cast {n' : ℕ} (hr : n' = n) {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
    {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} (j : GLoc σ J v ≃ₜ* GLoc σ J' v)
    (hj : IsLatticeConj L L' j) (hJ' : IsHermND σ J') (hL' : IsSelfDualAt σ J' L' v) :
    (∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) ∧ ∀ s : SplitAt σ J L v, ∃ s' : SplitAt σ J' L' v,
      (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧
      ∀ (k : stabLoc σ J L v) (k' : stabLoc σ J' L' v), (k' : GLoc σ J' v) = j k →
        ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  subst hr
  obtain ⟨h1, h2⟩ := split_conj j hj hJ' hL'
  refine ⟨h1, fun s => ?_⟩
  obtain ⟨s', e1, e2⟩ := h2 s
  exact ⟨s', fun g a b => by rw [e1]; rfl, fun k k' hk a b => by rw [e2 k k' hk]; rfl⟩

end

end GlobalTheory.LatConjSplit

theorem GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj : ∀ (D : D7) (V V' : HSp D) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → (∀ g, j g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ s : SplitAt D.sp.cm.sig V.gram (frameLat V) v, ∃ s' : SplitAt D.sp.cm.sig V'.gram (frameLat V') v, (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧ ∀ (k : Kv V v) (k' : Kv V' v), (k' : GLoc D.sp.cm.sig V'.gram v) = j k → ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  intro D V V' hr v j hj
  exact GlobalTheory.LatConjSplit.split_conj_cast hr j hj (GlobalTheory.Orb.isHermND_gram V') (SelfDual.isSelfDualAt_frameLat D V' v)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMulEndomorphismIsotypicRep
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.IsoTrace

theorem intertwining_sum_apply {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
    {π : Representation ℂ G N} {ρ : Representation ℂ G X} {ι : Type} (t : Finset ι)
    (c : ι → ℂ) (φ : ι → π.IntertwiningMap ρ) (n : N) : (∑ j ∈ t, c j • φ j) n = ∑ j ∈ t, c j • φ j n := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => simp [Finset.sum_insert ha, ih]

theorem trace_mul_isotypic : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur hiso H hH ⟨s, hs⟩
  let S := Submodule.span ℂ (s : Set (π.IntertwiningMap ρ))
  haveI : FiniteDimensional ℂ S := FiniteDimensional.span_finset ℂ s
  let bS := Module.finBasis ℂ S
  let φ : Fin (Module.finrank ℂ S) → π.IntertwiningMap ρ := fun j => (bS j : π.IntertwiningMap ρ)
  have hli : LinearIndependent ℂ φ := bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hinj := _root_.GlobalTheory.intertwiners_indep_injective G N X π ρ hirr hschur _ φ hli
  have hY : LinearMap.range H ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
    refine hs.trans (iSup₂_le fun ψ hψ => ?_)
    have hψS : ψ ∈ S := Submodule.subset_span hψ
    have e : ψ = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j := by
      have := congrArg Subtype.val (bS.sum_repr ⟨ψ, hψS⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rintro _ ⟨n, rfl⟩
    have hn : ψ n = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j n := by
      rw [← intertwining_sum_apply, ← e]
    change ψ n ∈ _
    rw [hn]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨n, rfl⟩)
  have hcoef : ∀ ψ : π.IntertwiningMap ρ, ∃ c : Fin (Module.finrank ℂ S) → ℂ,
      ∀ n, H (ψ n) = ∑ j, c j • φ j n := by
    intro ψ
    let Hψ : π.IntertwiningMap ρ := (H ∘ₗ ψ.toLinearMap).intertwiningMap_of_isIntertwiningMap π ρ
      (fun g v => by simp [ψ.isIntertwining, hH])
    have hr : LinearMap.range Hψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
      rintro _ ⟨n, rfl⟩
      exact hY ⟨ψ n, rfl⟩
    exact GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range G N X π ρ hschur _ φ hinj Hψ hr
  choose hc hhc using fun j => hcoef (φ j)
  refine ⟨∑ j, hc j j, fun A B hB b hb => ?_⟩
  obtain ⟨hfin, htr⟩ := hb
  let R := LinearMap.range A
  let Φ' : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] X :=
    ∑ j, (φ j).toLinearMap ∘ₗ R.subtype ∘ₗ LinearMap.proj j
  have hΦ' : ∀ w, Φ' w = ∑ j, φ j (w j : N) := by
    intro w
    simp [Φ', LinearMap.sum_apply]
  have hinj' : Function.Injective Φ' := by
    intro w w' e
    rw [hΦ', hΦ'] at e
    have := hinj e
    funext j
    exact Subtype.ext (congrFun this j)
  let Z := LinearMap.range Φ'
  have hBφ : ∀ (ψ : π.IntertwiningMap ρ) n, B (ψ n) = ψ (A n) := fun ψ n =>
    DFunLike.congr_fun (hB ψ) n
  have hrange : LinearMap.range (H ∘ₗ B) ≤ Z := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ f : π.IntertwiningMap ρ, LinearMap.range f.toLinearMap := by
      have : x ∈ isoPartAlg π ρ := hiso ▸ Submodule.mem_top
      exact this
    refine Submodule.iSup_induction _ (motive := fun x => (H ∘ₗ B) x ∈ Z) hx ?_ ?_ ?_
    · rintro ψ _ ⟨n, rfl⟩
      obtain ⟨c, hc'⟩ := hcoef ψ
      refine ⟨fun j => c j • ⟨A n, LinearMap.mem_range_self A n⟩, ?_⟩
      rw [hΦ']
      simp only [LinearMap.comp_apply, Pi.smul_apply, SetLike.val_smul, map_smul]
      rw [show ψ.toLinearMap n = ψ n from rfl, hBφ, hc']
    · simp
    · intro x y hx hy
      simpa using Z.add_mem hx hy
  haveI : FiniteDimensional ℂ Z := LinearMap.finiteDimensional_range Φ'
  have hT1 := GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional X (H ∘ₗ B) Z hrange
  let e : (Fin (Module.finrank ℂ S) → R) ≃ₗ[ℂ] Z := LinearEquiv.ofInjective Φ' hinj'
  let A' : R →ₗ[ℂ] R := A.restrict (p := R) (q := R) fun v _ => LinearMap.mem_range_self A v
  let h : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ := Matrix.of fun k j => hc j k
  let M : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → R) :=
    ∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ => R) k ∘ₗ A' ∘ₗ LinearMap.proj j)
  have hM : ∀ w k, (M w k : N) = ∑ j, hc j k • A (w j) := by
    intro w k
    simp [M, h, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, A']
  have hconj : (H ∘ₗ B).restrict (p := Z) (q := Z) (fun x _ => hrange (LinearMap.mem_range_self _ x)) =
      e.conj M := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change H (B (Φ' w)) = Φ' (M w)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦ', hΦ', map_sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hBφ, hhc, hM, map_sum, map_smul]
    rw [Finset.sum_comm]
  have key : LinearMap.trace ℂ Z ((H ∘ₗ B).restrict (p := Z) (q := Z)
      fun x _ => hrange (LinearMap.mem_range_self _ x)) = (∑ j, hc j j) * b := by
    rw [hconj, LinearMap.trace_conj', _root_.GlobalTheory.trace_matrix_pi_operator R _ h A', ← htr]
    simp [h, Matrix.trace, A', R]
  rw [← key]
  exact hT1

end GlobalTheory.IsoTrace
end

