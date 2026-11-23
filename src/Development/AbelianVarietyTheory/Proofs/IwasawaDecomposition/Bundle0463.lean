module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0805
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalCharacterAdmissibleConductorInertiaSurj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem universalCharacter_admissibleConductor_inertia_surjective : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (hE : IsEmpty D.nd.Loc) (F : TwF T)
    (i : T.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ (T.ntw hE F (TwL.empty T)) i Q M →
    ∀ P (hP : P ∈ Q),
      (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A =>
          Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩) ∧
      ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
        ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = 0 := by
  intro _ D cf b0 b1 Sx T Sp hE F i Q M hQ P hP
  obtain ⟨-, hadm⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hadm P hP
    rw [GlobalTheory.GalChar.isConjPl_unique h h'']
    exact hP''
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host T.cc (T.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact GlobalTheory.SpreadRestrict.surj_conj (X := T.ntw hE F (TwL.empty T)) χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host T.cc (T.l i) ⟨χ, hDel⟩
  have hcoord := (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.2.2.2.1 Q M hcl P hP
  refine ⟨fun A hA c => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, e⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd c)
    refine ⟨⟨σ, hσ⟩, ?_⟩
    show Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = c
    rw [hcoord, e, toAdd_ofAdd]
  · rw [hcoord, hD.2.2.2.1 P' (fun h => h.elim (fun e => hne e) (fun e => hnc e)) A hA σ hσ]
    rfl

end GlobalTheory.HeightCounting.FormsStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.W1idxUnionW1jwFinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

theorem conjPl_injective {K : Type} [Field K] [StarRing K] :
    Function.Injective (Formalism.DivisionValues.conjPl (K := K)) := by
  intro v w h
  have h1 : Ideal.map (Formalism.DivisionValues.cO K) v.asIdeal = Ideal.map (Formalism.DivisionValues.cO K) w.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal h
  have hb : Function.Bijective (Formalism.DivisionValues.cO K) := (Formalism.DivisionValues.cO K).bijective
  have h2 := congrArg (Ideal.comap (Formalism.DivisionValues.cO K)) h1
  rw [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at h2
  exact HeightOneSpectrum.ext h2

theorem dual_fg {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A).FG := by
  classical
  obtain ⟨S, hS⟩ := hA.toIsLattice.fg
  have hSm : ∀ a ∈ S, a ∈ A := fun a ha => hS ▸ Submodule.subset_span ha
  have mem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
    intro x
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
  choose g hg using fun (x : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) (a : S) => (mem x).1 x.2 a (hSm a a.2)
  have inj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective (𝓞 K) K
  let φ : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A →ₗ[𝓞 K] (S → 𝓞 K) :=
    { toFun := g
      map_add' := fun x y => funext fun a => inj (by
        rw [hg, Submodule.coe_add, map_add (f := _), Pi.add_apply, map_add (f := _), hg, hg])
      map_smul' := fun s x => funext fun a => inj (by
        rw [hg, Submodule.coe_smul, ← algebraMap_smul K s (x : Fin d → K), map_smul]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hg]) }
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ a ∈ S, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩, map_zero]
    have hL : ∀ a ∈ A, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hS] at ha
      induction ha using Submodule.span_induction with
      | mem a ha => exact h0 a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [← algebraMap_smul K s a, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hV : ∀ a, Formalism.DivisionValues.hform H a x = 0 := by
      intro a
      have ha : a ∈ Submodule.span K (A : Set (Fin d → K)) := by rw [Submodule.IsFullLattice.span_eq_top (self := hA)]; trivial
      induction ha using Submodule.span_induction with
      | mem a ha => exact hL a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hM : Matrix.mulVec H (x : Fin d → K) = 0 := by
      funext i
      have := hV (Pi.single i 1)
      simpa [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Pi.single_apply, mul_comm] using this
    exact Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hH.ne_zero hM)
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jw_finite_of_lat {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.jw H w A ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite A _ hA.toIsLattice.fg (dual_fg H hH A hA)

theorem idx_finite_of_fg {K : Type} [Field K] [NumberField K] {d d' : ℕ} (M : Submodule (𝓞 K) (Fin d' → K))
    (θ : Matrix (Fin d') (Fin d) K) (L : Submodule (𝓞 K) (Fin d → K)) (hM : M.FG) (hL : L.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.idx w M (Formalism.DivisionValues.matLat θ L) ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite M _ hM (hL.map _)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

end
end

