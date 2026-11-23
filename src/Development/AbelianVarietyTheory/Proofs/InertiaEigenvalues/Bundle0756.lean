module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSphericalLocProd
section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.UnitaryBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCSupport

variable {E : Type} [Field E] [NumberField E]

abbrev clsOf {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (k := w.adicCompletion E) :=
  IrrGL.of σ.ρ σ.smooth σ.irred

theorem good_of_good_locProd {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (hi : (locProd h w σ).IsIrreducible)
    (hG : Good (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi)) : ∀ i, Good (clsOf (σ i)) := by
  have hs : IsSubquotient (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi).rep
      (prodIrr (fun i => clsOf (σ i)) h) := by
    let e := prodIrrEquiv (k := w.adicCompletion E) h (fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred)
    let f := e.symm.trans (IrrGL.equivOf (locProd h w σ) (isSmooth_parInd _ _) hi)
    exact IsSubquotient.of_surjective f.toIntertwiningMap f.toLinearEquiv.surjective
  exact (GlobalTheory.RecT.good_toral_of_isSubquotient_prodIrr _ c (fun i => clsOf (σ i)) (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi) h hs).1 hG

theorem isSpherical_of_equiv {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (e : ρ.Equiv τ) {K : Subgroup G}
    (h : GlobalTheory.LGrp.IsSpherical ρ K) : GlobalTheory.LGrp.IsSpherical τ K := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e.toIntertwiningMap x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, ?_⟩
  · rw [← Representation.IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap k x, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
  · intro h1
    exact h0 (e.toLinearEquiv.injective (by simpa using h1))

theorem isSphericalFor_of_eq {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {K K' : Subgroup G} (e : K = K') (h : GlobalTheory.SmGL.IsSphericalFor ρ K) : GlobalTheory.SmGL.IsSphericalFor ρ K' := e ▸ h

variable [IsCMField E]

end GlobalTheory.BCSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValSubLtIff
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.WeilRes

open Pointwise

variable {Ω : Type} [Field Ω]

theorem mem_Dec_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ ∀ x, (σ x ∈ A ↔ x ∈ A) := by
  refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => ?_⟩
  show σ • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isPrime
  simpa only [normV, Ideal.absNorm_eq_natCard] using
    (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 K)).asIdeal w.asIdeal).symm

theorem under_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v)
    (h' : IsPlaceOver A w) : w.under (𝓞 K) = v := by
  refine eq_of_isPlaceOver (A := A) ?_ h
  intro x
  show _ ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ w.asIdeal
  rw [← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]
  rfl

section Res

variable {L : Type} [Field L] [NumberField L] [Algebra L Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

end Res

end GlobalTheory.DelEps.WeilRes
end
end

