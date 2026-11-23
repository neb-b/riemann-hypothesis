module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElement
section
open GlobalTheory.MeetsGen CategoryTheory

noncomputable section

namespace GlobalTheory.MeetsUnit

variable {G : Type} [Group G] [Fintype G]

theorem single_mul_cU (U : Subgroup G) [Fintype U] (f : U → ℂ) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * cU U f = cU U f * MonoidAlgebra.single h 1 := by
  unfold cU
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
  have e1 : MonoidAlgebra.single (h * g) (1 : ℂ) = MonoidAlgebra.single h 1 * MonoidAlgebra.single g 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul]
  have e2 : MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ) * MonoidAlgebra.single h 1 = MonoidAlgebra.single g⁻¹ 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul, mul_inv_rev, inv_mul_cancel_right]
  simp only [Equiv.coe_mulLeft]
  rw [mul_assoc _ (MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ)), e2, e1]
  simp only [mul_assoc]

theorem single_mul_uElt (U : Subgroup G) [Fintype U] (f : U → ℂ) (e : MonoidAlgebra ℂ G)
    (hC : ∀ a, e * a = a * e) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * uElt U f e = uElt U f e * MonoidAlgebra.single h 1 := by
  have hc := single_mul_cU U f h
  have he := hC (MonoidAlgebra.single h 1)
  simp only [uElt, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
  rw [he, mul_assoc (cU U f) e, he, ← mul_assoc, ← mul_assoc, hc]

theorem trace_cU (V : FDRep ℂ G) (U : Subgroup G) [Fintype U] (f : U → ℂ) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom V.ρ (cU U f)) =
      (Fintype.card G : ℂ) * ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * V.character u := by
  have hp : Representation.asAlgebraHom V.ρ (pU U f) = ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) • V.ρ u := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pU, map_sum, Representation.asAlgebraHom_single]
  unfold cU
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  rw [Finset.sum_congr rfl (fun g _ => by
    rw [map_mul (Representation.asAlgebraHom V.ρ), map_mul (Representation.asAlgebraHom V.ρ), Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, one_smul,
      one_smul, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul])]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hp, map_sum]
  simp only [map_smul, smul_eq_mul, FDRep.character]

def lreg : Representation ℂ G (MonoidAlgebra ℂ G) :=
  (Algebra.lmul ℂ (MonoidAlgebra ℂ G)).toRingHom.toMonoidHom.comp (MonoidAlgebra.of ℂ G)

theorem lreg_apply (g : G) (x : MonoidAlgebra ℂ G) : lreg g x = MonoidAlgebra.single g 1 * x := rfl

theorem exists_rightInv_uElt : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ)
    (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) →
    (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 →
      ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) →
    ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  intro G _ _ U _ ψ e hI hC hχ
  classical
  set f : U → ℂ := fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ) with hf
  set w := uElt U f e with hw
  have hinj : Function.Injective (LinearMap.mulLeft ℂ w) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    by_contra hy0
    let K : Submodule ℂ (MonoidAlgebra ℂ G) := LinearMap.ker (LinearMap.mulLeft ℂ w)
    have hK : ∀ x, x ∈ K ↔ w * x = 0 := fun x => LinearMap.mem_ker
    let A : Subrepresentation (lreg (G := G)) := ⟨K, fun g x hx => by
      rw [hK] at hx ⊢
      rw [lreg_apply, ← mul_assoc, ← single_mul_uElt U f e hC g, mul_assoc, hx, mul_zero]⟩
    haveI : Nontrivial A.toSubmodule :=
      Submodule.nontrivial_iff_ne_bot.2 (fun hb => hy0 ((Submodule.eq_bot_iff _).1 hb y hy))
    obtain ⟨τ, hτs, φ, hφ, hφ0⟩ := PI.GreenLabelSurjWork.exists_simple_constituent A.toRepresentation
    haveI := hτs
    haveI := PI.CharIdemW.nontrivial_of_simple τ
    have hcomm : ∀ a : MonoidAlgebra ℂ G, (∀ k : G, MonoidAlgebra.single k (1 : ℂ) * a = a * MonoidAlgebra.single k 1) →
        ∀ k : G, τ.ρ k * Representation.asAlgebraHom τ.ρ a = Representation.asAlgebraHom τ.ρ a * τ.ρ k := by
      intro a ha k
      rw [← Representation.asAlgebraHom_single_one, ← map_mul, ← map_mul, ha k]
    obtain ⟨μ, hμ⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm w (single_mul_uElt U f e hC))
    obtain ⟨ν, hν⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm e (fun k => hC _ |>.symm))
    have hφw : ∀ x, φ (Representation.asAlgebraHom τ.ρ w x) = 0 := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ w, LinearMap.sum_apply, map_sum]
      simp only [LinearMap.smul_apply, map_smul]
      have h1 : ∀ g, φ (τ.ρ g x) = A.toRepresentation g (φ x) := fun g => LinearMap.congr_fun (hφ g) x
      simp only [h1]
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      show ∑ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) = 0
      have h2 : ∀ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) =
          MonoidAlgebra.single g (w.coeff g) * (φ x : MonoidAlgebra ℂ G) := fun g => by
        rw [← smul_mul_assoc, MonoidAlgebra.smul_single', mul_one]
      simp only [h2]
      rw [← Finset.sum_mul, GlobalTheory.GoodFactor.sum_single]
      exact (hK _).1 (φ x).2
    have hμ0 : μ = 0 := by
      by_contra h
      apply hφ0
      refine LinearMap.ext fun x => ?_
      have h3 : x = μ⁻¹ • Representation.asAlgebraHom τ.ρ w x := by
        rw [hμ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, inv_mul_cancel₀ h, one_smul]
      rw [h3, map_smul, hφw, smul_zero, LinearMap.zero_apply]
    have h10 : (1 : Module.End ℂ τ) ≠ 0 := one_ne_zero
    have hνν : ν * ν = ν := by
      have h4 : Representation.asAlgebraHom τ.ρ (e * e) = Representation.asAlgebraHom τ.ρ e := by rw [hI]
      rw [map_mul, hν, smul_mul_smul_comm, one_mul] at h4
      exact smul_left_injective ℂ h10 h4
    have hTw : Representation.asAlgebraHom τ.ρ w =
        Representation.asAlgebraHom τ.ρ (cU U f) * Representation.asAlgebraHom τ.ρ e + 1 -
          Representation.asAlgebraHom τ.ρ e := by
      rw [hw, uElt, map_add (f := _), map_mul, map_sub, map_one, add_sub_assoc]
    rw [hμ, hμ0, zero_smul, hν] at hTw
    have hν01 : ν * (ν - 1) = 0 := by linear_combination hνν
    rcases mul_eq_zero.mp hν01 with h0 | h0
    · rw [h0, zero_smul, mul_zero, zero_add, sub_zero] at hTw
      exact h10 hTw.symm
    · have hν1 : ν = 1 := sub_eq_zero.mp h0
      rw [hν1, one_smul, mul_one, add_sub_cancel_right] at hTw
      have htr := trace_cU τ U f
      rw [← hTw, map_zero] at htr
      have hirr := GlobalTheory.GoodFactor.isIrrChar_character τ hτs
      have hfix : ∑ g, e.coeff g * τ.character g = τ.character 1 := by
        have h5 : LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ e) = ∑ g, e.coeff g * τ.character g := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ e, map_sum]
          simp only [map_smul, smul_eq_mul, FDRep.character]
        rw [← h5, hν, hν1, one_smul, FDRep.character, map_one τ.ρ]
      have hne := hχ _ hirr hfix
      have h6 : ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * τ.character u =
          (Fintype.card U : ℂ)⁻¹ * ∑ u : U, τ.character u * f u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [h6] at htr
      have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hU : (Fintype.card U : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      exact mul_ne_zero hG (mul_ne_zero hU hne) htr.symm
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj 1
  exact ⟨v, hv⟩

end GlobalTheory.MeetsUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesOver
section
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsobaricOfPublished

theorem multiset_eq_of_prod_map_add {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' := by
  first
  | exact @_root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
  | exact _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
  | (apply _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq ..)

end GlobalTheory.IsobaricOfPublished

namespace GlobalTheory.IsobaricOfPublished

end GlobalTheory.IsobaricOfPublished
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GamGalEqOfPlaceIso
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.FunExt GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RSGam.Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'}

theorem wdRel_mk (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : WDRep h V) (b' : WDRep h' V)
    (hN : b.N = b'.N) (hρ : ∀ σ, b'.ρ (c σ) = b.ρ σ) : WDRel φ (WD.mk b) (WD.mk b') := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨_, b.transport e, b'.transport e, WD.sound (b.iso_transport e).symm,
    WD.sound (b'.iso_transport e).symm, ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ b.N = e.conjAlgEquiv ℂ b'.N
    rw [hN]
  · show e.conjAlgEquiv ℂ (b.ρ σ) = e.conjAlgEquiv ℂ (b'.ρ σ')
    rw [← (hcr σ σ').1 hσ, hρ]

theorem wdRel_lpUnr (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    (hdeg : ∀ σ, deg (c σ) = deg σ) (m : Multiset ℂ) :
    WDRel φ (WD.lpUnr (h := h) m) (WD.lpUnr (h := h') m) := by
  classical
  unfold WD.lpUnr
  refine wdRel_mk c hcr _ _ rfl fun σ => ?_
  rw [WDRep.diag_ρ, WDRep.diag_ρ, hdeg]

end GlobalTheory.RSGam.Transport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaOperatorSemisimpleOfConclusions
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section LetterAux

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem γD_letE_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]
  congr 1
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem sum_letE_eq_one [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem le_Mmax_of [NeZero n] (Mi : ZMod n → ℕ) (i : ZMod n) : Mi i ≤ Formalism.MainNotions.LiftingTheory.Mmax n Mi := by
  have h := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt i))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem smul_letE_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n)
    (x : W.DD T) (hx : a • x ∈ W.N T) : a • ((letE i : LetA O n) • x) ∈ W.N T := by
  rw [smul_smul, mul_comm, ← smul_smul]
  exact (W.N T).smul_mem _ hx

theorem letE_rec (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (c : O)
    (y z : W.DD T) (h : W.π₀ • (y + c • z) = W.γD T W.gam z - z) :
    W.π₀ • ((letE i : LetA O n) • y + c • ((letE i : LetA O n) • z)) =
      W.γD T W.gam ((letE i : LetA O n) • z) - (letE i : LetA O n) • z := by
  rw [smul_comm c (letE i : LetA O n) z, ← smul_add, smul_smul, mul_comm W.π₀, ← smul_smul, h,
    smul_sub, γD_letE_smul]

theorem mem_N_of_letE [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : ∀ i : ZMod n, (letE i : LetA O n) • x ∈ W.N T) : x ∈ W.N T := by
  have e : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE_eq_one, one_smul]
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => h i)

theorem mem_of_qp_pow_zero (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ 0 • x ∈ W.N T) : x ∈ W.N T := by
  rwa [pow_zero, one_smul] at h

end LetterAux

theorem dss_semisimple_of_used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  intro D HW F Cm hN l _ K s LL h
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL h) := hN.2.2.2.2.2.2.2.2.1 l K s LL h
  rw [Formalism.MainNotions.UnusedSlot35.DssRec.coreDss_iff_mem _ h9]
  intro hA T Mi hi hT hJ ug hug hv cO hc Y y₀ hy hΔ seq h0 hrec
  subst h0
  have hs : s = 1 := ((HW l).W_s K s LL h).symm.trans hA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hA.2.2, h⟩
    obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
    have h2 := y.2.2
    have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
    rw [this] at h2
    exact h2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hw1 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL h).gam_gen
    rw [hA.2.1, Nat.cast_one] at this
    exact this
  have hug1 : ug ^ (l - 1) = (((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (l - 1) := by
    have := hug
    rw [hpl] at this
    exact this
  have hug' : ug = ((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam :=
    GlobalTheory.units_eq_of_pow_pred_eq_of_val_one l (D.loc l) LL ug _ hug1 hv hw1
  have hc' : ∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - ((((((HW l).W K 1 LL h).χΓ
      ((HW l).W K 1 LL h).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) := by
    intro x
    have := hc x
    rw [hpl, hug'] at this
    exact this
  have hjx : ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL h) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → 0 < j → j ≤ Y →
      a + (j : ℤ) ∈ Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y := by
    intro i τ a j hO hjump hj0 hjY
    have ha := hJ i τ hO a hjump
    have hM := le_Mmax_of Mi i
    have hH := le_Mmax_of hi i
    rw [Formalism.MainNotions.LiftingTheory.xList, Finset.mem_sort, Finset.mem_image]
    refine ⟨(a, (j : ℤ)), Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩
    · simp only [Formalism.MainNotions.LiftingTheory.jumpSet, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, τ, hjump⟩
      · have := ha.1; omega
      · have := ha.2; omega
    · rw [Finset.mem_Icc]; omega
  have hmem : ∀ i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)),
      (letE i : LetA ↥(OL LL) _) • seq (Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y).length ∈ ((HW l).W K 1 LL h).N T := by
    intro i
    have hDL : Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL h) T i ((letE i : LetA ↥(OL LL) _) • seq 0) := by
      refine ⟨by rw [smul_smul, letE_mul_self], fun δ hδ => ?_⟩
      rw [γD_letE_smul ((HW l).W K 1 LL h) T δ i (seq 0)]
      have e2 := hΔ δ hδ
      exact congrArg (fun z => (letE i : LetA ↥(OL LL) _) • z) e2
    have hYi : Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL h) ^ Y • ((letE i : LetA ↥(OL LL) _) • seq 0) ∈
        ((HW l).W K 1 LL h).N T := by
      exact smul_letE_mem ((HW l).W K 1 LL h) T i _ (seq 0) hy
    have key := GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl T hT i 0 Y cO hc' _
      (fun τ a j hO hjump hj hjY => hjx i τ a j hO hjump hj hjY)
      (fun k => (letE i : LetA ↥(OL LL) _) • seq k) hDL hYi
      (fun k hk => letE_rec ((HW l).W K 1 LL h) T i _ _ _ (hrec k hk))
    exact mem_of_qp_pow_zero ((HW l).W K 1 LL h) T _ key.2
  exact mem_N_of_letE ((HW l).W K 1 LL h) T _ hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeHeckeEigenvaluesAlgebraicAutomorphic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertHeckeCmp.satU_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w Dv.σw Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) α0 → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h (fun i => (α0 i : ℂ)) := by
  intro L _ _ _ n F π U hD v w hw Dv α hα α0 hα0 h hh
  rcases Nat.eq_zero_or_pos (n / 2) with h2 | h2
  · congr 1
    funext i
    exact absurd i.2 (by omega)
  have hn : 0 < n := by omega
  obtain ⟨b, hbK, hbJ, p, hp, σ, hcomp, hsat⟩ := hα0
  obtain ⟨hs, hsurj⟩ := GlobalTheory.T.inert_frame_conj_extends_and_frame_map_surjective L n hn v w hw Dv b hbK hbJ p hp
  obtain ⟨φ, hφU, hφ0, hfix, hAe⟩ := GlobalTheory.T.exists_lift_satake_vector_local_hecke_eigen L n F π U hD v w hw Dv α hα hs b hbK hbJ p hp
  have e1 := (hAe h hh).symm.trans (_root_.GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed L n U hD.1 w Dv.σw Dv.ϖ _ Dv.unram p hsurj σ hcomp α0 hsat φ hφU hfix h hh)
  rw [← sub_eq_zero, ← sub_smul] at e1
  exact sub_eq_zero.1 ((smul_eq_zero.1 e1).resolve_right hφ0)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isSpherical_iff_unr_of_lawsLit : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr := by
  intro hEx hMS hSC hZP hGL hBZ E Ω _ _ _ _ _ A w h a ha e rc H x
  constructor
  · intro hs
    obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main hBZ (w.adicCompletion E) x.1
      ⟨x.2.rep.V, x.2.rep.ρ, x.2.rep.smooth, x.2.rep.irr⟩ hs
    rw [GlobalTheory.T.epsilon_factor_rec_compatible hEx hMS hSC hZP hGL hBZ E Ω A w h a ha e rc H x α hα]
    exact (WD.unr_mk _).2 (WDRep.unr_diag _)
  · intro hu
    obtain ⟨α, hα⟩ := _root_.GlobalTheory.LocLanglands.unr_eq_diag_inv E Ω A w h (rc x) hu
    obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
    have φ := equivRep π
    have hπ' : HasSatake (cls π).rep α := ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hπ.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
    have e1 := GlobalTheory.T.epsilon_factor_rec_compatible hEx hMS hSC hZP hGL hBZ E Ω A w h a ha e rc H (cls π) α hπ'
    have e2 : cls π = x := H.bij.1 (e1.trans hα.symm)
    rw [← e2]
    exact hπ'.2.1

end GlobalTheory.LocLanglands
end

