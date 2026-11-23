module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.AffineCechOpenFunctionFieldGeneric
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem smooth_sections_of_affine_open (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ)
    [SmoothOfRelativeDimension d p] (V : Z.Opens) (hV : IsAffineOpen V) :
    Algebra.Smooth ℂ (Sec p V) := by
  have h1 := HasRingHomProperty.appLE @Smooth p (SmoothOfRelativeDimension.smooth d p)
    ⟨⊤, isAffineOpen_top (Sp ℂ)⟩ ⟨V, hV⟩ (by simp)
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  exact RingHom.Smooth.comp h2 h1

theorem UpperTheory.affineCechOpen_functionField_generic :
    ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) (s : Finset ι) (hs : s.Nonempty) (hV : IsAffineOpen (cechOpen ⊤ U s)) (hη : genericPoint Z ∈ cechOpen ⊤ U s), letI := algΓ p; Function.Injective (formGermI p a hV hη hinst) ∧ LinearMap.range (formGermI p a hV hη hinst) = omB ℂ Z.functionField (B s) a := by
  intro d Z _ p _ inst ι U B hinst hU a s hs hV hη
  letI := algΓ p
  subst hinst
  letI : Algebra ℂ Z.functionField := ffAlg p
  set V := cechOpen ⊤ U s with hVdef
  letI : Algebra (Sec p V) Z.functionField := (germSec p hη).toAlgebra
  haveI : IsScalarTower ℂ (Sec p V) Z.functionField :=
    IsScalarTower.of_algebraMap_eq (fun r => ((semiHom_germSec p hη).map_algebraMap r).symm)
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  haveI : IsFractionRing (Sec p V) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z V hV
  haveI := smooth_sections_of_affine_open d Z p V hV
  have hring : ∀ y, y ∈ B s ↔ ∃ f : Sec p V, algebraMap (Sec p V) Z.functionField f = y := by
    intro y
    rw [hU.ring s hs y]
    have hVeq : s.inf U = V := by
      rw [hVdef]
      simp [cechOpen, Finset.inf_eq_iInf]
    have gen : ∀ (W W' : Z.Opens) (_ : W = W') (h1 : genericPoint Z ∈ W)
        (h2 : genericPoint Z ∈ W'), ((∃ f, (Z.presheaf.germ W _ h1).hom f = y) ↔
          ∃ f, (Z.presheaf.germ W' _ h2).hom f = y) := by
      rintro W W' rfl h1 h2
      rfl
    exact gen _ _ hVeq _ hη
  obtain ⟨hinj, hom⟩ := mOm_injective_and_omB ℂ Z.functionField (Sec p V) (B s) hring a
  have hform : ∀ x, formGermI p a hV hη rfl x =
      ↑((semiHom_algebraMap ℂ (Sec p V) Z.functionField).mOm a
        ((toOmEquiv p a hV).symm ((sectionsOn.toΓ (Omega p a) V) x))) := fun x => rfl
  constructor
  · intro x y hxy
    rw [hform, hform] at hxy
    have h3 := hinj (Subtype.ext hxy)
    exact (sectionsOn.toΓ _ _).injective ((toOmEquiv p a hV).symm.injective h3)
  · ext y
    rw [LinearMap.mem_range, hom y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hform x).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨(sectionsOn.toΓ (Omega p a) V).symm (toOmEquiv p a hV z), ?_⟩
      rw [hform, AddEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsDeRhamTraceOfSeparable
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TensorProduct

namespace UpperTheory.DeRhamTrace

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L]

private noncomputable abbrev beta : L ⊗[K] Ω[K⁄k] →ₗ[L] L ⊗[K] DR k K :=
  LinearMap.baseChange L (ι1 (R := k) (B := K))

private theorem beta_anti (x y : L ⊗[K] Ω[K⁄k]) :
    beta k K L x * beta k K L y + beta k K L y * beta k K L x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), add_mul, mul_add]
    calc _ = (beta k K L a * beta k K L y + beta k K L y * beta k K L a) +
          (beta k K L b * beta k K L y + beta k K L y * beta k K L b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  | tmul a ω =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd =>
      rw [map_add (f := _), add_mul, mul_add]
      calc _ = (beta k K L (a ⊗ₜ ω) * beta k K L c + beta k K L c * beta k K L (a ⊗ₜ ω)) +
            (beta k K L (a ⊗ₜ ω) * beta k K L d + beta k K L d * beta k K L (a ⊗ₜ ω)) := by abel
        _ = 0 := by rw [hc, hd, add_zero]
    | tmul b ω' =>
      simp only [beta, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_comm b a, ← TensorProduct.tmul_add]
      have : ι1 (R := k) (B := K) ω * ι1 (R := k) (B := K) ω' +
          ι1 (R := k) (B := K) ω' * ι1 (R := k) (B := K) ω = 0 :=
        ExteriorAlgebra.ι_add_mul_swap ω ω'
      rw [this, TensorProduct.tmul_zero]

private theorem beta_sq (x : L ⊗[K] Ω[K⁄k]) : beta k K L x * beta k K L x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), add_mul, mul_add, mul_add, ha, hb, zero_add, add_zero]
    exact beta_anti k K L a b
  | tmul a ω =>
    simp only [beta, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have : ι1 (R := k) (B := K) ω * ι1 (R := k) (B := K) ω = 0 := ExteriorAlgebra.ι_sq_zero ω
    rw [this, TensorProduct.tmul_zero]

variable [Algebra.FormallyEtale K L]

private noncomputable def phi : Ω[L⁄k] →ₗ[L] L ⊗[K] DR k K :=
  beta k K L ∘ₗ (KaehlerDifferential.isBaseChange_of_formallyEtale k K L).equiv.symm.toLinearMap

private theorem phi_sq (x : Ω[L⁄k]) : phi k K L x * phi k K L x = 0 := beta_sq k K L _

private noncomputable def psi : DR k L →ₐ[L] L ⊗[K] DR k K :=
  ExteriorAlgebra.lift L ⟨phi k K L, phi_sq k K L⟩

private theorem psi_mapDR (ω : DR k K) : psi k K L (GlobalTheory.W1.mapDR k K L ω) = 1 ⊗ₜ ω := by
  have key : ((psi k K L).restrictScalars K).comp (GlobalTheory.W1.mapDR k K L) =
      Algebra.TensorProduct.includeRight := by
    apply ExteriorAlgebra.hom_ext
    refine LinearMap.ext fun η ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.W1.mapDR, ExteriorAlgebra.lift_ι_apply]
    simp only [GlobalTheory.W1.map1, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [psi, ExteriorAlgebra.lift_ι_apply]
    simp only [phi, LinearMap.comp_apply, LinearEquiv.coe_coe, IsBaseChange.equiv_symm_apply,
      beta, LinearMap.baseChange_tmul]
  exact congrArg (fun f ↦ f ω) key

end UpperTheory.DeRhamTrace

open UpperTheory.DeRhamTrace in
theorem UpperTheory.exists_deRhamTrace_of_separable :
    ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L], ∃ T : DR k L →ₗ[k] DR k K, GlobalTheory.W1.IsTrDR k K L T := by
  intro k K L _ _ _ _ _ _ _ _ _
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let Tr : (L ⊗[K] DR k K) →ₗ[K] DR k K :=
    (TensorProduct.lid K (DR k K)).toLinearMap ∘ₗ LinearMap.rTensor (DR k K) (Algebra.trace K L)
  refine ⟨(Tr.restrictScalars k) ∘ₗ ((psi k K L).toLinearMap.restrictScalars k), ?_⟩
  intro b ω
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply]
  rw [map_smul, psi_mapDR, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [Tr]
end

