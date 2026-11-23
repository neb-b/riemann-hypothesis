module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaLogNorms
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ClosureFinite

theorem integralClosure_finite_of_etale (R K L : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Module.Finite K L]
    [Algebra.Etale K L] : Module.Finite R (integralClosure R L) := by
  classical
  obtain ⟨I, hI, Ai, hF, hA, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K L).mp inferInstance
  letI : ∀ i, Algebra R (Ai i) := fun i => ((algebraMap K (Ai i)).comp (algebraMap R K)).toAlgebra
  haveI : ∀ i, IsScalarTower R K (Ai i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ψ : ∀ i, L →ₐ[K] Ai i := fun i => (Pi.evalAlgHom K Ai i).comp e.toAlgHom
  haveI : ∀ i, Module.Finite K (Ai i) := fun i =>
    Module.Finite.of_surjective (ψ i).toLinearMap (by
      intro y
      obtain ⟨x, hx⟩ := e.surjective (Pi.single i y)
      exact ⟨x, by simp [ψ, hx]⟩)
  haveI : ∀ i, Module.Finite R (integralClosure R (Ai i)) := fun i =>
    IsIntegralClosure.finite R K (Ai i) (integralClosure R (Ai i))
  let φ : integralClosure R L →ₗ[R] (∀ i, integralClosure R (Ai i)) :=
    LinearMap.pi (fun i =>
      (((ψ i).restrictScalars R).toLinearMap.comp (integralClosure R L).val.toLinearMap).codRestrict
        (integralClosure R (Ai i)).toSubmodule
        (fun x => IsIntegral.map ((ψ i).restrictScalars R) x.2))
  haveI : IsNoetherian R (∀ i, integralClosure R (Ai i)) := inferInstance
  have hφ : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    funext i
    have := congrArg (fun f => ((f i : integralClosure R (Ai i)) : Ai i)) h
    exact this
  haveI := isNoetherian_of_injective φ hφ
  exact Module.IsNoetherian.finite R _

end GlobalTheory.ClosureFinite

namespace GlobalTheory.ClosureFinite

theorem closure_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  classical
  let GF := GlobalTheory.LocAcyc.GenFib A R
  let S := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let K' := FractionRing R
  have hS : ∀ y : S, IsUnit (algebraMap R K' y) := by
    rintro ⟨y, a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    intro h0
    rw [IsFractionRing.to_map_eq_zero_iff] at h0
    have : a = 0 := hinj (by simpa using h0)
    exact nonZeroDivisors.ne_zero ha this
  let g : GF →+* K' := IsLocalization.lift (M := S) hS
  letI : Algebra GF K' := g.toAlgebra
  haveI : IsScalarTower R GF K' :=
    IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := S) hS r).symm)
  have hg : Function.Injective (algebraMap GF K') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    change g (IsLocalization.mk' GF r s) = 0 at hx
    show IsLocalization.mk' GF r s = 0
    rw [IsLocalization.lift_mk', mul_eq_zero] at hx
    rcases hx with hx | hx
    · rw [IsFractionRing.to_map_eq_zero_iff] at hx
      rw [hx, IsLocalization.mk'_zero]
    · exact absurd hx (Units.ne_zero _)
  let L' := K' ⊗[GF] D
  let ι : D →ₐ[GF] L' := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := by
    have h1 : Function.Injective ((Algebra.linearMap GF K').rTensor D) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hg
    intro x y hxy
    apply (TensorProduct.lid GF D).symm.injective
    apply h1
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hxy
  have key : (ι : D →+* L').comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = algebraMap R L' := by
    ext r
    show ι (algebraMap GF D (algebraMap R GF r)) = algebraMap R L' r
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply GF K' L', IsScalarTower.algebraMap_apply R K' L',
      ← IsScalarTower.algebraMap_apply R GF K']
  letI inst : Algebra R (GlobalTheory.KeyOriginNoeth.closure A R D) := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let Φ : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] integralClosure R L' :=
    { toFun := fun c => ⟨ι c.1, by
        have hc : (GlobalTheory.KeyOriginNoeth.baseHom A R D).IsIntegralElem c.1 := c.2
        obtain ⟨p, hp, he⟩ := hc
        refine ⟨p, hp, ?_⟩
        have h2 := Polynomial.hom_eval₂ p (GlobalTheory.KeyOriginNoeth.baseHom A R D) (ι : D →+* L') c.1
        rw [he, map_zero] at h2
        rw [← key]
        exact h2.symm⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show ι (x.1 + y.1) = ι x.1 + ι y.1
        exact map_add ι _ _
      map_smul' := fun r c => by
        apply Subtype.ext
        show ι (GlobalTheory.KeyOriginNoeth.baseHom A R D r * c.1) = r • ι c.1
        rw [map_mul, Algebra.smul_def]
        congr 1
        exact RingHom.congr_fun key r }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hxy
  haveI := integralClosure_finite_of_etale R K' L'
  haveI := isNoetherian_of_injective Φ hΦ
  exact Module.IsNoetherian.finite R _

end GlobalTheory.ClosureFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocal
section
open IsLocalRing TensorProduct

namespace GlobalTheory.PurityComplete

variable (R : Type) [CommRing R] [IsRegularLocalRing R]

theorem algebraMap_mem_maximalIdeal {r : R} (hr : r ∈ maximalIdeal R) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ hr

theorem faithfullyFlat_adicCompletion :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem modDepthGE_two_baseChange (A : Type) [CommRing A] [Algebra R A]
    (h : ReciprocityTheory.CA.ModDepthGE R A 2) :
    ReciprocityTheory.CA.ModDepthGE (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R ⊗[R] A) 2 := by
  obtain ⟨rs, hl, hm, hreg⟩ := h
  refine ⟨rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R)), by simp [hl], ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact algebraMap_mem_maximalIdeal R (hm s hs)
  · haveI := faithfullyFlat_adicCompletion R
    exact hreg.of_faithfullyFlat_of_isBaseChange (S := AdicCompletion (maximalIdeal R) R)
      (TensorProduct.isBaseChange R A (AdicCompletion (maximalIdeal R) R))

theorem etale_baseChange (A : Type) [CommRing A] [Algebra R A]
    (he : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A))
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : P ≠ maximalIdeal (AdicCompletion (maximalIdeal R) R)) :
    Algebra.Etale (Localization.AtPrime P)
      (TensorProduct (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime P)
        (AdicCompletion (maximalIdeal R) R ⊗[R] A)) := by
  set C := AdicCompletion (maximalIdeal R) R
  set p : Ideal R := P.comap (algebraMap R C) with hpdef
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, ← hpdef, h]
  haveI := he p hp
  haveI : P.LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p P
  let e : Localization.AtPrime P ⊗[Localization.AtPrime p] (Localization.AtPrime p ⊗[R] A) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime P ⊗[C] (C ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) (Localization.AtPrime P)
      (Localization.AtPrime P) A).trans
    (Algebra.TensorProduct.cancelBaseChange R C (Localization.AtPrime P)
      (Localization.AtPrime P) A).symm
  exact Algebra.Etale.of_equiv e

theorem free_of_free_baseChange (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A]
    (h : Module.Free (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal R) R ⊗[R] A)) :
    Module.Free R A := by
  haveI := faithfullyFlat_adicCompletion R
  haveI : Module.Flat R A := Module.Flat.of_flat_tensorProduct R A (AdicCompletion (maximalIdeal R) R)
  exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.PurityComplete

namespace GlobalTheory.PurityStep

theorem purityFree_of_complete :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S →
        ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  intro R _ _ H A _ _ _ hd he
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  have hC := H (AdicCompletion (maximalIdeal R) R) inferInstance (UpperTheory.V.CA.g_dimcpl R)
  refine GlobalTheory.PurityComplete.free_of_free_baseChange R A ?_
  exact hC _ (GlobalTheory.PurityComplete.modDepthGE_two_baseChange R A hd)
    (fun P _ hP => GlobalTheory.PurityComplete.etale_baseChange R A he P hP)

end GlobalTheory.PurityStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneReOpenNearOfIsUnit
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

theorem traceOpen_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro R _ _ _ a b hsq g hg hu W hW
  set s := g.re with hs
  let φ : R × R → ℍ[R, a, b] := fun p => ⟨p.1, p.2 * g.imI, p.2 * g.imJ, p.2 * g.imK⟩
  have hφ : Continuous φ := by
    apply continuous_induced_rng.2
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [coords, φ] using continuous_fst
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
  have hφs : φ (s, 1) = g := by ext <;> simp [φ, s]
  have hpre : φ ⁻¹' W ∈ 𝓝 (s, (1 : R)) := hφ.continuousAt.preimage_mem_nhds (by rw [hφs]; exact hW)
  obtain ⟨O₀, hO₀, V, hV, hOV⟩ := mem_nhds_prod_iff.1 hpre
  obtain ⟨U, hU, hUV⟩ := hsq V hV
  set c : R := ((hu.unit⁻¹ : Rˣ) : R) with hc_def
  have hc : c * (1 - s ^ 2) = 1 := by
    rw [hc_def]
    have := hu.unit.inv_mul
    simpa using this
  let r : R → R := fun t => (1 - t ^ 2) * c
  have hr : Continuous r := (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
  have hrs : r s = 1 := by simp only [r]; rw [mul_comm]; exact hc
  refine ⟨interior (O₀ ∩ r ⁻¹' U), isOpen_interior, ?_, ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hO₀ ?_
    exact hr.continuousAt.preimage_mem_nhds (by rw [hrs]; exact hU)
  · intro t ht
    have ht' := interior_subset ht
    obtain ⟨μ, hμV, hμ⟩ := hUV (r t) ht'.2
    refine ⟨φ (t, μ), hOV (Set.mk_mem_prod ht'.1 hμV), ?_, rfl⟩
    have hμ' : μ ^ 2 = (1 - t ^ 2) * c := hμ
    simp only [nrm, φ] at hg ⊢
    linear_combination μ ^ 2 * hg + (1 - s ^ 2) * hμ' + (1 - t ^ 2) * hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenPi
section
noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

namespace TraceOpenPi

variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {a b : ∀ i, R i}

def comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : ℍ[R i, a i, b i] :=
  ⟨x.re i, x.imI i, x.imJ i, x.imK i⟩

def glue (u : ∀ i, ℍ[R i, a i, b i]) : ℍ[∀ i, R i, a, b] :=
  ⟨fun i => (u i).re, fun i => (u i).imI, fun i => (u i).imJ, fun i => (u i).imK⟩

theorem glue_comp (x : ℍ[∀ i, R i, a, b]) : glue (fun i => comp i x) = x := by
  ext <;> rfl

theorem nrm_comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : nrm (comp i x) = nrm x i := by
  simp [nrm, comp]

theorem nrm_glue (u : ∀ i, ℍ[R i, a i, b i]) : nrm (glue u) = fun i => nrm (u i) := by
  funext i
  simp [nrm, glue]

theorem coords_glue (u : ∀ i, ℍ[R i, a i, b i]) : coords (glue u) = fun k i => coords (u i) k := by
  funext k i
  fin_cases k <;> rfl

theorem continuous_glue [∀ i, TopologicalSpace (R i)] :
    Continuous (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b]) := by
  refine continuous_induced_rng.2 ?_
  have : (coords ∘ (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b])) =
      fun u k i => coords (u i) k := by
    funext u
    exact coords_glue u
  rw [this]
  refine continuous_pi fun k => continuous_pi fun i => ?_
  have hc : Continuous (coords : ℍ[R i, a i, b i] → Fin 4 → R i) := continuous_induced_dom
  exact ((continuous_apply k).comp hc).comp (continuous_apply i)

end TraceOpenPi


open TraceOpenPi in
theorem traceOpen_pi : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i),
    (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  intro ι _ R _ _ a b h g hg W hW
  have hgi : ∀ i, nrm (comp i g) = 1 := fun i => by
    rw [nrm_comp, hg]; rfl
  have hW' : glue ⁻¹' W ∈ 𝓝 (fun i => comp i g) := by
    refine continuous_glue.continuousAt.preimage_mem_nhds ?_
    rw [glue_comp]; exact hW
  rw [nhds_pi, Filter.mem_pi] at hW'
  obtain ⟨I, -, V, hV, hVW⟩ := hW'
  have hO := fun i => h i (comp i g) (hgi i) (V i) (hV i)
  choose O hOo hOn hOt using hO
  refine ⟨Set.univ.pi O, isOpen_set_pi Set.finite_univ fun i _ => hOo i,
    Set.univ_pi_nonempty_iff.2 hOn, fun t ht => ?_⟩
  have ht' := fun i => hOt i (t i) (ht i (Set.mem_univ i))
  choose u huV hun hur using ht'
  refine ⟨glue u, hVW fun i _ => huV i, ?_, ?_⟩
  · rw [nrm_glue]; funext i; exact hun i
  · funext i; exact hur i

end GlobalTheory.QSA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenProd
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory.QSA.TraceOpenProd

variable {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
  {a₁ b₁ : R₁} {a₂ b₂ : R₂}

def glue (p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂]) : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)] :=
  ⟨(p.1.re, p.2.re), (p.1.imI, p.2.imI), (p.1.imJ, p.2.imJ), (p.1.imK, p.2.imK)⟩

def fst (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : ℍ[R₁, a₁, b₁] :=
  ⟨x.re.1, x.imI.1, x.imJ.1, x.imK.1⟩

def snd (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : ℍ[R₂, a₂, b₂] :=
  ⟨x.re.2, x.imI.2, x.imJ.2, x.imK.2⟩

theorem glue_fst_snd (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : glue (fst x, snd x) = x := by
  ext <;> rfl

theorem nrm_glue (p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂]) : nrm (glue p) = (nrm p.1, nrm p.2) := by
  ext <;> simp [nrm, glue]

theorem nrm_fst (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : nrm (fst x) = (nrm x).1 := by
  simp [nrm, fst]

theorem nrm_snd (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : nrm (snd x) = (nrm x).2 := by
  simp [nrm, snd]

theorem continuous_coord {R : Type} [CommRing R] [TopologicalSpace R] {a b : R} (i : Fin 4) :
    Continuous (fun x : ℍ[R, a, b] => coords x i) :=
  (continuous_apply i).comp continuous_induced_dom

theorem continuous_glue : Continuous (glue : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] → _) := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro i
  have h1 : Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords p.1 i) :=
    (continuous_coord i).comp continuous_fst
  have h2 : Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords p.2 i) :=
    (continuous_coord i).comp continuous_snd
  have : (fun p => coords (glue p) i) =
      fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => (coords p.1 i, coords p.2 i) := by
    funext p
    fin_cases i <;> rfl
  show Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords (glue p) i)
  rw [this]
  exact h1.prodMk h2

end GlobalTheory.QSA.TraceOpenProd

namespace GlobalTheory.QSA


open TraceOpenProd in
theorem traceOpen_prod : ∀ (R₁ R₂ : Type) [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
    (a₁ b₁ : R₁) (a₂ b₂ : R₂), TraceOpen R₁ a₁ b₁ → TraceOpen R₂ a₂ b₂ → TraceOpen (R₁ × R₂) (a₁, a₂) (b₁, b₂) := by
  intro R₁ R₂ _ _ _ _ a₁ b₁ a₂ b₂ h₁ h₂ g hg W hW
  have hW' : glue ⁻¹' W ∈ 𝓝 (fst g, snd g) := by
    apply continuous_glue.continuousAt.preimage_mem_nhds
    rw [glue_fst_snd]; exact hW
  obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := mem_nhds_prod_iff.1 hW'
  have hg₁ : nrm (fst g) = 1 := by rw [nrm_fst, hg]; rfl
  have hg₂ : nrm (snd g) = 1 := by rw [nrm_snd, hg]; rfl
  obtain ⟨O₁, hO₁, hne₁, hO₁t⟩ := h₁ _ hg₁ W₁ hW₁
  obtain ⟨O₂, hO₂, hne₂, hO₂t⟩ := h₂ _ hg₂ W₂ hW₂
  refine ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, hne₁.prod hne₂, ?_⟩
  rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
  obtain ⟨u₁, hu₁W, hu₁n, hu₁r⟩ := hO₁t t₁ ht₁
  obtain ⟨u₂, hu₂W, hu₂n, hu₂r⟩ := hO₂t t₂ ht₂
  refine ⟨glue (u₁, u₂), hsub ⟨hu₁W, hu₂W⟩, ?_, ?_⟩
  · rw [nrm_glue, hu₁n, hu₂n]; rfl
  · simp [glue, hu₁r, hu₂r]

end GlobalTheory.QSA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGenericPointStalkSubsetOfDenseOpen
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem range_jK_fromSpecStalk_subset_of_dense_range {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S]
    [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (s : S) :
    Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆
      Set.range j := by
  rintro _ ⟨x, rfl⟩
  have hZ : irreducibleComponent s ∈ irreducibleComponents S :=
    irreducibleComponent_mem_irreducibleComponents s
  have hZo : IsOpen (irreducibleComponent s) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hZ
  obtain ⟨_, hu, ⟨u, rfl⟩⟩ := hj.inter_open_nonempty _ hZo ⟨s, mem_irreducibleComponent⟩
  have hg := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ)
  have hgs : hZ.1.genericPoint ⤳ s := hg.specializes mem_irreducibleComponent
  have hgr : hZ.1.genericPoint ∈ Set.range (S.fromSpecStalk s) := by
    rw [Scheme.range_fromSpecStalk]; exact hgs
  obtain ⟨p, hp⟩ := hgr
  have hxp : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s)) x ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes (R := S.presheaf.stalk s) _ _).mp ?_
    show Ideal.comap _ x.asIdeal ≤ p.asIdeal
    have hx0 : x.asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime (FractionRing (S.presheaf.stalk s)) _ x.asIdeal x.isPrime
    intro a ha
    rw [Ideal.mem_comap, hx0, Ideal.mem_bot] at ha
    have ha0 : a = 0 :=
      IsFractionRing.injective (S.presheaf.stalk s) (FractionRing (S.presheaf.stalk s))
        (by simpa using ha)
    rw [ha0]
    exact Ideal.zero_mem _
  have h1 : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) x ⤳
      hZ.1.genericPoint := by
    rw [Scheme.Hom.comp_apply, ← hp]
    exact hxp.map (S.fromSpecStalk s).continuous
  have h2 : hZ.1.genericPoint ⤳ j u := hg.specializes hu
  exact (h1.trans h2).mem_open j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussianStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelGaussian_pair_standardGaussian : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ), GlobalTheory.IsSiegel τ → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  first | exact @GlobalTheory.siegelGauss_pair_standard | exact GlobalTheory.siegelGauss_pair_standard | (intros; apply GlobalTheory.siegelGauss_pair_standard <;> assumption)
end

