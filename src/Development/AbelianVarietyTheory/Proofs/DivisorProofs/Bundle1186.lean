module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTowerTrBasisAppendCoordinates
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1153
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicMvPolynomialEvalAdjoinEtaleTowerCoord
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TowerTrdeg

theorem image_isAlgebraic : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  (letI := cL.toAlgebra; ∀ a : MvPolynomial (Fin r) R,
    IsAlgebraic (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))))
      ((MvPolynomial.eval₂Hom ι τ a : T) : L)) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  letI := cL.toAlgebra
  intro a
  have hy : IsTranscendenceBasis ℂ (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) :=
    trBasis_append cK cL n r R T ι ψ τ x h hx
  exact hy.isAlgebraic.isAlgebraic _

end GlobalTheory.FieldPair.TowerTrdeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOfConjPointwise
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

theorem isCuspForm_of_conj_pointwise : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a), (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) → (∀ o φ, act o (C φ) = C (act o φ)) → (∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ)) → ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ) := by
  intro E _ _ _ a C hC hact hZ φ hφ
  obtain ⟨h, hc⟩ := hφ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    rw [hC, hC, h.left]
  · convert h.level using 1
    ext k
    change act (.fin k) (C φ) = C φ ↔ act (.fin k) φ = φ
    rw [hact]
    exact C.injective.eq_iff
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hact (.cpt k) φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := hZ z hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  · intro g
    obtain ⟨K, N, h1⟩ := h.growth g
    refine ⟨K, N, fun y => ?_⟩
    rw [hC, RCLike.norm_conj]
    exact h1 y
  · intro r hr0 hra _ _ μ 𝓕 hμ h𝓕 g
    have := hc r hr0 hra μ 𝓕 hμ h𝓕 g
    simp_rw [hC]
    rw [integral_conj, this, map_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeModuleGeneratorKaehlerWedgeRegularPairConsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeModuleGenerator_kaehlerWedge_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∃ (m : ℕ) (z : Fin m → Q),
    (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
    IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  first | exact @GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons | exact GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons | (intros; apply GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

def IsIdTorusElt (l : Fin r → (AF F ⊗[F] E)ˣ) (a : GAd σ J) : Prop :=
  (matHom _ σ J a).1 * adMat F X = adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  (matHom _ σ J a).1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  ∀ z ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ, (matHom _ σ J a).1 *ᵥ z = z



end GlobalTheory.IdTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := by
  first | exact @GlobalTheory.GraphLocal.isLocModel_locAt | exact GlobalTheory.GraphLocal.isLocModel_locAt | (intros; apply GlobalTheory.GraphLocal.isLocModel_locAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointTensorGraphLocalization
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DiagLoc

theorem isLocModel_loc : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ'),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  IsLocModel (algebraMap ℂ L) (GlobalTheory.DiagLoc.loc L σ) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ hK hκ
  have hc : ∀ a : ℂ, algebraMap ℂ L a ∈ loc L σ := fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L]
    exact (toLoc L σ (algebraMap ℂ (K ⊗[ℂ] κ') a)).2
  refine
    { const_mem := hc
      isLocalRing := inferInstance
      essFiniteType := ?_
      frac := ?_ }
  · have e : (algebraMap ℂ L).codRestrict (loc L σ) hc =
        (toLoc L σ).comp (algebraMap ℂ (K ⊗[ℂ] κ')) := by
      ext a
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, coe_toLoc]
      exact IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L a
    rw [e]
    haveI : Algebra.EssFiniteType K (K ⊗[ℂ] κ') := Algebra.EssFiniteType.baseChange ℂ κ' K
    haveI : Algebra.EssFiniteType ℂ (K ⊗[ℂ] κ') := Algebra.EssFiniteType.comp ℂ K (K ⊗[ℂ] κ')
    have h1 : (algebraMap ℂ (K ⊗[ℂ] κ')).EssFiniteType := RingHom.essFiniteType_algebraMap.2 this
    haveI : Algebra.EssFiniteType (K ⊗[ℂ] κ') (loc L σ) :=
      Algebra.EssFiniteType.of_isLocalization (loc L σ) (ker σ).primeCompl
    have h2 : (toLoc L σ).EssFiniteType := by
      rw [← algebraMap_loc]; exact RingHom.essFiniteType_algebraMap.2 this
    exact RingHom.EssFiniteType.comp h1 h2
  · intro f
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') f
    have hb0 : algebraMap (K ⊗[ℂ] κ') L b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨_, (toLoc L σ a).2, _, (toLoc L σ b).2, hb0, ?_⟩
    rw [coe_toLoc, coe_toLoc, ← e, div_mul_cancel₀ _ hb0]

end GlobalTheory.DiagLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalEquationChangeFormPerturbedDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem isLogEqn_changeForm_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (η η' : RatForms p n) (x : X) (m mD l : ℕ)
    (gG fD g a F : X.functionFieldˣ) (A : CartierDiv X) (δ t : ℚ), η' ≠ 0 → η = (F : X.functionField) • η' →
    0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) → A.IsEqn x a →
    ∃ (m₂ : ℕ) (g₂ : X.functionFieldˣ), 0 < m₂ ∧
      IsLogEqn p (Δ + (1 - δ) • D + t • qWeil (CartierDiv.principal g + l • A) 1) η' x m₂ g₂ ∧
      ∀ E : DivOver p, discrep E η' m₂ g₂ = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η' + E.ord F - E.ord gG / m
        - (1 - δ) * (E.ord fD / mD) - t * E.ord (g * a ^ l) := by
  intro X _ _ p _ n hn Δ D η η' x m mD l gG fD g a F A δ t hη' hηF hm hmD hg hD hA
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'

  set gG' : X.functionFieldˣ := gG * F ^ (-(m : ℤ)) with hgG'
  have hord (E : DivOver p) : (E.ord gG' : ℚ) = E.ord gG - m * E.ord F := by
    rw [hgG', E.ord_mul, divOver_ord_zpow]
    push_cast
    ring
  have h1 : IsLogEqn p Δ η' x m gG' := by
    intro z hz E hE
    have e := hg z hz E hE
    rw [hηF, E.formOrd_smul hn hη' F] at e
    rw [hord, ← e]
    push_cast
    ring
  have hd1 (E : DivOver p) : discrep E η' m gG' = E.formOrd η' + E.ord F - E.ord gG / m := by
    rw [discrep, hord]
    field_simp
    ring

  obtain ⟨m₁, g₁, hm₁, h2, hd2⟩ := isLogEqn_add_smul X p n Δ D η' x m mD gG' fD (1 - δ) hm hmD h1 hD

  have hB : (CartierDiv.principal g + l • A).IsEqn x (g * a ^ l) :=
    (CartierDiv.isEqn_principal g x).add (hA.nsmul l)
  obtain ⟨V, hxV, hV⟩ := hB.exists_nhds
  have hD' : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal g + l • A) 1 z = (E.ord (g * a ^ l) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    rw [qWeil, (hV z (hz.mem_open V.isOpen hxV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, h3, hd3⟩ := isLogEqn_add_smul X p n (Δ + (1 - δ) • D)
    (qWeil (CartierDiv.principal g + l • A) 1) η' x m₁ 1 g₁ (g * a ^ l) t hm₁ Nat.one_pos h2 hD'
  refine ⟨m₂, g₂, hm₂, h3, fun E => ?_⟩
  rw [hd3, hd2, hd1]
  unfold DivOver.formOrd
  push_cast
  ring

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPsEffPullReducedClosedOfDimLeStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPsEff_pull_reduced_closed_of_dim_le : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ M : LB X, IsNef k M → ∀ Z : Closeds X, IsIrreducible (Z : Set X) → topologicalKrullDim (Z : Set X) ≤ (d : ℕ) → IsPsEff (M.pull (redι Z)) := by
  first | exact @GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le | exact GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le | (intros; apply GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPseudoEffectiveReducedUnivOfSectionPowStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPseudoEffective_reducedUniv_of_section_pow : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (M : LB X), M.IsLB → ∀ r : ℕ, 1 ≤ r → HasNonzeroSec (lbPow M r) → ∀ Z : Closeds X, (Z : Set X) = Set.univ → IsPsEff (M.pull (redι Z)) := by
  first | exact @GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow | exact GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow | (intros; apply GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacConj
variable {D : D7}
theorem inv_neg' {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem star_char' {R : Type} [CommRing R] (ψ : AddChar R ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : R) :
    star (ψ (-x)) = ψ x := by
  have h1 : ψ (-x) * ψ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ (-x)) * ψ (-x) = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc star (ψ (-x)) = star (ψ (-x)) * (ψ (-x) * ψ x) := by rw [h1, mul_one]
    _ = ψ x := by rw [← mul_assoc, h2, one_mul]

theorem hO_neg (S T : HSp D) (x y : WO S T) : hO (negSp S) T x y = -hO S T x y := by
  unfold hO
  rw [negSp_gram, inv_neg']
  simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem symplOH_neg (S T : HSp D) (x y : WO S T) : symplOH (negSp S) T x y = -symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_neg, mul_neg, map_neg, mul_neg]

theorem heisO_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (u : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (fun w => starRingEnd ℂ (f w)) = fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w) := by
  funext w
  simp only [heisO, symplOH_neg, map_mul]
  rw [← Complex.star_def, star_char' ψ hψ]

theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (-z) t = lineAt θ τ z (-t) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) := Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)
  have hL0 : IsLineAt θ τ (-z) (lineAt θ τ (-z)) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ (-z))
  have hN : IsLineAt θ τ (-z) (-lineAt θ τ z) := by
    refine ⟨continuous_neg.comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => RingHom.map_neg (finPart D) a), hL.2.1 t, neg_zero]
    · have := hL.2.2 t τ'
      have e : compAt θ τ' ((-lineAt θ τ z) t) = -compAt θ τ' (lineAt θ τ z t) := by
        unfold compAt
        rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => by rw [RingHom.map_neg, RingHom.map_neg])]
      rw [e, this]
      split_ifs <;> simp
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-z) _ _ hL0 hN]
  simp

theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (f : Mx D m n → ℂ) (x : Mx D m n) :
    Formalism.IndefR.Datum.dRho hs θ τ (-z) f x = -Formalism.IndefR.Datum.dRho hs θ τ z f x := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [lineAt_neg hθ]
  rw [deriv_comp_neg (f := fun t => hs (lineAt θ τ z t) f x), neg_zero]

theorem dRho_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (x : WO S T) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (fun w => starRingEnd ℂ (f w)) x =
      starRingEnd ℂ (Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z f x) := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [heisO_conj ψ hψ]
  exact deriv.star

theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

theorem latO_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

end GlobalTheory.VacConj

namespace GlobalTheory.VacConj

theorem isVacO_conj_negSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO (negSp S) T → ℂ) :
    IsVacO ψ θ (negSp S) T (fun τ => -sS τ) sT LS LT f → IsVacO ψ θ S T sS sT LS LT (fun w => starRingEnd ℂ (f w)) := by
  rintro ⟨hψ, hv⟩
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hθ : IsInfFam θ := hv.inf
  refine ⟨hψ, ⟨hθ, ⟨fun γ w => ?_, ?_, ?_, ?_⟩, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, ?_⟩⟩
  · have h := hv.theta.quasi γ w
    show starRingEnd ℂ (f (ratW T S γ + w)) = _
    rw [show f (ratW T S γ + w) = _ from h, map_mul, symplOH_neg, ← Complex.star_def, star_char' ψ hn]
    rfl
  · obtain ⟨U, hU, hUf⟩ := hv.theta.level
    exact ⟨U, hU, fun u hu hu' => by rw [heisO_conj ψ hn, hUf u hu hu']⟩
  · exact Complex.continuous_conj.comp hv.theta.cont
  · intro k L hL hL' w
    exact (Complex.conjCLE.contDiff.comp (hv.theta.smooth k L hL hL' w) :)
  · rw [heisO_conj ψ hn, hv.lat.1 u (latO_le S T LS LT _ hu)]
  · rw [heisO_conj ψ hn, hv.lat.2 e he u (latO_le S T LS LT _ hu) hh]
  · funext x
    have h := congrFun (hv.fock τ z) x
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    rw [cplxO_neg, dRho_neg hθ] at h
    rw [dRho_conj ψ hn, dRho_conj ψ hn]
    have h' := congrArg (starRingEnd ℂ) h
    simp only [map_add (f := _), map_mul, map_neg, Complex.conj_I, map_zero] at h'
    linear_combination h'
  · obtain ⟨h1, h2⟩ := hv.norm
    refine ⟨h1, fun p hp => ?_⟩
    have := h2 p hp
    unfold nrm2 at this ⊢
    simp only [Complex.norm_conj]
    exact this

end GlobalTheory.VacConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlobalSectionsDimNefPowTensorAmpleIsBiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0}) [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F (X := Z)) → topologicalKrullDim Z ≤ d → ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  first | exact @GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | exact GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | (intros; apply GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO <;> assumption)
end

