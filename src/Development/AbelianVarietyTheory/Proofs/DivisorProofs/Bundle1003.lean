module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0962
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStable
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_of_le : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U →
    (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  intro ι M _ _ _ _ s F U U' hU hle hst
  obtain ⟨hfin, -, ip, hsym, hpos, hadj⟩ := hU
  refine ⟨Submodule.finiteDimensional_of_le hle, hst, ip, ?_, ?_, ?_⟩
  · intro x hx y hy; exact hsym x (hle hx) y (hle hy)
  · intro x hx h0; exact hpos x (hle hx) h0
  · intro a b hab x hx y hy; exact hadj a b hab x (hle hx) y (hle hy)

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCentOfMemKG
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

theorem cent_subset_KG_of_regSS {n : ℕ} {ε : Fin n → Bool} {k : UJ ε} (hk : k ∈ KG ε)
    (hr : IsRegSS (ujMat ε k)) : (cent k : Set (UJ ε)) ⊆ (KG ε : Set (UJ ε)) := by
  intro g hg
  have hg' : g * k = k * g := mem_cent.1 hg
  have h1 : ujMat ε g * ujMat ε k = ujMat ε k * ujMat ε g := by
    rw [← map_mul, ← map_mul, hg']
  have h2 : Jm ε * ujMat ε k = ujMat ε k * Jm ε := hk.2.symm
  have hJ : ujMat ε g * Jm ε = Jm ε * ujMat ε g := hr.commute h1 h2
  have hU : (ujMat ε g)ᴴ * Jm ε * ujMat ε g = Jm ε := g.2
  have hJJ := Formalism.REAL.Jm_mul_self ε
  refine ⟨?_, hJ⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (ujMat ε g)ᴴ * ujMat ε g = 1
  calc (ujMat ε g)ᴴ * ujMat ε g = (ujMat ε g)ᴴ * (Jm ε * Jm ε) * ujMat ε g := by rw [hJJ, Matrix.mul_one]
    _ = ((ujMat ε g)ᴴ * Jm ε * ujMat ε g) * Jm ε := by
        rw [Matrix.mul_assoc (ujMat ε g)ᴴ (Jm ε * Jm ε), Matrix.mul_assoc (Jm ε), ← hJ]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU, hJJ]

theorem isCompact_cent_of_mem_KG : ∀ (n : ℕ) (ε : Fin n → Bool) (k : UJ ε), k ∈ KG ε → IsRegSS (ujMat ε k) →
    IsCompact (cent k : Set (UJ ε)) := by
  intro n ε k hk hr
  have hK : IsCompact (KG ε : Set (UJ ε)) := by
    simpa [Subtype.range_coe] using (isCompact_univ (X := KG ε)).image continuous_subtype_val
  exact hK.of_isClosed_subset (isClosed_cent k) (cent_subset_KG_of_regSS hk hr)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianNondegenerateNegTraceZeroSmulInvSkewH
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory

theorem skew_dual_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = -J i j) → IsUnit J.det → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
    IsHermND σ (-ξ₀ • J⁻¹) := by
  intro F E _ _ _ _ _ σ d J hJ hdet ξ₀ hξ hσξ
  have hinv : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hmap : (J⁻¹).map σ * J.map σ = 1 := by
    have := congrArg (fun M => M.map σ) hinv
    simpa [Matrix.map_mul, Matrix.map_one] using this
  have hT : (J.map σ)ᵀ = -J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have h2 : (-J) * ((J⁻¹).map σ)ᵀ = 1 := by
    rw [← hT, ← Matrix.transpose_mul, hmap, Matrix.transpose_one]
  have hX : ((J⁻¹).map σ)ᵀ = -J⁻¹ := by
    have h3 : J * (-((J⁻¹).map σ)ᵀ) = 1 := by
      rw [Matrix.mul_neg, ← Matrix.neg_mul]; exact h2
    have h4 := Matrix.inv_eq_right_inv h3
    have h5 := congrArg Neg.neg h4
    rw [neg_neg] at h5
    exact h5.symm
  have hent : ∀ i j, σ (J⁻¹ j i) = -J⁻¹ i j := by
    intro i j
    have := congrFun (congrFun hX i) j
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_neg, hσξ, hent]
    ring
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hξ)) (Matrix.isUnit_nonsing_inv_det J hdet).ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturationStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHomogeneous_and_hilbertPoly_eq_of_prime_in_saturation : ∀ (K : Type) [Field K] (N : ℕ) (I Q : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) → Q.IsPrime → I ≤ Q → (∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) → (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧ GlobalTheory.idealHilbertPoly Q = GlobalTheory.idealHilbertPoly I := by
  first | exact @GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | exact GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | (intros; apply GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfAdicIntegralTensorBasisRingStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring : ∀ (v : HeightOneSpectrum ℤ) (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type)
    (b : Module.Basis κ ℚ C), IsIntB v b 1 → (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) →
      ∀ y, IsIntB v b y → IsIntegral (v.adicCompletionIntegers ℚ) y := by
  first | (exact @GlobalTheory.AdicSpan.isIntegral_of_isIntB) | (exact GlobalTheory.AdicSpan.isIntegral_of_isIntB) | (intros; apply GlobalTheory.AdicSpan.isIntegral_of_isIntB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeComapMulVecLinOfLeftInverseMatrix
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem isLattice_comap_mulVecLin_of_leftInverse (E : Type) [Field E] [NumberField E] (n n₁ : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hPι : P * ι = 1) (hL : L.IsFullLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E := by
  set f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E) with hf
  set g : (Fin n → E) →ₗ[𝓞 E] (Fin n₁ → E) := (Matrix.mulVecLin P).restrictScalars (𝓞 E) with hg
  have hgf : ∀ u, g (f u) = u := by
    intro u
    simp [hf, hg, Matrix.mulVec_mulVec, hPι]
  apply Submodule.IsLattice.of_fg E
  have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL.fg
  have h1 : ((L.comap f).map f).FG :=
    isNoetherian_submodule.1 hN _ (Submodule.map_comap_le f L)
  have h2 : ((L.comap f).map f).map g = L.comap f := by
    rw [← Submodule.map_comp]
    ext u
    simp only [Submodule.mem_map, LinearMap.coe_comp, Function.comp_apply, hgf]
    exact ⟨fun ⟨v, hv, he⟩ => he ▸ hv, fun hu => ⟨u, hu, rfl⟩⟩
  rw [← h2]
  exact h1.map g

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryPiFin
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem locU_pi_fin : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), LocU s F → ∀ n : ℕ, LocU s (fun a b => (LinearMap.pi fun i : Fin n => F a b ∘ₗ LinearMap.proj i : Module.End ℂ (Fin n → M))) := by
  intro ι M _ _ _ _ s F hF n t
  classical
  obtain ⟨U, htU, hfd, hst, ip, hsym, hpos, hadj⟩ := hF (t.biUnion fun x => Finset.univ.image x)
  have hmem : ∀ x ∈ t, ∀ i, x i ∈ U := fun x hx i =>
    htU _ (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  let U' : Submodule ℂ (Fin n → M) := Submodule.pi Set.univ (fun _ => U)
  let ip' : (Fin n → M) →ₗ⋆[ℂ] (Fin n → M) →ₗ[ℂ] ℂ :=
    ∑ i : Fin n, (ip ∘ₛₗ (LinearMap.proj i : (Fin n → M) →ₗ[ℂ] M)).compl₂ (LinearMap.proj i : (Fin n → M) →ₗ[ℂ] M)
  have hip' : ∀ x y, ip' x y = ∑ i, ip (x i) (y i) := by
    intro x y
    simp [ip', LinearMap.sum_apply]
  refine ⟨U', fun x hx i _ => hmem x hx i, ?_, ?_, ip', ?_, ?_, ?_⟩
  · let g : (Fin n → U) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun i => U.subtype ∘ₗ LinearMap.proj i
    have hle : U' ≤ LinearMap.range g := by
      intro x hx
      exact ⟨fun i => ⟨x i, hx i (Set.mem_univ _)⟩, by ext i; rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · intro a b hab u hu i _
    exact hst a b hab (u i) (hu i (Set.mem_univ _))
  · intro x hx y hy
    rw [hip', hip', star_sum]
    exact Finset.sum_congr rfl fun i _ => hsym _ (hx i (Set.mem_univ _)) _ (hy i (Set.mem_univ _))
  · intro x hx hx0
    rw [hip', Complex.re_sum]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (ip (x i) (x i)).re := by
      intro i _
      by_cases h : x i = 0
      · simp [h]
      · exact (hpos _ (hx i (Set.mem_univ _)) h).le
    exact Finset.sum_pos' hnn ⟨j, Finset.mem_univ _, hpos _ (hx j (Set.mem_univ _)) hj⟩
  · intro a b hab x hx y hy
    rw [hip', hip']
    exact Finset.sum_congr rfl fun i _ => hadj a b hab _ (hx i (Set.mem_univ _)) _ (hy i (Set.mem_univ _))

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotMStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrime_map_rationalFunctions_generic_linearForm_not_mem : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).IsPrime ∧ ((∃ j, X j ∉ P) → (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L) ∉ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
  first | exact @GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem | exact GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem | (intros; apply GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  intro hM
  have key := congrArg Matrix.det hA
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
    Fintype.card_fin] at key
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  have hsub : (Aᵀ * M * A.map star).submatrix e.symm e.symm =
      (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]
  have h2 := congrArg Matrix.det hsub
  rw [Matrix.det_submatrix_equiv_self, key, Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul] at h2
  exact pow_ne_zero _ (by norm_num) h2

theorem isUnit_det_of_isHerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → IsUnit X.J.det := by
  intro F E _ _ _ _ _ σ B n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact isUnit_iff_ne_zero.mpr fun h0 => h (by rw [h0, map_zero])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOpsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_matching_lattices_matches_spherical_ops : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (β' : GL (Fin V'.rank) (Lev.EAf D)) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (Lev.EAf D)) (Φ : GfC V ≃ₜ* GfC V') (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N N' : ℕ), IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → GlobalTheory.CuspMult.IsFinIso V V' β β' Pg j Φ → ∀ (P : Pl D.host.E), ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (d : List ℤ) (B : Finset (GfC V)), GlobalTheory.Hk3.SphOp V P d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ↔ GlobalTheory.Hk3.SphOp V' P d ((B.map Φ.toEquiv.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩) := by
  first | exact @GlobalTheory.SphTrans.sphOp_iff | exact GlobalTheory.SphTrans.sphOp_iff | (intros; apply GlobalTheory.SphTrans.sphOp_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOperatorGLnSmoothAffineTranslationSection
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem kerOpInf_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hχc hσ hα hαc hαs T hT
  have hdet : ∀ w : InfinitePlace E, ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      (Matrix.of (σ₀ + L p.1)).det w := by
    intro w
    simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply]
    refine ContDiff.sum fun s _ => ?_
    refine ContDiff.mul ?_ (contDiff_prod fun i _ => ?_)
    · exact contDiff_const
    have : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) => σ₀ + L p.1 :=
      contDiff_const.add (L.contDiff.comp contDiff_fst)
    exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 this (s i)) i) w
  have hJ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) := by
    simp only [jacInf, Complex.ofReal_prod, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    exact contDiff_prod fun w _ => ((Complex.conjCLE.contDiff.comp (hdet w)).mul (hdet w)).pow n
  have hΦ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 :=
    ((hχ.comp contDiff_fst).mul hJ).mul (hα.comp contDiff_snd)
  have hΦc : HasCompactSupport fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 := by
    refine HasCompactSupport.intro (hχc.isCompact.prod hαc.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  obtain ⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩ := _root_.GlobalTheory.JSW.exists_rapid_superposition_characters _ _ hΦ hΦc
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf E n Z σ₀ L χ α hχc hσ hαc hαs X ν κ τ h1 h2 h3 (fun z a => h4 (z, a))
  exact GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily E n Z T hT _ _ _ _ _ (GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ h1 h2 h3 R σ₀ L) (smoothMatInf α) _ χ
    (GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth E n α hα.continuous hαc hαs) hR

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_invariant_forms_proportional_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (κ : Type) [Fintype κ] (Λ : Submodule (Fv F v) ((κ → Fv F v) × (κ → Fv F v))),
    (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank (Fv F v) Λ = Fintype.card κ →
    ∀ l₁ l₂ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₁ (schr ψv w φ) = l₁ φ) →
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₂ (schr ψv w φ) = l₂ φ) →
    (∃ φ ∈ SB (κ → Fv F v), l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), l₁ φ = c * l₂ φ := by
  first | exact @GlobalTheory.LagrInvForm.proportional_at_place | exact GlobalTheory.LagrInvForm.proportional_at_place | (intros; apply GlobalTheory.LagrInvForm.proportional_at_place <;> assumption)
end

