module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFinite

theorem finiteDimensional_of_trdeg_eq (F A B K L : Type) [Field F] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra F A] [Algebra A B] [Algebra F B]
    [IsScalarTower F A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.FiniteType A B] (n : ℕ) (hA : Algebra.trdeg F A = n) (hB : Algebra.trdeg F B = n) :
    FiniteDimensional K L := by
  letI : Algebra F K := ((algebraMap A K).comp (algebraMap F A)).toAlgebra
  letI : Algebra F L := ((algebraMap B L).comp (algebraMap F B)).toAlgebra
  haveI : IsScalarTower F A K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F B L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F K L := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change algebraMap B L (algebraMap F B x) = algebraMap K L (algebraMap A K (algebraMap F A x))
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply F A B]
  haveI : FaithfulSMul F A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F A).injective
  haveI : FaithfulSMul F B := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F B).injective
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective A K)
  haveI : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective B L)
  haveI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  haveI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hK : Algebra.trdeg F K = n := (trdeg_eq_of_isAlgebraic_top F A K).trans hA
  have hL : Algebra.trdeg F L = n := (trdeg_eq_of_isAlgebraic_top F B L).trans hB
  have h0 : Algebra.trdeg K L = 0 := by
    have e := trdeg_add_eq F K (A := L)
    rw [hK, hL] at e
    rcases (Cardinal.add_eq_left_iff).1 e with h | h
    · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 (Cardinal.natCast_lt_aleph0))
    · exact h
  haveI : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.1 h0
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  let g : B →ₐ[A] L := IsScalarTower.toAlgHom A B L
  let T : IntermediateField K L := IntermediateField.adjoin K (g '' (s : Set B))
  have hfin : FiniteDimensional K T :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hrange : ∀ b : B, algebraMap B L b ∈ T := by
    intro b
    have hb : b ∈ Algebra.adjoin A (s : Set B) := hs ▸ Algebra.mem_top
    have : g b ∈ (Algebra.adjoin A (s : Set B)).map g := Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    have hle : Algebra.adjoin A (g '' (s : Set B)) ≤ T.toSubalgebra.restrictScalars A :=
      Algebra.adjoin_le (IntermediateField.subset_adjoin K _)
    exact hle this
  have htop : T = ⊤ := by
    refine eq_top_iff.2 fun l _ => ?_
    obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := B) l
    exact T.div_mem (hrange x) (hrange y)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv

end GlobalTheory.GenFinite

namespace GlobalTheory.GenFinite

theorem trdeg_affineOpen_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp F) [LocallyOfFiniteType q] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) [Algebra F Γ(Y, U)] [Algebra.FiniteType F Γ(Y, U)] (n : ℕ)
    (hn : topologicalKrullDim Y = n) : Algebra.trdeg F Γ(Y, U) = n := by
  haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  have e : topologicalKrullDim (U : Set Y) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F q U hne, hn] at e
  have hd : d = n := by exact_mod_cast e.symm
  rw [h₂, hd]

theorem residueDegree_genericPoint_ne_zero : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  intro F _ M W _ _ p f n hp hf hs hM hW
  have hη : f (genericPoint M) = genericPoint W := by
    have := (genericPoint_spec M).image f.continuous
    rw [Set.image_univ, f.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec W)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  have hA : Algebra.trdeg F Γ(W, V) = n := trdeg_affineOpen_eq F p hV ⟨_, hx⟩ n hW
  have hB : Algebra.trdeg F Γ(M, U) = n := trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  letI := (M.evaluation U _ hy).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
  letI : Algebra Γ(W, V) (M.residueField (genericPoint M)) :=
    (f.appLE V U e ≫ M.evaluation U _ hy).hom.toAlgebra
  haveI : IsScalarTower Γ(W, V) Γ(M, U) (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI : IsScalarTower Γ(W, V) (W.residueField (f (genericPoint M)))
      (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' congr($(nat).hom)
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  haveI := GenFiniteEtale.isFractionRing_eval M hU rfl hy
  have := finiteDimensional_of_trdeg_eq F Γ(W, V) Γ(M, U) (W.residueField (f (genericPoint M)))
    (M.residueField (genericPoint M)) n hA hB
  change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
  exact Module.finrank_pos.ne'

end GlobalTheory.GenFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoInvariantFormConstMulInner
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchUniq.FormTransport

open GlobalTheory.RealWeil GlobalTheory.ArchUniq
open scoped SchwartzMap ComplexConjugate

theorem rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    rhoFun w G x * conj (rhoFun w G' x) = G (x + pPart w) * conj (G' (x + pPart w)) := by
  have h : phase w x * conj (phase w x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]; simp
  simp only [rhoFun, map_mul]
  calc _ = (phase w x * conj (phase w x)) * (G (x + pPart w) * conj (G' (x + pPart w))) := by ring
    _ = _ := by rw [h, one_mul]

theorem integral_rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w G x * conj (rhoFun w G' x) = ∫ x, G x * conj (G' x) := by
  simp_rw [rhoFun_mul_conj]
  exact integral_add_right_eq_self (fun x => G x * conj (G' x)) (pPart w)


open scoped Classical in
theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    {κ : Type} [Fintype κ] (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (u : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w u = schrF (trP F κ) w u := by
  funext x
  have h2 : (⅟(2 : mixedEmbedding.mixedSpace F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]
    norm_num
  have ht : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w.2 + ⅟(2 : mixedEmbedding.mixedSpace F) * (w.1 ⬝ᵥ w.2)) =
      trP F κ x w.2 + trP F κ w.1 w.2 / 2 := by
    rw [map_add (f := _), h2, ← Algebra.smul_def, map_smul, smul_eq_mul]
    simp only [trP, dotProduct]
    ring
  simp only [schr, schrF, hψ, ht]

theorem haar_coords_cplx {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, ∀ G : V → ℂ, ∫ y, G y ∂μ = (k : ℂ) * ∫ x, G (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ), fun G => ?_⟩
  have h1 : ∫ y, G y ∂μ = ∫ x, G (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, G (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]


open scoped Classical in
theorem const_of_euclidean : (∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x)) → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro H F _ _ _ κ _ ψ hψ T A hT
  letI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  have hP : IsPairing (trP F κ) := Coord.isPairing_trP κ
  obtain ⟨C, φ, -, hS⟩ := exists_pairing_coords (κ → mixedEmbedding.mixedSpace F) (trP F κ) hP _ rfl
  generalize Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F) = n at C φ hS
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  let T' : Sch (Fin n) →L[ℂ] Sch (Fin n) := toE.comp (T.comp toV)
  have hT' : ∀ h, T' h = toE (T (toV h)) := fun h => rfl
  have hI : ∀ w (h g : Sch (Fin n)), ⇑g = rhoFun w ⇑h → ⇑(T' g) = rhoFun (φ (A (φ.symm w))) ⇑(T' h) := by
    intro w h g hg
    have e1 : ⇑(toV g) = schr ψ (φ.symm w) ⇑(toV h) := by
      rw [schr_eq_schrF ψ hψ]
      funext x
      have := congrFun (hS (φ.symm w) ⇑h) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hg]
      exact this.symm
    have e2 := hT _ _ _ e1
    rw [schr_eq_schrF ψ hψ] at e2
    rw [hT', hT', htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T (toV h)) = G ∘ ⇑C :=
      ⟨⇑(T (toV h)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp
  let B : Sch (Fin n) → Sch (Fin n) → ℂ := fun h h' => ∫ x, T' h x * conj (T' h' x)
  have hcont : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h := by
    intro h'
    refine ⟨(innerSL ℂ ((T' h').toLp 2)).comp
      ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))).comp T'), fun h => ?_⟩
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.inner_toL2_toL2_eq (T' h') (T' h) volume]
    simp only [B, RCLike.inner_apply]
  have hherm : ∀ h h', B h' h = conj (B h h') := by
    intro h h'
    simp only [B]
    rw [← integral_conj]
    congr 1
    funext x
    simp [mul_comm]
  have hpos : ∀ h, 0 ≤ (B h h).re := by
    intro h
    have e : B h h = ((∫ x, Complex.normSq (T' h x) : ℝ) : ℂ) := by
      have e0 : B h h = ∫ x, ((Complex.normSq (T' h x) : ℝ) : ℂ) := by simp only [B, Complex.mul_conj]
      rw [e0]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [e, Complex.ofReal_re]
    exact integral_nonneg fun x => Complex.normSq_nonneg _
  have hinv : ∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : Sch (Fin n)), ⇑g = rhoFun w ⇑h →
      ⇑g' = rhoFun w ⇑h' → B g g' = B h h' := by
    intro w h h' g g' hg hg'
    simp only [B]
    rw [hI w h g hg, hI w h' g' hg']
    exact integral_rhoFun_mul_conj _ _ _
  obtain ⟨c, hc0, hc⟩ := H n B hcont hherm hpos hinv
  have hB : ∀ f f' : SInf F κ, ∫ x, T f (C.symm x) * conj (T f' (C.symm x)) =
      (c : ℂ) * ∫ x, f (C.symm x) * conj (f' (C.symm x)) := by
    intro f f'
    have := hc (toE f) (toE f')
    simpa only [B, hT', hVE, htoE, Function.comp_apply] using this
  refine ⟨c, hc0, fun μ hμ f f' => ?_⟩
  haveI := hμ
  obtain ⟨k, hk⟩ := haar_coords_cplx μ C
  rw [hk, hk, hB]
  ring

end GlobalTheory.ArchUniq.FormTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
section
open IsDedekindDomain NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchDeriv
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem archimedean_map_add (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (a + b) = GlobalTheory.WeilL2Words.arch1 F a + GlobalTheory.WeilL2Words.arch1 F b := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact map_add _ a b
  · exact (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem adeleOfMixedSpaceComponent_finsetSum (f : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (∑ k, f k) = ∑ k, GlobalTheory.WeilL2Words.arch1 F (f k) :=
  map_sum (AddMonoidHom.mk' (GlobalTheory.WeilL2Words.arch1 F) (archimedean_map_add F)) f Finset.univ

theorem adeleJoin_mul_arch1 (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) (k : κ)
    (b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilCont.adeleJoin F x y k * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (x k * b) := by
  unfold GlobalTheory.WeilL2Words.arch1 GlobalTheory.WeilCont.adeleJoin
  refine Prod.ext ?_ ?_
  · exact (map_mul _ (x k) b).symm
  · exact mul_zero (y k)

theorem adeleOfMixedSpaceComponent_mul (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F a * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (a * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact (map_mul _ a b).symm
  · exact mul_zero (0 : FiniteAdeleRing (𝓞 F) F)

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + GlobalTheory.WeilL2Words.arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (map_add _ (x i) (v i)).symm
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x w : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, x k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleJoin_mul_arch1 F x y k (w k)

theorem arch_dot_arch (v w : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch F v ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, v k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleOfMixedSpaceComponent_mul F (v k) (w k)

theorem mul_arch1 [Invertible (2 : AdeleRing (𝓞 F) F)] (b : mixedEmbedding.mixedSpace F) :
    ⅟(2 : AdeleRing (𝓞 F) F) * GlobalTheory.WeilL2Words.arch1 F b =
      GlobalTheory.WeilL2Words.arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · show (⅟(2 : AdeleRing (𝓞 F) F)).1 * _ = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero _

end GlobalTheory.ArchDeriv

open GlobalTheory.ArchDeriv
namespace GlobalTheory.WeilL2Words

theorem dS_adeleJoin_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hs h x
  set s : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y) with hs_def
  set P : mixedEmbedding.mixedSpace F := ∑ k, x k * h.2 k with hP
  set Q : mixedEmbedding.mixedSpace F :=
    InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * ∑ k, h.1 k * h.2 k with hQ
  set r : ℝ → ℝ := fun t => t * ℓ P + t ^ 2 * ℓ Q with hr
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)) * s (x + t • h.1) := by
    funext t
    have e1 : (t • h).1 = t • h.1 := rfl
    have e2 : (t • h).2 = t • h.2 := rfl
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilL2Words.archPair, e1, e2, adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch,
      mul_arch1, ← archimedean_map_add]
    congr 1
    · rw [hψ]
      congr 2
      have q1 : (∑ k, x k * (t • h.2) k) = t • P := by
        simp only [hP, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]
      have q2 : InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 *
          ∑ k, (t • h.1) k * (t • h.2) k = t ^ 2 • Q := by
        simp only [Pi.smul_apply, smul_mul_smul_comm]
        rw [← Finset.smul_sum, mul_smul_comm, hQ, pow_two]
      rw [q1, q2, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hr' : HasDerivAt r (ℓ P) 0 := by
    have h1 := (hasDerivAt_mul_const (x := (0 : ℝ)) (ℓ P)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (ℓ Q))
    exact h1.congr_deriv (by simp)
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * (r 0 : ℂ)) * (2 * Real.pi * Complex.I * (ℓ P : ℂ))) 0 :=
    (hr'.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hc : HasDerivAt (fun t : ℝ => x + t • h.1) h.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add x
  have hS : HasDerivAt (fun t : ℝ => s (x + t • h.1)) (fderiv ℝ s x h.1) 0 := by
    have hf : HasFDerivAt s (fderiv ℝ s x) (x + (0 : ℝ) • h.1) := by
      rw [zero_smul, add_zero]
      exact (hs x).hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hc
  have hD := hE.mul hS
  unfold GlobalTheory.WeilL2Words.dS
  rw [key]
  refine hD.deriv.trans ?_
  have r0 : r 0 = 0 := by simp [hr]
  simp only [r0, zero_smul, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring

end GlobalTheory.WeilL2Words

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E), IsHecke F E χ →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), IsSmU (chrW χ t) ∧ (∃ e, GlobalTheory.SplitFlip.CondLE (unifAt v) e (chrW χ t)) ∧
      (GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t)) := by
  first | exact @GlobalTheory.ChrWLocal.chrW_local | exact GlobalTheory.ChrWLocal.chrW_local | (intros; apply GlobalTheory.ChrWLocal.chrW_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruenStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableTwistedOrbitalIntegral_integralNormCongruence_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  first | exact @GlobalTheory.BCT.StTwLevel.stTw2_lev | exact GlobalTheory.BCT.StTwLevel.stTw2_lev | (intros; apply GlobalTheory.BCT.StTwLevel.stTw2_lev <;> assumption)
end

