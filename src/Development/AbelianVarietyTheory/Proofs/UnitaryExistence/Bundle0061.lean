module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicQuotientMeasure
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
section
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.AdelicUnitaryTop

section Restricted

theorem secondCountable_restrictedProduct {ι : Type} [Countable ι] (R : ι → Type)
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)] (A : ∀ i, Set (R i))
    (hA : ∀ i, IsOpen (A i)) : SecondCountableTopology (Πʳ i, [R i, A i]) := by
  have hS : ∀ T : Finset ι, cofinite ≤ 𝓟 ((T : Set ι)ᶜ) := fun T =>
    le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)
  have hsc : ∀ T : Finset ι, SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((T : Set ι)ᶜ)]) :=
    fun T => RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  have he := fun T : Finset ι => RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)
  haveI : ∀ T : Finset ι, SecondCountableTopology
      (Set.range (RestrictedProduct.inclusion R A (hS T))) := fun T =>
    (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx : {i | ¬ x i ∈ A i}.Finite := eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ?_⟩
  refine RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_
  intro i hi
  by_contra h
  exact hi (by simpa using h)

end Restricted

section Adeles

variable (F : Type) [Field F] [NumberField F]

theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.glint_finite_residueField v

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  Valued.integer.properSpace_iff_compactSpace_integer.1 (properSpace_adicCompletion F v)

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
      fun a b h => HeightOneSpectrum.ext h

theorem locallyCompact_finiteAdele : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI := properSpace_adicCompletion F
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (.of_forall fun v => isCompact_iff_compactSpace.2 (compactSpace_adicCompletionIntegers F v))

theorem secondCountable_finiteAdele : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI := properSpace_adicCompletion F
  haveI := countable_heightOneSpectrum F
  exact secondCountable_restrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun _ ↦ Valued.isOpen_valuationSubring _

theorem t2Space_finiteAdeleRing_of_numberField : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem secondCountable_infiniteAdele : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

theorem t2Space_infiniteAdeleRing_of_numberField_field : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

theorem locallyCompact_adele : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  haveI := locallyCompact_finiteAdele F
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountable_adele : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  haveI := secondCountable_finiteAdele F
  haveI := secondCountable_infiniteAdele F
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem t2Space_adeleRing_numberField : T2Space (AdeleRing (𝓞 F) F) :=
  haveI := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Adeles

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem nonempty_homeomorph :
    Nonempty (R ⊗[F] E ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem lcsc_HA [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) :=
  by apply _root_.UpperTheory.Reformulated.B.Yzd4.lcsc_HA <;> assumption

end Tensor

theorem lcsc_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  intro F E _ _ _ _ _ σ M J
  haveI := locallyCompact_adele F
  haveI := secondCountable_adele F
  haveI := t2Space_adeleRing_numberField F
  exact lcsc_HA (AF F) σ M J

end GlobalTheory.AdelicUnitaryTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.QuotientMeasureEqChosenProbability
section
noncomputable section

open MeasureTheory NumberField GlobalTheory.IndefiniteRowSideFullHecke.AdelicQuotientClasses
open scoped ENNReal NNReal Pointwise Classical

namespace GlobalTheory.AutQuotCompare

section First

variable {H : Type} [Group H] (Γ : Subgroup H)

variable [MeasurableSpace H] (P P' : Measure H × Set H → Prop)

end First

section Haar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

end Haar

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

variable {G}

end Adelic

section Transport

variable {H H' : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H']
  {Γ : Subgroup H} {Γ' : Subgroup H'} (e : H ≃ₜ* H') (he : ∀ g, e g ∈ Γ' ↔ g ∈ Γ)


variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H']

end Transport

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {G : Matrix (Fin n) (Fin n) E}
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  {Γ : Subgroup H}

def IsHaarPair (Γ : Subgroup H) (p : Measure H × Set H) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain Γ p.2 p.1

end Main

section Split

open scoped Matrix

variable {R S ι : Type} [CommRing R] [CommRing S] (Φ : R ≃+* (ι → ℂ) × S) {n : ℕ}

def compAt (w : ι) : R →+* ℂ := (Pi.evalRingHom _ w).comp ((RingHom.fst _ _).comp Φ.toRingHom)

def compLast : R →+* S := (RingHom.snd _ _).comp Φ.toRingHom

theorem continuous_map {R R' : Type} [CommRing R] [CommRing R'] [TopologicalSpace R] [TopologicalSpace R']
    {φ : R →+* R'} (h : Continuous φ) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) φ) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map h, Units.continuous_coe_inv.matrix_map h⟩

variable [TopologicalSpace R] [TopologicalSpace S] (hc : Continuous Φ) (hc' : Continuous Φ.symm)
  {s : R →+* R} {s' : S →+* S} (hs : ∀ w z, compAt Φ w (s z) = starRingEnd ℂ (compAt Φ w z))
  (hs' : ∀ z, compLast Φ (s z) = s' (compLast Φ z)) {J : Matrix (Fin n) (Fin n) R}
  {A : ι → Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) S}
  (hA : ∀ w, Jᵀ.map (compAt Φ w) = A w) (hB : Jᵀ.map (compLast Φ) = B)

end Split

section Adeles

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem sigmaCompact_inf (F : Type) [Field F] [NumberField F] [Algebra F E] : SigmaCompactSpace (Ainf F ⊗[F] E) := by
  have : ∀ v : InfinitePlace F, SigmaCompactSpace v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.sigmaCompactSpace
  have : SigmaCompactSpace (Ainf F) := inferInstanceAs (SigmaCompactSpace (∀ v : InfinitePlace F, v.Completion))
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (Ainf F) (Ainf F ⊗[F] E)
  refine ⟨?_⟩
  rw [← hf.range_eq]
  exact isSigmaCompact_range (IsModuleTopology.continuous_of_linearMap f)

theorem exists_inf_equiv : ∃ Θ : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E ≃+* (InfinitePlace E → ℂ),
    Continuous Θ ∧ Continuous Θ.symm ∧ (∀ x w, Θ (1 ⊗ₜ x) w = w.embedding x) ∧
      ∀ z w, Θ (GlobalTheory.AdLat.sg _ (IsCMField.complexConj E) z) w = starRingEnd ℂ (Θ z w) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective (maximalRealSubfield E) E (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) inferInstance
    (IsCMField.complexEmbedding_complexConj E)
  choose θ hθ using h1
  obtain ⟨h3, h4, h5⟩ := h2 θ hθ
  have hinj : Function.Injective (fun w : InfinitePlace E => w.embedding) := fun v w h => by
    rw [← v.mk_embedding, ← w.mk_embedding]; exact congrArg _ h
  have hmem : ∀ τ : E →+* ℂ, τ ∈ Set.range (fun w : InfinitePlace E => w.embedding) ↔
      (InfinitePlace.mk τ).embedding = τ := fun τ =>
    ⟨fun ⟨w, hw⟩ => by rw [← hw]; simp only [InfinitePlace.mk_embedding], fun h => ⟨_, h⟩⟩
  have hb := h5 (Set.range fun w : InfinitePlace E => w.embedding) fun τ => by
    have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
      IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
    rw [hmem, hmem, InfinitePlace.mk_conjugate_eq]
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]; simp [hne.symm]
    · rw [h]; simp [hne]
  let f : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* (InfinitePlace E → ℂ) :=
    Pi.ringHom fun w => θ w.embedding
  have hf : Function.Bijective f :=
    (Equiv.arrowCongr (Equiv.ofInjective _ hinj).symm (Equiv.refl ℂ)).bijective.comp hb
  have hfc : Continuous f := continuous_pi fun w => h3 _
  have := sigmaCompact_inf E (maximalRealSubfield E)
  have : IsModuleTopology (Ainf (maximalRealSubfield E))
    (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) := ⟨rfl⟩
  have : IsTopologicalRing (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
    IsModuleTopology.isTopologicalRing (Ainf (maximalRealSubfield E)) _
  have ho : IsOpenMap f := f.toAddMonoidHom.isOpenMap_of_sigmaCompact hf.2 hfc
  refine ⟨RingEquiv.ofBijective f hf, hfc, ?_, fun x w => (hθ _).1 x, fun z w => h4 _ z⟩
  exact ((RingEquiv.ofBijective f hf).toEquiv.toHomeomorphOfContinuousOpen hfc ho).symm.continuous

end Adeles

section Groups

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Groups

section Record

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} [IsCMField D.host.E] (V : HSp D)

omit [IsCMField D.host.E]

end Record

end GlobalTheory.AutQuotCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ShortGenIndepConnection
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortConnIndep

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R)
    (h : ∀ a : R, @star R s.toStarMul.toInvolutiveStar.toStar a = @star R t.toStarMul.toInvolutiveStar.toStar a) :
    s = t := by
  cases s with | @mk s1 _ =>
  cases t with | @mk t1 _ =>
  cases s1 with | @mk s2 _ =>
  cases t1 with | @mk t2 _ =>
  cases s2 with | @mk s3 _ =>
  cases t2 with | @mk t3 _ =>
  have : s3 = t3 := by
    cases s3; cases t3; congr; exact funext h
  subst this
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (N : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have hU := thExprUniq_of_chartIndep2 hC
  obtain ⟨M, hM, hMP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have key0 : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ G : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)),
      ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) *
          ∏ b, nab y K (G b) (colOf m b) =
        ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) *
          ∏ b, nab' y K (G b) (colOf m b) := by
    rintro K k rfl G
    exact hU E H Dw l Xo c nab nab' h h' S y k n G a _ hMP
  have key := key0 _ (N ^ 2) (Nat.cast_pow N 2).symm F
  rw [hsupp] at key
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, map_mul (algebraMap c.F S),
    _root_.mul_assoc, ← Finset.mul_sum] at key
  have hu : IsUnit (algebraMap c.F S (M : c.F)) :=
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hM.ne')).map _
  exact hu.mul_left_cancel key

theorem shortValAt_of (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S)
    (hv : ShortValAt Xo c nab w Λ β N P y v) : ShortValAt Xo c nab' w Λ β N P y v := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7.trans ?_⟩
  congr 1
  refine finsum_congr fun q => ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ => sum_eq hC nab nab' h h' y' a P hP N (F q i)

end GlobalTheory.ShortConnIndep

namespace GlobalTheory

theorem shortGen_indep_connection : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (nab : NabV Xo c) (bad nV : ℕ), (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (_ : StarRing (𝓞 E)) (nab' : NabV d.Xo₂ d.c₂), IsNab d.Xo₂ d.c₂ nab' → ∀ a, shortGen Xo c nab bad nV a n { d with nab₂ := nab' } = shortGen Xo c nab bad nV a n d := by
  intro hC E _ _ _ H Dw l Xo c n d nab bad nV ⟨s, hs⟩ t nab' ht a
  have hst : s = t := ShortConnIndep.starRing_eq s t fun x => (hs.1 x).trans (ht.1 x).symm
  subst hst
  have hmap : ∀ P : MvPolynomial (LtN Dw n) c.F,
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) →
      MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈
        HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
    intro P hP
    have hs : Function.Surjective (d.eF : c.F →+* d.c₂.F) :=
      fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
    generalize (d.eF : c.F →+* d.c₂.F) = f at hs ⊢
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨?_, ?_, ?_⟩
    · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
      intro τ hτ b b'
      have hlap : lap Dw.mult n d.c₂.F 1 τ _ b b' (MvPolynomial.map f P) =
          MvPolynomial.map f (lap Dw.mult n c.F 1 τ _ b b' P) := by
        simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
          Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
          MvPolynomial.pderiv_map]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        congr 2
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hlap, h1 τ hτ b b', map_zero]
    · intro σ i i' hi t
      obtain ⟨s, rfl⟩ := hs t
      have hshift : rowShift Dw.mult n d.c₂.F σ i i' (f s) (MvPolynomial.map f P) =
          MvPolynomial.map f (rowShift Dw.mult n c.F σ i i' s P) := by
        clear h1 h2 h3
        induction P using MvPolynomial.induction_on with
        | C x => simp [rowShift]
        | add p q hp hq =>
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_add (f := _), hp, hq]
        | mul_X p x hp =>
          simp only [map_mul, hp, MvPolynomial.map_X]
          congr 1
          simp only [rowShift, MvPolynomial.aeval_X]
          set_option synthInstance.maxHeartbeats 100000 in
            split_ifs <;> simp
      rw [hshift, h2 σ i i' hi s]
    · intro m hm
      exact h3 m (MvPolynomial.support_map_subset f P hm)
  refine Set.ext fun f => ⟨?_, ?_⟩
  · rintro ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩
    refine ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩
    intro k i1 i2 i3 i4 hk y y₂ hy
    obtain ⟨v, hv, he⟩ := @hr k i1 i2 i3 i4 hk y y₂ hy
    exact ⟨v, ShortConnIndep.shortValAt_of hC nab' d.nab₂ ht hs _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩
  · rintro ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩
    refine ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩
    intro k i1 i2 i3 i4 hk y y₂ hy
    obtain ⟨v, hv, he⟩ := @hr k i1 i2 i3 i4 hk y y₂ hy
    exact ⟨v, ShortConnIndep.shortValAt_of hC d.nab₂ nab' hs ht _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩

end GlobalTheory
end

