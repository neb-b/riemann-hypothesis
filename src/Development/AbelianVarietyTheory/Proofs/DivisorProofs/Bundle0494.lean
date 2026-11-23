module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0475
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWordLeIntegralOfAevalCasimirEqZeroStatement
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_derivWord_bound_of_aeval_casimir : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ K : Set G, IsCompact K ∧ ∀ l : List 𝔤, ∃ C : ℝ, ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ‖l.foldr h.rightDeriv (f : G → ℂ) 1‖ ≤ C * ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ := by
  first | exact @GlobalTheory.derivWord_le_integral_of_aeval_casimir_eq_zero | exact GlobalTheory.derivWord_le_integral_of_aeval_casimir_eq_zero | (intros; apply GlobalTheory.derivWord_le_integral_of_aeval_casimir_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnWirtWordMulExpCompStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_wirtWord_mul_exp_comp' : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by
  first | exact @GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp | exact GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp | (intros; apply GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationEquivOfSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem cechAug_eqv_of_section : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Y),
    s ≫ f = 𝟙 X → Eqv R (GlobalTheory.EtC.cechAug f) F := by
  intro R _ F Y X f s hs
  have hsec : yoneda.map s ≫ yoneda.map f = 𝟙 (yoneda.obj X) := by
    rw [← yoneda.map_comp, hs, yoneda.map_id]
  have hls : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f) :=
    (GlobalTheory.T.isLocallySurjective_etale_baseChange).2.1 _ _ (yoneda.map f) (yoneda.map s) hsec
  have hq := _root_.GlobalTheory.EtC.quasiIso_chains_cech_of_isLocallySurjective R (yoneda.obj Y) (yoneda.obj X) (yoneda.map f) hls
  exact ((GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.1 _ _ (GlobalTheory.EtC.cechAug f)) hq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_bijective_of_support_bijective : GlobalTheory.EtC.A10 := by
  first | (exact @GlobalTheory.EtC.a10) | (exact GlobalTheory.EtC.a10) | (intros; apply GlobalTheory.EtC.a10  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem bij_of_subsingleton_pair {A B : Type*} [Subsingleton A] [Subsingleton B] (_b₀ : B) (a₀ : A) (φ : A → B) :
    Function.Bijective φ :=
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨a₀, Subsingleton.elim _ _⟩⟩

theorem eqv_of_gen_lc : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g →
    ∀ (U V : Scheme.{0}) (s : U ⟶ S) (f : V ⟶ U), AcycF R (sch.obj U) F → AcycF R (sch.obj V) F →
    Function.Bijective (fun φ : LocallyConstant U R ↦ φ.comap f.base.hom) → Eqv R (sch.map f) F := by
  intro R _ F S g hg U V s f hU hV hb n
  obtain ⟨hneg, e, he, -⟩ := _root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero R F
  obtain ⟨eL, -, hE⟩ := _root_.GlobalTheory.EtC.gen_locallyConstant R F S g hg
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := hneg (sch.obj U) n hn
    have := hneg (sch.obj V) n hn
    exact bij_of_subsingleton_pair 0 0 _
  · have key : (fun x ↦ pull R (sch.map f) F 0 x) =
        (fun x ↦ e V (eL V (f ≫ s) (LocallyConstant.comap f.base.hom ((eL U s).symm ((e U).symm x))))) := by
      funext x
      conv_lhs => rw [← (e U).apply_symm_apply x, ← (eL U s).apply_symm_apply ((e U).symm x)]
      rw [he, hE]
    change Function.Bijective (fun x ↦ pull R (sch.map f) F 0 x)
    rw [key]
    exact (e V).bijective.comp ((eL V (f ≫ s)).bijective.comp
      (hb.comp ((eL U s).symm.bijective.comp (e U).symm.bijective)))
  · have := hU n hn
    have := hV n hn
    exact bij_of_subsingleton_pair 0 0 _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureOfIsArtinianRing
section
open IsLocalRing

namespace GlobalTheory.PurityProd

theorem etale_of_etale_atMaximal {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (h : Algebra.Etale (Localization.AtPrime (maximalIdeal A))
      (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B)) :
    Algebra.Etale A B := by
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x hx => by
      simpa [IsUnit.mem_submonoid_iff] using IsLocalRing.notMem_maximalIdeal.mp hx)
  haveI : Algebra.Etale A (Localization.AtPrime (maximalIdeal A)) := Algebra.Etale.of_equiv e
  haveI : Algebra.Etale A (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B) :=
    Algebra.Etale.comp A (Localization.AtPrime (maximalIdeal A)) _
  let f : TensorProduct A (Localization.AtPrime (maximalIdeal A)) B ≃ₐ[A] B :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid A B)
  exact Algebra.Etale.of_equiv f

theorem isIntegral_of_forall_apply {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

theorem etale_of_etale_pi {R : Type} [CommRing R] [IsNoetherianRing R] {ι : Type} [Finite ι]
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)] [∀ i, Module.Finite R (C i)]
    (h : Algebra.Etale R (∀ i, C i)) (i : ι) : Algebra.Etale R (C i) :=
  ⟨(Algebra.FormallyEtale.pi_iff C).mp inferInstance i,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end GlobalTheory.PurityProd

namespace GlobalTheory.PurityProd

theorem etale_integralClosure_of_isArtinianRing : ∀ (A E : Type) [CommRing A] [IsRegularLocalRing A]
    [CommRing E] [Algebra A E], IsReduced E → IsArtinianRing E → NoZeroSMulDivisors A E →
    Module.Finite A (integralClosure A E) →
    (∀ (q : Ideal A) [q.IsPrime], q.height ≤ 1 → Algebra.Etale (Localization.AtPrime q)
      (TensorProduct A (Localization.AtPrime q) (integralClosure A E))) →
    Algebra.Etale A (integralClosure A E) := by
  intro A E _ _ _ _ hred hart hnz hfin hq
  classical
  by_cases hm : (maximalIdeal A).height ≤ 1
  · exact etale_of_etale_atMaximal (hq (maximalIdeal A) hm)
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A
  haveI := hdom
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  letI (I : MaximalSpectrum E) : Field (E ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  let F : MaximalSpectrum E → Type := fun I => E ⧸ I.asIdeal
  let ψ : E ≃ₐ[A] (∀ I, F I) := (IsArtinianRing.equivPi E).restrictScalars A
  let C : MaximalSpectrum E → Type := fun I => integralClosure A (F I)
  let Ψ : integralClosure A E →ₐ[A] ∀ I, C I := AlgHom.pi fun I =>
    ((Pi.evalAlgHom A F I).comp (ψ.toAlgHom.comp (integralClosure A E).val)).codRestrict
      (integralClosure A (F I)) fun x => x.2.map ((Pi.evalAlgHom A F I).comp ψ.toAlgHom)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply ψ.injective
      funext I
      exact congrArg Subtype.val (congrFun hxy I)
    · intro l
      refine ⟨⟨ψ.symm fun I => (l I).1, ?_⟩, ?_⟩
      · exact (isIntegral_of_forall_apply (fun I => ((l I : F I))) fun I => (l I).2).map
          ψ.symm.toAlgHom
      · funext I
        apply Subtype.ext
        change ψ (ψ.symm fun I => (l I).1) I = (l I).1
        rw [AlgEquiv.apply_symm_apply]
  let Φ : integralClosure A E ≃ₐ[A] ∀ I, C I := AlgEquiv.ofBijective Ψ hΨ
  have hinjF : ∀ I, Function.Injective (algebraMap A (F I)) := by
    intro I
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hne : ψ.symm (Pi.single I 1) ≠ 0 := by
      intro h0
      have := congrArg ψ h0
      rw [AlgEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero (by simpa using congrFun this I : (1 : F I) = 0)
    have h0 : a • ψ.symm (Pi.single I 1) = 0 := by
      apply ψ.injective
      rw [map_smul, AlgEquiv.apply_symm_apply, map_zero]
      funext J
      by_cases hJ : J = I
      · subst hJ; simp [Algebra.smul_def, ha]
      · simp [hJ]
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hne
  haveI hfaith : ∀ I, FaithfulSMul A (C I) := fun I => by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    apply hinjF I
    exact congrArg Subtype.val hab
  haveI hfC : ∀ I, FaithfulSMul (C I) (F I) := fun I =>
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI hintC : ∀ I, IsIntegrallyClosed (C I) := fun I =>
    IsIntegrallyClosed.of_isIntegrallyClosedIn (C I) (F I)
  haveI hfinC : ∀ I, Module.Finite A (C I) := fun I =>
    Module.Finite.of_surjective ((Pi.evalAlgHom A C I).toLinearMap.comp Φ.toLinearMap) (by
      intro c
      obtain ⟨x, hx⟩ := Φ.surjective (Pi.single I c)
      exact ⟨x, by simp [hx]⟩)
  haveI : ∀ I, Algebra.Etale A (C I) := by
    intro I
    have key := _root_.GlobalTheory.BranchPurity.etale_of_etale_height_one A (C I)
    refine key ?_ ?_ ?_ ?_
    · exact IsRegularLocalRing.spanFinrank_maximalIdeal
    · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast (le_of_lt (not_le.mp hm))
    · intro hf
      apply hm
      rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp hf, Ideal.height_bot]
      exact zero_le_one
    · intro p _ hp
      have h1 := hq p (le_of_eq hp)
      let G : TensorProduct A (Localization.AtPrime p) (integralClosure A E) ≃ₐ[Localization.AtPrime p]
          ∀ J, TensorProduct A (Localization.AtPrime p) (C J) :=
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans
          (Algebra.TensorProduct.piRight A (Localization.AtPrime p) (Localization.AtPrime p) C)
      haveI : Algebra.Etale (Localization.AtPrime p)
          (∀ J, TensorProduct A (Localization.AtPrime p) (C J)) := Algebra.Etale.of_equiv G
      exact etale_of_etale_pi (fun J => TensorProduct A (Localization.AtPrime p) (C J)) this I
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocycles
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCZero

noncomputable def clHom (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    Cocycle ((chains R).obj E) (res R F) 0 →+ H R E F 0 :=
  AddMonoidHom.mk' (fun c => CohomologyClass.mk c) (fun a b => CohomologyClass.mk_add a b)

theorem cochain_neg_one_eq_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (β : Cochain ((chains R).obj E) (res R F) (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · exact (GlobalTheory.EtC.HCElements.chains_X_isZero R E p hp).eq_of_src _ _
  · exact (GlobalTheory.EtC.HCElements.res_X_isZero R F q (by omega)).eq_of_tgt _ _

theorem clHom_bijective (R : Type) [CommRing R] (F : Shv R) (E : Spc) : Function.Bijective (clHom R F E) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : CohomologyClass.mk (a - b) = 0 := by
      rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 hab
    rw [CohomologyClass.mk_eq_zero_iff] at h0
    obtain ⟨m, hm, β, hβ⟩ := h0
    obtain rfl : m = -1 := by omega
    rw [cochain_neg_one_eq_zero R F E β, δ_zero] at hβ
    rw [← sub_eq_zero]
    exact Cocycle.ext (by simpa using hβ.symm)
  · obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c, rfl⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  intro R _ F
  obtain ⟨-, e, he, -⟩ := _root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero R F
  let cE : ∀ X : Scheme.{0}, Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 ≃+ H R (sch.obj X) F 0 :=
    fun X => AddEquiv.ofBijective (clHom R F (sch.obj X)) (clHom_bijective R F (sch.obj X))
  let φ : ∀ X : Scheme.{0}, Sec F X →+ Cochain ((chains R).obj (sch.obj X)) (res R F) 0 :=
    fun X => (AddMonoidHom.mk' (fun c : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 => c.1) (fun _ _ => rfl)).comp
      ((cE X).symm.toAddMonoidHom.comp (e X).toAddMonoidHom)
  have hφ : ∀ X s, φ X s = ((cE X).symm (e X s)).1 := fun _ _ => rfl
  refine ⟨{ app := fun U => AddCommGrpCat.ofHom (φ U.unop), naturality := ?_ }, fun U => ⟨?_, fun z => ⟨?_, ?_⟩⟩⟩
  · intro U V f
    ext x
    change φ V.unop ((F.obj.map f).hom x) = ((HC R F).map (sch.map f.unop).op).f 0 (φ U.unop x)
    set c := (cE U.unop).symm (e U.unop x) with hc
    have key : (cE V.unop) (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) =
        e V.unop ((F.obj.map f).hom x) := by
      have h1 := he f.unop x
      have h2 : pull R (sch.map f.unop) F 0 (cE U.unop c) =
          CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) := rfl
      rw [hc, AddEquiv.apply_symm_apply] at h2
      rw [h2] at h1
      exact h1
    rw [hφ, hφ, ← key, AddEquiv.symm_apply_apply]
    rfl
  · intro a b hab
    change φ U.unop a = φ U.unop b at hab
    rw [hφ, hφ] at hab
    exact (e U.unop).injective ((cE U.unop).symm.injective (Subtype.ext hab))
  · intro hz
    refine ⟨(e U.unop).symm (cE U.unop (Cocycle.mk z (0 + 1) rfl hz)), ?_⟩
    change φ U.unop _ = z
    rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, rfl⟩
    change δ 0 (0 + 1) (φ U.unop x) = 0
    rw [hφ]
    exact ((cE U.unop).symm (e U.unop x)).2

end GlobalTheory.EtC.HCZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EveryElementIsNorm
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_element_is_norm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  first | (exact @GlobalTheory.Shin.exists_isNorm) | (exact GlobalTheory.Shin.exists_isNorm) | (intros; apply GlobalTheory.Shin.exists_isNorm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsElementPosImUnderCmTypeStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_element_pos_im_under_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  first | exact @GlobalTheory.CMTypeImPos.exists_im_pos | exact GlobalTheory.CMTypeImPos.exists_im_pos | (intros; apply GlobalTheory.CMTypeImPos.exists_im_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOneStatement
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_end_lattice_trace_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → SelfDualLat G Λ → ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_endLat_trace_eq_one | exact GlobalTheory.LieDisc.exists_endLat_trace_eq_one | (intros; apply GlobalTheory.LieDisc.exists_endLat_trace_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsMaxRealSubfieldStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeRealEmb.exists_equiv | exact GlobalTheory.CMTypeRealEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeRealEmb.exists_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAdditiveFnPDivGroup
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem exists_res_eq_of_transl_eq_add {b : G.A 1} (hb : cobOne R (G.A 1) b = 0) (n : ℕ)
    (x : G.A (n + 1)) (hx : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ∃ y : G.A (n + 2), G.transl (n + 1) y = y ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b ∧ G.res (n + 1) y = x := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.transl_coaction_free_coassoc_counital G (n + 1)
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_coaction_eq_add_of_primitive (G.transl (n + 1)) h1 h2 h3 b hb
  have hr : G.transl n (G.res (n + 1) x') = G.res (n + 1) x' ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    rw [transl_res, hx', map_add (f := _), LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    simp
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_mulP_eq_of_transl_invariant G n (G.res (n + 1) x' - x) (by
    rw [map_sub, hr, hx, sub_tmul]
    abel)
  obtain ⟨e', rfl⟩ := G.res_surjective n e
  refine ⟨x' - G.mulP (n + 1) e', ?_, ?_⟩
  · rw [map_sub, hx', transl_mulP, sub_tmul]
    abel
  · rw [map_sub, res_mulP, ← mulP_res, he, sub_sub_cancel]

theorem exists_funs_transl_eq_add {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (b : G.A 1) (hb : cobOne R (G.A 1) b = 0) :
    ∃ B : G.funs, B.1 1 = b ∧
      ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  choose f hf hres using G.exists_res_eq_of_transl_eq_add hb
  have h0 : G.transl 0 b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    have h : (G.resOne 0 : G.A 1 →ₗ[R] G.A 1) = LinearMap.id := by
      apply LinearMap.ext
      intro a
      simp only [BialgHom.coe_toLinearMap, LinearMap.id_apply, resOne_zero]
    rw [transl_apply, h, LinearMap.lTensor_id, LinearMap.id_apply]
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb
    exact hb
  let s : ∀ n, {x : G.A (n + 1) // G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b} := fun n =>
    Nat.rec (motive := fun n => {x : G.A (n + 1) // G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b})
      ⟨b, h0⟩ (fun n x => ⟨f n x.1 x.2, hf n x.1 x.2⟩) n
  refine ⟨⟨fun n => Nat.casesOn (motive := fun n => G.A n) n (G.res 0 b) fun n => (s n).1, ?_⟩,
    rfl, fun n => (s n).2⟩
  rintro (_ | n)
  · rfl
  · exact hres n (s n).1 (s n).2

end PDivGroup

end GlobalTheory
end

