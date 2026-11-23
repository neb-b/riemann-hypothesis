module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNonemptyCrystallineTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UPoinc.UCTraitEx

theorem injective_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K] [CharZero K]
    (ψ : o →+* K) : Function.Injective ψ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hbot : RingHom.ker ψ ≠ ⊥ := fun h => ha0 (by
    have h' : a ∈ RingHom.ker ψ := ha
    rwa [h, Ideal.mem_bot] at h')
  haveI hmax : (RingHom.ker ψ).IsMaximal := hP.isMaximal hbot
  haveI := GlobalTheory.finite_quotient_of_finiteType_int (RingHom.ker ψ)
  haveI : CharZero (o ⧸ RingHom.ker ψ) := (RingHom.charZero_iff (RingHom.kerLift_injective ψ)).2 inferInstance
  exact not_finite (o ⧸ RingHom.ker ψ)

theorem exists_lift_genericFibre {o F K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F]
    (b : o →+* F) (hb : letI := b.toAlgebra; IsFractionRing o F) [Field K] [CharZero K] {Z : Scheme.{0}} (z : Z ⟶ Sp o)
    (x : Sp K ⟶ Z) : ∃ x' : Sp K ⟶ pullback z (spMap b), x' ≫ pullback.fst _ _ = x := by
  letI := b.toAlgebra
  haveI := hb
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ z)
  have hinj := injective_of_charZero ψ.hom
  let ψ' : F →+* K := IsFractionRing.lift hinj
  have hc : ψ'.comp b = ψ.hom := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  have e : x ≫ z = spMap ψ' ≫ spMap b := by
    rw [GlobalTheory.Poinc.GCTrait.spMap_comp'', hc, ← hψ]; rfl
  exact ⟨pullback.lift x (spMap ψ') e, pullback.lift_fst _ _ _⟩

theorem exists_finite_point_rat {X : Scheme.{0}} (s : X ⟶ Sp ℚ) [LocallyOfFiniteType s] (p : ℕ) [Fact p.Prime]
    (y : Sp (PadicAlgCl p) ⟶ X) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (x : Sp K ⟶ X),
      spMap (algebraMap K (PadicAlgCl p)) ≫ x = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  letI := a.hom.toAlgebra
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := ℚ) (A := Γ(X, U)) (self := hft)
  let S : Set (PadicAlgCl p) := φ.hom '' (T : Set Γ(X, U))
  have hSfin : S.Finite := T.finite_toSet.image _
  haveI : Finite S := hSfin.to_subtype
  let K := IntermediateField.adjoin ℚ_[p] S
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hS : S ⊆ K := IntermediateField.subset_adjoin ℚ_[p] S
  have hc : ∀ c : ℚ, φ.hom (a.hom c) ∈ K := fun c => by
    rw [show φ.hom (a.hom c) = (φ.hom.comp a.hom) c from rfl, eq_ratCast]
    exact SubfieldClass.ratCast_mem K c
  have hmem : ∀ b, φ.hom b ∈ K := fun b => by
    have hb : b ∈ Algebra.adjoin ℚ (T : Set Γ(X, U)) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS ⟨x, hx, rfl⟩
    | algebraMap c => exact hc c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  let φK : Γ(X, U) →+* K := φ.hom.codRestrict K hmem
  refine ⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩
  rw [← Category.assoc, GlobalTheory.Poinc.GCTrait.spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]
  rfl

theorem exists_uCTrait_of_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime], ∃ U : X.M.Z.Opens, (U : Set X.M.Z).Nonempty ∧ ∀ y : Sp (OO p) ⟶ X.M.Z, Set.range (gPt p ≫ y) ⊆ U → ∃ ct : UCTrait X p (y (cPt p)), ct.y = y := by
  intro E _ _ _ H Dw _ l Xo cf C X p _
  haveI := C.iF_open
  haveI := C.ded
  haveI := C.ft
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb : Topology.IsEmbedding (pullback.fst C.z (spMap C.b)) := Scheme.Hom.isEmbedding _
  let S : Set C.Z := pullback.fst C.z (spMap C.b) '' (Set.range C.iF)ᶜ
  have hS : pullback.fst C.z (spMap C.b) ⁻¹' closure S = (Set.range C.iF)ᶜ := by
    rw [← hemb.isInducing.closure_eq_preimage_closure_image]
    exact C.iF.isOpenEmbedding.isOpen_range.isClosed_compl.closure_eq
  let V : C.Z.Opens := ⟨(closure S)ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨X.π ⁻¹ᵁ V, ?_, ?_⟩
  · let w : Sp X.Ω₁ := IsLocalRing.closedPoint X.Ω₁
    refine ⟨X.M.pt w, ?_⟩
    have e : X.π (X.M.pt w) =
        pullback.fst C.z (spMap C.b) (C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w)) := by
      rw [← Scheme.Hom.comp_apply, X.comp]
      simp only [UCompact.i, Scheme.Hom.comp_apply]
    show X.π (X.M.pt w) ∈ (closure S)ᶜ
    rw [e]
    intro hc
    have h' : C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w) ∈ (Set.range C.iF)ᶜ := hS ▸ hc
    exact h' ⟨_, rfl⟩
  · intro y hr
    obtain ⟨x', hx'⟩ := exists_lift_genericFibre C.b C.isFractionRing C.z (gPt p ≫ y ≫ X.π)
    have hr' : Set.range x' ⊆ Set.range C.iF := by
      rintro _ ⟨w, rfl⟩
      by_contra hn
      have h1 : pullback.fst C.z (spMap C.b) (x' w) ∈ closure S := subset_closure ⟨_, hn, rfl⟩
      have h2 : (gPt p ≫ y) w ∈ X.π ⁻¹ᵁ V := hr ⟨w, rfl⟩
      have h3 : pullback.fst C.z (spMap C.b) (x' w) = X.π ((gPt p ≫ y) w) := by
        rw [← Scheme.Hom.comp_apply, hx']
        simp only [Scheme.Hom.comp_apply]
      exact h2 (h3 ▸ h1)
    let y₁ : Sp (PadicAlgCl p) ⟶ Xo.XF cf := IsOpenImmersion.lift C.iF x' hr'
    have hy₁ : y₁ ≫ C.i = gPt p ≫ y ≫ X.π := by
      show y₁ ≫ C.iF ≫ pullback.fst _ _ = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hx']
    haveI := cf.fin
    haveI := Xo.smooth
    haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
    haveI : LocallyOfFiniteType (spMap (algebraMap ℚ cf.F)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
    obtain ⟨K, hK, x, hx⟩ := exists_finite_point_rat (pullback.snd _ _ ≫ spMap (algebraMap ℚ cf.F)) p y₁
    obtain ⟨hdvr, hcomp, hunit⟩ := GlobalTheory.intRing_complete_dvr p K hK
    haveI := hdvr
    haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance
    let e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K := FractionRing.algEquiv _ K
    let es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := e.symm.toRingEquiv.toRingHom
    have hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) :=
      ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
    obtain ⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩ :=
      GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo cf _ hbase hdvr (spMap es ≫ x)
    haveI : IsDiscreteValuationRing T.V := T.cdvr.1
    obtain ⟨ι, hι, hint⟩ := GlobalTheory.Poinc.GCTrait.exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit
    have h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) =
        (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
      refine (IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_
      show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))
      rw [AlgEquiv.commutes]
      rfl
    have hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es =
        algebraMap K (PadicAlgCl p) := by
      ext k
      rw [h2]
      show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _
      rw [AlgEquiv.apply_symm_apply]
    have key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p)) := by
      rw [GlobalTheory.Poinc.GCTrait.spMap_comp'', GlobalTheory.Poinc.GCTrait.spMap_comp'', ← RingHom.comp_assoc, hι, hκ]
    refine ⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩
    calc gPt p ≫ y ≫ X.π = y₁ ≫ C.i := hy₁.symm
      _ = (spMap (algebraMap K (PadicAlgCl p)) ≫ x) ≫ C.i := by rw [hx]
      _ = ((spMap ι ≫ spMap fK ≫ spMap es) ≫ x) ≫ C.i := by rw [key]
      _ = spMap ι ≫ T.y ≫ C.i := by rw [hTy]; simp only [Category.assoc]

end GlobalTheory.UPoinc.UCTraitEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeIsotropicPair
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.Opp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem proj_quot_of_sat {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) (h : ∀ a : R, a ≠ 0 → ∀ y : M, a • y ∈ N → y ∈ N) :
    Module.Projective R (M ⧸ N) := by
  have htor : Submodule.torsion R (M ⧸ N) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact h a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat R (M ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation R (M ⧸ N) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem exists_ef_eq (D : Datum H) (ψ : D.La →+ ℤ) : ∃ y : D.La, ∀ x, D.EF y x = ψ x := by
  obtain ⟨y, hy⟩ := D.unimod.2 ψ.toIntLinearMap
  exact ⟨y, fun x => by rw [hy]; rfl⟩

theorem fin_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

variable {D : Datum H} {Z : Submodule (𝓞 E) D.La}

theorem sat_int (hZ : IsIsoSat D Z) (n : ℤ) (hn : n ≠ 0) (y : D.La) (hy : n • y ∈ Z) : y ∈ Z := by
  refine hZ.2 n.natAbs y (by omega) ?_
  rcases Int.natAbs_eq n with h1 | h1
  · rw [← natCast_zsmul, ← h1]; exact hy
  · have : ((n.natAbs : ℤ)) • y = -(n • y) := by rw [h1]; simp
    rw [← natCast_zsmul, this]; exact Z.neg_mem hy

theorem proj_int (hZ : IsIsoSat D Z) : Module.Projective ℤ (D.La ⧸ Z.restrictScalars ℤ) := by
  haveI := fin_int D
  exact proj_quot_of_sat _ fun a ha y hy => sat_int hZ a ha y hy

theorem exists_ext (hZ : IsIsoSat D Z) (φ : Z →+ ℤ) : ∃ y : D.La, ∀ z : Z, D.EF z y = φ z := by
  haveI := proj_int hZ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (Z.restrictScalars ℤ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ x : D.La, x - σ ((Z.restrictScalars ℤ).mkQ x) ∈ Z := fun x => by
    have : (Z.restrictScalars ℤ).mkQ (x - σ ((Z.restrictScalars ℤ).mkQ x)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  obtain ⟨y, hy⟩ := exists_ef_eq D (AddMonoidHom.mk' (fun x => φ ⟨_, hmem x⟩) fun x x' => by
    rw [← map_add (f := _)]; congr 1; ext; simp only [map_add (f := _), Submodule.coe_add]; abel)
  refine ⟨-y, fun z => ?_⟩
  have h0 : (Z.restrictScalars ℤ).mkQ (z : D.La) = 0 := (Submodule.Quotient.mk_eq_zero _).2 z.2
  rw [map_neg, ef_swap, neg_neg, hy]
  simp only [AddMonoidHom.mk'_apply, h0, map_zero, sub_zero]

theorem mem_of_perp_perp (hZ : IsIsoSat D Z) (y : D.La) (hy : ∀ p ∈ perp D Z, D.EF y p = 0) : y ∈ Z := by
  haveI := proj_int hZ
  by_contra hyZ
  have hu : (Z.restrictScalars ℤ).mkQ y ≠ 0 := fun h => hyZ ((Submodule.Quotient.mk_eq_zero _).1 h)
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual ℤ (D.La ⧸ Z.restrictScalars ℤ), χ ((Z.restrictScalars ℤ).mkQ y) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu ((Module.forall_dual_apply_eq_zero_iff ℤ _).1 hc)
  obtain ⟨p, hp⟩ := exists_ef_eq D (χ.comp (Z.restrictScalars ℤ).mkQ).toAddMonoidHom
  have hpZ : p ∈ perp D Z := fun z hz => by
    have h0 : (Z.restrictScalars ℤ).mkQ z = 0 := (Submodule.Quotient.mk_eq_zero _).2 hz
    rw [hp, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, h0, map_zero]
  have := hy p hpZ
  rw [ef_swap, hp, neg_eq_zero] at this
  exact hχ this

theorem perp_sat (D : Datum H) (Z : Submodule (𝓞 E) D.La) (a : 𝓞 E) (ha : a ≠ 0) (y : D.La) (hy : a • y ∈ perp D Z) :
    y ∈ perp D Z := by
  have hne : (Ideal.span {a}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
  intro z hz
  have h := (perp D Z).smul_mem a' hy z hz
  rw [smul_smul, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply,
    smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hn0

theorem exists_opp (D : Datum H) (Z : Submodule (𝓞 E) D.La) (hZ : IsIsoSat D Z) : ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' := by
  haveI := D.fin
  haveI : Module.Projective (𝓞 E) (D.La ⧸ perp D Z) := proj_quot_of_sat _ (perp_sat D Z)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (perp D Z).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  have hsx : ∀ q, (perp D Z).mkQ (s q) = q := fun q => by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  set C := LinearMap.range s with hC
  have hdec : ∀ x : D.La, x - s ((perp D Z).mkQ x) ∈ perp D Z := fun x =>
    (Submodule.Quotient.mk_eq_zero _).1 (by rw [← Submodule.mkQ_apply, map_sub, hsx, sub_self])
  have hC0 : ∀ c ∈ C, c ∈ perp D Z → c = 0 := by
    rintro _ ⟨q, rfl⟩ h
    have : q = 0 := by rw [← hsx q]; exact (Submodule.Quotient.mk_eq_zero _).2 h
    rw [this, map_zero]
  have hsC : ∀ c ∈ C, s ((perp D Z).mkQ c) = c := by
    rintro _ ⟨q, rfl⟩; rw [hsx]
  have hZx : ∀ (z : D.La), z ∈ Z → ∀ x, D.EF z x = D.EF z (s ((perp D Z).mkQ x)) := fun z hz x => by
    have := hdec x z hz
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [ef_swap, this, ← ef_swap]
  have A1 : ∀ φ : Z →+ ℤ, ∃! b : C, ∀ a : Z, D.EF a b = φ a := by
    intro φ
    obtain ⟨y, hy⟩ := exists_ext hZ φ
    refine ⟨⟨s ((perp D Z).mkQ y), _, rfl⟩, fun a => (hZx a a.2 y).symm.trans (hy a), fun b hb => Subtype.ext ?_⟩
    have h1 : (b : D.La) - s ((perp D Z).mkQ y) ∈ perp D Z := fun z hz => by
      rw [ef_swap, map_sub, hb ⟨z, hz⟩, ← hZx z hz, hy ⟨z, hz⟩, sub_self, neg_zero]
    exact sub_eq_zero.1 (hC0 _ (sub_mem b.2 ⟨_, rfl⟩) h1)

  have A2 : ∀ φ : C →+ ℤ, ∃! z : Z, ∀ c : C, D.EF c z = φ c := by
    intro φ
    have hmC : ∀ x : D.La, s ((perp D Z).mkQ x) ∈ C := fun x => ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := exists_ef_eq D (AddMonoidHom.mk' (fun x => φ ⟨_, hmC x⟩) fun x x' => by
      rw [← map_add (f := _)]; congr 1; ext; simp only [map_add (f := _), Submodule.coe_add])
    simp only [AddMonoidHom.mk'_apply] at hy
    have hyZ : -y ∈ Z := mem_of_perp_perp hZ _ fun p hp => by
      have h0 : (perp D Z).mkQ p = 0 := (Submodule.Quotient.mk_eq_zero _).2 hp
      rw [map_neg, LinearMap.neg_apply, hy]
      have : (⟨s ((perp D Z).mkQ p), hmC p⟩ : C) = 0 := Subtype.ext (by show s ((perp D Z).mkQ p) = 0; rw [h0, map_zero])
      rw [this, map_zero, neg_zero]
    have key : ∀ c : C, D.EF c (-y) = φ c := fun c => by
      rw [ef_swap, map_neg, LinearMap.neg_apply, neg_neg, hy]
      congr 1; exact Subtype.ext (hsC c c.2)
    refine ⟨⟨-y, hyZ⟩, key, fun z hz => Subtype.ext ?_⟩
    have hw : ∀ x, D.EF ((z : D.La) - -y) x = 0 := fun x => by
      have h1 := hz ⟨_, hmC x⟩
      have h2 := key ⟨_, hmC x⟩
      rw [hZx _ (sub_mem z.2 hyZ), ef_swap, map_sub]
      rw [h1, h2, sub_self, neg_zero]
    exact sub_eq_zero.1 (D.unimod.1 (LinearMap.ext fun x => by rw [hw, map_zero, LinearMap.zero_apply]))
  let β : LinearMap.BilinForm ℤ C := LinearMap.mk₂ ℤ (fun a b : C => -D.EF a b)
    (fun a a' b => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]; abel) (fun n a b => by simp) (fun a b b' => by simp only [Submodule.coe_add, map_add (f := _)]; abel) (fun n a b => by simp)
  obtain ⟨t, ht⟩ := exists_skew_solve A2 β (fun a b => by
      show -D.EF a b = -(-D.EF b a)
      rw [ef_swap D a b]) (fun c a b => by
      show -D.EF ((c • a : C) : D.La) b = -D.EF a ((H.bar c • b : C) : D.La)
      rw [Submodule.coe_smul, Submodule.coe_smul, D.adj])
  have ht' : ∀ a b : C, D.EF a (t b) + D.EF (t a) b = -D.EF a b := ht
  let g : C →ₗ[𝓞 E] D.La := C.subtype + Z.subtype ∘ₗ t
  have hg : ∀ c, g c = c + t c := fun c => rfl
  have kZ : ∀ (a : Z) (c : C), D.EF a (g c) = D.EF a c := fun a c => by
    rw [hg, map_add (f := _), hZ.1 a.2 _ (t c).2, add_zero]
  refine ⟨LinearMap.range g, hZ.1, ?_, fun φ => ?_, fun φ => ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    show D.EF (g b) (g b') = 0
    have h0 : D.EF (t b) (t b') = 0 := hZ.1 (t b).2 _ (t b').2
    rw [hg, hg]
    simp only [map_add (f := _), LinearMap.add_apply]
    linear_combination ht' b b' + h0
  · obtain ⟨b, hb, hu⟩ := A1 φ
    refine ⟨⟨g b, b, rfl⟩, fun a => (kZ a b).trans (hb a), ?_⟩
    rintro ⟨_, b', rfl⟩ hb'
    exact Subtype.ext (congrArg g (hu b' fun a => (kZ a b').symm.trans (hb' a)))
  · obtain ⟨a, ha, hu⟩ := A2 (-(φ.comp g.rangeRestrict.toAddMonoidHom))
    refine ⟨a, ?_, fun a' ha' => hu a' fun c => ?_⟩
    · rintro ⟨_, c, rfl⟩
      show D.EF a (g c) = φ ⟨g c, c, rfl⟩
      rw [kZ, ef_swap, ha c, AddMonoidHom.neg_apply, neg_neg]
      rfl
    · have h1 := ha' ⟨g c, c, rfl⟩
      rw [ef_swap, ← kZ a' c]
      show -D.EF a' (g c) = -φ ⟨g c, c, rfl⟩
      rw [← h1]

end GlobalTheory.LowFilt.Opp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_ratio_of_exp_one_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  intro R _ _ _ hB D C k hk G S Ψ hΨ W₀ _ _ _ T₀ a₀ b₀ ha hb hS
  obtain ⟨u₀, hu₀⟩ := hΨ W₀ T₀
  have hp := _root_.GlobalTheory.Mum.Trait.exp_pair R hB D C W₀ T₀ k hk G S Ψ a₀ b₀ 1 (u₀ : W₀) hS hu₀
  obtain ⟨r, t, hr, ht, hrt⟩ := _root_.GlobalTheory.Mum.secK_ratio_descends R hB D C W₀ T₀ k S Ψ ((u₀ : W₀) * a₀) (b₀ * 1)
    (mul_ne_zero u₀.ne_zero ha) (by rw [_root_.mul_one]; exact hb) hp
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨u, hu⟩ := hΨ W T
  exact ⟨u, _root_.GlobalTheory.Mum.Trait.exp_transfer R D C W T k G S Ψ r t (u : W) hrt hu⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbelia
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oLinear_of_oAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O), ∃ (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o
  have hgen : IsMonHom U.gen.hom := U.gen_hom
  have hgeni : IsMonHom U.gen.inv := by infer_instance
  have L1 : ∀ a : O, ∃ g : G ⟶ G, IsMonHom g ∧ ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
    intro a
    obtain ⟨f, hf, hfA⟩ := _root_.GlobalTheory.Mum.GenericEnd.main R hR D A G hG U O o a
    obtain ⟨g, hg, hgf⟩ := _root_.GlobalTheory.Mum.genericEnd_extends R hR G hG (U.gen.hom ≫ f ≫ U.gen.inv) inferInstance
    refine ⟨g, hg, hfA g hg ?_⟩
    rw [hgf]; simp
  have L2 := _root_.GlobalTheory.Mum.actsAs_unique R hR D A G hG U
  choose g hg hgA using L1
  have one : g 1 = 𝟙 G := by
    refine L2 _ _ _ _ (hg 1) inferInstance (hgA 1) ?_
    have := actsAs_id U.toUnifPre
    rw [o.onB.map_one]
    convert this using 1
    funext χ; simp
  have mul : ∀ a b : O, g (a * b) = g b ≫ g a := by
    intro a b
    haveI := hg a; haveI := hg b
    refine L2 _ _ _ _ (hg (a * b)) inferInstance (hgA (a * b)) ?_
    have := actsAs_comp U.toUnifPre (hgA b) (hgA a)
    rw [o.onB.map_mul]
    convert this using 1
    funext χ; simp [star_mul, mul_smul]
  have add : ∀ a b : O, g (a + b) = padd G (g a) (g b) := by
    intro a b
    haveI := hg a; haveI := hg b
    have hp : IsMonHom (padd G (g a) (g b)) := by unfold padd; infer_instance
    refine L2 _ _ _ _ (hg (a + b)) hp (hgA (a + b)) ?_
    have := actsAs_padd U.toUnifPre (hgA a) (hgA b)
    rw [o.onB.map_add]
    convert this using 1
    funext χ; simp [star_add, add_smul]
  let oG : RingAct G O := { act := g, hom := hg, map_one := one, map_mul := mul, map_add := add }
  let F := Over.pullback (jK R)
  let fA : O → (A.A ⟶ A.A) := fun a => U.gen.inv ≫ F.map (g a) ≫ U.gen.hom
  let oA : A.OAct O :=
    { act := fA
      hom := fun a => by haveI := hg a; dsimp [fA]; infer_instance
      map_one := by simp [fA, F, one]
      map_mul := fun a b => by simp [fA, F, mul]
      map_add := fun a b => by
        simp only [fA, F, add, pull_padd]
        rw [padd_comp_hom, padd, padd, comp_lift_assoc]
      rosati := fun a => _root_.GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs R hR D A G hG U O o a (g a) (g (star a)) (hg a) (hg (star a)) (hgA a) (hgA (star a)) }
  refine ⟨oA, oG, ⟨fun a => ?_, fun e a => (hgA a e).1, fun e a => (hgA a e).2⟩⟩
  simp [oA, oG, fA, F]
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantDerivationLiftsRaynaudCover
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.HeatInvLift.exists_invLift_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (D : Derivation ℤ R R), ∃ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧ ∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y D
  let J := {p : Dd.toPre.P.A.left.affineOpens × Dd.toPre.P.L.ι // p.1.1 ≤ Dd.toPre.P.L.U p.2}
  have H := fun i : J => _root_.GlobalTheory.Heat.HxLift.exists_invLift R Dd.toPre O oa Y i.1.1 D
  choose d hd using H
  refine ⟨J, fun i => i.1.1.1, fun i => i.1.2, d, ?_, fun i => i.2, fun i => (hd i).1, fun i α V' hV' f hf => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⨆ k, Dd.toPre.P.L.U k) := by rw [Dd.toPre.P.isLB.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVk⟩ :=
      Dd.toPre.P.A.left.isBasis_affineOpens.exists_subset_of_mem_open hk (Dd.toPre.P.L.U k).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, k), hVk⟩, hxV⟩
  · have e : Y.q.left ⁻¹ᵁ (V' ⊓ i.1.1.1) = Y.q.left ⁻¹ᵁ V' := by
      rw [Scheme.Hom.preimage_inf]; exact inf_eq_left.2 hV'
    have key := (hd i).2 α (V' ⊓ i.1.1.1) inf_le_right
    rw [e] at key
    exact key f hf
end

