module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteTraitExtensionOfBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitExt

theorem exists_finite_trait_extension : ∀ (R W R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (ρ : R →+* R₁), FinExt ρ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing W) Ω] [Algebra.IsAlgebraic (FractionRing W) Ω] (e : FractionRing R₁ →+* Ω), (∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) (φ r))) → ∃ (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsLocalRing W₁) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁) (σ : Ω →+* AlgebraicClosure (FractionRing W₁)), GlobalTheory.LN.CDvr W₁ ∧ Function.Injective iw ∧ iw.Finite ∧ IsLocalHom iw ∧ Function.Injective φ₁ ∧ IsLocalHom φ₁ ∧ φ₁.comp ρ = iw.comp φ ∧ (∀ w, σ (algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) w)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (iw w))) ∧ ∀ r, σ (e (algebraMap R₁ (FractionRing R₁) r)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (φ₁ r)) := by
  intro R W R₁ _ _ _ _ _ _ _ _ _ hW φ hφ hφl ρ hρ Ω _ _ _ _ e he
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨-, hρi, hρf⟩ := hρ

  letI : Algebra W Ω := ((algebraMap (FractionRing W) Ω).comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hWΩ : Function.Injective (algebraMap W Ω) :=
    (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  haveI : FaithfulSMul W Ω := (faithfulSMul_iff_algebraMap_injective W Ω).2 hWΩ
  haveI : Algebra.IsAlgebraic W Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := Ω)).mpr inferInstance

  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hρf
  letI : Algebra R W := φ.toAlgebra
  letI : Algebra R Ω := ((algebraMap W Ω).comp φ).toAlgebra
  haveI : IsScalarTower R W Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₀ : R₁ →+* Ω := e.comp (algebraMap R₁ (FractionRing R₁))
  have hf₀ : ∀ r, f₀ (ρ r) = algebraMap W Ω (φ r) := he
  let f : R₁ →ₐ[R] Ω := { f₀ with commutes' := fun r => hf₀ r }
  have hint : ∀ x : R₁, IsIntegral W (f₀ x) := fun x =>
    IsIntegral.tower_top (A := W) (IsIntegral.map f (show IsIntegral R x from RingHom.Finite.to_isIntegral hρf x))
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule R R₁).FG)
  classical
  obtain ⟨W₁, hd, hc, -, hfin, -, hloc, -, hmem⟩ :=
    GlobalTheory.exists_complete_dvr_finite_subalgebra W Ω (S.image f₀)
  have hin : ∀ x : R₁, f₀ x ∈ W₁ := by
    intro x
    have hx : x ∈ Submodule.span R (S : Set R₁) := hS ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact hmem _ (Finset.mem_image_of_mem _ hy) (hint y)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact W₁.add_mem hy hz
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul]
      refine W₁.mul_mem ?_ hy
      change f₀ (ρ a) ∈ W₁
      rw [hf₀]; exact W₁.algebraMap_mem _

  let iw : W →+* W₁ := algebraMap W W₁
  let φ₁ : R₁ →+* W₁ := f₀.codRestrict W₁ hin
  have hiwinj : Function.Injective iw := fun a b h => hWΩ (congrArg Subtype.val h)
  haveI : CharZero W₁ := charZero_of_injective_ringHom hiwinj
  have hcomp : φ₁.comp ρ = iw.comp φ := by
    ext r; exact hf₀ r
  have hφ₁inj : Function.Injective φ₁ := fun a b h => by
    have : f₀ a = f₀ b := congrArg Subtype.val h
    exact IsFractionRing.injective R₁ (FractionRing R₁) (e.injective this)
  have hφ₁l : IsLocalHom φ₁ := by
    have h1 : (maximalIdeal W₁).comap iw = maximalIdeal W := ((local_hom_tfae iw).out 1 5).mp hloc
    have h2 : (maximalIdeal W).comap φ = maximalIdeal R := ((local_hom_tfae φ).out 1 5).mp hφl
    have hP : ((maximalIdeal W₁).comap φ₁).comap ρ = maximalIdeal R := by
      rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, h1, h2]
    have hmax : ((maximalIdeal W₁).comap φ₁).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ (RingHom.Finite.to_isIntegral hρf) _
        (by rw [hP]; infer_instance)
    exact ((local_hom_tfae φ₁).out 1 5).mpr (IsLocalRing.eq_maximalIdeal hmax)
  haveI : Algebra.IsAlgebraic W₁ Ω := Algebra.IsAlgebraic.extendScalars hiwinj
  haveI : Module.IsTorsionFree W₁ Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  haveI : Module.IsTorsionFree W₁ (AlgebraicClosure (FractionRing W₁)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [IsScalarTower.algebraMap_eq W₁ (FractionRing W₁) (AlgebraicClosure (FractionRing W₁))]
      exact (algebraMap (FractionRing W₁) _).injective.comp (IsFractionRing.injective W₁ (FractionRing W₁)))
  let σ' : Ω →ₐ[W₁] AlgebraicClosure (FractionRing W₁) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ : ∀ x : W₁, σ' (x : Ω) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁))
      (algebraMap W₁ (FractionRing W₁) x) := fun x => by
    rw [← IsScalarTower.algebraMap_apply]; exact σ'.commutes x
  refine ⟨W₁, inferInstance, inferInstance, inferInstance, iw, φ₁, σ'.toRingHom, ⟨hd, hc, inferInstance⟩,
    hiwinj, RingHom.finite_algebraMap.2 hfin, hloc, hφ₁inj, hφ₁l, hcomp, fun w => hσ (iw w), fun r => hσ (φ₁ r)⟩

end GlobalTheory.TraitExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleCoverChartAtFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.ChartAt

theorem mem_genericPoints_of_forall_specializes {X : Scheme.{0}} (ε : X) (h : ∀ z, z ⤳ ε → z = ε) :
    ε ∈ genericPoints X := by
  have hc : irreducibleComponent ε ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents ε
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := ε)) isClosed_irreducibleComponent
  have e : ξ = ε := h ξ (hξ.specializes mem_irreducibleComponent)
  subst e
  change closure {ξ} ∈ irreducibleComponents X
  rw [hξ.def]
  exact hc

theorem forall_specializes_of_flat {X Y : Scheme.{0}} (g : Y ⟶ X) [Flat g] (ε : Y) (h : ∀ z, z ⤳ ε → z = ε) :
    ∀ z, z ⤳ g ε → z = g ε := by
  intro z hz
  obtain ⟨z', hz', e⟩ := Flat.generalizingMap g hz
  rw [← e, h z' hz']

theorem forall_specializes_fromSpec {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(Y, U))
    (hP : P.asIdeal ∈ minimalPrimes Γ(Y, U)) : ∀ z, z ⤳ hU.fromSpec P → z = hU.fromSpec P := by
  intro z hz
  have hr : z ∈ Set.range hU.fromSpec := hz.mem_open hU.fromSpec.isOpenEmbedding.isOpen_range ⟨P, rfl⟩
  obtain ⟨Q, rfl⟩ := hr
  have h1 : Q ⤳ P := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 hz
  have h2 : (show PrimeSpectrum Γ(Y, U) from Q).asIdeal ≤ P.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h1
  have h3 := hP.2 ⟨PrimeSpectrum.isPrime Q, bot_le⟩ h2
  rw [show Q = P from PrimeSpectrum.ext (le_antisymm h2 h3)]

theorem exists_chart_at : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := by
  intro n N X Y Z sX sY q i hi hn hN hsX hsY hq he hs K _ y'
  let pt : Sp K := closedPoint (CommRingCat.of K)
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q (y' pt))) isOpen_univ
  replace hV₀ : IsAffineOpen V₀ := hV₀
  have hU : IsAffineOpen (q ⁻¹ᵁ V₀) := hV₀.preimage q
  set U := q ⁻¹ᵁ V₀ with hUdef
  have hrange : Set.range y' ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨w, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim w pt]
    exact hxV
  let χ : Γ(Y, U) →+* K := (Spec.preimage (IsOpenImmersion.lift hU.fromSpec y' hrange)).hom
  have hχ : spMap χ ≫ hU.fromSpec = y' := by
    have : spMap χ = IsOpenImmersion.lift hU.fromSpec y' hrange := Spec.map_preimage _
    rw [this, IsOpenImmersion.lift_fac]
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨P₀, hP₀, hPχ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal Γ(Y, U))) (J := RingHom.ker χ) bot_le
  obtain ⟨P, rfl⟩ : ∃ P : PrimeSpectrum Γ(Y, U), P.asIdeal = P₀ := ⟨⟨P₀, hP₀.1.1⟩, rfl⟩
  have hmax := forall_specializes_fromSpec hU P hP₀
  have hgen : (sY (hU.fromSpec P)).asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY (hU.fromSpec P) := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    rw [← forall_specializes_of_flat sY _ hmax b hb]
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hsm : ψ.Smooth := by
    have : Smooth (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  haveI : Algebra.Smooth (cycAway N) Γ(Y, U) := hsm
  haveI : IsDedekindDomain (cycAway N) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N
  have hic : IsIntegrallyClosed (Γ(Y, U) ⧸ P.asIdeal) := isIntegrallyClosed_quotient_of_mem_minimalPrimes
    (fun m _ => isDomain_and_isIntegrallyClosed_atPrime_of_smooth (cycAway N) m _) hP₀
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω :=
    ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  have hsurj : Function.Surjective f.rangeRestrict.toRingHom := f.rangeRestrict_surjective
  have hkerR : RingHom.ker f.rangeRestrict.toRingHom = P.asIdeal := by
    ext a
    rw [RingHom.mem_ker, ← hφker, Subtype.ext_iff]
    rfl
  let χR : f.range →+* K := RingHom.liftOfSurjective f.rangeRestrict.toRingHom hsurj ⟨χ, hkerR.le.trans hPχ⟩
  have hχR : χR.comp f.rangeRestrict.toRingHom = χ := RingHom.liftOfSurjective_comp _ _ _
  have hfin : IsFinite (spMap f.rangeRestrict.toRingHom) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_surjective _ hsurj)
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    spMap χR, i ''ᵁ V₀, spMap f.rangeRestrict.toRingHom ≫ hU.isoSpec.inv ≫ (q ∣_ V₀) ≫ (i.isoImage V₀).hom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hV₀.image_of_isOpenImmersion i, inferInstance, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · exact IsIntegrallyClosed.of_equiv
      ((Ideal.quotEquivOfEq hkerR.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj))
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · rw [← Category.assoc, ← hχ, ← hχR, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) ∈ genericPoints X
    rw [hw]
    exact mem_genericPoints_of_forall_specializes _ (forall_specializes_of_flat q _ hmax)
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    have h1 := GlobalTheory.Poinc.Chart.stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec
      (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) (fun z => by
        obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact ⟨a, c, rfl⟩) _ rfl
    have e2 : spMap f.range.val.toRingHom ≫ (spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec) ≫ q ≫ i =
        (spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) ≫ hU.fromSpec ≫ q) ≫ i := by
      rw [← e]; simp only [Category.assoc]
    rw [e2, Scheme.Hom.stalkMap_comp]
    exact h1.comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (i.stalkMap _)).2)
  · simp only [Category.assoc]
    rw [Scheme.Hom.isoImage_hom_ι, ← Category.assoc (q ∣_ V₀), morphismRestrict_ι, Category.assoc,
      ← Category.assoc hU.isoSpec.inv, hU.isoSpec_inv_ι]

end GlobalTheory.Poinc.ChartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionPointAbelianVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TwoTorsionDescent

theorem exists_finite_ext_of_sq_eq_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (G : Over (Sp Ω)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A (spMap ga) α → ∀ x : 𝟙_ (Over (Sp Ω)) ⟶ G, x * x = 1 → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (l : K' →+* Ω) (y : Over.mk (spMap io) ⟶ A.A), io.Finite ∧ l.comp io = ga ∧ y * y = 1 ∧ spMap l ≫ y.left = x.left ≫ α := by
  intro K Ω _ _ _ ga A G _ α h x hx

  set T : Over (Sp K) := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ spMap ga) with hT
  let zo : T ⟶ A.A := pushHom h (𝟙_ (Over (Sp Ω))) x
  have hzo : zo * zo = 1 := by
    show pushHom h _ x * pushHom h _ x = 1
    rw [← map_mul, hx, map_one]
  have hzl : zo.left = x.left ≫ α := rfl
  have hmul : zo ≫ mulN A.A 2 = toUnit T ≫ η[A.A] := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq, hzo]
    rfl
  let t : T ⟶ torsion A.A 2 := pullback.lift zo (toUnit T) hmul
  have ht : t ≫ torsion.ι A.A 2 = zo := pullback.lift_fst _ _ _

  have h2 : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have e : ((2 : ℕ) : Γ(Sp K, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (2 : K) := by
      rw [map_ofNat]; rfl
    rw [e]
    exact (IsUnit.mk0 (2 : K) two_ne_zero).map _
  haveI := A.isAb
  have hfin : IsFinite (torsion A.A 2).hom := (GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.A h2).2.1
  set X := (torsion A.A 2).left
  set p := (torsion A.A 2).hom
  let tl : Sp Ω ⟶ X := t.left
  let w : X := tl (IsLocalRing.closedPoint Ω)
  let φ : X.residueField w ⟶ CommRingCat.of Ω := X.descResidueField (Scheme.stalkClosedPointTo tl)
  have htl : Spec.map φ ≫ X.fromSpecResidueField w = tl :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X tl

  let s : Sp K := p w
  haveI : s.asIdeal.IsPrime := s.isPrime
  haveI : s.asIdeal.IsMaximal := by rw [Ideal.eq_bot_of_prime s.asIdeal]; exact Ideal.bot_isMaximal
  let c : K →+* (Sp K).residueField s :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).inv.hom.comp (algebraMap K s.asIdeal.ResidueField)
  have hc : spMap c = (Sp K).fromSpecResidueField s := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    rfl
  have hcfin : c.Finite := by
    refine RingHom.Finite.of_surjective _ ?_
    refine (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).commRingCatIsoToRingEquiv.symm.surjective.comp ?_
    have hq : Function.Surjective (Ideal.Quotient.mk s.asIdeal) := Ideal.Quotient.mk_surjective
    have hb := Ideal.bijective_algebraMap_quotient_residueField s.asIdeal
    have e : (algebraMap K s.asIdeal.ResidueField) = (algebraMap (K ⧸ s.asIdeal) s.asIdeal.ResidueField).comp (Ideal.Quotient.mk s.asIdeal) := by
      ext a; rfl
    rw [e]
    exact hb.2.comp hq
  let io : K →+* X.residueField w := (p.residueFieldMap w).hom.comp c
  have hio : io.Finite := (GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite p w).comp hcfin
  have hsio : spMap io = X.fromSpecResidueField w ≫ p := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc, ← Spec.map_comp]
    rfl

  have hu : X.fromSpecResidueField w ≫ p = spMap io := hsio.symm
  let u : Over.mk (spMap io) ⟶ torsion A.A 2 := Over.homMk (X.fromSpecResidueField w) hu
  let y : Over.mk (spMap io) ⟶ A.A := u ≫ torsion.ι A.A 2
  have hy : y * y = 1 := by
    have e1 : y * y = y ≫ mulN A.A 2 := by
      rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq]
    have e2 : torsion.ι A.A 2 ≫ mulN A.A 2 = pullback.snd (mulN A.A 2) η[A.A] ≫ η[A.A] :=
      pullback.condition
    rw [e1, Category.assoc, e2]
    show (u ≫ pullback.snd (mulN A.A 2) η[A.A]) ≫ η[A.A] = toUnit _ ≫ η[A.A]
    rw [toUnit_unique (u ≫ pullback.snd (mulN A.A 2) η[A.A]) (toUnit _)]
  have hlo : Spec.map φ ≫ X.fromSpecResidueField w ≫ p = spMap ga := by
    rw [← Category.assoc, htl]
    exact Over.w t
  refine ⟨X.residueField w, inferInstance, io, φ.hom, y, hio, ?_, hy, ?_⟩
  · have e : spMap (φ.hom.comp io) = spMap ga := by
      rw [← hlo, ← hsio]
      show _ = Spec.map φ ≫ Spec.map (CommRingCat.ofHom io)
      erw [← Spec.map_comp]
      rfl
    have e' := Spec.map_inj.mp e
    exact congrArg CommRingCat.Hom.hom e'
  · show Spec.map (CommRingCat.ofHom φ.hom) ≫ (X.fromSpecResidueField w ≫ (torsion.ι A.A 2).left) = x.left ≫ α
    rw [CommRingCat.ofHom_hom, ← Category.assoc, htl, ← hzl, ← ht]
    rfl

end GlobalTheory.TwoTorsionDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalNoetherianCoverFractionFieldEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.LocExt

theorem exists_finite_normal_cover_of_finiteDimensional : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'), Function.Injective ρ ∧ ρ.Finite ∧ ((τ.comp (algebraMap (FractionRing R) K')).comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  intro R _ _ _ _ hcomp K' _ _ _
  have hnorm : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hCN : IsCN R := ⟨inferInstance, hnorm, hcomp, inferInstance⟩
  let K := FractionRing R
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K K' := inferInstance
  let C := integralClosure R K'
  haveI hCf : Module.Finite R C := IsIntegralClosure.finite R K K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  have hRK' : Function.Injective (algebraMap R K') := by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K)
  have hRC : Function.Injective (algebraMap R C) := fun x y h => hRK' (congrArg Subtype.val h)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρ, hρf, -, hσρ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) hCN hRC
      (RingHom.finite_algebraMap.2 hCf)
  obtain ⟨hnoeth', hnorm', -, -⟩ := hCN'
  letI : Algebra C R' := σ.toAlgebra
  letI : Algebra R R' := ρ.toAlgebra
  haveI : IsScalarTower R C R' := IsScalarTower.of_algebraMap_eq (fun r => (RingHom.congr_fun hσρ r).symm)
  haveI : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  have hσ : Function.Injective σ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have hker : RingHom.ker σ = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := R)
      ext r
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro h
        apply hρ
        rw [map_zero, ← h]
        exact (RingHom.congr_fun hσρ r).symm
      · rintro rfl; simp
    have : c ∈ RingHom.ker σ := hc
    rw [hker] at this
    exact this
  have hσ' : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσ
  let τ : K' →+* FractionRing R' := IsFractionRing.lift (A := C) hσ'
  refine ⟨R', inferInstance, inferInstance, hnoeth', hnorm', inferInstance, ρ, τ, hρ, hρf, ?_⟩
  ext r
  simp only [RingHom.comp_apply]
  have h1 : algebraMap K K' (algebraMap R K r) = algebraMap C K' (algebraMap R C r) := rfl
  rw [h1]
  simp only [τ, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  rw [← RingHom.comp_apply σ, hσρ]

end GlobalTheory.LocExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalActRankOne
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section
variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}}

end


open GlobalTheory.TorsionFormCompare in
theorem isPullUnif_refl {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre) (hid : IsIdPull hD)
    (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G)
    (hbc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 _) : IsPullUnif (RingHom.id R) hD bc U U := by
  obtain ⟨hx, he, hw⟩ := hid
  have hs := specOf_id R
  have heG : eSec G ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = specOf (RingHom.id R) ≫ eSec G := by
    rw [hbc, hs, Category.comp_id]; exact (Category.id_comp _).symm
  refine (GlobalTheory.isPullUnif_iff_stalks R R I I _ D D hD A A G G bc U U).2
    ⟨isoPullId (Geo.Tor.idIso U.LG.L) hbc, (isGen_iff _).2 (isoPullId_pgen (idIso_isGen U.LG.isLB) hbc), heG,
      isoPullId_maps (idIso_maps U.LG) hbc hs heG, fun e => ⟨𝟙 _, by rw [hbc, Category.id_comp, Category.comp_id],
      ⟨by rw [he, Category.id_comp, Category.comp_id], fun x => ?_⟩, ?_⟩⟩
  · rw [hx x]
    exact ⟨fun κ => by rw [he, Category.id_comp, Category.comp_id],
      pmaps_self_of_tautological he hD.w hw _ _ _ ((U.gt e).t_gen x)⟩
  · intro Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have h₁' : (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM := by rw [he] at h₁; exact h₁
    have h₃' : (fstG I e G).left (r z) ∈ U.LG.L.U jL := by rw [hbc] at h₃; exact h₃
    rw [Category.comp_id, gw_isoPullId _ hbc _ z jL jL' h₃' h₄, hw Z (r ≫ (U.gt e).pG.left) z jM jM' h₁' h₂]
    have H := (isGen_iff (U.w e)).1 (U.w_gen e) Z r z jM jM' (fun _ => jL) (fun _ => jL') h₁' h₂
      (mem_pull.2 h₃') (mem_pull.2 h₄)
    have hp : r z ∈ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL') :=
      ⟨mem_pull.2 h₃', mem_pull.2 h₄⟩
    have e₂ : gm r z _ ((U.LG.L.pull (fstG I e G).left).g (fun _ => jL) (fun _ => jL')) =
        gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL') := by
      show gm r z _ (∏ _k : PUnit, (res _ (pullU _ _ (U.LG.L.g jL jL'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res r z _ hp _).trans (gm_pull r _ z (U.LG.L.U jL ⊓ U.LG.L.U jL') ⟨h₃', h₄⟩ _)
    rw [H, e₂]
    show _ = _ * gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL')
    rw [mul_right_comm _ _⁻¹, inv_mul_cancel_right]

end GlobalTheory.Mum
end
end

