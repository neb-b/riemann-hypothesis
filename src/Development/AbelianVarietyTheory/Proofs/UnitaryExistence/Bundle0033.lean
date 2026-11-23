module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOverLaOfNotCharZero
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open Formalism.L2.Pj

namespace GlobalTheory.LocalDepthCompare

section Places

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem valV_le_one (v : V) : valV V (algebraMap V K' v) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one _ v

theorem valV_lt_one_iff (v : V) : valV V (algebraMap V K' v) < 1 ↔ v ∈ maximalIdeal V :=
  HeightOneSpectrum.valuation_lt_one_iff_mem _ v

theorem valV_eq_one {v : V} (h : v ∉ maximalIdeal V) : valV V (algebraMap V K' v) = 1 :=
  le_antisymm (valV_le_one v) (not_lt.1 fun h' => h ((valV_lt_one_iff v).1 h'))

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K' v) := by
  have h1 : algebraMap V K' v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K')).2 h0
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 ((valV_lt_one_iff v).2 h)
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

theorem not_charZero_iff : ¬ CharZero (ResidueField V) ↔ ∃ n : ℕ, n ≠ 0 ∧ (n : V) ∈ maximalIdeal V := by
  constructor
  · intro h
    by_contra hn
    refine h (charZero_of_inj_zero fun n h0 => ?_)
    by_contra hn0
    exact hn ⟨n, hn0, by rw [← residue_eq_zero_iff, map_natCast, h0]⟩
  · rintro ⟨n, hn, hm⟩ _
    rw [← residue_eq_zero_iff, map_natCast] at hm
    exact hn (by exact_mod_cast hm)

variable {K : Type} [Field K] [NumberField K]

theorem not_charZero_of_overLa {la : HeightOneSpectrum (𝓞 K)} {io : K →+* K'} {e : ℕ}
    (ho : OverLa la V io e) : ¬ CharZero (ResidueField V) := by
  rw [not_charZero_iff]
  have hn : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨_, hn, ?_⟩
  have hmem := Ideal.absNorm_mem la.asIdeal
  generalize Ideal.absNorm la.asIdeal = n at hn hmem
  by_contra hV
  have hK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn
  have h1 : valV V ((n : ℕ) : K') = 1 := by
    rw [← map_natCast (algebraMap V K') n]
    exact valV_eq_one hV
  have h2 : la.valuation K ((n : ℕ) : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) n, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  have h3 : WithZero.log (la.valuation K ((n : ℕ) : K)) < 0 := by
    have := (WithZero.log_lt_log ((la.valuation K).ne_zero_iff.2 hK) one_ne_zero).2 h2
    simpa using this
  have h4 := ho.2 ((n : ℕ) : K)
  rw [map_natCast, vV, h1, vLa, WithZero.log_one] at h4
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  nlinarith [mul_pos he (neg_pos.2 h3)]

theorem exists_overLa_of_not_charZero (io : K →+* K') (hT : ¬ CharZero (ResidueField V)) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la V io e := by
  have hint : ∀ a : 𝓞 K, ∃ v : V, algebraMap V K' v = io a := fun a =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := K')
      (IsIntegral.map_of_comp_eq (Int.castRingHom V) io (RingHom.ext_int _ _) a.isIntegral_coe)
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective V K'
  let g : 𝓞 K →+* V :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap V K' (g a) = io (algebraMap (𝓞 K) K a) := hg0
  have hne : (maximalIdeal V).comap g ≠ ⊥ := by
    obtain ⟨n, hn, hm⟩ := not_charZero_iff.1 hT
    intro h
    have h1 : ((n : ℕ) : 𝓞 K) ∈ (maximalIdeal V).comap g := by
      rw [Ideal.mem_comap, map_natCast]; exact hm
    rw [h, Ideal.mem_bot] at h1
    exact hn (by exact_mod_cast h1)
  let la : HeightOneSpectrum (𝓞 K) := ⟨(maximalIdeal V).comap g, Ideal.comap_isPrime _ _, hne⟩
  have hun : ∀ a : 𝓞 K, a ∉ la.asIdeal → valV V (io (algebraMap (𝓞 K) K a)) = 1 := fun a ha => by
    rw [← hg]
    exact valV_eq_one ha
  have hone : ∀ x : K, la.valuation K x = 1 → valV V (io x) = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
    have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
    have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
    have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
    rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  have hπK : la.valuation K (algebraMap (𝓞 K) K π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := fun h => by
    simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
  have hπm : π ∈ la.asIdeal := by
    rw [← la.valuation_lt_one_iff_mem (K := K), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hpos : 0 < vV V (io (algebraMap (𝓞 K) K π)) := by
    rw [← hg]
    refine vV_pos (fun h => ?_) hπm
    have := hg π
    rw [h, map_zero] at this
    exact (map_ne_zero io).2 hπ0 this.symm
  refine ⟨la, (vV V (io (algebraMap (𝓞 K) K π))).toNat, by omega, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hpos.le]
  by_cases ha : a = 0
  · simp [ha, vV, vLa]
  have hva : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have h1 := hone (a * (algebraMap (𝓞 K) K π) ^ (-vLa la a)) (by
    rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
    simp [vLa])
  have h2 := congrArg WithZero.log h1
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero io).2 ha))
    (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero io).2 hπ0))), WithZero.log_zpow,
    WithZero.log_one] at h2
  simp only [vV, smul_eq_mul] at h2 ⊢
  linarith

end Places

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Local

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

variable {la : HeightOneSpectrum (𝓞 c.F)} {e : ℕ}

end Local

variable (Xo c)

end GlobalTheory.LocalDepthCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.NormCurve

theorem exists_eq_div {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) (z : R) :
    ∃ x y : B, z = algebraMap B R x / algebraMap B R y := by
  obtain ⟨x, r, c, hc, hr, e⟩ := (RingHom.surjective_localRingHom_iff (⊥ : Ideal R)).mp
    (h ⊥ inferInstance) z
  rw [Ideal.mem_bot] at hc hr
  refine ⟨x, r, ?_⟩
  rw [eq_div_iff hr]
  apply mul_left_cancel₀ hc
  rw [← e]
  ring

theorem isIntegrallyClosed_integralClosure {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) : IsIntegrallyClosed (integralClosure B R) := by
  haveI : IsFractionRing (integralClosure B R) R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, e⟩
  exact (isIntegrallyClosed_iff R).mpr fun {x} hx => ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

theorem finite_integralClosure (k : Type) {B R : Type} [Field k] [PerfectField k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) :
    Module.Finite B (integralClosure B R) ∧ ∀ [Algebra k R] [IsScalarTower k B R],
      ringKrullDim (B ⧸ RingHom.ker (algebraMap B R)) ≤ 1 → Algebra.trdeg k R ≤ 1 := by
  let A := B ⧸ RingHom.ker (algebraMap B R)
  haveI : (RingHom.ker (algebraMap B R)).IsPrime := RingHom.ker_isPrime _
  letI : Algebra A R := (RingHom.kerLift (algebraMap B R)).toAlgebra
  haveI : IsScalarTower B A R := .of_algebraMap_eq fun x => (RingHom.kerLift_mk _ x).symm
  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (RingHom.kerLift_injective _)
  haveI : IsFractionRing A R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, by
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩
  constructor
  · haveI := NormFin.finite_integralClosure_of_perfectField k A R R
    haveI : Module.Finite B (integralClosure A R) := Module.Finite.trans A _
    have h' : Module.Finite B ((integralClosure A R).restrictScalars B) := this
    rwa [integralClosure_restrictScalars_of_isIntegral] at h'
  · intro _ _ hd
    haveI : IsScalarTower k A R := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k B R, IsScalarTower.algebraMap_apply k B A,
        ← IsScalarTower.algebraMap_apply B A R]
    obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
    haveI : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap k A).injective
    haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := R), trdeg_eq_zero (R := A) (A := R), add_zero, hs2]
    rw [hs1] at hd
    exact_mod_cast hd

theorem dimensionLEOne_of_injective {k A R : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (g : A →ₐ[k] R)
    (hg : Function.Injective g) (h : Algebra.trdeg k R ≤ 1) : Ring.DimensionLEOne A := by
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  have h1 := (trdeg_le_of_injective g hg).trans h
  rw [hs2] at h1
  have h2 : s ≤ 1 := by exact_mod_cast h1
  have h3 : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, hs1]
    exact_mod_cast h2
  exact ⟨fun {p} hp hp' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h3 p hp hp'⟩

section Scheme

variable {k : Type} [Field k] {X Z : Scheme.{0}}

noncomputable def constHom (s : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ U le_top).hom

theorem finiteType_constHom (s : X ⟶ Sp k) [LocallyOfFiniteType s] {U : X.Opens}
    (hU : IsAffineOpen U) : (constHom s U).FiniteType := by
  have h : (s.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      le_top
  exact h.comp (.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)

theorem appLE_comp_constHom (s : X ⟶ Sp k) (f : Z ⟶ X) (U : X.Opens) (V : Z.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.comp (constHom s U) = constHom (f ≫ s) V := by
  rw [constHom, constHom, ← Scheme.Hom.appLE_comp_appLE f s ⊤ U V le_top e]
  rfl

theorem isField_sections [IsIntegral Z] [Subsingleton Z] (V : Z.Opens) [hV : Nonempty V] :
    IsField Γ(Z, V) := by
  refine ⟨exists_pair_ne _, mul_comm, fun {a} ha => IsUnit.exists_right_inv ?_⟩
  refine Z.toRingedSpace.isUnit_of_isUnit_germ V a fun x hx => ?_
  have h : Z.basicOpen a ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff a).mp h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h
  rw [Subsingleton.elim y x] at hy
  exact (Z.mem_basicOpen a x hx).mp hy

theorem isAffineOpen_of_subsingleton [IsAffine Z] [Subsingleton Z] (V : Z.Opens)
    [hV : Nonempty V] : IsAffineOpen V := by
  obtain ⟨y, hy⟩ := hV
  have : V = ⊤ := eq_top_iff.mpr fun x _ => Subsingleton.elim y x ▸ hy
  rw [this]
  exact isAffineOpen_top Z

variable [IsIntegral Z] [Subsingleton Z] [IsAffine Z] (f : Z ⟶ X) [SurjectiveOnStalks f]

theorem surjectiveOnStalks_appLE {U : X.Opens} (hU : IsAffineOpen U) (V : Z.Opens) [Nonempty V]
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.SurjectiveOnStalks :=
  HasRingHomProperty.appLE @SurjectiveOnStalks f inferInstance ⟨U, hU⟩
    ⟨V, isAffineOpen_of_subsingleton V⟩ e

variable [QuasiCompact f] [QuasiSeparated f]

theorem isFinite_fromNormalization [PerfectField k] (s : X ⟶ Sp k) [LocallyOfFiniteType s] :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  letI := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U)) := by
    by_cases hne : Nonempty (f ⁻¹ᵁ U)
    · letI := (isField_sections (f ⁻¹ᵁ U)).toField
      letI := (constHom s U).toAlgebra
      haveI : Algebra.FiniteType k Γ(X, U) := finiteType_constHom s hU
      refine (finite_integralClosure k ?_).1
      have := surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl
      rwa [← Scheme.Hom.app_eq_appLE] at this
    · have : f ⁻¹ᵁ U = ⊥ := eq_bot_iff.mpr fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      have : Subsingleton Γ(Z, f ⁻¹ᵁ U) := by rw [this]; infer_instance
      infer_instance
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr h)

theorem isIntegrallyClosed_stalk (y : f.normalization) :
    IsIntegrallyClosed (f.normalization.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.fromNormalization y)) isOpen_univ
  have hy : y ∈ f.fromNormalization ⁻¹ᵁ U := hyU
  have hne : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.fromNormalization ⁻¹ᵁ U).isOpen ⟨y, hy⟩
    refine ⟨⟨z, ?_⟩⟩
    rw [← f.toNormalization_fromNormalization]
    exact hz
  letI := (f.app U).hom.toAlgebra
  have h1 : IsIntegrallyClosed (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U)) := by
    letI := (isField_sections (f ⁻¹ᵁ U)).toField
    refine isIntegrallyClosed_integralClosure ?_
    have := surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  have h2 : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
  have hV := hU.preimage f.fromNormalization
  haveI : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨y, hy⟩⟩
  letI := f.normalization.presheaf.algebra_section_stalk (⟨y, hy⟩ : f.fromNormalization ⁻¹ᵁ U)
  haveI := hV.isLocalization_stalk ⟨y, hy⟩
  exact isIntegrallyClosed_of_isLocalization (R := Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)) _
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

theorem isDedekindDomain_sections [PerfectField k] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hd : letI := (constHom (f ≫ s) ⊤).toAlgebra; Algebra.trdeg k Γ(Z, ⊤) ≤ 1)
    (U : f.normalization.Opens) (hU : IsAffineOpen U) [hne : Nonempty U] :
    IsDedekindDomain Γ(f.normalization, U) := by
  haveI := isFinite_fromNormalization f s
  letI := (constHom (f ≫ s) ⊤).toAlgebra
  letI := (constHom (f.fromNormalization ≫ s) U).toAlgebra
  haveI : Algebra.FiniteType k Γ(f.normalization, U) := finiteType_constHom _ hU
  have e : ⊤ ≤ f.toNormalization ⁻¹ᵁ U := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩
    exact fun x _ => Subsingleton.elim z x ▸ hz
  have hc := appLE_comp_constHom (f.fromNormalization ≫ s) f.toNormalization U ⊤ e
  rw [f.toNormalization_fromNormalization_assoc] at hc
  let g : Γ(f.normalization, U) →ₐ[k] Γ(Z, ⊤) :=
    { (f.toNormalization.appLE U ⊤ e).hom with commutes' := fun a => congr($hc a) }
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have h : f.normalization.basicOpen a ≠ ⊥ := fun h => h0 ((basicOpen_eq_bot_iff a).mp h)
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.normalization.basicOpen a).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h)
    have h1 : z ∈ Z.basicOpen (f.toNormalization.appLE U ⊤ e a) := by
      rw [Scheme.basicOpen_appLE]
      exact ⟨trivial, hz⟩
    have ha' : f.toNormalization.appLE U ⊤ e a = 0 := ha
    rw [ha', Scheme.basicOpen_zero] at h1
    exact h1
  exact { Algebra.FiniteType.isNoetherianRing k _, dimensionLEOne_of_injective g hg hd,
    isIntegrallyClosed_sections_of_stalks (isIntegrallyClosed_stalk f) hU with }

end Scheme

end GlobalTheory.NormCurve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsScaledIsometry
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.SelfDualIsom

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {M₁ M₂ V : Type}
    [AddCommGroup M₁] [Module (𝓞 E) M₁] [Module.Finite (𝓞 E) M₁]
    [AddCommGroup M₂] [Module (𝓞 E) M₂] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (φ₁ : M₁ →ₗ[𝓞 E] V) (φ₂ : M₂ →ₗ[𝓞 E] V)
    (hspan : Submodule.span E (Set.range φ₂) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, (N : 𝓞 E) • φ₁ x ∈ LinearMap.range φ₂ := by
  classical
  have h1 : ∀ v : V, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ LinearMap.range φ₂ := by
    intro v
    have hv : v ∈ Submodule.span E (Set.range φ₂) := by rw [hspan]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [← LinearMap.coe_range, Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hm := Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)})
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ht0
    · rw [← hc, mul_smul]
      exact Submodule.smul_mem _ _ ht
  choose n hn hmem using h1
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M₁)
  refine ⟨∏ x ∈ s, n (φ₁ x), Finset.prod_pos fun x _ => hn _, fun x => ?_⟩
  have hx : x ∈ Submodule.span (𝓞 E) (s : Set M₁) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ₁ x)) (Finset.mem_coe.1 hy)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hmem _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.SelfDualIsom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_frameChangeByMatrices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) → ∃! y' : FrPt Xo c S, FrChg g (a : S) y y' := by
  first | exact @GlobalTheory.Frames.existsUnique_frChg | exact GlobalTheory.Frames.existsUnique_frChg | (intros; apply GlobalTheory.Frames.existsUnique_frChg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsAlgebraicPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_finite_point_mem_opens {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧
      ∃ y : Spec (CommRingCat.of L) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧ Set.range y ⊆ W := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxW, hx⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  have hc : IsClosedImmersion (X.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  rw [← hφ, IsFinite.SpecMap_iff] at hfin
  let : Algebra k (X.residueField x) := φ.hom.toAlgebra
  refine ⟨X.residueField x, inferInstance, inferInstance, hfin, X.fromSpecResidueField x, hφ.symm, ?_⟩
  rw [Scheme.range_fromSpecResidueField]
  simpa using hxW

theorem moduli_exists_algebraic_point :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W : (Xo.XF c).Opens), (W : Set (Xo.XF c)).Nonempty → ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L), FiniteDimensional c.F L ∧ ∃ y : Sp L ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧ Set.range y ⊆ W := by
  intro E _ _ _ H D l Xo c W hW
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  exact exists_finite_point_mem_opens (pullback.snd _ _) W hW

end GlobalTheory
end

