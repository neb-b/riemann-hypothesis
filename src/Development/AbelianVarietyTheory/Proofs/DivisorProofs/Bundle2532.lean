module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionTensorQuotientRingEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartPresentsLevelsModIdeal
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

theorem coeff_mem_of_mem_smul_top {O σ : Type} [CommRing O] (I : Ideal O)
    {h : MvPowerSeries σ O} (hh : h ∈ I • (⊤ : Submodule O (MvPowerSeries σ O))) (α : σ →₀ ℕ) :
    coeff α h ∈ I := by
  refine Submodule.smul_induction_on hh (fun a ha x _ => ?_) (fun x y hx hy => ?_)
  · rw [MvPowerSeries.coeff_smul]
    exact I.mul_mem_right _ ha
  · rw [map_add (f := _)]
    exact I.add_mem hx hy

theorem presents_quotient :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
      (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I →
      ∃ hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i),
        (∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
          (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f) ∧
        Presents (O ⧸ I) (B := fun n => (O ⧸ I) ⊗[O] G.A n) (fun n i => 1 ⊗ₜ[O] c.x n i) hx := by
  intro p _ O _ G d c I m hm
  have hp : ∀ n, ((p : (O ⧸ I) ⊗[O] G.A n)) ^ m = 0 := fun n => by
    have h0 : ((p : O ⧸ I)) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    rw [← map_natCast (algebraMap (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n)), ← map_pow, h0, map_zero]
  have hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i) := fun n i => by
    obtain ⟨N, y, hy⟩ := c.nil n i
    refine ⟨N * m, ?_⟩
    have : (1 : O ⧸ I) ⊗ₜ[O] c.x n i = Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)
      (c.x n i) := rfl
    rw [this, ← map_pow, pow_mul, hy, mul_pow, map_mul, map_pow, map_natCast, hp, zero_mul]
  have hev : ∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
      (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f := fun n f =>
    (GlobalTheory.algHom_eval_comp_eq_evA_map p m O (G.A n) (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) (Fin d) (c.x n) (c.ev n) (c.isEval n)
      (Ideal.Quotient.mk I)
      (Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)).toRingHom
      (fun a => by
        change Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I) (algebraMap O (G.A n) a) = _
        rw [AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply O (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) a)
      (hp n) (hx n) f).symm
  refine ⟨hx, hev, fun n y => ?_, fun N => ?_⟩
  · obtain ⟨b, rfl⟩ := (GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).1 y
    obtain ⟨f, rfl⟩ := c.surj n b
    exact ⟨_, hev n f⟩
  · obtain ⟨n, hn⟩ := c.ker m N
    refine ⟨n, fun g hg α hα => ?_⟩
    obtain ⟨f, rfl, -⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 g
    rw [hev] at hg
    have h1 : c.ev n f ∈ I • (⊤ : Submodule O (G.A n)) := ((GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).2.1 _).1 hg
    have h2 : c.ev n f ∈ (I • (⊤ : Submodule O (MvPowerSeries (Fin d) O))).map
        (c.ev n).toLinearMap := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (c.surj n)]
      exact h1
    obtain ⟨h, hh, he⟩ := h2
    have h3 : c.ev n (f - h) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact he.symm
    have h4 : coeff α (f - h) ∈ I := by
      obtain ⟨z, hz⟩ := hn (f - h) h3 α hα
      rw [hz]
      exact I.mul_mem_right _ hm
    have h5 : coeff α f ∈ I := by
      have := I.add_mem h4 (coeff_mem_of_mem_smul_top I hh α)
      rwa [map_sub, sub_add_cancel] at this
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    exact h5

end GlobalTheory.QLog.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndomorphismPullsTorusCoordinateNormalised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem coord_of_formalEnd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  intro R _ _ _ _ D a a' h h' hE A G _ _ _ U b ⟨hb, _, hq, ht⟩ α u ⟨hu, hu1⟩ e Z x z J hJ
  obtain ⟨t, ht, hi⟩ := ht e
  have := hb e
  have := (U.gt e).q_hom
  obtain ⟨v, hv, vv⟩ := GlobalTheory.gtCoord_end_ratio_descends R (maximalIdeal R) D.toPre e G (U.gt e) (b e) a h' t
    (hb e) ht hi (hq e) α
  have hA : IsAbelianScheme (thickObj R (maximalIdeal R) e D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have key := gen_unique D.toPre.P.isLB (thickObj R (maximalIdeal R) e D.toPre.P.A).hom
    (η[thickObj R (maximalIdeal R) e D.toPre.P.A]).left (Over.w _) (GlobalTheory.globalFns_holds _ _ hA).2 hv
    (DVR.pullGen_isGen _ _ _ _ hu (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)))
    (fun y J hJ => by
      have k := vv _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
          thickObj R (maximalIdeal R) e D.toPre.P.A) = η[thickObj R (maximalIdeal R) e D.toPre.P.A] := by
        simp [Hom.one_def]
      rw [o] at k
      exact k.symm.trans ((hu1 _ (thick R (maximalIdeal R) e) y J hJ).symm.trans
        ((congrArg (fun p => val u p y J)
          (UnitValue.eSec_pullback_fst (thick R (maximalIdeal R) e) D.toPre.P.A).symm).trans
          (val_pull hJ _ _ _).symm)))
  refine (vv Z x z J hJ).trans (congrArg (_ * ·) ((key Z _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)))
  exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.TwFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeInt
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem perfectField_fractionRing_zmod (p : ℕ) [Fact p.Prime] :
    PerfectField (FractionRing (ZMod p)) :=
  PerfectField.of_ringEquiv (FractionRing.algEquiv (ZMod p) (ZMod p)).symm.toRingEquiv

theorem formalFibre_isRegularRing_of_essFiniteType_int :
    ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Algebra.EssFiniteType ℤ R] [Field K] [Algebra R K]
      [Algebra.EssFiniteType R K], IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  intro R K _ _ _ _ _ _
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  ·
    set p := ringChar K with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℤ R
    have hpK : algebraMap R K (p : R) = 0 := by
      rw [map_natCast]; exact CharP.cast_eq_zero K p
    have hnu : ((p : ℕ) : R) ∈ nonunits R := fun hu => by
      have := hu.map (algebraMap R K); rw [hpK] at this; exact not_isUnit_zero this
    let I : Ideal R := Ideal.span {((p : ℕ) : R)}
    haveI : CharP (R ⧸ I) p := CharP.quotient R p hnu
    have hI : I ≠ ⊤ := by
      exact fun h => hnu (Ideal.span_singleton_eq_top.mp h)
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hker : I ≤ RingHom.ker (algebraMap R K) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact hpK
    letI : Algebra (R ⧸ I) K := (Ideal.Quotient.lift I (algebraMap R K) hker).toAlgebra
    haveI : IsScalarTower R (R ⧸ I) K := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.EssFiniteType R (R ⧸ I) :=
      Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
    haveI : Algebra.EssFiniteType ℤ (R ⧸ I) := Algebra.EssFiniteType.comp ℤ R (R ⧸ I)
    letI : Algebra (ZMod p) (R ⧸ I) := ZMod.algebra (R ⧸ I) p
    haveI : Algebra.EssFiniteType (ZMod p) (R ⧸ I) := Algebra.EssFiniteType.of_comp ℤ (ZMod p) (R ⧸ I)
    haveI : Algebra.EssFiniteType (R ⧸ I) K := Algebra.EssFiniteType.of_comp R (R ⧸ I) K
    haveI := perfectField_fractionRing_zmod p
    have hinj : ∀ a : ZMod p, algebraMap (R ⧸ I) K (algebraMap (ZMod p) (R ⧸ I) a) = 0 → a = 0 :=
      fun a ha => ((algebraMap (R ⧸ I) K).comp (algebraMap (ZMod p) (R ⧸ I))).injective
        (by simpa using ha)
    have hreg := _root_.GlobalTheory.formalFibre_isRegularRing_of_essFiniteType (ZMod p) (R ⧸ I) K hinj
    obtain ⟨e⟩ := _root_.GlobalTheory.adicCompletion_tensor_quotient_ringEquiv R (R ⧸ I) K Ideal.Quotient.mk_surjective
    exact IsRegularRing.of_ringEquiv e
  ·
    haveI : CharP K 0 := by rw [← h0]; exact ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    refine _root_.GlobalTheory.formalFibre_isRegularRing_of_essFiniteType ℤ R K ?_
    intro a ha
    rw [eq_intCast (algebraMap ℤ R), map_intCast] at ha
    exact_mod_cast ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSumTwistCubeIdentity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem formEq_twist_cube : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := by
  intro R _ _ D₂ D T Y₀ q y p₂ β _ hp b χ₂ χ U _ h
  have hu : ∀ x : T ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit T := fun x => toUnit_unique _ _
  have ht : ∀ x : T ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.Oφ p₂ χ₂ k = ((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) ^ (Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k ≫ β) * (toUnit T ≫ b)).left *
        (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left) ^ Oinvε k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (Oinvε k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have h0 : (p₂ * (toUnit T ≫ D₂.c χ₂)) ≫ β = (q ≫ y) * (toUnit T ≫ D₂.c χ₂ ≫ β) := by
    rw [MonObj.mul_comp, hp, Category.assoc]
  have h3 : (1 : T ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  have hC : ∏ k, h (D.Oφ (q ≫ y) χ k) ^ (-Oinvε k) = h ((q ≫ y) * (toUnit T ≫ D.c χ)).left *
      (h (toUnit T ≫ D.c χ).left)⁻¹ * (h (q ≫ y).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((q ≫ y) * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
      h (q ≫ y).left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ) = _
    simp only [zpow_neg, zpow_one, inv_inv]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA, prod_cub, hC, GlobalTheory.CoordCompare.prod_diff, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    h0, h3, hp, _root_.one_mul, Category.assoc]
  simp only [Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.BaseTerms

def FrPull {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    {A : PolAV (Sp (FractionRing V))} {A₂ : PolAV (Sp (FractionRing V'))} {ψ : A₂.A.left ⟶ A.A.left}
    (w : LB.Iso A₂.L (A.L.pull ψ)) (f : FractionRing V →+* FractionRing V')
    (x₂ : TFK (R := V') (FractionRing V') ⟶ A₂.A) (fr₂ : FrAt x₂) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x)
    (ρ : FractionRing V') : Prop :=
  ∀ (z : (TFK (R := V') (FractionRing V')).left) (J : ((TFK (R := V') (FractionRing V')).left ⟶ A.A.left) → A.L.ι)
    (J' : ((TFK (R := V') (FractionRing V')).left ⟶ A₂.A.left) → A₂.L.ι), Good A.L z J → Good A₂.L z J' →
    ((gw w x₂.left z (J (x₂.left ≫ ψ)) (J' x₂.left) : _) * (val fr₂ (𝟙 _) z J' : _) : ((TFK (R := V') (FractionRing V')).left.presheaf.stalk z)) =
      @id ((TFK (R := V') (FractionRing V')).left.presheaf.stalk z) (GlobalTheory.UT.cst (R := V') (FractionRing V') z ρ) *
        (val fr (show (TFK (R := V') (FractionRing V')).left ⟶ (TFK (R := V) (FractionRing V)).left from spMap f) z J : _)

end GlobalTheory.Poinc.Sep.BaseTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentialVolumeSmall
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThickBerg

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem cpt_mem_dom_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
    cpt X x z ∈ X.dom := _root_.GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le

theorem ball_injects : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q →
    ∀ (k : U.Comp) (x : Frame (U.X k).Ψ r), IsOrth (U.X k) x →
    100 * (((U.X k).Ψ.card : ℝ) * r) ^ 4 ≤ (l.M' : ℝ) * (U.X k).firstMinimumSq x →
    ∀ γ ∈ (U.X k).Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (nd (U.X k)), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor (U.X k).Ψ r,
      lact γ (cpt (U.X k) x z) = rmul (cpt (U.X k) x z') b → γ = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hl hp hq k x hx hM γ hγ z z' hz hz' b hb he
  obtain ⟨hsd, horb⟩ := _root_.GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf E H Dw l Xo c σ r U hσ hU hl hp hq k
  have hwd : cpt (U.X k) x z ∈ (U.X k).dom := cpt_mem_dom_small E r (U.X k) x z hx hz
  obtain ⟨γ', hγ'U, hγ'c, b', hb', he'⟩ := horb γ hγ _ hwd
  have h1 : lact γ' (cpt (U.X k) x z) =
      rmul (cpt (U.X k) x z') (rmul b (ExtFPf.invF (U.X k) b')) := by
    have e1 := congrArg (fun w => rmul w (ExtFPf.invF (U.X k) b')) (he'.symm.trans he)
    simp only [ExtFPf.rmul_assoc, ExtFPf.rmul_invF _ hb', ExtFPf.rmul_oneF] at e1
    exact e1
  have hγ'1 : γ' = 1 := _root_.GlobalTheory.ThickSep.deep_cong_chart_sep E r (U.X k) l.M' x hsd hx hM γ' hγ'U hγ'c z z' hz hz' _
    (ExtFPf.mul_mem _ hb (ExtFPf.invF_mem _ hb')) h1
  subst hγ'1
  rw [FundSetPf.lact_one] at he'
  exact (U.X k).Γ_free γ hγ _ hwd b' hb' he'

theorem modelWt_shape : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ),
    (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp,
    (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧
    (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧
    (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = l1 u1 ∧
    (U.X k).Ψ.card = Nat.card (Psi H) := _root_.GlobalTheory.ModelWtGap.model_weight_gap_l1_card

theorem orth_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (y : Frame X.Ψ r), y ∈ X.dom → ∃ x, IsOrth X x ∧ X.firstMinimumSq x = X.firstMinimumSq y ∧
    ∀ P ∈ X.SS la, P x ≠ 0 → P y ≠ 0 ∧ X.pnorm la P y = X.pnorm la P x := by
  intro E _ _ _ r X la y hy
  obtain ⟨x, hx, b, hb, rfl⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds r X y hy
  have hxd := ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom X hx
  refine ⟨x, hx, (firstMinimumSq_rightBorel X hxd hb).symm, fun P hP hPx =>
    ⟨?_, FrameDegreeData.pnorm_rmul X la P hP.1.1.2.1 x hxd b hb⟩⟩
  rw [hP.1.1.2.1 x hxd b hb]
  refine mul_ne_zero ?_ hPx
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular ((ExtFPf.upper_iff X b τ).mp (hb τ).2)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)

theorem nums (a l C0 PP T D b uE : ℝ) (ha : 1 ≤ a) (hl : 10 ≤ l) (hlC : C0 ≤ l) (hPP : (a * l) ^ 12 ≤ PP)
    (hT : (a * l) ^ 24 ≤ T) (hD : 1 ≤ D) (hrows : PP * T * D ^ 2 * l ≤ b) (hbu : b ≤ uE) :
    T * a ^ 8 ≤ uE ∧ C0 * a ^ 8 ≤ T ∧ 100 * a ^ 4 ≤ b := by
  have h1 : 1 ≤ a * l := by nlinarith
  have hal8 : a ^ 8 ≤ (a * l) ^ 12 :=
    calc a ^ 8 ≤ (a * l) ^ 8 := pow_le_pow_left₀ (by linarith) (by nlinarith) 8
      _ ≤ (a * l) ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have hPP' : a ^ 8 ≤ PP := hal8.trans hPP
  have hT1 : 1 ≤ T := (one_le_pow₀ h1).trans hT
  have hPP0 : 0 ≤ PP := (by positivity : (0 : ℝ) ≤ a ^ 8).trans hPP'
  have hDl : 1 ≤ D ^ 2 * l := by nlinarith [one_le_pow₀ (n := 2) hD]
  have hTPP : T * PP ≤ b := by
    have h2 : T * PP ≤ PP * T * D ^ 2 * l := by
      have h3 : 0 ≤ PP * T := mul_nonneg hPP0 (by linarith)
      nlinarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · calc T * a ^ 8 ≤ T * PP := mul_le_mul_of_nonneg_left hPP' (by linarith)
      _ ≤ uE := hTPP.trans hbu
  · have h4 : a ^ 8 * l ≤ (a * l) ^ 24 := by
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ ha (by norm_num)) (le_self_pow₀ (by linarith) (by norm_num))
        (by linarith) (by positivity)
    have h5 : C0 * a ^ 8 ≤ l * a ^ 8 := mul_le_mul_of_nonneg_right hlC (by positivity)
    linarith
  · have h12 : 100 * a ^ 4 ≤ (a * l) ^ 12 := by
      rw [mul_pow]
      have h6 : (100 : ℝ) ≤ l ^ 12 :=
        calc (100 : ℝ) ≤ 10 ^ 12 := by norm_num
          _ ≤ l ^ 12 := pow_le_pow_left₀ (by norm_num) hl 12
      have h7 : a ^ 4 ≤ a ^ 12 := pow_le_pow_right₀ ha (by norm_num)
      have h8 : 0 ≤ a ^ 4 := by positivity
      nlinarith
    have h9 : PP ≤ T * PP := le_mul_of_one_le_left hPP0 hT1
    linarith

end GlobalTheory.ThickBerg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecAppLETopEq
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.CechKSSmul

theorem valR_mul_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a * b) = valR x O a * valR x O b := by
  simp only [valR, dif_pos h, map_mul]

theorem valR_sub_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a - b) = valR x O a - valR x O b := by
  simp only [valR, dif_pos h, map_sub]

theorem valR_appLE_comp {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ W) (a : Γ(Z, U)) :
    valR x W ((g.appLE U W e).hom a) = valR (x ≫ g) U a := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun y hy => e (h hy)
  simp only [valR, dif_pos h, dif_pos h']
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (q.hom a))
    (Scheme.Hom.appLE_comp_appLE x g U W ⊤ e h)

theorem fromSpec_appLE_top_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem valR_spMap_chart {X : Scheme.{0}} (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (r : Γ(X, U.1)) : valR (spMap φ ≫ chart U) U.1 r = φ r := by
  have h1 : ⊤ ≤ (chart U) ⁻¹ᵁ U.1 := by
    show ⊤ ≤ U.2.fromSpec ⁻¹ᵁ U.1
    rw [U.2.fromSpec_preimage_self]
  rw [← valR_appLE_comp (spMap φ) (chart U) U.1 ⊤ h1 (fun _ _ => trivial)]
  have e : (chart U).appLE U.1 ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    exact fromSpec_appLE_top_eq U.2 h1
  rw [e]
  simp only [valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from fun _ _ => trivial)]
  have e2 : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop :=
    Scheme.Hom.appLE_eq_app (f := spMap φ) (U := ⊤)
  rw [e2]
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom r)) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [this]
  congr 1
  exact (Scheme.ΓSpecIso Γ(X, U.1)).inv_hom_id_apply r

theorem resG_appLE' {Y Z : Scheme.{0}} (f : Y ⟶ Z) {W : Z.Opens} {O O' : Y.Opens} (h : O' ≤ O) (e : O ≤ f ⁻¹ᵁ W)
    (a : Γ(Z, W)) : resG Y h ((f.appLE W O e).hom a) = (f.appLE W O' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

end GlobalTheory.CechKSSmul
end

