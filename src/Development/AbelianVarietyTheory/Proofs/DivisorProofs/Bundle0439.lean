module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplittingFw
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAffineLineMorphismToProperAcrossPoint
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffineLineExt

open Polynomial

theorem isPrincipalIdealRing_away {R : Type} [CommRing R] [IsPrincipalIdealRing R] (r : R) :
    IsPrincipalIdealRing (Localization.Away r) := ⟨fun J => by
  rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) J]
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal
  rw [ha]
  exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩

theorem extend : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  intro k _ B _ _ P c hP u hu
  have hQ0 : P * (X - C c) ≠ 0 := mul_ne_zero hP (X_sub_C_ne_zero c)
  haveI : IsDomain (Localization.Away P) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  haveI : IsDomain (Localization.Away (P * (X - C c))) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hQ0)
  haveI : IsPrincipalIdealRing (Localization.Away P) := isPrincipalIdealRing_away P
  have hφ : ∀ a : k[X], IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c) (algebraMap k[X] (Localization.Away P) a) =
      algebraMap k[X] (Localization.Away (P * (X - C c))) a :=
    IsLocalization.Away.awayToAwayRight_eq P (X - C c)
  have hcomp : spMap (algebraMap k[X] (Localization.Away (P * (X - C c)))) =
      spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  haveI : IsOpenImmersion (spMap (algebraMap k[X] (Localization.Away P))) :=
    IsOpenImmersion.of_isLocalization P
  haveI : IsOpenImmersion (spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P))) := by
    rw [← hcomp]
    exact IsOpenImmersion.of_isLocalization (P * (X - C c))
  haveI := IsOpenImmersion.of_comp (spMap (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)))
    (spMap (algebraMap k[X] (Localization.Away P)))
  haveI : B.left.IsSeparated := ⟨by
    rw [show terminal.from B.left = B.hom ≫ terminal.from (Sp k) from terminal.hom_ext _ _]
    infer_instance⟩
  have hu' : u ≫ B.hom = spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k (Localization.Away P)) := by
    rw [hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away P), hφ,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, h1, h2⟩ := TorusConst.exists_extension (Z := Sp (Localization.Away P))
    (fun x => TorusConst.valuationRing_stalk (Localization.Away P) x) _
    (spMap (algebraMap k (Localization.Away P))) B.hom u hu'
  exact ⟨g, h2, h1⟩

end GlobalTheory.AffineLineExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsTateTwistResolutionHomExtAugmentati
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem secMap_res' {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.hom.naturality g.op)) x).symm

theorem secMap_nsmul' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map f (c • x) = c • Sec.map f x :=
  map_nsmul (f.hom.app (op U)).hom c x

theorem secMap_zero' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} :
    Sec.map f (0 : Sec F U) = 0 :=
  map_zero (f.hom.app (op U)).hom

theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {M : Shv S} (a b : (extSh φ).obj F ⟶ M)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map a (extSh.sec φ F U y) = Sec.map b (extSh.sec φ F U y)) : a = b := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    a.hom b.hom M.property ?_
  ext U : 2
  apply ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext y
  exact h (unop U) y

end

theorem extAug_comp_ext : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q))
    (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
      Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) =
        Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) →
    extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  intro Q q _ hq i K u u' h
  have e : ∀ (v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K) (V : Scheme.{0}) (z : Sec (tw Q i) V),
      Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0)
          (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) V z) =
        Sec.map (v.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app V 0 (Sec.map (resι _ (tw Q i)) z)) := by
    intro v V z
    change Sec.map (v.f 0) (Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i))) _) = _
    rw [extSh.sec_map]
    rfl
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u.f 0 =
      (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u'.f 0 := by
    apply extSh_hom_ext
    intro U y
    apply (_root_.GlobalTheory.EtC.sec_ext_glue _ (K.X 0) U).1
    obtain ⟨S, hS, hy⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).1 U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [secMap_res', secMap_res', extSh.sec_res, e, e]
    rcases hy V g hg with h0 | ⟨ζ, c, hc⟩
    · rw [h0, secMap_zero', map_zero, secMap_zero', secMap_zero']
    · rw [hc, secMap_nsmul', map_nsmul, secMap_nsmul', secMap_nsmul']
      exact congrArg (c • ·) (h V ζ)
  have hv : ∀ v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K, (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ v).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0 := by
    intro v
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        v.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ v.f 0) hs').trans (Category.assoc _ _ _)
  apply HomologicalComplex.from_single_hom_ext
  rw [hv, hv, key]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology

namespace GlobalTheory.CMVal.OrderUnits

variable {E : Type} [Field E] [NumberField E]

theorem ball_mem_nhds (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z : P.adicCompletion E) :
    {x : P.adicCompletion E | Valued.v (x - z) ≤ WithZero.exp (-(n : ℤ))} ∈ 𝓝 z := by
  set t : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) ^ n with ht
  have hv : Valued.v (t : P.adicCompletion E) = WithZero.exp (-(n : ℤ)) := by
    have h2 : Valued.v ((Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) : (P.adicCompletion E)ˣ) : P.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec P
    rw [ht, Units.val_pow_eq_pow_val, map_pow, h2, ← WithZero.exp_nsmul]
    simp
  have hc : Continuous fun x : P.adicCompletion E => (x - z) / (t : P.adicCompletion E) := by fun_prop
  have ho := (Valued.isOpen_valuationSubring (P.adicCompletion E)).preimage hc
  refine mem_of_superset (ho.mem_nhds ?_) ?_
  · show (z - z) / (t : P.adicCompletion E) ∈ Valued.v.valuationSubring
    rw [sub_self, zero_div]; exact zero_mem _
  · intro x hx
    have hx' : Valued.v ((x - z) / (t : P.adicCompletion E)) ≤ 1 := hx
    rw [map_div₀, hv, div_le_one₀ (WithZero.exp_pos)] at hx'
    exact hx'

theorem val_int_le (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (b : 𝓞 E) (hb : b ∈ P.asIdeal ^ n) :
    Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (P.intValuation_le_pow_iff_mem b n).2 hb

theorem exists_cong {c : Ideal (OF E)} (v : HeightOneSpectrum (OF E)) (n : ℕ) (hn : v.asIdeal ^ n ∣ c)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P ∈ S, Over P v) {z : Af E} (hz : z ∈ hatO c) :
    ∃ a : OF E, ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
  have hev : ∀ P : HeightOneSpectrum (𝓞 E), Continuous fun z : Af E => z P := fun P =>
    RestrictedProduct.continuous_eval P
  have hU : ∀ᶠ x : Af E in 𝓝 z, ∀ P ∈ S, Valued.v (x P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [Filter.eventually_all_finset]
    intro P _
    exact (hev P).tendsto z (ball_mem_nhds P n (z P))
  have hz1 : z ∈ closure (((orderC c).map (algebraMap E (Af E)) : Subring (Af E)) : Set (Af E)) := hz
  obtain ⟨x, ⟨k, hk, rfl⟩, hx⟩ := ((mem_closure_iff_frequently.1 hz1).and_eventually hU).exists
  obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hk
  refine ⟨a, fun P hP => ?_⟩
  have hb' : b ∈ P.asIdeal ^ n := by
    have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ n := by
      refine (Ideal.map_mono (Ideal.le_of_dvd hn)).trans ?_
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      exact (hS P hP).ge
    exact h1 hb
  have h2 := val_int_le P n b hb'
  have h3 := hx P hP
  rw [map_add (f := _)] at h3
  have h4 : algebraMap E (Af E) (algebraMap (OF E) E a) P - z P =
      ((algebraMap E (Af E) (algebraMap (OF E) E a) + algebraMap E (Af E) (algebraMap (𝓞 E) E b)) P - z P) -
        algebraMap E (Af E) (algebraMap (𝓞 E) E b) P := by
    change _ = (algebraMap E (Af E) (algebraMap (OF E) E a) P + algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z P) - _
    ring
  rw [h4]
  exact Valuation.map_sub_le _ h3 h2

theorem val_le_one {c : Ideal (OF E)} {z : Af E} (hz : z ∈ hatO c) (P : HeightOneSpectrum (𝓞 E)) : Valued.v (z P) ≤ 1 := by
  obtain ⟨a, ha⟩ := exists_cong (P.under (OF E)) 0 (by simp) {P} (fun P' hP' => by
    rw [Finset.mem_singleton.1 hP']; rfl) hz
  have h1 := ha P (Finset.mem_singleton_self P)
  have h2 := val_int_le P 0 (algebraMap (OF E) (𝓞 E) a) (by simp)
  have h3 : z P = algebraMap E (Af E) (algebraMap (OF E) E a) P - (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) := by
    ring
  rw [h3]
  exact (Valuation.map_sub_le _ h2 h1).trans_eq (by simp)

theorem val_eq_one {c : Ideal (OF E)} {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) P) = 1 := by
  have h1 := val_le_one (mem_hatOUnits.1 hy).1 P
  have h2 := val_le_one (mem_hatOUnits.1 hy).2 P
  have h3 : Valued.v ((y : Af E) P) * Valued.v ((↑y⁻¹ : Af E) P) = 1 := by
    rw [← map_mul]
    exact (congrArg Valued.v (coord P y).val_inv).trans (map_one _)
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((y : Af E) P) * 1 := by gcongr
      _ = _ := mul_one _)

theorem finPart_eq_one_of_level {c : Ideal (OF E)} {χ : HChar E} (hF : TrivOnF χ)
    (hl : ∀ v : HeightOneSpectrum (OF E), ∃ n : ℕ, v.asIdeal ^ n ∣ c ∧ ∀ P, Over P v → LevelLe χ P n)
    {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) : finPart χ y = 1 := by
  refine Fibre.finPart_eq_one_of_fibres E χ y fun v => ?_
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hO : ∀ P ∈ S, Over P v := fun P hP => by
    rw [hS] at hP
    unfold Formalism.L2.Host.aboveF at hP
    rw [Set.Finite.mem_toFinset] at hP
    have : P.under (OF E) = v := hP
    rw [← this]; rfl
  obtain ⟨n, hn, hlev⟩ := hl v
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Finset.prod_eq_one fun P hP => (χ.unrAt_iff P).2 (hlev P (hO P hP)) _ (val_eq_one hy P)
  obtain ⟨a, ha⟩ := exists_cong v n hn S hO (mem_hatOUnits.1 hy).1
  have hva : ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P) = 1 := fun P hP => by
    have hlt : Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - (y : Af E) P) < Valued.v ((y : Af E) P) := by
      rw [val_eq_one hy P]
      refine (ha P hP).trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, val_eq_one hy P]
  by_cases h0 : algebraMap (OF E) E a = 0
  · refine Finset.prod_eq_one fun P hP => ?_
    have h1 := hva P hP
    rw [h0, map_zero] at h1
    exact absurd (h1.symm.trans (map_zero _)) one_ne_zero
  let k' : (maximalRealSubfield E)ˣ := Units.mk0 (a : maximalRealSubfield E)
    (fun h1 => h0 (congrArg Subtype.val h1))
  have h2 := hF.1 v k'
  unfold Formalism.L2.Host.HChar.resFin at h2
  rw [MonoidHom.finsetProd_apply] at h2
  rw [← h2]
  refine Finset.prod_congr rfl fun P hP => ?_
  set u : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) k') with hu
  have hu' : (u : P.adicCompletion E) = algebraMap E (Af E) (algebraMap (OF E) E a) P := rfl
  have hvu : Valued.v (u : P.adicCompletion E) = 1 := hva P hP
  show χ.loc P (coord P y) = χ.loc P u
  have h3 : χ.loc P (u / coord P y) = 1 := by
    refine hlev P (hO P hP) _ ?_ ?_
    · show Valued.v ((u / coord P y : (P.adicCompletion E)ˣ) : P.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, hvu, coe_coord, val_eq_one hy P, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one (coord P y).ne_zero, map_div₀, coe_coord, val_eq_one hy P, div_one, hu']
      exact ha P hP
  rw [map_div, div_eq_one] at h3
  exact h3.symm

theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E),
    UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ →
      ∀ y ∈ hatOUnits (condQ 𝔣 Q), finPart χ y = 1 := by
  intro E _ _ _ I _ φ _ s κ 𝔣 Q χ _ _ _ hχ y hy
  refine finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hy
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

end GlobalTheory.CMVal.OrderUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLaRingOfIntegers
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

theorem Datum.finrank_La_ringOfIntegers :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p),
      letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
      Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  intro p _ D
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  letI iV : Module (𝓞 D.F) D.VF := Module.compHom D.VF (algebraMap (𝓞 D.F) D.F)
  haveI : IsScalarTower (𝓞 D.F) D.F D.VF :=
    ⟨fun c x v => by
      show (algebraMap (𝓞 D.F) D.F c * x) • v = algebraMap (𝓞 D.F) D.F c • (x • v)
      rw [mul_smul]⟩
  let f : D.La →ₗ[𝓞 D.F] D.VF :=
    { toFun := fun z => (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF)
      map_add' := fun z w => TensorProduct.tmul_add _ _ _
      map_smul' := fun c z => by
        rw [RingHom.id_apply]
        show (((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O c • z) : D.VQ) : D.VF) =
          algebraMap (𝓞 D.F) D.F c • (show D.VF from (1 : ℚ) ⊗ₜ z)
        rw [D.smul_VF, show algebraMap (𝓞 D.F) D.F c = (c : D.F) from rfl, D.actF_coe, D.coe_actInt]
        rfl }
  have hf : ∀ z, f z = (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF) := fun _ => rfl

  have hnat : ∀ (n : ℕ) (v : D.VF), ((n : 𝓞 D.F)) • v = n • v := by
    intro n v
    show algebraMap (𝓞 D.F) D.F (n : 𝓞 D.F) • v = n • v
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) f := by
    constructor
    · rintro ⟨c, hc⟩
      have hc0 : (c : D.F) ≠ 0 := by
        intro h
        exact (mem_nonZeroDivisors_iff_ne_zero.1 hc) (by exact_mod_cast h)
      rw [Module.End.isUnit_iff]
      constructor
      · intro v w h
        have h' : (c : D.F) • v = (c : D.F) • w := h
        exact smul_right_injective D.VF hc0 h'
      · intro v
        refine ⟨(c : D.F)⁻¹ • v, ?_⟩
        show (c : D.F) • ((c : D.F)⁻¹ • v) = v
        rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    · intro y
      obtain ⟨q, z, -, hy⟩ := D.exists_tmul y
      have hd : ((q.den : ℕ) : 𝓞 D.F) ∈ nonZeroDivisors (𝓞 D.F) :=
        mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)
      refine ⟨(q.num • z, ⟨_, hd⟩), ?_⟩
      show ((q.den : ℕ) : 𝓞 D.F) • y = f (q.num • z)
      rw [hnat, hf, hy]
      show q.den • (q ⊗ₜ z : D.VQ) = ((1 : ℚ) ⊗ₜ (q.num • z) : D.VQ)
      rw [TensorProduct.smul_tmul', nsmul_eq_mul, Rat.den_mul_eq_num, ← TensorProduct.smul_tmul,
        zsmul_eq_mul, mul_one]
    · intro z w h
      rw [hf, hf] at h
      obtain ⟨⟨c, hc⟩, hcz⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
        (TensorProduct.mk ℤ ℚ D.La 1)).1 h
      have hc0 : ((c : ℤ) : 𝓞 D.F) ≠ 0 := by
        exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.1 hc
      refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
      show algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • z = algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • w
      rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact hcz
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 D.F)) f le_rfl
  have h2 := IsFractionRing.finrank_right_eq (𝓞 D.F) D.F D.VF
  rw [← h1, ← h2, D.finrank_VF]

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstFunctionalIntegralSmoothCompact
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_nil_eq_integral_smooth : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∃ α : G → ℂ, h.IsSmoothFun α ∧ HasCompactSupport α ∧ ∀ f ∈ S, ∫ y, f y * α y ∂μ = Λ [] f := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hSc hSt K hK Λ hΛ
  haveI := hμ
  haveI : LocallyCompactSpace G := IsExpLieAlgebra.locallyCompactSpace (h := h)
  haveI : SecondCountableTopology G := IsExpLieAlgebra.secondCountableTopology (h := h)
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp_tsupport μ b
  obtain ⟨N, Λ', κ, hκ, hsum⟩ := _root_.GlobalTheory.HCA.SmFn.exists_decomp_prodExp 𝔸 G 𝔤 h d b μ hμ S hSc hSt K hK ε hε d id Λ hΛ
  choose κ' hκ'sm hκ'cs _ hκ'int using fun m => hdens (κ m) (hκ m).2.1 (hκ m).2.2
  have hKμ : μ K < ⊤ := hK.measure_lt_top
  choose C hC using fun m => (hκ m).1.bdd []
  choose a ha using fun m => _root_.GlobalTheory.exists_integrable_density_of_bound_by_integral_compact G μ K hK hKμ S hSc (Λ' m []) (C m) ((hκ m).1.lin []) (hC m)
  have hκ'is : ∀ m, h.IsSmoothFun (κ' m) := fun m => hκ'sm m
  have hκ'c : ∀ m, Continuous (κ' m) := fun m => by
    letI := h.chartedSpace; exact (hκ'sm m).continuous
  have hconv := fun m => _root_.GlobalTheory.ConvSmooth.conv_smooth_compactSupport 𝔸 G 𝔤 h μ hμ K hK (κ' m) (a m) (hκ'is m) (hκ'cs m) (ha m).1 (ha m).2.1 (ha m).2.2.1
  refine ⟨fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ, ?_, ?_, ?_⟩
  · have e : (fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) =
        ∑ m, (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := by
      ext z; simp [Finset.sum_apply]
    rw [e]
    exact h.mem_smoothFuns.1 (Submodule.sum_mem (h.smoothFuns (F := ℂ)) fun m _ => h.mem_smoothFuns.2 (hconv m).1)
  · have e : (fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) =
        ∑ m, (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := by
      ext z; simp [Finset.sum_apply]
    rw [e]
    exact Finset.sum_induction _ HasCompactSupport (fun _ _ hu hv => hu.add hv) HasCompactSupport.zero
      fun m _ => (hconv m).2
  · intro f hf
    have hcc : ∀ m, Continuous (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := fun m => by
      letI := h.chartedSpace; exact (hconv m).1.continuous
    have hint : ∀ m, Integrable (fun z => f z * ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) μ := fun m =>
      ((hSc f hf).mul (hcc m)).integrable_of_hasCompactSupport (hconv m).2.mul_left
    calc ∫ y, f y * (∑ m, ∫ x, κ' m x * a m (x⁻¹ * y) ∂μ) ∂μ
        = ∑ m, ∫ y, f y * ∫ x, κ' m x * a m (x⁻¹ * y) ∂μ ∂μ := by
          simp_rw [Finset.mul_sum]; exact integral_finsetSum _ fun m _ => hint m
      _ = ∑ m, ∫ x, κ' m x * Λ' m [] (fun y => f (x * y)) ∂μ := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [GlobalTheory.T.integral_mul_convolution_eq_alt G μ hμ K hK (κ' m) (a m) (hκ'c m) (hκ'cs m) (ha m).1 (ha m).2.1 (ha m).2.2.1 f (hSc f hf)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          have hx := (ha m).2.2.2 _ (hSt f hf x)
          simp only at hx ⊢
          rw [hx]
      _ = ∑ m, ∫ t, κ m t * Λ' m [] (fun y => f (h.prodExp (fun k => b (id k)) t * y)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          exact hκ'int m _ (_root_.GlobalTheory.HCA.SmFn.continuous_leftTranslate 𝔸 G 𝔤 h d b μ hμ S hSc hSt K hK (Λ' m) (hκ m).1 [] f hf)
      _ = Λ [] f := (hsum f hf).symm

end GlobalTheory.HCA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH1BijectiveStatement
section
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forget_positive_h1_bijective : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), K.M1.Ac0 → K.M1.Ac1 → K.M2.Ac0 → Function.Bijective K.fnMap.h1 := by
  first | exact @GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | exact GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | (intros; apply GlobalTheory.CxCoh.Cx.fnMap_h1_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH2BijectiveStatement
section
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forget_positive_h2_bijective : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), K.M1.Ac1 → K.M1.Ac2 → K.M2.Ac0 → K.M2.Ac1 → K.M3.Ac0 → Function.Bijective K.fnMap.h2 := by
  first | exact @GlobalTheory.CxCoh.fnMap_h2_bijective | exact GlobalTheory.CxCoh.fnMap_h2_bijective | (intros; apply GlobalTheory.CxCoh.fnMap_h2_bijective <;> assumption)
end

