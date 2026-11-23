module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Formalism.DoubleCosetMeasures.LatticeCoset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowValuationLtOfIntegralAlgClosurePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MaxIdealPow

variable {Ω : Type} [Field Ω]

theorem aeval_eq_coeff_zero_add (A : ValuationSubring Ω) (g : ℤ[X]) {y : Ω} (hy : y ∈ A) :
    ∃ w ∈ A, aeval y g = ((g.coeff 0 : ℤ) : Ω) + y * w := by
  obtain ⟨r, hr⟩ := X_dvd_sub_C (p := g)
  have hg : g = C (g.coeff 0) + X * r := by rw [← hr]; ring
  refine ⟨((aeval (⟨y, hy⟩ : A) r : A) : Ω), SetLike.coe_mem _, ?_⟩
  have h1 : aeval y r = ((aeval (⟨y, hy⟩ : A) r : A) : Ω) :=
    aeval_algebraMap_apply Ω (⟨y, hy⟩ : A) r
  conv_lhs => rw [hg]
  rw [map_add (f := _), map_mul, aeval_C, aeval_X, h1]
  simp

theorem exists_nat_of_isPlaceOver (E : Type) [Field E] [NumberField E] [Algebra E Ω]
    (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (hP : IsPlaceOver (F := E) A P) :
    ∃ p : ℕ, p ≠ 0 ∧ p ≠ 1 ∧ ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  let I : Ideal ℤ := P.asIdeal.comap (Int.castRingHom (𝓞 E))
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ a ∣ n := by
    intro n
    have h1 := hP (n : 𝓞 E)
    have h2 : (algebraMap E Ω) (((n : 𝓞 E)) : E) = (n : Ω) := by simp
    rw [h2] at h1
    rw [h1]
    have h3 : (n : 𝓞 E) ∈ P.asIdeal ↔ n ∈ I := by simp [I]
    rw [h3, ha, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨k, rfl⟩; exact Dvd.intro_left k rfl
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [smul_eq_mul, mul_comm]⟩
  refine ⟨a.natAbs, ?_, ?_, fun n => by rw [hmem n, Int.natAbs_dvd]⟩
  · intro h0
    have ha0 : a = 0 := Int.natAbs_eq_zero.mp h0
    have hN := Ideal.absNorm_mem P.asIdeal
    have hNv : A.valuation (((Ideal.absNorm P.asIdeal : ℕ) : ℤ) : Ω) < 1 := by
      have h1 := (hP ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)).mpr hN
      simpa using h1
    rw [hmem, ha0, zero_dvd_iff] at hNv
    have : Ideal.absNorm P.asIdeal = 0 := by exact_mod_cast hNv
    exact P.ne_bot (Ideal.absNorm_eq_zero_iff.mp this)
  · intro h1
    have : A.valuation ((1 : ℤ) : Ω) < 1 := by
      rw [hmem, ← Int.natAbs_dvd, h1]; simp
    simp at this

end GlobalTheory.MaxIdealPow

namespace GlobalTheory.MaxIdealPow

theorem exists_pow_lt_valuation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  intro E Ω _ _ _ _ _ A P hP x c hx hc hc0 hvx
  obtain ⟨p, hp0, hp1, hpv⟩ := exists_nat_of_isPlaceOver E A P hP
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hvp : A.valuation (p : Ω) < 1 := by
    have := (hpv p).2 dvd_rfl
    simpa using this
  have hvp0 : A.valuation (p : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hp0
  have hunit : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → A.valuation (n : Ω) = 1 := fun n hn =>
    le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A n))
      (not_lt.1 (fun h => hn ((hpv n).1 h)))
  have hxA : x ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hx
  have hcA : c ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hc

  have hstep2 : ∃ s : ℕ, A.valuation x ^ s ≤ A.valuation (p : Ω) := by
    haveI : Fact (1 < p) := ⟨by omega⟩
    let f := minpoly ℤ x
    have hfm : f.Monic := minpoly.monic hx
    let fb := f.map (Int.castRingHom (ZMod p))
    have hfb0 : fb ≠ 0 := (hfm.map _).ne_zero
    obtain ⟨q, hq, hqX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd fb hfb0 0
    simp only [map_zero, sub_zero] at hq hqX
    set s := rootMultiplicity 0 fb
    have hq0 : q.coeff 0 ≠ 0 := fun h => hqX (X_dvd_iff.mpr h)
    obtain ⟨g, hg⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
    have hker : f - X ^ s * g ∈ RingHom.ker (mapRingHom (Int.castRingHom (ZMod p))) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, hg]
      exact sub_eq_zero.mpr hq
    rw [ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hker
    obtain ⟨h, hh⟩ := hker
    have hev := congrArg (aeval x) hh
    rw [map_sub, map_mul, map_pow, aeval_X, minpoly.aeval, map_mul, aeval_C] at hev
    have hg0 : ¬ (p : ℤ) ∣ g.coeff 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h0; apply hq0; rw [← hg, coeff_map]; simpa using h0
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A g hxA
    have hvg : A.valuation (aeval x g) = 1 := by
      rw [hw, Valuation.map_add_eq_of_lt_left, hunit _ hg0]
      rw [hunit _ hg0, Valuation.map_mul]
      calc A.valuation x * A.valuation w ≤ A.valuation x * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation x := mul_one _
        _ < 1 := hvx
    have hhA : aeval x h ∈ A := by
      obtain ⟨w', hw'A, hw'⟩ := aeval_eq_coeff_zero_add A h hxA
      rw [hw']; exact add_mem (intCast_mem A _) (mul_mem hxA hw'A)
    refine ⟨s, ?_⟩
    have hev2 : x ^ s * aeval x g = -((algebraMap ℤ Ω p) * aeval x h) := by
      rw [← hev]; ring
    have := congrArg A.valuation hev2
    rw [Valuation.map_neg, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hvg,
      mul_one] at this
    rw [this]
    have hp' : (algebraMap ℤ Ω (p : ℤ)) = (p : Ω) := by simp
    rw [hp']
    calc A.valuation (p : Ω) * A.valuation (aeval x h) ≤ A.valuation (p : Ω) * 1 :=
          mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hhA) |>.trans_eq (mul_one _).symm
      _ = A.valuation (p : Ω) := mul_one _

  have hstep3 : ∃ t : ℕ, A.valuation (p : Ω) ^ t ≤ A.valuation c := by
    let f := minpoly ℤ c
    have hf0 : f ≠ 0 := (minpoly.monic hc).ne_zero
    obtain ⟨f₁, hf, hfX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
    simp only [map_zero, sub_zero] at hf hfX
    have ha0 : f₁.coeff 0 ≠ 0 := fun h => hfX (X_dvd_iff.mpr h)
    have hev : aeval c f₁ = 0 := by
      have h1 := minpoly.aeval ℤ c
      change aeval c f = 0 at h1
      rw [hf, map_mul, map_pow, aeval_X] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc0)
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A f₁ hcA
    rw [hev] at hw
    have hle : A.valuation ((f₁.coeff 0 : ℤ) : Ω) ≤ A.valuation c := by
      have he : ((f₁.coeff 0 : ℤ) : Ω) = -(c * w) := by linear_combination -hw
      rw [he, Valuation.map_neg, Valuation.map_mul]
      calc A.valuation c * A.valuation w ≤ A.valuation c * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation c := mul_one _
    have hn0 : (f₁.coeff 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha0
    obtain ⟨t, u, hu, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp1
    refine ⟨t, le_trans (le_of_eq ?_) hle⟩
    have habs : A.valuation ((f₁.coeff 0 : ℤ) : Ω) = A.valuation (((f₁.coeff 0).natAbs : ℤ) : Ω) := by
      rcases Int.natAbs_eq (f₁.coeff 0) with h | h
      · rw [← h]
      · conv_lhs => rw [h]
        rw [Int.cast_neg, Valuation.map_neg]
    rw [habs, hfac]
    have hu1 : A.valuation ((u : ℤ) : Ω) = 1 := hunit u (by exact_mod_cast hu)
    push_cast
    rw [Valuation.map_mul, Valuation.map_pow]
    push_cast at hu1
    rw [hu1, mul_one]
  obtain ⟨s, hs⟩ := hstep2
  obtain ⟨t, ht⟩ := hstep3
  refine ⟨s * (t + 1), ?_⟩
  calc A.valuation x ^ (s * (t + 1)) = (A.valuation x ^ s) ^ (t + 1) := pow_mul _ _ _
    _ ≤ A.valuation (p : Ω) ^ (t + 1) := pow_le_pow_left₀ zero_le' hs _
    _ = A.valuation (p : Ω) ^ t * A.valuation (p : Ω) := pow_succ _ _
    _ < A.valuation (p : Ω) ^ t * 1 :=
        mul_lt_mul_of_pos_left hvp (zero_lt_iff.mpr (pow_ne_zero _ hvp0))
    _ = A.valuation (p : Ω) ^ t := mul_one _
    _ ≤ A.valuation c := ht

end GlobalTheory.MaxIdealPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionToG
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.WholeBaseFinitePart

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

theorem exists_torsion_toG (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [CharZero R] (hR : AdmBase R (maximalIdeal R)) (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom ∧ Flat N.hom ∧ GtTors k g₀ ∧
      (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧
      x₀ ^ k = 1 ∧ FormalEq P.U.toUnifPre x₀ g₀ := by
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt P.D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ P.D.toPre.P k hk
    have h₁' : IsFinite (𝟙 P.D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 P.D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion P.D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt P.D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  obtain ⟨J, hJ⟩ := exists_mulEquiv P.U.toUnifPre hL.globalFns hΦ
  have hN := isAdicColimit_of_isFinite hc (torsion Gt k)
  refine ⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl,
    (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_,
    (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← map_pow, torsionι_pow, map_one]

open GlobalTheory.FinitePartGeneric ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint

theorem generic (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [CharZero R] (hR : AdmBase R (maximalIdeal R)) (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (k : ℕ) (hk : 1 ≤ k) (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N)
    (x₀ : N ⟶ t.G) (hfin : IsFinite N.hom) (htors : x₀ ^ k = 1) (hform : FormalEq P.U.toUnifPre x₀ g₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left) (hx : OverGen F N x)
    (q : QkPt P.D.toPre F k) (hq : q.y = 0) (hg : GtPt.IsPullF F x g₀ q.g) : IsImage P F k q (x ≫ x₀.left) := by
  have hL := firstFiveLaws
  have := hfin
  obtain ⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩ := exists_normal_point R hR F N x hx
  have hφ : Function.Injective φ := fun a b e => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))
  obtain ⟨D', hD, A', U', hU⟩ := UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange
    hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U
  have hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ := hξ.trans (Category.id_comp _).symm
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh g₀
  let x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh))
      (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) =
      ξ ≫ x₀.left := (congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁
  have gG := isGrpPullback_pullback t.G (spMap φ)
  have hk₁ : x₁ ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N := Over.homMk ξ hh
    have e : pushHom gG _ x₁ = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])
  have hp := isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)
  obtain ⟨g', hg'⟩ := FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj t.G :=
    Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F)
      (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)
  have hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      ((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine ⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _)
    (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁
    (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩
  · let xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj
        (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G)) :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩
  · rw [hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]
    exact Category.assoc _ _ _

end GlobalTheory.WholeBaseFinitePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapHypOfNodes
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.Mem.Top.NodeGap

theorem gapHyp_of_nodes (D : D7) (hm : 1801 ≤ D.R.m) (h : ℕ) (hh : 16 * (D.R.r : ℝ) ^ 19 ≤ (h : ℝ))
    (hb : ∀ τ, ∃ b1 : ℤ, ∀ j : Fin D.R.m, (D.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ)) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.m_add_three_le_k
    show 1801 ≤ D.R.k + D.R.m - 1
    omega
  · intro τ j hj
    obtain ⟨b1, hb1⟩ := hb τ
    rw [hb1 ⟨j.1 + 1, hj⟩, hb1 j]
    have h2 : 16 * D.R.r ^ 19 ≤ h := by exact_mod_cast hh
    have h3 : (16 * (D.R.r : ℚ) ^ 19) ≤ (h : ℚ) := by exact_mod_cast h2
    push_cast
    linarith

private theorem ev_mono_of_forall_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  unfold Ev at hp ⊢
  obtain ⟨w, hw, H⟩ := hp
  refine ⟨w, hw, fun eps C8 a b c d => ?_⟩
  obtain ⟨K0, H1⟩ := H eps C8 a b c d
  refine ⟨K0, fun C e f g => ?_⟩
  obtain ⟨c1, H2⟩ := H1 C e f g
  refine ⟨c1, fun cD hc => ?_⟩
  obtain ⟨c2, H3⟩ := H2 cD hc
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H4⟩ := H3 ch hch
  exact ⟨x0, fun K k1 k2 k3 k4 k5 => h K (H4 K k1 k2 k3 k4 k5)⟩

theorem ev_gapHyp : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → Formalism.L2.SG.ConcreteSettingExists.GapHyp X.toD7 := by
  refine ev_mono_of_forall_imp ?_ (ev_nodes 16 19 1801)
  intro K hK X hX
  obtain ⟨hm, h, hh, hb⟩ := hK X hX
  exact gapHyp_of_nodes X.toD7 hm h hh fun τ => (hb τ).imp fun b1 hb1 j => (hb1 j).1

end GlobalTheory.Mem.Top.NodeGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalAtCompletionIntegersChosenUniformiser
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.HD

private theorem lt_one_iff_le_exp_neg_one (g : WithZero (Multiplicative ℤ)) :
    g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

theorem isLocalAt_adicCompletionIntegers_uniformizer (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsLocalAt (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) := by
  have hv : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)
      = WithZero.exp (-1 : ℤ) := unif_spec P
  have hne : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≠ 0 := Units.ne_zero _
  have mem : ∀ x : P.adicCompletion L, x ∈ OP P ↔ Valued.v x ≤ 1 := fun x =>
    HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 L) (K := L) (v := P)
  have hexp : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) :=
    zero_lt_iff.2 WithZero.exp_ne_zero
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := (mem _).1 h
    rw [map_inv₀, hv, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · intro x hx hnot
    have hx1 : Valued.v x ≤ 1 := (mem x).1 hx
    have hx_eq : Valued.v x = 1 := by
      by_contra hne1
      have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne1
      have hle := (lt_one_iff_le_exp_neg_one _).1 hlt
      refine hnot (((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)⁻¹ * x) ?_ ?_
      · rw [mem, map_mul, map_inv₀, hv]
        exact inv_mul_le_one_of_le₀ hle hexp.le
      · rw [mul_inv_cancel_left₀ hne]
    rw [mem, map_inv₀, hx_eq, inv_one]

end GlobalTheory.Mem.HD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem descend_exists (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∃ Φ : S.WL j →+ FmT D T S i j b, (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) ∧
      (∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x)) ∧
      ∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w := by
  obtain ⟨n, bs, hb, -, hKs, hLi, hLs⟩ := In.ks j h1 h2
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  exact _root_.GlobalTheory.exists_semilinear_descent_to_baseChange D.LL0 S.kKs S.kKs_spec (WKr D S j) bs (fun k => hW ▸ hb k) (hW ▸ hKs) hLi hLs
    (KT := KT D T i b) (readK D T i b) (fun s => rfl)

theorem descend_actL (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hf : ∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x))
    (g : G0g D.nd) (x : S.WL j) :
    Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x) := by
  have hcR : cR D S In.chi j (S.eG.symm g) = chiL S j (In.chi j h1 h2) (S.eG.symm g) := by
    unfold cR; rw [dite_eq_left ⟨h1, h2⟩]
  change _ = ((readK D T i b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
    Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g))) (Φ x)
  rw [hcR]
  have e1 : actL D S j g x = (((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) •
      (S.A j).ρ (S.eG.symm g) x := by
    simp only [actL, chiL, IntermediateField.coe_inv, LinearMap.smul_apply]
  rw [e1, hc, hf ((S.A j).ρ (S.eG.symm g)) (rhoR D S In.rho j (S.eG.symm g)) (fun w => rfl), map_inv₀]
  rfl

theorem descend_eSum (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) :
    Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x) := by
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum]
  unfold eGT
  rw [MonoidAlgebra.lift_apply]
  simp only [eAlgT, MonoidAlgebra.coeff_ofCoeff]
  rw [Finsupp.sum_fintype _ _ (by intro; simp), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, hc, ha]
  simp

theorem descend_mem_V0T (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (he : ∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x))
    (x : S.WL j) (hx : x ∈ goodL D S In.θ j) : Φ x ∈ V0T D T S In.rho In.chi In.θ i j b := by
  rw [goodL, Submodule.mem_inf, Submodule.mem_iInf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨Φ x, ?_, ?_⟩
  · rw [SetLike.mem_coe, Fm0T, Submodule.mem_iInf]
    intro u
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    have h := hx2 u
    rw [Module.End.mem_eigenspace_iff] at h
    rw [LinearEquiv.coe_coe, ← ha, h, hc]
    simp [psiUT]
  · rw [Module.End.mem_eigenspace_iff, one_smul] at hx1
    rw [← he, hx1]

theorem descend_mem_eigenspace (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hf : ∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x))
    (k : ℕ) (P : PlE D.host) (μ : ↥D.LL0) (x : S.WL j)
    (hx : x ∈ Module.End.eigenspace (In.hL j k P) (μ : D.what₂.LL)) :
    Φ x ∈ Module.End.eigenspace (hkT D T S In i j b k P)
      (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b μ) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hw : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  change ((show KT D T i b from algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k •
    LinearMap.baseChange (KT D T i b) (hLr D S In j k P) (Φ x) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = _
  rw [← hf _ _ hw, hx, hc]
  exact smul_smul _ _ _

end GlobalTheory.HeightCounting.FormsStep
end
end

