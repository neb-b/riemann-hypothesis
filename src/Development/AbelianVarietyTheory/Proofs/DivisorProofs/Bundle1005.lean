module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivJacobson

theorem exists_specializes {R : Type} [CommRing R] {J : Ideal R} (hJ : J ≤ Ideal.jacobson ⊥)
    (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum (R ⧸ J), p ⤳ PrimeSpectrum.comap (Ideal.Quotient.mk J) q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : J ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem kTriv_of_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (J : Ideal R), J ≤ Ideal.jacobson ⊥ → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → RelAmple B M → ∀ (Y₀ : Over (Spec (CommRingCat.of (R ⧸ J)))) [GrpObj Y₀] (b : Y₀.left ⟶ B.left), IsGrpPullback Y₀ B (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) b → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → KTriv Y₀ N₀ → KTriv B M := by
  intro R _ _ J hJ B _ hB M hM hA Y₀ _ b hb N₀ hN₀ e hK
  have key : ∀ p : Spec (CommRingCat.of R), ∃ U : (Spec (CommRingCat.of R)).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj B) (M.pull (pullback.fst B.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL := fun p => LB.isLB_pull hM (pullback.fst B.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U B _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback B (U p).ι) _ _ hM hL (fun p => GlobalTheory.lbIso_refl (hL p)) hB
    (fun p => GlobalTheory.isAbelianScheme_pullback_obj (U p).ι B hB) hK

end GlobalTheory.KTrivJacobson
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
section
noncomputable section

namespace GlobalTheory.UnrEuler

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]




end GlobalTheory.UnrEuler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEpsilonFactorTameFiniteOrderTwist
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

noncomputable section

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem pow_apply_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (x : Ideles E) : ((ξ.1 x : ℂˣ) : ℂ) ^ N = 1 := by
  have h1 : ((ξ ^ N : HChar E).1 x) = (ξ.1 x) ^ N := by
    rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
  rw [← Units.val_pow_eq_pow_val, ← h1, h]
  rfl

theorem locK_pow_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ((ξ.locK w x : ℂˣ) : ℂ) ^ N = 1 :=
  pow_apply_eq_one h _

theorem isUnitary_of_orderDvd {ξ : HChar E} {N : ℕ} (hN : 0 < N) (h : ξ.OrderDvd N) : IsUnitary ξ := fun x =>
  Complex.norm_eq_one_of_pow_eq_one (pow_apply_eq_one h x) hN.ne'

theorem expAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : χ.UnrAt w) (hξ : ExpAt ξ w a) :
    ExpAt (χ * ξ) w a := by
  intro k
  have hk : χ.LevelLe w k := hχ.levelLe k
  refine ⟨fun hx => (hξ k).1 ?_, fun hn => hk.mul ((hξ k).2 hn)⟩
  have := hk.inv.mul hx
  rwa [inv_mul_cancel_left] at this

theorem psiAt_natMul (w : HeightOneSpectrum (𝓞 E)) (t : w.adicCompletion E) (k : ℕ) :
    psiAt w ((k : w.adicCompletion E) * t) = psiAt w t ^ k := by
  induction k with
  | zero => simpa using psiAt_eq_one (w := w) (t := 0) (by simp)
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, psiAt_add, ih, pow_succ]

theorem gaussSumAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w) {a : ℕ} (ha : a ≠ 0) (c : Eˣ) :
    gaussSumAt (χ * ξ) w a c = gaussSumAt ξ w a c := by
  unfold gaussSumAt
  congr 1
  funext y
  have hy := out_notMem w ha y
  have hy1 : w.valuation E ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) = 1 :=
    (w.valuation_eq_one_iff_notMem (K := E)).2 hy
  have hz0 : ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) ≠ 0 := fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  rw [gaussTerm, gaussTerm, dite_eq_right hz0, dite_eq_right hz0]
  have h1 : χ.locK w (Units.mk0 _ hz0) = 1 := by
    refine hχ _ ?_
    show Valued.v (((atFin w (Units.mk0 _ hz0)) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    simp only [atFin, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_mk0]
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval, hy1]
  have e : (χ * ξ).locK w (Units.mk0 _ hz0) = χ.locK w (Units.mk0 _ hz0) * ξ.locK w (Units.mk0 _ hz0) := rfl
  rw [e, h1, one_mul]

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem exists_gaussSumAt_dvd {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {q N : ℕ} (hq : q.Prime) (hqw : Ideal.absNorm w.asIdeal = q) (hN : 0 < N) (hξN : ξ.OrderDvd N) (hξ : ExpAt ξ w 1)
    (hξK : ∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) (hqK : ∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) :
    ∃ g : 𝓞 K, σ (g : K) = gaussSumAt ξ w 1 (unif w ^ (1 + diffExp w)) ∧ g ∣ (q : 𝓞 K) := by
  classical
  set c : Eˣ := unif w ^ (1 + diffExp w) with hc
  haveI : Fintype (𝓞 E ⧸ w.asIdeal ^ 1)ˣ := Fintype.ofFinite _
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hqv : w.valuation E ((q : 𝓞 E) : E) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have h := valuation_sub_le (w := w) (a := 1) (y := (q : 𝓞 E)) (y' := 0)
      (by rw [sub_zero, pow_one, ← hqw]; exact Ideal.absNorm_mem _)
    simpa using h
  have hterm : ∀ y : (𝓞 E ⧸ w.asIdeal ^ 1)ˣ, ∃ x : K,
      σ x = gaussTerm ξ w c ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1) : 𝓞 E) : E) ∧ x ^ (N * q) = 1 := by
    intro y
    have hy := out_notMem w one_ne_zero y
    set z : 𝓞 E := Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1)
    have hy1 : w.valuation E (z : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
    have hz0 : (z : E) ≠ 0 := fun h => by
      rw [h, map_zero] at hy1
      exact zero_ne_one hy1
    rw [gaussTerm, dite_eq_right hz0]
    obtain ⟨x1, hx1⟩ := hξK (Units.mk0 _ hz0)⁻¹
    have hp : psiAt w (algebraMap E (w.adicCompletion E) ((z : E) / c)) ^ q = 1 := by
      rw [← psiAt_natMul]
      apply psiAt_eq_one
      have e : ((q : ℕ) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) ((z : E) / c) =
          algebraMap E (w.adicCompletion E) (((q : 𝓞 E) : E) * ((z : E) / c)) := by simp
      rw [e, hval, map_mul, map_div₀, hy1, hc, valuation_unif_pow, one_div, ← div_eq_mul_inv,
        div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
      convert hqv using 2
      push_cast
      ring
    obtain ⟨x2, hx2⟩ := hqK _ hp
    have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
    have hx2q : x2 ^ q = 1 := σ.injective (by rw [map_pow, hx2, hp, map_one])
    refine ⟨x1 * x2, by rw [map_mul, hx1, hx2, map_inv], ?_⟩
    rw [mul_pow, pow_mul, hx1N, one_pow, one_mul, mul_comm N q, pow_mul, hx2q, one_pow]
  choose X hX using hterm
  have hpos : 0 < N * q := Nat.mul_pos hN hq.pos
  have hXi : ∀ y, IsIntegral ℤ (X y) := fun y => IsIntegral.of_pow hpos (by rw [(hX y).2]; exact isIntegral_one)
  have hXi' : ∀ y, IsIntegral ℤ (X y)⁻¹ := fun y =>
    IsIntegral.of_pow hpos (by rw [inv_pow, (hX y).2, inv_one]; exact isIntegral_one)
  have hnorm : ∀ y, ‖σ (X y)‖ = 1 := fun y =>
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, (hX y).2, map_one]) hpos.ne'
  have hgi : IsIntegral ℤ (∑ y, X y) := IsIntegral.sum _ fun y _ => hXi y
  have hgi' : IsIntegral ℤ (∑ y, (X y)⁻¹) := IsIntegral.sum _ fun y _ => hXi' y
  have hσg : σ (∑ y, X y) = gaussSumAt ξ w 1 c := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, gaussSumAt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun y _ => (hX y).1
  have hσg' : σ (∑ y, (X y)⁻¹) = starRingEnd ℂ (gaussSumAt ξ w 1 c) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hσg, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [map_inv₀, Complex.inv_eq_conj (hnorm y)]
  have hu : IsUnitary ξ := isUnitary_of_orderDvd hN hξN
  have hG := GlobalTheory.GaussMod.gaussSumAt_normSq ξ w 1 c one_ne_zero hξ hu (valuation_unif_pow w _)
  have hprod : (∑ y, X y) * (∑ y, (X y)⁻¹) = (q : K) := σ.injective (by
    rw [map_mul, hσg, hσg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hG, hqw, map_natCast]
    push_cast
    ring)
  refine ⟨⟨_, hgi⟩, hσg, ⟨⟨_, hgi'⟩, RingOfIntegers.ext ?_⟩⟩
  have e : ((q : 𝓞 K) : K) = (q : K) := by simp
  rw [e, ← hprod]
  rfl

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

theorem locEps_tame_twist : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q m N : ℕ) (s : ℤ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → q ∣ m → 0 < N → ξ.OrderDvd N → χ.UnrAt w → ExpAt ξ w 1 → (∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) → (∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) → s ≤ 0 → ExpAt (χ * ξ) w 1 ∧ ∃ g : K, GlobalTheory.Square.IsAwayUnit m g ∧ locEps (χ * ξ) w 1 (s : ℂ) = σ g * ((χ.val w : ℂˣ) : ℂ) * locEps χ w 0 (s : ℂ) := by
  intro E _ _ K _ _ _ σ χ ξ w q m N s hq hcard hqm hN hξN hχ hξ hξK hqK hs
  have hqw : Ideal.absNorm w.asIdeal = q := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hcard
  refine ⟨expAt_unr_mul hχ hξ, ?_⟩
  obtain ⟨gG, hgG, hdvd⟩ := exists_gaussSumAt_dvd σ hq hqw hN hξN hξ hξK hqK
  obtain ⟨x1, hx1⟩ := hξK (unif w ^ (1 + diffExp w))
  have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
  have hx1i : IsIntegral ℤ x1 := IsIntegral.of_pow hN (by rw [hx1N]; exact isIntegral_one)
  set a1 : 𝓞 K := ⟨x1, hx1i⟩ with ha1d
  have ha1 : IsUnit a1 := by
    have e : ((a1 : 𝓞 K) : K) = x1 := rfl
    exact IsUnit.of_pow_eq_one (RingOfIntegers.ext (by push_cast; exact (congrArg (· ^ N) e).trans hx1N)) hN.ne'
  have hqm' : (q : 𝓞 K) ∣ (m : 𝓞 K) := Nat.cast_dvd_cast hqm
  refine ⟨x1 * (q : K) ^ (-s).toNat * (gG : K), ?_, ?_⟩
  · have h1 : GlobalTheory.Square.IsAwayUnit m x1 := GlobalTheory.Square.IsAwayUnit.of_dvd (a := a1) (k := 0) (by simpa using ha1.dvd)
    have h2 : GlobalTheory.Square.IsAwayUnit m ((q : K) ^ (-s).toNat) := by
      have := GlobalTheory.Square.IsAwayUnit.of_dvd (K := K) (m := m) (a := (q : 𝓞 K) ^ (-s).toNat) (pow_dvd_pow_of_dvd hqm' _)
      simpa using this
    have h3 : GlobalTheory.Square.IsAwayUnit m (gG : K) := GlobalTheory.Square.IsAwayUnit.of_dvd (k := 1) (by rw [pow_one]; exact hdvd.trans hqm')
    exact (h1.mul h2).mul h3
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hj : (((-s).toNat : ℕ) : ℂ) = -(s : ℂ) := by
      have : (((-s).toNat : ℕ) : ℤ) = -s := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have e1 : ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((1 + diffExp w : ℕ) : ℂ)) =
        ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((0 + diffExp w : ℕ) : ℂ)) * (q : ℂ) ^ ((-s).toNat) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, hj]
      congr 1
      push_cast
      ring
    have e2 : (χ * ξ).locK w (unif w ^ (1 + diffExp w)) =
        χ.val w * χ.locK w (unif w ^ (0 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) := by
      show χ.locK w (unif w ^ (1 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) = _
      rw [pow_add, pow_one, map_mul, zero_add]
      rfl
    rw [locEps, locEps, if_neg one_ne_zero, if_pos rfl, gaussSumAt_unr_mul hχ one_ne_zero, hqw, e1, e2, map_mul, map_mul,
      hx1, hgG, map_pow σ, map_natCast σ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end GlobalTheory.TameTwistEps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingImageStalkMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ _root_.GlobalTheory.LogDR.locRing y ↔ ∃ z ∈ _root_.GlobalTheory.DI.stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  intro X Y _ π y h hsurj c
  have hcomm : ∀ b : Y.presheaf.stalk (π y),
      (π.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes h).hom b) =
        algebraMap (X.presheaf.stalk y) X.functionField ((π.stalkMap y).hom b) := by
    intro b
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply π _ _
      ((genericPoint_spec X).specializes (Set.mem_univ y)) b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj a
    exact ⟨(Y.presheaf.stalkSpecializes h).hom b, ⟨b, rfl⟩, hcomm b⟩
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨(π.stalkMap y).hom b, (hcomm b).symm⟩

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinranStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  first | (exact @GlobalTheory.OrbFinAf.iotaF_props) | (exact GlobalTheory.OrbFinAf.iotaF_props) | (intros; apply GlobalTheory.OrbFinAf.iotaF_props  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquiv
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc

theorem localTransfer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  intro p _ G K K' _ _ _ _ e Y a b b' ⟨u, z, hc, h⟩
  have hq : ∀ q : ℚ, e (algebraMap ℚ K q) = algebraMap ℚ K' q := fun q =>
    RingHom.congr_fun (Subsingleton.elim ((e : K →+* K').comp (algebraMap ℚ K)) (algebraMap ℚ K')) q
  let e' : K ≃ₐ[ℚ] K' := AlgEquiv.ofRingEquiv (f := e) hq
  let T : K ⊗[ℚ] G.C ≃ₐ[ℚ] K' ⊗[ℚ] G.C := Algebra.TensorProduct.congr e' AlgEquiv.refl
  have hT1 : ∀ c : G.C, T (inC G K c) = inC G K' c := by
    intro c
    simp [T, inC, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have hT2 : ∀ x : K, T (algebraMap K (K ⊗[ℚ] G.C) x) = algebraMap K' (K' ⊗[ℚ] G.C) (e x) := by
    intro x
    simp [T, e', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
  have hT3 : ∀ w : K ⊗[ℚ] G.C, (starT G.star K' (T w)).unop = T (starT G.star K w).unop := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have : T (r ⊗ₜ x) = e r ⊗ₜ x := by
        simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      rw [this, starT_tmul, starT_tmul]
      simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]
  refine ⟨Units.map (e : K →* K') u, Units.map (T : K ⊗[ℚ] G.C →* K' ⊗[ℚ] G.C) z, ?_, ?_⟩
  · have := hc.map T
    rw [hT1] at this
    exact this
  · have h' := congrArg T h
    rw [hT1, map_mul, hT2, map_mul, map_mul, map_mul, hT1, hT1, ← hT3] at h'
    simpa using h'

end GlobalTheory.FinClsLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFormsGeneratedDlog
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma smul_dlog_mem_forms {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (y : X)
    (g : X.functionFieldˣ) (hg : _root_.GlobalTheory.LogDR.LogUnit Z y g) (b : X.functionField)
    (hb : b ∈ _root_.GlobalTheory.LogDR.locRing y) :
    ExteriorAlgebra.ι X.functionField (b • _root_.GlobalTheory.LogDR.dlog g) ∈
      _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
        (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1 := by
  unfold _root_.GlobalTheory.DI.forms
  refine AddSubgroup.subset_closure ⟨b, hb, fun _ => _root_.GlobalTheory.LogDR.dlog g,
    fun _ => ⟨g, hg, rfl⟩, ?_⟩
  rw [map_smul, ExteriorAlgebra.ιMulti_apply]
  simp

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma logUnit_of_isUnit_stalk {X : Scheme.{0}} [IsIntegral X] (Z : Set X)
    (y : X) (g : X.functionFieldˣ) (a : X.presheaf.stalk y) (ha : IsUnit a)
    (hg : algebraMap (X.presheaf.stalk y) X.functionField a = g) :
    _root_.GlobalTheory.LogDR.LogUnit Z y g := by
  intro z hz _
  refine ⟨X.presheaf.stalkSpecializes hz a, ha.map (X.presheaf.stalkSpecializes hz).hom, ?_⟩
  rw [← hg]
  change (X.presheaf.stalkSpecializes _) ((X.presheaf.stalkSpecializes hz) a) =
    (X.presheaf.stalkSpecializes _) a
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.dK_dlog_mem_forms_one : ∀ {X : Scheme.{0}} [IsIntegral X]
    (Z : Set X) (y : X), (∀ w ∈ _root_.GlobalTheory.LogDR.locRing y,
      ExteriorAlgebra.ι X.functionField (_root_.GlobalTheory.LogDR.dK w) ∈
        _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
          (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1) ∧
      ∀ g, _root_.GlobalTheory.LogDR.LogUnit Z y g → ExteriorAlgebra.ι X.functionField (_root_.GlobalTheory.LogDR.dlog g) ∈
        _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
          (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1 := by
  intro X _ Z y
  refine ⟨fun w hw => ?_, fun g hg => ?_⟩
  · obtain ⟨a, rfl⟩ := _root_.GlobalTheory.LogDR.mem_locRing.mp hw
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with ha | ha
    · set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU
      have hUv : (U : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField a := rfl
      have key := smul_dlog_mem_forms Z y U
        (logUnit_of_isUnit_stalk Z y U a ha hUv.symm) _ hw
      convert key using 2
      unfold _root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK
      rw [smul_smul, ← hUv, Units.mul_inv, one_smul]
    · set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU
      have hUv : (U : X.functionField) =
          algebraMap (X.presheaf.stalk y) X.functionField (1 - a) := rfl
      have hmem : -(U : X.functionField) ∈ _root_.GlobalTheory.LogDR.locRing y :=
        neg_mem (_root_.GlobalTheory.LogDR.mem_locRing.mpr ⟨1 - a, hUv.symm⟩)
      have key := smul_dlog_mem_forms Z y U
        (logUnit_of_isUnit_stalk Z y U (1 - a) ha hUv.symm) _ hmem
      convert key using 2
      unfold _root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK
      rw [smul_smul, neg_mul, Units.mul_inv, neg_smul, one_smul, hUv, map_sub, map_one,
        map_sub, Derivation.map_one_eq_zero, zero_sub, neg_neg]
  · simpa using smul_dlog_mem_forms Z y g hg 1 (one_mem _)

end GlobalTheory.DI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactorStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mark_norm_sq_eq_similitudeFactor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ → ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKMid.Pair.mark_norm_sq) | (exact GlobalTheory.LKMid.Pair.mark_norm_sq) | (intros; apply GlobalTheory.LKMid.Pair.mark_norm_sq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitsGiveMatrixAlgebraIso
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_units_give_matrix_algebra_iso : ∀ (k K B : Type) [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B] [FiniteDimensional k B] (n : ℕ) (ι : K →ₐ[k] B), Function.Injective ι → (∀ z x, Commute (ι z) x) → Module.finrank k B = n ^ 2 * Module.finrank k K → ∀ E : Fin n → Fin n → B, (∀ a b c d, E a b * E c d = if b = c then E a d else 0) → ∑ a, E a a = 1 → ∃ Φ : Matrix (Fin n) (Fin n) K ≃+* B, (∀ M, Φ M = ∑ a, ∑ b, ι (M a b) * E a b) ∧ ∀ x a b, ι (Φ.symm x a b) = ∑ c, E c a * x * E b c := by
  first | (exact @GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits) | (exact GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits) | (intros; apply GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.PlaneSkew

variable {E : Type} [Field E] [NumberField E]

def lowLat {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n₁ → E) :=
  L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))

theorem mem_lowLat {n n₁ : ℕ} {ι : Matrix (Fin n) (Fin n₁) E} {L : Submodule (𝓞 E) (Fin n → E)} {u : Fin n₁ → E} :
    u ∈ lowLat ι L ↔ ι *ᵥ u ∈ L := Iff.rfl

def PrimAt (𝔓 : HeightOneSpectrum (𝓞 E)) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) : Prop :=
  (∀ s : E, s • x ∈ L → 𝔓.valuation E s ≤ 1) ∧ ∃ s : E, s • x ∈ L ∧ 𝔓.valuation E s = 1

end GlobalTheory.PlaneSkew
end
end

