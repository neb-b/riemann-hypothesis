module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule
section
noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {r m : ℕ}

theorem Supports.mul {d : ℕ} {γ : Fin r → LinearMap.BilinForm ℤ X} {a : Fin m → X} (h : Supports bar φ d γ a) {k : ℕ}
    (hk : 0 < k) : Supports bar φ (d * k) γ fun j : Fin (m * k) => a (finProdFinEquiv.symm j).1 := by
  have key : ∀ β : LinearMap.BilinForm ℤ X,
      (∑ j : Fin (m * k), β (a (finProdFinEquiv.symm j).1) (a (finProdFinEquiv.symm j).1) : ℤ) =
        k * ∑ i, β (a i) (a i) := fun β => by
    rw [finProdFinEquiv.symm.sum_comp (fun p : Fin m × Fin k => β (a p.1) (a p.1)), Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => h.only β hβ hp ?_⟩
  · rw [← h.span]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨finProdFinEquiv (i, ⟨0, hk⟩), by simp⟩
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    have := h.le β hβ hp
    nlinarith
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← h.eq j]; ring
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast] at he
    have : (k : ℝ) * (d * φ.evalZ β) = k * (∑ i, β (a i) (a i) : ℤ) := by rw [← he]; ring
    exact mul_left_cancel₀ hk'.ne' this

theorem Supports.of_pull {d : ℕ} (e : X ≃ₗ[O] X₁) {γ : Fin r → LinearMap.BilinForm ℤ X₁} {a : Fin m → X}
    (h : Supports bar φ d (fun j => pull e.toLinearMap (γ j)) a) : Supports bar φ d γ fun i => e (a i) := by
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩
  · have h1 : Set.range (fun i => e (a i)) = e.toAddEquiv.toIntLinearEquiv.toLinearMap '' Set.range a := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h.span, Submodule.map_top, LinearMap.range_eq_top]
    exact e.toAddEquiv.toIntLinearEquiv.surjective
  · have := h.le _ (pull_mem e.toLinearMap hβ) fun y => hp _
    rwa [evalZ_pull φ e.surjective] at this
  · have := h.eq j
    rwa [evalZ_pull φ e.surjective] at this
  · have he' : d * φ.evalZ (pull e.toLinearMap β) = (∑ i, pull e.toLinearMap β (a i) (a i) : ℤ) := by
      rw [evalZ_pull φ e.surjective]; exact he
    obtain ⟨k, c, hk, hc⟩ := h.only _ (pull_mem e.toLinearMap hβ) (fun y => hp _) he'
    refine ⟨k, c, hk, LinearMap.ext₂ fun x y => ?_⟩
    have := LinearMap.congr_fun₂ hc (e.symm x) (e.symm y)
    simpa [LinearMap.sum_apply] using this

end Transport

theorem exists_common {ι : Type} [Finite ι] (P : ι → ℕ → Prop) (hmul : ∀ i d d', P i d → d ∣ d' → 0 < d' → P i d')
    (h : ∀ i, ∃ d, 1 ≤ d ∧ P i d) : ∃ d, 1 ≤ d ∧ ∀ i, P i d := by
  have := Fintype.ofFinite ι
  choose d hd hP using h
  have hpos : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  exact ⟨_, hpos, fun i => hmul i _ _ (hP i) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hpos⟩

section Module

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}

theorem exists_common_module {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (hX : IsPolFanOn bar φ X)
    (hs : ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧
      Supports bar φ d γ a) :
    ∃ d, 1 ≤ d ∧ ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → X),
      Supports bar φ d γ a := by
  obtain ⟨S, hS, hfin⟩ := hX.finite
  have := hS.to_subtype
  let N := Nat.card S
  obtain ⟨d, hd, hP⟩ := exists_common (ι := Σ r : Fin (N + 1), (Fin r → S))
    (fun i d => IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) →
      ∃ (m : ℕ) (a : Fin m → X), Supports bar φ d (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) a)
    (fun i d d' h hdd hd' hc => by
      obtain ⟨m, a, ha⟩ := h hc
      obtain ⟨c, rfl⟩ := hdd
      exact ⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)
    (fun i => by
      by_cases hc : IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X))
      · obtain ⟨d, m, a, hd, ha⟩ := hs _ _ hc
        exact ⟨d, hd, fun _ => ⟨m, a, ha⟩⟩
      · exact ⟨1, le_rfl, fun h => (hc h).elim⟩)
  refine ⟨d, hd, fun r γ hγ => ?_⟩
  obtain ⟨e, he⟩ := hfin r γ hγ
  have hγ' := hγ.pull_equiv e
  have hr : r ≤ N := by
    have := Nat.card_le_card_of_injective (fun i : Fin r => (⟨_, he i⟩ : S))
      (fun i j h => hγ'.injective (congrArg Subtype.val h))
    rwa [Nat.card_fin] at this
  obtain ⟨m, a, ha⟩ := hP ⟨⟨r, by omega⟩, fun i => ⟨_, he i⟩⟩ hγ'
  exact ⟨m, _, ha.of_pull e⟩

end Module

theorem exists_hasSupports : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Free ℤ O]
    [Finite (ClassGroup O)] (bar : O → O) (q : ℕ) (φ : InvFun O), IsPolFan bar q φ →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
      ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧
        Supports bar φ d γ a) → ∃ d, 1 ≤ d ∧ HasSupports bar q φ d := by
  intro O _ _ _ _ _ bar q φ hpol hs
  obtain ⟨n, Y, hY⟩ := GlobalTheory.ProjModFinIso.exists_finite_reps (R := O) q
  obtain ⟨d, hd, hP⟩ := exists_common (ι := Fin n)
    (fun k d => ∀ [Module.Finite O (Y k)] [Module.Projective O (Y k)], Module.finrank O (Y k) ≤ q →
      ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ (Y k)), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → Y k),
        Supports bar φ d γ a)
    (fun k d d' h hdd hd' _ _ hq r γ hγ => by
      obtain ⟨m, a, ha⟩ := h hq r γ hγ
      obtain ⟨c, rfl⟩ := hdd
      exact ⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)
    (fun k => by
      by_cases hk : Module.Finite O (Y k) ∧ Module.Projective O (Y k) ∧ Module.finrank O (Y k) ≤ q
      · obtain ⟨h1, h2, h3⟩ := hk
        obtain ⟨d, hd, h⟩ := exists_common_module (hpol _ h3) (hs _ h3)
        exact ⟨d, hd, fun _ => h⟩
      · exact ⟨1, le_rfl, fun h3 => (hk ⟨‹_›, ‹_›, h3⟩).elim⟩)
  refine ⟨d, hd, fun X _ _ _ _ hX r γ hγ => ?_⟩
  obtain ⟨k, ⟨e⟩⟩ := hY X hX
  haveI := Module.Finite.equiv e
  haveI := Module.Projective.of_equiv e
  obtain ⟨m, a, ha⟩ := hP k (e.finrank_eq ▸ hX) r _ (hγ.pull_equiv e.symm)
  exact ⟨m, _, ha.of_pull e.symm⟩

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.DvrCentre

theorem exists_complete_dvr_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) (z : M.Z), ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
    (_ : CharZero V) (ξ : Sp V ⟶ M.Z), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧
    ξ (IsLocalRing.closedPoint V) = z ∧ ∃ w, ξ w = genericPoint M.Z := by
  intro o Ω _ _ _ hA M z
  have hΩ : CharZero Ω := hA.char
  by_cases hz : z = genericPoint M.Z
  · subst hz
    have : CharZero (PowerSeries Ω) := charZero_of_injective_ringHom (PowerSeries.C_injective (R := Ω))
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries Ω)) (PowerSeries Ω) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, this,
      spMap (PowerSeries.C (R := Ω)) ≫ M.pt, hc, ?_, IsLocalRing.closedPoint _, ?_⟩
    · exact M.pt_apply _
    · exact M.pt_apply _
  · have : IsDedekindDomain o := hA.ded
    have : IsLocallyNoetherian M.Z := by
      have := M.lft
      exact LocallyOfFiniteType.isLocallyNoetherian M.s
    let S := M.Z.presheaf.stalk z
    have hS : CharZero S := (M.stalkHom z).charZero

    have hgen : M.Z.fromSpecStalk z (⊥ : PrimeSpectrum S) = genericPoint M.Z := by
      have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk z) := by
        rw [Scheme.range_fromSpecStalk]
        exact genericPoint_specializes z
      obtain ⟨q, hq⟩ := h1
      have h2 : (⊥ : PrimeSpectrum S) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
      have h3 := h2.map (M.Z.fromSpecStalk z).continuous
      rw [hq] at h3
      exact (h3.antisymm (genericPoint_specializes _)).eq
    have hne : (⊥ : Ideal S) ≠ IsLocalRing.maximalIdeal S := by
      intro e
      apply hz
      have : (⊥ : PrimeSpectrum S) = IsLocalRing.closedPoint S := PrimeSpectrum.ext e
      rw [← hgen, this, Scheme.fromSpecStalk_closedPoint]
    obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ :=
      GlobalTheory.exists_complete_discreteValuationRing_ker_eq (S := S) (⊥ : Ideal S) hne
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    have : CharZero O := charZero_of_injective_ringHom hφ
    refine ⟨O, inferInstance, hO, hO', this, spMap φ ≫ M.Z.fromSpecStalk z, hO'', ?_, (⊥ : PrimeSpectrum O), ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans
        (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) (Scheme.fromSpecStalk_closedPoint (x := z)))
      exact IsLocalRing.comap_closedPoint φ
    · refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) hgen)
      exact PrimeSpectrum.ext h1

end GlobalTheory.DvrCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalDomainLiftCyclotomicAway
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor.CycLift

theorem charZero_witt (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 ((CharP.cast_eq_zero_iff K p l).1 h2)
    subst h4
    exact WittVector.p_ne_zero p K h1
  · subst h
    exact CharP.charP_to_charZero _

theorem isPrimitiveRoot_zetaAway {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zetaAway n) n :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn)
    Subtype.val_injective

theorem hom_ext {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] (f g : cycAway n →+* R)
    (h : f (zetaAway n) = g (zetaAway n)) : f = g := by
  have hinv : ∀ hx : (n : ℂ)⁻¹ ∈ cycAway n, f ⟨(n : ℂ)⁻¹, hx⟩ = g ⟨(n : ℂ)⁻¹, hx⟩ := by
    intro hx
    have hu : (⟨(n : ℂ)⁻¹, hx⟩ : cycAway n) * (n : cycAway n) = 1 :=
      Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])
    have hf := congrArg f hu
    have hg := congrArg g hu
    rw [map_mul, map_natCast, map_one] at hf hg
    calc f ⟨(n : ℂ)⁻¹, hx⟩ = f ⟨(n : ℂ)⁻¹, hx⟩ * ((n : R) * g ⟨(n : ℂ)⁻¹, hx⟩) := by
          rw [_root_.mul_comm (n : R), hg, _root_.mul_one]
      _ = g ⟨(n : ℂ)⁻¹, hx⟩ := by rw [← _root_.mul_assoc, hf, _root_.one_mul]
  ext ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · exact hinv _
  | zero => exact (map_zero f).trans (map_zero g).symm
  | one => exact (map_one f).trans (map_one g).symm
  | add x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add (f := _), map_add (f := _), ihx, ihy]
  | neg x hx ih =>
    change f (-⟨x, hx⟩) = g (-⟨x, hx⟩)
    rw [map_neg, map_neg, ih]
  | mul x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

end GlobalTheory.SiegelTor.CycLift

namespace GlobalTheory.SiegelTor.CycLift

theorem exists_hom {n : ℕ} (hn : n ≠ 0) {F : Type} [Field F] [CharZero F] {y : F} (hy : IsPrimitiveRoot y n) :
    ∃ f : cycAway n →+* F, Function.Injective f ∧ f (zetaAway n) = y := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  set z : ℂ := ((zetaAway n : cycAway n) : ℂ) with hzdef
  have hz : IsPrimitiveRoot z n := (isPrimitiveRoot_zetaAway hn).map_of_injective (f := (cycAway n).subtype) Subtype.val_injective
  have hint : IsIntegral ℚ z := (hz.isIntegral hpos).tower_top
  let pb := IntermediateField.adjoin.powerBasis hint
  have hgen : pb.gen = IntermediateField.AdjoinSimple.gen ℚ z := rfl
  have hroot : Polynomial.aeval y (minpoly ℚ pb.gen) = 0 := by
    have hmp : minpoly ℚ pb.gen = minpoly ℚ z := by
      exact IntermediateField.minpoly_gen ℚ z
    rw [hmp, ← Polynomial.cyclotomic_eq_minpoly_rat hz hpos, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hy.isRoot_cyclotomic hpos
  let ψ := pb.lift y hroot
  have hle : cycAway n ≤ (IntermediateField.adjoin ℚ {z}).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ z
    · show _ ∈ IntermediateField.adjoin ℚ {z}
      exact inv_mem (IntermediateField.natCast_mem _ n)
  refine ⟨(ψ : IntermediateField.adjoin ℚ {z} →+* F).comp (Subring.inclusion hle), ?_, ?_⟩
  · exact ((ψ : IntermediateField.adjoin ℚ {z} →+* F).injective).comp (Subring.inclusion_injective hle)
  · change ψ pb.gen = y
    exact PowerBasis.lift_gen _ _ _

end GlobalTheory.SiegelTor.CycLift

namespace GlobalTheory.SiegelTor.CycLift

theorem exists_complete_domain_lift : ∀ (n : ℕ), 3 ≤ n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K),
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsNoetherianRing V) (βV : cycAway n →+* V)
      (π : V →+* K), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Function.Injective βV ∧ Function.Surjective π ∧
        π.comp βV = β := by
  intro n hn3 K _ _ β
  have hn : n ≠ 0 := by omega
  have hβζ := isPrimitiveRoot_map hn β
  have hnK : (n : K) ≠ 0 := by simpa using ((isUnit_natCast hn).map β).ne_zero
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hpp | hp0
  · have : Fact p.Prime := ⟨hpp⟩
    have := charZero_witt p K
    have hinj := IsFractionRing.injective (WittVector p K) (FractionRing (WittVector p K))
    have : CharZero (FractionRing (WittVector p K)) := charZero_of_injective_algebraMap hinj
    have hc : ∀ a : K, (WittVector.constantCoeff : WittVector p K →+* K) (WittVector.teichmuller p a) = a :=
      fun a => by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    set t : WittVector p K := WittVector.teichmuller p (β (zetaAway n)) with ht_def
    have ht : IsPrimitiveRoot t n := by
      refine ⟨?_, fun l hl => hβζ.dvd_of_pow_eq_one l ?_⟩
      · rw [ht_def, ← map_pow, hβζ.pow_eq_one, map_one]
      · have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) hl
        rwa [map_pow, map_one, hc] at this
    obtain ⟨f, hf, hfζ⟩ := exists_hom hn (ht.map_of_injective hinj)
    have hnW : IsUnit (n : WittVector p K) :=
      WittVector.isUnit_of_coeff_zero_ne_zero _ (by rw [← WittVector.constantCoeff_apply, map_natCast]; exact hnK)
    have hmem : ∀ x, f x ∈ (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range := by
      rintro ⟨x, hx⟩
      induction hx using Subring.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx'
        · exact ⟨t, hfζ.symm⟩
        · subst hx'
          refine ⟨↑hnW.unit⁻¹, ?_⟩
          apply mul_right_cancel₀ (Nat.cast_ne_zero.2 hn : (n : FractionRing (WittVector p K)) ≠ 0)
          have e1 : algebraMap (WittVector p K) (FractionRing (WittVector p K)) ↑hnW.unit⁻¹ * n = 1 := by
            rw [← map_natCast (algebraMap (WittVector p K) (FractionRing (WittVector p K))) n, ← map_mul,
              hnW.val_inv_mul, map_one]
          have hu : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) * (n : cycAway n) = 1 :=
            Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])
          have e2 := congrArg f hu
          rw [map_mul, map_natCast, map_one] at e2
          exact e1.trans e2.symm
      | zero => show f 0 ∈ _; rw [map_zero]; exact zero_mem _
      | one => show f 1 ∈ _; rw [map_one]; exact one_mem _
      | add x y hx hy ihx ihy =>
        show f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _; rw [map_add]; exact add_mem ihx ihy
      | neg x hx ih => show f (-⟨x, hx⟩) ∈ _; rw [map_neg]; exact neg_mem ih
      | mul x y hx hy ihx ihy =>
        show f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _; rw [map_mul]; exact mul_mem ihx ihy
    let e : WittVector p K ≃+* (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range :=
      RingEquiv.ofBijective (algebraMap (WittVector p K) (FractionRing (WittVector p K))).rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
    let βV : cycAway n →+* WittVector p K := e.symm.toRingHom.comp (f.codRestrict _ hmem)
    have hβV : ∀ x, algebraMap (WittVector p K) (FractionRing (WittVector p K)) (βV x) = f x := fun x =>
      congrArg Subtype.val (e.apply_symm_apply (f.codRestrict _ hmem x))
    refine ⟨WittVector p K, inferInstance, inferInstance, inferInstance, inferInstance, βV, WittVector.constantCoeff,
      ?_, ?_, ?_, ?_⟩
    · rw [(WittVector.irreducible p).maximalIdeal_eq]
      exact WittVector.isAdicCompleteIdealSpanP
    · exact fun a b h => hf (by rw [← hβV, ← hβV, h])
    · exact fun a => ⟨WittVector.teichmuller p a, hc a⟩
    · refine hom_ext hn _ _ ?_
      have h1 : βV (zetaAway n) = t := hinj (by rw [hβV, hfζ])
      show WittVector.constantCoeff (βV (zetaAway n)) = β (zetaAway n)
      rw [h1, hc]
  · subst hp0
    have : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, hf, hfζ⟩ := exists_hom hn hβζ
    have hβ : β = f := hom_ext hn _ _ hfζ.symm
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, β, RingHom.id K, ?_, hβ ▸ hf,
      fun x => ⟨x, rfl⟩, RingHom.id_comp β⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance

end GlobalTheory.SiegelTor.CycLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelic
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem exists_realPart_hom : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V), V.SigOK → IsInfFam θ → IsFrames V A → ∃ rp : GA D V →* (∀ ρ, Upq V ρ), Continuous rp ∧ IsRealPart V θ A rp := by
  intro D V θ A hV hθ hA
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ (fun i => hV (tauE D i)) hA
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  refine ⟨e1.toMulEquiv.toMonoidHom.comp ((MonoidHom.fst _ _).comp e0.toMulEquiv.toMonoidHom),
    e1.continuous.comp (continuous_fst.comp e0.continuous), fun h i => ?_⟩
  show UpqT.mat (e1 (e0 h).1 i) * A i = _
  rw [he1, (he0 h).2]; rfl

end GlobalTheory.CovTop.VolUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminantLineSectionRestriction
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_bar (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R]
    {x : Sp R ⟶ Xo.XF c} {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} (h : ∃ j, FrU Xo c U τ j x v w) :
    ∃ vb wb, FrY Y (compactOf Y U) τ h.choose (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb :=
  (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R h.choose x).1 v w h.choose_spec

def restrictRule (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y) : RuleU Xo c :=
  fun R _ x v w =>
    haveI := Classical.propDecidable (∃ j, FrU Xo c U τ j x v w)
    if h : ∃ j, FrU Xo c U τ j x v w then
      σb R (x ≫ Y.jQ) (exists_bar Y U τ h).choose (exists_bar Y U τ h).choose_spec.choose
    else 0

theorem restrictRule_eq (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {σb : RuleY Y}
    (hσb : SecY Y (compactOf Y U) τ σb) {R : Type} [CommRing R] {j : c.F →+* R} {x : Sp R ⟶ Xo.XF c}
    {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin D.p → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} {wb : Fin D.q → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)}
    (h : FrU Xo c U τ j x v w) (hb : FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb) (hv : SameVecs Y x v vb)
    (hw : SameVecs Y x w wb) : restrictRule Y U τ σb R x v w = σb R (x ≫ Y.jQ) vb wb := by
  have hex : ∃ j, FrU Xo c U τ j x v w := ⟨j, h⟩
  obtain ⟨hb0, hv0, hw0⟩ := (exists_bar Y U τ hex).choose_spec.choose_spec
  have e : restrictRule Y U τ σb R x v w =
      σb R (x ≫ Y.jQ) (exists_bar Y U τ hex).choose (exists_bar Y U τ hex).choose_spec.choose := by
    unfold restrictRule
    rw [dite_eq_left hex]
  rw [e]
  have hx : x ≫ Y.jQ = spMap (RingHom.id R) ≫ (x ≫ Y.jQ) := by
    rw [DetExtendZero.spMap_id, Category.id_comp]
  have hx' : x = spMap (RingHom.id R) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
  have cv : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.p) (Fin D.p) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (vb k).left) ((exists_bar Y U τ hex).choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.p v vb v _ hx' hv hv0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.1.1 k).1) i
  have cw : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.q) (Fin D.q) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (wb k).left)
      ((exists_bar Y U τ hex).choose_spec.choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.q w wb w _ hx' hw hw0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have key := sec_chg hσb hb hb0 (g := RingHom.id R) (M := 1) (N := 1) ⟨hx, cv, cw⟩
  simpa using key.symm

theorem exists_restriction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y), SecY Y (compactOf Y U) τ σb → ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ Restricts Y U τ σb σ ∧ (NzY Y (compactOf Y U) τ σb → NzU Xo c U τ σ) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ σb hσb
  refine ⟨restrictRule Y U τ σb, isSection_of_chg ?_, ?_, ?_⟩
  · intro R R' _ _ g j j' x v w x' v' w' M N h h' hc
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    obtain ⟨vb', wb', hb', hv', hw'⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R' j' x').1 v' w' h'
    rw [restrictRule_eq Y U τ hσb h hb hv hw, restrictRule_eq Y U τ hσb h' hb' hv' hw']
    refine sec_chg hσb hb hb' ⟨by rw [hc.1, Category.assoc], fun i => ?_, fun i => ?_⟩
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.p v vb v' vb' hc.1 hv hv'
        _ i).mp (hc.2.1 i)
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.q w wb w' wb' hc.1 hw hw'
        _ i).mp (hc.2.2 i)
  · intro R _ j x v w vb wb h hb hv hw
    exact (restrictRule_eq Y U τ hσb h hb hv hw).symm
  · intro hnz R _ j x v w h
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    rw [restrictRule_eq Y U τ hσb h hb hv hw]
    exact hnz R j _ vb wb hb

end GlobalTheory.DetLine.Restrict
end
end

