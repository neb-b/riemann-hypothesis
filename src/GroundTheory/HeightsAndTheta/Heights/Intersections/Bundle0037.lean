module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherSide
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def VerticalDegreeAfterAdjoining.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ)
    (i' : ∀ k', ι' k'),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    IsChart (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' →
    ∀ G' : GenFibre v W',
      fnDeg v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' =
        Module.finrank G'.Φ (IntermediateField.adjoin G'.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩))

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreDimensionZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    ∀ G' : GenFibre v W', IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IntCastMemRegMaxAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem regRing_mem_locRing {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((x : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W :=
  x.2 W hW hPW

def regToLoc (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) : regRing P →+* locRing P W where
  toFun x := ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

theorem regToLoc_apply {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    regToLoc P W hW hPW x = ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩ :=
  rfl

theorem regToLoc_coe {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((regToLoc P W hW hPW x : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) :=
  (congrArg Subtype.val (regToLoc_apply hW hPW x)).trans (Subtype.coe_mk _ _)

def regMaxAt (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    Ideal (regRing P) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (regToLoc P W hW hPW)

theorem not_mem_regMaxAt_iff {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W)
    (hloc : IsLocalRing (locRing P W)) (x : regRing P) :
    x ∉ regMaxAt P W hW hPW hloc ↔
      ∃ z ∈ locRing P W, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 := by
  have hc : ∀ b : locRing P W, ((regToLoc P W hW hPW x * b : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * b := fun b => by
    rw [Subring.coe_mul, regToLoc_coe]
  simp only [regMaxAt, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    refine ⟨b.1, b.2, ?_⟩
    rw [← hc b, hb, Subring.coe_one]
  · rintro ⟨z, hz, h⟩
    refine IsUnit.of_mul_eq_one (a := regToLoc P W hW hPW x) ⟨z, hz⟩ (Subtype.ext ?_)
    rw [hc, Subring.coe_one]
    exact h

theorem intCast_mem_regMaxAt (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)} (hPp : P.IsPrime)
    (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) {n : ℤ} (hn : C n ∈ W) :
    (n : regRing P) ∈ regMaxAt P W hW hPW hloc := by
  by_contra h
  obtain ⟨z, hz, h⟩ := (not_mem_regMaxAt_iff hW hPW hloc _).1 h
  have h1W : (1 : MRing ι) ∉ W := fun h => hW.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hu := ((hL K ι P W hPp hW.1.1 hPW).2 (n : locRing P W) (C n) 1 0 (RegularityDenominator.isMultiHomog_C n)
    AvoidRing.isMultiHomog_one h1W (by simp [eq_intCast C n])).1
  refine hu (IsUnit.of_mul_eq_one (a := (n : locRing P W)) ⟨z, hz⟩ (Subtype.ext ?_)) hn
  simpa using h

theorem regMaxAt_isMaximal (hO : RegularityOrder.Statement) (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    (regMaxAt P W hW hPW hloc).IsMaximal := by
  have : (regMaxAt P W hW hPW hloc).IsPrime := by unfold regMaxAt; infer_instance
  have : Module.Finite ℤ (regRing P) := (hO K ι P hP).2.1
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
  have hn : n ∈ (regMaxAt P W hW hPW hloc).comap (algebraMap ℤ (regRing P)) := by
    rw [Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
    exact intCast_mem_regMaxAt hL hP.2.1.1 hW hPW hloc hnW
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap ℤ (regRing P))
    Algebra.IsIntegral.isIntegral _
    (_root_.IsPrime.to_maximal_ideal fun h => hn0 (by rw [h] at hn; exact hn))

theorem RegularityMaximalSpectrum.proof (hO : RegularityOrder.Statement)
    (hZ : RegularityLocalize.Statement) (hI : LocRingInj.Statement) (hS : RegularityMaximalSurjective.Statement) :
    RegularityMaximalSpectrum.Statement := by
  classical
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof
  intro K _ ι _ P hP
  have hPp : P.IsPrime := hP.2.1.1
  have hloc : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, IsLocalRing (locRing P W.1) :=
    fun W => (hL K ι P W.1 hPp W.2.1.1.1 W.2.2).1
  let m : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → Ideal (regRing P) := fun W =>
    regMaxAt P W.1 W.2.1 W.2.2 (hloc W)
  have hm : ∀ W (x : regRing P), x ∉ m W ↔
      ∃ z ∈ locRing P W.1, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 :=
    fun W => not_mem_regMaxAt_iff W.2.1 W.2.2 (hloc W)

  have hsub : ∀ W W', m W = m W' → locRing P W.1 ≤ locRing P W'.1 := by
    intro W W' hWW' y hy
    obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    obtain ⟨z, hz, hsz⟩ := (hm W' s).1 (hWW' ▸ (hm W s).2 hsu)
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W'.2.1 W'.2.2 x) hz
  let f : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → MaximalSpectrum (regRing P) := fun W =>
    ⟨m W, regMaxAt_isMaximal hO hL hP W.2.1 W.2.2 (hloc W)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun W W' h => Subtype.ext (hI K ι P W.1 W'.1 hPp W.2.1.1 W'.2.1.1 W.2.2 W'.2.2
      (le_antisymm (hsub W W' (congrArg MaximalSpectrum.asIdeal h))
        (hsub W' W (congrArg MaximalSpectrum.asIdeal h).symm))), ?_⟩
    rintro ⟨M, hM⟩
    obtain ⟨W, hWc, hPW, hW⟩ := hS K ι P hP M hM
    refine ⟨⟨W, hWc, hPW⟩, ?_⟩
    have hle : M ≤ m ⟨W, hWc, hPW⟩ := fun x hx => by
      by_contra hc
      obtain ⟨z, hz, h⟩ := (hm _ x).1 hc
      exact hW x hx z hz h
    exact MaximalSpectrum.ext (hM.eq_of_le (regMaxAt_isMaximal hO hL hP hWc hPW _).ne_top hle).symm
  refine ⟨Equiv.ofBijective f hbij, fun W y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    exact ⟨x, s, (hm W s).2 hsu, hys⟩
  · rintro ⟨x, s, hs, hys⟩
    obtain ⟨z, hz, hsz⟩ := (hm W s).1 hs
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W.2.1 W.2.2 x) hz

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockGenFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGenFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p ↦ c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem eval_map_rename (v : (Σ k, ι k) → (Σ k', ι' k')) (s : MRing ι) (z' : (Σ k', ι' k') → ℂ) :
    eval z' (map (Int.castRingHom ℂ) (rename v s)) = eval (fun p ↦ z' (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

end BlockGenFinite


open BlockGenFinite in
theorem BlockGenFinite.proof (hR : BlockRatioAlg.Statement) : BlockGenFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hv hP' hP
  have hrel := hP'.2.1.2.2
  have hpr := hP'.2.1.1
  have hrel' : ∀ k : FibreBlock κ, ∃ i : ι' k.1, (X (⟨k.1, i⟩ : Σ k', ι' k') : MRing ι') ∉ P' := fun k ↦ hrel k.1
  choose c hc using hrel'
  have hA := fun q : (Σ k : FibreBlock κ, ι' k.1) ↦
    hR K ι K' ι' κ v P' n hv hP' hP ⟨q.1.1, q.2⟩ ⟨q.1.1, c q.1⟩ rfl (hc q.1)
  choose m A a hAh hAl hAP using hA
  refine ⟨(∏ q, rename v (A q (Fin.last (m q)))) * ∏ k : FibreBlock κ, X ⟨k.1, c k⟩,
    (∑ q, Function.extend κ (a q) 0) + ∑ k : FibreBlock κ, Pi.single k.1 1, ?_, ?_, ?_⟩
  · exact AvoidRing.isMultiHomog_mul
      (AvoidRing.isMultiHomog_prod _ _ _ fun q _ ↦ ArithmeticIntersectionHorizontal.isMultiHomog_rename hv (hAh q _))
      (AvoidRing.isMultiHomog_prod _ _ _ fun k _ ↦ AvoidRing.isMultiHomog_X _ _)
  · intro h
    rcases hpr.mul_mem_iff_mem_or_mem.mp h with h | h
    · obtain ⟨q, -, hq⟩ := hpr.prod_mem_iff.mp h
      exact hAl q hq
    · obtain ⟨k, -, hk⟩ := hpr.prod_mem_iff.mp h
      exact hc k hk
  intro u

  obtain ⟨pol, hpol⟩ : ∃ pol : (Σ k : FibreBlock κ, ι' k.1) → Polynomial ℂ, ∀ q, pol q =
      ∑ j : Fin (m q + 1), Polynomial.C (eval u (map (Int.castRingHom ℂ) (A q j))) * Polynomial.X ^ (j : ℕ) :=
    ⟨_, fun _ ↦ rfl⟩

  obtain ⟨build, hbuild⟩ : ∃ build : ((Σ k : FibreBlock κ, ι' k.1) → ℂ) → (Σ k', ι' k') → ℂ, ∀ ρ p',
      build ρ p' = if h : p'.1 ∈ Set.range κ then u (hv.2.2.2 p' h).choose else ρ ⟨⟨p'.1, h⟩, p'.2⟩ :=
    ⟨_, fun _ _ ↦ rfl⟩
  refine ⟨(Fintype.piFinset fun q ↦ (pol q).roots.toFinset).image build, ?_⟩
  rintro z' hz' hf0 ⟨d, hd, hzd⟩
  have hzd' : ∀ p, z' (v p) = d p.1 * u p := fun p ↦ congrFun hzd p
  simp only [map_mul, map_prod, map_X, eval_X] at hf0
  have hcz : ∀ k : FibreBlock κ, z' ⟨k.1, c k⟩ ≠ 0 := fun k ↦
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf0) k (Finset.mem_univ _)
  have hlead : ∀ q, eval u (map (Int.castRingHom ℂ) (A q (Fin.last (m q)))) ≠ 0 := by
    intro q h
    have := Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hf0) q (Finset.mem_univ _)
    rw [eval_map_rename, show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd,
      eval_smul_of_isMultiHomog (hAh q _), h, mul_zero] at this
    exact this rfl

  have hroot : ∀ q, z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩ ∈ (pol q).roots.toFinset := by
    intro q
    have hne : pol q ≠ 0 := by
      intro h0
      have h1 := congrArg (fun f ↦ _root_.AddMonoidAlgebra.coeff (M := ℕ) f (m q)) h0
      simp only [hpol, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single (Fin.last (m q))] at h1
      · simp only [Fin.val_last, if_true] at h1
        exact hlead q h1
      · intro j _ hj
        rw [if_neg]
        intro e
        exact hj (Fin.ext (by simp [e]))
      · simp
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    have hrel0 := hz'.2 _ (hAP q)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_X, eval_X, eval_map_rename,
      show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd, eval_smul_of_isMultiHomog (hAh q _)] at hrel0
    have hD : (∏ k, d k ^ a q k) * z' ⟨q.1.1, c q.1⟩ ^ m q ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hd k)) (pow_ne_zero _ (hcz q.1))
    refine (mul_eq_zero.mp ?_).resolve_left hD
    rw [hpol, Polynomial.eval_finsetSum, Finset.mul_sum, ← hrel0]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : (j : ℕ) ≤ m q := Nat.lt_succ_iff.mp j.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← pow_sub_mul_pow (z' ⟨q.1.1, c q.1⟩) hj, div_pow]
    field_simp [pow_ne_zero _ (hcz q.1)]

  refine ⟨build fun q ↦ z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩,
    Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hroot), ?_⟩
  refine ⟨fun k' ↦ if h : k' ∈ Set.range κ then d h.choose else z' ⟨k', c ⟨k', h⟩⟩,
    fun k' ↦ ?_, funext fun p' ↦ ?_⟩
  · dsimp only
    split_ifs with h
    · exact hd _
    · exact hcz ⟨k', h⟩
  · rw [hbuild]
    by_cases h : p'.1 ∈ Set.range κ
    · rw [dite_eq_left h]
      dsimp only
      rw [dite_eq_left h]
      obtain ⟨p, rfl⟩ := hv.2.2.2 p' h
      rw [show h.choose = p.1 from hv.1 (h.choose_spec.trans (hv.2.2.1 p)),
        show (hv.2.2.2 (v p) h).choose = p from hv.2.1 (hv.2.2.2 (v p) h).choose_spec]
      exact hzd' p
    · rw [dite_eq_right h]
      dsimp only
      rw [dite_eq_right h]
      have hc' := hcz ⟨p'.1, h⟩
      dsimp only at hc'
      field_simp [hc']

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingInj.le_of_locRing_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W W' : Ideal (MRing ι)} (hP : P.IsPrime) (hW : IsMultiProjPrime W) (hW' : IsMultiProjPrime W')
    (hPW : P ≤ W) (hPW' : P ≤ W') (heq : locRing P W = locRing P W') : W ≤ W' := by
  classical
  have := hP
  have hL := LocRingLocal.proof LocRingFrac.proof
  set φ := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) with hφ
  have hne : ∀ {f : MRing ι}, f ∉ P → φ (Ideal.Quotient.mk P f) ≠ 0 := fun hf h => hf <| by
    rwa [hφ, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h

  have hunit : ∀ {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) (hy' : y ∈ locRing P W'),
      IsUnit (⟨y, hy'⟩ : locRing P W') → IsUnit (⟨y, hy⟩ : locRing P W) := by
    intro y hy hy' hu
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    have hb' : y * (b : FractionRing (MRing ι ⧸ P)) = 1 := by
      have := congrArg Subtype.val hb
      rwa [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk] at this
    have hbW : (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by rw [heq]; exact b.2
    refine IsUnit.of_mul_eq_one (⟨b, hbW⟩ : locRing P W) (Subtype.ext ?_)
    rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk, hb']
  choose i hi using hW.2.2
  choose j hj using hW'.2.2

  have hjW : ∀ k, (X ⟨k, j k⟩ : MRing ι) ∉ W := by
    intro k
    have hiP : (X ⟨k, i k⟩ : MRing ι) ∉ P := fun h => hi k (hPW h)
    have hjP : (X ⟨k, j k⟩ : MRing ι) ∉ P := fun h => hj k (hPW' h)
    have h1 : φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) ∈ locRing P W :=
      heq ▸ frac_mem_locRing hPW' (AvoidRing.isMultiHomog_X k (i k)) (AvoidRing.isMultiHomog_X k (j k))
        (hj k) (div_mul_cancel₀ _ (hne hjP))
    have h2 : φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) ∈ locRing P W :=
      frac_mem_locRing hPW (AvoidRing.isMultiHomog_X k (j k)) (AvoidRing.isMultiHomog_X k (i k))
        (hi k) (div_mul_cancel₀ _ (hne hiP))
    have hu : IsUnit (⟨_, h2⟩ : locRing P W) := by
      refine IsUnit.of_mul_eq_one (⟨_, h1⟩ : locRing P W) (Subtype.ext ?_)
      rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk]
      have := hne hiP
      have := hne hjP
      field_simp
    exact ((hL K ι P W hP hW.1 hPW).2 _ _ _ _ (AvoidRing.isMultiHomog_X k (j k))
      (AvoidRing.isMultiHomog_X k (i k)) (hi k) (div_mul_cancel₀ _ (hne hiP))).mp hu

  obtain ⟨S, hS, hWS⟩ := hW.2.1
  rw [hWS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
  by_contra hfW'
  have htW := AvoidRing.coordProd_not_mem hW.1 j hjW a
  have htW' := AvoidRing.coordProd_not_mem hW'.1 j hj a
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) (ι := ι) j a
  have hy := div_mul_cancel₀ (φ (Ideal.Quotient.mk P f)) (hne fun h => htW (hPW h))
  have hyW := frac_mem_locRing hPW ha ht htW hy
  have hyW' := frac_mem_locRing hPW' ha ht htW' hy
  have hu' : IsUnit (⟨_, hyW'⟩ : locRing P W') :=
    ((hL K ι P W' hP hW'.1 hPW').2 _ f _ a ha ht htW' hy).mpr hfW'
  exact ((hL K ι P W hP hW.1 hPW).2 _ f _ a ha ht htW hy).mp (hunit hyW hyW' hu') hfW

theorem LocRingInj.proof : LocRingInj.Statement := by
  intro K _ ι _ P W W' hP hW hW' hPW hPW' heq
  exact le_antisymm (LocRingInj.le_of_locRing_eq hP hW hW' hPW hPW' heq)
    (LocRingInj.le_of_locRing_eq hP hW' hW hPW' hPW heq.symm)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSheetHessPSD
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ComplexOrder

theorem analyticAt_of_eventually_differentiableAt {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {e : ℕ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') : AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp h
  rw [analyticAt_pi_iff]
  intro p
  exact osgood e U (fun y' => γ y' p) hUo
    (fun y' hy' => ((differentiableAt_pi.mp (hU y' hy')) p).differentiableWithinAt) y hyU

theorem SheetHessPSD.proof : SheetHessPSD.Statement := by
  intro K _ ι _ P e Ψ M y w γ hM hPos hγ
  have hev := hγ.2
  have hγy : γ y ∈ mcPts P := hev.self_of_nhds.2.1
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hγy.1
  have han : AnalyticAt ℂ γ y :=
    analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
  have hUo := SemipositiveTwist.isOpen_noZeroBlock (ι := ι)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (M.h z)) (γ y) :=
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos _ hz).ne'
  have hcomp : (fun y' => Real.log (M.h (γ y'))) = (fun z => Real.log (M.h z)) ∘ γ := rfl
  have hC2 : ContDiffAt ℝ 2 (fun y' => Real.log (M.h (γ y'))) y := by
    rw [hcomp]
    exact hlog.comp y (han.restrictScalars.contDiffAt)
  show (ReciprocityTheory.AnForm.hessC (fun y' => Real.log (M.h (γ y'))) y).PosSemidef
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ y hC2 fun x => ?_
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp x han hlog]
  have hL := SemipositiveTwist.laplacian_line_eq_levi hlog (fderiv ℂ γ y x)
  have hΔ := hPos (γ y) hz (fderiv ℂ γ y x)
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

