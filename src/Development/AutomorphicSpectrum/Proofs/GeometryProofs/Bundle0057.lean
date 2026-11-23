module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbPull

theorem dual_frame_ext {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {W W' : Type} [AddCommGroup W] [Module Ω W]
    [AddCommGroup W'] [Module Ω' W'] (j : W →+ W') (hj : ∀ (a : Ω) (e : W), j (a • e) = i a • j e)
    (hs : Submodule.span Ω' (Set.range j) = ⊤) (jW : Module.Dual Ω W →+ Module.Dual Ω' W')
    (hjW : ∀ u e, jW u (j e) = i (u e)) {r : ℕ} (b : Fin r → Module.Dual Ω W) (hli : LinearIndependent Ω b)
    (hb : Submodule.span Ω (Set.range b) = ⊤) :
    LinearIndependent Ω' (fun k => jW (b k)) ∧ Submodule.span Ω' (Set.range fun k => jW (b k)) = ⊤ := by
  classical
  let c := Module.Basis.mk hli hb.ge
  have hc : ∀ k, c k = b k := fun k => by simp [c]
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis c
  haveI : Module.Finite Ω W := (Module.finite_dual_iff Ω).1 inferInstance
  let e : Fin r → W := fun l => (Module.evalEquiv Ω W).symm (c.dualBasis l)
  have he : ∀ k l, b k (e l) = if k = l then 1 else 0 := by
    intro k l
    simp only [e]
    rw [Module.apply_evalEquiv_symm_apply, ← hc k, Module.Basis.dualBasis_apply_self]
  have hx : ∀ x : W, x = ∑ k, b k x • e k := by
    intro x
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff Ω _).1
    intro u
    have hu : u ∈ Submodule.span Ω (Set.range b) := by rw [hb]; trivial
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      set_option synthInstance.maxHeartbeats 100000 in
        simp [he, map_sum]
    | zero => simp
    | add y z _ _ hy hz => simp only [LinearMap.add_apply, hy, hz, add_zero]
    | smul a y _ hy => simp only [LinearMap.smul_apply, hy, smul_zero]
  have hjx : ∀ x, j x = ∑ k, i (b k x) • j (e k) := by
    intro x
    conv_lhs => rw [hx x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hj _ _
  have hext : ∀ v v' : Module.Dual Ω' W', (∀ k, v (j (e k)) = v' (j (e k))) → v = v' := by
    intro v v' h
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨x, rfl⟩
    rw [hjx x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, h]
  have hpair : ∀ k l, jW (b k) (j (e l)) = if k = l then 1 else 0 := by
    intro k l
    rw [hjW, he]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg l
    have := congrArg (fun v : Module.Dual Ω' W' => v (j (e l))) hg
    simpa [hpair] using this
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k, v (j (e k)) • jW (b k) := by
      apply hext
      intro l
      simp [hpair]
    rw [hv]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem isVBOn_dual_pull : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (Lo : Lat ξ (Module.Dual Ω V)) (Lo' : Lat ξ' (Module.Dual Ω' V')) (T : Set (Cpt ξ)) (T' : Set (Cpt ξ')) (r : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (Lo.map W.dualRestrict).IsVBOn T r ⊤ → (∀ p' ∈ T', ∃ hq : genPt ξ ⤳ f p'.1, (⟨f p'.1, hq⟩ : Cpt ξ) ∈ T ∧ (0 < r → Lo' p' = Submodule.span (regAt ξ' p') (jd '' (Lo ⟨f p'.1, hq⟩ : Set (Module.Dual Ω V))))) → (Lo'.map W'.dualRestrict).IsVBOn T' r ⊤ := by
  intro X X' Ω Ω' _ _ ξ ξ' f i V V' _ _ _ _ j jd W W' Lo Lo' T T' r hd _ hj hjd hW hvb hT
  have hmem : ∀ e : W, j e ∈ W' := fun e => by
    rw [hW]
    exact Submodule.subset_span ⟨e, e.2, rfl⟩
  let jr : W →+ W' :=
    { toFun := fun e => ⟨j e, hmem e⟩
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j _ _) }
  have hsm : ∀ (a : Ω) (e : W), jr (a • e) = i a • jr e := fun a e => Subtype.ext (hj.1 a e)
  have hext : IsExtOver i jr := ⟨hsm, fun n b hb => by
    have h1 := hj.2 n (fun k => (b k : V)) (hb.map' W.subtype W.ker_subtype)
    exact LinearIndependent.of_comp W'.subtype h1⟩
  have hs : Submodule.span Ω' (Set.range jr) = ⊤ := by
    have h1 : (Submodule.span Ω' (Set.range jr)).map W'.subtype = W' := by
      rw [Submodule.map_span]
      conv_rhs => rw [hW]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
        exact ⟨e, e.2, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
    have h2 := Submodule.comap_map_eq_of_injective W'.injective_subtype (Submodule.span Ω' (Set.range jr))
    rw [h1, Submodule.comap_subtype_self] at h2
    exact h2.symm
  obtain ⟨jW, hjW⟩ := DualExt.dual_ext Ω Ω' i W W' jr hext hs
  have hcomp : ∀ w, W'.dualRestrict (jd w) = jW (W.dualRestrict w) := by
    intro w
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    rw [hjW]
    exact hjd w e
  have hsemi : ∀ (a : Ω) (u : Module.Dual Ω W), jW (a • u) = i a • jW u := by
    intro a u
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    simp [hjW]
  intro p' hp'
  obtain ⟨hq, hpT, -⟩ := hT p' hp'
  obtain ⟨U, hU, b, hb, hfr⟩ := hvb _ hpT
  obtain ⟨hli', hspan'⟩ := dual_frame_ext i jr hsm hs jW hjW b (hfr _ hpT hU).1 hb
  refine ⟨f ⁻¹ᵁ U, hU, fun k => jW (b k), hspan', fun q' hq' hq'U => ⟨hli', ?_⟩⟩
  obtain ⟨hq2, hqT, hL⟩ := hT q' hq'
  have hfrq := (hfr _ hqT hq'U).2
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : Subsingleton (Module.Dual Ω' W') := by
      rw [← Submodule.subsingleton_iff Ω', ← subsingleton_iff_bot_eq_top]
      rw [← hspan']
      simp
    exact Subsingleton.elim _ _
  · obtain ⟨hq3, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
    apply le_antisymm
    · show Submodule.map _ _ ≤ _
      rw [hL hr, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      show W'.dualRestrict (jd w) ∈ _
      rw [hcomp]
      have hin : W.dualRestrict w ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b) := by
        rw [← hfrq]
        exact ⟨w, hw, rfl⟩
      have key : ∀ y ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b),
          jW y ∈ Submodule.span (regAt ξ' q') (Set.range fun k => jW (b k)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact Submodule.subset_span ⟨k, rfl⟩
        | zero => simp
        | add y z _ _ hy hz =>
          rw [map_add (f := _)]
          exact Submodule.add_mem _ hy hz
        | smul a y _ hy =>
          have : jW (a • y) = (⟨i a, hreg _ a.2⟩ : regAt ξ' q') • jW y := hsemi (a : Ω) y
          rw [this]
          exact Submodule.smul_mem _ _ hy
      exact key _ hin
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hin : b k ∈ (Lo.map W.dualRestrict) ⟨f q'.1, hq2⟩ := by
        rw [hfrq]
        exact Submodule.subset_span ⟨k, rfl⟩
      obtain ⟨w, hw, hwk⟩ := hin
      refine ⟨jd w, ?_, ?_⟩
      · rw [hL hr]
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      · show W'.dualRestrict (jd w) = jW (b k)
        rw [hcomp]
        exact congrArg jW hwk

end GlobalTheory.CompanionTheory.Ar.VbPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogDenominatorBoundPrimes
section
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ClearConstants

private theorem prod_one_sub_lemma {Ω : Type} [Field Ω] (W : ValuationSubring Ω) (π : Ω)
    (s : Finset Ω) (h : ∀ μ ∈ s, ∃ u ∈ W, 1 - μ = π * u) :
    ∃ w ∈ W, ∏ μ ∈ s, (1 - μ) = w * π ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, W.one_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, hs⟩ := ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ))
    obtain ⟨u, hu, hau⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨u * w, mul_mem hu hw, ?_⟩
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hs, hau]
    ring

theorem prime_eq_mul_pow {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) : ∃ w ∈ W, (p : Ω) = w * (ζ - 1) ^ (p - 1) := by
  haveI := Fact.mk hp
  have hpow : ζ ^ p = 1 := hζ.pow_eq_one
  have hζW : ζ ∈ W := by
    rcases W.mem_or_inv_mem ζ with h | h
    · exact h
    · have hne : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
      have h1 : (ζ⁻¹) ^ (p - 1) * ζ⁻¹ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le, inv_pow, hpow, inv_one]
      have key : (ζ⁻¹) ^ (p - 1) = ζ := by
        calc (ζ⁻¹) ^ (p - 1) = (ζ⁻¹) ^ (p - 1) * ζ⁻¹ * ζ := by
              rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
          _ = ζ := by rw [h1, one_mul]
      rw [← key]
      exact pow_mem h _
  have hprod : (p : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ) := by
    have h0 := Polynomial.eval_one_cyclotomic_prime (R := Ω) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h0
    simpa using h0.symm
  have hcard : (primitiveRoots p Ω).card = p - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hp]
  have hall : ∀ μ ∈ primitiveRoots p Ω, ∃ u ∈ W, 1 - μ = (ζ - 1) * u := by
    intro μ hμ
    have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμp.pow_eq_one
    refine ⟨-(∑ j ∈ Finset.range i, ζ ^ j), neg_mem (sum_mem fun j _ => pow_mem hζW j), ?_⟩
    rw [← hi]
    linear_combination geom_sum_mul ζ i
  obtain ⟨w, hw, hw'⟩ := prod_one_sub_lemma W (ζ - 1) _ hall
  rw [hcard] at hw'
  exact ⟨w, hw, hprod.trans hw'⟩

def expo (q p : ℕ) : ℕ := if p = 2 then 2 * q else q / (p - 1)

theorem expo_cast {q p : ℕ} (hp : p.Prime) (hd : p - 1 ∣ q) :
    (expo q p : ℝ) = q * (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) := by
  unfold expo
  by_cases h : p = 2
  · subst h
    simp only [if_true]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    have hne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      have h2 : 2 ≤ p := hp.two_le
      have h3 : p - 1 ≠ 0 := by omega
      exact_mod_cast h3
    rw [Nat.cast_div hd hne, Nat.cast_sub hp.one_le]
    push_cast
    ring

theorem pow_expo_eq {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {p q : ℕ} (hp : p.Prime) (hd : p - 1 ∣ q)
    {κ : Ω} (hκ : HT.IsCp p κ) : ∃ w ∈ W, ((p ^ expo q p : ℕ) : Ω) = w * κ ^ q := by
  unfold HT.IsCp at hκ
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl] at hκ
    refine ⟨1, W.one_mem, ?_⟩
    have he : expo q 2 = 2 * q := by simp [expo]
    rw [hκ, one_mul, he, pow_mul]
    norm_num
  · rw [if_neg h2] at hκ
    obtain ⟨ζ, hζ, rfl⟩ := hκ
    obtain ⟨r, rfl⟩ := hd
    obtain ⟨w₀, hw₀, hpw⟩ := prime_eq_mul_pow W hp hζ
    have hpos : 0 < p - 1 := by have := hp.two_le; omega
    refine ⟨w₀ ^ r, pow_mem hw₀ r, ?_⟩
    have he : expo ((p - 1) * r) p = r := by
      simp only [expo, if_neg h2]
      exact Nat.mul_div_cancel_left r hpos
    rw [he, Nat.cast_pow, hpw, mul_pow, ← pow_mul]

theorem clear_constants : ∀ (S : Finset ℕ) (m₀ : ℕ), (∀ p ∈ S, p.Prime) → 0 < m₀ → ∃ q m : ℕ, 0 < q ∧ 0 < m ∧
    Real.log m ≤ q * (Real.log m₀ + ∑ p ∈ S, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p) ∧
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (W : ValuationSubring Ω) (κ : Ω), (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) →
      ∀ t : Ω, ((m₀ : Ω) * κ) * t ∈ W → (m : Ω) * t ^ q ∈ W := by
  intro S m₀ hS hm₀
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ∏ p ∈ S, (p - 1) := ⟨_, rfl⟩
  have hqpos : 0 < q := by
    rw [hq]
    exact Finset.prod_pos fun p hp => by have := (hS p hp).two_le; omega
  have hdvd : ∀ p ∈ S, p - 1 ∣ q := fun p hp => by
    rw [hq]
    exact Finset.dvd_prod_of_mem (fun p => p - 1) hp
  refine ⟨q, m₀ ^ q * ∏ p ∈ S, p ^ expo q p, hqpos,
    Nat.mul_pos (pow_pos hm₀ q) (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _), ?_, ?_⟩
  · apply le_of_eq
    push_cast
    have hm0 : ((m₀ : ℝ) ^ q) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₀.ne')
    have hprod : (∏ p ∈ S, (p : ℝ) ^ expo q p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero)
    rw [Real.log_mul hm0 hprod, Real.log_pow,
      Real.log_prod fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero),
      mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Real.log_pow, expo_cast (hS p hp) (hdvd p hp)]
    ring
  · intro Ω _ _ W κ hκ t ht
    have hrest : ∀ T : Finset ℕ, (∏ x ∈ T, ((x : Ω) ^ expo q x)) ∈ W :=
      fun T => prod_mem fun x _ => pow_mem (natCast_mem W x) _
    push_cast
    rcases hκ with rfl | ⟨p, hpS, hp⟩
    · rw [mul_one] at ht
      have e : (m₀ : Ω) ^ q * (∏ x ∈ S, (x : Ω) ^ expo q x) * t ^ q
          = ((m₀ : Ω) * t) ^ q * ∏ x ∈ S, (x : Ω) ^ expo q x := by ring
      rw [e]
      exact mul_mem (pow_mem ht q) (hrest S)
    · obtain ⟨w, hw, hpw⟩ := pow_expo_eq W (hS p hpS) (hdvd p hpS) hp
      push_cast at hpw
      have hsplit : ∏ x ∈ S, (x : Ω) ^ expo q x = w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x := by
        rw [← Finset.mul_prod_erase S (fun x => (x : Ω) ^ expo q x) hpS, hpw]
      rw [hsplit]
      have e : (m₀ : Ω) ^ q * (w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x) * t ^ q
          = w * ((m₀ : Ω) * κ * t) ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x := by ring
      rw [e]
      exact mul_mem (mul_mem hw (pow_mem ht q)) (hrest _)

end GlobalTheory.CompanionTheory.Ar.ClearConstants
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosed
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.IntEmb

theorem ringOfIntegers_embedding_mem_range
    (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [IsIntegrallyClosed A] (E : Type) [Field E] [NumberField E] (σ : E →+* Ω) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A Ω).range := by
  have hℤ : IsIntegral ℤ (σ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom ℤ) σ (RingHom.ext_int _ _)
      (NumberField.RingOfIntegers.isIntegral_coe a)
  have hA : IsIntegral A (σ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom A) (RingHom.id Ω) (RingHom.ext_int _ _) hℤ
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hA
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.IntEmb
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptFlag
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagMatch

theorem matched_generic_flags_carried : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀) (φ : A.Li ≃ₗ[Ω] A'.Li), Mono (spMap β) → Mono (spMap β') → A.fn.comp ψ.toRingHom = A'.fn → (∀ w, TwTan n Y Y' ((A.M.pt w).left ≫ A.m.φ) ((A'.M.pt (φ w)).left ≫ A'.m.φ)) → (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) → (∀ e, φ (Fl.j e) = Fl'.j (θ e)) ∧ ∀ s s' (r : ℕ) (b : Fin r → Fl.Li₀) (u : Matrix (Fin r) (Fin r) Ω), (∀ k, flagStep Ω (Fl.b s) k = flagStep Ω (fun a => ∑ q, u q a • Fl.j (b q)) k) → (∀ k, flagStep Ω (Fl'.b s') k = flagStep Ω (fun a => ∑ q, u q a • Fl'.j (θ (b q))) k) → ∀ k, (flagStep Ω (Fl.b s) k).map φ.toLinearMap = flagStep Ω (Fl'.b s') k :=
  @PositivityTheory.UnitarySelfGeneration.flag_data_match_under_twist

end GlobalTheory.CompanionTheory.Ar.FlagMatch
end

