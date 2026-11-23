module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0009
public import ReciprocityTheory.SemistableReduction.Bundle0017

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegHorPf
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem not_isUnit_algebraMap_of_finite {O V : Type} [CommRing O] [IsLocalRing O] [CommRing V]
    [Nontrivial V] [Algebra O V] [Module.Finite O V] (π : O) (hπ : π ∈ maximalIdeal O) :
    ¬ IsUnit (algebraMap O V π) := by
  intro hu
  have htop : (⊤ : Submodule O V) ≤ maximalIdeal O • ⊤ := by
    intro v _
    obtain ⟨w, hw⟩ : ∃ w : V, algebraMap O V π * w = v :=
      ⟨hu.unit⁻¹ * v, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
    rw [← hw, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hπ Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) ⊤
    Module.Finite.fg_top htop (IsLocalRing.maximalIdeal_le_jacobson _)
  have h1 : (1 : V) ∈ (⊥ : Submodule O V) := hbot ▸ Submodule.mem_top
  exact one_ne_zero ((Submodule.mem_bot O).mp h1)

theorem reg_horizontal_pf {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  by_contra hno
  obtain ⟨a, s, haP, hsP, hfas⟩ := hdvr hno
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hno ⟨0, 1, (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top ‹_›), by simp⟩
  have hs0 : algebraMap A (FractionRing A) s ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; rintro rfl; exact hsP P.zero_mem
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hfas
    rcases hfas with h | h
    · exact hf0 (inv_eq_zero.mp h)
    · exact hs0 h
  have hfa : f * algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) s := by
    rw [← hfas, ← mul_assoc, mul_inv_cancel₀ hf0, one_mul]

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖm : ϖ ∈ maximalIdeal O := (mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hmapw : Ideal.map (algebraMap O A) (maximalIdeal O) = Ideal.span {algebraMap O A ϖ} := by
    rw [hmax, Ideal.map_span, Set.image_singleton]
  have hwP : algebraMap O A ϖ ∉ P := fun h =>
    hh (by rw [hmapw, Ideal.span_le, Set.singleton_subset_iff]; exact h)
  have hws : algebraMap O A ϖ * s ∉ P := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hwP hsP
  have hws0 : algebraMap A (FractionRing A) (algebraMap O A ϖ * s) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; rintro h; exact hws (h ▸ P.zero_mem)

  have hOA : Function.Injective (algebraMap O A) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow, mul_eq_zero] at hx
    rcases hx with h | h
    · exact (u.isUnit.map (algebraMap O A)).ne_zero h
    · exact hwP (pow_eq_zero_iff'.mp h |>.1 ▸ P.zero_mem)

  set y : FractionRing A := algebraMap A (FractionRing A) a /
    algebraMap A (FractionRing A) (algebraMap O A ϖ * s) with hy
  let B : Subalgebra A (FractionRing A) := Algebra.adjoin A {y}
  have hyB : y ∈ B := Algebra.subset_adjoin rfl

  let S : Subalgebra A (FractionRing A) :=
    { carrier := {x | ∃ a' p t : A, p ∈ P ∧ t ∉ P ∧
        x * algebraMap A (FractionRing A) t = algebraMap A (FractionRing A) (a' * t + p)}
      mul_mem' := by
        rintro x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩
        refine ⟨a1 * a2, a1 * t1 * p2 + a2 * t2 * p1 + p1 * p2, t1 * t2,
          P.add_mem (P.add_mem (P.mul_mem_left _ hp2) (P.mul_mem_left _ hp1)) (P.mul_mem_left _ hp2),
          fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩
        have : x1 * x2 * algebraMap A (FractionRing A) (t1 * t2) =
            (x1 * algebraMap A (FractionRing A) t1) * (x2 * algebraMap A (FractionRing A) t2) := by
          rw [map_mul]; ring
        rw [this, h1, h2, ← map_mul]
        congr 1
        ring
      add_mem' := by
        rintro x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩
        refine ⟨a1 + a2, p1 * t2 + p2 * t1, t1 * t2,
          P.add_mem (P.mul_mem_right _ hp1) (P.mul_mem_right _ hp2),
          fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩
        have : (x1 + x2) * algebraMap A (FractionRing A) (t1 * t2) =
            (x1 * algebraMap A (FractionRing A) t1) * algebraMap A (FractionRing A) t2 +
              (x2 * algebraMap A (FractionRing A) t2) * algebraMap A (FractionRing A) t1 := by
          rw [map_mul]; ring
        rw [this, h1, h2, ← map_mul, ← map_mul, ← map_add (f := _)]
        congr 1
        ring
      algebraMap_mem' := fun r => ⟨r, 0, 1, P.zero_mem, (Ideal.ne_top_iff_one P).mp
        (Ideal.IsPrime.ne_top ‹_›), by simp⟩ }
  have hyS : y ∈ S := ⟨0, a, algebraMap O A ϖ * s, haP, hws, by
    rw [hy, div_mul_cancel₀ _ hws0]; simp⟩
  have hBS : B ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hyS)

  have hcoe : ∀ r : O, ((algebraMap O B r : B) : FractionRing A) =
      algebraMap A (FractionRing A) (algebraMap O A r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply O A (FractionRing A)]
    rfl
  have hOB : Function.Injective (algebraMap O B) := by
    intro r1 r2 h
    apply hOA; apply hinj
    rw [← hcoe, ← hcoe, h]
  have : Module.Flat O B := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff x).mp hx
    rw [Submonoid.smul_def, Algebra.smul_def] at hr
    rcases mul_eq_zero.mp hr with h | h
    · exact absurd (hOB (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero r)
    · rw [h]; exact Submodule.zero_mem _
  have : Algebra.FiniteType A B :=
    (Subalgebra.fg_iff_finiteType B).mp (by simpa using Subalgebra.fg_adjoin_finset ({y} : Finset _))
  have : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance

  have hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤ := by
    rw [hmax, Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨a', p, t, hp, ht, h⟩ := hBS (↑u⁻¹ : B).2
    apply hmeet
    rw [eq_top_iff, hmapw]
    have hwb : algebraMap A (FractionRing A) (algebraMap O A ϖ) * ((↑u⁻¹ : B) : FractionRing A) = 1 := by
      rw [← hcoe, ← hu, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have hkey : algebraMap A (FractionRing A) (t - algebraMap O A ϖ * (a' * t + p)) = 0 := by
      rw [map_sub, map_mul, ← h]
      calc algebraMap A (FractionRing A) t - algebraMap A (FractionRing A) (algebraMap O A ϖ) *
            (((↑u⁻¹ : B) : FractionRing A) * algebraMap A (FractionRing A) t)
          = algebraMap A (FractionRing A) t - (algebraMap A (FractionRing A) (algebraMap O A ϖ) *
            ((↑u⁻¹ : B) : FractionRing A)) * algebraMap A (FractionRing A) t := by ring
        _ = 0 := by rw [hwb, one_mul, sub_self]
    have hk := hinj (hkey.trans (map_zero _).symm)
    have htw : t * (1 - algebraMap O A ϖ * a') ∈ P := by
      have : t * (1 - algebraMap O A ϖ * a') = algebraMap O A ϖ * p := by
        linear_combination hk
      rw [this]; exact P.mul_mem_left _ hp
    have h1 : 1 - algebraMap O A ϖ * a' ∈ P :=
      (Ideal.IsPrime.mem_or_mem ‹_› htw).resolve_left ht
    have : (1 : A) = (1 - algebraMap O A ϖ * a') + algebraMap O A ϖ * a' := by ring
    intro z _
    rw [← mul_one z, this, mul_add]
    exact Submodule.add_mem _ (Ideal.mem_sup_left (P.mul_mem_left _ h1))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
        (Ideal.subset_span rfl))))

  have heas : algebraMap A B (e * a * s) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : B => (x : FractionRing A)) h
    simp only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h'
    have := hinj (h'.trans (map_zero _).symm)
    rcases mul_eq_zero.mp this with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact he h3
      · exact ha0 h3
    · exact hsP (h2 ▸ P.zero_mem)
  obtain ⟨V, _, _, _, _, _, φ, hφ⟩ := av_point hsp _ heas
  let φA : A →ₐ[O] V := φ.comp (IsScalarTower.toAlgHom O A B)
  have hφA : ∀ x : A, φA x = φ (algebraMap A B x) := fun x => rfl
  rw [map_mul, map_mul, map_mul, map_mul] at hφ
  have hφe : φA e ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  have hφa : φA a ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  have hφs : φA s ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  obtain ⟨v, hv⟩ := hf V φA s a hfa hφa hφe

  have hab : algebraMap A B a = algebraMap O B ϖ * algebraMap A B s * ⟨y, hyB⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply O A (FractionRing A) ϖ, hy, ← map_mul]
    field_simp
  have hφab : φA a = algebraMap O V ϖ * φA s * φ ⟨y, hyB⟩ := by
    rw [hφA, hab, map_mul, map_mul, AlgHom.commutes]
    rfl
  rw [hφab] at hv
  have hunit : algebraMap O V ϖ * (v * φ ⟨y, hyB⟩) = 1 := by
    have h2 : φA s * (1 - algebraMap O V ϖ * (v * φ ⟨y, hyB⟩)) = 0 := by
      linear_combination hv
    have h3 := (mul_eq_zero.mp h2).resolve_left hφs
    linear_combination -h3
  exact not_isUnit_algebraMap_of_finite ϖ hϖm
    ⟨⟨algebraMap O V ϖ, v * φ ⟨y, hyB⟩, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain IsLocalRing

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]


variable (O F L) in
noncomputable def hoEquiv : HeightOneSpectrum (integralClosure O L) ≃
    {Q : Ideal (integralClosure O L) // Q.IsMaximal} where
  toFun v := ⟨v.asIdeal, v.isMaximal⟩
  invFun Q := (exists_heightOne O F L Q.1 Q.2).choose
  left_inv v := by
    apply HeightOneSpectrum.ext
    exact (exists_heightOne O F L v.asIdeal v.isMaximal).choose_spec
  right_inv Q := Subtype.ext (exists_heightOne O F L Q.1 Q.2).choose_spec


include F in
theorem norm_integral (b : integralClosure O L) (hb : b ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F (algebraMap (integralClosure O L) L b) = algebraMap O F
        (ϖ ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
          * u) := by
  haveI : Module.Finite O (integralClosure O L) :=
    IsIntegralClosure.finite O F L (integralClosure O L)
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  have hinjB : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L x,
      IsScalarTower.algebraMap_apply O (integralClosure O L) L y, hxy]
  haveI : NoZeroSMulDivisors O (integralClosure O L) := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left (fun h' => hinjB (h'.trans (map_zero _).symm))
  have hN := ReciprocityTheory.MultiplicativeHeights.Closed.normOrd O (integralClosure O L) b hb
  have hne : Algebra.norm O b ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at hN
    exact ENat.top_ne_coe _ hN
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hn := IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  rw [hn] at hN
  have hnN : n = ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}, Q.1.inertiaDeg O *
      Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
    exact_mod_cast hN
  have hsum : (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) = n := by
    rw [hnN]
    exact finsum_comp_equiv (hoEquiv (O := O) (F := F) (L := L))
      (f := fun Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal} => Q.1.inertiaDeg O *
        Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure O L) (nonZeroDivisors O)) L :=
    IsIntegralClosure.isLocalization O F L (integralClosure O L)
  refine ⟨u, u.isUnit, ?_⟩
  rw [Algebra.norm_localization O (nonZeroDivisors O) b, hu, hsum, mul_comm (u : O)]

theorem norm_eq_heightOne (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ v : HeightOneSpectrum (integralClosure O L),
          (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) * algebraMap O F u := by
  haveI : Finite (HeightOneSpectrum (integralClosure O L)) := by
    have hinj : Function.Injective (algebraMap O L) := by
      rw [IsScalarTower.algebraMap_eq O F L]
      exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
    obtain ⟨b, hbdef⟩ : ∃ b : (integralClosure O L), b = algebraMap O (integralClosure O L) ϖ := ⟨_, rfl⟩
    have hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ := by
      rw [hbdef]
      exact (IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm
    have hb : b ≠ 0 := by
      intro h0
      have h00 : algebraMap O L ϖ = 0 := by rw [← hbL, h0, map_zero]
      exact hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))
    have hmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
    have hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b} := by
      intro v
      have h1 := ((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem
      rw [← hbL, addv_count v b hb] at h1
      have h2 : 0 < Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
        rcases Nat.eq_zero_or_pos (Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h
        · rw [h, Nat.cast_zero] at h1
          exact absurd h1 (lt_irrefl 0)
        · exact h
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)
    have hspan : Ideal.span {b} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hb
    have hfin := Ideal.finite_factors hspan
    have huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} = Set.univ :=
      Set.eq_univ_of_forall hdvd
    rw [huniv] at hfin
    exact Set.finite_univ_iff.1 hfin
  haveI := Fintype.ofFinite (HeightOneSpectrum (integralClosure O L))
  obtain ⟨b1, b2, hb2m, hyb⟩ := IsFractionRing.div_surjective (A := (integralClosure O L)) y
  have hb2 : b2 ≠ 0 := nonZeroDivisors.ne_zero hb2m
  have hb1 : b1 ≠ 0 := by
    intro h
    apply hy
    rw [← hyb, h, map_zero, zero_div]
  have hb2L : algebraMap (integralClosure O L) L b2 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosure O L) L)).2 hb2
  have hyb2 : y * algebraMap (integralClosure O L) L b2 = algebraMap (integralClosure O L) L b1 := by
    rw [← hyb, div_mul_cancel₀ _ hb2L]
  have ha : algebraMap O F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O F)).2 hϖ.ne_zero
  obtain ⟨u1, hu1, h1⟩ := norm_integral (F := F) b1 hb1 hϖ
  obtain ⟨u2, hu2, h2⟩ := norm_integral (F := F) b2 hb2 hϖ
  have hmul : Algebra.norm F y * Algebra.norm F (algebraMap (integralClosure O L) L b2) =
      Algebra.norm F (algebraMap (integralClosure O L) L b1) := by
    rw [← map_mul, hyb2]
  rw [h1, h2] at hmul
  simp only [map_mul, map_pow] at hmul
  have hk : ∀ v : HeightOneSpectrum (integralClosure O L),
      WithTop.untopD 0 (addv L v y) = ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) - ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ) := by
    intro v
    have hm := (addv L v).map_mul y (algebraMap (integralClosure O L) L b2)
    rw [hyb2, addv_count v b1 hb1, addv_count v b2 hb2] at hm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (mt (addv L v).top_iff.1 hy)
    rw [← hk] at hm ⊢
    have hm' : ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) = k + ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ) := by
      exact_mod_cast hm
    rw [WithTop.untopD_coe]
    omega
  have hz : (∑ᶠ v : HeightOneSpectrum (integralClosure O L),
      (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) =
        (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) : ℕ) : ℤ) - (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) : ℕ) : ℤ) := by
    simp only [hk]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  refine ⟨u1 * ((hu2.unit⁻¹ : Oˣ) : O), hu1.mul (hu2.unit⁻¹).isUnit, ?_⟩
  have hU : algebraMap O F u2 * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, hu2.mul_val_inv, map_one]
  have haS : (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) ≠ 0 := pow_ne_zero _ ha
  rw [hz, zpow_sub₀ ha, zpow_natCast, zpow_natCast, map_mul]
  calc Algebra.norm F y
      = Algebra.norm F y * ((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) * algebraMap O F u2) *
          (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))))⁻¹ * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O)) := by
        rw [mul_assoc, mul_mul_mul_comm, mul_inv_cancel₀ haS, hU, one_mul, mul_one]
    _ = (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) * algebraMap O F u1 *
          (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))))⁻¹ * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O)) := by
        rw [hmul]
    _ = _ := by
        rw [div_eq_mul_inv]
        ring

theorem norm_eq_places (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ PlacesOver O L),
          (letI := resAlg (F := F) w
           (Module.finrank (ResidueField ((vRing w).comap (algebraMap F L)))
             (ResidueField (vRing w)) : ℤ)) * WithTop.untopD 0 (w y)) * algebraMap O F u := by
  obtain ⟨u, hu, h⟩ := norm_eq_heightOne (F := F) y hy hϖ
  refine ⟨u, hu, ?_⟩
  rw [h]
  congr 2
  obtain ⟨e, he⟩ := placesOver_bij (O := O) (F := F) (L := L)
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv e]
  apply finsum_congr
  intro v
  rw [he v]
  congr 1
  exact congrArg (fun n : ℕ => (n : ℤ)) (ValPl.resDeg_addv (F := F) v).symm


variable (O L) in
include F in
theorem placesOver_finite : (PlacesOver O L).Finite := by
  obtain ⟨e, he⟩ := placesOver_bij (O := O) (F := F) (L := L)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  obtain ⟨b, hbdef⟩ : ∃ b : integralClosure O L, b = algebraMap O (integralClosure O L) ϖ :=
    ⟨_, rfl⟩
  have hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ := by
    rw [hbdef]
    exact (IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm
  have hb : b ≠ 0 := by
    intro h0
    have h00 : algebraMap O L ϖ = 0 := by rw [← hbL, h0, map_zero]
    exact hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))
  have hmem : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b} := by
    intro v
    have h1 := ((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem
    rw [← hbL, addv_count v b hb] at h1
    have h2 : 0 < Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
      rcases Nat.eq_zero_or_pos (Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h
      · rw [h, Nat.cast_zero] at h1
        exact absurd h1 (lt_irrefl 0)
      · exact h
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)
  have hspan : Ideal.span {b} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hb
  have hfin := Ideal.finite_factors hspan
  have hfin' : Finite (HeightOneSpectrum (integralClosure O L)) := by
    have huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} =
        Set.univ := Set.eq_univ_of_forall hdvd
    rw [huniv] at hfin
    exact Set.finite_univ_iff.1 hfin
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ e)

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0
end

