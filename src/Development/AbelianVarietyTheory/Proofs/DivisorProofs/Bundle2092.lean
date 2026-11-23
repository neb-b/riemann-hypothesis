module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAwayOfFlatLift
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftAway

theorem mul_eq_zero_of_mem_map {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal R} (hI : I ^ 2 = 0) {u v : S} (hu : u ∈ I.map (algebraMap R S))
    (hv : v ∈ I.map (algebraMap R S)) : u * v = 0 := by
  have h := Ideal.mul_mem_mul hu hv
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  exact h

theorem frac_add {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B'] {a : B} {y z : B'}
    (hy : ∃ (n : ℕ) (b : B), y * algebraMap B B' a ^ n = algebraMap B B' b)
    (hz : ∃ (n : ℕ) (b : B), z * algebraMap B B' a ^ n = algebraMap B B' b) :
    ∃ (n : ℕ) (b : B), (y + z) * algebraMap B B' a ^ n = algebraMap B B' b := by
  obtain ⟨n, b, hb⟩ := hy
  obtain ⟨m, c, hc⟩ := hz
  refine ⟨n + m, b * a ^ m + c * a ^ n, ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← hb, ← hc]
  ring

theorem isLocalization_away_of_flat_lift (R B B' B₀ B₀' : Type) [CommRing R] [CommRing B]
    [CommRing B'] [CommRing B₀] [CommRing B₀'] [Algebra R B] [Algebra R B'] [Algebra B B']
    [IsScalarTower R B B'] [Algebra B₀ B₀'] (I : Ideal R) (hI : I ^ 2 = 0)
    (hflat : Module.Flat R B') (p : B →+* B₀) (p' : B' →+* B₀') (hp : Function.Surjective p)
    (hp' : Function.Surjective p') (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B))
    (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B'))
    (hcomm : ∀ b, p' (algebraMap B B' b) = algebraMap B₀ B₀' (p b)) (a : B)
    (hloc : IsLocalization.Away (p a) B₀') : IsLocalization.Away a B' := by
  haveI := hloc
  haveI := hflat
  set φ := algebraMap B B' with hφ
  have hφs : ∀ (r : R) (b : B), φ (r • b) = r • φ b := fun r b => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, ← IsScalarTower.algebraMap_apply]

  have hunit : IsUnit (φ a) := by
    have hu : IsUnit (p' (φ a)) := by
      rw [hcomm]; exact IsLocalization.Away.algebraMap_isUnit (p a)
    obtain ⟨v, hv⟩ := hp' (↑hu.unit⁻¹ : B₀')
    have hn : φ a * v - 1 ∈ I.map (algebraMap R B') := by
      rw [← hker', map_sub, map_mul, hv, map_one, IsUnit.mul_val_inv, sub_self]
    have h2 := mul_eq_zero_of_mem_map hI hn hn
    refine isUnit_iff_exists_inv.mpr ⟨v * (1 - (φ a * v - 1)), ?_⟩
    linear_combination (-1 : B') * h2

  have lift0 : ∀ y : B', ∃ (n : ℕ) (b : B), y * φ a ^ n - φ b ∈ I.map (algebraMap R B') := by
    intro y
    obtain ⟨⟨z, s, hs⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (p a)) (p' y)
    obtain ⟨n, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := hp z
    refine ⟨n, b, ?_⟩
    dsimp only at hz
    rw [← hker', map_sub, map_mul, map_pow, hcomm, hcomm, ← map_pow, hz, sub_self]
  have fracI : ∀ i ∈ I, ∀ y : B', ∃ (n : ℕ) (b : B),
      algebraMap R B' i * y * φ a ^ n = φ b := by
    intro i hi y
    obtain ⟨n, b, hb⟩ := lift0 y
    refine ⟨n, algebraMap R B i * b, ?_⟩
    have h0 := mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem (algebraMap R B') hi) hb
    rw [map_mul, hφ, ← IsScalarTower.algebraMap_apply]
    linear_combination h0
  have fracMem : ∀ z ∈ I.map (algebraMap R B'), ∃ (n : ℕ) (b : B), z * φ a ^ n = φ b := by
    intro z hz
    change z ∈ Submodule.span B' (algebraMap R B' '' I) at hz
    have key : ∀ c : B', ∃ (n : ℕ) (b : B), (c * z) * φ a ^ n = φ b := by
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        intro c
        obtain ⟨n, b, hb⟩ := fracI i hi c
        exact ⟨n, b, by rw [← hb]; ring⟩
      | zero => intro c; exact ⟨0, 0, by simp⟩
      | add x y _ _ hx hy => intro c; rw [mul_add]; exact frac_add (hx c) (hy c)
      | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
    simpa using key 1
  have surj : ∀ y : B', ∃ (n : ℕ) (b : B), y * φ a ^ n = φ b := by
    intro y
    obtain ⟨n, b, hb⟩ := lift0 y
    obtain ⟨m, c, hc⟩ := fracMem _ hb
    refine ⟨n + m, c + b * a ^ m, ?_⟩
    rw [map_add (f := _), map_mul, map_pow, ← hc]
    ring

  have kerI : ∀ x : B, φ x = 0 → ∃ n : ℕ, a ^ n * x ∈ I.map (algebraMap R B) := by
    intro x hx
    have h : algebraMap B₀ B₀' (p x) = 0 := by rw [← hcomm, hx, map_zero]
    obtain ⟨⟨s, hs⟩, h2⟩ :=
      (IsLocalization.map_eq_zero_iff (M := Submonoid.powers (p a)) (S := B₀') (p x)).mp h
    obtain ⟨n, rfl⟩ := hs
    refine ⟨n, (hker _).mp ?_⟩
    rw [map_mul, map_pow]
    exact h2
  have core : ∀ x ∈ I.map (algebraMap R B), φ x = 0 → ∃ N : ℕ, a ^ N * x = 0 := by
    intro x hxI hx
    change x ∈ Submodule.span B (algebraMap R B '' I) at hxI
    obtain ⟨k, c, g, rfl⟩ := Submodule.mem_span_set'.mp hxI
    choose i hi hgi using fun j => (g j).2
    have hrel : ∑ j, i j • φ (c j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hx, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, map_mul, Algebra.smul_def, ← hgi j, hφ,
        IsScalarTower.algebraMap_apply R B B', mul_comm]
    obtain ⟨l, A, y, hy, hA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := R) (M := B') (f := i) (x := fun j => φ (c j)) hrel
    choose m d hd using fun j => surj (y j)
    obtain ⟨M, hMdef⟩ : ∃ M, M = ∑ j, m j := ⟨_, rfl⟩
    have hMle : ∀ j, m j ≤ M := fun j => hMdef ▸
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ j)
    have hM : ∀ j, y j * φ a ^ M = φ (d j * a ^ (M - m j)) := by
      intro j
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hMle j)
      rw [ht, Nat.add_sub_cancel_left, map_mul, map_pow, ← hd j, pow_add]
      ring
    have he : ∀ q, φ (c q * a ^ M - ∑ j, A q j • (d j * a ^ (M - m j))) = 0 := by
      intro q
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_mul, map_pow, map_sum]
      simp_rw [hφs, ← hM]
      rw [show φ (c q) = ∑ j, A q j • y j from hy q, Finset.sum_mul]
      simp [smul_mul_assoc]
    choose n' hn' using fun q => kerI _ (he q)
    obtain ⟨N, hNdef⟩ : ∃ N, N = ∑ q, n' q := ⟨_, rfl⟩
    have hNle : ∀ q, n' q ≤ N := fun q => hNdef ▸
      Finset.single_le_sum (fun q _ => Nat.zero_le (n' q)) (Finset.mem_univ q)
    have hz : ∀ q, algebraMap R B (i q) *
        (a ^ N * (c q * a ^ M - ∑ j, A q j • (d j * a ^ (M - m j)))) = 0 := by
      intro q
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hNle q)
      rw [ht, pow_add, mul_comm (a ^ n' q), mul_assoc, mul_left_comm,
        mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem _ (hi q)) (hn' q), mul_zero]
    refine ⟨N + M, ?_⟩
    have step : ∀ q, a ^ (N + M) * (c q • (g q : B)) =
        ∑ j, algebraMap R B (i q * A q j) * (a ^ N * (d j * a ^ (M - m j))) := by
      intro q
      have h1 := hz q
      rw [← hgi q, smul_eq_mul]
      simp_rw [map_mul, Algebra.smul_def] at h1 ⊢
      rw [mul_sub, mul_sub, sub_eq_zero, Finset.mul_sum, Finset.mul_sum] at h1
      calc a ^ (N + M) * (c q * algebraMap R B (i q))
          = algebraMap R B (i q) * (a ^ N * (c q * a ^ M)) := by ring
        _ = ∑ j, algebraMap R B (i q) * (a ^ N * (algebraMap R B (A q j) * (d j * a ^ (M - m j)))) := h1
        _ = _ := Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.mul_sum, Finset.sum_congr rfl fun q _ => step q, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← map_sum, hA j, map_zero, zero_mul]
  have kerAll : ∀ x : B, φ x = 0 → ∃ N : ℕ, a ^ N * x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := kerI x hx
    obtain ⟨N, hN⟩ := core _ hn (by rw [map_mul, hx, mul_zero])
    exact ⟨N + n, by rw [pow_add, mul_assoc, hN]⟩
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    exact (map_pow φ a n).symm ▸ hunit.pow n
  · intro y
    obtain ⟨n, b, hb⟩ := surj y
    exact ⟨(b, ⟨a ^ n, n, rfl⟩), by simpa only [map_pow] using hb⟩
  · intro x y hxy
    obtain ⟨n, hn⟩ := kerAll (x - y) (by rw [map_sub, hxy, sub_self])
    exact ⟨⟨a ^ n, n, rfl⟩, by rw [← sub_eq_zero, ← mul_sub]; exact hn⟩

end GlobalTheory.LiftAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FiniteCoverProper

theorem isProper_of_lift_through_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  intro R _ _ X Y₀ Y τ s t i hτ hs hi hd ht h
  have hX : IsLocallyNoetherian X := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : LocallyOfFiniteType τ := by rw [← e]; infer_instance
    have : IsLocallyNoetherian (Sp R) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
    exact LocallyOfFiniteType.isLocallyNoetherian τ
  have hsep : IsSeparated τ := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : IsImmersion j := hj
    rw [← e]; infer_instance
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hq : IsQProjOver (t ≫ τ) := ht ▸ GlobalTheory.isQProjOver_comp_of_isFinite_general s hτ
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R Y X t τ hsep hq ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have hgen : genericPoints Y ⊆ Set.range i := GlobalTheory.genericPoints_subset_range_of_isDominant i
  have hr : Set.range x ⊆ Set.range i := hx.trans hgen
  have hx₀ : IsOpenImmersion.lift i x hr ≫ i = x := IsOpenImmersion.lift_fac i x hr
  obtain ⟨z, hz⟩ := h V K y (IsOpenImmersion.lift i x hr) (by rw [← Category.assoc, hx₀, hxy])
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z := by
    rw [← hx₀, Category.assoc]; exact hz.symm
  obtain ⟨⟨x', hx', -⟩⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z, commSq := ⟨hw⟩ }).exists_lift
  exact ⟨x', hx'⟩

end GlobalTheory.FiniteCoverProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackCoprodDescOfPiecesOverCoprod
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPullback_coprod_desc_of_pieces : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f : T ⟶ S) (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂), IsPullback v₁ f₁ f u₁ → IsPullback v₂ f₂ f u₂ → ∀ {X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂) (y : Y ⟶ T) (y₁ : Y₁ ⟶ T₁) (y₂ : Y₂ ⟶ T₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₁ ⟶ X₁) (i₂ : Y₂ ⟶ X₂), IsPullback j₁ y₁ y v₁ → IsPullback j₂ y₂ y v₂ → IsPullback i₁ y₁ x₁ f₁ → IsPullback i₂ y₂ x₂ f₂ → ∃ i : Y ⟶ X₁ ⨿ X₂, j₁ ≫ i = i₁ ≫ Limits.coprod.inl ∧ j₂ ≫ i = i₂ ≫ Limits.coprod.inr ∧ IsPullback i y (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) f := by
  intro S S₁ S₂ T T₁ T₂ u₁ u₂ hS v₁ v₂ hT f f₁ f₂ hf₁ hf₂ X₁ X₂ Y Y₁ Y₂ x₁ x₂ y y₁ y₂ j₁ j₂ i₁ i₂
    hj₁ hj₂ hi₁ hi₂
  obtain ⟨hS⟩ := hS
  obtain ⟨hT⟩ := hT
  obtain ⟨hY⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk j₁ j₂) y₁ y₂ y hj₁.w.symm hj₂.w.symm).mpr ⟨hj₁, hj₂⟩
  let x : X₁ ⨿ X₂ ⟶ S := Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)
  obtain ⟨hX₁, hX₂⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hS) (Limits.BinaryCofan.mk (Limits.coprod.inl : X₁ ⟶ X₁ ⨿ X₂)
    Limits.coprod.inr) x₁ x₂ x (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm).mp ⟨Limits.coprodIsCoprod X₁ X₂⟩
  obtain ⟨i, hi₁', hi₂'⟩ := Limits.BinaryCofan.IsColimit.desc' hY
    (i₁ ≫ Limits.coprod.inl) (i₂ ≫ Limits.coprod.inr)
  have e₁ : j₁ ≫ i = i₁ ≫ Limits.coprod.inl := hi₁'
  have e₂ : j₂ ≫ i = i₂ ≫ Limits.coprod.inr := hi₂'
  refine ⟨i, e₁, e₂, ?_⟩
  have H₁ : IsPullback (j₁ ≫ i) y₁ x (v₁ ≫ f) := by
    rw [e₁, hf₁.w]; exact hi₁.paste_horiz hX₁
  have H₂ : IsPullback (j₂ ≫ i) y₂ x (v₂ ≫ f) := by
    rw [e₂, hf₂.w]; exact hi₂.paste_horiz hX₂
  have w : i ≫ x = y ≫ f := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · change j₁ ≫ i ≫ x = j₁ ≫ y ≫ f
      rw [← Category.assoc j₁ i x, H₁.w, ← Category.assoc j₁ y f, hj₁.w, Category.assoc]
    · change j₂ ≫ i ≫ x = j₂ ≫ y ≫ f
      rw [← Category.assoc j₂ i x, H₂.w, ← Category.assoc j₂ y f, hj₂.w, Category.assoc]
  let c : Y ⟶ Limits.pullback x f := Limits.pullback.lift i y w
  have hcf : c ≫ Limits.pullback.fst x f = i := Limits.pullback.lift_fst _ _ _
  have hcs : c ≫ Limits.pullback.snd x f = y := Limits.pullback.lift_snd _ _ _
  have Q₁ : IsPullback (j₁ ≫ c) y₁ (Limits.pullback.snd x f) v₁ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₁)
      (by rw [Category.assoc, hcs]; exact hj₁.w)
      (IsPullback.of_hasPullback x f)
  have Q₂ : IsPullback (j₂ ≫ c) y₂ (Limits.pullback.snd x f) v₂ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₂)
      (by rw [Category.assoc, hcs]; exact hj₂.w)
      (IsPullback.of_hasPullback x f)
  obtain ⟨hP⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk (j₁ ≫ c) (j₂ ≫ c)) y₁ y₂ (Limits.pullback.snd x f)
    Q₁.w.symm Q₂.w.symm).mpr ⟨Q₁, Q₂⟩
  have hc : c = (hY.coconePointUniqueUpToIso hP).hom := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.left⟩).symm
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.right⟩).symm
  haveI : IsIso c := by rw [hc]; exact Iso.isIso_hom _
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) hcf hcs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfOpenBaseChangeEqPreimage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isPullback_of_open_part_eq_preimage :
    ∀ (S S₁ P G : Scheme.{0}) (p : P ⟶ S) (s : S₁ ⟶ S) (e : G ⟶ P) (c : G ⟶ S₁) (hw : e ≫ p = c ≫ s), IsOpenImmersion (Limits.pullback.lift e c hw) → ∀ V : P.Opens, (∀ w : ↥(Limits.pullback p s), Limits.pullback.fst p s w ∈ V ↔ w ∈ Set.range (Limits.pullback.lift e c hw)) → ∃ e' : G ⟶ V.toScheme, e' ≫ V.ι = e ∧ IsPullback e' c (V.ι ≫ p) s := by
  intro S S₁ P G p s e c hw hl V hV
  have hlf : Limits.pullback.lift e c hw ≫ Limits.pullback.fst p s = e :=
    Limits.pullback.lift_fst _ _ _
  have hls : Limits.pullback.lift e c hw ≫ Limits.pullback.snd p s = c :=
    Limits.pullback.lift_snd _ _ _
  generalize Limits.pullback.lift e c hw = l at hl hV hlf hls
  have hr : Set.range e ⊆ Set.range V.ι := by
    rintro _ ⟨g, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h := (hV (l g)).mpr ⟨g, rfl⟩
    rw [← Scheme.Hom.comp_apply, hlf] at h
    exact h
  have he' : IsOpenImmersion.lift V.ι e hr ≫ V.ι = e := IsOpenImmersion.lift_fac _ _ _
  generalize IsOpenImmersion.lift V.ι e hr = e' at he'
  have hcomm : e' ≫ V.ι ≫ p = c ≫ s := by rw [← Category.assoc, he', hw]
  have hk : ∀ t : PullbackCone (V.ι ≫ p) s, ∃ q : t.pt ⟶ G,
      q ≫ l = Limits.pullback.lift (t.fst ≫ V.ι) t.snd
        ((Category.assoc _ _ _).trans t.condition) := by
    intro t
    refine ⟨IsOpenImmersion.lift l _ ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    refine (hV _).mp ?_
    rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst, Scheme.Hom.comp_apply]
    exact (t.fst x).2
  choose q hq using hk
  refine ⟨e', he', ⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm q ?_ ?_ ?_⟩⟩
  · intro t
    rw [← cancel_mono V.ι, Category.assoc, he', ← hlf, ← Category.assoc, hq,
      Limits.pullback.lift_fst]
  · intro t
    conv_lhs => rw [← hls]
    rw [← Category.assoc, hq, Limits.pullback.lift_snd]
  · intro t m h₁ h₂
    rw [← cancel_mono l, hq]
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hlf, Limits.pullback.lift_fst, ← h₁, Category.assoc, he']
    · rw [Category.assoc, hls, Limits.pullback.lift_snd, h₂]

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOneProdKernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RigDesc

theorem isPullback_one_prod {S : Scheme.{0}} (A : Over S) {V V' : Over S} (v : V ⟶ V') :
    IsPullback (lift (fst A V) (snd A V ≫ v)).left (snd A V).left (snd A V').left v.left := by
  have hT : IsPullback (fst A V).left (snd A V).left A.hom V.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A V').left (snd A V').left A.hom V'.hom := IsPullback.of_hasPullback _ _
  have m₁ : (lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left = (fst A V).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : (lift (fst A V) (snd A V ≫ v)).left ≫ (snd A V').left = (snd A V).left ≫ v.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback ((lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left) (snd A V).left A.hom
      (v.left ≫ V'.hom) := by
    rw [m₁, Over.w v]; exact hT
  exact IsPullback.of_right hT' m₂ hY

theorem isPullback_one_prod_kernel {S : Scheme.{0}} (A Y Y' W : Over S) (c : Y' ⟶ Y) (w₁ w₂ : W ⟶ Y')
    (hK : IsPullback w₁.left w₂.left c.left c.left) :
    IsPullback (lift (fst A W) (snd A W ≫ w₁)).left (lift (fst A W) (snd A W ≫ w₂)).left
      (lift (fst A Y') (snd A Y' ≫ c)).left (lift (fst A Y') (snd A Y' ≫ c)).left := by
  have Hc := isPullback_one_prod A c
  have H₂ := isPullback_one_prod A w₂
  have outer := H₂.flip.paste_horiz hK
  have e₁ : (lift (fst A W) (snd A W ≫ w₁)).left ≫ (snd A Y').left = (snd A W).left ≫ w₁.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (lift (fst A Y') (snd A Y' ≫ c)).left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext hK.w
  refine IsPullback.of_right (h₁₂ := (snd A Y').left) (h₂₂ := (snd A Y).left) ?_ ?_ Hc.flip
  · rw [e₁, e₂]; exact outer
  · rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc,
      lift_snd_assoc, Category.assoc, Category.assoc, hw]

theorem triv_of_triv_zero_of_fpqc : ∀ (S : Scheme.{0}) (X Y Y' : Over S) [GrpObj X], IsAbelianScheme X →
    ∀ (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → ∀ D : LB (X ⊗ Y).left, D.IsLB →
    Triv (ev D (1 : Y ⟶ X) (𝟙 Y)) → Triv (ev D (fst X Y') (snd X Y' ≫ c)) → Triv D := by
  intro S X Y Y' _ hA c hfl hsu hqc L hL h0 h1
  let F : X ⊗ Y' ⟶ X ⊗ Y := lift (fst X Y') (snd X Y' ≫ c)
  let e : Y ⟶ X ⊗ Y := lift 1 (𝟙 Y)
  let e' : Y' ⟶ X ⊗ Y' := lift 1 (𝟙 Y')
  change Triv (L.pull e.left) at h0
  change Triv (L.pull F.left) at h1
  have hEF : e' ≫ F = c ≫ e := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [e, e', F]
  have hep : e' ≫ snd X Y' = 𝟙 Y' := lift_snd _ _
  have H : IsPullback F.left (snd X Y').left (snd X Y).left c.left := isPullback_one_prod X c
  have hF₁ : Flat F.left := MorphismProperty.of_isPullback H.flip hfl
  have hF₂ : Surjective F.left := MorphismProperty.of_isPullback H.flip hsu
  have hF₃ : QuasiCompact F.left := MorphismProperty.of_isPullback H.flip hqc
  let W : Over S := Over.mk (pullback.fst c.left c.left ≫ Y'.hom)
  let w₁ : W ⟶ Y' := Over.homMk (pullback.fst c.left c.left) rfl
  let w₂ : W ⟶ Y' := Over.homMk (pullback.snd c.left c.left) (by
    show pullback.snd c.left c.left ≫ Y'.hom = pullback.fst c.left c.left ≫ Y'.hom
    rw [← Over.w c, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext pullback.condition
  have hK : IsPullback w₁.left w₂.left c.left c.left := IsPullback.of_hasPullback c.left c.left
  let g₁ : X ⊗ W ⟶ X ⊗ Y' := lift (fst X W) (snd X W ≫ w₁)
  let g₂ : X ⊗ W ⟶ X ⊗ Y' := lift (fst X W) (snd X W ≫ w₂)
  have hKP : IsPullback g₁.left g₂.left F.left F.left := isPullback_one_prod_kernel X Y Y' W c w₁ w₂ hK
  have hg : g₁.left ≫ F.left = g₂.left ≫ F.left := hKP.w
  obtain ⟨g, hgg⟩ := h0
  obtain ⟨t, ht⟩ := h1
  have n₁ : (snd X Y' ≫ e').left ≫ F.left = (snd X Y' ≫ c).left ≫ e.left := by
    rw [← Over.comp_left, ← Over.comp_left, Category.assoc, hEF, Category.assoc]
  obtain ⟨t', ht', hv⟩ := exists_gen hL (K' := PUnit) (φ' := fun _ => F.left) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁]
      simp)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (snd X Y' ≫ e').left)))
      (LB.pullGen L _ _ g (snd X Y' ≫ c).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hgg _))
  have norm : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z) (J), Geo.Tor.Good L z J →
      val t' (r ≫ e'.left) z J = val g (r ≫ c.left) z J := by
    intro Z r z J hJ
    have a₁ : (r ≫ e'.left) ≫ (snd X Y' ≫ e').left = r ≫ e'.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    have a₂ : (r ≫ e'.left) ≫ (snd X Y' ≫ c).left = r ≫ c.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, a₁, a₂, mul_inv_cancel,
      _root_.one_mul]
  refine GlobalTheory.FlatDescent.triv_of_gen_descent L hL F.left hF₁ hF₂ hF₃ g₁.left g₂.left hKP t' ht' (fun z J hJ => ?_)
  let o : W ⟶ X ⊗ W := lift 1 (𝟙 W)
  have hg1 : o.left ≫ g₁.left = w₁.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₁, e']
  have hg2 : o.left ≫ g₂.left = w₂.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₂, e']
  have ho : o.left ≫ (snd X W).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hwc : w₁.left ≫ c.left = w₂.left ≫ c.left := by rw [← Over.comp_left, ← Over.comp_left, hw]
  have key2 := gen_unique' hL (φ := fun _ : PUnit => g₁.left ≫ F.left) (ε := fun _ => (1 : ℤ))
    (φ' := fun _ : PUnit => g₂.left ≫ F.left) (ε' := fun _ => 1)
    (fun U _ k => by simp only [hg]) (snd X W).left o.left ho (surj_snd GlobalTheory.SemiRigid.globalFns hA W)
    (u := LB.pullGen L _ _ t' g₁.left) (u' := LB.pullGen L _ _ t' g₂.left)
    (DVR.pullGen_isGen _ _ _ _ ht' _) (DVR.pullGen_isGen _ _ _ _ ht' _)
    (fun y I hI => by rw [val_pull hI, val_pull hI, hg1, hg2, norm _ _ _ _ hI, norm _ _ _ _ hI, hwc])
    _ (𝟙 _) z J hJ
  rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at key2

end GlobalTheory.RigDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionFamilyZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Pinch

def IsSecFam {X : Scheme.{0}} (L : LB X) {J : Type} (D : J → X.Opens) (k : J → L.ι)
    (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)) : Prop :=
  ∀ (j j' : J) (z : X) (hz : z ∈ D j) (hz' : z ∈ D j'),
    (X.presheaf.germ (D j) z hz).hom (e j) =
      (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hD j hz, hD j' hz'⟩).hom (L.g (k j) (k j')).val *
        (X.presheaf.germ (D j') z hz').hom (e j')

end GlobalTheory.Pinch
end
end

