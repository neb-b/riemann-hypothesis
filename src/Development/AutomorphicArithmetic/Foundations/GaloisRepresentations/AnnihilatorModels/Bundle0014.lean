module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.ExistsAlg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma exists_alg {κ B Λ : Type} [Field κ] [CommRing B] [Algebra κ B] [CommRing Λ] [Algebra κ Λ]
    (u : Sp Λ ⟶ Sp B) (h : u ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ)) :
    ∃ ν : B →ₐ[κ] Λ, u = spMap ν.toRingHom := by
  obtain ⟨φ, rfl⟩ : ∃ φ, u = Spec.map φ := ⟨Spec.preimage u, (Spec.map_preimage u).symm⟩
  have hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ Λ := by
    have h' : Spec.map (CommRingCat.ofHom (algebraMap κ B) ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap κ Λ)) := by
      rw [Spec.map_comp]
      exact h
    have h'' := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom h''
  refine ⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, ?_⟩
  rfl

theorem UpperTheory.Gal.crystallineComparison.Mod.infE_of :
    SplitAlg → InfE := by
  intro hS κ _ A _ P d hRep hcard Λ _ _ _ ε g hP hInf
  obtain ⟨B, _, _, hfin, hfree, hrank, i, hmono, hiff⟩ := hRep
  haveI : Mono i := hmono
  have key : ∀ (Λ' : Type) [CommRing Λ'] [Algebra κ Λ'] (ν : B →ₐ[κ] Λ'),
      spMap ν.toRingHom ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ') := by
    intro Λ' _ _ ν
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp
  have hid : spMap (algebraMap κ κ) = 𝟙 (Sp κ) := by simp [spMap]
  let F : (B →ₐ[κ] κ) → { g // P (𝟙_ (Over (Sp κ))) g } := fun ν =>
    ⟨Over.homMk (U := 𝟙_ (Over (Sp κ))) (V := algPt κ B) (spMap ν.toRingHom)
        (by
          show spMap ν.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _
          rw [key κ ν, hid]) ≫ i,
      (hiff _ _).1 ⟨_, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro ν₁ ν₂ h
      have h1 := congrArg Subtype.val h
      have h2 := (cancel_mono i).1 h1
      have h3 := congrArg CommaMorphism.left h2
      have h4 : CommRingCat.ofHom ν₁.toRingHom = CommRingCat.ofHom ν₂.toRingHom :=
        Spec.map_injective h3
      ext x
      exact congrArg (fun φ => φ.hom x) h4
    · rintro ⟨g₀, hg₀⟩
      obtain ⟨y, hy⟩ := (hiff _ _).2 hg₀
      obtain ⟨ν, hν⟩ := exists_alg (Λ := κ) y.left (by
        rw [hid]
        exact Over.w y)
      refine ⟨ν, Subtype.ext ?_⟩
      show _ ≫ i = g₀
      rw [← hy]
      congr 1
      apply Over.OverMorphism.ext
      simp [hν]
  have hpts : Nat.card (B →ₐ[κ] κ) = Module.finrank κ B := by
    rw [hrank, ← hcard]
    exact Nat.card_congr (Equiv.ofBijective F hF)
  obtain ⟨y, hy⟩ := (hiff _ _).2 hP
  obtain ⟨ν, hν⟩ := exists_alg y.left (Over.w y)
  have hsplit := hS κ B Λ hpts ε ν
  have e1 : spMap ν.toRingHom = spMap (algebraMap κ Λ) ≫ spMap (ε.comp ν).toRingHom := by
    conv_lhs => rw [hsplit]
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e2 : spMap ε.toRingHom ≫ spMap (algebraMap κ Λ) = 𝟙 (Sp κ) := by
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show ε.toRingHom.comp (algebraMap κ Λ) = RingHom.id κ from by ext r; simp]
    simp
  have gl : g.left = y.left ≫ i.left := by
    rw [← hy]
    rfl
  have one_l : ∀ T : Over (Sp κ), (1 : T ⟶ A).left = T.hom ≫ η[A].left := by
    intro T
    show (toUnit T ≫ η[A]).left = _
    rw [Over.comp_left]
    congr 1
  have hI : spMap ε.toRingHom ≫ g.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left := hInf
  rw [one_l, gl, hν, e1] at hI
  simp only [← Category.assoc, e2, Category.id_comp] at hI
  apply Over.OverMorphism.ext
  rw [one_l, gl, hν, e1, Category.assoc, hI]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MAlgOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.algOf_of :
    AlgOf := by
  intro S K h hfin hflat V _ _ z
  let h' : pullback h z ⟶ Sp V := pullback.snd h z
  haveI : IsFinite h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hfin
  haveI : Flat h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hflat
  haveI : IsAffine (pullback h z) := isAffine_of_isAffineHom h'
  let φ : CommRingCat.of V ⟶ Γ(pullback h z, ⊤) := (Scheme.ΓSpecIso (.of V)).inv ≫ h'.appTop
  letI alg : Algebra V Γ(pullback h z, ⊤) := φ.hom.toAlgebra
  have hfinite : φ.hom.Finite := by
    have h1 : h'.appTop.hom.Finite := Scheme.Hom.finite_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv).2
    exact RingHom.Finite.comp h1 h2
  have hflat' : φ.hom.Flat := by
    have h1 : h'.appTop.hom.Flat := Scheme.Hom.flat_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv)
    exact RingHom.Flat.comp h2 h1
  haveI mf : Module.Finite V Γ(pullback h z, ⊤) := hfinite
  haveI mfl : Module.Flat V Γ(pullback h z, ⊤) := hflat'
  refine ⟨Γ(pullback h z, ⊤), inferInstance, alg, (pullback h z).isoSpec.inv ≫ pullback.fst h z, mf,
    Module.free_of_flat_of_isLocalRing, ?_⟩
  have key : (pullback h z).isoSpec.inv ≫ h' = spMap (algebraMap V Γ(pullback h z, ⊤)) := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have sq : IsPullback (pullback h z).isoSpec.inv (spMap (algebraMap V Γ(pullback h z, ⊤))) h' (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, key]⟩
  have := sq.paste_horiz (IsPullback.of_hasPullback h z)
  rwa [Category.id_comp] at this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MChainLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem finrank_quotient_eq_add_finrank_ker_factor (κ Λ : Type) [Field κ] [CommRing Λ] [Algebra κ Λ]
    [Module.Finite κ Λ] (I J : Ideal Λ) (h : I ≤ J) :
    Module.finrank κ (Λ ⧸ I) = Module.finrank κ (Λ ⧸ J) +
      Module.finrank κ (LinearMap.ker (Ideal.Quotient.factorₐ κ h).toLinearMap) := by
  haveI : Module.Finite κ (Λ ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ I).toLinearMap Ideal.Quotient.mk_surjective
  have hs : Function.Surjective (Ideal.Quotient.factorₐ κ h).toLinearMap :=
    Ideal.Quotient.factor_surjective h
  rw [← LinearMap.finrank_range_add_finrank_ker (Ideal.Quotient.factorₐ κ h).toLinearMap,
    LinearMap.range_eq_top.mpr hs, finrank_top]

set_option maxHeartbeats 400000 in
private theorem ideal_eq_span_pow_of_finrank (κ Λ : Type) [Field κ] [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ]
    [Module.Finite κ Λ] (ε : Λ →ₐ[κ] κ) (t : Λ)
    (ht : IsLocalRing.maximalIdeal Λ = Ideal.span {t}) (q : ℕ) :
    ∀ J : Ideal Λ, Module.finrank κ (Λ ⧸ J) = q → J = Ideal.span {t ^ q} := by
  classical
  intro J hJ
  haveI : IsArtinianRing Λ := IsArtinianRing.of_finite κ Λ
  haveI hfin : ∀ I : Ideal Λ, Module.Finite κ (Λ ⧸ I) := fun I ↦
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ I).toLinearMap Ideal.Quotient.mk_surjective
  have tm : t ∈ IsLocalRing.maximalIdeal Λ := by
    rw [ht]
    exact Ideal.subset_span rfl
  have mem_m : ∀ a, a ∈ IsLocalRing.maximalIdeal Λ ↔ ∃ b, b * t = a := fun a ↦ by
    rw [ht, Ideal.mem_span_singleton']
  have mem_pow : ∀ k x, x ∈ Ideal.span {t ^ k} ↔ ∃ a, a * t ^ k = x := fun k x ↦
    Ideal.mem_span_singleton'
  have unit_of : ∀ a : Λ, a ∉ IsLocalRing.maximalIdeal Λ → IsUnit a := fun a ha ↦ by
    by_contra hu
    exact ha ((IsLocalRing.mem_maximalIdeal a).2 hu)
  have hker : ∀ a : Λ, a - algebraMap κ Λ (ε a) ∈ IsLocalRing.maximalIdeal Λ := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map ε
    simp at this
  have dec : ∀ a : Λ, ∃ b, a = algebraMap κ Λ (ε a) + b * t := by
    intro a
    obtain ⟨b, hb⟩ := (mem_m _).1 (hker a)
    exact ⟨b, by rw [hb]; ring⟩
  have drop : ∀ k, t ^ k ∈ Ideal.span {t ^ (k + 1)} → t ^ k = 0 := by
    intro k hk
    obtain ⟨a, ha⟩ := (mem_pow _ _).1 hk
    have hu : IsUnit (1 - a * t) := unit_of _ (fun h ↦ by
      have h1 : (1 : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
        have := (IsLocalRing.maximalIdeal Λ).add_mem h
          ((IsLocalRing.maximalIdeal Λ).mul_mem_left a tm)
        simpa using this
      exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one)
    have e : t ^ k * (1 - a * t) = 0 := by
      calc t ^ k * (1 - a * t) = t ^ k - a * t ^ (k + 1) := by ring
        _ = 0 := by rw [ha, sub_self]
    exact hu.mul_left_eq_zero.1 e
  have hNex : ∃ N, t ^ N = 0 := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Λ)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, ht] at hN
    refine ⟨N, ?_⟩
    have h := Ideal.pow_mem_pow (Ideal.subset_span rfl : t ∈ Ideal.span {t}) N
    rw [hN] at h
    simpa using h
  obtain ⟨n, hn, hlt⟩ : ∃ n, t ^ n = 0 ∧ ∀ k < n, t ^ k ≠ 0 :=
    ⟨Nat.find hNex, Nat.find_spec hNex, fun k hk ↦ Nat.find_min hNex hk⟩
  have dimB : ∀ k ≤ n, Module.finrank κ (Λ ⧸ Ideal.span {t ^ k}) = k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [pow_zero, Ideal.span_singleton_one]
      haveI : Subsingleton (Λ ⧸ (⊤ : Ideal Λ)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Module.finrank_zero_of_subsingleton
    | succ k ih =>
      intro hk
      have hle : Ideal.span {t ^ (k + 1)} ≤ Ideal.span {t ^ k} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow t (Nat.le_succ k))
      rw [finrank_quotient_eq_add_finrank_ker_factor κ Λ _ _ hle, ih (by omega)]
      congr 1
      set v := Ideal.Quotient.mk (Ideal.span {t ^ (k + 1)}) (t ^ k) with hv
      apply le_antisymm
      · have hsub : LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap ≤ κ ∙ v := by
          intro z hz
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
          rw [LinearMap.mem_ker] at hz
          have hx : x ∈ Ideal.span {t ^ k} := by
            rw [← Ideal.Quotient.eq_zero_iff_mem]
            simpa using hz
          obtain ⟨a, rfl⟩ := (mem_pow _ _).1 hx
          obtain ⟨b, hb⟩ := dec a
          rw [Submodule.mem_span_singleton]
          refine ⟨ε a, ?_⟩
          have e : a * t ^ k = algebraMap κ Λ (ε a) * t ^ k + b * t ^ (k + 1) := by
            linear_combination (t ^ k) * hb
          have hb0 : Ideal.Quotient.mk (Ideal.span {t ^ (k + 1)}) (b * t ^ (k + 1)) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ b (Ideal.subset_span rfl))
          rw [e, map_add (f := _), hb0, add_zero, map_mul, Algebra.smul_def, Ideal.Quotient.mk_algebraMap]
        exact (Submodule.finrank_mono hsub).trans
          (by simpa using finrank_span_le_card ({v} : Set (Λ ⧸ Ideal.span {t ^ (k + 1)})))
      · have hvk : v ∈ LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap := by
          rw [LinearMap.mem_ker]
          simp only [v, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        have hv0 : v ≠ 0 := by
          intro h0
          exact hlt k (by omega) (drop k (Ideal.Quotient.eq_zero_iff_mem.1 h0))
        have hne : LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap ≠ ⊥ := fun hb ↦
          hv0 ((Submodule.mem_bot κ).1 (hb ▸ hvk))
        exact Nat.one_le_iff_ne_zero.2 (fun h ↦ hne (Submodule.finrank_eq_zero.1 h))
  have factA : ∃ k ≤ n, J = Ideal.span {t ^ k} := by
    by_cases h0 : J ≤ Ideal.span {t ^ n}
    · refine ⟨n, le_rfl, le_antisymm h0 ?_⟩
      rw [hn, Ideal.span_singleton_eq_bot.2 rfl]
      exact bot_le
    · have hex : ∃ k, ¬ J ≤ Ideal.span {t ^ k} := ⟨n, h0⟩
      obtain ⟨k0, hk0, hk0n, hmin⟩ : ∃ k0, ¬ J ≤ Ideal.span {t ^ k0} ∧ k0 ≤ n ∧
          ∀ j < k0, J ≤ Ideal.span {t ^ j} :=
        ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex h0,
          fun j hj ↦ not_not.1 (Nat.find_min hex hj)⟩
      have hk0pos : k0 ≠ 0 := by
        intro hz
        apply hk0
        rw [hz, pow_zero, Ideal.span_singleton_one]
        exact le_top
      obtain ⟨k, rfl⟩ : ∃ k, k0 = k + 1 := Nat.exists_eq_succ_of_ne_zero hk0pos
      have hJk : J ≤ Ideal.span {t ^ k} := hmin k (by omega)
      obtain ⟨x, hxJ, hx⟩ := SetLike.not_le_iff_exists.1 hk0
      obtain ⟨a, rfl⟩ := (mem_pow _ _).1 (hJk hxJ)
      have ha : a ∉ IsLocalRing.maximalIdeal Λ := by
        intro ham
        obtain ⟨b, rfl⟩ := (mem_m _).1 ham
        apply hx
        rw [mem_pow]
        exact ⟨b, by ring⟩
      obtain ⟨u, hu⟩ := unit_of a ha
      refine ⟨k, by omega, le_antisymm hJk ?_⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have e : t ^ k = ↑u⁻¹ * (a * t ^ k) := by
        rw [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
      rw [e]
      exact J.mul_mem_left _ hxJ
  obtain ⟨k, hkn, rfl⟩ := factA
  rw [dimB k hkn] at hJ
  rw [hJ]

theorem UpperTheory.Gal.crystallineComparison.Mod.chainLoc_of :
    ChainLoc := by
  intro κ Λ _ _ _ _ _ ε t ht J q hq
  exact ideal_eq_span_pow_of_finrank κ Λ ε t ht q J hq
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MChainRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.chainRing_of :
    ChainLoc → ChainRing := by
  intro hC κ B B' Λ _ _ _ _ _ _ _ _ _ π ε' _ q hπ hq hex εΛ g hg
  obtain ⟨t, ht, htm⟩ := hex
  set m : Ideal B := RingHom.ker (ε'.comp π).toRingHom with hm
  set m' : Ideal B' := RingHom.ker ε'.toRingHom with hm'
  haveI : m.IsPrime := RingHom.ker_isPrime _
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI : Module.Finite κ B' := Module.Finite.of_surjective π.toLinearMap hπ
  haveI : IsArtinianRing B' := IsArtinianRing.of_finite κ B'
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime m)) :=
    IsArtinianRing.localization_surjective m.primeCompl _
  have hsurj' : Function.Surjective (algebraMap B' (Localization.AtPrime m')) :=
    IsArtinianRing.localization_surjective m'.primeCompl _
  haveI : Module.Finite κ (Localization.AtPrime m) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom κ B (Localization.AtPrime m)).toLinearMap hsurj
  haveI : IsArtinianRing (Localization.AtPrime m) := IsArtinianRing.of_finite κ _
  have hmem : ∀ x, x ∈ m ↔ ε' (π x) = 0 := fun x => by simp [m, RingHom.mem_ker]
  have hmem' : ∀ y, y ∈ m' ↔ ε' y = 0 := fun y => by simp [m', RingHom.mem_ker]
  have hunit : ∀ s, ε' (π s) ≠ 0 → IsUnit (g s) := by
    intro s hs
    by_contra hns
    have hker : (RingHom.ker εΛ.toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨algebraMap κ Λ c, by simp⟩)
    have heq : RingHom.ker εΛ.toRingHom = IsLocalRing.maximalIdeal Λ := IsLocalRing.eq_maximalIdeal hker
    have hin : g s ∈ RingHom.ker εΛ.toRingHom := by
      rw [heq]
      exact (IsLocalRing.mem_maximalIdeal _).2 hns
    have h2 : εΛ (g s) = ε' (π s) := by
      simpa using congrArg (fun f : B →ₐ[κ] κ => f s) hg
    apply hs
    rw [← h2]
    simpa [RingHom.mem_ker] using hin
  have hφu : ∀ y : m.primeCompl,
      IsUnit (((IsScalarTower.toAlgHom κ B' (Localization.AtPrime m')).comp π) y) := by
    rintro ⟨y, hy⟩
    have hy' : π y ∈ m'.primeCompl := by
      show π y ∉ m'
      rw [hmem']
      exact fun h => hy ((hmem y).2 h)
    exact IsLocalization.map_units (Localization.AtPrime m') (⟨π y, hy'⟩ : m'.primeCompl)
  let φ : Localization.AtPrime m →ₐ[κ] Localization.AtPrime m' := IsLocalization.liftAlgHom hφu
  have hφ : ∀ x, φ (algebraMap B _ x) = algebraMap B' (Localization.AtPrime m') (π x) := fun x => by
    simp [φ, IsLocalization.lift_eq]
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := hsurj' z
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨_, hφ x⟩
  have hεu : ∀ y : m.primeCompl, IsUnit ((ε'.comp π) y) := by
    rintro ⟨y, hy⟩
    exact isUnit_iff_ne_zero.2 (fun h => hy ((hmem y).2 h))
  let ε : Localization.AtPrime m →ₐ[κ] κ := IsLocalization.liftAlgHom hεu
  have hmapm : m.map (algebraMap B (Localization.AtPrime m)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := Localization.AtPrime.map_eq_maximalIdeal
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime m) =
      Ideal.span {algebraMap B (Localization.AtPrime m) t} := by
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal (Localization.AtPrime m))
        (IsNoetherian.noetherian _)
      · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      · rw [Ideal.smul_eq_mul, ← hmapm]
        calc m.map (algebraMap B (Localization.AtPrime m))
            ≤ (Ideal.span {t} ⊔ m ^ 2).map (algebraMap B (Localization.AtPrime m)) := Ideal.map_mono htm
          _ = _ := by rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, Set.image_singleton, sq]
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← hmapm]
      exact Ideal.mem_map_of_mem _ ht
  have hJ : RingHom.ker φ = Ideal.span {(algebraMap B (Localization.AtPrime m) t) ^ q} := by
    apply hC κ (Localization.AtPrime m) ε (algebraMap B _ t) hmax (RingHom.ker φ) q
    rw [← hq]
    exact LinearEquiv.finrank_eq (Ideal.quotientKerAlgEquivOfSurjective hφs).toLinearEquiv
  have hfac : ∀ x y : B, algebraMap B (Localization.AtPrime m) x = algebraMap B _ y → g x = g y := by
    intro x y h
    rw [← sub_eq_zero, ← map_sub] at h
    obtain ⟨⟨u, hu⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) (x - y)).1 h
    have hu' : ε' (π u) ≠ 0 := fun h0 => hu ((hmem u).2 h0)
    have h1 := congrArg g hu0
    rw [map_mul, map_sub, map_zero] at h1
    exact sub_eq_zero.1 ((hunit u hu').mul_right_eq_zero.1 h1)
  constructor
  · intro hker x hx
    have ht1 : (algebraMap B (Localization.AtPrime m) t) ^ q ∈ RingHom.ker φ := by
      rw [hJ]
      exact Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker, ← map_pow, hφ, map_pow] at ht1
    rw [← map_pow] at ht1
    obtain ⟨⟨u', hu'⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff m'.primeCompl (Localization.AtPrime m') _).1 ht1
    obtain ⟨v, rfl⟩ := hπ u'
    have hv : ε' (π v) ≠ 0 := fun h0 => hu' ((hmem' _).2 h0)
    have h1 : g (v * t ^ q) = 0 := hker _ (by rw [map_mul]; exact hu0)
    rw [map_mul, map_pow] at h1
    have hgt : g t ^ q = 0 := (hunit v hv).mul_right_eq_zero.1 h1
    have hx' : algebraMap B (Localization.AtPrime m) x ∈ Ideal.span {algebraMap B (Localization.AtPrime m) t} := by
      rw [← hmax, ← hmapm]
      exact Ideal.mem_map_of_mem _ ((hmem x).2 hx)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hx'
    obtain ⟨y, rfl⟩ := hsurj z
    have he := hfac x (y * t) (by rw [map_mul, hz])
    rw [he, map_mul, mul_pow, hgt, mul_zero]
  · intro hq' x hx
    have hgt : g t ^ q = 0 := hq' t ((hmem t).1 ht)
    have hx' : algebraMap B (Localization.AtPrime m) x ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, hφ, hx, map_zero]
    rw [hJ] at hx'
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hx'
    obtain ⟨y, rfl⟩ := hsurj z
    have he := hfac x (y * t ^ q) (by rw [map_mul, map_pow, hz])
    rw [he, map_mul, map_pow, hgt, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.frobHom_of :
    FrobHom := by
  intro p f hp κ _ _ φ hφ A A' _ _ ψ hpull h
  obtain ⟨hpb, hmul⟩ := hpull
  have hκ : ((p : ℕ) : Γ(Sp κ, ⊤)) = 0 := by
    have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (CharP.cast_eq_zero κ p)
    rw [map_natCast, map_zero] at e
    exact e
  have hfrκ : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap φ :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ φ hφ
  have hsq : GlobalTheory.SS.FrobField.absFrob A.left p f hp h ≫ A.hom = A.hom ≫ spMap φ := by
    rw [GlobalTheory.SS.FrobField.absFrob_nat A.hom p f hp h hκ, hfrκ]
  let F : A ⟶ A' := Over.homMk (hpb.lift (GlobalTheory.SS.FrobField.absFrob A.left p f hp h) A.hom hsq)
    (hpb.lift_snd _ _ _)
  have hFψ : F.left ≫ ψ = GlobalTheory.SS.FrobField.absFrob A.left p f hp h := hpb.lift_fst _ _ _
  have hTz : ∀ T : Over (Sp κ), ((p : ℕ) : Γ(T.left, ⊤)) = 0 := fun T =>
    GlobalTheory.SS.FrobField.cast_zero_of_hom T.hom hκ
  have key : ∀ (T : Over (Sp κ)) (x : T ⟶ A),
      (x ≫ F).left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ x.left := by
    intro T x
    rw [Over.comp_left, Category.assoc, hFψ]
    exact (GlobalTheory.SS.FrobField.absFrob_nat x.left p f hp (hTz T) h).symm
  let Fr : ∀ T : Over (Sp κ), Over.mk (T.hom ≫ spMap φ) ⟶ T := fun T =>
    Over.homMk (GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T)) (by
      simp only [Over.mk_hom]
      rw [GlobalTheory.SS.FrobField.absFrob_nat T.hom p f hp (hTz T) hκ, hfrκ])
  haveI hF : IsMonHom F := by
    apply isMonHom_of_mul F
    intro T x y
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [← hmul T (x ≫ F) (y ≫ F) (Fr T ≫ x) (Fr T ≫ y) (by rw [key]; rfl) (by rw [key]; rfl),
        ← MonObj.comp_mul, key, Over.comp_left]
      rfl
    · rw [Over.w, Over.w]
  refine ⟨F, hF, hFψ, fun T g => ?_⟩
  have hone : (1 : T ⟶ A').left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ (1 : T ⟶ A).left := by
    rw [← MonObj.one_comp (X := T) F, key]
  constructor
  · intro hg h'
    have e := congrArg (fun k => k.left ≫ ψ) hg
    rw [key, hone] at e
    exact e
  · intro hk
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [key, hone]
      exact hk (hTz T)
    · rw [Over.w, Over.w]
end

