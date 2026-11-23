module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsFixPOrderPowIffLeAndAssocPow
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

section
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private theorem ord_mem {y z : Etau K τ} :
    z ∈ Ord O y ↔ ∃ p q : O, (algebraMap O K p) • (1 : Etau K τ) + (algebraMap O K q) • y = z := by
  simp only [PK.Ord, SetLike.mem_coe, Submodule.mem_span_pair, algebraMap_smul]

private theorem pair_im (a b a' b' : K) (y : Etau K τ) :
    ((a • (1 : Etau K τ) + b • y) * star (a' • (1 : Etau K τ) + b' • y)).im = (b * a' - a * b') * y.im := by
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

private theorem comb_im (a b : K) (y : Etau K τ) : (a • (1 : Etau K τ) + b • y).im = b * y.im := by
  simp [QuadraticAlgebra.im_one]

private theorem comb_re (a b : K) (y : Etau K τ) : (a • (1 : Etau K τ) + b • y).re = a + b * y.re := by
  simp [QuadraticAlgebra.re_one]

private theorem coord {y : Etau K τ} (hy : y.im ≠ 0) (z : Etau K τ) :
    ∃ a b : K, a • (1 : Etau K τ) + b • y = z := by
  refine ⟨z.re - z.im / y.im * y.re, z.im / y.im, ?_⟩
  ext
  · rw [comb_re]
    ring
  · rw [comb_im]
    field_simp

private theorem mul_two_dim_algebra_stable (w y : Etau K τ) (a b c d p q : K) (h1 : w = a • (1 : Etau K τ) + b • y)
    (h2 : w * y = c • (1 : Etau K τ) + d • y) :
    w * (p • (1 : Etau K τ) + q • y) = (p * a + q * c) • (1 : Etau K τ) + (p * b + q * d) • y := by
  rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, h2, h1]
  module
end

theorem UpperTheory.isFixP_order_pow_iff_le_and_assoc_pow :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ (t : K) (m : ℕ), IsFixP O τ t (Ord O (yy π m x)) ↔ m ≤ n ∧ ∃ u : Oˣ, t * algebraMap O K (π ^ m) = algebraMap O K u * algebraMap O K (π ^ n) := by
  intro O K _ _ _ _ _ Δ τ hL hτ π n e h x hc t m
  classical
  have hfr := hL.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hπ0 : π ≠ 0 := hc.irr.ne_zero
  have hπu : ¬ IsUnit π := hc.irr.not_isUnit
  have hA1 : ∀ r : O, algebraMap O (Etau K τ) r = algebraMap O K r • (1 : Etau K τ) := by
    intro r
    rw [algebraMap_etau, Algebra.algebraMap_eq_smul_one]
  have hxim : algebraMap O K (π ^ n) * x.im = 1 := by
    have := congrArg QuadraticAlgebra.im hc.om
    simp [yy, algebraMap_etau, QuadraticAlgebra.omega_im] at this
    rw [map_pow]
    exact this.symm
  have hx0 : x.im ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hxim
    exact zero_ne_one hxim
  have hAπ : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]
    exact hπ0
  have hy0 : (yy π m x).im = algebraMap O K (π ^ m) * x.im := by
    simp [yy]
  have hy0ne : (yy π m x).im ≠ 0 := by
    rw [hy0]
    exact mul_ne_zero (by rw [map_pow]; exact pow_ne_zero _ hAπ) hx0
  set y0 := yy π m x with hy0def
  have uniq : ∀ a b a' b' : K, a • (1 : Etau K τ) + b • y0 = a' • 1 + b' • y0 → a = a' ∧ b = b' := by
    intro a b a' b' hab
    have him := congrArg QuadraticAlgebra.im hab
    have hre := congrArg QuadraticAlgebra.re hab
    rw [comb_im, comb_im] at him
    rw [comb_re, comb_re] at hre
    have hb : b = b' := mul_right_cancel₀ hy0ne him
    subst hb
    exact ⟨add_right_cancel hre, rfl⟩
  have memc : ∀ a b : K, a • (1 : Etau K τ) + b • y0 ∈ PK.Ord O y0 ↔
      a ∈ (algebraMap O K).range ∧ b ∈ (algebraMap O K).range := by
    intro a b
    rw [ord_mem]
    constructor
    · rintro ⟨p, q, hpq⟩
      obtain ⟨h1, h2⟩ := uniq _ _ _ _ hpq
      exact ⟨⟨p, h1⟩, ⟨q, h2⟩⟩
    · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
      exact ⟨p, q, rfl⟩
  set c := t * y0.im with hcdef
  have dualc : ∀ a' b' : K, (∀ s ∈ PK.Ord O y0,
      t * (s * star (a' • (1 : Etau K τ) + b' • y0)).im ∈ (algebraMap O K).range) ↔
      (a' * c ∈ (algebraMap O K).range ∧ b' * c ∈ (algebraMap O K).range) := by
    intro a' b'
    constructor
    · intro H
      have h1 := H _ ((memc 1 0).2 ⟨⟨1, map_one _⟩, ⟨0, map_zero _⟩⟩)
      have h2 := H _ ((memc 0 1).2 ⟨⟨0, map_zero _⟩, ⟨1, map_one _⟩⟩)
      rw [pair_im] at h1 h2
      constructor
      · have e1 : a' * c = t * ((1 * a' - 0 * b') * y0.im) := by
          rw [hcdef]
          ring
        rw [e1]
        exact h2
      · have e2 : b' * c = -(t * ((0 * a' - 1 * b') * y0.im)) := by
          rw [hcdef]
          ring
        rw [e2]
        exact neg_mem h1
    · rintro ⟨ha, hb⟩ s hs
      obtain ⟨p, q, rfl⟩ := ord_mem.1 hs
      rw [pair_im]
      have e : t * ((algebraMap O K q * a' - algebraMap O K p * b') * y0.im) =
          algebraMap O K q * (a' * c) - algebraMap O K p * (b' * c) := by
        rw [hcdef]
        ring
      rw [e]
      exact sub_mem (mul_mem ⟨q, rfl⟩ ha) (mul_mem ⟨p, rfl⟩ hb)
  have dual_iff : (∀ y : Etau K τ, y ∈ PK.Ord O y0 ↔
      ∀ s ∈ PK.Ord O y0, t * (s * star y).im ∈ (algebraMap O K).range) ↔
      ∀ v : K, v ∈ (algebraMap O K).range ↔ v * c ∈ (algebraMap O K).range := by
    constructor
    · intro H v
      have hv := H (v • (1 : Etau K τ) + (0 : K) • y0)
      rw [memc, dualc] at hv
      constructor
      · intro hv'
        exact (hv.1 ⟨hv', zero_mem _⟩).1
      · intro hv'
        exact (hv.2 ⟨hv', by rw [zero_mul]; exact zero_mem _⟩).1
    · intro H y
      obtain ⟨a, b, rfl⟩ := coord hy0ne y
      rw [memc, dualc, H a, H b]
  have unit_iff : (∀ v : K, v ∈ (algebraMap O K).range ↔ v * c ∈ (algebraMap O K).range) ↔
      ∃ u : Oˣ, c = algebraMap O K u := by
    constructor
    · intro H
      obtain ⟨r, hr⟩ := (H 1).1 ⟨1, map_one _⟩
      have hcr : c = algebraMap O K r := by
        rw [hr, one_mul]
      by_cases hr0 : r = 0
      · exfalso
        obtain ⟨s, hs⟩ := (H (algebraMap O K π)⁻¹).2
          (by rw [hcr, hr0, map_zero, mul_zero]; exact zero_mem _)
        apply hπu
        refine isUnit_iff_exists_inv.2 ⟨s, hinj ?_⟩
        rw [map_mul, hs, map_one, mul_inv_cancel₀ hAπ]
      · have hAr : algebraMap O K r ≠ 0 := by
          rw [Ne, map_eq_zero_iff _ hinj]
          exact hr0
        obtain ⟨s, hs⟩ := (H (algebraMap O K r)⁻¹).2
          (by rw [hcr, inv_mul_cancel₀ hAr]; exact one_mem _)
        have hu : IsUnit r :=
          isUnit_iff_exists_inv.2 ⟨s, hinj (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hAr])⟩
        exact ⟨hu.unit, by rw [IsUnit.unit_spec, hcr]⟩
    · rintro ⟨u, hu⟩ v
      constructor
      · intro hv
        rw [hu]
        exact mul_mem hv ⟨u, rfl⟩
      · intro hv
        have e : v = (v * c) * algebraMap O K ↑u⁻¹ := by
          rw [hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
        rw [e]
        exact mul_mem hv ⟨_, rfl⟩
  have c_iff : ∀ u : Oˣ, c = algebraMap O K u ↔
      t * algebraMap O K (π ^ m) = algebraMap O K u * algebraMap O K (π ^ n) := by
    intro u
    constructor
    · intro hu
      calc t * algebraMap O K (π ^ m)
          = t * algebraMap O K (π ^ m) * (algebraMap O K (π ^ n) * x.im) := by rw [hxim, mul_one]
        _ = c * algebraMap O K (π ^ n) := by rw [hcdef, hy0]; ring
        _ = algebraMap O K u * algebraMap O K (π ^ n) := by rw [hu]
    · intro hu
      calc c = t * algebraMap O K (π ^ m) * x.im := by rw [hcdef, hy0]; ring
        _ = algebraMap O K u * (algebraMap O K (π ^ n) * x.im) := by rw [hu]; ring
        _ = algebraMap O K u := by rw [hxim, mul_one]
  have stab_iff : (∀ s ∈ PK.Ord O y0, ω * s ∈ PK.Ord O y0) ↔ m ≤ n := by
    constructor
    · intro H
      have h1mem : (1 : Etau K τ) ∈ PK.Ord O y0 :=
        Submodule.subset_span (Set.mem_insert _ _)
      have hω := H 1 h1mem
      rw [mul_one, ord_mem] at hω
      obtain ⟨p, q, hpq⟩ := hω
      have him := congrArg QuadraticAlgebra.im hpq
      rw [comb_im, QuadraticAlgebra.omega_im, hy0] at him
      have hq : algebraMap O K (q * π ^ m) = algebraMap O K (π ^ n) := by
        apply mul_right_cancel₀ hx0
        rw [map_mul, mul_assoc, him, hxim]
      have hd : π ^ m ∣ π ^ n := ⟨q, by rw [mul_comm]; exact (hinj hq).symm⟩
      exact (pow_dvd_pow_iff hπ0 hπu).1 hd
    · intro hmn s hs
      obtain ⟨p, q, rfl⟩ := ord_mem.1 hs
      have hω : (ω : Etau K τ) = algebraMap O K h • (1 : Etau K τ) + algebraMap O K (π ^ (n - m)) • y0 := by
        rw [hc.om, hy0def, hA1]
        simp only [yy, smul_smul, ← map_mul, ← pow_add, Nat.sub_add_cancel hmn]
      have hωy : (ω : Etau K τ) * y0 =
          algebraMap O K (π ^ m * π ^ n * e) • (1 : Etau K τ) + algebraMap O K h • y0 := by
        rw [hy0def, hc.om]
        simp only [yy, hA1, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, hc.sq, smul_smul, map_mul]
        module
      rw [mul_two_dim_algebra_stable ω y0 _ _ _ _ _ _ hω hωy, ord_mem]
      exact ⟨p * h + q * (π ^ m * π ^ n * e), p * π ^ (n - m) + q * h, by simp only [map_add (f := _), map_mul]⟩
  constructor
  · intro hF
    obtain ⟨u, hu⟩ := unit_iff.1 (dual_iff.1 hF.dual)
    exact ⟨stab_iff.1 hF.stab, u, (c_iff u).1 hu⟩
  · rintro ⟨hmn, u, hu⟩
    exact ⟨⟨{1, y0}, by simp [PK.Ord]⟩, dual_iff.2 (unit_iff.2 ⟨u, (c_iff u).2 hu⟩), stab_iff.2 hmn⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSquareSqSubFourIffIsSquareUnit
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.isSquare_sq_sub_four_iff_isSquare_unit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (IsSquare (τ ^ 2 - 4) ↔ IsSquare (e : O)) := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc
  haveI := L.frac
  have E : (ω - algebraMap O (Etau K τ) h) * (ω - algebraMap O (Etau K τ) h) = algebraMap O (Etau K τ) (π ^ n * π ^ n * e) := by
    rw [hc.om, add_sub_cancel_left]
    simp only [yy, smul_mul_smul_comm, hc.sq]
    simp only [algebraMap_etau (O := O), Algebra.smul_def, map_mul]
  have Er := congrArg QuadraticAlgebra.re E
  have Ei := congrArg QuadraticAlgebra.im E
  simp [algebraMap_etau] at Er Ei
  have hτ : τ = 2 * algebraMap O K h := by linear_combination Ei
  have key : τ ^ 2 - 4 = (2 * algebraMap O K π ^ n) ^ 2 * algebraMap O K (e : O) := by
    rw [hτ]
    linear_combination 4 * Er
  constructor
  · rintro ⟨r, hr⟩
    have hq : 2 * algebraMap O K π ^ n ≠ 0 := by
      intro h0
      apply hD
      rw [key, h0]
      ring
    have hsq : (r / (2 * algebraMap O K π ^ n)) ^ 2 = algebraMap O K (e : O) := by
      rw [div_pow, sq r, ← hr, key]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hq)
    obtain ⟨b, hb⟩ := sq_int L _ _ hsq
    refine ⟨b, IsFractionRing.injective O K ?_⟩
    rw [map_mul, hb, ← hsq]
    ring
  · rintro ⟨b, hb⟩
    refine ⟨2 * algebraMap O K π ^ n * algebraMap O K b, ?_⟩
    rw [key, hb, map_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NcardUnitTranslatesOrderEqRelIndex
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.ncard_unit_translates_order_eq_relIndex :
    ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (τ : K) (a : (Etau K τ)ˣ) (y : Etau K τ), {S : Set (Etau K τ) | ∃ u ∈ Gu O τ, S = PS.ml (a * u) (Ord O y)}.ncard = (Hu O y).relIndex (Gu O τ) := by
  intro O K _ _ _ τ a y
  set G := Gu O τ
  set H := (Hu O y).subgroupOf G
  have key : ∀ g₁ g₂ : G, PS.ml (a * (g₁ : (Etau K τ)ˣ)) (PK.Ord O y) =
      PS.ml (a * (g₂ : (Etau K τ)ˣ)) (PK.Ord O y) ↔ g₁⁻¹ * g₂ ∈ H := by
    intro g₁ g₂
    rw [Subgroup.mem_subgroupOf]
    show _ ↔ PS.ml (((g₁⁻¹ * g₂ : G)) : (Etau K τ)ˣ) (PK.Ord O y) = PK.Ord O y
    rw [PS.ml_mul, PS.ml_mul, (PS.ml_inj a).eq_iff, Subgroup.coe_mul, Subgroup.coe_inv, PS.ml_mul]
    constructor
    · intro h
      rw [← h, ← PS.ml_mul, inv_mul_cancel, PS.ml_one]
    · intro h
      conv_lhs => rw [← h]
      rw [← PS.ml_mul, mul_inv_cancel, PS.ml_one]
  let f : G ⧸ H → Set (Etau K τ) :=
    Quotient.lift (fun g : G => PS.ml (a * (g : (Etau K τ)ˣ)) (PK.Ord O y))
      (fun g₁ g₂ hg => (key g₁ g₂).2 (QuotientGroup.leftRel_apply.1 hg))
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.2 ((key _ _).1 hq)
  have hrange : {S : Set (Etau K τ) | ∃ u ∈ G, S = PS.ml (a * u) (PK.Ord O y)} = Set.range f := by
    ext S
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨((⟨u, hu⟩ : G) : G ⧸ H), rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g, g.2, rfl⟩
  rw [hrange, Set.ncard_range_of_injective hf]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RelIndexStabilizerSuccEqCardResidueField
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

namespace UpperTheory.HilbertUnitGroup

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {τ : K}

private theorem mem_ord {y w : Etau K τ} :
    w ∈ Ord O y ↔ ∃ a b : O, w = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y := by
  change w ∈ Submodule.span O {1, y} ↔ _
  rw [Submodule.mem_span_pair]
  simp only [Algebra.smul_def, mul_one, eq_comm]

private theorem ord_mul {y v w : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    (hv : v ∈ Ord O y) (hw : w ∈ Ord O y) : v * w ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hv
  obtain ⟨a', b', rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
  simp only [map_add (f := _), map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy

private theorem mem_Hu {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c) {u : (Etau K τ)ˣ} :
    u ∈ Hu O y ↔ (u : Etau K τ) ∈ Ord O y ∧ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
  have one : (1 : Etau K τ) ∈ Ord O y := mem_ord.2 ⟨1, 0, by simp⟩
  have key : ∀ v : (Etau K τ)ˣ, v ∈ Hu O y → ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := fun v hv => by
    have h1 : (1 : Etau K τ) ∈ PS.ml v (Ord O y) := by
      rw [show PS.ml v (Ord O y) = Ord O y from hv]; exact one
    simpa using PS.mem_ml.1 h1
  refine ⟨fun h => ⟨by simpa using key _ (inv_mem h), key _ h⟩, fun ⟨h1, h2⟩ => ?_⟩
  change PS.ml u (Ord O y) = Ord O y
  ext w
  rw [PS.mem_ml]
  refine ⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩
  simpa using ord_mul hy h1 hw

private theorem uniq (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {a b a' b' : O}
    (h : algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y =
      algebraMap O (Etau K τ) a' + algebraMap O (Etau K τ) b' * y) : a = a' ∧ b = b' := by
  rw [algebraMap_etau a, algebraMap_etau b, algebraMap_etau a', algebraMap_etau b'] at h
  have im_algebraMap_add_mul : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).im = q * y.im := by
    intro p q; simp
  have kre : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).re = p + q * y.re := by
    intro p q; simp
  have him := congrArg QuadraticAlgebra.im h
  have hre := congrArg QuadraticAlgebra.re h
  rw [im_algebraMap_add_mul, im_algebraMap_add_mul] at him
  rw [kre, kre] at hre
  have hb := mul_right_cancel₀ h0 him
  rw [hb] at hre
  exact ⟨hinj (add_right_cancel hre), hinj hb⟩

private theorem isUnit_fst (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c : O}
    (hy : y * y = algebraMap O (Etau K τ) c) (hc : ¬ IsUnit c) {u : (Etau K τ)ˣ} (hu : u ∈ Hu O y) {a b : O}
    (e : (u : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y) : IsUnit a := by
  obtain ⟨a', b', e'⟩ := mem_ord.1 ((mem_Hu hy).1 hu).2
  have h1 : algebraMap O (Etau K τ) (a * a' + b * b' * c) + algebraMap O (Etau K τ) (a * b' + a' * b) * y =
      algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) 0 * y := by
    have := u.mul_inv
    rw [e, e'] at this
    simp only [map_add (f := _), map_mul, map_one, map_zero]
    linear_combination this - (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy
  have h2 := (uniq hinj h0 h1).1
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h2 with h3 | h3
  · exact isUnit_of_mul_isUnit_left h3
  · exact absurd (isUnit_of_mul_isUnit_right h3) hc

private theorem step (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c π : O}
    (hπ : Irreducible π) (hy : y * y = algebraMap O (Etau K τ) c) (hc : π ∣ c) :
    (Hu O (algebraMap O (Etau K τ) π * y)).relIndex (Hu O y) = Nat.card (IsLocalRing.ResidueField O) := by
  classical
  have hcu : ¬ IsUnit c := fun h => hπ.not_isUnit (isUnit_of_dvd_unit hc h)
  have hy' : (algebraMap O (Etau K τ) π * y) * (algebraMap O (Etau K τ) π * y) =
      algebraMap O (Etau K τ) (π * π * c) := by
    simp only [map_mul]; linear_combination (algebraMap O (Etau K τ) π * algebraMap O (Etau K τ) π) * hy
  have hπ0 : IsLocalRing.residue O π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]; exact hπ.not_isUnit
  have hc0 : IsLocalRing.residue O c = 0 := by
    obtain ⟨d, rfl⟩ := hc; rw [map_mul, hπ0, zero_mul]
  have ex : ∀ u : Hu O y, ∃ p : O × O, ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) p.1 + algebraMap O (Etau K τ) p.2 * y := fun u => by
    obtain ⟨a, b, e⟩ := mem_ord.1 ((mem_Hu hy).1 u.2).1
    exact ⟨(a, b), e⟩
  choose P hP using ex
  let g : Hu O y → IsLocalRing.ResidueField O := fun u =>
    IsLocalRing.residue O (P u).2 / IsLocalRing.residue O (P u).1
  have gval : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y →
      g u = IsLocalRing.residue O b / IsLocalRing.residue O a := fun u a b e => by
    obtain ⟨h1, h2⟩ := uniq hinj h0 ((hP u).symm.trans e)
    simp only [g, h1, h2]
  have resne : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y → IsLocalRing.residue O a ≠ 0 := fun u a b e =>
    ((isUnit_fst hinj h0 hy hcu u.2 e).map (IsLocalRing.residue O)).ne_zero
  have gmul : ∀ u v : Hu O y, g (u * v) = g u + g v := fun u v => by
    have eu := hP u
    have ev := hP v
    have e : (((u * v : Hu O y) : (Etau K τ)ˣ) : Etau K τ) =
        algebraMap O (Etau K τ) ((P u).1 * (P v).1 + (P u).2 * (P v).2 * c) +
          algebraMap O (Etau K τ) ((P u).1 * (P v).2 + (P v).1 * (P u).2) * y := by
      rw [Subgroup.coe_mul, Units.val_mul, eu, ev]
      simp only [map_add (f := _), map_mul]
      linear_combination (algebraMap O (Etau K τ) (P u).2 * algebraMap O (Etau K τ) (P v).2) * hy
    have n1 := resne u _ _ eu
    have n2 := resne v _ _ ev
    rw [gval _ _ _ e, gval _ _ _ eu, gval _ _ _ ev]
    simp only [map_add (f := _), map_mul, hc0, mul_zero, add_zero]
    field_simp
    ring
  let f : Hu O y →* Multiplicative (IsLocalRing.ResidueField O) :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd (g u)) (fun u v => by rw [gmul, ofAdd_add])
  have fval : ∀ u, f u = Multiplicative.ofAdd (g u) := fun _ => rfl
  have down : ∀ u : Hu O y, f u = 1 → ((u : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O (algebraMap O (Etau K τ) π * y) := fun u hu => by
    have h1 : g u = 0 := by simpa [fval] using hu
    have e := hP u
    rw [gval _ _ _ e, div_eq_zero_iff, or_iff_left (resne u _ _ e), IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at h1
    obtain ⟨d, hd⟩ := h1
    refine mem_ord.2 ⟨(P u).1, d, ?_⟩
    rw [e, hd, map_mul]
    ring
  have hker : f.ker = (Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Hu hy']
    refine ⟨fun hu => ⟨down u hu, ?_⟩, fun ⟨h1, _⟩ => ?_⟩
    · have := down u⁻¹ (by rw [map_inv, hu, inv_one])
      simpa using this
    · obtain ⟨a, b, e⟩ := mem_ord.1 h1
      have e' : ((u : (Etau K τ)ˣ) : Etau K τ) =
          algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) (b * π) * y := by
        rw [e, map_mul]; ring
      rw [fval, gval _ _ _ e', map_mul, hπ0, mul_zero, zero_div, ofAdd_zero]
  have hsurj : Function.Surjective f := fun r => by
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (Multiplicative.toAdd r)
    have hn : IsUnit (1 - s * s * c) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := 1 - s * s * c) (b := s * s * c) (by ring) with h | h
      · exact h
      · exact absurd (isUnit_of_mul_isUnit_right h) hcu
    obtain ⟨ν, hν⟩ := hn
    have hν' : algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * (1 - algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) c) = 1 := by
      rw [← map_mul, ← map_mul, ← map_one (algebraMap O (Etau K τ)), ← map_sub, ← hν, ← map_mul, Units.inv_mul]
    let w : (Etau K τ)ˣ :=
      { val := algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) s * y
        inv := algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) + algebraMap O (Etau K τ) (-(((ν⁻¹ : Oˣ) : O) * s)) * y
        val_inv := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy
        inv_val := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy }
    have hw : w ∈ Hu O y := (mem_Hu hy).2 ⟨mem_ord.2 ⟨1, s, rfl⟩, mem_ord.2 ⟨_, _, rfl⟩⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [fval, gval ⟨w, hw⟩ 1 s rfl, map_one, div_one, hs, ofAdd_toAdd]
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  change ((Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y)).index = _
  rw [← hker, Subgroup.index_ker, hr, Subgroup.card_top]
  exact Nat.card_congr Multiplicative.toAdd

end UpperTheory.HilbertUnitGroup

theorem UpperTheory.relIndex_stabilizer_succ_eq_card_residueField :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ m : ℕ, 1 ≤ m → (Hu O (yy π (m + 1) x)).relIndex (Hu O (yy π m x)) = Nat.card (IsLocalRing.ResidueField O) := by
  intro O K _ _ _ _ _ Δ τ L _ π n e h x hC m hm
  haveI := L.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hπ := hC.irr
  have hp : algebraMap O K (π ^ m) ≠ 0 := fun h0 =>
    pow_ne_zero m hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have h0 : (yy π m x).im ≠ 0 := by
    rw [yy, im_smul, smul_eq_mul]
    exact mul_ne_zero hp hC.gen.im_ne
  have hsm : ∀ k : ℕ, yy π k x = algebraMap O (Etau K τ) (π ^ k) * x := fun k => by
    rw [yy, Algebra.smul_def, ← algebraMap_etau]
  have hy : yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * (e : O)) := by
    rw [hsm, map_mul, map_mul, ← hC.sq]; ring
  have hc : π ∣ π ^ m * π ^ m * (e : O) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _) _
  have e1 : yy π (m + 1) x = algebraMap O (Etau K τ) π * yy π m x := by
    rw [hsm, hsm, pow_succ, map_mul]; ring
  rw [e1]
  exact UpperTheory.HilbertUnitGroup.step hinj h0 hπ hy hc
end

