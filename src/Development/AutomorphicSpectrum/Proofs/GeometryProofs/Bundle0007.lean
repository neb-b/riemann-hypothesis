module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMax
section
namespace GlobalTheory.CompanionTheory.Domination

theorem isUnit_subring_iff {K : Type} [Field K] (D : Subring K) (d : D) :
    IsUnit d ↔ (d : K) ≠ 0 ∧ (d : K)⁻¹ ∈ D := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : ((u : D) : K) * (((u⁻¹ : Dˣ) : D) : K) = 1 := by
      exact_mod_cast congrArg Subtype.val u.mul_inv
    refine ⟨left_ne_zero_of_mul_eq_one h, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h]
    exact ((u⁻¹ : Dˣ) : D).2
  · rintro ⟨h0, h⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h⟩, Subtype.ext (by simp [h0])⟩

theorem isMaximal_of_comap {K : Type} [Field K] (R T : Subring K) (hRT : R ≤ T)
    (hint : ∀ t ∈ T, IsIntegral R t) (P : Ideal T) [P.IsPrime]
    (hc : (P.comap (Subring.inclusion hRT)).IsMaximal) : P.IsMaximal := by
  let _ : Algebra R T := (Subring.inclusion hRT).toAlgebra
  have : Algebra.IsIntegral R T := ⟨fun t ↦ by
    let f : T →ₐ[R] K := { T.subtype with commutes' := fun r ↦ rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).1 (hint t t.2)⟩
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under P hc

theorem eq_ofPrime {K : Type} [Field K] (T D : Subring K) (P : Ideal T) [P.IsPrime]
    (hP : ∀ t : T, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D)) (hTD : T ≤ D)
    (gen : ∀ a ∈ D, ∃ u ∈ T, ∃ v ∈ T, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) :
    D = (LocalSubring.ofPrime T P).toSubring := by
  ext a
  simp only [LocalSubring.ofPrime, LocalSubring.range_toSubring]
  show a ∈ D ↔ a ∈ Set.range _
  rw [Set.mem_range]
  constructor
  · intro ha
    obtain ⟨u, hu, v, hv, h0, hvD, rfl⟩ := gen a ha
    have hvP : (⟨v, hv⟩ : T) ∈ P.primeCompl := by
      show (⟨v, hv⟩ : T) ∉ P
      rw [hP]
      exact not_not.2 ⟨h0, hvD⟩
    refine ⟨IsLocalization.mk' _ (⟨u, hu⟩ : T) (⟨⟨v, hv⟩, hvP⟩ : P.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    show u = v * (u / v)
    field_simp
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨u, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    have hs : ¬ ((s : T) ∈ P) := s.2
    rw [hP, not_not] at hs
    have key : ∀ z : K, ((u : T) : K) = ((s : T) : K) * z → z ∈ D := by
      intro z hz
      have hz' : z = (u : K) * ((s : T) : K)⁻¹ := by
        rw [hz]
        field_simp [hs.1]
      rw [hz']
      exact D.mul_mem (hTD u.2) hs.2
    dsimp only
    apply key
    exact (IsLocalization.lift_mk'_spec (S := Localization.AtPrime P) (g := T.subtype) _ _ _ _).1 rfl

theorem eq_localisation_integralClosure :
    ∀ {K : Type} [Field K] (R D B : Subring K) [IsLocalRing R] [IsLocalRing D], R ≤ D →
      (∀ r ∈ R, r ≠ 0 → r⁻¹ ∈ D → r⁻¹ ∈ R) → (integralClosure R K).toSubring ≤ D →
      B ≤ (integralClosure R K).toSubring →
      (∀ a ∈ D, ∃ u ∈ B, ∃ v ∈ B, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) →
      ∃ (P : Ideal (integralClosure R K).toSubring) (_ : P.IsMaximal),
        D = (LocalSubring.ofPrime _ P).toSubring ∧
        ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
  intro K _ R D B _ _ hRD hdom hTD hBT gen
  let P : Ideal (integralClosure R K).toSubring :=
    (IsLocalRing.maximalIdeal D).comap (Subring.inclusion hTD)
  have hP : ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
    intro t
    show Subring.inclusion hTD t ∈ IsLocalRing.maximalIdeal D ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_subring_iff]
    rfl
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hRT : R ≤ (integralClosure R K).toSubring := fun r hr ↦ by
    show IsIntegral R (algebraMap R K ⟨r, hr⟩)
    exact isIntegral_algebraMap
  have hint : ∀ t ∈ (integralClosure R K).toSubring, IsIntegral R t := fun t ht ↦ ht
  have hPmax : P.IsMaximal := by
    apply isMaximal_of_comap R _ hRT hint P
    have hc : P.comap (Subring.inclusion hRT) = IsLocalRing.maximalIdeal R := by
      ext r
      rw [Ideal.mem_comap, hP, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_subring_iff]
      show ¬ ((r : K) ≠ 0 ∧ (r : K)⁻¹ ∈ D) ↔ ¬ ((r : K) ≠ 0 ∧ (r : K)⁻¹ ∈ R)
      exact not_congr ⟨fun ⟨h0, h⟩ ↦ ⟨h0, hdom _ r.2 h0 h⟩, fun ⟨h0, h⟩ ↦ ⟨h0, hRD h⟩⟩
    rw [hc]
    exact IsLocalRing.maximalIdeal.isMaximal R
  refine ⟨P, hPmax, ?_, hP⟩
  refine eq_ofPrime _ D P hP hTD fun a ha ↦ ?_
  obtain ⟨u, hu, v, hv, h0, hvD, rfl⟩ := gen a ha
  exact ⟨u, hBT hu, v, hBT hv, h0, hvD, rfl⟩

end GlobalTheory.CompanionTheory.Domination
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationSheafGlueModules
section
namespace GlobalTheory.CompanionTheory.BasicCover

theorem exists_uniform_bound {J : Type} [Finite J] (P : J → ℕ → Prop)
    (mono : ∀ j n m, n ≤ m → P j n → P j m) (h : ∀ j, ∃ n, P j n) : ∃ N, ∀ j, P j N := by
  classical
  cases nonempty_fintype J
  choose n hn using h
  exact ⟨∑ j, n j, fun j => mono j _ _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) (hn j)⟩

theorem pow_smul_eq_zero_mono {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (t : R) (y : M) {n m : ℕ} (hnm : n ≤ m) (h : t ^ n • y = 0) : t ^ m • y = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm, mul_smul, h, smul_zero]

theorem exists_pow_smul_eq_zero {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (t : R) (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers t) φ] (y : M) (h : φ y = 0) :
    ∃ n : ℕ, t ^ n • y = 0 := by
  obtain ⟨⟨c, hc⟩, hc'⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers t) (f := φ)
    (x₁ := y) (x₂ := 0) (by rw [h, map_zero])
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
  exact ⟨n, by simpa [Submonoid.smul_def] using hc'⟩

theorem exists_pow_smul_eq_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (t : R) (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers t) φ] (z : M') :
    ∃ (n : ℕ) (y : M), t ^ n • z = φ y := by
  obtain ⟨⟨y, ⟨c, hc⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers t) φ z
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
  exact ⟨n, y, by simpa [Submonoid.smul_def] using hy⟩

theorem isLocalizedModule_of_basic_cover : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : {g : R // ∃ i, f i ∣ g} → Type) [∀ g, AddCommGroup (F g)] [∀ g, Module R (F g)]
    (res : ∀ g g' : {g : R // ∃ i, f i ∣ g}, g.1 ∣ g'.1 → (F g →ₗ[R] F g'))
    (ρ : ∀ g, E →ₗ[R] F g),
    (∀ g (h : g.1 ∣ g.1) y, res g g h y = y) →
    (∀ g g' g'' (h : g.1 ∣ g'.1) (h' : g'.1 ∣ g''.1) (h'' : g.1 ∣ g''.1) y, res g' g'' h' (res g g' h y) = res g g'' h'' y) →
    (∀ g g' (h : g.1 ∣ g'.1) e, res g g' h (ρ g e) = ρ g' e) →
    (∀ g (a : R), a ∣ g.1 → IsUnit (algebraMap R (Module.End R (F g)) a)) →
    (∀ g g' (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → IsLocalizedModule (Submonoid.powers t) (res g g' h)) →
    (∀ e, (∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = 0) → e = 0) →
    (∀ w : ∀ i, F ⟨f i, i, dvd_rfl⟩,
      (∀ i j, res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (w i) =
        res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (w j)) →
      ∃ e, ∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = w i) →
    ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (ρ ⟨f i, i, dvd_rfl⟩) := by
  intro R E _ _ _ J _ f _ F _ _ res ρ _ hcomp hrρ hunit hloc hsep hglue i
  have inj : ∀ (g g' : {g : R // ∃ i, f i ∣ g}) (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → t ∣ g.1 →
      ∀ x, res g g' h x = 0 → x = 0 := by
    intro g g' h t ht htd x hx
    have := hloc g g' h t ht
    obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero t (res g g' h) x hx
    have hu : IsUnit (algebraMap R (Module.End R (F g)) (t ^ n)) := by
      rw [map_pow]
      exact (hunit g t htd).pow n
    apply ((Module.End.isUnit_iff _).1 hu).1
    rw [Module.algebraMap_end_apply, hn, map_zero]
  refine ⟨fun x => ?_, fun z => ?_, fun {x₁ x₂} hx => ?_⟩
  · obtain ⟨c, hc⟩ := x
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
    show IsUnit (algebraMap R (Module.End R (F ⟨f i, i, dvd_rfl⟩)) (f i ^ n))
    rw [map_pow]
    exact (hunit _ (f i) dvd_rfl).pow n
  · have Pex : ∀ j, ∃ n, (fun j n => ∃ y : F ⟨f j, j, dvd_rfl⟩, f i ^ n • res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) z = res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) y) j n := by
      intro j
      have := hloc ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (f i) (mul_comm _ _)
      exact GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_map (f i) _ _
    obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound (fun j n => ∃ y : F ⟨f j, j, dvd_rfl⟩, f i ^ n • res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) z = res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) y)
      (fun j n m hnm hex => by
        obtain ⟨y, hy⟩ := hex
        exact ⟨f i ^ (m - n) • y, by
          rw [map_smul, ← hy, smul_smul, ← pow_add, Nat.sub_add_cancel hnm]⟩) Pex
    choose y hy using hN
    have lift : ∀ j (g'' : {g : R // ∃ i, f i ∣ g}) (h1 : f j ∣ g''.1) (h2 : f i * f j ∣ g''.1)
        (h3 : f i ∣ g''.1), res ⟨f j, j, dvd_rfl⟩ g'' h1 (y j) = f i ^ N • res ⟨f i, i, dvd_rfl⟩ g'' h3 z := by
      intro j g'' h1 h2 h3
      rw [← hcomp ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ g'' (dvd_mul_left _ _) h2 h1 (y j), ← hy j, map_smul,
        hcomp ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ g'' (dvd_mul_right _ _) h2 h3 z]
    have Qex : ∀ p : J × J, ∃ m, f i ^ m • (res ⟨f p.1, p.1, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (y p.1) - res ⟨f p.2, p.2, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (y p.2)) = 0 := by
      rintro ⟨j, k⟩
      dsimp only
      have := hloc ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _) (f i) rfl
      apply GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero (f i) (res ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _))
      rw [map_sub, hcomp ⟨f j, j, dvd_rfl⟩ ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _) (dvd_mul_right _ _)
          (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (y j),
        hcomp ⟨f k, k, dvd_rfl⟩ ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_left _ _) (dvd_mul_right _ _)
          (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (y k),
        lift j ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
          (Dvd.intro (f k) (show f i * f j * f k = f j * f k * f i by ring))
          (Dvd.intro (f j * f k) (show f i * (f j * f k) = f j * f k * f i by ring)),
        lift k ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
          (Dvd.intro (f j) (show f i * f k * f j = f j * f k * f i by ring))
          (Dvd.intro (f j * f k) (show f i * (f j * f k) = f j * f k * f i by ring)), sub_self]
    obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound
      (fun (p : J × J) m => f i ^ m • (res ⟨f p.1, p.1, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (y p.1) - res ⟨f p.2, p.2, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (y p.2)) = 0)
      (fun p n m hnm hn => GlobalTheory.CompanionTheory.BasicCover.pow_smul_eq_zero_mono _ _ hnm hn) Qex
    have hii : f i ^ N • z = y i := by
      apply sub_eq_zero.1
      apply inj ⟨f i, i, dvd_rfl⟩ ⟨f i * f i, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (f i) rfl dvd_rfl
      rw [map_sub, map_smul, hy i, sub_self]
    obtain ⟨e, he⟩ := hglue (fun j => f i ^ M • y j) fun j k => by
      have h4 := hM (j, k)
      dsimp only at h4 ⊢
      rw [smul_sub, sub_eq_zero] at h4
      rw [map_smul, map_smul]
      exact h4
    refine ⟨(e, ⟨f i ^ (M + N), pow_mem (Submonoid.mem_powers _) _⟩), ?_⟩
    show f i ^ (M + N) • z = ρ ⟨f i, i, dvd_rfl⟩ e
    rw [he i]
    rw [← hii, smul_smul, ← pow_add]
  · have hd : ρ ⟨f i, i, dvd_rfl⟩ (x₁ - x₂) = 0 := by rw [map_sub, hx, sub_self]
    have Rj : ∀ j, ∃ n, f i ^ n • ρ ⟨f j, j, dvd_rfl⟩ (x₁ - x₂) = 0 := by
      intro j
      have := hloc ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (f i) (mul_comm _ _)
      apply GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero (f i)
        (res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _))
      rw [hrρ, ← hrρ ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _), hd, map_zero]
    obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound
      (fun j n => f i ^ n • ρ ⟨f j, j, dvd_rfl⟩ (x₁ - x₂) = 0)
      (fun j n m hnm hn => GlobalTheory.CompanionTheory.BasicCover.pow_smul_eq_zero_mono _ _ hnm hn) Rj
    have h0 : f i ^ N • (x₁ - x₂) = 0 := hsep _ fun j => by rw [map_smul]; exact hN j
    refine ⟨⟨f i ^ N, pow_mem (Submonoid.mem_powers _) N⟩, ?_⟩
    show f i ^ N • x₁ = f i ^ N • x₂
    rw [← sub_eq_zero, ← smul_sub]
    exact h0

end GlobalTheory.CompanionTheory.BasicCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizedModuleBaseChange
section
namespace GlobalTheory.CompanionTheory.LocHom

variable {R : Type*} [CommRing R]

theorem isLocalizedModule_of_retract {M M' N N' : Type*} [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [AddCommGroup N'] [Module R M] [Module R M'] [Module R N] [Module R N']
    (S : Submonoid R) (g : M →ₗ[R] M') (h : N →ₗ[R] N') [IsLocalizedModule S h]
    (i : M →ₗ[R] N) (j : N →ₗ[R] M) (i' : M' →ₗ[R] N') (j' : N' →ₗ[R] M')
    (hji : ∀ x, j (i x) = x) (hji' : ∀ x, j' (i' x) = x)
    (hi : ∀ x, h (i x) = i' (g x)) (hj : ∀ y, g (j y) = j' (h y)) :
    IsLocalizedModule S g := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [Module.End.isUnit_iff]
    have hu := IsLocalizedModule.map_units h s
    rw [Module.End.isUnit_iff] at hu
    constructor
    · intro x y hxy
      apply (show Function.Injective i' from fun a b e => by rw [← hji' a, ← hji' b, e])
      apply hu.1
      simp only [Module.algebraMap_end_apply] at hxy ⊢
      rw [← map_smul, ← map_smul, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hu.2 (i' y)
      refine ⟨j' z, ?_⟩
      simp only [Module.algebraMap_end_apply] at hz ⊢
      rw [← map_smul, hz, hji']
  · intro y
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj S h (i' y)
    refine ⟨⟨j x, s⟩, ?_⟩
    simp only at hx ⊢
    rw [hj, ← hx, Submonoid.smul_def, Submonoid.smul_def, map_smul, hji']
  · intro x₁ x₂ e
    have h0 : h (i x₁) = h (i x₂) := by rw [hi, hi, e]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) h0
    refine ⟨c, ?_⟩
    have h1 := congrArg j hc
    simpa only [Submonoid.smul_def, map_smul, hji] using h1

theorem map_away_smul {f : R} {P D : Type*} [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
    [CommRing D] [Algebra R D] (ρ : Localization.Away f →ₐ[R] D) (φ : P →ₗ[R] D)
    (a : Localization.Away f) (p : P) : φ (a • p) = ρ a * φ p := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers f) a
  simp only at hrs
  have hs : IsUnit (algebraMap R D s) := by
    have := (IsLocalization.map_units (Localization.Away f) s).map ρ
    rwa [AlgHom.commutes] at this
  have h1 : (s : R) • (a • p) = r • p := by
    rw [← algebraMap_smul (Localization.Away f) (s : R), ← algebraMap_smul (Localization.Away f) r,
      ← hrs, smul_smul, mul_comm]
  have h2 : (s : R) • φ (a • p) = r • φ p := by rw [← map_smul, h1, map_smul]
  rw [Algebra.smul_def, Algebra.smul_def] at h2
  have h3 := congrArg ρ hrs
  rw [map_mul, AlgHom.commutes, AlgHom.commutes] at h3
  apply hs.mul_right_injective
  show algebraMap R D s * _ = algebraMap R D s * _
  linear_combination h2 - φ p * h3

section retraction

variable {A P D : Type*} [CommRing A] [Algebra R A] [AddCommGroup P] [Module R P]
  [CommRing D] [Algebra R D] {n : ℕ}

noncomputable def coord (s : P →ₗ[R] (Fin n → A)) (ρ : A →ₐ[R] D) (k : Fin n) : P →ₗ[R] D :=
  ρ.toLinearMap ∘ₗ LinearMap.proj k ∘ₗ s

noncomputable def assemble (s : P →ₗ[R] (Fin n → A)) (ρ : A →ₐ[R] D) :
    (Fin n → D) →ₗ[R] (P →ₗ[R] D) where
  toFun v := ∑ k, v k • coord s ρ k
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.smul_sum, smul_assoc]

def evalAt (D : Type*) [CommRing D] [Algebra R D] (b : Fin n → P) :
    (P →ₗ[R] D) →ₗ[R] (Fin n → D) where
  toFun φ k := φ (b k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end retraction

theorem isLocalizedModule_compRight_away :
    ∀ (R P C C' : Type) [CommRing R] [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (f t : R) [AddCommGroup P] [Module R P]
      [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
      [Module.Finite (Localization.Away f) P]
      [Module.Projective (Localization.Away f) P], IsUnit (algebraMap R C f) →
      ∀ c : C →ₐ[R] C',
      IsLocalizedModule (Submonoid.powers t) c.toLinearMap →
      IsLocalizedModule (Submonoid.powers t)
        (LinearMap.compRight R c.toLinearMap : (P →ₗ[R] C) →ₗ[R] (P →ₗ[R] C')) := by
  intro R P C C' _ _ _ _ _ f t _ _ _ _ _ _ hf c hc
  have hunit : ∀ y : Submonoid.powers f, IsUnit ((Algebra.ofId R C) (y : R)) := by
    rintro ⟨_, k, rfl⟩
    simpa [Algebra.ofId_apply] using hf.pow k
  let ρ : Localization.Away f →ₐ[R] C := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  let ρ' : Localization.Away f →ₐ[R] C' := c.comp ρ
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (Localization.Away f) P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let s₀ : P →ₗ[R] (Fin n → Localization.Away f) := s.restrictScalars R
  let b : Fin n → P := fun k => π (fun j => if k = j then 1 else 0)
  have hexp : ∀ p : P, ∑ k, s p k • b k = p := by
    intro p
    have h1 := LinearMap.congr_fun hs p
    have h2 := LinearMap.pi_apply_eq_sum_univ π (s p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [h1] at h2
    exact h2.symm
  have hret : ∀ {D : Type} [CommRing D] [Algebra R D] (σ : Localization.Away f →ₐ[R] D)
      (φ : P →ₗ[R] D), assemble s₀ σ (evalAt D b φ) = φ := by
    intro D _ _ σ φ
    ext p
    conv_rhs => rw [← hexp p]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [assemble, evalAt, coord, s₀, map_sum, map_away_smul σ, mul_comm]
  haveI : IsLocalizedModule (Submonoid.powers t)
      (LinearMap.pi fun k : Fin n => c.toLinearMap ∘ₗ LinearMap.proj k) :=
    IsLocalizedModule.pi (Submonoid.powers t) (fun _ : Fin n => c.toLinearMap)
  refine isLocalizedModule_of_retract (Submonoid.powers t) _
    (LinearMap.pi fun k : Fin n => c.toLinearMap ∘ₗ LinearMap.proj k)
    (evalAt C b) (assemble s₀ ρ) (evalAt C' b) (assemble s₀ ρ')
    (hret ρ) (hret ρ') ?_ ?_
  · intro φ
    rfl
  · intro v
    ext p
    set_option synthInstance.maxHeartbeats 100000 in
      simp [assemble, coord, ρ', map_sum]

end GlobalTheory.CompanionTheory.LocHom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MatrixEqOfLinearIndependent
section
namespace GlobalTheory.CompanionTheory.Ggeo.FrameDet

open scoped BigOperators

private theorem det_mem_of_forall_mem' {Ω : Type} [CommRing Ω] (R : Subring Ω) {n : ℕ}
    (P : Matrix (Fin n) (Fin n) Ω) (hP : ∀ i j, P i j ∈ R) : P.det ∈ R := by
  have h : P = R.subtype.mapMatrix (Matrix.of fun i j => (⟨P i j, hP i j⟩ : R)) := by
    ext i j
    rfl
  rw [h, ← RingHom.map_det]
  exact (Matrix.det (Matrix.of fun i j => (⟨P i j, hP i j⟩ : R))).2

theorem matrix_eq_of_linearIndependent {Ω M : Type} [Field Ω] [AddCommGroup M] [Module Ω M]
    {n : ℕ} {w : Fin n → M} (hw : LinearIndependent Ω w)
    {C D : Matrix (Fin n) (Fin n) Ω}
    (h : ∀ i, ∑ j, C i j • w j = ∑ j, D i j • w j) : C = D := by
  ext i j
  have h' : ∑ k, (C i k - D i k) • w k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h i, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hw (fun k => C i k - D i k) h' j)

theorem sum_smul_sum_smul {Ω M : Type} [Field Ω] [AddCommGroup M] [Module Ω M]
    {n : ℕ} (w : Fin n → M) (C D : Matrix (Fin n) (Fin n) Ω) (i : Fin n) :
    ∑ j, C i j • ∑ k, D j k • w k = ∑ k, (C * D) i k • w k := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem det_eq_unit_mul : ∀ (Ω M : Type) [Field Ω] [AddCommGroup M] [Module Ω M] (R : Subring Ω) (n : ℕ) (u : Fin n → M) (A B : Matrix (Fin n) (Fin n) Ω), LinearIndependent Ω u → LinearIndependent Ω (fun i => ∑ j, A i j • u j) → LinearIndependent Ω (fun i => ∑ j, B i j • u j) → Submodule.span R (Set.range fun i => ∑ j, A i j • u j) = Submodule.span R (Set.range fun i => ∑ j, B i j • u j) → ∃ c : Ω, c ∈ R ∧ c⁻¹ ∈ R ∧ c ≠ 0 ∧ B.det = c * A.det := by
  intro Ω M _ _ _ R n u A B hu ha _ hspan
  have key : ∀ a b : Fin n → M, Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range a) →
      ∃ P : Matrix (Fin n) (Fin n) Ω, (∀ i j, P i j ∈ R) ∧ ∀ i, b i = ∑ j, P i j • a j := by
    intro a b hle
    have hex : ∀ i, ∃ c : Fin n → R, ∑ j, c j • a j = b i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun R).mp (hle (Submodule.subset_span ⟨i, rfl⟩))
    choose c hc using hex
    refine ⟨Matrix.of fun i j => (c i j : Ω), fun i j => (c i j).2, fun i => ?_⟩
    rw [← hc i]
    exact Finset.sum_congr rfl fun j _ => Subring.smul_def _ _
  obtain ⟨P, hPR, hP⟩ := key (fun i => ∑ j, A i j • u j) (fun i => ∑ j, B i j • u j) hspan.ge
  obtain ⟨Q, hQR, hQ⟩ := key (fun i => ∑ j, B i j • u j) (fun i => ∑ j, A i j • u j) hspan.le
  have hP' : ∀ i, ∑ j, B i j • u j = ∑ j, P i j • ∑ k, A j k • u k := hP
  have hQ' : ∀ i, ∑ j, A i j • u j = ∑ j, Q i j • ∑ k, B j k • u k := hQ
  have hBPA : B = P * A := GlobalTheory.CompanionTheory.Ggeo.FrameDet.matrix_eq_of_linearIndependent hu fun i =>
    (hP' i).trans (GlobalTheory.CompanionTheory.Ggeo.FrameDet.sum_smul_sum_smul u P A i)
  have hQP : Q * P = 1 := by
    apply GlobalTheory.CompanionTheory.Ggeo.FrameDet.matrix_eq_of_linearIndependent ha
    intro i
    calc ∑ j, (Q * P) i j • ∑ k, A j k • u k
        = ∑ j, Q i j • ∑ k, P j k • ∑ l, A k l • u l :=
          (GlobalTheory.CompanionTheory.Ggeo.FrameDet.sum_smul_sum_smul (fun k => ∑ l, A k l • u l) Q P i).symm
      _ = ∑ j, Q i j • ∑ k, B j k • u k := Finset.sum_congr rfl fun j _ => by rw [hP' j]
      _ = ∑ k, A i k • u k := (hQ' i).symm
      _ = ∑ j, (1 : Matrix (Fin n) (Fin n) Ω) i j • ∑ k, A j k • u k := by
          simp [Matrix.one_apply]
  have hdet : P.det * Q.det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hQP, Matrix.det_one]
  refine ⟨P.det, det_mem_of_forall_mem' R P hPR, ?_, left_ne_zero_of_mul_eq_one hdet, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hdet]
    exact det_mem_of_forall_mem' R Q hQR
  · rw [hBPA, Matrix.det_mul]

end GlobalTheory.CompanionTheory.Ggeo.FrameDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocal
section
namespace GlobalTheory.CompanionTheory.IntegralClosureLocal

theorem mem_maximal_iff_not_inv_mem {K : Type} [Field K] (R : Subring K) [IsLocalRing R]
    (P : Ideal (integralClosure R K).toSubring) (hP : P.IsMaximal)
    (t : (integralClosure R K).toSubring) (htR : (t : K) ∈ R) :
    t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ R) := by
  let f : R →+* (integralClosure R K).toSubring :=
    (algebraMap R K).codRestrict (integralClosure R K).toSubring
      (fun r => (integralClosure R K).algebraMap_mem r)
  letI : Algebra R (integralClosure R K).toSubring := f.toAlgebra
  haveI : Algebra.IsIntegral R (integralClosure R K).toSubring := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp, h⟩ : IsIntegral R (x : K) := x.2
    refine ⟨p, hp, ?_⟩
    apply Subtype.ext
    have key := Polynomial.hom_eval₂ p f (integralClosure R K).toSubring.subtype x
    exact key.trans h
  have hm : (P.comap (algebraMap R (integralClosure R K).toSubring)).IsMaximal :=
    letI := hP
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  have hmax : P.comap (algebraMap R (integralClosure R K).toSubring)
      = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
  have hrt : algebraMap R (integralClosure R K).toSubring ⟨t, htR⟩ = t := Subtype.ext rfl
  have h1 : t ∈ P ↔ (⟨t, htR⟩ : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hmax, Ideal.mem_comap, hrt]
  rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have hne : (t : K) ≠ 0 := by
      intro h0
      have : (u : R) = 0 := by rw [hu]; exact Subtype.ext h0
      exact u.ne_zero this
    refine ⟨hne, ?_⟩
    have hmul : ((u : R) : K) * (((u⁻¹ : Rˣ) : R) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    have hut : ((u : R) : K) = (t : K) := by rw [hu]
    rw [hut] at hmul
    have : (t : K)⁻¹ = (((u⁻¹ : Rˣ) : R) : K) := inv_eq_of_mul_eq_one_right hmul
    rw [this]
    exact Subtype.coe_prop _
  · rintro ⟨hne, hinv⟩
    refine IsUnit.of_mul_eq_one (⟨(t : K)⁻¹, hinv⟩ : R) ?_
    exact Subtype.ext (mul_inv_cancel₀ hne)

end GlobalTheory.CompanionTheory.IntegralClosureLocal
end

