module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHOmega
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {W : LocWach PD LL O v n}

theorem Pf_HOmega_pow_card (δ : W.Gam) (hδ : δ ∈ W.DelF) : δ ^ W.DelF.card = 1 := by
  have hH : ∀ g : W.Gam, g ∈ CommGroup.torsion W.Gam ↔ g ∈ W.DelF := by
    intro g
    rw [W.DelF_def, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  have hset : ((CommGroup.torsion W.Gam : Subgroup W.Gam) : Set W.Gam) = (W.DelF : Set W.Gam) := by
    ext g
    simp only [SetLike.mem_coe]
    exact hH g
  have hcardH : Nat.card (CommGroup.torsion W.Gam) = W.DelF.card := by
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hd := orderOf_dvd_natCard (⟨δ, (hH δ).2 hδ⟩ : CommGroup.torsion W.Gam)
  rw [Subgroup.orderOf_mk, hcardH] at hd
  exact orderOf_dvd_iff_pow_eq_one.1 hd

theorem hω_holds (hcard : W.DelF.card = PD.p - 1) (hinj : Function.Injective (algebraMap O LL))
    (ιZ : ℤ_[PD.p] →+* O) :
    ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF, algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ω.1) := by
  classical
  intro ω
  have hpos : 0 < PD.p - 1 := by have := PD.hp.two_le; omega
  set f : W.Gam → LL := fun g => algebraMap O LL (W.χΓ g : O) with hf
  have hAcard : (W.DelF.image f).card = PD.p - 1 := by
    rw [Finset.card_image_of_injOn, hcard]
    intro x _ y _ hxy
    apply W.χΓ_inj
    apply Units.ext
    exact hinj hxy
  have hARt : W.DelF.image f ⊆ Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [Polynomial.mem_nthRootsFinset hpos]
    have h1 : g ^ (PD.p - 1) = 1 := hcard ▸ Pf_HOmega_pow_card g hg
    simp only [hf]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one, map_one]
  have hRt : (Polynomial.nthRootsFinset (PD.p - 1) (1 : LL)).card ≤ PD.p - 1 := by
    unfold Polynomial.nthRootsFinset
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  have hEq : W.DelF.image f = Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) :=
    Finset.eq_of_subset_of_card_le hARt (by omega)
  have hωR : algebraMap O LL (ιZ ω.1) ∈ Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) := by
    rw [Polynomial.mem_nthRootsFinset hpos, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ω.2,
      Units.val_one, map_one, map_one]
  rw [← hEq] at hωR
  obtain ⟨g, hg, hgω⟩ := Finset.mem_image.1 hωR
  exact ⟨g, hg, hgω⟩

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvDelta
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Graded

variable {LL Ks : Type} [Field LL] [CommRing Ks] [Algebra LL Ks]

theorem grdB_zero' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a 0 = 0 := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((0 : HahnSeries ℤ Ks).coeff n) = (0 : HahnSeries ℤ Ks).coeff n
  simp

theorem grdB_one' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a 1 = 1 := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((1 : HahnSeries ℤ Ks).coeff n) = (1 : HahnSeries ℤ Ks).coeff n
  by_cases h : n = 0
  · subst h
    simp
  · simp [HahnSeries.coeff_one, h]

theorem grdB_mul' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x y : HahnSeries ℤ Ks) :
    grdB τ a (x * y) = grdB τ a x * grdB τ a y := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((x * y).coeff n) = (grdB τ a x * grdB τ a y).coeff n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [HahnSeries.coeff_mul, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
  symm
  have hsub : ∀ ij : ℤ × ℤ, ij ∈ Finset.antidiagonal (grdB τ a x).isPWO_support
      (grdB τ a y).isPWO_support n → ij ∈ Finset.antidiagonal x.isPWO_support y.isPWO_support n := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    refine ⟨fun h0 => hij.1 ?_, fun h0 => hij.2.1 ?_, hij.2.2⟩
    · change algebraMap LL Ks ((a ^ ij.1 : LLˣ) : LL) * τ (x.coeff ij.1) = 0
      rw [h0, map_zero, mul_zero]
    · change algebraMap LL Ks ((a ^ ij.2 : LLˣ) : LL) * τ (y.coeff ij.2) = 0
      rw [h0, map_zero, mul_zero]
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    have hn : ij.1 + ij.2 = n := hij.2.2
    change (algebraMap LL Ks ((a ^ ij.1 : LLˣ) : LL) * τ (x.coeff ij.1)) *
      (algebraMap LL Ks ((a ^ ij.2 : LLˣ) : LL) * τ (y.coeff ij.2)) = _
    rw [← hn, zpow_add, Units.val_mul, map_mul, map_mul]
    ring
  · intro ij hmem hnot
    rw [Finset.mem_antidiagonal] at hmem hnot
    by_cases h1 : (grdB τ a x).coeff ij.1 = 0
    · rw [h1, zero_mul]
    · by_cases h2 : (grdB τ a y).coeff ij.2 = 0
      · rw [h2, mul_zero]
      · exact absurd ⟨h1, h2, hmem.2.2⟩ hnot

theorem grdB_ringInverse (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) {X : HahnSeries ℤ Ks} (hX : grdB τ a X = X) :
    grdB τ a (Ring.inverse X) = Ring.inverse X := by
  by_cases hu : IsUnit X
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    have h1 : grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * ↑u = 1 := by
      conv_lhs => rw [← hX]
      rw [← grdB_mul', Units.inv_mul, grdB_one']
    calc grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks)
        = grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = (grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * ↑u) * ↑u⁻¹ := by ring
      _ = ↑u⁻¹ := by rw [h1, one_mul]
  · rw [Ring.inverse_non_unit _ hu, grdB_zero']

theorem ofPS_coeff_neg {R : Type} [CommRing R] (x : PowerSeries R) {i : ℤ} (hi : i < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff i = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_of_notMem_range (by
    rintro ⟨m, hm⟩
    simp at hm
    omega)

end Graded

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem val_sub_toZModPow (W : LocWach PD LL O v n) (valRing : ValRing O v) (ιZ : ℤ_[PD.p] →+* O)
    (ω : ℤ_[PD.p]) (N : ℕ) :
    ((N : ℕ) : WithTop ℚ) ≤
      v (algebraMap O LL (ιZ ω) - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : LL)) := by
  have : NeZero (PD.p ^ N) := ⟨pow_ne_zero _ PD.hp.ne_zero⟩
  have hk : ω - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : ℤ_[PD.p]) ∈
      RingHom.ker (PadicInt.toZModPow (p := PD.p) N) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨y, hy⟩ := hk
  have e : algebraMap O LL (ιZ ω) - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : LL) =
      ((PD.p : ℕ) : LL) ^ N * algebraMap O LL (ιZ y) := by
    rw [← map_natCast (algebraMap O LL), ← map_natCast ιZ, ← map_sub, ← map_sub, hy, map_mul, map_mul,
      map_pow, map_pow, map_natCast, map_natCast]
  rw [e, AddValuation.map_mul, AddValuation.map_pow, W.v_l, nsmul_one]
  exact le_add_of_nonneg_right (valRing.2.2 _)

variable {W : LocWach PD LL O v n}

theorem delta_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (c : ZMod n)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF, algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ω.1))
    (valRing : ValRing O v) :
    DeltaRho hR uZ ιZ c := by
  intro s j a
  obtain ⟨g, hg, hχ⟩ := hω j
  apply HahnSeries.ext
  funext i
  by_cases hi : i < 0
  · show algebraMap LL (KsW W s) ((((levW W uZ ιZ s).a j) ^ i : LLˣ) : LL) *
        ((levW W uZ ιZ s).τ j) ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i) =
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i
    rw [ofPS_coeff_neg _ hi, map_zero, mul_zero]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hi)
    show algebraMap LL (KsW W s) ((((levW W uZ ιZ s).a j) ^ (k : ℤ) : LLˣ) : LL) *
        ((levW W uZ ιZ s).τ j) ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff (k : ℤ)) =
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff (k : ℤ)
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    have hc : ∀ ζ' : Rs LL PD.p s, (PowerSeries.coeff k (rhoL hR c s a)) ζ' =
        PowerSeries.coeff k (W.lev c (ζ' : LL) ((baseIdOf hR).d a)) := fun ζ' => by
      show Pi.evalRingHom (fun _ => LL) ζ' (PowerSeries.coeff k (rhoL hR c s a)) = _
      rw [← PowerSeries.coeff_map, map_eval_rhoL]
      rfl
    funext ζ
    change ((((levW W uZ ιZ s).a j) ^ (k : ℤ) : LLˣ) : LL) *
      (PowerSeries.coeff k (rhoL hR c s a)) (powR LL PD.p s (redU PD.p s j.1) ζ) =
      (PowerSeries.coeff k (rhoL hR c s a)) ζ
    rw [hc, hc]
    have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) := (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
    have hv := val_sub_toZModPow W valRing ιZ (j.1 : ℤ_[PD.p]) (s + 1)
    rw [← hχ] at hv
    have hL := lev_Γ g c ζ _ (s + 1) _ hprim hv rfl ((baseIdOf hR).d a)
    rw [BaseId.γA_Δ _ g hg] at hL
    rw [hL, PowerSeries.coeff_rescale, hχ]
    congr 1

theorem loclInv_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (T : LocLat G Qp LL O)
    (c : ZMod n) {r : ℕ} (Λ : PowerSeries O) (lam : Fin r → Dc W T c) (hΔ : DeltaRho hR uZ ιZ c) :
    LocLInv hR uZ ιZ T c Λ lam := by
  intro s y j
  rw [Level.δ]
  unfold locLF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [graded_semilinear_holds, grdB_ringInverse _ _ (hΔ s j Λ), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [graded_semilinear_holds, hΔ s j (y k), SlopeTestRemainingChoices.grd_cst]

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvExp
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Conv

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem Pf_LvExp_coeff_neg (x : PowerSeries R) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff (Int.negSucc k) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  simp

theorem Pf_LvExp_coeff_smul (x : PowerSeries R) (y : HahnModule ℤ R M) (m : ℤ)
    (hy : ∀ k < m, ((HahnModule.of R).symm y).coeff k = 0) (k : ℤ) (N : ℕ) (hN : k - m < N) :
    ((HahnModule.of R).symm (HahnSeries.ofPowerSeries ℤ R x • y)).coeff k =
      ∑ j ∈ Finset.range N, PowerSeries.coeff j x • ((HahnModule.of R).symm y).coeff (k - j) := by
  rw [HahnModule.coeff_smul]
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ => ((j : ℤ), k - j)) ?_ ?_ ?_ ?_
  · intro j _ hj
    have h1 : PowerSeries.coeff j x ≠ 0 := fun h => hj (by rw [h, zero_smul])
    have h2 : ((HahnModule.of R).symm y).coeff (k - j) ≠ 0 := fun h => hj (by rw [h, smul_zero])
    rw [Finset.mem_vaddAntidiagonal]
    refine ⟨?_, ?_, ?_⟩
    · rw [HahnSeries.mem_support, HahnSeries.ofPowerSeries_apply_coeff]
      exact h1
    · rw [HahnSeries.mem_support]
      exact h2
    · show (j : ℤ) + (k - j) = k
      ring
  · intro j _ _ j' _ _ h
    exact_mod_cast (Prod.mk.inj h).1
  · intro ij hij hne
    rw [Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    obtain ⟨i, i'⟩ := ij
    simp only at h1 h2 h3 hne
    cases i with
    | negSucc t => exact absurd (Pf_LvExp_coeff_neg x t) ((HahnSeries.mem_support _ _).1 h1)
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast, vadd_eq_add] at h3 hne
      have hi' : i' = k - j := by omega
      have hm' : m ≤ i' := by
        by_contra hlt
        push Not at hlt
        exact (HahnSeries.mem_support _ _).1 h2 (hy _ hlt)
      refine ⟨j, Finset.mem_range.2 (by omega), ?_, ?_⟩
      · rw [← hi']
        rwa [HahnSeries.ofPowerSeries_apply_coeff] at hne
      · simp [hi']
  · intro j _ _
    dsimp only
    rw [HahnSeries.ofPowerSeries_apply_coeff]

theorem Pf_LvExp_finsum (f : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • g (k - j) = ∑ j ∈ Finset.range N, PowerSeries.coeff j f • g (k - j) := by
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply hj
  show PowerSeries.coeff j f • g (k - j) = 0
  rw [hg (k - j) (by omega), smul_zero]

end Conv

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem Pf_LvExp_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab


open Classical in
def Pf_LvExp_Φ (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

theorem Pf_LvExp_Φ_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (f : Rs LL PD.p s → D) : Pf_LvExp_Φ W s D (toKsD W s D f) = f := by
  simp only [Pf_LvExp_Φ, toKsD, LinearEquiv.trans_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem Pf_LvExp_Φ_smul (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (f : KsW W s)
    (z : KsW W s ⊗[LL] D) (ζ : Rs LL PD.p s) :
    Pf_LvExp_Φ W s D (f • z) ζ = f ζ • Pf_LvExp_Φ W s D z ζ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul g d => simp [Pf_LvExp_Φ, TensorProduct.smul_tmul', TensorProduct.piScalarRightHom_tmul, mul_smul]
  | add z z' hz hz' => rw [smul_add, map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, hz, hz', smul_add]

theorem Pf_LvExp_coeff_expN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) : ((HahnModule.of (KsW W s)).symm (expN Lb s T c y)).coeff k = coefN Lb s T c y k :=
  rfl

theorem Pf_LvExp_Φ_coefN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) (ζ : Rs LL PD.p s) :
    ((Pf_LvExp_Φ W s (Dc W T c) (coefN Lb s T c y k) ζ : Dc W T c) : T.V ⊗[Qp] B) =
      Lb.levB T c ζ y k := by
  simp only [coefN, Pf_LvExp_Φ_toKsD]

theorem expSemi_holds (Lb : LevB W) (hR : Ring9 W) (T : LocLat G Qp LL O) (c : ZMod n)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k)) :
    ExpSemi Lb hR T c := by
  intro s a y hy
  obtain ⟨m, hm⟩ := bdd_coefN Lb s T c y
  have hm' : ∀ k < m, coefN Lb s T c y k = 0 := fun k hk => by
    by_contra h
    exact absurd (hm h) (not_le.2 hk)
  apply (HahnModule.of (KsW W s)).symm.injective
  ext k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N := ⟨(k - m).toNat + 1, by omega⟩
  rw [Pf_LvExp_coeff_smul _ _ m (fun k' hk' => by rw [Pf_LvExp_coeff_expN]; exact hm' k' hk') k N hN]
  simp only [Pf_LvExp_coeff_expN]
  apply (Pf_LvExp_Φ W s (Dc W T c)).injective
  funext ζ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  simp only [Pf_LvExp_Φ_smul]
  apply Subtype.ext
  apply Pf_LvExp_ιV_inj (PD := PD) T
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Pf_LvExp_Φ_coefN]
  simp only [← levN_eq]
  have hg : ∀ k' < m, W.levN T c ζ y k' = 0 := fun k' hk' => by
    rw [levN_eq, ← Pf_LvExp_Φ_coefN Lb s T c y k' ζ, hm' k' hk', map_zero]
    simp
  rw [show (⟨_, hy⟩ : ↥(W.N T)) = (baseIdOf hR).d a • y from rfl, W.levN_smul,
    Pf_LvExp_finsum _ _ m hg k N hN]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := congrArg (PowerSeries.coeff j) (map_eval_rhoL hR c s a ζ)
  rw [PowerSeries.coeff_map] at h
  exact h.symm

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvRhoC
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem rhoC_holds (hR : Ring9 W) (c : ZMod n) (s : ℕ) (a : O) :
    rhoL hR c s (PowerSeries.C a) =
      PowerSeries.C (algebraMap LL (KsW W s) (algebraMap O LL a)) := by
  ext k ζ
  have hC : (PowerSeries.C a : PowerSeries O) = algebraMap O (PowerSeries O) a := by
    rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h1 : PowerSeries.coeff k (rhoL hR c s (PowerSeries.C a)) ζ =
      PowerSeries.coeff k (rhoZ W c ζ ((baseIdOf hR).ι (PowerSeries.C a))) := by
    have h := congrArg (PowerSeries.coeff k) (map_eval_rhoL hR c s (PowerSeries.C a) ζ)
    rw [PowerSeries.coeff_map] at h
    exact h
  rw [h1, hC, AlgHom.commutes, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.coeff_C,
    PowerSeries.coeff_C]
  split_ifs <;> rfl

end Formalism.MainNotions.N.Ln03.Pf
end
end

