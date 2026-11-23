module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PhiDvd
section
open UpperTheory.V.FW

private theorem UpperTheory.V.FW.phiDvd_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (k A : Type) [Field k] [CharP k l]
    [CommRing A] [Algebra k A] (x : A) : (x - 1) ^ l ^ n = x ^ l ^ n - 1 := by
  have h : ((Polynomial.X : Polynomial k) - 1) ^ l ^ n = Polynomial.X ^ l ^ n - 1 := by
    rw [sub_pow_char_pow, one_pow]
  have := congrArg (Polynomial.aeval x) h
  simpa using this

private theorem UpperTheory.V.FW.phiDvd_nil (k A : Type) [Field k] [CommRing A] [Algebra k A] (T φ : A)
    (hT : IsNilpotent T) (hφ : φ ∈ Algebra.adjoin k {T}) (N : ℕ) (h : ¬ T ^ N ∣ φ) : φ ∣ T ^ N := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hφ
  obtain ⟨f, rfl⟩ := hφ
  change ¬ T ^ N ∣ Polynomial.aeval T f at h
  show Polynomial.aeval T f ∣ T ^ N
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h (by simp)
  obtain ⟨q, hq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  simp only [map_zero, sub_zero] at hq hnd
  rw [Polynomial.X_dvd_iff] at hnd
  have hu : IsUnit (Polynomial.aeval T q) := by
    obtain ⟨r, hr⟩ : Polynomial.X ∣ q - Polynomial.C (q.coeff 0) :=
      Polynomial.X_dvd_iff.2 (by simp)
    have hq' : q = Polynomial.C (q.coeff 0) + Polynomial.X * r := sub_eq_iff_eq_add'.mp hr
    have hev : Polynomial.aeval T q = algebraMap k A (q.coeff 0) + T * Polynomial.aeval T r := by
      conv_lhs => rw [hq']
      simp
    have hnil : IsNilpotent (T * Polynomial.aeval T r) := by
      obtain ⟨M, hM⟩ := hT
      exact ⟨M, by rw [mul_pow, hM, zero_mul]⟩
    have hc : IsUnit (algebraMap k A (q.coeff 0)) := (Ne.isUnit hnd).map _
    rw [hev]
    first
      | exact hnil.isUnit_add_right_of_commute hc (Commute.all _ _)
      | (rw [add_comm]; exact hnil.isUnit_add_right_of_commute hc (Commute.all _ _))
  have hφ : Polynomial.aeval T f = T ^ Polynomial.rootMultiplicity 0 f * Polynomial.aeval T q := by
    conv_lhs => rw [hq]
    simp
  by_cases hv : N ≤ Polynomial.rootMultiplicity 0 f
  · exfalso
    exact h (hφ ▸ dvd_mul_of_dvd_left (pow_dvd_pow T hv) _)
  · push_neg at hv
    rw [hφ]
    refine ⟨↑hu.unit⁻¹ * T ^ (N - Polynomial.rootMultiplicity 0 f), ?_⟩
    calc T ^ N = T ^ Polynomial.rootMultiplicity 0 f * T ^ (N - Polynomial.rootMultiplicity 0 f) := by
          rw [← pow_add, Nat.add_sub_cancel' hv.le]
      _ = T ^ Polynomial.rootMultiplicity 0 f * Polynomial.aeval T q *
          (↑hu.unit⁻¹ * T ^ (N - Polynomial.rootMultiplicity 0 f)) := by
          rw [mul_assoc, ← mul_assoc (Polynomial.aeval T q), hu.mul_val_inv, one_mul]

theorem UpperTheory.V.FW.phiDvd :
    ∀ (l : ℕ) [Fact l.Prime] (b K : ℕ) (k G Q : Type) [Field k] [CharP k l] [CommGroup G] [CommGroup Q] (p : G →* G) (π : G →* Q) (γ : G) (χ : G →* kˣ) (θ : MonoidAlgebra k G), γ ^ l ^ b = 1 → (∀ g, p g ∈ Subgroup.zpowers γ) → (∀ g, π (p g) = π g) → π γ ^ l ^ K = 1 → tw χ π θ ≠ 0 → tw χ p θ ∣ (MonoidAlgebra.of k G γ - 1) ^ l ^ K := by
  intro l _ b K k G Q _ _ _ _ p π γ χ θ hγ hp hπ hπγ hne
  set T : MonoidAlgebra k G := MonoidAlgebra.of k G γ - 1 with hT
  have hof : ∀ m : ℕ, MonoidAlgebra.of k G (γ ^ m) ∈ Algebra.adjoin k {T} := by
    intro m
    have e : MonoidAlgebra.of k G (γ ^ m) = (T + 1) ^ m := by rw [hT, sub_add_cancel, map_pow]
    rw [e]
    exact Subalgebra.pow_mem _ (Subalgebra.add_mem _ (Algebra.self_mem_adjoin_singleton k T) (Subalgebra.one_mem _)) _
  have hfin : IsOfFinOrder γ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ b, pow_pos (Fact.out : l.Prime).pos _, hγ⟩
  have hmem : tw χ p θ ∈ Algebra.adjoin k {T} := by
    rw [← MonoidAlgebra.sum_coeff_single θ, map_finsuppSum, Finsupp.sum]
    refine Subalgebra.sum_mem _ fun g _ => ?_
    rw [tw_single]
    obtain ⟨m, hm⟩ := (hfin.mem_powers_iff_mem_zpowers).2 (hp g)
    have e : MonoidAlgebra.single (p g) (θ.coeff g * ↑(χ g)) =
        (θ.coeff g * ↑(χ g)) • MonoidAlgebra.of k G (γ ^ m) := by
      rw [← (show γ ^ m = p g from hm), MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    rw [e]
    exact Subalgebra.smul_mem _ (hof m) _
  have hTnil : IsNilpotent T :=
    ⟨l ^ b, by rw [hT, phiDvd_pow l b k, ← map_pow, hγ, map_one, sub_self]⟩
  refine phiDvd_nil k _ T _ hTnil hmem _ ?_
  intro hdvd
  apply hne
  set ψ := MonoidAlgebra.mapDomainAlgHom k k π with hψ
  have hcomp : ψ.comp (tw χ p) = tw χ π := by
    refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
    simp [hψ, tw_single, hπ]
  have hψT : ψ T ^ l ^ K = 0 := by
    rw [← map_pow, hT, phiDvd_pow l K k, map_sub, map_pow, map_one]
    simp [hψ, MonoidAlgebra.of_apply, MonoidAlgebra.single_pow, ← map_pow, hπγ, MonoidAlgebra.one_def]
  obtain ⟨c, hc⟩ := hdvd
  have h1 : tw χ π θ = ψ (tw χ p θ) := by rw [← hcomp]; rfl
  rw [h1, hc, map_mul, map_pow, hψT, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SepChar
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sepChar :
    ∀ (k D A : Type) [Field k] [IsAlgClosed k] [CommGroup D] [Finite D] [CommRing A] [Algebra k A] (ρ : D →* A) (x : A), (Nat.card D : k) ≠ 0 → (∀ (ψ : D →* kˣ) (e : A), (∀ d, ρ d * e = (ψ d : k) • e) → x * e = 0) → x = 0 := by
  intro k D A _ _ _ _ _ _ ρ x hD h
  classical
  letI := Fintype.ofFinite D
  have hexp : ((Monoid.exponent D : ℕ) : k) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := Group.exponent_dvd_nat_card (G := D)
    apply hD
    rw [hc]; push_cast; rw [h0, zero_mul]
  haveI : NeZero ((Monoid.exponent D : ℕ) : k) := ⟨hexp⟩
  haveI : NeZero (Monoid.exponent D) := ⟨fun h0 => hexp (by rw [h0]; simp)⟩
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent D) := inferInstance
  have hcard : Nat.card (D →* kˣ) = Nat.card D :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity D k
  haveI : Finite (D →* kˣ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  letI := Fintype.ofFinite (D →* kˣ)
  have h1 : ∀ ψ : D →* kˣ, x * (∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d) = 0 := by
    intro ψ
    apply h ψ
    intro g
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro d
    simp only [Equiv.coe_mulLeft, mul_smul_comm, smul_smul, ← map_mul, ← Units.val_mul]
    congr 3
    rw [mul_inv, mul_inv_cancel_left]
  have h2 : ∀ d : D, d ≠ 1 → ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0 := by
    intro d hd
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity D k (a := d⁻¹) (inv_ne_one.mpr hd)
    have e : ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = (φ d⁻¹ : k) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) := by
      rw [Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.mulLeft φ) _ _ ?_).symm
      intro ψ
      simp only [Equiv.coe_mulLeft, MonoidHom.mul_apply, Units.val_mul]
    have hne : ((φ d⁻¹ : kˣ) : k) ≠ 1 := fun h' => hφ (Units.val_eq_one.mp h')
    have : (1 - ((φ d⁻¹ : kˣ) : k)) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0 := by
      rw [sub_mul, one_mul, ← e, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne.symm)
  have h3 : ∑ ψ : D →* kˣ, ∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d = (Nat.card D : k) • (1 : A) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (1 : D)]
    · rw [← hcard, Nat.card_eq_fintype_card]
      simp
    · intro d _ hd
      rw [h2 d hd, zero_smul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have h4 : x * ((Nat.card D : k) • (1 : A)) = 0 := by
    rw [← h3, Finset.mul_sum]
    exact Finset.sum_eq_zero fun ψ _ => h1 ψ
  rw [mul_smul_comm, mul_one] at h4
  exact (smul_eq_zero.mp h4).resolve_left hD
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SepPair
section
open UpperTheory.V.FW

private theorem sep_pair (l : ℕ) [Fact l.Prime] (x y : ℤ_[l]) :
    ∀ᶠ n in Filter.atTop, PadicInt.toZModPow n x = PadicInt.toZModPow n y → x = y := by
  by_cases h : x = y
  · exact Filter.Eventually.of_forall fun _ _ => h
  · obtain ⟨m, hm⟩ : ∃ m, PadicInt.toZModPow m x ≠ PadicInt.toZModPow m y := by
      by_contra hc
      push_neg at hc
      exact h (PadicInt.ext_of_toZModPow.mp hc)
    filter_upwards [Filter.eventually_ge_atTop m] with n hn heq
    exfalso
    apply hm
    rw [← PadicInt.cast_toZModPow m n hn x, ← PadicInt.cast_toZModPow m n hn y, heq]

theorem UpperTheory.V.FW.sep :
    ∀ (l : ℕ) [Fact l.Prime] (S : Finset ℤ_[l]), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Set.InjOn (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) S := by
  intro l _ S
  have h : ∀ᶠ n in Filter.atTop, ∀ p ∈ S ×ˢ S,
      PadicInt.toZModPow n p.1 = PadicInt.toZModPow n p.2 → p.1 = p.2 :=
    (Filter.eventually_all_finset _).mpr fun p _ => sep_pair l p.1 p.2
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨n₀, fun n hn x hx y hy hxy => hn₀ n hn (x, y) (Finset.mk_mem_product hx hy) hxy⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinFin
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinFin :
    ∀ (k ι : Type) [CommRing k] [Fintype ι] [DecidableEq ι] (m : ℕ) [NeZero m] (η : ι → (ZMod m)ˣ) (N : ℕ) (P : ℕ → k) (α : ZMod m → k), (∀ y, α y - α (y - N) = ∑ s ∈ Finset.range N, if (s : ZMod m) = y then P s else 0) → (∀ y, ∑ i, α (((η i)⁻¹ : (ZMod m)ˣ) * y) = 0) → sinE (fun i => (η i : ZMod m)) N P = 0 := by
  intro k ι _ _ _ m _ η N P α hα hsum
  have hsingSum : ∀ (z : ZMod m) (t : Finset ℕ) (g : ℕ → k),
      AddMonoidAlgebra.single z (∑ s ∈ t, g s) = ∑ s ∈ t, AddMonoidAlgebra.single z (g s) :=
    fun z t g => map_sum (AddMonoidAlgebra.singleAddHom z) g t
  have hsingSumι : ∀ (z : ZMod m) (g : ι → k),
      AddMonoidAlgebra.single z (∑ i, g i) = ∑ i, AddMonoidAlgebra.single z (g i) :=
    fun z g => map_sum (AddMonoidAlgebra.singleAddHom z) g Finset.univ
  have hsingSub : ∀ (z : ZMod m) (a b : k),
      AddMonoidAlgebra.single z (a - b) = AddMonoidAlgebra.single z a - AddMonoidAlgebra.single z b :=
    fun z a b => map_sub (AddMonoidAlgebra.singleAddHom z) a b
  set A : ι → AddMonoidAlgebra k (ZMod m) :=
    fun i => ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α y) with hA
  have hS : ∀ i, (∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s)) =
      (1 - AddMonoidAlgebra.single (N • (η i : ZMod m)) 1) * A i := by
    intro i
    have hone : ∀ s : ℕ, ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y)
        (if (s : ZMod m) = y then P s else 0) = AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s) := by
      intro s
      rw [Finset.sum_eq_single (s : ZMod m)]
      · simp [nsmul_eq_mul, mul_comm]
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    have e1 : ∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s) =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α y - α (y - N)) := by
      simp_rw [hα, hsingSum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => (hone s).symm
    have e2 : ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α (y - N)) =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * (y + N)) (α y) := by
      rw [← Equiv.sum_comp (Equiv.addRight (N : ZMod m))]
      simp
    have e3 : AddMonoidAlgebra.single (N • (η i : ZMod m)) (1 : k) * A i =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * (y + N)) (α y) := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [AddMonoidAlgebra.single_mul_single, one_mul, nsmul_eq_mul]
      congr 1
      ring
    rw [e1, sub_mul, one_mul, e3, ← e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => hsingSub _ _ _
  have hA0 : ∑ i, A i = 0 := by
    have hre : ∀ i, A i = ∑ z : ZMod m,
        AddMonoidAlgebra.single z (α (((η i)⁻¹ : (ZMod m)ˣ) * z)) := by
      intro i
      rw [hA, ← Equiv.sum_comp (Units.mulLeft (η i))]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp
    simp_rw [hre]
    rw [Finset.sum_comm]
    simp_rw [← hsingSumι, hsum]
    simp
  unfold sinE
  dsimp only
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [hS i, mul_assoc, mul_left_comm, Finset.mul_prod_erase Finset.univ
      (fun j => 1 - AddMonoidAlgebra.single (N • (η j : ZMod m)) (1 : k)) (Finset.mem_univ i)])]
  rw [← Finset.sum_mul, hA0, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinMap
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinMap :
    ∀ (k A B ι : Type) [CommRing k] [AddCommGroup A] [AddCommGroup B] [Fintype ι] [DecidableEq ι] (φ : A →+ B) (η : ι → A) (N : ℕ) (P : ℕ → k), AddMonoidAlgebra.mapDomainRingHom k φ (sinE η N P) = sinE (fun i => φ (η i)) N P := by
  intro k A B ι _ _ _ _ _ φ η N P
  unfold sinE
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_sub, map_one, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, map_nsmul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinSign
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinSign :
    ∀ x : ℝ, 0 ≤ x → Real.sin (Real.pi * x) ≠ 0 → (Real.sin (Real.pi * x) < 0 ↔ Odd ⌊x⌋₊) := by
  intro x hx hne
  set n := ⌊x⌋₊ with hn
  have h0 : (0 : ℝ) ≤ x - n := sub_nonneg.mpr (Nat.floor_le hx)
  have h1 : x - n ≤ 1 := by
    have := Nat.lt_floor_add_one x
    linarith
  have hs : 0 ≤ Real.sin (Real.pi * (x - n)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le h0)
      (mul_le_of_le_one_right Real.pi_pos.le h1)
  have he : Real.sin (Real.pi * x) = (-1) ^ n * Real.sin (Real.pi * (x - n)) := by
    rw [← Real.sin_add_nat_mul_pi]
    congr 1
    ring
  rw [he] at hne ⊢
  have hpos : 0 < Real.sin (Real.pi * (x - n)) :=
    lt_of_le_of_ne hs (fun h => hne (by rw [← h, mul_zero]))
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, one_mul]
    exact ⟨fun hlt => absurd hlt (not_lt.mpr hpos.le), fun ho => absurd ho (Nat.not_odd_iff_even.mpr h)⟩
  · rw [h.neg_one_pow]
    exact ⟨fun _ => h, fun _ => by linarith⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinSupp
section
open UpperTheory.V.FW

private theorem prod_single_eq_single_sum {k A ι : Type} [CommRing k] [AddCommGroup A] [DecidableEq ι]
    (T : Finset ι) (f : ι → A) (c : k) :
    ∏ j ∈ T, (AddMonoidAlgebra.single (f j) c : AddMonoidAlgebra k A)
      = AddMonoidAlgebra.single (∑ j ∈ T, f j) (∏ _j ∈ T, c) := by
  induction T using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, ih, AddMonoidAlgebra.single_mul_single, Finset.sum_insert hi,
      Finset.prod_insert hi]

private theorem coeff_monic_poly_sum {k A ι : Type} [CommRing k] [AddCommGroup A]
    (T : Finset ι) (f : ι → AddMonoidAlgebra k A) (a : A) (h : (∑ j ∈ T, f j).coeff a ≠ 0) :
    ∃ j ∈ T, (f j).coeff a ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero hc

theorem UpperTheory.V.FW.sinSupp :
    ∀ (A ι : Type) [AddCommGroup A] [Fintype ι] [DecidableEq ι] (η : ι → A) (N : ℕ), ∃ S : Finset A, ∀ (k : Type) [CommRing k] (P : ℕ → k) (a : A), (sinE η N P).coeff a ≠ 0 → a ∈ S := by
  intro A ι _ _ _ η N
  classical
  refine ⟨(Finset.univ ×ˢ (Finset.range N ×ˢ (Finset.univ : Finset ι).powerset)).image
    (fun p : ι × ℕ × Finset ι => p.2.1 • η p.1 + ∑ j ∈ p.2.2, N • η j), ?_⟩
  intro k _ P a ha
  simp only [sinE] at ha
  obtain ⟨i, -, hi⟩ := coeff_monic_poly_sum _ _ a ha
  have hprod : ∏ j ∈ Finset.univ.erase i, (1 - AddMonoidAlgebra.single (N • η j) (1 : k))
      = ∑ t ∈ (Finset.univ.erase i).powerset,
          AddMonoidAlgebra.single (∑ j ∈ t, N • η j) (∏ _j ∈ t, (-1 : k)) := by
    have e : ∀ j, (1 - AddMonoidAlgebra.single (N • η j) (1 : k))
        = AddMonoidAlgebra.single (N • η j) (-1 : k) + 1 := by
      intro j
      rw [AddMonoidAlgebra.single_neg]
      abel
    simp_rw [e]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_const_one, mul_one, prod_single_eq_single_sum]
  rw [hprod, Finset.sum_mul] at hi
  obtain ⟨s, hs, hs2⟩ := coeff_monic_poly_sum _ _ a hi
  rw [Finset.mul_sum] at hs2
  obtain ⟨t, ht, ht2⟩ := coeff_monic_poly_sum _ _ a hs2
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single_apply] at ht2
  split_ifs at ht2 with hEq
  · rw [Finset.mem_image]
    refine ⟨(i, s, t), ?_, hEq⟩
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_powerset, true_and]
    exact ⟨hs, Finset.subset_univ _⟩
  · exact absurd rfl ht2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ToZModPowOneEqZeroIff
section
open UpperTheory.V.FW

private theorem toZModPow_one_eq_zero_iff {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    PadicInt.toZModPow 1 x = 0 ↔ ‖x‖ < 1 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton, pow_one]

private theorem exists_root_lift {l : ℕ} [Fact l.Prime] (u : (ZMod (l ^ 1))ˣ) :
    ∃ ζ ∈ rootsOfUnity (Nat.totient (l ^ 1)) ℤ_[l], redU l 1 ζ = u := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  have ht : Nat.totient (l ^ 1) = l - 1 := by rw [pow_one, Nat.totient_prime hl]
  have hu : u ^ (l - 1) = 1 := by
    rw [← ht, ← ZMod.card_units_eq_totient]
    exact pow_card_eq_one
  have hn : l - 1 ≠ 0 := by have := hl.two_le; omega
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], PadicInt.toZModPow 1 a = (u : ZMod (l ^ 1)) :=
    ⟨((u : ZMod (l ^ 1)).val : ℤ_[l]), by simp⟩
  set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hF
  have hFa : ‖F.aeval a‖ < 1 := by
    rw [← toZModPow_one_eq_zero_iff]
    have : ((u : ZMod (l ^ 1))) ^ (l - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
    simp [hF, ha, this]
  have hdF : ‖(Polynomial.derivative F).aeval a‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    rw [← toZModPow_one_eq_zero_iff] at h
    have hmul : PadicInt.toZModPow 1 ((Polynomial.derivative F).aeval a) =
        ((l - 1 : ℕ) : ZMod (l ^ 1)) * ((u : ZMod (l ^ 1))) ^ (l - 1 - 1) := by
      rw [hF, Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow]
      simp [ha]
    have hcast : ((l - 1 : ℕ) : ZMod (l ^ 1)) = -1 := by
      rw [Nat.cast_sub hl.one_le, Nat.cast_one, pow_one, ZMod.natCast_self, zero_sub]
    rw [hmul, hcast, neg_one_mul, neg_eq_zero, ← Units.val_pow_eq_pow_val] at h
    exact Units.ne_zero _ h
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a) (by rw [hdF]; simpa using hFa)
  rw [hdF, ← toZModPow_one_eq_zero_iff, map_sub, sub_eq_zero, ha] at hza
  have hz1 : z ^ (l - 1) = 1 := by
    simpa [hF, sub_eq_zero] using hz
  refine ⟨Units.ofPowEqOne z (l - 1) hz1 hn, ?_, ?_⟩
  · rw [ht, mem_rootsOfUnity]
    exact Units.pow_ofPowEqOne _ _
  · exact Units.ext (by simp [redU, hza])

private theorem units_four (u : (ZMod (2 ^ 2))ˣ) : u = 1 ∨ u = -1 := by
  revert u
  decide

theorem UpperTheory.V.FW.teich :
    ∀ (l : ℕ) [Fact l.Prime], Function.Bijective ((redU l (ee l)).comp (WW l).subtype) := by
  intro l _
  have hl : l.Prime := Fact.out
  have hsurj : Function.Surjective ((redU l (ee l)).comp (WW l).subtype) := by
    by_cases h2 : l = 2
    · subst h2
      intro u
      have ht : Nat.totient (2 ^ ee 2) = 2 := by decide
      rcases units_four u with h | h
      · exact ⟨1, by simp [h] <;> rfl⟩
      · refine ⟨⟨-1, ?_⟩, ?_⟩
        · show (-1 : ℤ_[2]ˣ) ∈ rootsOfUnity (Nat.totient (2 ^ ee 2)) ℤ_[2]
          rw [ht, mem_rootsOfUnity]
          simp
        · rw [h]
          exact Units.ext (by simp [redU] <;> rfl)
    · have he : ee l = 1 := if_neg h2
      have key : ∀ u : (ZMod (l ^ 1))ˣ, ∃ a : WW l, (redU l 1) a = u := by
        intro u
        obtain ⟨ζ, hζ, hred⟩ := exists_root_lift u
        exact ⟨⟨ζ, by simpa [WW, he] using hζ⟩, hred⟩
      rw [he]
      intro u
      obtain ⟨a, ha⟩ := key u
      exact ⟨a, ha⟩
  have hfin : Finite (WW l) := by
    show Finite (rootsOfUnity _ ℤ_[l])
    infer_instance
  haveI : NeZero (l ^ ee l) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hc := card_rootsOfUnity ℤ_[l] (Nat.totient (l ^ ee l))
  refine hsurj.bijective_of_nat_card_le (le_trans hc (le_of_eq ?_))
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
end

