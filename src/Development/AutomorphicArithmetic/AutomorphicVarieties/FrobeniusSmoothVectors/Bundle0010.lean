module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBstab
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C}
    (hM : UpT M) (hN : UpT N) : UpT (M * N) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : a < i
  · rw [hM i a ha, zero_mul]
  · rw [hN a j (lt_of_lt_of_le h (not_lt.mp ha)), mul_zero]

theorem UpperTheory.V.Fr.pr_bstab :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (C : Type) [CommRing C] (B : Box F n C) (v : F.V) (s : F.Gv v), ∀ X ∈ B.b v, B.ad (F.loc v s) X ∈ B.b v := by
  intro l _ k _ F n C _ B v s X hX
  have h1 : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have h2 : (B.r (F.loc v s⁻¹)).left = (B.r (F.loc v s)).left⁻¹ := by
    rw [map_inv, map_inv, SemidirectProduct.inv_left, h1, inv_one, sgnAct_one]
  have t1 := B.tri v s
  have t2 := B.tri v s⁻¹
  have t3 := upT_mul (upT_mul t1 hX) t2
  simp only [GG.mat, h2] at t3
  show UpT ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).adFun X *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))
  have hg : ∀ Y : Matrix (Fin n) (Fin n) C,
      (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) * ((B.g v : Matrix (Fin n) (Fin n) C) * Y) = Y :=
    fun Y => Units.inv_mul_cancel_left _ Y
  simp only [Matrix.mul_assoc, hg] at t3
  simp only [GG.adFun, GG.mat, h1, if_true, Matrix.mul_assoc]
  exact t3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem tri_zero {K G ι : Type} [Field K] [Fintype ι] [LinearOrder ι] (M : G → Matrix ι ι K) (ω : G → K)
    (Φ : Matrix ι ι K) (hM : ∀ g i j, j < i → M g i j = 0)
    (h : ∀ g i j, ∑ p, M g i p * Φ p j = ω g * ∑ q, Φ i q * M g q j)
    (key : ∀ i j, (∀ g, M g i i * Φ i j = ω g * (Φ i j * M g j j)) → Φ i j = 0) : ∀ i j, Φ i j = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | _ i ih =>
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih' =>
  refine key i j fun g => ?_
  have := h g i j
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at this
  · exact this
  · intro q _ hq
    rcases lt_or_gt_of_ne hq with h1 | h1
    · rw [ih' q h1, zero_mul]
    · rw [hM g q j h1, mul_zero]
  · simp
  · intro p _ hp
    rcases lt_or_gt_of_ne hp with h1 | h1
    · rw [hM g i p h1, zero_mul]
    · rw [ih p h1 j, mul_zero]
  · simp

private theorem om_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (F : Frame l k) {K : Type} [Field K]
    [CharP K l] (φ : k →+* K) (g : F.Γ) : φ (F.om k g : k) = (F.om K g : K) := by
  have : φ.comp (ZMod.castHom (dvd_refl l) k) = ZMod.castHom (dvd_refl l) K := Subsingleton.elim _ _
  exact RingHom.congr_fun this _

private theorem w_cases {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) :
    w n j - w n i = 0 ∨ (w n j - w n i = 1 ∨ w n j - w n i = -1) ∨
      ((w n j - w n i = 2 ∨ w n j - w n i = -2) ∧ j = i.rev) := by
  rcases hn with rfl | rfl
  · revert i j; decide
  · revert i j; decide

private theorem thetaLie_single {K : Type} [Field K] {n : ℕ} (i : Fin n) :
    thetaLie (Matrix.single i i.rev (1 : K)) = -Matrix.single i i.rev (1 : K) := by
  unfold thetaLie
  congr 1
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b.rev, Matrix.mul_apply, Finset.sum_eq_single a.rev]
  · simp only [Jmat, Matrix.transpose_apply, Matrix.single_apply, Fin.rev_rev, if_true, one_mul, mul_one,
      Fin.rev_inj]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl⟩; simp
  · intro p _ hp
    simp [Jmat, hp]
  · simp
  · intro p _ hp
    have : b ≠ p.rev := fun h => hp (by simp [h])
    simp [Jmat, this]
  · simp

theorem UpperTheory.V.Fr.pr_dual :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] [CharP K l] (φ : k →+* K) (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.IsBar φ → ((∀ g, UpT (ρ.r g)) ∨ ∀ g, UpT (ρ.r g)ᵀ) → ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K, (∀ g X, f (B.ad g X) = F.om K g * f X) → f = 0 := by
  intro l _ k _ _ F C₀ n ok hn K _ _ φ ρ B hB hbar htri f hf
  set Φ : Matrix (Fin n) (Fin n) K := fun i j => f (Matrix.single i j 1) with hΦ
  have hsum : ∀ X : Matrix (Fin n) (Fin n) K, f X = ∑ i, ∑ j, X i j * Φ i j := fun X => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ, ← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have h0 : ∀ (g : F.G0) X, f (ρ.r g * X) = F.om K g * f (X * ρ.r g) := fun g X => by
    rw [← hf]
    congr 1
    have hr : (B.r g).right = 1 := (B.nu g).trans g.2
    show _ = (B.r g).adFun _
    rw [GG.adFun, if_pos hr, ← hB.res g, GG.mat]
    simp [Matrix.mul_assoc]
  have h1 : ∀ (g : F.G0) i j, ∑ p, ρ.r g p i * Φ p j = F.om K g * ∑ q, Φ i q * ρ.r g j q := fun g i j => by
    have := h0 g (Matrix.single i j 1)
    rw [hsum, hsum] at this
    rw [Finset.sum_eq_single i (s := Finset.univ) (f := fun a => ∑ b, (Matrix.single i j (1 : K) * ρ.r g) a b * Φ a b)]
      at this
    · convert this using 2 with p
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
        · simp
      · simp [mul_comm]
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, zero_mul]
    · simp
  have hc : ∀ i, -Φ i i.rev = F.om K F.c * Φ i i.rev := fun i => by
    rw [hΦ]
    dsimp only
    rw [← hf, ← map_neg, ← thetaLie_single]
    congr 1
    have hr : (B.r F.c).right ≠ 1 := by rw [B.nu, ok.del_c]; decide
    have hl : (B.r F.c).left = 1 := Units.ext hB.atc
    show _ = (B.r F.c).adFun _
    rw [GG.adFun, if_neg hr, GG.mat, hl]
    simp
  have key : ∀ i j, (∀ g : F.G0, ρ.r g i i * Φ i j = F.om K g * (Φ i j * ρ.r g j j)) → Φ i j = 0 := by
    intro i j h
    by_contra hne
    have h2 : ∀ g : F.G0, F.om k g * F.Ψ g ^ (w n j - w n i) = 1 := fun g => by
      have e := h g
      rw [hbar.1, hbar.1, ← om_map F φ, mul_comm (Φ i j), ← mul_assoc, ← map_mul] at e
      have e2 := φ.injective (mul_right_cancel₀ hne e)
      rw [← Units.val_mul, Units.val_inj] at e2
      rw [_root_.zpow_sub, ← mul_assoc, ← e2, mul_inv_cancel]
    rcases w_cases hn i j with h3 | h3 | ⟨h3, rfl⟩
    · obtain ⟨g, hg⟩ := ok.f2a
      exact hg (by simpa [h3] using h2 g)
    · obtain ⟨g, hg⟩ := ok.f2b _ h3
      exact hg (h2 g)
    · obtain ⟨g, hg⟩ := ok.f2c _ h3
      apply hg
      rcases Int.units_eq_one_or (F.del g) with hd | hd
      · rw [h2 ⟨g, hd⟩, one_mul]
        simp [Frame.delK, hd]
      · have hm : g * F.c ∈ F.del.ker := by rw [MonoidHom.mem_ker, map_mul, hd, ok.del_c]; rfl
        have e := h2 ⟨_, hm⟩
        have ec : F.om k F.c = -1 := by
          apply Units.ext
          apply φ.injective
          rw [om_map]
          have := hc i
          rw [← neg_one_mul] at this
          rw [← mul_right_cancel₀ hne this]
          simp
        have ed : F.delK k g = -1 := by
          apply Units.ext
          simp [Frame.delK, hd]
        simp only [map_mul, ec, ok.Ψ_c, mul_one] at e
        rw [ed, mul_right_comm, e]
  have hz : ∀ i j, Φ i j = 0 := by
    rcases htri with ht | ht
    · exact tri_zero (ι := (Fin n)ᵒᵈ) (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ
        (fun g i j hij => ht g j i hij) h1 key
    · exact tri_zero (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ ht h1 key
  ext1 X
  simp [hsum, hz]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDualb
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_dualb :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Ideal C) (κ : Type) [Fintype κ] (ε : κ → C), maximalIdeal C * K = ⊥ → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) → ∃ co : κ → K →ₗ[O] ResidueField O, ∀ y : K, ∃ a : κ → O, (∀ u, residue O (a u) = co u y) ∧ (y : C) = ∑ u, a u • ε u := by
  intro O _ _ C _ _ _ K κ _ ε hK hspan hind
  have hε : ∀ u, ε u ∈ K := fun u => by
    rw [hspan]; exact Ideal.subset_span ⟨u, rfl⟩
  have hex : ∀ y : K, ∃ a : κ → O, (y : C) = ∑ u, a u • ε u := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span (Set.range ε) := hspan ▸ hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy'
    choose a ha using fun u => IsCO.res_surj (O := O) (c u)
    refine ⟨a, ?_⟩
    show y = _
    rw [← hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h0 : (c u - algebraMap O C (a u)) * ε u ∈ maximalIdeal C * K :=
      Ideal.mul_mem_mul (ha u) (hε u)
    rw [hK, Ideal.mem_bot, sub_mul, sub_eq_zero] at h0
    rw [h0, Algebra.smul_def]
  have huniq : ∀ a b : κ → O, ∑ u, a u • ε u = ∑ u, b u • ε u →
      ∀ u, residue O (a u) = residue O (b u) := by
    intro a b hab u
    have h := hind (fun u => a u - b u) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hab, sub_self]) u
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h
  choose a ha using hex
  refine ⟨fun u =>
    { toFun := fun y => residue O (a y u)
      map_add' := fun x y => ?_
      map_smul' := fun c x => ?_ }, fun y => ⟨a y, fun u => rfl, ha y⟩⟩
  · rw [← map_add (f := _)]
    refine huniq (a (x + y)) (fun u => a x u + a y u) ?_ u
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, ← ha, ← ha]
    rfl
  · have h := huniq (a (c • x)) (fun u => c * a x u) (by
      simp only [mul_smul, ← Finset.smul_sum]
      rw [← ha, ← ha]
      rfl) u
    rw [h, RingHom.id_apply, map_mul, Algebra.smul_def]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrGood
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem two_ne {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (h : l ≠ 2) : (2 : k) ≠ 0 := by
  intro h2
  have h3 : ((2 : ℕ) : k) = 0 := by simpa using h2
  rw [CharP.cast_eq_zero_iff k l] at h3
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)

private theorem sq_facts {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) :
    (t : k) ≠ (t : k)⁻¹ ∧ (t : k) ≠ 1 ∧ (t : k)⁻¹ ≠ 1 := by
  have h0 : (t : k) ≠ 0 := t.ne_zero
  have h1 : (t : k) ≠ 1 := fun e => h (by ext; simp [e])
  refine ⟨fun e => h ?_, h1, fun e => h1 (inv_eq_one.1 e)⟩
  ext
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
  nth_rewrite 2 [e]
  exact mul_inv_cancel₀ h0

private theorem pow_inj {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (i j : Fin n) (hij : i ≠ j) : ((t ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) := by
  obtain ⟨a, b, c⟩ := sq_facts h
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, a, b, c, a.symm, b.symm, c.symm]

private theorem diff_inj {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (i j : Fin n) (hij : i ≠ j) :
    ((t ^ w n i : kˣ) : k) - ((t⁻¹ ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) - ((t⁻¹ ^ w n j : kˣ) : k) := by
  obtain ⟨a, -, -⟩ := sq_facts h
  have b : (t : k) - (t : k)⁻¹ ≠ 0 := sub_ne_zero.2 a
  have c : (t : k)⁻¹ - (t : k) ≠ 0 := sub_ne_zero.2 a.symm
  have d : (t : k) - (t : k)⁻¹ ≠ (t : k)⁻¹ - (t : k) := fun e =>
    mul_ne_zero h2 b (by linear_combination e)
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, b, c, d, b.symm, c.symm, d.symm]

theorem UpperTheory.V.Fr.pr_good :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] (φ : k →+* K) (ρ : NRep F n K), ρ.IsBar φ → ρ.Good ∧ lieT K n ≠ 0 ∧ thetaLie (lieT K n) = lieT K n := by
  intro l _ k _ _ F C₀ n hF hn K _ φ ρ hρ
  have h2 : (2 : k) ≠ 0 := two_ne hF.l_odd
  have hs : F.Ψ (F.star F.g0) = (F.Ψ F.g0)⁻¹ := by
    have e : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  refine ⟨⟨?_, fun i j hij => ?_, fun v => ?_⟩, ?_, ?_⟩
  · have := (map_ne_zero φ).2 h2
    rwa [map_ofNat] at this
  · rw [Matrix.sub_apply, Matrix.sub_apply, hρ.1, hρ.1, hρ.1, hρ.1, hs, ← map_sub, ← map_sub]
    exact fun e => diff_inj h2 hF.baseSubgroup_spec hn i j hij (φ.injective e)
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij e => pow_inj hs hn i j hij (φ.injective ?_)⟩
    rw [← hρ.2, ← hρ.2, e]
  · intro e
    rcases hn with rfl | rfl
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
  · rcases hn with rfl | rfl
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_two, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrMu
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_mu :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (K : Ideal C') (q : C' →ₐ[O] C'') (u : K →ₗ[O] ResidueField O), maximalIdeal C' * K = ⊥ → K ≤ maximalIdeal C' → Function.Surjective q → (∀ y : K, u y = 0 → q y = 0) → ∃ μ : ResidueField O →+ C'', IsSq O μ ∧ (∀ y : K, μ (u y) = q y) ∧ ∀ c, ∃ y : K, μ c = q y := by
  intro O _ _ C' _ _ _ C'' _ _ _ K q u hmK hKm hq hker
  classical
  have hwd : ∀ y y' : K, u y = u y' → q y = q y' := by
    intro y y' h
    have h0 : u (y - y') = 0 := by rw [map_sub, h, sub_self]
    have h1 := hker _ h0
    rw [Submodule.coe_sub, map_sub, sub_eq_zero] at h1
    exact h1
  have hmem : ∀ y : K, q y ∈ maximalIdeal C'' := by
    intro y
    rw [← res_eq_zero_iff O C'', res_map, res_eq_zero_iff]
    exact hKm y.2
  by_cases hu : ∀ y, u y = 0
  · refine ⟨0, ⟨fun a c => by simp, fun c => by simp⟩, fun y => ?_, fun c => ⟨0, by simp⟩⟩
    show (0 : C'') = q y
    exact (hker y (hu y)).symm
  · push_neg at hu
    obtain ⟨y0, hy0⟩ := hu
    have hsurj : Function.Surjective u := by
      intro c
      obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (c * (u y0)⁻¹)
      refine ⟨o • y0, ?_⟩
      rw [map_smul, Algebra.smul_def]
      show residue O o * u y0 = c
      rw [ho, mul_assoc, inv_mul_cancel₀ hy0, mul_one]
    let s := Function.surjInv hsurj
    have hs : ∀ c, u (s c) = c := Function.surjInv_eq hsurj
    let μ : ResidueField O →+ C'' :=
      { toFun := fun c => q (s c)
        map_zero' := by
          show q (s 0 : C') = 0
          rw [hwd (s 0) 0 (by rw [hs, map_zero])]
          simp
        map_add' := by
          intro c d
          show q (s (c + d) : C') = q (s c : C') + q (s d : C')
          rw [hwd (s (c + d)) (s c + s d) (by rw [hs, map_add (f := _), hs, hs]), Submodule.coe_add, map_add (f := _)] }
    have hμ : ∀ c, μ c = q (s c) := fun c => rfl
    refine ⟨μ, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro a c
      obtain ⟨b, rfl⟩ := hq a
      obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) b
      have hby : b * (s c : C') = o • (s c : C') := by
        have hz : (b - algebraMap O C' o) * (s c : C') = 0 := by
          have hin : (b - algebraMap O C' o) * (s c : C') ∈ maximalIdeal C' * K :=
            Ideal.mul_mem_mul ho (s c).2
          rw [hmK] at hin
          simpa using hin
        rw [Algebra.smul_def]
        linear_combination hz
      have hres : res O C' b = algebraMap O (ResidueField O) o := by
        rw [← AlgHom.commutes (res O C') o, ← sub_eq_zero, ← map_sub, res_eq_zero_iff]
        exact ho
      have hw := hwd (s (res O C'' (q b) * c)) (o • s c)
        (by rw [hs, res_map, hres, map_smul, hs, Algebra.smul_def])
      rw [hμ, hμ, hw, Submodule.coe_smul_of_tower, ← hby, map_mul]
    · intro c
      rw [hμ]
      exact hmem _
    · intro y
      rw [hμ]
      exact hwd _ _ (hs _)
    · intro c
      exact ⟨s c, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrNorm1
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_norm1 :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] (p : C' →ₐ[O] C) (n : ℕ) (x : GG (m := n) (R := C')), maximalIdeal C' * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal C' → (2 : ResidueField O) ≠ 0 → x * x = 1 → x.right = -1 → x.mat.map p = 1 → ∃ h : GL (Fin n) C', (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ (GG.ofGL h * x * (GG.ofGL h)⁻¹).mat = 1 := by
  intro O _ _ C' _ _ _ C _ _ p n x hmI hle h2R hxx hr hmap
  have hgt : x.left * theta x.left = 1 := by
    have hl := congrArg SemidirectProduct.left hxx
    simpa [SemidirectProduct.mul_left, hr] using hl
  have hθ : ∀ u : GL (Fin n) C', ((theta u⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
      Jmat (R := C') n * (u : Matrix (Fin n) (Fin n) C')ᵀ * Jmat (R := C') n := by
    intro u
    rw [show theta u⁻¹ = (theta u)⁻¹ from map_inv (thetaAut (m := n) (R := C')) u, theta_inv_val]
  have hgg : (x.left : Matrix (Fin n) (Fin n) C') =
      Jmat (R := C') n * (x.left : Matrix (Fin n) (Fin n) C')ᵀ * Jmat (R := C') n := by
    have h1 : (theta x.left)⁻¹ = x.left := inv_eq_of_mul_eq_one_left hgt
    rw [← theta_inv_val x.left, h1]
  have hsq : ∀ a b : C', a ∈ RingHom.ker p → b ∈ RingHom.ker p → a * b = 0 := by
    intro a b ha hb
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker p := Ideal.mul_mem_mul (hle ha) hb
    rw [hmI] at hab
    exact (Ideal.mem_bot).mp hab
  have hp1 : ∀ i j : Fin n,
      p ((1 : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j := by
    intro i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  set X : Matrix (Fin n) (Fin n) C' := (x.left : Matrix (Fin n) (Fin n) C') - 1 with hXdef
  have hX : ∀ i j, X i j ∈ RingHom.ker p := by
    intro i j
    have hgij : p ((x.left : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j :=
      congrFun (congrFun hmap i) j
    rw [RingHom.mem_ker, hXdef, Matrix.sub_apply, map_sub, hp1, hgij, sub_self]
  have hXX : X * X = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => hsq _ _ (hX i k) (hX k j)
  have hXJ : Jmat (R := C') n * Xᵀ * Jmat (R := C') n = X := by
    rw [hXdef, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Jmat_mul_Jmat, ← hgg]
  have hO : IsUnit (2 : O) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_ofNat]
    exact h2R
  have h2 : IsUnit (2 : C') := by
    have h2' := hO.map (algebraMap O C')
    rwa [map_ofNat] at h2'
  have hc2 : (↑h2.unit⁻¹ : C') * 2 = 1 := h2.val_inv_mul
  set Y : Matrix (Fin n) (Fin n) C' := (↑h2.unit⁻¹ : C') • X with hYdef
  have hYX : Y * X = 0 := by rw [hYdef, Matrix.smul_mul, hXX, smul_zero]
  have hXY : X * Y = 0 := by rw [hYdef, Matrix.mul_smul, hXX, smul_zero]
  have hYY : Y * Y = 0 := by rw [hYdef, Matrix.mul_smul, hYX, smul_zero]
  have hY2 : Y + Y = X := by rw [hYdef, ← add_smul, ← mul_two, hc2, one_smul]
  have e1 : (1 - Y) * (1 + Y) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hYY, add_zero, add_sub_cancel_right]
  have e2 : (1 + Y) * (1 - Y) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hYY, sub_zero, sub_add_cancel]
  have hpY : ∀ i j, p (Y i j) = 0 := by
    intro i j
    rw [hYdef, Matrix.smul_apply, smul_eq_mul, map_mul, (RingHom.mem_ker).mp (hX i j), mul_zero]
  obtain ⟨U, hU⟩ : ∃ U : GL (Fin n) C', (U : Matrix (Fin n) (Fin n) C') = 1 - Y :=
    ⟨⟨1 - Y, 1 + Y, e1, e2⟩, rfl⟩
  have hJ : Jmat (R := C') n * (1 - Y)ᵀ * Jmat (R := C') n = 1 - Y := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Jmat_mul_Jmat, hYdef, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, hXJ]
  have hg1 : (x.left : Matrix (Fin n) (Fin n) C') = 1 + X := by rw [hXdef, add_sub_cancel]
  have key : (1 - Y) * (1 + X) * (1 - Y) =
      1 + X - (Y + Y) - Y * X - X * Y + Y * Y + Y * X * Y := by noncomm_ring
  refine ⟨U, ?_, ?_⟩
  · ext i j
    show p ((U : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j
    rw [hU, Matrix.sub_apply, map_sub, hp1, hpY, sub_zero]
  · simp [GG.mat, SemidirectProduct.mul_left, hr]
    rw [hθ, hU, hJ, hg1, key, hYX, hXY, hYY, hY2, zero_mul]
    simp
end

