module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.InfPowBot
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)
  refine ⟨k + 1, fun x hxI hxm => ?_⟩
  have hx : x ∈ maximalIdeal R ^ (k + 1) • (⊤ : Submodule R R) ⊓ (I : Submodule R R) := by
    refine ⟨?_, hxI⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hxm
  rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
  have hle : maximalIdeal R • (maximalIdeal R ^ k • (⊤ : Submodule R R) ⊓ (I : Submodule R R))
      ≤ maximalIdeal R • (I : Submodule R R) :=
    Submodule.smul_mono le_rfl inf_le_right
  have hx' := hle hx
  rw [Ideal.smul_eq_mul, h] at hx'
  exact (Submodule.mem_bot R).1 hx'

theorem UpperTheory.V.Fr.pr_sec :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C), Function.Surjective p → maximalIdeal C' * RingHom.ker p = ⊥ → ∀ (Γ : Type) [TopologicalSpace Γ] (x : Γ → C), AdicCont (maximalIdeal C) x → ∃ y : Γ → C', AdicCont (maximalIdeal C') y ∧ ∀ g, p (y g) = x g := by
  intro O _ _ C' _ _ _ C _ _ _ p hp hker Γ _ x hx
  have hmem : ∀ z : C', p z ∈ maximalIdeal C ↔ z ∈ maximalIdeal C' := by
    intro z
    rw [← res_eq_zero_iff O C, ← res_eq_zero_iff O C', res_map]
  have hmap : Ideal.map p (maximalIdeal C') = maximalIdeal C := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (hmem z).2 hz
    · intro c hc
      obtain ⟨z, rfl⟩ := hp c
      exact Ideal.mem_map_of_mem p ((hmem z).1 hc)
  have hpow : ∀ n : ℕ, ∀ c ∈ maximalIdeal C ^ n, ∃ z ∈ maximalIdeal C' ^ n, p z = c := by
    intro n c hc
    rw [← hmap, ← Ideal.map_pow] at hc
    exact (Ideal.mem_map_iff_of_surjective p hp).1 hc
  haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O
  obtain ⟨N₀, hN₀⟩ := inf_pow_bot C' (RingHom.ker p) hker
  have hq : Function.Surjective (fun z : C' => Ideal.Quotient.mk (maximalIdeal C ^ N₀) (p z)) :=
    Ideal.Quotient.mk_surjective.comp hp
  let σ := Function.surjInv hq
  have hσ : ∀ c : C, c - p (σ (Ideal.Quotient.mk _ c)) ∈ maximalIdeal C ^ N₀ := by
    intro c
    apply Ideal.Quotient.eq.1
    exact (Function.surjInv_eq hq (Ideal.Quotient.mk _ c)).symm
  have hw : ∀ c : C, ∃ w ∈ maximalIdeal C' ^ N₀, p w = c - p (σ (Ideal.Quotient.mk _ c)) :=
    fun c => hpow N₀ _ (hσ c)
  choose w hwm hwp using hw
  let s : C → C' := fun c => σ (Ideal.Quotient.mk (maximalIdeal C ^ N₀) c) + w c
  have hs : ∀ c, p (s c) = c := by
    intro c
    simp only [s, map_add (f := _), hwp]
    ring
  have hsd : ∀ n ≥ N₀, ∀ c₁ c₂ : C, c₁ - c₂ ∈ maximalIdeal C ^ n →
      s c₁ - s c₂ ∈ maximalIdeal C' ^ n := by
    intro n hn c₁ c₂ h
    have hcl : Ideal.Quotient.mk (maximalIdeal C ^ N₀) c₁ = Ideal.Quotient.mk _ c₂ :=
      Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right hn h)
    obtain ⟨z, hz, hpz⟩ := hpow n _ h
    have hdiff : s c₁ - s c₂ = w c₁ - w c₂ := by
      simp only [s, hcl]
      ring
    have hz0 : (s c₁ - s c₂) - z = 0 := by
      apply hN₀
      · rw [RingHom.mem_ker]
        simp [map_sub, hs, hpz]
      · rw [hdiff]
        exact sub_mem (sub_mem (hwm c₁) (hwm c₂)) (Ideal.pow_le_pow_right hn hz)
    rw [sub_eq_zero.1 hz0]
    exact hz
  refine ⟨fun g => s (x g), ?_, fun g => hs (x g)⟩
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hxl := (IsLocallyConstant.iff_eventually_eq _).1 (hx (max n N₀)) g
  filter_upwards [hxl] with g' hg'
  apply Ideal.Quotient.eq.2
  exact Ideal.pow_le_pow_right (le_max_left n N₀)
    (hsd _ (le_max_right _ _) _ _ (Ideal.Quotient.eq.1 hg'))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.JconjApply
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem jconj_apply {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Jmat (R := R) n * Mᵀ * Jmat (R := R) n) i j = M j.rev i.rev := by
  have h1 : ∀ k, (Jmat (R := R) n * Mᵀ) i k = M k i.rev := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
    · simp [Jmat]
    · intro b _ hb
      simp [Jmat, hb]
    · simp
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · rw [h1]
    simp [Jmat]
  · intro b _ hb
    have : j ≠ b.rev := by
      intro h
      apply hb
      rw [h, Fin.rev_rev]
    simp [Jmat, this]
  · simp

theorem UpperTheory.V.Fr.pr_norm2 :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] (p : C' →ₐ[O] C) (n : ℕ) (Z : Matrix (Fin n) (Fin n) C'), maximalIdeal C' * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal C' → thetaLie Z = Z → (∀ i j, i ≠ j → p (Z i j) = 0) → (∀ i j, i ≠ j → res O C' (Z i i) ≠ res O C' (Z j j)) → ∃ h : GL (Fin n) C', (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ theta h = h ∧ ∀ i j, i ≠ j → ((h : Matrix (Fin n) (Fin n) C') * Z * ((h⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C')) i j = 0 := by
  intro O _ _ C' _ _ _ C _ _ p n Z hmI hIm hZ hoff hdiag
  classical
  have hII : ∀ a b : C', a ∈ RingHom.ker p → b ∈ RingHom.ker p → a * b = 0 := by
    intro a b ha hb
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker p := Ideal.mul_mem_mul (hIm ha) hb
    rw [hmI] at hab
    simpa using hab
  have hZI : ∀ i j, i ≠ j → Z i j ∈ RingHom.ker p := by
    intro i j hij
    rw [RingHom.mem_ker]
    exact hoff i j hij
  have hunit : ∀ i j, i ≠ j → IsUnit (Z i i - Z j j) := by
    intro i j hij
    by_contra hu
    have hm : Z i i - Z j j ∈ maximalIdeal C' := (IsLocalRing.mem_maximalIdeal _).2 hu
    rw [← res_eq_zero_iff O C', map_sub, sub_eq_zero] at hm
    exact hdiag i j hij hm
  have hZr : ∀ i j, Z j.rev i.rev = -Z i j := by
    intro i j
    have hij := congrFun (congrFun hZ i) j
    simp only [thetaLie, Matrix.neg_apply, jconj_apply] at hij
    rw [← hij, neg_neg]
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) C', ∀ i j,
      A i j = if i = j then 0 else Z i j * Ring.inverse (Z i i - Z j j) :=
    ⟨Matrix.of fun i j => if i = j then 0 else Z i j * Ring.inverse (Z i i - Z j j), fun i j => rfl⟩
  have hAI : ∀ i j, A i j ∈ RingHom.ker p := by
    intro i j
    rw [hA]
    split_ifs with h
    · exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (hZI i j h)
  have hAA : A * A = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => hII _ _ (hAI i k) (hAI k j)
  have hAr : ∀ i j, A j.rev i.rev = -A i j := by
    intro i j
    rw [hA, hA]
    by_cases hij : i = j
    · subst hij
      simp
    · have hrev : j.rev ≠ i.rev := fun h => hij (Fin.rev_injective h).symm
      rw [if_neg hrev, if_neg hij, hZr i j, hZr j j, hZr i i]
      have hd : -Z j j - -Z i i = Z i i - Z j j := by ring
      rw [hd]
      ring
  have h1 : (1 + A) * (1 - A) = 1 := by
    rw [show (1 + A) * (1 - A) = 1 - A * A by noncomm_ring, hAA, sub_zero]
  have h2 : (1 - A) * (1 + A) = 1 := by
    rw [show (1 - A) * (1 + A) = 1 - A * A by noncomm_ring, hAA, sub_zero]
  refine ⟨⟨1 + A, 1 - A, h1, h2⟩, ?_, ?_, ?_⟩
  · ext i j
    have h0 : p (A i j) = 0 := by
      have := hAI i j
      rwa [RingHom.mem_ker] at this
    simp only [Units.val_mk, Matrix.map_apply, Matrix.add_apply, map_add (f := _), h0, add_zero,
      Matrix.one_apply]
    split_ifs <;> simp
  · apply Units.ext
    rw [theta_val]
    show Jmat (R := C') n * (1 - A)ᵀ * Jmat (R := C') n = 1 + A
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Jmat_mul_Jmat, sub_eq_add_neg]
    congr 1
    ext i j
    rw [Matrix.neg_apply, jconj_apply, hAr, neg_neg]
  · intro i j hij
    show ((1 + A) * Z * (1 - A)) i j = 0
    rw [show (1 + A) * Z * (1 - A) = Z + A * Z - Z * A - A * Z * A by noncomm_ring]
    have hAZ : (A * Z) i j = A i j * Z j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro k _ hk
        exact hII _ _ (hAI i k) (hZI k j hk)
      · simp
    have hZA : (Z * A) i j = Z i i * A i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · intro k _ hk
        exact hII _ _ (hZI i k (Ne.symm hk)) (hAI k j)
      · simp
    have hAZA : (A * Z * A) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => hII _ _ ?_ (hAI k j)
      rw [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hAI i l)
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.add_apply, hAZ, hZA, hAZA, hA, if_neg hij]
    have hu := Ring.inverse_mul_cancel _ (hunit i j hij)
    linear_combination (-(Z i j)) * hu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section LC

variable {T A C : Type} [TopologicalSpace T] [CommRing A] [CommRing C] {n : ℕ}

private theorem lc_matrix {B : Type} {f : T → Matrix (Fin n) (Fin n) B}
    (h : ∀ a b, IsLocallyConstant fun s => f s a b) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hall : ∀ᶠ y in nhds x, ∀ a b, f y a b = f x a b :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
      (IsLocallyConstant.iff_eventually_eq _).1 (h a b) x
  filter_upwards [hall] with y hy
  ext a b
  exact hy a b

private theorem lc_gl {I : Ideal A} {f : T → GL (Fin n) A} (h : ∀ a b, AdicCont I fun s => f s a b) (N : ℕ) :
    IsLocallyConstant fun s => GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ N)) (f s) := by
  apply IsLocallyConstant.desc _ (fun u : GL (Fin n) (A ⧸ I ^ N) => (u : Matrix (Fin n) (Fin n) (A ⧸ I ^ N)))
  · apply lc_matrix
    intro a b
    simpa [Function.comp_def] using h a b N
  · exact fun u v huv => Units.ext huv

private theorem mem_ker (p : A →+* C) {u : GL (Fin n) A} (h : GeneralLinearGroup.map p u = 1) (i j : Fin n) :
    ((u : Matrix (Fin n) (Fin n) A) - 1) i j ∈ RingHom.ker p := by
  rw [RingHom.mem_ker]
  have he := congrArg (fun v : GL (Fin n) C => (v : Matrix (Fin n) (Fin n) C) i j) h
  simp only [GeneralLinearGroup.map_apply, Units.val_one] at he
  rw [Matrix.sub_apply, map_sub, he, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem lc_ker [IsNoetherianRing A] {I K : Ideal A} (hs : I * K = ⊥) {f : T → GL (Fin n) A}
    (hf : ∀ s a b, ((f s : Matrix (Fin n) (Fin n) A) - 1) a b ∈ K)
    (h : ∀ N, IsLocallyConstant fun s => GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ N)) (f s)) :
    IsLocallyConstant fun s => (f s : Matrix (Fin n) (Fin n) A) - 1 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (K : Submodule A A)
  have h0 : ∀ x ∈ I ^ (k + 1), x ∈ K → x = 0 := by
    intro x hxm hxK
    have hx : x ∈ I ^ (k + 1) • (⊤ : Submodule A A) ⊓ (K : Submodule A A) := by
      refine ⟨?_, hxK⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hxm
    rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
    have hle : I • (I ^ k • (⊤ : Submodule A A) ⊓ (K : Submodule A A)) ≤ I • (K : Submodule A A) :=
      Submodule.smul_mono le_rfl inf_le_right
    have hx' := hle hx
    rw [Ideal.smul_eq_mul, hs] at hx'
    exact (Submodule.mem_bot A).1 hx'
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (h (k + 1)) s] with s' hs'
  ext a b
  have he := congrArg
    (fun v : GL (Fin n) (A ⧸ I ^ (k + 1)) => (v : Matrix (Fin n) (Fin n) (A ⧸ I ^ (k + 1))) a b) hs'
  simp only [GeneralLinearGroup.map_apply] at he
  have hd := Ideal.Quotient.eq.1 he
  have hK : (f s' : Matrix (Fin n) (Fin n) A) a b - (f s : Matrix (Fin n) (Fin n) A) a b ∈ K := by
    have := sub_mem (hf s' a b) (hf s a b)
    simpa [Matrix.sub_apply] using this
  rw [Matrix.sub_apply, Matrix.sub_apply, sub_eq_zero.1 (h0 _ hd hK)]

private theorem map_sgn (f : A →+* C) (s : ℤˣ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (sgnAct n A s g) = sgnAct n C s (GeneralLinearGroup.map f g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp
  · simpa using map_theta f g

private theorem lc_hom {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (φ : G →* H) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : ∀ᶠ z in nhds (1 : G), z ∈ (φ.ker : Set G) := h.mem_nhds (one_mem _)
  have hc : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    have := (continuous_const_mul x⁻¹).tendsto x
    rwa [inv_mul_cancel] at this
  filter_upwards [hc.eventually h1] with y hy
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hy
  exact hy.symm

end LC

theorem UpperTheory.V.Fr.pr_omk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B), maximalIdeal C' * RingHom.ker p = ⊥ → (∀ x i j, D.om x i j ∈ RingHom.ker p) ∧ (∀ v s i j, D.a v s i j ∈ RingHom.ker p) ∧ IsLocallyConstant D.om ∧ ∀ v, IsLocallyConstant (D.a v) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D hker
  have hgrp : ∀ s t, (B.r (s * t)).left = (B.r s).left * sgnAct n C (F.del s) (B.r t).left := by
    intro s t
    rw [map_mul, SemidirectProduct.mul_left, B.nu]
  have hom1 : ∀ x : F.Γ × F.Γ, GeneralLinearGroup.map (p : C' →+* C)
      (D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹) = 1 := by
    intro x
    rw [map_mul, map_mul, map_inv, map_sgn, D.r_map, D.r_map, D.r_map, hgrp, mul_inv_cancel]
  have ha1 : ∀ v s, GeneralLinearGroup.map (p : C' →+* C)
      (D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹) = 1 := by
    intro v s
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, D.r_map, D.g_map, D.t_map]
    group
  haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O
  have hrc : ∀ N, IsLocallyConstant fun s : F.Γ =>
      GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.r s) :=
    fun N => lc_gl (fun a b => D.r_cont a b) N
  have hdel : IsLocallyConstant F.del := lc_hom F.del hF.del_open
  refine ⟨fun x i j => mem_ker _ (hom1 x) i j, fun v s i j => mem_ker _ (ha1 v s) i j, ?_, ?_⟩
  · have := lc_ker hker
      (f := fun x : F.Γ × F.Γ => D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹)
      (fun x a b => mem_ker _ (hom1 x) a b) (by
        intro N
        have e1 := (hrc N).comp_continuous (continuous_fst (X := F.Γ) (Y := F.Γ))
        have e2 := (hrc N).comp_continuous (continuous_snd (X := F.Γ) (Y := F.Γ))
        have e3 := (hrc N).comp_continuous (continuous_mul (M := F.Γ))
        have e4 := hdel.comp_continuous (continuous_fst (X := F.Γ) (Y := F.Γ))
        have := IsLocallyConstant.comp₂
          (IsLocallyConstant.comp₂ e1 (IsLocallyConstant.comp₂ e4 e2
            fun s g => sgnAct n _ s g) (· * ·)) e3 (fun a b => a * b⁻¹)
        convert this using 1
        funext x
        simp [Function.comp, map_sgn])
    exact this
  · intro v
    have hloc : Continuous (F.loc v) := continuous_subtype_val.comp (hF.loc_cont v)
    have := lc_ker hker
      (f := fun s : F.Gv v => D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹)
      (fun s a b => mem_ker _ (ha1 v s) a b) (by
        intro N
        have e1 := (hrc N).comp_continuous hloc
        have e2 := lc_gl (fun a b => D.t_cont v a b) N
        have := IsLocallyConstant.comp₂ e1 e2 (fun a b => a *
          ((GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.g v))⁻¹ * b *
            GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.g v))⁻¹)
        convert this using 1
        funext s
        simp [Function.comp])
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MapThetaLie
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C]
  {K : Ideal C} (u : K →ₗ[O] ResidueField O)

private theorem evk_add {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    evK K u (x + y) = evK K u x + evK K u y := by
  rw [evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.add_mem hx hy), ← map_add (f := _)]
  rfl

private theorem evk_sub {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    evK K u (x - y) = evK K u x - evK K u y := by
  rw [evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.sub_mem hx hy), ← map_sub]
  rfl

private theorem evk_neg {x : C} (hx : x ∈ K) : evK K u (-x) = - evK K u x := by
  rw [evK_of_mem u hx, evK_of_mem u (K.neg_mem hx), ← map_neg]
  rfl

private theorem evk_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i, f i ∈ K) :
    evK K u (∑ i ∈ s, f i) = ∑ i ∈ s, evK K u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, evK_of_mem u K.zero_mem]
    exact map_zero u
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evk_add u (hf a) (K.sum_mem fun i _ => hf i), ih]

private theorem evk_mul [IsCO O C] (hK : maximalIdeal C * K = ⊥) (a : C) {x : C} (hx : x ∈ K) :
    evK K u (a * x) = res O C a * evK K u x := by
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
  have h0 : (a - algebraMap O C b) * x = 0 := by
    have := Ideal.mul_mem_mul hb hx
    rwa [hK, Ideal.mem_bot] at this
  have h1 : res O C a = algebraMap O _ b := by
    have := (res_eq_zero_iff O C _).2 hb
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  rw [evK_of_mem u hx, evK_of_mem u (K.mul_mem_left a hx), h1, ← Algebra.smul_def, ← map_smul]
  congr 1
  apply Subtype.ext
  show a * x = b • x
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, h0]

variable {n : ℕ}

private theorem mem_left {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (A * Z) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_left _ (hZ k j)

private theorem mem_right {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (Z * A) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_right _ (hZ i k)

private theorem map_left [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_left _ (hZ k j)]
  exact Finset.sum_congr rfl fun k _ => evk_mul u hK _ (hZ k j)

private theorem map_right [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_right _ (hZ i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, evk_mul u hK _ (hZ i k), mul_comm]
  rfl

private theorem mem_theta {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K) (i j : Fin n) :
    thetaLie Z i j ∈ K :=
  K.neg_mem (mem_right (mem_left (Z := Zᵀ) (fun i j => hZ j i) _) _ i j)

private theorem map_thetaLie [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) : (thetaLie Z).map (evK K u) = thetaLie (Z.map (evK K u)) := by
  have hT : ∀ i j, Zᵀ i j ∈ K := fun i j => hZ j i
  have hJ : (Jmat C n).map (res O C) = Jmat (ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have e : (Jmat C n * Zᵀ * Jmat C n).map (evK K u) =
      Jmat (ResidueField O) n * (Z.map (evK K u))ᵀ * Jmat (ResidueField O) n := by
    rw [map_right u hK (mem_left hT _), map_left u hK hT, hJ]
    rfl
  unfold thetaLie
  rw [← e]
  ext i j
  exact evk_neg u (mem_right (mem_left hT _) _ i j)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.pr_evk :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (K : Ideal C) (u : K →ₗ[O] ResidueField O), maximalIdeal C * K = ⊥ → K ≤ maximalIdeal C → ∀ Z : Matrix (Fin n) (Fin n) C, (∀ i j, Z i j ∈ K) → (∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 ∧ (Z + Z').map (evK K u) = Z.map (evK K u) + Z'.map (evK K u) ∧ (Z - Z').map (evK K u) = Z.map (evK K u) - Z'.map (evK K u)) ∧ (∀ A : Matrix (Fin n) (Fin n) C, (∀ i j, (A * Z) i j ∈ K ∧ (Z * A) i j ∈ K) ∧ (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) ∧ (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C)) ∧ ∀ x : GG (m := n) (R := C), (∀ i j, x.adFun Z i j ∈ K) ∧ (x.adFun Z).map (evK K u) = (GG.map (res O C : C →+* ResidueField O) x).adFun (Z.map (evK K u)) ∧ ∀ z : GL (Fin n) C, (z : Matrix (Fin n) (Fin n) C) = 1 + Z → (x * GG.ofGL z * x⁻¹).mat = 1 + x.adFun Z := by
  intro O _ _ C _ _ _ n K u hK hKm Z hZ
  have hsq : ∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 := fun Z' hZ' => by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := Ideal.mul_mem_mul (hKm (hZ i k)) (hZ' k j)
    rwa [hK, Ideal.mem_bot] at this
  refine ⟨fun Z' hZ' => ⟨hsq Z' hZ', ?_, ?_⟩,
    fun A => ⟨fun i j => ⟨mem_left hZ A i j, mem_right hZ A i j⟩, map_left u hK hZ A, map_right u hK hZ A⟩,
    fun x => ?_⟩
  · ext i j
    exact evk_add u (hZ i j) (hZ' i j)
  · ext i j
    exact evk_sub u (hZ i j) (hZ' i j)
  have hY : ∀ i j, (if x.right = 1 then Z else thetaLie Z) i j ∈ K := fun i j => by
    split_ifs
    · exact hZ i j
    · exact mem_theta hZ i j
  refine ⟨mem_right (mem_left hY _) _, ?_, fun z hz => ?_⟩
  · have hY' : (if x.right = 1 then Z else thetaLie Z).map (evK K u) =
        if x.right = 1 then Z.map (evK K u) else thetaLie (Z.map (evK K u)) := by
      split_ifs
      · rfl
      · exact map_thetaLie u hK hZ
    unfold GG.adFun
    rw [map_right u hK (mem_left hY _), map_left u hK hY, hY']
    rfl
  · have hinv : ((z⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = 1 - Z := by
      have : (z : Matrix (Fin n) (Fin n) C) * (1 - Z) = 1 := by
        rw [hz, add_mul, mul_sub, mul_sub, hsq Z hZ]
        simp
      exact Units.inv_eq_of_mul_eq_one_right this
    have hl : (x * GG.ofGL z * x⁻¹).left = x.left * sgnAct n C x.right z * x.left⁻¹ := by
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one,
        ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hs : ((sgnAct n C x.right z : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
        1 + (if x.right = 1 then Z else thetaLie Z) := by
      rcases Int.units_eq_one_or x.right with h | h
      · rw [h, sgnAct_one, if_pos rfl, hz]
      · rw [h, sgnAct_neg_one, if_neg (by decide), theta_val, hinv, thetaLie, Matrix.transpose_sub,
          Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat,
          sub_eq_add_neg]
    unfold GG.adFun GG.mat
    rw [hl, Units.val_mul, Units.val_mul, hs, mul_add, add_mul, mul_one, Units.mul_inv]
end

