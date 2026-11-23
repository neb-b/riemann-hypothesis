module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqNsmulOfForallAddChar
section
set_option autoImplicit false

namespace GlobalTheory

namespace ConjIdeal

theorem exists_eq_nsmul_of_forall_zmod {X : Type*} [AddCommGroup X] [Module.Free ℤ X] (M : ℕ) (v : X)
    (h : ∀ t : X →+ ZMod M, t v = 0) : ∃ z : X, v = M • z := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hd : ∀ i, (M : ℤ) ∣ b.repr v i := fun i => by
    have := h ((Int.castAddHom (ZMod M)).comp (b.coord i).toAddMonoidHom)
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
  refine ⟨b.repr.symm ((b.repr v).mapRange (fun n => n / (M : ℤ)) (by simp)), ?_⟩
  apply b.repr.injective
  ext i
  simp [Int.mul_ediv_cancel' (hd i)]

theorem exists_eq_nsmul_of_forall_addChar {X : Type*} [AddCommGroup X] [Module.Free ℤ X] {M : ℕ}
    (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C} (hζ : IsPrimitiveRoot ζ M) (v : X)
    (h : ∀ t : AddChar X C, (∀ x, t x ^ M = 1) → t v = 1) : ∃ z : X, v = M • z := by
  haveI : NeZero M := ⟨hM⟩
  refine exists_eq_nsmul_of_forall_zmod M v fun t => ?_
  have h1 := h ((AddChar.zmodChar M hζ.pow_eq_one).compAddMonoidHom t) fun x => by
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  rw [AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply, hζ.pow_eq_one_iff_dvd] at h1
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)

variable {O : Type*} [CommRing O]

theorem dvd_of_dvd_conj (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, bar x • d y = M • z) (y : X) : ∃ z : Y, d y = M • z := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
  obtain ⟨z₁, hz₁⟩ := h₁ j hj y
  obtain ⟨z₂, hz₂⟩ := h₂ (bar i) (Ideal.mem_map_of_mem bar hi) y
  rw [hbar] at hz₂
  refine ⟨z₂ + z₁, ?_⟩
  rw [smul_add, ← hz₁, ← hz₂, map_smul, ← add_smul, hij, one_smul]

theorem dvd_of_addChar (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) {M : ℕ} (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C}
    (hζ : IsPrimitiveRoot ζ M) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ t : AddChar Y C, (∀ v, t v ^ M = 1) → ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 1) (y : X) :
    ∃ z : Y, d y = M • z :=
  dvd_of_dvd_conj bar hbar I hsup M d h₁
    (fun x hx y => exists_eq_nsmul_of_forall_addChar hM hζ _ fun t ht => h₂ t ht x hx y) y

theorem trans_symm_congr_one (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) {M : ℕ} (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C}
    (hζ : IsPrimitiveRoot ζ M) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ X] (e₁ e₂ : X ≃ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, e₂ (x • y) = e₁ (x • y) + M • z)
    (h₂ : ∀ t : AddChar X C, (∀ v, t v ^ M = 1) → ∀ x ∈ I.map bar, ∀ χ : Y,
      t (bar x • e₁.symm χ) = t (bar x • e₂.symm χ)) (y : X) :
    ∃ z : X, e₁.trans e₂.symm y = y + M • z := by
  obtain ⟨z, hz⟩ := dvd_of_addChar bar hbar I hsup hM hζ
    ((e₁.trans e₂.symm).toLinearMap - LinearMap.id) (fun x hx y => by
      obtain ⟨z, hz⟩ := h₁ x hx y
      refine ⟨-e₂.symm z, ?_⟩
      have h : e₁ (x • y) = e₂ (x • y) - M • z := by rw [hz]; abel
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.id_apply]
      rw [h, map_sub, map_nsmul, e₂.symm_apply_apply, smul_neg]
      abel) (fun t ht x hx y => by
      have h := h₂ t ht x hx (e₁ y)
      rw [e₁.symm_apply_apply] at h
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.id_apply]
      rw [smul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← h, ← AddChar.map_add_eq_mul,
        add_neg_cancel, AddChar.map_zero_eq_one]) y
  refine ⟨z, ?_⟩
  rw [← hz]
  simp

theorem fix_torsion_of_fix_conj (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {G A : Type*} [CommGroup G] [CommGroup A]
    (act : O → G →* G) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (e : G → G → A)
    (e_mul : ∀ x x' y, x ^ M = 1 → x' ^ M = 1 → y ^ M = 1 → e (x * x') y = e x y * e x' y)
    (e_nondeg : ∀ x, x ^ M = 1 → (∀ y, y ^ M = 1 → e x y = 1) → x = 1)
    (e_adj : ∀ a x y, x ^ M = 1 → y ^ M = 1 → e (act a x) y = e x (act (bar a) y))
    (θ : G →* G) (θ_act : ∀ a x, x ^ M = 1 → θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y, x ^ M = 1 → y ^ M = 1 → e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, y ^ M = 1 → θ (act a y) = act a y)
    (x : G) (hx : x ^ M = 1) : θ x = x := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
  have tors : ∀ (f : G →* G) y, y ^ M = 1 → f y ^ M = 1 := fun f y hy => by
    rw [← map_pow, hy, map_one]
  have act_zero : ∀ y, act 0 y = 1 := fun y => by
    have := act_add 0 0 y
    rw [add_zero] at this
    exact left_eq_mul.mp this
  have act_nat : ∀ (n : ℕ) y, act (n : O) y = y ^ n := fun n y => by
    induction n with
    | zero => simpa using act_zero y
    | succ n ih => rw [Nat.cast_succ, act_add, ih, act_one, pow_succ]
  have e_one : ∀ y, y ^ M = 1 → e 1 y = 1 := fun y hy => by
    have := e_mul 1 1 y (one_pow _) (one_pow _) hy
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have e_one' : ∀ y, y ^ M = 1 → e y 1 = 1 := fun y hy => by
    have := e_adj 0 y 1 hy (one_pow _)
    rw [act_zero, map_one, e_one 1 (one_pow _)] at this
    exact this.symm
  have split : ∀ w y, w ^ M = 1 → y ^ M = 1 → e w y = e w (act i y) * e w (act j y) := fun w y hw hy => by
    have h1 : w = act (bar.symm i) w * act (bar.symm j) w := by
      rw [← act_add, ← map_add (f := _), hij, map_one, act_one]
    conv_lhs => rw [h1]
    rw [e_mul _ _ _ (tors _ _ hw) (tors _ _ hw) hy, e_adj _ _ _ hw hy, e_adj _ _ _ hw hy,
      bar.apply_symm_apply, bar.apply_symm_apply]
  have hm : (θ x * x⁻¹) ^ M = 1 := by rw [mul_pow, tors θ x hx, inv_pow, hx, inv_one, mul_one]
  have hu : act i x ^ M = 1 := tors _ _ hx
  have hw : θ (act i x) = act i (θ x * x⁻¹) * act i x := by
    rw [← map_mul, θ_act _ _ hx, inv_mul_cancel_right]
  have key : act i (θ x * x⁻¹) = 1 := by
    refine e_nondeg _ (tors _ _ hm) fun y hy => ?_
    rw [split _ _ (tors _ _ hm) hy]
    have hA : e (act i (θ x * x⁻¹)) (act i y) = 1 := by
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
        (hIJ (Ideal.mul_mem_mul hi (Ideal.mem_map_of_mem bar hi)))
      rw [e_adj _ _ _ hm (tors _ _ hy), ← act_mul, mul_comm (bar i), ← hc, act_mul, act_nat, hy,
        map_one, e_one' _ hm]
    have hB : e (act i (θ x * x⁻¹)) (act j y) = 1 := by
      have hv : act j y ^ M = 1 := tors _ _ hy
      have h := θ_iso _ _ hu hv
      rw [θ_fix j hj y hy, hw, e_mul _ _ _ (tors _ _ hm) hu hv] at h
      exact mul_eq_right.mp h
    rw [hA, hB, mul_one]
  have hx' : x = act i x * act j x := by rw [← act_add, hij, act_one]
  conv_lhs => rw [hx']
  rw [map_mul, hw, key, one_mul, θ_fix j hj x hx, ← hx']

theorem fix_torsion_of_fix_conj_rel (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {G A : Type*} [CommGroup G] [CommGroup A]
    (act : O → G →* G) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (R : G → G → A → Prop)
    (R_ex : ∀ x y, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (R_mul : ∀ x x' y c c', x ^ M = 1 → x' ^ M = 1 → y ^ M = 1 → R x y c → R x' y c' →
      R (x * x') y (c * c'))
    (R_nondeg : ∀ x, x ^ M = 1 → (∀ y, y ^ M = 1 → R x y 1) → x = 1)
    (R_adj : ∀ a x y c, x ^ M = 1 → y ^ M = 1 → R x (act (bar a) y) c → R (act a x) y c)
    (θ : G →* G) (θ_act : ∀ a x, x ^ M = 1 → θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y c, x ^ M = 1 → y ^ M = 1 → R x y c → R (θ x) (θ y) c)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, y ^ M = 1 → θ (act a y) = act a y)
    (x : G) (hx : x ^ M = 1) : θ x = x := by
  classical
  have tors : ∀ (f : G →* G) y, y ^ M = 1 → f y ^ M = 1 := fun f y hy => by
    rw [← map_pow, hy, map_one]
  let e : G → G → A := fun x y => if h : ∃ c, R x y c then h.choose else 1
  have he : ∀ x y, x ^ M = 1 → y ^ M = 1 → R x y (e x y) := fun x y hx hy => by
    have h : ∃ c, R x y c := (R_ex x y hx hy).exists
    simp only [e, dif_pos h]
    exact h.choose_spec
  have hu : ∀ x y c, x ^ M = 1 → y ^ M = 1 → R x y c → e x y = c := fun x y c hx hy h =>
    (R_ex x y hx hy).unique (he x y hx hy) h
  refine fix_torsion_of_fix_conj bar I hsup M hIJ act act_one act_add act_mul e ?_ ?_ ?_ θ θ_act ?_
    θ_fix x hx
  · intro x x' y hx hx' hy
    exact hu _ _ _ (by rw [mul_pow, hx, hx', mul_one]) hy
      (R_mul _ _ _ _ _ hx hx' hy (he _ _ hx hy) (he _ _ hx' hy))
  · intro x hx h
    exact R_nondeg x hx fun y hy => h y hy ▸ he x y hx hy
  · intro a x y hx hy
    exact hu _ _ _ (tors _ _ hx) hy (R_adj _ _ _ _ hx hy (he _ _ hx (tors _ _ hy)))
  · intro x y hx hy
    exact hu _ _ _ (tors _ _ hx) (tors _ _ hy) (θ_iso _ _ _ hx hy (he _ _ hx hy))

end ConjIdeal

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemSpanSingleInlIff
section
namespace GlobalTheory.SpanSingleInlMembership

theorem mem_span_single_inl_iff {g : ℕ} (S : Finset (Fin g)) (u : Fin g ⊕ Fin g → ℤ) :
    u ∈ Submodule.span ℤ ((fun (k : Fin g) ↦ Pi.single (Sum.inl k) (1 : ℤ)) '' (↑S : Set (Fin g))) ↔
      (∀ (k : Fin g), u (Sum.inr k) = (0 : ℤ)) ∧ ∀ k ∉ S, u (Sum.inl k) = (0 : ℤ) := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨fun k => by simp, fun k hk => ?_⟩
      have hne : k ≠ j := fun e => hk (e ▸ hj)
      simp [hne]
    | zero => simp
    | add x y _ _ hx hy =>
      exact ⟨fun k => by simp [hx.1 k, hy.1 k], fun k hk => by simp [hx.2 k hk, hy.2 k hk]⟩
    | smul a x _ hx =>
      exact ⟨fun k => by simp [hx.1 k], fun k hk => by simp [hx.2 k hk]⟩
  · rintro ⟨h1, h2⟩
    have hu : u = ∑ k ∈ S, u (Sum.inl k) • (Pi.single (Sum.inl k) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) := by
      funext i
      rcases i with j | j
      · by_cases hj : j ∈ S
        · simp [Finset.sum_apply, Pi.single_apply, hj]
        · simp [Finset.sum_apply, Pi.single_apply, hj, h2 j hj]
      · simp [Finset.sum_apply, h1 j]
    rw [hu]
    exact Submodule.sum_mem _ fun k hk =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.SpanSingleInlMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SummableExpNegSumAbs
section
namespace GlobalTheory.SummableExpNegAbsSum

theorem summable_int : Summable fun n : ℤ ↦ Real.exp (-|(n : ℝ)|) := by
  have h : Summable fun n : ℕ ↦ Real.exp (-(n : ℝ)) := Real.summable_exp_neg_nat
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h

theorem summable_exp_neg_sum_abs {ι : Type} [inst : Fintype ι] :
    Summable fun (m : ι → ℤ) ↦ Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) := by
  classical
  set g : ℤ → ℝ := fun n ↦ Real.exp (-|(n : ℝ)|) with hg
  have hgpos : ∀ n, 0 ≤ g n := fun n => (Real.exp_pos _).le
  have hgs : Summable g := summable_int
  have hprod : ∀ m : ι → ℤ, Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) = ∏ i : ι, g (m i) := by
    intro m
    simp only [hg]
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  simp_rw [hprod]
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' n : ℤ, g n)
    (fun m => Finset.prod_nonneg fun i _ => hgpos _) fun s => ?_
  set T : ι → Finset ℤ := fun i => s.image (fun m : ι → ℤ => m i) with hT
  have hsub : s ⊆ Fintype.piFinset T := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hm
  calc ∑ m ∈ s, ∏ i : ι, g (m i)
      ≤ ∑ m ∈ Fintype.piFinset T, ∏ i : ι, g (m i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          Finset.prod_nonneg fun i _ => hgpos _
    _ = ∏ i : ι, ∑ n ∈ T i, g n := (Finset.prod_univ_sum T (fun _ n => g n)).symm
    _ ≤ ∏ _i : ι, ∑' n : ℤ, g n := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => hgpos _)
          fun i _ => ?_
        exact hgs.sum_le_tsum _ fun _ _ => hgpos _

end GlobalTheory.SummableExpNegAbsSum
end

