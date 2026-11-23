module

public import ReciprocityTheory.DualLattices.Bundle0007
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.FourierMapSmulLambdaWeight
section
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

theorem exists_charEquiv [NeZero p] {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    ∃ e : ZMod p ≃ AddChar (ZMod p) C, (∀ h h', e (h + h') = e h * e h') ∧
      ∀ h a, e h a = ζ ^ (h * a).val := by
  have hp1 : ζ ^ p = 1 := hζ.pow_eq_one
  let ψ : AddChar (ZMod p) C := AddChar.zmodChar p hp1
  have hψ : ∀ a, ψ a = ζ ^ a.val := fun a => AddChar.zmodChar_apply hp1 a
  let f : ZMod p → AddChar (ZMod p) C := fun h => ψ.mulShift h
  have hf : ∀ h a, f h a = ζ ^ (h * a).val := fun h a => by
    simp only [f, AddChar.mulShift_apply, hψ]
  have hgen : ∀ (χ : AddChar (ZMod p) C) (a : ZMod p), χ a = χ 1 ^ a.val := by
    intro χ a
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← nsmul_one]
    exact AddChar.map_nsmul_eq_pow χ _ _
  have hinj : Function.Injective f := by
    intro h h' hh
    have := congrArg (fun χ : AddChar (ZMod p) C => χ 1) hh
    simp only [hf, mul_one] at this
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt h) (ZMod.val_lt h') this)
  have hsurj : Function.Surjective f := by
    intro χ
    have h1 : χ 1 ^ p = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self, AddChar.map_zero_eq_one]
    obtain ⟨k, hk, hkχ⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨(k : ZMod p), ?_⟩
    ext a
    rw [hgen χ a, hgen (f k) a, hf, mul_one, ZMod.val_natCast, Nat.mod_eq_of_lt hk, hkχ]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro h h'
    ext a
    show (ψ.mulShift (h + h')) a = ψ.mulShift h a * ψ.mulShift h' a
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, AddChar.mulShift_apply, add_mul,
      AddChar.map_add_eq_mul]
  · intro h a
    exact hf h a

theorem v_gamma (hv : v.Integers R) (hpv : v (p : C) < 1) {ω : ZMod p → C} (hω : IsTeich v ω)
    {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    v (∑ a, u0 ω a * ζ ^ a.val) ^ (p - 1) = v (p : C) := by
  have hpp : 2 ≤ p := hp.out.two_le
  have hζ1 : v ζ ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 := one_lt_pow₀ h (show p ≠ 0 by omega)
    rw [← map_pow, hζ.pow_eq_one, map_one] at h2
    exact lt_irrefl _ h2
  have hπ1 : v (ζ - 1) < 1 := by
    by_contra h
    push_neg at h
    have h2 := one_le_pow₀ (n := p - 1) h
    rw [val_prim_root hζ] at h2
    exact absurd hpv (not_lt.mpr h2)
  have hnat : ∀ n : ℕ, v (n : C) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ]; exact Valuation.map_add_le v ih (by rw [map_one])
  have hdec : ∀ n : ℕ, ∃ s : C, v s ≤ 1 ∧ ζ ^ n - 1 = (ζ - 1) * (n + (ζ - 1) * s) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs1, hs⟩ := ih
      refine ⟨n + ζ * s, Valuation.map_add_le v (hnat n) (by rw [map_mul]; exact mul_le_one' hζ1 hs1), ?_⟩
      push_cast
      linear_combination ζ * hs
  choose s hs1 hs using hdec
  have h1 : ∑ a, u0 ω a * ζ ^ a.val = ∑ a, wt ω a * (ζ ^ a.val - 1) := by
    have := hω.lam_eq (fun a => ζ ^ a.val)
    simpa [lam, ZMod.val_zero] using this
  have h2 : ∑ a, wt ω a * ω a = (p : C) - 1 := by
    have := hω.lam_eq ω
    rw [hω.lam_omega, hω.zero] at this
    simpa using this.symm
  have hγ : ∑ a, u0 ω a * ζ ^ a.val = (ζ - 1) * (((p : C) - 1) +
      (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val)) := by
    rw [h1, ← h2]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hs]
    ring
  have hδ : v (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val) < 1 := by
    apply Valuation.map_add_lt v
    · apply Valuation.map_sum_lt v one_ne_zero
      intro a _
      rw [map_mul]
      calc v (wt ω a) * v ((a.val : C) - ω a) ≤ 1 * v ((a.val : C) - ω a) := by
            gcongr; exact hω.wt_int a
        _ < 1 := by rw [one_mul, Valuation.map_sub_swap]; exact hω.cong a
    · rw [map_mul]
      have hsum : v (∑ a, wt ω a * s a.val) ≤ 1 :=
        Valuation.map_sum_le v fun a _ => by rw [map_mul]; exact mul_le_one' (hω.wt_int a) (hs1 _)
      calc v (ζ - 1) * v (∑ a, wt ω a * s a.val) ≤ v (ζ - 1) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hπ1
  have hp1 : v ((p : C) - 1) = 1 := by
    have hnd : ¬ (p : ℤ) ∣ (p : ℤ) - 1 := by
      intro hd
      have h1' : (p : ℤ) ∣ 1 := by simpa using dvd_sub (dvd_refl (p : ℤ)) hd
      have := Int.eq_one_of_dvd_one (by positivity) h1'
      omega
    have := v_intCast_eq_one hv hpv hnd
    push_cast at this
    exact this
  have hunit : v ((p : C) - 1 + (∑ a, wt ω a * ((a.val : C) - ω a) +
      (ζ - 1) * ∑ a, wt ω a * s a.val)) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left v (by rw [hp1]; exact hδ), hp1]
  rw [hγ, map_mul, hunit, mul_one]
  exact val_prim_root hζ

theorem fourierMap_smul_lambdaWeight {ω : ZMod p → C} (hω : IsTeich v ω) {ζ : C}
    (e : ZMod p ≃ AddChar (ZMod p) C) (he2 : ∀ h a, e h a = ζ ^ (h * a).val) (c : C) :
    fourier (R := R) (fun h a => e h a) (fun a => c * u0 ω a) =
      fun h => (c * ∑ a, u0 ω a * ζ ^ a.val) * ω h := by
  have hω0 : ∀ h : ZMod p, h ≠ 0 → ω h ≠ 0 := by
    intro h hh
    have := hω.sep h 0 hh
    rw [hω.zero, sub_zero] at this
    intro h0
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow1 : ∀ h : ZMod p, h ≠ 0 → ω h ^ (p - 1) = 1 := by
    intro h hh
    have e1 := hω.pow h
    have : ω h ^ (p - 1) * ω h = 1 * ω h := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, e1]
    exact mul_right_cancel₀ (hω0 h hh) this
  have hwt : ∀ h : ZMod p, h ≠ 0 → wt ω h * ω h = 1 := by
    intro h hh
    simp only [wt]
    rw [← pow_succ, show 2 * p - 3 + 1 = (p - 1) + (p - 1) by omega, pow_add, hpow1 h hh, one_mul]
  have hwtmul : ∀ a b : ZMod p, wt ω (a * b) = wt ω a * wt ω b := by
    intro a b; simp only [wt, hω.mul, mul_pow]
  have hwtinv : ∀ h : ZMod p, h ≠ 0 → wt ω h⁻¹ = ω h := by
    intro h hh
    have hi : h⁻¹ ≠ 0 := inv_ne_zero hh
    have e1 := hwt h⁻¹ hi
    have e2 : ω h⁻¹ * ω h = 1 := by rw [← hω.mul, inv_mul_cancel₀ hh, hω.one]
    calc wt ω h⁻¹ = wt ω h⁻¹ * (ω h⁻¹ * ω h) := by rw [e2, mul_one]
      _ = ω h := by rw [← mul_assoc, e1, one_mul]
  have hwt0 : wt ω 0 = 0 := by
    simp only [wt, hω.zero]; exact zero_pow (by omega)
  have hS : ∀ h : ZMod p, h ≠ 0 → sS ω = ω h * sS ω := by
    intro h hh
    have := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => wt ω (h⁻¹ * b)) (wt ω) (fun _ => rfl)
    simp only [hwtmul, hwtinv h hh, ← Finset.mul_sum] at this
    simp only [sS]; exact this.symm
  have hu : ∀ h : ZMod p, h ≠ 0 → ∀ b, u0 ω (h⁻¹ * b) = ω h * u0 ω b := by
    intro h hh b
    simp only [u0]
    by_cases hb : b = 0
    · subst hb
      simp only [mul_zero, if_true, hwt0]
      nth_rewrite 1 [hS h hh]; ring
    · have : h⁻¹ * b ≠ 0 := mul_ne_zero (inv_ne_zero hh) hb
      simp only [this, hb, if_false, sub_zero, hwtmul, hwtinv h hh]
  funext h
  simp only [L2.fourier, LinearMap.coe_mk, AddHom.coe_mk, he2]
  by_cases hh : h = 0
  · subst hh
    simp only [zero_mul, ZMod.val_zero, pow_zero, mul_one, hω.zero, mul_zero]
    rw [← Finset.mul_sum]
    simp only [u0, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [sS]
  · have hb := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => c * u0 ω (h⁻¹ * b) * ζ ^ (h * (h⁻¹ * b)).val)
      (fun a => c * u0 ω a * ζ ^ (h * a).val) (fun _ => rfl)
    rw [← hb]
    simp only [hu h hh, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end ReciprocityTheory.PGsh.Up.U3
end
end

-- bundled from ReciprocityTheory.DualLattices.IsLocalOfIntegers
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

lemma det_col_comb {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i₀ : Fin n)
    (c₀ : R) (β : Fin n → R) :
    (A.updateCol i₀
      (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i)).det = c₀ * A.det := by
  have e : (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i) =
      fun k => ∑ i, (if i = i₀ then c₀ else -β i) • A k i := by
    funext k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), if_pos rfl, smul_eq_mul, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi), smul_eq_mul, neg_mul]
  rw [e, Matrix.det_updateCol_sum, if_pos rfl, smul_eq_mul]

theorem det_mem_span_prod {R : Type*} [CommRing R] [IsLocalRing R] :
    ∀ (m : ℕ) (c : Fin m → R) (n : ℕ) (q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j})),
      Submodule.span R (Set.range q) = ⊤ →
      ∀ T : Matrix (Fin n) (Fin n) R, (∀ k, ∑ i, T k i • q i = 0) →
      T.det ∈ Ideal.span {∏ j, c j} := by
  intro m
  induction m with
  | zero => intro c n q _ T _; simp
  | succ m ih =>
    intro c n q hq T hT
    let tl : ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) →ₗ[R]
        ((j : Fin m) → R ⧸ Ideal.span {c j.succ}) :=
      LinearMap.pi fun j => LinearMap.proj j.succ
    have htl_surj : Function.Surjective tl := fun y =>
      ⟨Fin.cons (0 : R ⧸ Ideal.span {c 0}) y, funext fun j => rfl⟩
    have hprod : ∏ j, c j = c 0 * ∏ j : Fin m, c j.succ := Fin.prod_univ_succ c

    have hfst : ∀ (r : Fin n → R) (a : Fin n → R),
        (∀ i, Ideal.Quotient.mk (Ideal.span {c 0}) (a i) = q i 0) →
        (∑ i, r i • q i) 0 = Ideal.Quotient.mk (Ideal.span {c 0}) (∑ i, r i * a i) := by
      intro r a ha
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, ← ha i, map_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    by_cases hc0 : IsUnit (c 0)
    · have hgen : Submodule.span R (Set.range (tl ∘ q)) = ⊤ := by
        rw [Set.range_comp, ← Submodule.map_span, hq, Submodule.map_top,
          LinearMap.range_eq_top.2 htl_surj]
      have h := ih (fun j => c j.succ) n (tl ∘ q) hgen T (fun k => by
        have := congrArg tl (hT k)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at this
        simpa only [map_smul, Function.comp_apply] using this)
      rw [hprod, Ideal.span_singleton_mul_left_unit hc0]
      exact h
    · choose a ha using fun i => Ideal.Quotient.mk_surjective (q i 0)
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
        (hq ▸ Submodule.mem_top : (Pi.single (0 : Fin (m + 1)) (1 : R ⧸ Ideal.span {c 0}) :
          (j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) ∈ Submodule.span R (Set.range q))
      have hc0m : c 0 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hc0
      have hspan_le : Ideal.span {c 0} ≤ IsLocalRing.maximalIdeal R :=
        (Ideal.span_singleton_le_iff_mem _).2 hc0m
      have h1 : ∑ i, g i * a i - 1 ∈ Ideal.span {c 0} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hfst g a ha, hg]
        simp
      have hu : IsUnit (∑ i, g i * a i) := by
        by_contra hx
        have hx' : ∑ i, g i * a i ∈ IsLocalRing.maximalIdeal R :=
          (IsLocalRing.mem_maximalIdeal _).2 hx
        have := Ideal.sub_mem _ hx' (hspan_le h1)
        rw [sub_sub_cancel] at this
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, IsUnit (a i₀) := by
        by_contra hne
        push Not at hne
        apply (IsLocalRing.mem_maximalIdeal _).1 _ hu
        exact Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i))
      set ai : R := ↑hi₀.unit⁻¹ with hai
      have haai : a i₀ * ai = 1 := by rw [hai]; exact hi₀.mul_val_inv
      let β : Fin n → R := fun i => a i * ai
      have hβ0 : β i₀ = 1 := haai
      let q'' : Fin n → ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) := fun i =>
        if i = i₀ then c 0 • q i₀ else q i - β i • q i₀

      have hcomb : ∀ (r : Fin n → R) (w : R), c 0 * w = ∑ i, r i * β i →
          ∑ i, (if i = i₀ then w else r i) • q'' i = ∑ i, r i • q i := by
        intro r w hw
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        have hrest : ∑ i ∈ Finset.univ.erase i₀, (if i = i₀ then w else r i) • q'' i =
            ∑ i ∈ Finset.univ.erase i₀, r i • q i -
              (∑ i ∈ Finset.univ.erase i₀, r i * β i) • q i₀ := by
          rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
          simp only [q'', if_neg hne, smul_sub, smul_smul]
        have hw' : c 0 * w = r i₀ + ∑ i ∈ Finset.univ.erase i₀, r i * β i := by
          rw [hw, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hβ0, mul_one]
        rw [hrest]
        simp only [q'', if_pos rfl, smul_smul, ↓reduceIte]
        rw [mul_comm w, hw', add_smul]
        abel

      have hk0 : ∀ k, ∑ i, T k i * a i ∈ Ideal.span {c 0} := fun k => by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfst (T k) a ha, hT k]; rfl
      choose t' ht' using fun k => Ideal.mem_span_singleton'.1 (hk0 k)
      let t : Fin n → R := fun k => t' k * ai
      have ht : ∀ k, c 0 * t k = ∑ i, T k i * β i := fun k => by
        simp only [t, β, ← mul_assoc, ← Finset.sum_mul, ← ht' k]
        ring
      let T'' : Matrix (Fin n) (Fin n) R := Matrix.of fun k i => if i = i₀ then t k else T k i
      have hrel : ∀ k, ∑ i, T'' k i • (tl ∘ q'') i = 0 := fun k => by
        have := hcomb (T k) (t k) (ht k)
        rw [hT k] at this
        have h2 := congrArg tl this
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at h2
        simpa only [T'', Matrix.of_apply, map_smul, Function.comp_apply] using h2
      have hgen : Submodule.span R (Set.range (tl ∘ q'')) = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := htl_surj y
        let x0 : (j : Fin (m + 1)) → R ⧸ Ideal.span {c j} := Fin.cons 0 (tl x)
        obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
          (hq ▸ Submodule.mem_top : x0 ∈ Submodule.span R (Set.range q))
        have hr0 : ∑ i, r i * a i ∈ Ideal.span {c 0} := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfst r a ha, hr]; rfl
        obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 hr0
        have hw : c 0 * (w' * ai) = ∑ i, r i * β i := by
          simp only [β, ← mul_assoc, ← Finset.sum_mul, ← hw']
          ring
        have hx := hcomb r (w' * ai) hw
        rw [hr] at hx
        have htx : tl x = tl x0 := funext fun j => rfl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [htx, ← hx, map_sum]
        exact Submodule.sum_mem _ fun i _ => by
          rw [map_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hdet'' := ih (fun j => c j.succ) n (tl ∘ q'') hgen T'' hrel
      have hTeq : T = T''.updateCol i₀
          (fun k => c 0 * T'' k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * T'' k i) := by
        ext k i
        by_cases hi : i = i₀
        · subst hi
          rw [updateCol_self]
          simp only [T'', Matrix.of_apply, ↓reduceIte]
          rw [ht k, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hβ0, mul_one]
          have : ∑ x ∈ Finset.univ.erase i, β x * (if x = i then t k else T k x) =
              ∑ x ∈ Finset.univ.erase i, T k x * β x :=
            Finset.sum_congr rfl fun x hx => by
              rw [if_neg (Finset.ne_of_mem_erase hx), mul_comm]
          rw [this]; ring
        · rw [updateCol_ne hi]
          simp only [T'', Matrix.of_apply, if_neg hi]
      rw [hTeq, det_col_comb]
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hdet''
      rw [hprod, ← hz]
      exact Ideal.mem_span_singleton'.2 ⟨z, by ring⟩

lemma isLocal_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) : IsLocalRing R := by
  have hne : Nontrivial R := ⟨⟨0, 1, fun h => by
    have := congrArg (fun x => v (algebraMap R C x)) h
    simp at this⟩⟩
  refine @IsLocalRing.of_nonunits_add R _ hne ?_
  intro a b ha hb
  rw [mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one] at ha hb ⊢
  have ha' : v (algebraMap R C a) < 1 := lt_of_le_of_ne (hv.map_le_one a) ha
  have hb' : v (algebraMap R C b) < 1 := lt_of_le_of_ne (hv.map_le_one b) hb
  rw [map_add (f := _)]
  exact ne_of_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt ha' hb'))

theorem prod_le_of_gen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (hx : HasLen v R M x) {n : ℕ} (y : Fin n → M)
    (hy : Submodule.span R (Set.range y) = ⊤) (δ : Fin n → R)
    (hrel : ∀ i, ∃ a : Fin n → R, δ i • y i = ∑ j, (if j < i then a j else 0) • y j) :
    ∏ i, v (algebraMap R C (δ i)) ≤ x := by
  haveI := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, hxc⟩ := hx
  choose a ha using hrel
  obtain ⟨q, hqdef⟩ : ∃ q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j}), q = fun i => e (y i) :=
    ⟨_, rfl⟩
  have hq : Submodule.span R (Set.range q) = ⊤ := by
    have h1 : Set.range q = (e : M →ₗ[R] _) '' Set.range y := by
      ext z
      simp [hqdef]
    rw [h1, Submodule.span_image, hy, Submodule.map_top, LinearEquiv.range]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) R,
      T = fun i j => (if j = i then δ i else 0) - (if j < i then a i j else 0) := ⟨_, rfl⟩
  have hrelT : ∀ k, ∑ i, T k i • q i = 0 := by
    intro k
    have h := congrArg e (ha k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, ite_smul, zero_smul] at h
    simp only [hT, hqdef, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hdet := det_mem_span_prod m c n q hq T hrelT
  have hdetT : T.det = ∏ i, δ i := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [hT]
    · intro i j hij
      have h' : i < j := OrderDual.toDual_lt_toDual.mp hij
      simp [hT, h'.ne', not_lt.mpr h'.le]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hdet
  calc ∏ i, v (algebraMap R C (δ i)) = v (algebraMap R C (∏ i, δ i)) := by simp [map_prod]
    _ = v (algebraMap R C r) * ∏ j, v (algebraMap R C (c j)) := by
        rw [← hdetT, ← hr]
        simp [map_prod]
    _ ≤ 1 * ∏ j, v (algebraMap R C (c j)) := by
        gcongr
        exact hv.map_le_one r
    _ = x := by rw [one_mul, hxc]

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ModuliPointsState
section
namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

structure DualPair (R : LAlg R₀) where
  D : LAlg R₀
  π : LHom D R
  σ : LHom R D
  η : (D : Type u)
  sect : ∀ r, π.1 (σ.1 r) = r
  η_sq : η * η = 0
  ker_eq : RingHom.ker π.1 = Ideal.span {η}
  free : ∀ r, σ.1 r * η = 0 → r = 0

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma η_mem : Dp.η ∈ Dp.π.ker := by
  show Dp.η ∈ RingHom.ker Dp.π.1
  rw [Dp.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma sqZero : Dp.π.SqZero := by
  refine ⟨fun r => ⟨Dp.σ.1 r, Dp.sect r⟩, ?_⟩
  rw [Dp.ker_eq, Ideal.span_singleton_pow, pow_two, Dp.η_sq, Ideal.span_singleton_eq_bot]

def ηk : Dp.π.ker := ⟨Dp.η, Dp.η_mem⟩

end DualPair

namespace BX

variable (B : BX R₀)

def IsHeight {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] R) : Prop :=
  ∀ v : B.gg, ∃ z : (Dp.D : Type u)ˣ,
    B.IsPairing N (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y) z ∧ (z : Dp.D) = 1 + Dp.σ.1 (h v) * Dp.η

end BX

def HighestWeightVectorUniformBounds (B : BX R₀) : Prop :=
  ∀ (R : LAlg R₀) (Dp : DualPair R) (N : ℕ), (N : (R : Type u)) = 0 →
    (∀ (y : B.G R) (v : B.gg) (u : B.P Dp.D (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y)),
      HEq (B.pmap Dp.π u) (B.zero1 y) →
      HEq (B.nsmul1 u N) (B.zero1 (B.map Dp.σ y))) ∧
    (∀ y : B.G R, N • y = 0 → ∃! h : B.gg →ₗ[R₀] R, B.IsHeight Dp N y h) ∧
    (∀ (y y' : B.G R) (h h' : B.gg →ₗ[R₀] R), B.IsHeight Dp N y h → B.IsHeight Dp N y' h' →
      B.IsHeight Dp N (y + y') (h + h'))

end ReciprocityTheory.PGsh
end

