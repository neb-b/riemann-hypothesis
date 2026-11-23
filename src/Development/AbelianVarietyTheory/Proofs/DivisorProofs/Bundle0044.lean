module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingBasicOpenFunctions
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_separating_basicOpen_functions : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  intro X U hU F hFU hsp W hW
  classical
  have key : ∀ a ∈ F, ∃ g : Γ(X, U), a ∈ X.basicOpen g ∧ X.basicOpen g ≤ W a ∧
      ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen g := by
    intro a ha
    let C : Set X := ⋃ b ∈ F.erase a, closure {b}
    have hC : IsClosed C := isClosed_biUnion_finset (fun b _ => isClosed_closure)
    let V : X.Opens := W a ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
    have haC : a ∉ C := by
      simp only [C, Set.mem_iUnion, not_exists]
      intro b hb hab
      have hb' := Finset.mem_erase.mp hb
      exact hb'.1 (hsp b hb'.2 a ha (specializes_iff_mem_closure.mpr hab))
    have haV : a ∈ V := ⟨hW a ha, haC⟩
    obtain ⟨g, hgV, hag⟩ := hU.exists_basicOpen_le ⟨a, haV⟩ (hFU a ha)
    refine ⟨g, hag, le_trans hgV inf_le_left, ?_⟩
    intro b hb hba hbg
    have hbV : b ∈ V := hgV hbg
    apply hbV.2
    simp only [C, Set.mem_iUnion]
    exact ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, subset_closure rfl⟩
  choose! f hf using key
  exact ⟨f, hf⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingElementRingHomModuleFiniteInt
section
open Finset

namespace GlobalTheory

theorem ringHom_sep_charZero (k : Type) [Field k] [CharZero k] (C : Type) [CommRing C]
    (S : Finset (C →+* k)) (χ₀ : C →+* k) : ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert χ' S hχ' ih =>
    obtain ⟨c, hc⟩ := ih
    by_cases h0 : χ' = χ₀
    · refine ⟨c, fun χ hχ hne => ?_⟩
      rcases Finset.mem_insert.1 hχ with rfl | h
      · exact absurd h0 hne
      · exact hc χ h hne
    obtain ⟨d, hd⟩ := DFunLike.ne_iff.1 h0
    have key : ∀ χ ∈ insert χ' S, χ ≠ χ₀ →
        ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ).Subsingleton := by
      intro χ hχ hne n hn m hm
      simp only [Set.mem_setOf_eq, map_add (f := _), map_mul, map_natCast] at hn hm
      have hsub : ((n : k) - m) * (χ d - χ₀ d) = 0 := by linear_combination hn - hm
      rcases mul_eq_zero.1 hsub with h | h
      · exact_mod_cast sub_eq_zero.1 h
      · have hb : χ d = χ₀ d := sub_eq_zero.1 h
        rcases Finset.mem_insert.1 hχ with rfl | h'
        · exact absurd hb hd
        · exact absurd (by rw [hb] at hn; linear_combination hn) (hc χ h' hne)
    have hfin : (⋃ χ ∈ (insert χ' S).filter (· ≠ χ₀),
        ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ)).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun χ hχ => ?_
      rw [Finset.mem_coe, Finset.mem_filter] at hχ
      exact (key χ hχ.1 hχ.2).finite
    obtain ⟨n, hn⟩ := hfin.exists_notMem
    refine ⟨c + n * d, fun χ hχ hne heq => hn ?_⟩
    simp only [Set.mem_iUnion]
    exact ⟨χ, Finset.mem_filter.2 ⟨hχ, hne⟩, heq⟩

theorem ringHom_pow_eq_one_of_finite_range {k : Type} [Field k] {C : Type} [CommRing C]
    (ψ : C →+* k) [Finite ψ.range] (a : C) (ha : ψ a ≠ 0) (m : ℕ)
    (hm : (Nat.card ψ.range).factorial ∣ m) : ψ a ^ m = 1 := by
  classical
  haveI := Fintype.ofFinite ψ.range
  let f : Fin (Nat.card ψ.range + 1) → ψ.range := fun i => ⟨ψ a ^ (i : ℕ), ⟨a ^ (i : ℕ), by simp⟩⟩
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have hf' : ψ a ^ (i : ℕ) = ψ a ^ (j : ℕ) := congrArg Subtype.val hf
  have hpos : ∀ (u v : ℕ), u < v → v ≤ Nat.card ψ.range → ψ a ^ u = ψ a ^ v → ψ a ^ m = 1 := by
    intro u v huv hv he
    have h1 : ψ a ^ (v - u) = 1 := by
      have : ψ a ^ u * (ψ a ^ (v - u) - 1) = 0 := by
        rw [mul_sub, ← pow_add, Nat.add_sub_cancel' huv.le, mul_one, he, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff'.1 h).1 ha
      · exact sub_eq_zero.1 h
    have hd : v - u ∣ m := (Nat.dvd_factorial (by omega) (by omega)).trans hm
    obtain ⟨t, rfl⟩ := hd
    rw [pow_mul, h1, one_pow]
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact hpos i j h (by omega) hf'
  · exact hpos j i h (by omega) hf'.symm

theorem ringHom_exists_generator_of_finite_range {k : Type} [Field k] {C : Type} [CommRing C]
    (χ₀ : C →+* k) [Finite χ₀.range] :
    ∃ g : C, χ₀ g ≠ 0 ∧ ∀ b, χ₀ b ≠ 0 → ∃ n : ℕ, χ₀ b = χ₀ g ^ n := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (χ₀.range)ˣ)
  obtain ⟨g, hg⟩ := ((u : χ₀.range)).2
  refine ⟨g, ?_, fun b hb => ?_⟩
  · rw [hg]
    exact fun h => u.ne_zero (Subtype.ext h)
  · set y : χ₀.range := ⟨χ₀ b, ⟨b, rfl⟩⟩
    have hy0 : y ≠ 0 := fun h => hb (congrArg Subtype.val h)
    have hyu : IsUnit y := by
      have hpow := ringHom_pow_eq_one_of_finite_range χ₀ b hb _ dvd_rfl
      exact ⟨Units.ofPowEqOne y (Nat.card χ₀.range).factorial
        (Subtype.ext (by simpa [y] using hpow)) (Nat.factorial_ne_zero _), rfl⟩
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.2 (hu hyu.unit) : hyu.unit ∈ Submonoid.powers u)
    refine ⟨n, ?_⟩
    have h1 : ((u ^ n : (χ₀.range)ˣ) : χ₀.range) = y := by
      rw [show u ^ n = hyu.unit from hn]; rfl
    have h2 : ((u : χ₀.range) : k) ^ n = χ₀ b := by
      have := congrArg Subtype.val h1
      simpa [y] using this
    rw [hg]
    exact h2.symm

end GlobalTheory

namespace GlobalTheory

theorem ringHom_sep_of_finite_range (k : Type) [Field k] (C : Type) [CommRing C]
    (hfin : ∀ ψ : C →+* k, Finite ψ.range) (S : Finset (C →+* k)) (χ₀ : C →+* k) :
    ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  classical
  let M : ℕ := ∏ ψ ∈ insert χ₀ S, (Nat.card ψ.range).factorial
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hpow : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ a ≠ 0 → ψ a ^ M = 1 := fun ψ hψ a ha => by
    haveI := hfin ψ
    exact ringHom_pow_eq_one_of_finite_range ψ a ha M (Finset.dvd_prod_of_mem _ hψ)
  have hpow' : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ (a ^ M) = if ψ a = 0 then 0 else 1 := by
    intro ψ hψ a
    rw [map_pow]
    split_ifs with h
    · rw [h, zero_pow hM0]
    · exact hpow ψ hψ a h
  haveI := hfin χ₀
  obtain ⟨g, hg0, hgen⟩ := ringHom_exists_generator_of_finite_range χ₀
  have hsep : ∀ χ ∈ S, χ ≠ χ₀ → χ g = χ₀ g → ∃ a, χ a = 0 ∧ χ₀ a ≠ 0 := by
    intro χ hχ hne hgeq
    by_contra hcon
    push_neg at hcon
    have hχ' : χ ∈ insert χ₀ S := Finset.mem_insert_of_mem hχ
    have hk : ∀ b, χ₀ b = 0 → χ b = 0 := by
      intro b hb
      by_contra hb'
      have h1 := hcon (1 - b ^ M) (by rw [map_sub, map_one, map_pow, hpow χ hχ' b hb', sub_self])
      rw [map_sub, map_one, map_pow, hb, zero_pow hM0, sub_zero] at h1
      exact one_ne_zero h1
    apply hne
    ext b
    by_cases hb : χ₀ b = 0
    · rw [hb, hk b hb]
    · obtain ⟨n, hn⟩ := hgen b hb
      have h3 : χ (b - g ^ n) = 0 := hk _ (by rw [map_sub, map_pow, hn, sub_self])
      rw [map_sub, map_pow, sub_eq_zero, hgeq, ← hn] at h3
      exact h3
  let V := S.filter (fun χ => χ ≠ χ₀ ∧ χ g = χ₀ g)
  have hV : ∀ χ ∈ V, ∃ a, χ a = 0 ∧ χ₀ a ≠ 0 := fun χ hχ => by
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 hχ)
    exact hsep χ h1 h2 h3
  choose! a ha using hV
  let A : C := ∏ χ ∈ V, a χ
  have hA0 : χ₀ A ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun χ hχ => (ha χ hχ).2
  have hAV : ∀ χ ∈ V, χ A = 0 := fun χ hχ => by
    rw [map_prod]
    exact Finset.prod_eq_zero hχ (ha χ hχ).1
  refine ⟨g * A ^ M, fun χ hχ hne => ?_⟩
  have hχ' : χ ∈ insert χ₀ S := Finset.mem_insert_of_mem hχ
  rw [map_mul, map_mul, hpow' χ₀ (Finset.mem_insert_self _ _), if_neg hA0, mul_one,
    hpow' χ hχ']
  by_cases hgeq : χ g = χ₀ g
  · rw [if_pos (hAV χ (Finset.mem_filter.2 ⟨hχ, hne, hgeq⟩)), mul_zero]
    exact fun h => hg0 h.symm
  · split_ifs
    · rw [mul_zero]; exact fun h => hg0 h.symm
    · rwa [mul_one]

theorem ringHom_finite_range_of_charP {k : Type} [Field k] {C : Type} [CommRing C]
    [Module.Finite ℤ C] (p : ℕ) [hp : CharP k p] (hp0 : p ≠ 0) (ψ : C →+* k) :
    Finite ψ.range := by
  haveI : Module.Finite ℤ ψ.range :=
    Module.Finite.of_surjective (ψ.rangeRestrict.toAddMonoidHom.toIntLinearMap)
      ψ.rangeRestrict_surjective
  haveI : AddGroup.FG ψ.range := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨p, Nat.pos_of_ne_zero hp0, ?_⟩
  apply Subtype.ext
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

theorem ringHom_exists_sep_of_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C]
    [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k),
    ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  intro k _ C _ _ S χ₀
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · exact ringHom_sep_of_finite_range k C
      (fun ψ => ringHom_finite_range_of_charP p hpp.ne_zero ψ) S χ₀
  · haveI := CharP.charP_to_charZero k
    exact ringHom_sep_charZero k C S χ₀

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFockFormOfComplexStructure
section
open scoped Matrix

namespace GlobalTheory

theorem siegel_fock_exists : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by
  intro V _ _ _ β J hsym hJJ hJ hpos
  set Φ : (V × V) →ₗ[ℝ] (V × V) :=
    LinearMap.inr ℝ V V ∘ₗ LinearMap.fst ℝ V V + J ∘ₗ LinearMap.inr ℝ V V ∘ₗ LinearMap.snd ℝ V V with hΦdef
  have hΦ : ∀ u : V × V, Φ u = (0, u.1) + J (0, u.2) := by
    intro u; simp [hΦdef]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hΦ] at hu
    have h1 : (J (0, u.2)).1 = 0 := by
      have := congrArg Prod.fst hu; simpa using this
    have hb : u.2 = 0 := by
      by_contra hne
      have := hpos (0, u.2) (by simpa using hne)
      simp [h1] at this
    have hJ0 : J (0, 0) = 0 := J.map_zero
    have ha : u.1 = 0 := by
      have := congrArg Prod.snd hu; simpa [hb, hJ0] using this
    exact Prod.ext ha hb
  set E := LinearEquiv.ofInjectiveEndo Φ hinj with hEdef
  have hE : ∀ w, Φ (E.symm w) = w := fun w => by
    show E (E.symm w) = w
    exact E.apply_symm_apply w
  have hJ0 : J (0, 0) = 0 := J.map_zero
  set A : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hAdef
  set B : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hBdef
  have hAB : ∀ p, E.symm (p, 0) = (A p, B p) := fun p => by simp [hAdef, hBdef]
  have hP0 : ∀ q, E.symm (0, q) = (q, 0) := fun q => by
    apply E.injective
    rw [E.apply_symm_apply]
    show (0, q) = Φ (q, 0)
    rw [hΦ]; simp [hJ0]
  have hsplit : ∀ w : V × V, E.symm w = (A w.1 + w.2, B w.1) := fun w => by
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    rw [hw, map_add (f := _), hAB, hP0]; simp
  have hJB : ∀ p, J (0, B p) = (p, -A p) := fun p => by
    have := hE (p, 0)
    rw [hAB, hΦ] at this
    have h2 : J (0, B p) = (p, 0) - (0, A p) := by rw [← this]; abel
    rw [h2]; simp
  have hPJ : ∀ w : V × V, E.symm (J w) = (-(E.symm w).2, (E.symm w).1) := fun w => by
    apply E.injective
    rw [E.apply_symm_apply]
    show J w = Φ _
    conv_lhs => rw [← hE w]
    rw [hΦ, hΦ, map_add (f := _), hJJ]
    ext <;> simp <;> abel
  have hAsym : ∀ x y, β x (A y) = β y (A x) := fun x y => by
    have := hJ (0, B x) (0, B y)
    rw [hJB, hJB] at this
    simp at this
    linarith
  have hBsym : ∀ x y, β x (B y) = β y (B x) := fun x y => by
    have := hJ (J (0, B x)) (0, B y)
    rw [hJJ, hJB, hJB] at this
    simp at this
    linarith
  have hBpos : ∀ x, x ≠ 0 → 0 < -β x (B x) := fun x hx => by
    have hne : ((0 : V), B x) ≠ 0 := by
      intro h0
      have h1 : J (0, B x) = 0 := by rw [h0]; exact J.map_zero
      rw [hJB] at h1
      exact hx (congrArg Prod.fst h1)
    have := hpos (0, B x) hne
    rw [hJB] at this
    simpa using this
  let Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ))
    (fun m₁ m₂ n => by simp; ring)
    (fun c m n => by simp; ring)
    (fun m n₁ n₂ => by simp; ring)
    (fun c m n => by simp; ring)
  let Q : V →L[ℝ] V →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ Q')
  have hQ : ∀ x y, Q x y = ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ) :=
    fun x y => rfl
  have hre : ∀ x, (Q x x).re = Real.pi * -β x (B x) := fun x => by
    rw [hQ]; simp
  have hscale : ∀ (t : ℝ) (y : V), Real.pi * -β (t • y) (B (t • y)) = t ^ 2 * (Real.pi * -β y (B y)) :=
    fun t y => by simp; ring
  have hcont : Continuous fun x => (Q x x).re := by fun_prop
  have hsym' : ∀ x y, Q x y = Q y x := fun x y => by rw [hQ, hQ, hAsym x y, hBsym x y]
  have hfock : ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) =
      Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := fun w x => by
    have e1 := hsplit (J w)
    rw [hPJ, hsplit w] at e1
    have h1 : A (J w).1 + (J w).2 = -(B w.1) := (congrArg Prod.fst e1).symm
    have h2 : B (J w).1 = A w.1 + w.2 := (congrArg Prod.snd e1).symm
    have hb1 : β x (A (J w).1) = -β x (B w.1) - β x (J w).2 := by
      have := congrArg (β x) h1; simp at this; linarith
    have hb2 : β x (B (J w).1) = β x (A w.1) + β x w.2 := by rw [h2]; simp
    rw [hQ, hQ, hb1, hb2]
    push_cast
    linear_combination (-((Real.pi : ℂ) * (β x (A w.1) : ℂ) + (Real.pi : ℂ) * (β x w.2 : ℂ))) * Complex.I_sq
  by_cases hs : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hs hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    refine ⟨Q, (Q u u).re, ?_, ?_, hsym', hfock⟩
    · rw [hre]; exact mul_pos Real.pi_pos (hBpos u hu0)
    · intro x
      by_cases hx : x = 0
      · subst hx; simp
      · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hu' : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
        have hm : (Q u u).re ≤ (Q (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := hmin hu'
        have key : Real.pi * -β x (B x) = ‖x‖ ^ 2 * (Real.pi * -β (‖x‖⁻¹ • x) (B (‖x‖⁻¹ • x))) := by
          rw [hscale]; field_simp
        rw [hre, hre] at hm
        rw [hre u, hre x, key]
        have := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖x‖)
        linarith
  · refine ⟨Q, 1, one_pos, ?_, hsym', hfock⟩
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      apply hs
      refine ⟨‖x‖⁻¹ • x, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemRangeOfSurjectiveLocalizedMap
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_smul_mem_range_of_surjective_localization_map
    (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B)
    (hs : Function.Surjective (Algebra.TensorProduct.map
      (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ)) :
    ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  intro b
  classical
  set L := Localization.AtPrime p
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  let π := N.mkQ
  let g : L ⊗[R] B →ₗ[R] L ⊗[R] (B ⧸ N) := LinearMap.lTensor L π
  obtain ⟨z, hz⟩ := hs ((1 : L) ⊗ₜ[R] b)
  have key : ∀ w : L ⊗[R] A, g (Algebra.TensorProduct.map
      (AlgHom.id L L) ψ w) = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul]
      simp only [g, LinearMap.lTensor_tmul]
      have : π (ψ y) = 0 := by
        simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨y, rfl⟩
      rw [this, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  have h0 : (TensorProduct.mk R L (B ⧸ N) 1) (π b) = 0 := by
    have := key z
    rw [hz] at this
    simpa [g] using this
  have hloc : IsLocalizedModule p.primeCompl (TensorProduct.mk R L (B ⧸ N) 1) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl L _).mpr (TensorProduct.isBaseChange R _ L)
  obtain ⟨s, hs'⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl _).mp h0
  refine ⟨s, s.2, ?_⟩
  have : π ((s : R) • b) = 0 := by
    rw [map_smul]; exact hs'
  simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquarePresentationOfTower
section
open scoped TensorProduct

namespace GlobalTheory.SquareTower

open MvPolynomial

noncomputable def presOf {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {s : ℕ}
    (φ : MvPolynomial (Fin s) R →ₐ[R] S) (g : Fin s → MvPolynomial (Fin s) R)
    (hs : Function.Surjective φ) (hk : RingHom.ker φ = Ideal.span (Set.range g)) :
    Algebra.Presentation R S (Fin s) (Fin s) :=
  have he : MvPolynomial.aeval (fun i => φ (X i)) = φ := MvPolynomial.algHom_ext (fun i => aeval_X _ _)
  { toGenerators := Algebra.Generators.ofSurjective (fun i => φ (X i)) (by rw [he]; exact hs)
    relation := g
    span_range_relation_eq_ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, ← hk]
      change RingHom.ker φ = RingHom.ker (MvPolynomial.aeval (fun i => φ (X i)))
      rw [he] }

theorem square_of_pres {R T ι σ : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (P : Algebra.Presentation R T ι σ) (e : Fin n ≃ ι) (f : Fin n ≃ σ) :
    ∃ (s : ℕ) (φ : MvPolynomial (Fin s) R →ₐ[R] T) (g : Fin s → MvPolynomial (Fin s) R),
      Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g) := by
  let E : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial ι R := renameEquiv R e
  refine ⟨n, (aeval P.val).comp E.toAlgHom, fun i => E.symm (P.relation (f i)), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := P.toGenerators.algebraMap_surjective y
    refine ⟨E.symm x, ?_⟩
    show aeval P.val (E (E.symm x)) = y
    rw [E.apply_symm_apply, ← hx, Algebra.Generators.algebraMap_eq]
    rfl
  · have h1 : Set.range (fun i => E.symm (P.relation (f i))) = E.symm '' Set.range P.relation := by
      rw [← Set.range_comp]
      exact f.surjective.range_comp (⇑E.symm ∘ P.relation)
    rw [h1, ← Ideal.map_span, P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      refine ⟨E x, ?_, by simp⟩
      rw [RingHom.mem_ker]; simpa using hx
    · rintro ⟨y, hy, rfl⟩
      rw [RingHom.mem_ker] at hy
      simpa using hy

theorem tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro k B A _ _ _ _ _ _ _
  rintro ⟨t, φ, g, hφ, hg⟩ ⟨d, ψ, h, hψ, hh⟩
  let P := presOf φ g hφ hg
  let Q := presOf ψ h hψ hh
  exact square_of_pres (Q.comp P) finSumFinEquiv.symm finSumFinEquiv.symm

end GlobalTheory.SquareTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAppOfIsAffineHomFlatSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem faithfullyFlat_app_of_isAffineHom_flat_surjective :
    ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p →
      IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by
  intro X Y p V _ _ _ hV
  have hpre : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have : IsAffine V := hV
  have : IsAffine (p ⁻¹ᵁ V) := hpre
  have : Flat (p ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p V).flip ‹Flat p›
  have : Surjective (p ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Surjective p› V
  have hff := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (p ∣_ V)).mp
    ⟨inferInstance, inferInstance⟩
  rw [morphismRestrict_appTop] at hff
  have hff' := (RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso
    (p.app (V.ι ''ᵁ ⊤)) (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)).mp hff
  rwa [Scheme.Opens.ι_image_top] at hff'

end GlobalTheory
end

