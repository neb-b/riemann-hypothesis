module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.H1cEqH1

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.HasSmithOfOne
section
namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [CommRing R]

private def HasSmith {a : ℕ} (Φ : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ (U V : Matrix (Fin a) (Fin a) R) (d : Fin a → R), IsUnit U.det ∧ IsUnit V.det ∧
      Φ = U * diagonal d * V ∧ ∀ i j, i ≤ j → d i ∣ d j

private theorem HasSmith.smul {a : ℕ} {Φ : Matrix (Fin a) (Fin a) R} (h : HasSmith Φ) (x : R) :
    HasSmith (x • Φ) := by
  obtain ⟨U, V, d, hU, hV, rfl, hd⟩ := h
  refine ⟨U, V, x • d, hU, hV, ?_, fun i j hij => ?_⟩
  · rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  · exact mul_dvd_mul_left x (hd i j hij)

private theorem HasSmith.perm {a : ℕ} {Φ : Matrix (Fin a) (Fin a) R} (h : HasSmith Φ)
    (σ τ : Equiv.Perm (Fin a)) : HasSmith (Φ.submatrix σ τ) := by
  obtain ⟨U, V, d, hU, hV, rfl, hd⟩ := h
  refine ⟨U.submatrix σ id, V.submatrix id τ, d, ?_, ?_, ?_, hd⟩
  · rw [det_permute]
    exact ((Equiv.Perm.sign σ).isUnit.map (Int.castRingHom R)).mul hU
  · rw [det_permute']
    exact ((Equiv.Perm.sign τ).isUnit.map (Int.castRingHom R)).mul hV
  · ext i j
    simp [Matrix.mul_apply]

private def consEquiv (a : ℕ) : Fin (a + 1) ≃ Unit ⊕ Fin a where
  toFun := Fin.cases (Sum.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by cases i using Fin.cases <;> simp
  right_inv i := by rcases i with _ | i <;> simp

private theorem hasSmith_of_one {a : ℕ} (ih : ∀ Ψ : Matrix (Fin a) (Fin a) R, HasSmith Ψ)
    (M : Matrix (Fin (a + 1)) (Fin (a + 1)) R) (h : M 0 0 = 1) : HasSmith M := by
  set e := consEquiv a with he
  set N := M.submatrix e.symm e.symm with hN
  have h11 : N.toBlocks₁₁ = 1 := by
    ext i j
    have : N (Sum.inl i) (Sum.inl j) = M 0 0 := rfl
    simp [toBlocks₁₁, this, h]
  obtain ⟨U, V, d, hU, hV, hΨ, hd⟩ := ih (N.toBlocks₂₂ - N.toBlocks₂₁ * N.toBlocks₁₂)
  have key : N = fromBlocks 1 0 N.toBlocks₂₁ U * diagonal (Sum.elim (fun _ => 1) d) *
      fromBlocks 1 N.toBlocks₁₂ 0 V := by
    rw [← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply]
    conv_lhs => rw [← fromBlocks_toBlocks N, h11]
    simp [← hΨ]
  refine ⟨(fromBlocks 1 0 N.toBlocks₂₁ U).submatrix e e,
    (fromBlocks 1 N.toBlocks₁₂ 0 V).submatrix e e, Sum.elim (fun _ => 1) d ∘ e, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; simpa using hU
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]; simpa using hV
  · rw [← submatrix_diagonal_equiv, submatrix_mul_equiv, submatrix_mul_equiv, ← key, hN]
    simp
  · intro i j hij
    cases i using Fin.cases with
    | zero => exact one_dvd _
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j => exact hd i j (by simpa using hij)

private theorem exists_dvd_all [PreValuationRing R] {ι : Type*} (f : ι → R) (s : Finset ι)
    (hs : s.Nonempty) : ∃ p ∈ s, ∀ i ∈ s, f p ∣ f i := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, by simp, by simp⟩
  | cons a s ha hs ih =>
    obtain ⟨p, hp, h⟩ := ih
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond (f a) (f p)
    · refine ⟨a, by simp, fun i hi => ?_⟩
      rcases Finset.mem_cons.1 hi with rfl | hi
      · exact dvd_rfl
      · exact (Dvd.intro c hc).trans (h i hi)
    · refine ⟨p, by simp [hp], fun i hi => ?_⟩
      rcases Finset.mem_cons.1 hi with rfl | hi
      · exact Dvd.intro c hc
      · exact h i hi

private theorem hasSmith_all [PreValuationRing R] (a : ℕ) (Φ : Matrix (Fin a) (Fin a) R) :
    HasSmith Φ := by
  classical
  induction a with
  | zero =>
    exact ⟨1, 1, fun _ => 1, by simp, by simp, Subsingleton.elim _ _, fun _ _ _ => dvd_rfl⟩
  | succ a ih =>
    obtain ⟨⟨p, q⟩, -, h⟩ := exists_dvd_all (fun ij : Fin (a + 1) × Fin (a + 1) => Φ ij.1 ij.2)
      Finset.univ Finset.univ_nonempty
    have h' : ∀ i j, ∃ c, Φ i j = Φ p q * c ∧ (i = p → j = q → c = 1) := by
      intro i j
      by_cases hij : i = p ∧ j = q
      · obtain ⟨rfl, rfl⟩ := hij
        exact ⟨1, by simp, by simp⟩
      · obtain ⟨c, hc⟩ := h (i, j) (Finset.mem_univ _)
        exact ⟨c, hc, fun h1 h2 => absurd ⟨h1, h2⟩ hij⟩
    choose M hM hM1 using h'
    have h1 : HasSmith ((Matrix.of M).submatrix (Equiv.swap 0 p) (Equiv.swap 0 q)) :=
      hasSmith_of_one ih _ (by simp [hM1 p q rfl rfl])
    have h2 := (h1.perm (Equiv.swap 0 p) (Equiv.swap 0 q)).smul (Φ p q)
    convert h2 using 1
    ext i j
    simpa using hM i j

theorem exists_smith [PreValuationRing R] (a : ℕ) (Φ : Matrix (Fin a) (Fin a) R) :
    ∃ (U V : Matrix (Fin a) (Fin a) R) (d : Fin a → R), IsUnit U.det ∧ IsUnit V.det ∧
      Φ = U * diagonal d * V ∧ ∀ i j, i ≤ j → d i ∣ d j :=
  hasSmith_all a Φ

end KStar.Selmer
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthExact
section
namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [Ring R] {A B C D : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

theorem length_add_of_exact₄ (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hh : Function.Surjective h) :
    Module.length R A + Module.length R C = Module.length R B + Module.length R D := by
  have h1 : Module.length R B = Module.length R A + Module.length R (LinearMap.range g) := by
    refine Module.length_eq_add_of_exact f g.rangeRestrict hf g.surjective_rangeRestrict ?_
    intro x
    rw [← hfg x]
    exact Subtype.ext_iff
  have h2 : Module.length R C = Module.length R (LinearMap.range g) + Module.length R D := by
    refine Module.length_eq_add_of_exact (LinearMap.range g).subtype h
      (Submodule.injective_subtype _) hh ?_
    intro x
    rw [hgh x]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  rw [h1, h2, add_assoc]

theorem length_ker_eq_length_coker (f : A →ₗ[R] A) (hfin : Module.length R A ≠ ⊤) :
    Module.length R (LinearMap.ker f) = Module.length R (A ⧸ LinearMap.range f) := by
  have h1 := length_add_of_exact₄ (LinearMap.ker f).subtype f (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map f)
    (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)
  rw [add_comm (Module.length R (LinearMap.ker f))] at h1
  exact ENat.add_right_injective_of_ne_top hfin h1

end KStar.Selmer
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj
section
namespace KStar.Selmer

open Matrix Module

variable {N : ℕ} [NeZero N] {M M' : Type*} [AddCommGroup M] [Module (ZMod N) M] [AddCommGroup M']
  [Module (ZMod N) M']

private theorem zmod_dbl_ann (d y : ZMod N) (h : ∀ r : ZMod N, r * d = 0 → r * y = 0) :
    ∃ c : ZMod N, y = c * d := by
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective d
  obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective y
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right a N
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a N
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by rw [hm, h0, mul_zero]) (NeZero.ne N)
    · exact h0
  have h1 : (m : ZMod N) * a = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨a', ?_⟩
    calc m * a = m * (a.gcd N * a') := by rw [← ha']
      _ = (a.gcd N * m) * a' := by ring
      _ = N * a' := by rw [← hm]
  have h2 := h _ h1
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h2
  have h3 : a.gcd N * m ∣ b * m := by rw [← hm, mul_comm]; exact h2
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_right hm0 h3
  have h4 : ((a.gcd N : ℕ) : ZMod N) = (a : ZMod N) * ((Nat.gcdA a N : ℤ) : ZMod N) := by
    have := congrArg (fun t : ℤ => (t : ZMod N)) (Nat.gcd_eq_gcd_ab a N)
    simpa using this
  refine ⟨((Nat.gcdA a N : ℤ) : ZMod N) * k, ?_⟩
  rw [hk, Nat.cast_mul, h4]
  ring

omit [NeZero N] in
private theorem zmod_ideal_gen (I : Ideal (ZMod N)) :
    ∃ d ∈ I, ∀ x ∈ I, ∃ r : ZMod N, x = r * d := by
  have : IsPrincipalIdealRing (ZMod N) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod N)) (ZMod.ringHom_surjective _)
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal I).principal
  refine ⟨d, hd ▸ Submodule.mem_span_singleton_self d, fun x hx => ?_⟩
  rw [hd, Submodule.mem_span_singleton] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, rfl⟩

theorem zmod_baer : Module.Baer (ZMod N) (ZMod N) := by
  intro I g
  obtain ⟨d, hd, hI⟩ := zmod_ideal_gen I
  obtain ⟨c, hc⟩ := zmod_dbl_ann d (g ⟨d, hd⟩) (fun r hr => by
    have : r • (⟨d, hd⟩ : I) = 0 := Subtype.ext hr
    rw [← smul_eq_mul, ← map_smul, this, map_zero])
  refine ⟨LinearMap.toSpanSingleton _ _ c, fun x hx => ?_⟩
  obtain ⟨r, rfl⟩ := hI x hx
  have : (⟨r * d, hx⟩ : I) = r • (⟨d, hd⟩ : I) := rfl
  rw [this, map_smul, hc, LinearMap.toSpanSingleton_apply, smul_eq_mul, smul_eq_mul]
  ring

private theorem zmod_extend {A B : Type*} [AddCommGroup A] [Module (ZMod N) A] [AddCommGroup B]
    [Module (ZMod N) B] (φ : A →ₗ[ZMod N] B) (c : A →ₗ[ZMod N] ZMod N)
    (h : ∀ a, φ a = 0 → c a = 0) : ∃ t : B →ₗ[ZMod N] ZMod N, ∀ a, t (φ a) = c a := by
  obtain ⟨t, ht⟩ := (zmod_baer (N := N)).extension_property
    ((LinearMap.ker φ).liftQ φ le_rfl)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
    ((LinearMap.ker φ).liftQ c (fun a ha => h a ha))
  refine ⟨t, fun a => ?_⟩
  exact LinearMap.congr_fun ht (Submodule.Quotient.mk a)

theorem exists_form_ne_zero (I : Submodule (ZMod N) M) {z : M} (hz : z ∉ I) :
    ∃ f : M →ₗ[ZMod N] ZMod N, (∀ x ∈ I, f x = 0) ∧ f z ≠ 0 := by
  obtain ⟨d, hd, hI⟩ :=
    zmod_ideal_gen (LinearMap.ker (LinearMap.toSpanSingleton (ZMod N) (M ⧸ I) (I.mkQ z)))
  have hw : ∃ w : ZMod N, w * d = 0 ∧ w ≠ 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨c, hc⟩ := zmod_dbl_ann d 1 (fun r hr => by rw [hne r hr, zero_mul])
    have h0 : d • I.mkQ z = 0 := hd
    have h1 : I.mkQ z = 0 := by
      rw [← one_smul (ZMod N) (I.mkQ z), hc, mul_smul, h0, smul_zero]
    exact hz (by simpa using h1)
  obtain ⟨w, hw, hw0⟩ := hw
  obtain ⟨t, ht⟩ := zmod_extend (LinearMap.toSpanSingleton (ZMod N) (M ⧸ I) (I.mkQ z))
    (LinearMap.toSpanSingleton (ZMod N) (ZMod N) w) (fun a ha => by
      obtain ⟨r, rfl⟩ := hI a ha
      rw [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_assoc, mul_comm d w, hw, mul_zero])
  refine ⟨t ∘ₗ I.mkQ, fun x hx => ?_, ?_⟩
  · have : I.mkQ x = 0 := by simpa using hx
    rw [LinearMap.comp_apply, this, map_zero]
  · have := ht 1
    rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, one_smul, one_smul] at this
    rw [LinearMap.comp_apply, this]
    exact hw0

end KStar.Selmer
end

