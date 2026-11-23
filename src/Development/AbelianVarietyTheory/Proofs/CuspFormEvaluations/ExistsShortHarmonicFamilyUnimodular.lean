module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyLinear
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyFewColumnsLinear
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Harm

open MvPolynomial

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_iff_herm_of_unimod {n : ℕ} {Λ : GenLat E n} (h : Λ.Unimod) (x : Fin n → E) :
    x ∈ Λ.La ↔ ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y) := by
  have hI : ∀ z : E, IsIntegral ℤ z ↔ z ∈ (algebraMap (𝓞 E) E).range := fun z =>
    ⟨fun hz => ⟨⟨z, hz⟩, rfl⟩, fun ⟨o, ho⟩ => ho ▸ o.isIntegral_coe⟩
  have hc : ∀ z : E, IsIntegral ℤ (IsCMField.complexConj E z) ↔ IsIntegral ℤ z := by
    intro z
    constructor
    · intro hz
      have := hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
      simpa [IsCMField.complexConj_apply_apply] using this
    · intro hz
      exact hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  have key : ∀ y : Fin n → E, FD.herm 1 x y =
      IsCMField.complexConj E (∑ j, IsCMField.complexConj E (x j) * y j) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FD.herm, FD.cc, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
      IsCMField.complexConj_apply_apply]
  rw [h x]
  refine forall₂_congr fun y _ => ?_
  rw [key y, hc, hI]

theorem not_inPsi_and_conjugate (H : Host E) (τ : E →+* ℂ) :
    ¬ (InPsi H τ ∧ InPsi H (ComplexEmbedding.conjugate τ)) := by
  rintro ⟨h1, h2⟩
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1] at h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h2
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
    Complex.natCast_re] at hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [mul_self_nonneg H.rt0.re]

private theorem coe_embF {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : E) :
    ((embF c τ x : c.F) : ℂ) = τ x := rfl

theorem injective_embF_inPsi {H : Host E} {l : Level H} (c : Coeff l) :
    Function.Injective fun s : {τ : E →+* ℂ // InPsi H τ} × Bool =>
      fun x : E => embF c s.1.1 (if s.2 then FD.cc x else x) := by
  rintro ⟨⟨τ, hτ⟩, b⟩ ⟨⟨τ', hτ'⟩, b'⟩ h
  have hx : ∀ x : E, (if b then ComplexEmbedding.conjugate τ else τ) x =
      (if b' then ComplexEmbedding.conjugate τ' else τ') x := by
    intro x
    have := congrArg (fun z : c.F => (z : ℂ)) (congrFun h x)
    simp only [coe_embF] at this
    cases b <;> cases b' <;>
      simpa [FD.cc, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
        using this
  have hf : (if b then ComplexEmbedding.conjugate τ else τ) =
      (if b' then ComplexEmbedding.conjugate τ' else τ') := RingHom.ext hx
  cases b <;> cases b'
  · simp only [Bool.false_eq_true, if_false] at hf
    subst hf
    rfl
  · simp only [Bool.false_eq_true, if_false, if_true] at hf
    exact absurd ⟨hτ', by rw [← hf]; exact hτ⟩ (not_inPsi_and_conjugate H τ')
  · simp only [Bool.false_eq_true, if_false, if_true] at hf
    exact absurd ⟨hτ, by rw [hf]; exact hτ'⟩ (not_inPsi_and_conjugate H τ)
  · simp only [if_true] at hf
    have h2 := (ComplexEmbedding.involutive_conjugate E).injective hf
    subst h2
    rfl

theorem sum_norm_coeff_eq_l1Norm {K σ σ' : Type} [Field K] (e : σ ≃ σ') (f : K →+* ℂ)
    (Q : MvPolynomial σ K) :
    ∑ m ∈ Q.support, ‖f (Q.coeff m)‖ = MvPoly.l1Norm (MvPolynomial.map f (rename e Q)) := by
  rw [MvPolynomial.map_rename, MvPoly.l1Norm_rename_of_injective e.injective, MvPoly.l1Norm_map]

theorem log_le_of_le_of_log_le {x y B : ℝ} (hx : 0 ≤ x) (h : x ≤ y) (hy : Real.log y ≤ B)
    (hB : 0 ≤ B) : Real.log x ≤ B := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact hB
  · exact (Real.log_le_log hpos h).trans hy

end SlopeTestRemainingChoices

theorem exists_short_harmL_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.La.FG → Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ S : Finset (MvPolynomial (LtN Dw n) c.F), (∀ Q ∈ S, Q ∈ harmL c Λ a ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a) ∧ (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (S : Set (MvPolynomial (LtN Dw n) c.F))) ∧ S.card ≤ ((2 * (Dw.p + Dw.q) + 1) * DF Dw a + 1) ^ (2 * FD.fdeg E * n * (2 * Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l c n Λ hU hfg hn a L hL hrd hf hDF hnL
  classical
  let _ : Fintype {τ : E →+* ℂ // InPsi H τ} := Fintype.ofFinite _
  obtain ⟨e, hsym, hHH⟩ := theta_letter_dictionary E H Dw l c n
  have hint : ∀ x ∈ Λ.La, ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y) := fun x hx =>
    (mem_iff_herm_of_unimod hU x).1 hx
  have hdual : ∀ x, (∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y)) → x ∈ Λ.La := fun x hx =>
    (mem_iff_herm_of_unimod hU x).2 hx
  have hre : ∀ M : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F,
      rename e (rename e.symm M) = M := fun M => by
    rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
  have hre' : ∀ P : MvPolynomial (LtN Dw n) c.F, rename e.symm (rename e P) = P := fun P => by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
  rcases hHH a with hzero | ⟨k, k', hdeg, hiff⟩
  · refine ⟨∅, by simp, fun P hP => ?_, by simp⟩
    rw [hzero P hP]
    exact Submodule.zero_mem _
  rcases Nat.eq_zero_or_pos (DF Dw a) with h0 | hpos
  ·
    have hconst : ∀ P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
        (fun τ i => a (τ, i)) → P = C (P.coeff 0) := by
      intro P hP
      have h1 := isHomogeneous_of_mem_rowHighest ((hiff P).1 hP)
      rw [hdeg, h0] at h1
      have h2 : (rename e P).totalDegree = 0 := Nat.le_zero.1 h1.totalDegree_le
      have h3 : P.totalDegree = 0 := by
        have := totalDegree_rename_le e.symm (rename e P)
        rw [hre', h2] at this
        exact Nat.le_zero.1 this
      exact totalDegree_eq_zero_iff_eq_C.1 h3
    by_cases h1 : (1 : MvPolynomial (LtN Dw n) c.F) ∈
        HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    · refine ⟨{1}, fun Q hQ => ?_, fun P hP => ?_, ?_⟩
      · rw [Finset.mem_singleton] at hQ
        subst hQ
        refine ⟨⟨h1, Subring.one_mem _⟩, fun σ' => ?_⟩
        simp [h0]
      · rw [hconst P hP, ← mul_one (C (P.coeff 0)), ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · simp [h0]
    · refine ⟨∅, by simp, fun P hP => ?_, by simp⟩
      by_cases hr : P.coeff 0 = 0
      · rw [hconst P hP, hr, C_0]
        exact Submodule.zero_mem _
      · exfalso
        apply h1
        have hmem := (hiff P).1 hP
        rw [hconst P hP, rename_C] at hmem
        have h1' : (1 : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F)
            = C ((P.coeff 0)⁻¹ * P.coeff 0) := by
          rw [inv_mul_cancel₀ hr, C_1]
        rw [hiff, map_one, h1', C_mul, ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hmem

  have ha1 : 1 ≤ typeDegree k k' := by rw [hdeg]; exact hpos
  have det_mem_subalgebra_of_entries_mem' {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
      (S : Subalgebra A B) {m : ℕ} (M : Matrix (Fin m) (Fin m) B) (hM : ∀ i j, M i j ∈ S) :
      M.det ∈ S := by
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (Subalgebra.prod_mem _ fun i _ => hM _ _) _

  have minorProd_mem_Ha_of_herm_orthogonal {Λ₀ : Submodule (𝓞 E) (Fin n → E)} {K : Type} [Field K] {T : Type} [Fintype T] {p q : ℕ}
      (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (e : Fin p → Fin n → E)
      (f : Fin q → Fin n → E) (he : ∀ a, e a ∈ Λ₀) (hf : ∀ b, f b ∈ Λ₀)
      (hef : ∀ a b, FD.herm 1 (e a) (f b) = 0) :
      minorProd c c' (fun t a k => τ t (e a k)) (fun t b k => τ t (FD.cc (f b k))) ∈ GlobalTheory.Harm.symO p q τ Λ₀ := by
    unfold GlobalTheory.Harm.symO minorProd
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.mul_mem _
        (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
        (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · unfold xMinor
      exact det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inl ⟨t, _, e _, he _, rfl⟩)
    · unfold yMinor
      exact det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inr ⟨t, _, f _, hf _, rfl⟩)

  have local_short_family {Λ₀ : Submodule (𝓞 E) (Fin n → E)} (hfg : Λ₀.FG)
      (hint : ∀ x ∈ Λ₀, ∀ y ∈ Λ₀, IsIntegral ℤ (FD.herm 1 x y))
      (hdual : ∀ x, (∀ y ∈ Λ₀, IsIntegral ℤ (FD.herm 1 x y)) → x ∈ Λ₀)
      {p q : ℕ} (hn : p + q ≤ n) {T : Type} [Fintype T] (c : T → Fin p → ℕ)
      (c' : T → Fin q → ℕ) (ha : 1 ≤ typeDegree c c') :
      ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)),
        (∀ s ∈ S, (∀ a, s.1 a ∈ Λ₀) ∧ (∀ b, s.2 b ∈ Λ₀) ∧ ∀ a b, FD.herm 1 (s.1 a) (s.2 b) = 0) ∧
        (∀ (K : Type) [Field K] (τ : T → E →+* K), ∀ s ∈ S,
          (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (FD.cc (s.2 b k))) ∈
            GlobalTheory.Harm.symO p q τ Λ₀) ∧
        (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K),
          (Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then FD.cc x else x)) →
          Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) =>
            minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (FD.cc (s.2 b k))) '' S) =
            rowHighest K c c') ∧
        (∀ (τ : T → E →+* ℂ), ∀ s ∈ S,
          MvPoly.l1Norm (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (FD.cc (s.2 b k))) ≤
            (((p + q : ℕ) : ℝ) * Real.sqrt n * (((p + q) + 1).factorial * ((2 * FD.fdeg E * n) *
              ((2 * (p + q : ℕ) + 1) * typeDegree c c') *
              (2 * (FD.fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * FD.rdE E)) ^ (2 * (p + q) + 1))) ^
              typeDegree c c') ∧
        S.card ≤ ((2 * (p + q) + 1) * typeDegree c c' + 1) ^ (2 * FD.fdeg E * n * (2 * p + q)) := by
    classical
    obtain ⟨hfg', hint', hdual'⟩ := conjLattice_selfDual hfg hint hdual
    obtain ⟨S', hS'1, hS'2, hS'3, hS'4⟩ :=
      exists_short_harmonic_family_few_columns (Λ := conjLattice Λ₀) hfg' hint' hdual' hn c c' ha
    let cj : (Fin p → Fin n → E) × (Fin q → Fin n → E) → (Fin p → Fin n → E) × (Fin q → Fin n → E) :=
      fun s => (fun a => conjVec E n (s.1 a), fun b => conjVec E n (s.2 b))
    have hcc : ∀ x : E, FD.cc (FD.cc x) = x := fun x => by
      have := congrFun (conjVec_conjVec (E := E) (n := 1) (fun _ => x)) 0
      simpa only [conjVec_apply] using this
    have hpoly : ∀ (K : Type) [Field K] (τ : T → E →+* K) (s : (Fin p → Fin n → E) × (Fin q → Fin n → E)),
        minorProd c c' (fun t a k => τ t ((cj s).1 a k)) (fun t b k => τ t (FD.cc ((cj s).2 b k))) =
          minorProd c c' (fun t a k => τ t (FD.cc (s.1 a k))) (fun t b k => τ t (s.2 b k)) := by
      intro K _ τ s
      simp only [cj, conjVec_apply, hcc]
    have hmem : ∀ s ∈ S', (∀ a, (cj s).1 a ∈ Λ₀) ∧ (∀ b, (cj s).2 b ∈ Λ₀) ∧
        ∀ a b, FD.herm 1 ((cj s).1 a) ((cj s).2 b) = 0 := by
      intro s hs
      obtain ⟨h1, h2, h3⟩ := hS'1 s hs
      refine ⟨fun a => mem_conjLattice.mp (h1 a), fun b => mem_conjLattice.mp (h2 b), fun a b => ?_⟩
      simp only [cj]
      rw [herm_conjVec]
      exact h3 a b
    refine ⟨S'.image cj, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
      exact hmem s' hs'
    · intro K _ τ s hs
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨h1, h2, h3⟩ := hmem s' hs'
      exact minorProd_mem_Ha_of_herm_orthogonal τ c c' _ _ h1 h2 h3
    · intro K _ _ τ hτ
      rw [← hS'2 K τ hτ, Finset.coe_image, ← Set.image_comp]
      exact congrArg _ (Set.image_congr fun s _ => hpoly K τ s)
    · intro τ s hs
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
      rw [hpoly ℂ τ s']
      exact hS'3 τ s' hs'
    · exact Finset.card_image_le.trans hS'4
  obtain ⟨S0, _, hHa, hspan, hnorm, hcard⟩ := local_short_family hfg hint hdual hn k k' ha1
  have hinj := injective_embF_inPsi (H := H) c
  have hsp := hspan c.F (fun t => embF c t.1) hinj
  refine ⟨S0.image fun s => rename e.symm (minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
    fun t b kk => embF c t.1 (FD.cc (s.2 b kk))), fun Q hQ => ?_, fun P hP => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hQ
    have hM : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
        (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈ rowHighest c.F k k' := by
      rw [← hsp]
      exact Submodule.subset_span ⟨s, Finset.mem_coe.2 hs, rfl⟩
    have hS : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
        (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈
        GlobalTheory.Harm.symO Dw.p Dw.q (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La := by
      have := hHa c.F (fun t => embF c t.1) s hs
      exact this
    refine ⟨⟨(hiff _).2 (by rw [hre]; exact hM), (hsym Λ _).2 (by rw [hre]; exact hS)⟩,
      fun σ' => ?_⟩
    rw [sum_norm_coeff_eq_l1Norm e σ', hre, map_minorProd]
    have hb := hnorm (fun t => σ'.comp (embF c t.1)) s hs
    refine log_le_of_le_of_log_le (MvPoly.l1Norm_nonneg _) hb ?_ ?_
    · rw [hdeg]
      exact log_shortFamilyNumbers_le (Dw.p + Dw.q) n (DF Dw a) (FD.fdeg E) (FD.rdE E) L
        (one_le_add_of_one_le_typeDegree ha1) hn hpos one_le_fdeg one_le_rdE hL hrd hf hDF hnL
    · have hL0 : (0 : ℝ) ≤ L := by linarith
      positivity
  · have h1 : rename e P ∈ Submodule.span c.F ((fun s : (Fin Dw.p → Fin n → E) ×
        (Fin Dw.q → Fin n → E) => minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
          fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) '' ↑S0) := by
      rw [hsp]
      exact (hiff P).1 hP
    have h2 := Submodule.mem_map_of_mem
      (f := (rename (R := c.F) (⇑e.symm)).toLinearMap) h1
    rw [Submodule.map_span, ← Set.image_comp] at h2
    rw [Finset.coe_image]
    convert h2 using 1
    all_goals first
      | exact (hre' P).symm
      | simp
  · calc _ ≤ S0.card := Finset.card_image_le
      _ ≤ _ := by rw [← hdeg]; exact hcard

end GlobalTheory.Harm
