module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealTranslateIsMinNormTensorInOrbit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosure
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma ringEquiv_eval_eq_eval_map {σ : Type} (e : ℂ ≃+* ℂ) (x : σ → ℂ)
    (p : MvPolynomial σ ℂ) :
    e (MvPolynomial.eval x p) =
      MvPolynomial.eval (fun i => e (x i)) (MvPolynomial.map (e : ℂ →+* ℂ) p) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
  exact MvPolynomial.hom_eval₂ p (RingHom.id ℂ) (e : ℂ →+* ℂ) x

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma ev_eq_evC_map_algebraMap {ι : Type} (p : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) :
    _root_.GlobalTheory.ClassFin.ev p g =
      _root_.GlobalTheory.ClassFin.evC (MvPolynomial.map (algebraMap ℚ ℂ) p) g := by
  unfold _root_.GlobalTheory.ClassFin.ev _root_.GlobalTheory.ClassFin.evC
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma mem_span_rational_of_vanishing {ι : Type} (Γ : Set (Matrix ι ι ℂ))
    (hΓ : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : ∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC f g = 0) :
    f ∈ Submodule.span ℂ {w | ∃ p ∈ _root_.GlobalTheory.ClassFin.vanI Γ,
      MvPolynomial.map (algebraMap ℚ ℂ) p = w} := by
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {w | ∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC w g = 0}
      add_mem' := fun {a b} ha hb g hg => by
        simp only [_root_.GlobalTheory.ClassFin.evC, map_add (f := _)] at *
        rw [ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by simp [_root_.GlobalTheory.ClassFin.evC]
      smul_mem' := fun c w hw g hg => by
        simp only [_root_.GlobalTheory.ClassFin.evC, Set.mem_setOf_eq] at *
        rw [MvPolynomial.smul_eval, hw g hg, mul_zero] }
  have hstable : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr w' k =
        σ ((MvPolynomial.basisMonomials (ι × ι) ℂ).repr w k) := by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, fun g hg => ?_, fun k => MvPolynomial.coeff_map _ _ _⟩
    have h := hw (g.map σ.symm) (hΓ σ.symm g hg)
    have h2 := ringEquiv_eval_eq_eval_map σ (fun ij => (g.map σ.symm) ij.1 ij.2) w
    simp only [_root_.GlobalTheory.ClassFin.evC] at h ⊢
    rw [h, map_zero] at h2
    simpa [Matrix.map_apply] using h2.symm
  have hle := _root_.GlobalTheory.ClassFin.GaloisDescent.le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ)
    W hstable
  refine Submodule.span_mono ?_ (hle hf)
  rintro w ⟨hwW, hrat⟩
  have hrange : w ∈ Set.range (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
    obtain ⟨q, hq⟩ := hrat n
    exact ⟨q, hq.symm⟩
  obtain ⟨p, rfl⟩ := hrange
  refine ⟨p, fun g hg => ?_, rfl⟩
  rw [ev_eq_evC_map_algebraMap]
  exact hwW g hg


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) →
    ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC f g = 0) →
    ∀ y ∈ _root_.GlobalTheory.ClassFin.pts Γ ℂ, _root_.GlobalTheory.ClassFin.evC f y = 0 := by
  intro ι _ _ Γ hΓ f hf y hy
  have hspan := mem_span_rational_of_vanishing Γ hΓ f hf
  clear hf
  induction hspan using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, hp, rfl⟩ := hw
    rw [← ev_eq_evC_map_algebraMap]
    exact hy p hp
  | zero => simp [_root_.GlobalTheory.ClassFin.evC]
  | add a b _ _ ha hb =>
    simp only [_root_.GlobalTheory.ClassFin.evC, map_add (f := _)] at *
    rw [ha, hb, add_zero]
  | smul c w _ hw =>
    simp only [_root_.GlobalTheory.ClassFin.evC] at *
    rw [MvPolynomial.smul_eval, hw, mul_zero]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspaceStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) → ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  first | exact @GlobalTheory.ClassFin.exists_rat_idempotent_of_stable | exact GlobalTheory.ClassFin.exists_rat_idempotent_of_stable | (intros; apply GlobalTheory.ClassFin.exists_rat_idempotent_of_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatLinearParamBlockDiagKernel
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem corner_mul_corner {A : Type} [Ring A] (E x y : A) (hE : E * E = E)
    (hx : E * x * (1 - E) = x) (hy : E * y * (1 - E) = y) : x * y = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc x * y = (E * x * (1 - E)) * (E * y * (1 - E)) := by rw [hx, hy]
    _ = E * x * ((1 - E) * E) * y * (1 - E) := by simp only [mul_assoc]
    _ = 0 := by rw [h]; simp

theorem exists_linExt_corner_proj : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ ∀ ε : Matrix ι ι ℂ, 1 + ε ∈ Γ → e.map (algebraMap ℚ ℂ) * ε * (1 - e.map (algebraMap ℚ ℂ)) = ε → linExt c ε = ε := by
  intro ι _ _ Γ e hΓ he
  set E : Matrix ι ι ℂ := e.map (algebraMap ℚ ℂ) with hEdef
  have hE : E * E = E := by
    rw [hEdef, ← Matrix.map_mul, he]
  let S : Submodule ℂ (Matrix ι ι ℂ) :=
    { carrier := {ε | 1 + ε ∈ Γ ∧ E * ε * (1 - E) = ε}
      zero_mem' := ⟨by simpa using hΓ.one_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨?_, by rw [mul_add, add_mul, hx2, hy2]⟩
        have h0 := corner_mul_corner E x y hE hx2 hy2
        have h1 := hΓ.mul_mem _ hx1 _ hy1
        have h2 : (1 + x) * (1 + y) = 1 + (x + y) := by
          rw [mul_add, add_mul, add_mul, h0]; simp [add_assoc]
        rwa [h2] at h1
      smul_mem' := by
        rintro t x ⟨hx1, hx2⟩
        refine ⟨_root_.GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero ι Γ hΓ x (corner_mul_corner E x x hE hx2 hx2) hx1 t, ?_⟩
        rw [Matrix.mul_smul, Matrix.smul_mul, hx2] }
  have hS : ∀ σ : ℂ ≃+* ℂ, ∀ x ∈ S, x.map σ ∈ S := by
    rintro σ x ⟨hx1, hx2⟩
    have hEσ : (σ : ℂ →+* ℂ).mapMatrix E = E := by
      ext i j
      simp [hEdef]
    have hx : x.map σ = (σ : ℂ →+* ℂ).mapMatrix x := rfl
    refine ⟨?_, ?_⟩
    · have h1 := hΓ.aut_mem σ _ hx1
      have h2 : (1 + x).map σ = (σ : ℂ →+* ℂ).mapMatrix (1 + x) := rfl
      rw [h2, map_add (f := _), map_one] at h1
      exact h1
    · have h3 := congrArg (σ : ℂ →+* ℂ).mapMatrix hx2
      rw [map_mul, map_mul, map_sub, map_one, hEσ] at h3
      exact h3
  obtain ⟨c, hc1, hc2⟩ := _root_.GlobalTheory.ClassFin.RatProj.exists_rat_projector ι S hS
  exact ⟨c, fun X => hc1 X, fun ε h1 h2 => hc2 ε ⟨h1, h2⟩⟩

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCorrectionCongruentOneAtLevel
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Correct

variable {E : Type} [Field E] {n : ℕ}

theorem exists_nat_mulVec_mem [NumberField E] (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • (M *ᵥ v) ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem
  | exact _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem
  | (apply _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem ..)

theorem congAt_mul {L : Submodule (𝓞 E) (Fin n → E)} {N D : ℕ} {A B : Matrix (Fin n) (Fin n) E}
    (hA : CongAt L N D A) (hB : CongAt L N D B) : CongAt L N D (A * B) := by
  obtain ⟨t₁, c₁, h₁⟩ := hA
  obtain ⟨t₂, c₂, h₂⟩ := hB
  refine ⟨t₁ * t₂, Nat.Coprime.mul_left c₁ c₂, fun v hv => ?_⟩
  obtain ⟨w₂, hw₂, e₂⟩ := h₂ v hv
  have hy : t₂ • (B *ᵥ v) ∈ L := by
    have : t₂ • (B *ᵥ v) = t₂ • v + D • w₂ := by rw [← e₂, smul_sub]; abel
    rw [this]
    exact L.add_mem (nsmul_mem hv _) (nsmul_mem hw₂ _)
  obtain ⟨w₁, hw₁, e₁⟩ := h₁ _ hy
  refine ⟨w₁ + t₁ • w₂, L.add_mem hw₁ (nsmul_mem hw₂ _), ?_⟩
  rw [smul_add, smul_comm D t₁, ← e₁, ← e₂, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  module

theorem congAt_conj [CharZero E] {L : Submodule (𝓞 E) (Fin n → E)} {N D d e : ℕ} (he : 0 < e)
    {A R R' : Matrix (Fin n) (Fin n) E} (hRR : R * R' = 1)
    (hR : ∀ v ∈ L, d • (R *ᵥ v) ∈ L) (hR' : ∀ v ∈ L, e • (R' *ᵥ v) ∈ L)
    (hA : CongAt L N (D * d * e) A) : CongAt L N D (R * A * R') := by
  obtain ⟨t, ct, h⟩ := hA
  refine ⟨t, ct, fun v hv => ?_⟩
  obtain ⟨w, hw, e₁⟩ := h _ (hR' v hv)
  refine ⟨_, hR w hw, ?_⟩
  have e₂ := congrArg (fun z => R *ᵥ z) e₁
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec] at e₂
  have he' : (e : E) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  apply smul_right_injective (Fin n → E) he'
  simp only [Nat.cast_smul_eq_nsmul]
  rw [Matrix.mul_assoc]
  linear_combination (exp := 1) e₂

theorem splitOr_mul {F : Type} [Field F] [Algebra F E] {c : E ≃ₐ[F] E} {N : ℕ} {s t : 𝓞 E}
    (hs : SplitOr c N s) (ht : SplitOr c N t) : SplitOr c N (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, fun P hP h => (hP.mem_or_mem h).elim (hs.2 P hP) (ht.2 P hP)⟩

theorem smul_mul_mem {L : Submodule (𝓞 E) (Fin n → E)} {s t : 𝓞 E} {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ v ∈ L, s • (A *ᵥ v) ∈ L) (hB : ∀ v ∈ L, t • (B *ᵥ v) ∈ L) (v : Fin n → E) (hv : v ∈ L) :
    (s * t) • ((A * B) *ᵥ v) ∈ L := by
  have := hA _ (hB v hv)
  rwa [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_smul] at this

theorem exists_unitary_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL γ₀ N D hγ₀ hN hD
  obtain ⟨l, hl, hprod⟩ := _root_.GlobalTheory.UnRep.isUnE_eq_prod_refl F E c n G hG _ hγ₀
  clear hγ₀
  induction l generalizing γ₀ D with
  | nil =>
    have h1 : γ₀ = 1 := Units.ext (by simpa using hprod)
    subst h1
    refine ⟨1, fun x y => by simp, ⟨1, by simp, fun v _ => ⟨0, L.zero_mem, by simp⟩⟩, 1,
      ⟨one_ne_zero, fun P hP h => absurd ((Ideal.eq_top_iff_one P).2 h) hP.ne_top⟩, fun v hv => ?_⟩
    simpa using hv
  | cons p l ih =>
    obtain ⟨x, u⟩ := p
    obtain ⟨hx, hu⟩ := hl (x, u) List.mem_cons_self
    simp only at hx hu
    obtain ⟨-, r1, rmul, run⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG x hx
    have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
    let R : (a : E) → a ≠ 0 → GL (Fin n) E := fun a ha =>
      ⟨refl c G x a, refl c G x a⁻¹, by rw [rmul, mul_inv_cancel₀ ha, r1],
        by rw [rmul, inv_mul_cancel₀ ha, r1]⟩
    obtain ⟨d, hd, hRd⟩ := exists_nat_mulVec_mem L hfg hL (R u hu0).1
    obtain ⟨e, he, hRe⟩ := exists_nat_mulVec_mem L hfg hL ((R u hu0)⁻¹).1
    obtain ⟨γ₁, hγ₁, hc₁, s₁, hs₁, hL₁⟩ := ih ((R u hu0)⁻¹ * γ₀) (D * d * e)
      (Nat.mul_pos (Nat.mul_pos hD hd) he) (fun p hp => hl p (List.mem_cons_of_mem _ hp)) (by
        rw [Units.val_mul, hprod, List.map_cons, List.prod_cons, ← mul_assoc]
        change _ = _
        have : ((R u hu0)⁻¹).1 * refl c G x u = 1 := (R u hu0).inv_mul
        rw [this, one_mul])
    obtain ⟨u', hu', hc', s', hs', hL'⟩ := _root_.GlobalTheory.UnRep.exists_refl_correction F E c n G hG L hfg hL x u N D hx hu hN hD
    have hu'0 : u' ≠ 0 := left_ne_zero_of_mul_eq_one hu'
    refine ⟨R u' hu'0 * γ₁, ?_, ?_, s' * s₁, splitOr_mul hs' hs₁, fun v hv => ⟨?_, ?_⟩⟩
    · intro y z
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact (run u' hu' _ _).trans (hγ₁ y z)
    · have hconj := congAt_conj he (R u hu0).mul_inv hRd hRe hc₁
      have h := congAt_mul hc' hconj
      have e1 : refl c G x (u' / u) = (R u' hu'0 * (R u hu0)⁻¹).1 := by
        rw [div_eq_mul_inv, ← rmul]; rfl
      rw [e1, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul] at h
      convert h using 2
      group
    · rw [Units.val_mul]
      exact smul_mul_mem (fun v hv => (hL' v hv).1) (fun v hv => (hL₁ v hv).1) v hv
    · rw [mul_inv_rev, Units.val_mul, mul_comm s']
      exact smul_mul_mem (fun v hv => (hL₁ v hv).2) (fun v hv => (hL' v hv).2) v hv

end GlobalTheory.UnRep.Correct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteIntegralClassesClosedOrbit
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem finite_bdd_denominator_vectors {κ : Type} [Fintype κ] (D : ℕ) (hD : 0 < D) (B : ℝ) :
    {w : κ → ℚ | (∀ k, ∃ z : ℤ, (D : ℚ) * w k = z) ∧ nsq (fun k => ((w k : ℚ) : ℂ)) ≤ B}.Finite := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge ((D : ℝ) * (B + 1))
  have hDq : (D : ℚ) ≠ 0 := by positivity
  have hfin : ((fun z : ℤ => (z : ℚ) / D) '' (Set.Icc (-(N : ℤ)) N)).Finite :=
    (Set.finite_Icc _ _).image _
  refine (Set.Finite.pi' (fun _ : κ => hfin)).subset ?_
  rintro w ⟨hw, hB⟩ k
  obtain ⟨z, hz⟩ := hw k
  refine ⟨z, ?_, ?_⟩
  · have h1 : ‖((w k : ℚ) : ℂ)‖ ^ 2 ≤ B := by
      refine le_trans ?_ hB
      exact Finset.single_le_sum (f := fun k => ‖((w k : ℚ) : ℂ)‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ k)
    have h2 : ‖((w k : ℚ) : ℂ)‖ = |(w k : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    rw [h2] at h1
    have h3 : |(w k : ℝ)| ≤ B + 1 := by nlinarith [abs_nonneg (w k : ℝ), sq_nonneg (|(w k : ℝ)| - 1)]
    have h4 : (z : ℝ) = D * (w k : ℝ) := by exact_mod_cast hz.symm
    have h5 : |(z : ℝ)| ≤ N := by
      rw [h4, abs_mul, Nat.abs_cast]
      exact le_trans (mul_le_mul_of_nonneg_left h3 (by positivity)) hN
    have h6 : |z| ≤ (N : ℤ) := by exact_mod_cast h5
    exact abs_le.mp h6
  · simp only
    rw [← hz]; field_simp

theorem finite_integral_classes_closed_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) → ∀ D : ℕ, 0 < D → ∃ Z : Finset (TIdx ι d → ℚ), ∀ h : Matrix ι ι ℚ, h.det = 1 → (∀ k, ∃ z : ℤ, (D : ℚ) * act d t h k = z) → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ act d t (h * γ.map (Int.cast : ℤ → ℚ)) ∈ Z := by
  intro ι _ _ m d t hcl D hD
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hC := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d
  have hQ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℚ).2 m d
  set tC : TIdx ι d → ℂ := fun k => ((t k : ℚ) : ℂ) with htC
  have htR : (fun k => (((t k : ℚ) : ℝ) : ℂ)) = tC := by
    funext k; simp [htC]
  obtain ⟨g, hg, hmin⟩ := _root_.GlobalTheory.ClassFin.exists_real_translate_isMinVec ι m d (fun k => ((t k : ℚ) : ℝ))
    (by rw [htR]; exact GlobalTheory.T.exists_minNormTensor_of_isClosed_tensorSLOrbit ι m d tC hcl)
  rw [htR] at hmin
  have hmap : ∀ x y : Matrix ι ι ℝ, (x * y).map (fun r : ℝ => (r : ℂ)) =
      x.map (fun r : ℝ => (r : ℂ)) * y.map (fun r : ℝ => (r : ℂ)) := fun x y =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have hgg : g * g.adjugate = 1 := by rw [mul_adjugate, hg, one_smul]
  set gC : Matrix ι ι ℂ := g.map (fun r : ℝ => (r : ℂ)) with hgC
  have hgCd : gC.det = 1 := by
    have := (RingHom.map_det Complex.ofRealHom g)
    rw [hg, map_one] at this
    exact this.symm
  have hgCadj : gC * gC.adjugate = 1 := by rw [mul_adjugate, hgCd, one_smul]
  set v := act d tC gC with hv
  have horb : orb d v = orb d tC := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨gC * y, by rw [det_mul, hgCd, hy, one_mul], by rw [(hC tC).2.1]⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨gC.adjugate * y, by rw [det_mul, det_adjugate, hgCd, hy, one_pow, one_mul], ?_⟩
      rw [hv, ← (hC tC).2.1, ← mul_assoc, hgCadj, one_mul]
  obtain ⟨C, hSieg⟩ := _root_.GlobalTheory.ClassFin.siegel_cover ι
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.ClassFin.SiegelBound.borel_harishChandra ι m d v (_root_.GlobalTheory.ClassFin.orbit_proper_of_isClosed ι m d v (horb ▸ hcl))
    (_root_.GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec ι m d v hmin) C (1 / D) (by positivity)
  refine ⟨(finite_bdd_denominator_vectors (κ := TIdx ι d) D hD B).toFinset, ?_⟩
  intro h hh hint
  have hhR : (h.map (fun q : ℚ => (q : ℝ))).det = 1 := by
    have := (RingHom.map_det (Rat.castHom ℝ) h)
    rw [hh, map_one] at this
    exact this.symm
  obtain ⟨γ, hγ, k, a, n, hS, hkan⟩ := hSieg (g.adjugate * h.map (fun q : ℚ => (q : ℝ)))
    (by rw [det_mul, det_adjugate, hg, hhR, one_pow, one_mul])
  refine ⟨γ, hγ, ?_⟩
  set w := act d t (h * γ.map (Int.cast : ℤ → ℚ)) with hw
  have hwint : ∀ j, ∃ z : ℤ, (D : ℚ) * w j = z := by
    intro j
    have h1 := (hQ ((D : ℚ) • act d t h)).2.2.2.1 (Int.castRingHom ℚ).range
      (γ.map (Int.cast : ℤ → ℚ)) (fun k => by
        obtain ⟨z, hz⟩ := hint k
        exact ⟨z, hz.symm⟩) (fun i j => ⟨γ i j, rfl⟩) j
    rw [(hQ _).2.2.2.2.1, ← (hQ t).2.1] at h1
    obtain ⟨z, hz⟩ := h1
    exact ⟨z, hz.symm⟩
  have hact : act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) = fun j => ((w j : ℚ) : ℂ) := by
    rw [← hkan, hv, ← (hC tC).2.1, hgC, ← hmap, ← mul_assoc, ← mul_assoc, hgg, one_mul]
    have h2 := (hQ t).2.2.2.2.2 ℂ (Rat.castHom ℂ) (h * γ.map (Int.cast : ℤ → ℚ))
    have h3 : (h.map (fun q : ℚ => (q : ℝ)) * γ.map (Int.cast : ℤ → ℝ)).map (fun r : ℝ => (r : ℂ)) =
        (h * γ.map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℂ) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [h3]
    exact h2
  rw [Set.Finite.mem_toFinset]
  refine ⟨hwint, ?_⟩
  rw [← hact]
  refine hB k a n hS ?_
  intro j
  rw [hact]
  obtain ⟨z, hz⟩ := hwint j
  by_cases hz0 : z = 0
  · left
    have : w j = 0 := by
      rw [hz0] at hz
      have hDq : (D : ℚ) ≠ 0 := by positivity
      simpa [hD.ne'] using hz
    simp [this]
  · right
    have h2 : ‖((w j : ℚ) : ℂ)‖ = |(w j : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    have h4 : (z : ℝ) = D * (w j : ℝ) := by exact_mod_cast hz.symm
    have h5 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
    show 1 / (D : ℝ) ≤ ‖((w j : ℚ) : ℂ)‖
    rw [h2, div_le_iff₀ (by positivity)]
    rw [h4, abs_mul, Nat.abs_cast] at h5
    linarith

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem span_range_toMatrix_eq_top_of_isIrreducible {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (b : Module.Basis ι ℂ V) (h : ρ.IsIrreducible) :
    Submodule.span ℂ (Set.range
      ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ)) = ⊤ := by
  have : FiniteDimensional ℂ V := Module.Finite.of_basis b
  have h1 := span_range_eq_top_of_isIrreducible G V ρ h
  have h2 : Set.range ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ) =
      (LinearMap.toMatrix b b).toLinearMap '' Set.range ρ := by
    rw [← Set.range_comp]; rfl
  rw [h2, ← Submodule.map_span, h1, Submodule.map_top, LinearMap.range_eq_top]
  exact (LinearMap.toMatrix b b).surjective

theorem isSemisimpleRepresentation_tprod_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsIrreducible → ρ'.IsIrreducible → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  intro G _ V _ _ ρ W _ _ ρ' _ _ h h'
  let b := Module.finBasis ℂ V
  let b' := Module.finBasis ℂ W
  have key := _root_.GlobalTheory.ClassFin.ss_kronecker_of_span_top _ _ G _ _ (span_range_toMatrix_eq_top_of_isIrreducible ρ b h)
    (span_range_toMatrix_eq_top_of_isIrreducible ρ' b' h')
  rw [← ss_range_toMatrix_iff_isSemisimpleRepresentation _ G _ _ (b.tensorProduct b')]
  convert key using 3 with g
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  rfl

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletionStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) (L : Type) [Field L] [Algebra (v.adicCompletion F) L] [FiniteDimensional (v.adicCompletion F) L], 0 < p → v.valuation F (p : F) = WithZero.exp (-(e : ℤ)) → pTor p (⊤ : Subgroup Lˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Lˣ) = p * (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L * pTor p (⊤ : Subgroup Lˣ) := by
  first | exact @GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion | exact GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion | (intros; apply GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion <;> assumption)
end

