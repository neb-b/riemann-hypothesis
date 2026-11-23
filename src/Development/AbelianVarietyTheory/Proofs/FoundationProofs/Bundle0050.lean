module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisDenseTauPowMulFixingQRoots
section
noncomputable section

namespace GlobalTheory.K5.Dense

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isClosed_eval_mem {K : Type*} [Field K] [Algebra K Ω] [Algebra.IsIntegral K Ω]
    (x : Ω) (s : Set Ω) : IsClosed {σ : Ω ≃ₐ[K] Ω | σ x ∈ s} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)), ?_,
    (stabilizer_isOpen_of_isIntegral x).preimage (by fun_prop), ?_⟩
  · intro τ hτ
    have h : σ.symm (τ x) = x := hτ
    have h' : τ x = σ x := by rw [← σ.symm_apply_eq.1 h]
    simpa [h'] using hσ
  · simp

theorem exists_of_seq (h : IsClo p Ω) (P : ℕ → Ω → Set Ω)
    (hP : ∀ n, ∃ σ : Gal p Ω, ∀ m ≤ n, ∀ x, σ x ∈ P m x) :
    ∃ σ : Gal p Ω, ∀ n x, σ x ∈ P n x := by
  classical
  let K := FractionRing (O0 p)
  letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra
  have hK : ∀ a : O0 p, algebraMap K Ω (algebraMap (O0 p) K a) = algebraMap (O0 p) Ω a :=
    fun a => IsFractionRing.lift_algebraMap h.inj a
  haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq (fun a => (hK a).symm)
  haveI : IsAlgClosed Ω := h.clo
  haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg
  haveI : Algebra.IsAlgebraic K Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)
  haveI : IsAlgClosure K Ω := ⟨h.clo, inferInstance⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap h.inj
  haveI : CharZero K := RingHom.charZero (algebraMap K Ω)
  haveI : IsGalois K Ω := {}
  have hfix : ∀ σ : Gal p Ω, ∀ y : K, σ (algebraMap K Ω y) = algebraMap K Ω y := by
    intro σ y
    have e : ((σ : Ω →+* Ω).comp (algebraMap K Ω)) = algebraMap K Ω := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (O0 p))
      ext a
      simp only [RingHom.comp_apply, hK]
      exact σ.commutes a
    exact congrArg (fun f : K →+* Ω => f y) e
  let φ : Gal p Ω → (Ω ≃ₐ[K] Ω) := fun σ => AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (hfix σ)
  have hφ : ∀ σ x, φ σ x = σ x := fun _ _ => rfl
  let G : ℕ → Set (Ω ≃ₐ[K] Ω) := fun n => {τ | ∀ m ≤ n, ∀ x, τ x ∈ P m x}
  have hcl : ∀ n, IsClosed (G n) := fun n => by
    have e : G n = ⋂ m, ⋂ (_ : m ≤ n), ⋂ x, {τ : Ω ≃ₐ[K] Ω | τ x ∈ P m x} := by
      ext τ; simp [G]
    rw [e]
    exact isClosed_iInter fun m => isClosed_iInter fun _ => isClosed_iInter fun x =>
      isClosed_eval_mem x _
  have hdec : ∀ n, G (n + 1) ⊆ G n := fun n τ hτ m hm x => hτ m (hm.trans n.le_succ) x
  have hne : ∀ n, (G n).Nonempty := fun n => by
    obtain ⟨σ, hσ⟩ := hP n
    exact ⟨φ σ, fun m hm x => by rw [hφ]; exact hσ m hm x⟩
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed G hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hτ
  exact ⟨τ.restrictScalars (O0 p), fun n x => hτ n n le_rfl x⟩

theorem exists_finset_orbit (h : IsClo p Ω) (x : Ω) : ∃ R : Finset Ω, ∀ σ : Gal p Ω, σ x ∈ R := by
  classical
  obtain ⟨P, hP0, hPx⟩ := h.alg.isAlgebraic x
  refine ⟨(P.aroots Ω).toFinset, fun σ => ?_⟩
  rw [Multiset.mem_toFinset, mem_aroots']
  refine ⟨(Polynomial.map_ne_zero_iff h.inj).2 hP0, ?_⟩
  have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[O0 p] Ω) x P
  simp only [AlgEquiv.coe_algHom] at e
  rw [e, hPx, map_zero]

theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp (p := p) (T.ζ n) := by
  refine ⟨X ^ (p ^ n) - C 1, X_pow_sub_C_ne_zero (pow_pos hp.out.pos n) 1, ?_⟩
  simp [(T.prim n).pow_eq_one]

theorem qq_pow_sub (T : Tower p Ω) {n m : ℕ} (h : n ≤ m) : T.qq m ^ p ^ (m - n) = T.qq n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, T.qpow, ih]

theorem ggeo_apply {g : Gal p Ω} (hg : g ∈ Ggeo (p := p) Ω) {x : Ω} (hx : IsAlgZp (p := p) x) : g x = x := hg x hx

theorem tau_pow_qq (T : Tower p Ω) {τ : Gal p Ω} (hτ : τ ∈ Ggeo (p := p) Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) (n s : ℕ) :
    (τ ^ s) (T.qq n) = T.ζ n ^ s * T.qq n := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih,
      ggeo_apply ((Ggeo (p := p) Ω).pow_mem hτ s) (isAlgZp_zeta T n), pow_succ]
    ring

theorem dense_tau_pow_mul (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (Ω : Type) [Field Ω]
    [Algebra (O0 p) Ω] (hΩ : IsClo p Ω) (T : Tower p Ω) (τ : Gal p Ω) (hτ : τ ∈ Ggeo (p := p) Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) :
    ∀ g ∈ Ggeo (p := p) Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo (p := p) Ω ⊓ ⨅ n, Gn T n,
      ∀ x ∈ S, (τ ^ s * h) x = g x := by
  classical
  intro g hg S
  have hs : ∀ n, ∃ s : ℕ, (τ ^ s) (T.qq n) = g (T.qq n) := by
    intro n
    have hq0 := Basic.qq_ne_zero T n
    have hqp : T.qq n ^ p ^ n ≠ 0 := pow_ne_zero _ hq0
    have e : (g (T.qq n) / T.qq n) ^ (p ^ n) = 1 := by
      rw [div_pow, ← map_pow, Basic.qq_pow, AlgEquiv.commutes, ← Basic.qq_pow T n, div_self hqp]
    obtain ⟨i, -, hi⟩ := (T.prim n).eq_pow_of_pow_eq_one e
    exact ⟨i, by rw [tau_pow_qq T hτ hτq, hi, div_mul_cancel₀ _ hq0]⟩
  choose s hs using hs
  let σ : ℕ → Gal p Ω := fun n => (τ ^ s n)⁻¹ * g
  have hσG : ∀ n, σ n ∈ Ggeo (p := p) Ω := fun n =>
    (Ggeo (p := p) Ω).mul_mem ((Ggeo (p := p) Ω).inv_mem ((Ggeo (p := p) Ω).pow_mem hτ _)) hg
  have hσq : ∀ n, σ n (T.qq n) = T.qq n := by
    intro n
    show ((τ ^ s n)⁻¹ * g) (T.qq n) = T.qq n
    rw [AlgEquiv.mul_apply, ← hs n, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  choose R hR using fun x => exists_finset_orbit hΩ x
  let F : ℕ → ((x : S) → ↥(R x.1)) := fun n x => ⟨σ n x, hR x.1 (σ n)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber F
  have hinf : (F ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  obtain ⟨n₁, hn₁⟩ := hinf.nonempty
  have hS : ∀ m ∈ F ⁻¹' {y}, ∀ x ∈ S, σ m x = σ n₁ x := by
    intro m hm x hx
    have e : F m = F n₁ := (Set.mem_preimage.1 hm).trans (Set.mem_preimage.1 hn₁).symm
    exact congrArg Subtype.val (congrFun e ⟨x, hx⟩)
  let P : ℕ → Ω → Set Ω := fun n x =>
    {z | (IsAlgZp (p := p) x → z = x) ∧ (x ∈ S → z = σ n₁ x) ∧ (x = T.qq n → z = x)}
  have hP : ∀ n, ∃ ρ : Gal p Ω, ∀ m ≤ n, ∀ x, ρ x ∈ P m x := by
    intro n
    obtain ⟨m, hm, hnm⟩ := hinf.exists_gt n
    refine ⟨σ m, fun m' hm' x => ⟨fun hx => ggeo_apply (hσG m) hx, fun hx => hS m hm x hx, ?_⟩⟩
    rintro rfl
    rw [← qq_pow_sub T (hm'.trans hnm.le), map_pow, hσq m]
  obtain ⟨z, hz⟩ := exists_of_seq hΩ P hP
  refine ⟨s n₁, z, ?_, fun x hx => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨fun x hx => (hz 0 x).1 hx, Subgroup.mem_iInf.2 fun n => ?_⟩
    exact (Basic.mem_gn T n z).2 ⟨(hz 0 _).1 (isAlgZp_zeta T n), (hz n _).2.2 rfl⟩
  · rw [AlgEquiv.mul_apply, (hz 0 x).2.1 hx]
    show (τ ^ s n₁) (((τ ^ s n₁)⁻¹ * g) x) = g x
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

end GlobalTheory.K5.Dense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOne
section
noncomputable section

open scoped UpperHalfPlane
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Sieg.EisQ

theorem ee_int_mul' (n : ℤ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  simp only [ee, ← Complex.exp_int_mul]; congr 1; ring

theorem hasSum_point {M : ℕ} (hM : 0 < M) (a A e : ℤ) (w : ℤ → ℤ → ℂ) :
    HasSum (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0)
      (if A ≡ a [ZMOD M] then w A e else 0) := by
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  split_ifs with h
  · obtain ⟨n, hn⟩ := h.symm.dvd
    have hA : a + M * n = A := by linarith
    have := hasSum_single (f := fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0)
      (n, e) (fun p hp => by
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hp
        refine Prod.ext ?_ h1
        apply mul_left_cancel₀ hM'
        simp only
        linarith)
    simpa [hA] using this
  · have : (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0) = fun _ => 0 := by
      funext p
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact h (Int.ModEq.symm (Int.modEq_iff_dvd.2 ⟨p.1, by linarith⟩))
    rw [this]
    exact hasSum_zero

theorem sum_div_point {m : ℕ} (hm : m ≠ 0) (A e : ℤ) (v : ℂ) :
    ∑ d ∈ m.divisors, ((if e = (d : ℤ) ∧ A = ((m / d : ℕ) : ℤ) then v else 0) +
      (if e = -(d : ℤ) ∧ A = -((m / d : ℕ) : ℤ) then v else 0)) = if A * e = m then v else 0 := by
  have key : ∀ d ∈ m.divisors, (((m / d : ℕ) : ℤ)) * d = m ∧ 0 < (d : ℤ) := fun d hd => by
    refine ⟨?_, by exact_mod_cast Nat.pos_of_mem_divisors hd⟩
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  split_ifs with h
  · have hd : e.natAbs ∈ m.divisors := by
      rw [Nat.mem_divisors]
      refine ⟨?_, hm⟩
      rw [← Int.natCast_dvd_natCast, Int.natAbs_dvd]
      exact ⟨A, by rw [← h, mul_comm]⟩
    rw [Finset.sum_eq_single_of_mem _ hd]
    · obtain ⟨k1, k2⟩ := key _ hd
      generalize ((m / e.natAbs : ℕ) : ℤ) = B at *
      rcases Int.natAbs_eq e with he | he
      · rw [← he] at k1 k2 ⊢
        have : A = B := mul_right_cancel₀ k2.ne' (by rw [h, k1])
        rw [if_pos ⟨rfl, this⟩, if_neg (by omega), add_zero]
      · have he' : (e.natAbs : ℤ) = -e := by omega
        rw [he'] at k1 k2 ⊢
        have : A = -B := mul_right_cancel₀ (b := e) (by omega) (by rw [h, ← k1]; ring)
        rw [if_neg (by omega), if_pos ⟨by ring, this⟩, zero_add]
    · intro d _ hne
      rw [if_neg (by omega), if_neg (by omega), add_zero]
  · refine Finset.sum_eq_zero fun d hd => ?_
    obtain ⟨k1, k2⟩ := key _ hd
    rw [if_neg, if_neg, add_zero]
    · rintro ⟨h1, h2⟩
      exact h (by rw [h1, h2, ← k1]; ring)
    · rintro ⟨h1, h2⟩
      exact h (by rw [h1, h2, ← k1])

theorem fTerm_eq (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) (τ : ℍ) (p : ℤ × ℤ) :
    fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p =
      if 0 < (a + M * p.1) * p.2 then
        (Int.sign p.2 : ℂ) * (((a + M * p.1 : ℤ) : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * p.2) *
          ee ((((a + M * p.1) * p.2 : ℤ) : ℂ) * τ / M)
      else 0 := by
  have hQ : (0 : ℚ) < M := by exact_mod_cast hM
  have hC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc : (0 < ((a : ℚ) / M + p.1) * p.2) ↔ 0 < (a + M * p.1) * p.2 := by
    have : ((a : ℚ) / M + p.1) * p.2 = (((a + M * p.1) * p.2 : ℤ) : ℚ) / M := by
      push_cast; field_simp
    rw [this, div_pos_iff_of_pos_right hQ, Int.cast_pos]
  unfold fTerm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  split_ifs with h
  · rw [← ee_int_mul', mul_right_comm]
    congr 1
    · congr 1
      · congr 2
        push_cast; field_simp
      · congr 1
        push_cast; ring
    · congr 1
      push_cast; field_simp
  · rfl

theorem hasSum_fibre (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) (τ : ℍ) (m : ℕ) :
    HasSum (Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m})
        (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ))
      ((if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m) *
        Complex.exp (2 * Real.pi * Complex.I * m * τ / M)) := by
  split_ifs with hm
  · have : Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m})
        (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ) = fun _ => 0 := by
      funext p
      rw [Set.indicator_apply_eq_zero]
      intro hp
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
      rw [fTerm_eq j hM, if_neg (by omega)]
    rw [this, zero_mul]
    exact hasSum_zero
  · set E := Complex.exp (2 * Real.pi * Complex.I * m * τ / M) with hE
    let w : ℤ → ℤ → ℂ := fun A e => (Int.sign e : ℂ) * ((A : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * e) * E
    have h1 := hasSum_sum (s := m.divisors) fun d _ =>
      (hasSum_point hM a ((m / d : ℕ) : ℤ) (d : ℤ) w).add (hasSum_point hM a (-((m / d : ℕ) : ℤ)) (-(d : ℤ)) w)
    convert (preTransparency := .reducible) h1 using 1
    · funext p
      classical
      rw [sum_div_point hm, Set.indicator_apply, fTerm_eq j hM]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases h : (a + M * p.1) * p.2 = m
      · rw [if_pos (by omega), if_pos (by omega), if_pos h, h]
        simp only [w, hE, ee]
        congr 2
        push_cast; ring
      · rw [if_neg (by omega), if_neg h]
    · unfold coefPos
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have s1 : Int.sign (d : ℤ) = 1 := Int.sign_eq_one_of_pos hd'
      simp only [w, Int.sign_neg, s1, mul_neg, Int.cast_neg, Int.cast_one, Int.cast_natCast, neg_div]
      split_ifs <;> ring

theorem fract_eq {M : ℕ} (a : ℤ) : Int.fract ((a : ℚ) / M) = frc M a := by
  unfold frc
  exact Int.fract_div_intCast_eq_div_intCast_mod

theorem eisensteinFxConstantTerm_rationalIndex_eq (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    f0 j ![(a : ℚ) / M, (b : ℚ) / M] = const0 j M (ee (1 / (M : ℂ))) a b := by
  have hQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have h0 : frc M a = 0 ↔ (M : ℤ) ∣ a := by
    unfold frc
    rw [div_eq_zero_iff, or_iff_left hQ, Int.cast_eq_zero, Int.dvd_iff_emod_eq_zero]
  have he : ee ((((b : ℚ) / M : ℚ)) : ℂ) = ee (1 / (M : ℂ)) ^ b := by
    rw [← ee_int_mul']; congr 1; push_cast; ring
  unfold f0 const0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fract_eq, h0, he]
  split_ifs
  · rfl
  · push_cast; ring
  · push_cast; ring

theorem hasQ_F (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    HasQ M (F j ![(a : ℚ) / M, (b : ℚ) / M]) (eisF j M (ee (1 / (M : ℂ))) a b) := by
  have h1 : HasQ M (fun τ => ∑' p : ℤ × ℤ, fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p)
      (fun m => if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m) := fun τ => by
    have := (Model.summable_fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ).hasSum.tsum_fiberwise
      (fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat)
    have e : ∀ m : ℕ, ∑' q : ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m}),
        fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ q = _ := fun m => by
      rw [tsum_subtype, (hasSum_fibre j hM a b τ m).tsum_eq]
    simpa only [e] using this
  have h2 := (HasQ.const M (f0 j ![(a : ℚ) / M, (b : ℚ) / M])).add h1
  have e : eisF j M (ee (1 / (M : ℂ))) a b = fun n => (if n = 0 then f0 j ![(a : ℚ) / M, (b : ℚ) / M] else 0) +
      (if n = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b n) := by
    funext n
    unfold eisF
    split_ifs
    · rw [eisensteinFxConstantTerm_rationalIndex_eq j hM, add_zero]
    · rw [zero_add]
  rw [e]
  exact h2

theorem hasQ_cF_weight (c j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    HasQ M (cF c j ![(a : ℚ) / M, (b : ℚ) / M]) (smF (c : ℤ) j M (ee (1 / (M : ℂ))) a b) := by
  have hx : c • ![(a : ℚ) / M, (b : ℚ) / M] = ![(((c : ℤ) * a : ℤ) : ℚ) / M, (((c : ℤ) * b : ℤ) : ℚ) / M] := by
    funext i
    fin_cases i <;> simp [mul_div_assoc]
  have := ((hasQ_F j hM a b).const_mul ((c : ℂ) ^ 2)).sub
    ((hasQ_F j hM (c * a) (c * b)).const_mul ((c : ℂ) ^ (2 - (j : ℤ))))
  rw [← hx] at this
  unfold smF
  simp only [Int.cast_natCast]
  exact this

theorem hasQ_cF_one : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M])
    (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) :=
  fun c _ a b hM => hasQ_cF_weight c 1 hM a b

end GlobalTheory.Sieg.EisQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTSlashInvariant
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HkInv
open GlobalTheory.HeckeFamilyMatrices

theorem reps (N l q : ℕ) (σ γ : SL(2, ℤ)) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ)
    (hγ : γ ∈ GlobalTheory.Hk.lev N l) (i : Fin (q + 1)) :
    ∃ i' : Fin (q + 1), ∃ γ' ∈ GlobalTheory.Hk.lev N l, tqFam q σ i * mat γ = mat γ' * tqFam q σ i' := by
  by_cases hi : (i : ℕ) < q
  · have e : tqFam q σ i = !![(1 : ℤ), ((i : ℕ) : ℤ); 0, (q : ℤ)] := by rw [tqFam, if_pos hi]
    rw [e]
    by_cases hd : (q : ℤ) ∣ mat γ 0 0 + ((i : ℕ) : ℤ) * mat γ 1 0
    · obtain ⟨γ', h1, h2⟩ := _root_.GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag N l q i σ γ hq hqN hσ hi hγ hd
      refine ⟨Fin.last q, γ', h1, ?_⟩
      rw [h2, tqFam, if_neg (by simp)]
    · obtain ⟨j', hj', γ', h1, h2⟩ := _root_.GlobalTheory.Hk.tinv_fin_fin N l q i γ hq hqN hi hγ hd
      refine ⟨⟨j', by omega⟩, γ', h1, ?_⟩
      rw [h2, tqFam, if_pos (by simpa using hj')]
  · have e : tqFam q σ i = mat σ * dg q 1 := by rw [tqFam, if_neg hi]
    rw [e]
    by_cases hd : (q : ℤ) ∣ mat γ 1 0
    · obtain ⟨γ', h1, h2⟩ := _root_.GlobalTheory.Hk.dia_diag_mul_of_dvd_lowerLeft N l q σ γ hq hqN hσ hγ hd
      refine ⟨Fin.last q, γ', h1, ?_⟩
      rw [h2, tqFam, if_neg (by simp)]
    · obtain ⟨j', hj', γ', h1, h2⟩ := _root_.GlobalTheory.HkInvFin.sigma_dg_mul_eq N l q σ γ hq hqN hσ hγ hd
      refine ⟨⟨j', by omega⟩, γ', h1, ?_⟩
      rw [h2, tqFam, if_pos (by simpa using hj')]

theorem perm (N l q : ℕ) (σ γ : SL(2, ℤ)) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ)
    (hγ : γ ∈ GlobalTheory.Hk.lev N l) :
    ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  choose π g hg he using reps N l q σ γ hq hqN hσ hγ
  have hinj : Function.Injective π := by
    intro i₁ i₂ h
    have e1 := he i₁
    have e2 := he i₂
    rw [h] at e1
    apply _root_.GlobalTheory.tqFam_cosets_distinct q σ (g i₁ * (g i₂)⁻¹) i₁ i₂ hq
    have hγi : mat γ * mat γ⁻¹ = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgi : mat (g i₂)⁻¹ * mat (g i₂) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc tqFam q σ i₁ = tqFam q σ i₁ * mat γ * mat γ⁻¹ := by rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
      _ = mat (g i₁) * (mat (g i₂)⁻¹ * (mat (g i₂) * tqFam q σ (π i₂))) * mat γ⁻¹ := by
          rw [e1, ← Matrix.mul_assoc (mat (g i₂)⁻¹), hgi, Matrix.one_mul]
      _ = mat (g i₁ * (g i₂)⁻¹) * (tqFam q σ i₂ * mat γ * mat γ⁻¹) := by
          rw [← e2, show mat (g i₁ * (g i₂)⁻¹) = mat (g i₁) * mat (g i₂)⁻¹ from Matrix.SpecialLinearGroup.coe_mul _ _]
          simp only [Matrix.mul_assoc]
      _ = mat (g i₁ * (g i₂)⁻¹) * tqFam q σ i₂ := by rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
  exact ⟨Equiv.ofBijective π hinj.bijective_of_finite, fun i => ⟨g i, hg i, he i⟩⟩

theorem det_tqFam (q : ℕ) (hq : 0 < q) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : (tqFam q σ i).det ≠ 0 := by
  unfold tqFam
  split_ifs
  · simp [Matrix.det_fin_two_of, hq.ne']
  · rw [Matrix.det_mul]; simp [dg, Matrix.det_fin_two_of, hq.ne']

theorem heckeT_slash_invariant : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → (∀ γ ∈ GlobalTheory.Hk.lev N l, f ∣[k] γ = f) →
    ∀ γ ∈ GlobalTheory.Hk.lev N l, GlobalTheory.Hk.heckeT k q σ f ∣[k] γ = GlobalTheory.Hk.heckeT k q σ f := by
  intro N l q k σ f _ hq hqN hσ hf γ hγ
  obtain ⟨π, hπ⟩ := perm N l q σ γ hq hqN hσ hγ
  have hq0 := hq.pos
  have hmat : (mat γ).det ≠ 0 := by simp [mat]
  rw [← GlobalTheory.SlashUpperTriangularMatrices.tq_eq k q σ f hq0, TqF, hkF]
  have key : ∀ i, (f ∣[k] toGL (tqFam q σ i)) ∣[k] γ = f ∣[k] toGL (tqFam q σ (π i)) := by
    intro i
    obtain ⟨γ', hγ', he⟩ := hπ i
    have hmat' : (mat γ').det ≠ 0 := by simp [mat]
    rw [ModularForm.SL_slash, ← SlashAction.slash_mul, ← GlobalTheory.SlashUpperTriangularMatrices.toGL_SL,
      ← GlobalTheory.SlashUpperTriangularMatrices.toGL_mul _ _ (det_tqFam q hq0 σ i) hmat, he,
      GlobalTheory.SlashUpperTriangularMatrices.toGL_mul _ _ hmat' (det_tqFam q hq0 σ _), SlashAction.slash_mul,
      GlobalTheory.SlashUpperTriangularMatrices.toGL_SL, ← ModularForm.SL_slash, hf γ' hγ']
  have hsum : ∀ (s : Finset (Fin (q + 1))) (F : Fin (q + 1) → ℍ → ℂ),
      (∑ i ∈ s, F i) ∣[k] γ = ∑ i ∈ s, F i ∣[k] γ := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simp [SlashAction.zero_slash]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  rw [hsum, Finset.sum_congr rfl (fun i _ => key i)]
  exact Equiv.sum_comp π (fun i => f ∣[k] toGL (tqFam q σ i))

end GlobalTheory.HkInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjMulExpEqConjQExpansionCoeffStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff : ∀ (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ), 0 < T → 0 < y → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) = T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral | exact GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral | (intros; apply GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacterStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → θ ≠ 0 → θ ^ N ∈ Set.range (algebraMap K Ω) →
  IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
  (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧ (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) := by
  first | exact @GlobalTheory.NeedB.KumLemma.kummer_character_main | exact GlobalTheory.NeedB.KumLemma.kummer_character_main | (intros; apply GlobalTheory.NeedB.KumLemma.kummer_character_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEqStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (N : Subgroup G) [Fintype (G ⧸ N)] (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, ∑ i, a i * cosetTrace N (b i * x) = c * x := by
  first | exact @GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq | exact GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq | (intros; apply GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq <;> assumption)
end

