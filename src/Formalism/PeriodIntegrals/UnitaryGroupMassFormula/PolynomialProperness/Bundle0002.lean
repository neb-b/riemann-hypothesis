module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.AddLeMulPowOfSqLeOfLeMul
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness

lemma fmul_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) :
    fmul k r z 1 b = fvec k r z b := by
  simp [fmul, Matrix.one_apply]

lemma frame_mulVec_fmul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {σ : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) :
    σ *ᵥ fmul k r z c b = fmul k r z (v * c) b := by
  show σ *ᵥ (∑ a, c a b • fvec k r z a) = ∑ a, (v * c) a b • fvec k r z a
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.mulVecLin_apply, map_sum]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h, fmul, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm (c a b)]

lemma ut_det {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v.det = 1 := by
  rw [Matrix.det_of_upperTriangular hv.1]
  simp [hv.2]

lemma ut_mul_inv {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v * v⁻¹ = 1 := Matrix.mul_nonsing_inv v (by rw [ut_det hv]; exact isUnit_one)

lemma mx_nonneg {m : ℕ} (v : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ mx v := norm_nonneg _

lemma real_sq_bound {C CA m n x : ℝ} {e : ℕ} (hm : 0 ≤ m) (hmx : m ≤ CA * x ^ e) (hx : 1 ≤ x)
    (hn : n ≤ C * m ^ 2) : n ≤ |C| * CA ^ 2 * x ^ (2 * e) := by
  have h1 : m ^ 2 ≤ (CA * x ^ e) ^ 2 := pow_le_pow_left₀ hm hmx 2
  have h2 : C * m ^ 2 ≤ |C| * m ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg m)
  calc n ≤ C * m ^ 2 := hn
    _ ≤ |C| * m ^ 2 := h2
    _ ≤ |C| * (CA * x ^ e) ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * CA ^ 2 * x ^ (2 * e) := by ring

lemma add_le_mul_pow_of_sq_le_of_le_mul {Cc D a s sp x : ℝ} {e N : ℕ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hs1 : 1 ≤ s) (hx : 1 ≤ x)
    (hs : s ^ 2 ≤ Cc * (1 + D * x ^ (2 * e + 2)) ^ 2) (hsp : sp ≤ a * s * x) (hN : 4 * e + 5 ≤ N) :
    s + sp ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ s := by linarith
  set K := 2 * e + 2 with hK
  have hxK : 1 ≤ x ^ K := one_le_pow₀ hx
  have hA : 1 + D * x ^ K ≤ (1 + D) * x ^ K := by nlinarith
  have hA0 : 0 ≤ 1 + D * x ^ K := by nlinarith
  have hs_le : s ≤ s ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ |Cc| * ((1 + D) * x ^ K) ^ 2 := by
    calc s ^ 2 ≤ Cc * (1 + D * x ^ K) ^ 2 := hs
      _ ≤ |Cc| * (1 + D * x ^ K) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |Cc| * ((1 + D) * x ^ K) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA 2) (abs_nonneg _)
  have hsx : s ≤ |Cc| * (1 + D) ^ 2 * x ^ (2 * K) := by
    have e2 : ((1 + D) * x ^ K) ^ 2 = (1 + D) ^ 2 * x ^ (2 * K) := by ring
    rw [e2] at hs2
    nlinarith
  have hxN : x ^ (2 * K + 1) ≤ x ^ N := pow_le_pow_right₀ hx (by omega)
  have hB0 : 0 ≤ |Cc| * (1 + D) ^ 2 := by positivity
  calc s + sp ≤ s + a * s * x := by linarith
    _ ≤ (1 + a) * x * s := by nlinarith
    _ ≤ (1 + a) * x * (|Cc| * (1 + D) ^ 2 * x ^ (2 * K)) :=
        mul_le_mul_of_nonneg_left hsx (mul_nonneg (by linarith) hx0)
    _ = (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ (2 * K + 1) := by ring
    _ ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N :=
        mul_le_mul_of_nonneg_left hxN (mul_nonneg (by linarith) hB0)

theorem bound_core (hG : GVGroup) (hN : NormInv) (hNF : GNFacts)
    {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {Cf Cf' CA Cc : ℝ}
    (hCf : ∀ c b, nsq (fmul k r z c b) ≤ Cf * mx c ^ 2)
    (hCf' : ∀ c b, nsq (fmul k r z' c b) ≤ Cf' * mx c ^ 2)
    (hCc : ∀ s ∈ B.GV k r, ∀ K : ℝ, 0 ≤ K → (∀ i, nsq (s *ᵥ gramVec k r z z' γ i) ≤ K) →
      B.gN s ^ 2 ≤ Cc * (1 + K) ^ 2)
    (σ s' : B.Mat k r) (v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hσ : σ ∈ B.GV k r) (hs' : s' ∈ B.GV k r) (hv : v ∈ UTset (r + 1)) (hu : u' ∈ UTset (r + 1))
    (hσf : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (hsf : ∀ b, s' *ᵥ fvec k r z' b = fmul k r z' u' b)
    (hbv : mx v⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1)))
    (hbu : mx u'⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1))) :
    B.gN σ + B.gN s' ≤ (1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2) *
      B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2) := by
  obtain ⟨hmul, hinv⟩ := hG k r
  obtain ⟨hnn, hsub, hvec, -⟩ := hNF k r
  have hσi := hinv σ hσ
  have hγi := hinv γ hγ
  have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ hσi.2.1 _ hγ) _ hs'
  have hx1 : 1 ≤ B.gN (σ⁻¹ * γ * s') := (hN k r _ hg).2

  have hσinv_f : ∀ b, σ⁻¹ *ᵥ fvec k r z b = fmul k r z v⁻¹ b := by
    intro b
    have h1 : σ *ᵥ fmul k r z v⁻¹ b = fvec k r z b := by
      rw [frame_mulVec_fmul hσf, ut_mul_inv hv, fmul_one]
    rw [← h1, Matrix.mulVec_mulVec, hσi.2.2.2, Matrix.one_mulVec]

  have hσinv_f' : ∀ b, σ⁻¹ *ᵥ (γ *ᵥ fvec k r z' b) =
      (σ⁻¹ * γ * s') *ᵥ fmul k r z' u'⁻¹ b := by
    intro b
    have h1 : s' *ᵥ fmul k r z' u'⁻¹ b = fvec k r z' b := by
      rw [frame_mulVec_fmul hsf, ut_mul_inv hu, fmul_one]
    rw [← h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hgv : ∀ i, nsq (σ⁻¹ *ᵥ gramVec k r z z' γ i) ≤
      (|Cf| + |Cf'|) * CA ^ 2 * B.gN (σ⁻¹ * γ * s') ^ (2 * (r * (r + 1)) + 2) := by
    intro i
    generalize hxg : B.gN (σ⁻¹ * γ * s') = x at hx1 hbv hbu
    have hx0 : 0 ≤ x := by linarith
    have hxp : x ^ (2 * (r * (r + 1))) ≤ x ^ (2 * (r * (r + 1)) + 2) :=
      pow_le_pow_right₀ hx1 (by omega)
    have hc0 : 0 ≤ CA ^ 2 := sq_nonneg _
    cases i with
    | inl a =>
      show nsq (σ⁻¹ *ᵥ fvec k r z a) ≤ _
      rw [hσinv_f]
      have h1 := real_sq_bound (mx_nonneg _) hbv hx1 (hCf v⁻¹ a)
      have h2 : |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1))) ≤ |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) :=
        mul_le_mul_of_nonneg_left hxp (by positivity)
      have h3 : 0 ≤ |Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by positivity
      linarith
    | inr b =>
      show nsq (σ⁻¹ *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [hσinv_f']
      have h0 := hvec (σ⁻¹ * γ * s') (fmul k r z' u'⁻¹ b)
      rw [hxg] at h0
      have h1 := real_sq_bound (mx_nonneg _) hbu hx1 (hCf' u'⁻¹ b)
      have h2 : x ^ 2 * nsq (fmul k r z' u'⁻¹ b) ≤ x ^ 2 * (|Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : x ^ 2 * (|Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)))) =
          |Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by ring
      have h4 : 0 ≤ |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by positivity
      linarith
  have hD : 0 ≤ (|Cf| + |Cf'|) * CA ^ 2 := by positivity
  have hcore := hCc σ⁻¹ hσi.2.1 _ (by positivity) hgv
  have hNσ := hN k r σ hσ
  rw [hNσ.1] at hcore
  have hs'eq : s' = γ⁻¹ * σ * (σ⁻¹ * γ * s') := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc γ⁻¹ σ σ⁻¹, hσi.2.2.1,
      Matrix.mul_one, hγi.2.2.2, Matrix.one_mul]
  have hs'b : B.gN s' ≤ B.gN γ⁻¹ * B.gN σ * B.gN (σ⁻¹ * γ * s') := by
    conv_lhs => rw [hs'eq]
    calc B.gN (γ⁻¹ * σ * (σ⁻¹ * γ * s')) ≤ B.gN (γ⁻¹ * σ) * B.gN (σ⁻¹ * γ * s') := hsub _ _
      _ ≤ B.gN γ⁻¹ * B.gN σ * B.gN (σ⁻¹ * γ * s') :=
        mul_le_mul_of_nonneg_right (hsub _ _) (hnn _)
  have hN5 : 4 * (r * (r + 1)) + 5 ≤ 5 * (r + 1) ^ 2 := by nlinarith
  exact add_le_mul_pow_of_sq_le_of_le_mul hD (hnn γ⁻¹) hNσ.2 hx1 hcore hs'b hN5

theorem polyProper_of_steps (hG : GVGroup) (hN : NormInv) (hNF : GNFacts) (hF : FmulBound)
    (hZ : ZhatMove) (hS : FrameS) (hSg : FrameSg) (hSg' : FrameSg') (hA : UnitriangularInversePolynomialBound)
    (hC : CoreInst) : PolyProper := by
  refine ⟨5, fun k r z z' γ hstd hpos hmono => ?_⟩
  obtain ⟨CA, hA1, hA2⟩ := hA k r z z' γ hmono
  obtain ⟨Cc, hCc⟩ := hC k r z z' γ hstd hpos
  obtain ⟨Cf, hCf⟩ := hF k r z
  obtain ⟨Cf', hCf'⟩ := hF k r z'
  have hγ : γ ∈ B.GV k r := hpos.1
  obtain ⟨hmul, hinv⟩ := hG k r
  refine ⟨(1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2), ?_, ?_⟩
  · intro σ hσ s' hs'
    obtain ⟨hσG, v, hv, hvL, hσf⟩ := hSg k r z z' γ hstd σ hσ
    obtain ⟨hs'G, u', hu, hsf⟩ := hS k r z' hstd.2.2 s' hs'
    have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ (hinv σ hσG).2.1 _ hγ) _ hs'G
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ σ s' v u' hσG hs'G hσf hsf
    obtain ⟨hbv, hbu⟩ := hA1 v hv hvL u' hu _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc σ s' v u' hσG hs'G hv hu hσf hsf hbv hbu
  · intro s hs σ' hσ'
    obtain ⟨hsG, u, hu, hsf⟩ := hS k r z hstd.2.1 s hs
    obtain ⟨hσG, v', hv', hPv, hσf⟩ := hSg' k r z z' γ hstd σ' hσ'
    have hg : s⁻¹ * γ * σ' ∈ B.GV k r := hmul _ (hmul _ (hinv s hsG).2.1 _ hγ) _ hσG
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ s σ' u v' hsG hσG hsf hσf
    obtain ⟨hbu, hbv⟩ := hA2 u hu v' hv' hPv _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc s σ' u v' hsG hσG hu hv' hsf hσf hbu hbv

end PI.PolynomialProperness
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.CoreInst
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness

theorem coreInst_of (hC : IsoCore) (hI : HpkInvol) (hN : GNFacts) (h1 : Formalism.FourierDecayAlt.C2.GramIndependentSignature) :
    CoreInst := by
  intro k r z z' γ hstd hpos
  obtain ⟨_, ⟨Q, _, hQG⟩, hpd, _⟩ := h1 k r z z' γ hstd hpos
  obtain ⟨hH1, hH2⟩ := hI k r
  have hG : gramOf (Hpk k r) (gramVec k r z z' γ) = gramM k r z z' γ := by
    ext i j
    rfl
  have hunit : IsUnit (gramOf (Hpk k r) (gramVec k r z z' γ)).det := by
    rw [hG]
    set M0 : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
      Matrix.fromBlocks 1 0 0 (-1) with hM0
    have hsq : M0 * M0 = 1 := by
      rw [hM0, Matrix.fromBlocks_multiply]
      simp [Matrix.fromBlocks_one]
    have hM0u : IsUnit M0.det :=
      IsUnit.of_mul_eq_one (b := M0.det) (by rw [← Matrix.det_mul, hsq, Matrix.det_one])
    rw [← hQG, Matrix.det_mul, Matrix.det_mul] at hM0u
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hM0u)
  have hcond : ∀ x, (∀ i, herm (Hpk k r) x (gramVec k r z z' γ i) = 0) →
      0 ≤ (herm (Hpk k r) x x).re := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp [herm]
    · have hxU : x ∈ Uperp k r z z' γ := by
        rw [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
        ext i
        have h2 := hx i
        simp only [herm] at h2
        simpa [Matrix.mulVec, dotProduct] using h2
      exact (hpd x hxU hx0).le
  obtain ⟨C0, hC0⟩ := hC _ (Hpk k r) _ (gramVec k r z z' γ) hH1 hH2 hunit hcond
  obtain ⟨_, _, _, hgn⟩ := hN k r
  refine ⟨C0 * ∑ j : Fin (2 * r + k + 1), nsq (bvec j : Fin (2 * r + k + 1) → ℂ), fun s hs K hK hsm => ?_⟩
  rw [hgn s]
  calc ∑ j, nsq (s *ᵥ bvec j) ≤ ∑ j : Fin (2 * r + k + 1), C0 * (1 + K) ^ 2 * nsq (bvec j : Fin (2 * r + k + 1) → ℂ) :=
        Finset.sum_le_sum fun j _ => hC0 s hs K hK hsm (bvec j)
    _ = C0 * (∑ j : Fin (2 * r + k + 1), nsq (bvec j : Fin (2 * r + k + 1) → ℂ)) * (1 + K) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

end PI.PolynomialProperness
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.HermProjRight
section
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness.CoreW

def eN {n : ℕ} (x : Fin n → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖

theorem eN_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ eN x := norm_nonneg _

theorem eN_add {n : ℕ} (x y : Fin n → ℂ) : eN (x + y) ≤ eN x + eN y := by
  simp only [eN, WithLp.toLp_add]
  exact norm_add_le _ _

theorem eN_sub {n : ℕ} (x y : Fin n → ℂ) : eN (x - y) ≤ eN x + eN y := by
  simp only [eN, WithLp.toLp_sub]
  exact norm_sub_le _ _

theorem eN_smul {n : ℕ} (c : ℂ) (x : Fin n → ℂ) : eN (c • x) = ‖c‖ * eN x := by
  simp only [eN, WithLp.toLp_smul]
  exact norm_smul _ _

theorem eN_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Fin n → ℂ) :
    eN (∑ i ∈ s, f i) ≤ ∑ i ∈ s, eN (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eN]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (eN_add _ _).trans (add_le_add le_rfl ih)

theorem eN_sq {n : ℕ} (x : Fin n → ℂ) : eN x ^ 2 = nsq x := by
  rw [eN, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [nsq, Complex.sq_norm]

theorem dot_le {n : ℕ} (w v : Fin n → ℂ) : ‖star w ⬝ᵥ v‖ ≤ eN w * eN v := by
  have e : star w ⬝ᵥ v =
      inner ℂ (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v) := by
    simp [PiLp.inner_apply, dotProduct, RCLike.inner_apply, mul_comm]
  rw [e]
  exact norm_inner_le_norm _ _

theorem nsq_ofReal {n : ℕ} (x : Fin n → ℂ) : ((nsq x : ℝ) : ℂ) = star x ⬝ᵥ x := by
  simp [nsq, dotProduct, Complex.normSq_eq_conj_mul_self]

section form

variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem star_H_dot (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) :
    star (H *ᵥ v) ⬝ᵥ (H *ᵥ v) = star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH, hHH,
    Matrix.one_mulVec]

theorem nsq_H (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) : nsq (H *ᵥ v) = nsq v := by
  have h : ((nsq (H *ᵥ v) : ℝ) : ℂ) = ((nsq v : ℝ) : ℂ) := by
    rw [nsq_ofReal, nsq_ofReal, star_H_dot H hH hHH v]
  exact_mod_cast h

theorem eN_H (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) : eN (H *ᵥ v) = eN v := by
  have h : eN (H *ᵥ v) ^ 2 = eN v ^ 2 := by rw [eN_sq, eN_sq, nsq_H H hH hHH]
  exact (pow_left_inj₀ (eN_nonneg _) (eN_nonneg _) two_ne_zero).mp h

theorem herm_le (hH : Hᴴ = H) (hHH : H * H = 1) (v w : Fin n → ℂ) :
    ‖herm H v w‖ ≤ eN v * eN w := by
  unfold herm
  calc ‖star w ⬝ᵥ (H *ᵥ v)‖ ≤ eN w * eN (H *ᵥ v) := dot_le _ _
    _ = eN v * eN w := by rw [eN_H H hH hHH, mul_comm]

theorem herm_H_self (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) :
    herm H v (H *ᵥ v) = ((nsq v : ℝ) : ℂ) := by
  unfold herm
  rw [star_H_dot H hH hHH, nsq_ofReal]

theorem herm_iso (s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H) (v w : Fin n → ℂ) :
    herm H (s *ᵥ v) (s *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hs]

theorem herm_conj (hH : Hᴴ = H) (v w : Fin n → ℂ) : conj (herm H v w) = herm H w v := by
  unfold herm
  rw [← Complex.star_def, Matrix.star_dotProduct, star_star, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, hH]

theorem herm_sub_left (v v' w : Fin n → ℂ) : herm H (v - v') w = herm H v w - herm H v' w := by
  simp [herm, Matrix.mulVec_sub, dotProduct_sub]

theorem herm_smul_left (c : ℂ) (v w : Fin n → ℂ) : herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

theorem herm_sum_left {ι : Type} [Fintype ι] (f : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ i, f i) w = ∑ i, herm H (f i) w := by
  simp [herm, Matrix.mulVec_sum, dotProduct_sum]

theorem herm_sub_right (hH : Hᴴ = H) (v w w' : Fin n → ℂ) :
    herm H v (w - w') = herm H v w - herm H v w' := by
  simp [herm, star_sub, sub_dotProduct]

theorem herm_smul_right (hH : Hᴴ = H) (c : ℂ) (v w : Fin n → ℂ) :
    herm H v (c • w) = conj c * herm H v w := by
  simp [herm, star_smul, smul_dotProduct]

theorem herm_sum_right (hH : Hᴴ = H) {ι : Type} [Fintype ι] (f : ι → Fin n → ℂ) (v : Fin n → ℂ) :
    herm H v (∑ i, f i) = ∑ i, herm H v (f i) := by
  simp [herm, star_sum, sum_dotProduct]

end form

section proj

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def coef (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    ι → ℂ :=
  Γi *ᵥ fun k => herm H y (p k)

def proj (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    Fin n → ℂ :=
  ∑ i, coef H Γi p y i • p i

theorem herm_proj_left (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ)
    (hG : gramOf H p * Γi = 1) (y : Fin n → ℂ) (j : ι) :
    herm H (proj H Γi p y) (p j) = herm H y (p j) := by
  unfold proj
  rw [herm_sum_left]
  simp only [herm_smul_left]
  have e : (∑ i, coef H Γi p y i * herm H (p i) (p j)) = (gramOf H p *ᵥ coef H Γi p y) j := by
    simp only [Matrix.mulVec, dotProduct, gramOf, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [e, coef, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]

theorem proj_orth (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ)
    (hG : gramOf H p * Γi = 1) (y : Fin n → ℂ) (j : ι) :
    herm H (y - proj H Γi p y) (p j) = 0 := by
  rw [herm_sub_left, herm_proj_left H Γi p hG y j, sub_self]

theorem herm_proj_right (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (Γi : Matrix ι ι ℂ)
    (p : ι → Fin n → ℂ) (y x : Fin n → ℂ) (hx : ∀ j, herm H x (p j) = 0) :
    herm H x (proj H Γi p y) = 0 := by
  unfold proj
  rw [herm_sum_right H hH]
  simp [herm_smul_right H hH, hx]

theorem lincomb_bound (c : ι → ℂ) (q : ι → Fin n → ℂ) (a R : ℝ) (_hR : 0 ≤ R)
    (hc : ∀ i, ‖c i‖ ≤ a) (hq : ∀ i, eN (q i) ≤ R) :
    eN (∑ i, c i • q i) ≤ (Fintype.card ι : ℝ) * a * R := by
  calc eN (∑ i, c i • q i) ≤ ∑ i, eN (c i • q i) := eN_sum _ _
    _ = ∑ i, ‖c i‖ * eN (q i) := by simp only [eN_smul]
    _ ≤ ∑ _i : ι, a * R := Finset.sum_le_sum (fun i _ =>
        mul_le_mul (hc i) (hq i) (eN_nonneg _) ((norm_nonneg _).trans (hc i)))
    _ = (Fintype.card ι : ℝ) * a * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem coef_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (R : ℝ) (hp : ∀ k, eN (p k) ≤ R)
    (y : Fin n → ℂ) (i : ι) :
    ‖coef H Γi p y i‖ ≤ (∑ j, ∑ k, ‖Γi j k‖) * (eN y * R) := by
  have hb : ∀ k, ‖herm H y (p k)‖ ≤ eN y * R := fun k =>
    (herm_le H hH hHH y (p k)).trans (mul_le_mul_of_nonneg_left (hp k) (eN_nonneg _))
  unfold coef
  simp only [Matrix.mulVec, dotProduct]
  calc ‖∑ k, Γi i k * herm H y (p k)‖ ≤ ∑ k, ‖Γi i k * herm H y (p k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖Γi i k‖ * (eN y * R) := Finset.sum_le_sum (fun k _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _))
    _ = (∑ k, ‖Γi i k‖) * (eN y * R) := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ k, ‖Γi j k‖) * (eN y * R) := by
        apply mul_le_mul_of_nonneg_right _ ((norm_nonneg _).trans (hb i))
        exact Finset.single_le_sum (f := fun j => ∑ k, ‖Γi j k‖)
          (fun j _ => Finset.sum_nonneg (fun k _ => norm_nonneg _)) (Finset.mem_univ i)

theorem proj_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R) (hp : ∀ k, eN (p k) ≤ R)
    (y : Fin n → ℂ) :
    eN (proj H Γi p y) ≤
      (Fintype.card ι : ℝ) * ((∑ j, ∑ k, ‖Γi j k‖) * (eN y * R)) * R :=
  lincomb_bound _ _ _ R hR (fun i => coef_bound H hH hHH Γi p R hp y i) hp

end proj

end PI.PolynomialProperness.CoreW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.TauDefs
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness

def MXFacts : Prop :=
  ∀ (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ), vX ∈ UTset r →
    mX k r vX ∈ Nset k r ∧ (∀ p : Fin r → ℂ, mX k r vX *ᵥ xiV k r p = xiV k r (vX *ᵥ p)) ∧
    ∀ w : Fin (2 * r + k + 1) → ℂ, inWb k r w → mX k r vX *ᵥ w = w

def NEFacts : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → ∀ ξ : Fin r → ℂ,
    nEich k r z ξ ∈ Nset k r ∧ (∀ p : Fin r → ℂ, nEich k r z ξ *ᵥ xiV k r p = xiV k r p) ∧
    nEich k r z ξ *ᵥ z = z + xiV k r ξ

end PI.PolynomialProperness
end
end

