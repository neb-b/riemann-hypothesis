module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.FvecCastSucc
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness.TauW

lemma xiV_eq_sum (k r : ℕ) (p : Fin r → ℂ) : xiV k r p = ∑ a, p a • bvec (eI k r a) := by
  ext i
  simp only [xiV, bvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val, h⟩]
    · rw [if_pos]
      ext
      simp [eI]
    · intro b _ hb
      rw [if_neg]
      intro he
      apply hb
      ext
      simp only [Fin.val_mk]
      have := congrArg Fin.val he
      simp [eI] at this
      omega
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro he
    apply h
    rw [he]
    simp [eI]

lemma fvec_castSucc' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    fvec k r z b.castSucc = bvec (eI k r b) := by
  simp [fvec]

lemma fvec_last' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

lemma frame_sum' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    ∑ a, c a • fvec k r z a = ∑ b : Fin r, c b.castSucc • bvec (eI k r b) + c (Fin.last r) • z := by
  rw [Fin.sum_univ_castSucc]
  simp only [fvec_castSucc', fvec_last']

lemma bvec_eq_xiV (k r : ℕ) (b : Fin r) : bvec (eI k r b) = xiV k r (Pi.single b 1) := by
  rw [xiV_eq_sum]
  simp [Pi.single_apply, ite_smul]

end PI.PolynomialProperness.TauW

namespace PI.PolynomialProperness

open TauW

theorem tauMem_of (hMX : MXFacts) (hNE : NEFacts) : TauMem := by
  intro k r z hz v hv
  have hvX : v.submatrix Fin.castSucc Fin.castSucc ∈ UTset r :=
    ⟨fun i j hij => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij), fun i => hv.2 _⟩
  obtain ⟨hm1, hm2, hm3⟩ := hMX k r _ hvX
  obtain ⟨hn1, hn2, hn3⟩ := hNE k r z hz (fun a => v a.castSucc (Fin.last r))
  have hfr : ∀ b, tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a := by
    intro b
    simp only [tauM]
    rw [← Matrix.mulVec_mulVec]
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · rw [fvec_last', hm3 z hz.1, hn3, frame_sum', hv.2 (Fin.last r), one_smul, xiV_eq_sum]
      exact add_comm _ _
    · have h0 : v (Fin.last r) b'.castSucc = 0 := hv.1 _ _ (Fin.castSucc_lt_last b')
      rw [fvec_castSucc', bvec_eq_xiV, hm2, hn2, frame_sum', xiV_eq_sum, h0, zero_smul, add_zero]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Matrix.mulVec_single]
  exact ⟨WeylGroupFacts.mem_n_mul hn1 hm1, hfr, P.C2x5.uMap_eq hz _ _ hfr⟩

end PI.PolynomialProperness
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInverseBoundOf
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness.CA

theorem ut_conjT {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : uᴴ ∈ LTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conjTranspose_apply, hu.1 j i hij, star_zero]
  · rw [conjTranspose_apply, hu.2 i, star_one]

theorem isMonomial_conjT {m : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} (h : IsMonomial P) : IsMonomial Pᴴ := by
  obtain ⟨w, d, hd, rfl⟩ := h
  refine ⟨w.symm, fun a => star (d (w.symm a)), fun a => by simpa using hd (w.symm a), ?_⟩
  ext i a
  simp only [monoP, conjTranspose_apply, of_apply]
  by_cases h : a = w i
  · have h' : i = w.symm a := by rw [h, Equiv.symm_apply_apply]
    rw [if_pos h, if_pos h', h']
  · have h' : ¬ i = w.symm a := by
      intro h'; apply h; rw [h', Equiv.apply_symm_apply]
    rw [if_neg h, if_neg h', star_zero]

theorem mx_inv_conjT {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : mx (Mᴴ)⁻¹ = mx M⁻¹ := by
  rw [← conjTranspose_nonsing_inv, GN.mx_conjTranspose]

theorem finish_bound {M C0 X A G : ℝ} (e : ℕ) (hm : M ≤ C0 * X ^ e) (hX : 0 ≤ X) (hXY : X ≤ A * G) :
    M ≤ max C0 0 * A ^ e * G ^ e := by
  calc M ≤ C0 * X ^ e := hm
    _ ≤ max C0 0 * X ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hX e)
    _ ≤ max C0 0 * (A * G) ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hXY e) (le_max_right _ _)
    _ = max C0 0 * A ^ e * G ^ e := by rw [mul_pow]; ring

theorem exp_eq (r : ℕ) : (r + 1 - 1) * (r + 1) = r * (r + 1) := by
  rw [Nat.add_sub_cancel]

end PI.PolynomialProperness.CA

namespace PI.PolynomialProperness

open CA in
theorem unitriangular_inverse_bound_of (h : MonomialFactorizationBound) (hZ : ZhatBound) : UnitriangularInversePolynomialBound := by
  intro k r z z' γ hmono
  obtain ⟨C1, h1⟩ := h (r + 1) (Zhat k r z z' γ) hmono
  obtain ⟨C2, h2⟩ := h (r + 1) (Zhat k r z z' γ)ᴴ (isMonomial_conjT hmono)
  obtain ⟨CZ, hCZ⟩ := hZ k r z z'
  set A : ℝ := 1 + max CZ 0 with hA
  set e : ℕ := r * (r + 1) with he
  have hzg : ∀ g : B.Mat k r, 1 ≤ B.gN g → 1 + mx (Zhat k r z z' g) ≤ A * B.gN g := by
    intro g hg
    have h3 := hCZ g
    have h4 : CZ * B.gN g ≤ max CZ 0 * B.gN g :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    rw [hA]; nlinarith
  have hX : ∀ g : B.Mat k r, 0 ≤ 1 + mx (Zhat k r z z' g) := fun g => by
    have := GN.mx_nonneg (Zhat k r z z' g); linarith
  have hApos : 0 ≤ A ^ e := pow_nonneg (by rw [hA]; have := le_max_right CZ 0; linarith) e
  refine ⟨max (max C1 0) (max C2 0) * A ^ e, ?_, ?_⟩
  · intro v hv hvl u' hu' g hg hZg
    have hb := h1 vᴴ hvl u' hu'
    rw [← hZg, exp_eq] at hb
    have hmax : max C1 0 * A ^ e ≤ max (max C1 0) (max C2 0) * A ^ e :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hApos
    have hG : 0 ≤ B.gN g ^ e := pow_nonneg (by linarith) e
    constructor
    · rw [← mx_inv_conjT]
      exact (finish_bound e hb.2.2.1 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
    · exact (finish_bound e hb.2.2.2 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
  · intro u hu v' hv' hPv g hg hZg
    have hl : v'ᴴ ∈ LPg (Zhat k r z z' γ)ᴴ := by
      refine ⟨ut_conjT hv', ?_⟩
      have e1 : ((Zhat k r z z' γ)ᴴ)⁻¹ * v'ᴴ * (Zhat k r z z' γ)ᴴ =
          (Zhat k r z z' γ * v' * (Zhat k r z z' γ)⁻¹)ᴴ := by
        rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]
      rw [e1]
      exact ut_conjT hPv
    have hb := h2 v'ᴴ hl u hu
    have e2 : v'ᴴ * (Zhat k r z z' γ)ᴴ * u = (Zhat k r z z' g)ᴴ := by
      rw [hZg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e2, GN.mx_conjTranspose (Zhat k r z z' g), exp_eq] at hb
    have hmax : max C2 0 * A ^ e ≤ max (max C1 0) (max C2 0) * A ^ e :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hApos
    have hG : 0 ≤ B.gN g ^ e := pow_nonneg (by linarith) e
    constructor
    · exact (finish_bound e hb.2.2.2 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)
    · rw [← mx_inv_conjT]
      exact (finish_bound e hb.2.2.1 (hX g) (hzg g hg)).trans (mul_le_mul_of_nonneg_right hmax hG)

theorem unitriangular_inverse_bound (h : MonomialFactorizationBound) : UnitriangularInversePolynomialBound := unitriangular_inverse_bound_of h zhatBound

end PI.PolynomialProperness
end
end

