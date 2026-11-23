module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsotropicNormalFormFullStatement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0121
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0126
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0078
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0135

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixFirstLineZero
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

section nf

variable {k r : ℕ}

theorem zb_last_row (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (a b : ℕ) (ha : a ≠ i0)
    (ha' : a + 1 < i0 + s) (hb : b = i0) : C3.Zb i0 s hh t a b = 0 := by
  subst hb
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem zb_col_last (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (a : ℕ) (ha : a ≠ i0)
    (ha' : a + 1 < i0 + s) : C3.Zb i0 s hh t a (i0 + s - 1) = 0 := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem corner_matrix_last_entry (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) :
    C3.Zb i0 s hh t i0 (i0 + s - 1) = t := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem corner_matrix_first_line_zero (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (b : ℕ) (hb : b + 1 < i0 + s) :
    C3.Zb i0 s hh t i0 b = 0 := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem herm_bvec_right (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec p) = WeylGroupFacts.sgn k r p * v (WeylGroupFacts.tau k r p) := by
  have hs : star (Pi.single p (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single p 1 := by
    ext q
    by_cases h : q = p
    · subst h
      simp
    · simp [Pi.single_apply, h]
  unfold herm bvec
  rw [hs, single_dotProduct, one_mul, SignAntidiagonal.mulVec_hpk]

theorem nf_top (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hT' : herm (Hpk k r) z' z' ≠ 0)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : γ ∈ UH (Hpk k r)) (i0 s : ℕ) (hs : 2 ≤ s)
    (hj : i0 + s = r + 1) (hh : Matrix (Fin i0) (Fin i0) ℂ) (hdet : hh.det ≠ 0) (t : ℂ) (ht : t ≠ 0)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' γ a b = C3.Zb i0 s hh t a.val b.val) :
    ∃ n0 ∈ C3.N0set k r z', ∃ yb : Fin (2 * r + k + 1) → ℂ, inWb k r yb ∧ herm (Hpk k r) z' yb = t ∧
      (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
        PBG.xi0 (γ * n0) a p = if p.val < r ∧ p.val ≠ i0 then C3.Zb i0 s hh t a.val p.val else 0) ∧
      (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val = i0 → PBG.xi0 (γ * n0) a p = herm (Hpk k r) (bvec p) yb) := by
  obtain ⟨s'', rfl⟩ : ∃ s'', s = s'' + 2 := ⟨s - 2, by omega⟩
  obtain rfl : r = i0 + s'' + 1 := by omega
  have hγi : γ⁻¹ ∈ UH (Hpk k (i0 + s'' + 1)) := WeylGroupFacts.uh_inv hγ
  have hγu := WeylGroupFacts.isUnit_of_uh hγ
  set y : Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) → ℂ := fun a => γ⁻¹ *ᵥ bvec (eI k _ a) with hy
  set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hi

  have hyS : ∀ (a b : Fin (i0 + s'' + 1)), y a (esI k _ b) = star (C3.Zb i0 (s'' + 2) hh t a.val b.val) := by
    intro a b
    simp only [hy]
    rw [(xi_Y_zhat_identity k _ z z' γ a b hγ).2, hZ]
    rfl
  have hfz' : fvec k (i0 + s'' + 1) z' (Fin.last _) = z' := by unfold fvec; rw [dite_eq_right (by simp)]
  have hfa : ∀ a : Fin (i0 + s'' + 1), fvec k _ z a.castSucc = bvec (eI k _ a) := by
    intro a; unfold fvec; rw [dite_eq_left (by have := a.isLt; simp; omega)]; rfl
  have hyz : ∀ a : Fin (i0 + s'' + 1), herm (Hpk k _) z' (y a) = C3.Zb i0 (s'' + 2) hh t a.val (i0 + s'' + 1) := by
    intro a
    have h1 : herm (Hpk k _) z' (y a) = herm (Hpk k _) (γ *ᵥ z') (γ *ᵥ y a) := (herm_unitary γ hγ _ _).symm
    have h2 : γ *ᵥ y a = bvec (eI k _ a) := by
      rw [hy]; simp only
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mulVec]
    rw [h1, h2]
    have := hZ a.castSucc (Fin.last _)
    simp only [Zhat, hfz', hfa] at this
    rw [this]
    simp
  obtain ⟨n0, hn0, y', hy'⟩ := isotropicNormalFormFull_statement k (i0 + s'') z' i y t hz' hT' ht
    (by
      intro a ha
      rw [hyS]
      have : C3.Zb i0 (s'' + 2) hh t a.val i0 = 0 :=
        zb_last_row i0 _ hh t (by omega) a.val i0 (fun h => ha (Fin.ext h)) (by omega) rfl
      show star (C3.Zb i0 (s'' + 2) hh t a.val i0) = 0
      rw [this, star_zero])
    (by
      intro p hp
      have hb : 2 * (i0 + s'' + 1) + k - p.val < i0 + s'' + 1 := by omega
      have hpe : p = esI k _ ⟨2 * (i0 + s'' + 1) + k - p.val, hb⟩ := by ext; simp [esI]; omega
      rw [hpe, hyS]
      have : C3.Zb i0 (s'' + 2) hh t i0 (2 * (i0 + s'' + 1) + k - p.val) = 0 :=
        corner_matrix_first_line_zero i0 _ hh t (by omega) _ (by omega)
      simp [hi, this])
    (by
      have hP := third_polynomial_expansion i0 s'' hh t
      have hS := (sign_permutation_identity s'').2
      have hsg : C3.sgnW s'' ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hS; exact (by norm_num : (0 : ℂ) ≠ -1) hS
      have hne : (Matrix.of fun a b : Fin (i0 + s'') => C3.Zb i0 (s'' + 2) hh t
          ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
          ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val).det ≠ 0 := by
        rw [hP]; exact mul_ne_zero (mul_ne_zero hdet (pow_ne_zero _ ht)) hsg
      have e : (Matrix.of fun a b : Fin (i0 + s'') => y (i.succAbove a) (esI k (i0 + s'' + 1) (i.succAbove b))) =
          (Matrix.of fun a b : Fin (i0 + s'') => C3.Zb i0 (s'' + 2) hh t
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val).map (starRingEnd ℂ) := by
        ext a b; simp [hyS, hi]
      rw [e]
      change ((starRingEnd ℂ).mapMatrix _).det ≠ 0
      rw [← RingHom.map_det]
      exact (map_ne_zero _).2 hne)
    (by
      intro a ha
      rw [hyz]
      have := zb_col_last i0 (s'' + 2) hh t (by omega) a.val (fun h => ha (Fin.ext h)) (by omega)
      rwa [show i0 + (s'' + 2) - 1 = i0 + s'' + 1 by omega] at this)
    (by
      rw [hyz]
      have := corner_matrix_last_entry i0 (s'' + 2) hh t (by omega)
      rwa [show i0 + (s'' + 2) - 1 = i0 + s'' + 1 by omega] at this)
    (by
      intro a a'
      rw [hy]; simp only
      rw [herm_unitary _ hγi, herm_bvec_bvec]
      have := a.isLt
      have := a'.isLt
      unfold Hpk
      rw [if_neg (fun h => by simp only [eI] at h; omega), if_neg (fun h => by simp only [eI] at h; omega),
        if_neg (fun h => by simp only [eI] at h; omega)])

  have hn0u : n0 ∈ UH (Hpk k (i0 + s'' + 1)) := hn0.1
  have hxi : ∀ (a : Fin (i0 + s'' + 1)) (p : Fin (2 * (i0 + s'' + 1) + k + 1)),
      PBG.xi0 (γ * n0) a p = herm (Hpk k _) (bvec p) (y' a) := by
    intro a p
    unfold PBG.xi0
    have h2 : bvec (eI k _ a) = γ *ᵥ y a := by
      rw [hy]; simp only
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mulVec]
    rw [h2, ← Matrix.mulVec_mulVec, herm_unitary γ hγ, ← (hy' a).1, herm_unitary n0 hn0u]
  refine ⟨n0, hn0, y' i, ((hy' i).2.2 rfl).1, ((hy' i).2.2 rfl).2, ?_, ?_⟩
  · intro a p ha
    have hai : a ≠ i := fun h => ha (by rw [h])
    obtain ⟨hz0, hsame⟩ := (hy' a).2.1 hai
    rw [hxi, herm_swap, herm_bvec_right]
    by_cases hp : p.val < i0 + s'' + 1
    ·
      have htau : WeylGroupFacts.tau k _ p = esI k _ ⟨p.val, hp⟩ := by
        ext; rw [tau_val, if_pos (Or.inl hp)]; simp [esI]
      have hsg : WeylGroupFacts.sgn k _ p = 1 := sgn_one _ (by omega)
      rw [htau, hsg, one_mul, hsame _ (by simp [esI]; omega), hyS, star_star]
      by_cases hpi : p.val = i0
      · rw [if_neg (by omega)]
        exact zb_last_row i0 _ hh t (by omega) a.val p.val ha (by omega) hpi
      · rw [if_pos ⟨hp, hpi⟩]
    · rw [if_neg (by omega)]
      have hle : (WeylGroupFacts.tau k _ p).val ≤ i0 + s'' + 1 + k := by
        rw [tau_val]; split_ifs <;> omega
      rw [hz0 _ hle]
      simp
  · intro a p ha
    have hai : a = i := Fin.ext ha
    subst hai
    rw [hxi]

end nf

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefTraceCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def BsAt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (μ0 : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (h0 : IsSection P.k P.r Bs.z Bs.z' μ0) :
    B.RealPlaceData P.k P.r Wp Wq :=
  { Bs with μsec := μ0, sec := h0 }

def GTRMove : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (μ0 : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (h0 : IsSection P.k P.r Bs.z Bs.z' μ0)
      (e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)), IsFrameB P (BsAt P Bs μ0 h0) e0 →
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', trR P Bs e Φ = trR P (BsAt P Bs μ0 h0) e0 Φ

def GTRConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧ KapF P Bs d e ∧
      ∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ'

def GTRRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∀ ρ : M.Ty P, ∃ m : ℤ, ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs e (Rt Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
          fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + ((m : ℂ)) • trR P Bs e Φ ρ

def GTRInt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ ρ : M.Ty P, ∃ n : ℤ, uSum P - rhoSum P ρ = n

def GTRTrans : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∀ (ρ : M.Ty P) (m : ℂ),
        (∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
          trR P Bs e ((ThetaNF P d).1 Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
            fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + m • trR P Bs e Φ ρ) →
        ∀ ζ ∈ Ann P, ζ * A ρ ζ + star ζ * B ρ ζ =
          m + ((-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)

theorem poly_coeff_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (a : ℕ → V)
    (h : ∀ Y : ℂ, ∑ j ∈ Finset.range N, Y ^ j • a j = 0) : ∀ j < N, a j = 0 := by
  intro j hj
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (a j)).mp ?_
  intro f
  have hp0 : (∑ i ∈ Finset.range N, Polynomial.C (f (a i)) * Polynomial.X ^ i : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro Y
    have hY := congrArg f (h Y)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hY
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    rw [← hY]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hc := congrArg (fun q => q.coeff j) hp0
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj] using hc

theorem poly_coeff_eq {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (a b : ℕ → V)
    (h : ∀ Y : ℂ, ∑ j ∈ Finset.range N, Y ^ j • a j = ∑ j ∈ Finset.range N, Y ^ j • b j) :
    ∀ j < N, a j = b j := by
  intro j hj
  have hz : ∀ Y : ℂ, ∑ i ∈ Finset.range N, Y ^ i • (a - b) i = 0 := by
    intro Y
    simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, h Y, sub_self]
  exact sub_eq_zero.mp (poly_coeff_zero N (a - b) hz j hj)

theorem pr_fst_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (Y : ℂ) (x : Q.Pr V) : (Y • x).1 = Y • x.1 := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

theorem pr_fst_add {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : Q.Pr V) : (x + y).1 = x.1 + y.1 := rfl

theorem pr_fst_one {V : Type*} [AddCommGroup V] [Module ℂ V] : (1 : Q.Pr V).1 = 1 := rfl

theorem pr_fst_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (s : Finset ℕ) (f : ℕ → Q.Pr V) :
    (∑ j ∈ s, f j).1 = ∑ j ∈ s, (f j).1 := Prod.fst_sum

theorem final_arith (P : M.Par) (ρ : M.Ty P) (A ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (m N : ℤ)
    (hN : uSum P - rhoSum P ρ = N)
    (hA : ζ * A + star ζ * star A =
      (m : ℂ) + ((-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)) :
    (ζ * (modA P ρ ζ - A)).re = ((N - m : ℤ) : ℝ) / 2 := by
  have hpos : 0 < Complex.normSq ζ - P.TT := sub_pos.mpr hζ
  have hne : ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hpos.ne'
  have haC : M.aC P ρ = uSum P / 2 - rhoSum P ρ := rfl
  have hre := congrArg Complex.re hA
  have h1 : (ζ * A + star ζ * star A).re = 2 * (ζ * A).re := by
    rw [← star_mul', Complex.add_re, Complex.star_def, Complex.conj_re]; ring
  rw [h1, Complex.add_re, Complex.intCast_re, Complex.ofReal_re] at hre
  have h2 : ζ * modA P ρ ζ = ((M.aC P ρ * Complex.normSq ζ / (Complex.normSq ζ - P.TT) : ℝ) : ℂ) := by
    unfold modA
    rw [Complex.star_def]
    push_cast
    rw [← Complex.mul_conj]
    field_simp
  rw [mul_sub, Complex.sub_re, h2, Complex.ofReal_re, haC]
  have hA' : (ζ * A).re = ((m : ℝ) + (-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT))) / 2 := by
    linarith
  rw [hA']
  push_cast
  rw [← hN]
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsNv (l : Fin (r + 1)) (s : Fin (k + 1)) : Fin (r - l.val + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < s.val then r + j.val else r + j.val + 1, by
    have := j.isLt; have := s.isLt; have := l.isLt; split_ifs <;> omega⟩

def NLv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
    (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
      qminorOp (Q.EH k r) (rowsNv k r l s) (rowsNv k r l t) u f g

def FNv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (J : Q.Mx k r → E) (l : Fin (r + 1)) : Q.Fn k r E :=
  Q.resG k r (Fin.last r) (NLv k r z z' l (Q.uC k r (Fin.last r) Y - 1) J)

end defs

def JDRvBeta : Prop :=
  ∀ k r : ℕ, ∃ σ : ℂ, σ ≠ 0 ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) (f : Q.Mx k r → E), inWb k r z → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      rvhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
        (σ * ∏ a, c a) • NLv k r z z' 0 (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c * g)

def JDRvTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J (Fin.last r) c g = -Q.QL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J) c g

def JDRvStepA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨r - 1, by omega⟩ c g =
        (Y • FNv k r z z' Y J (Fin.last r) - Q.crd (Formalism.QuantumDeterminants.pbOp ⟨r - 1, by omega⟩) (FNv k r z z' Y J (Fin.last r)) -
          Q.crd (Formalism.QuantumDeterminants.cbiOp ⟨r - 1, by omega⟩) (Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J))) c g

def JDRvStepB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ (l : ℕ) (hl : l + 2 ≤ r),
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨l, by omega⟩ c g =
        (Y • FNv k r z z' Y J ⟨l + 1, by omega⟩ -
          Q.crd (Formalism.QuantumDeterminants.pbOp ⟨l, by omega⟩) (FNv k r z z' Y J ⟨l + 1, by omega⟩) -
          Q.crd (Formalism.QuantumDeterminants.cbOp ⟨l + 1, by omega⟩) (Q.crd (Formalism.QuantumDeterminants.cbiOp ⟨l, by omega⟩)
            (FNv k r z z' Y J ⟨l + 2, by omega⟩))) c g

def JDRvChainM : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J 0 c g =
        -(Q.QL k r z z' (Fin.last r) Y 0 1 (Q.crd (Q.cmp (Q.vABs r Y r) 0) (Q.resG k r (Fin.last r) J)) +
          Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (Q.cmp (Q.vABs r Y r) 1) (Q.resG k r (Fin.last r) J))) c g

def JDRvConseq : Prop := JDRvTop → JDRvStepA → JDRvStepB → JDRvChainM

theorem jDRRadM_of_parts (hB : JDRvBeta) (hT : JDRvTop) (hA : JDRvStepA) (hS : JDRvStepB) (hC : JDRvConseq) :
    JDRRadM := by
  have hCh := hC hT hA hS
  intro k r
  obtain ⟨σ, hσ, hβ⟩ := hB k r
  refine ⟨-σ⁻¹, ?_⟩
  intro Wp Wq _ _ _ _ z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have h1 := hβ (Wq →L[ℂ] Wp) z z' Y J hz c hc g hg
  have h2 := hCh Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  simp only [FNv, Q.resG] at h2
  simp only [Q.resG, rhvGrp, dMul, drF]
  rw [h1, smul_smul, smul_smul, show ∀ a b : ℂ, a * -σ⁻¹ * (σ * b) = -b * a from fun a b => by field_simp,
    ← smul_smul, h2, smul_neg, neg_smul, neg_neg]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPComm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JDRPComm : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Dc : (Fin r → ℂ) → Set (Q.Mx k r)) (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} →
    Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ →
    ∀ (l : Fin r) (Y : ℂ) (a b : Fin 2), ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
      Q.crd (Formalism.QuantumDeterminants.pOp l) (Q.QL k r z z' (Fin.last r) Y a b Ψ) c g =
        Q.QL k r z z' (Fin.last r) Y a b (Q.crd (Formalism.QuantumDeterminants.pOp l) Ψ) c g

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity
section
theorem Formalism.FourierDecayAlt.P.sign_permutation_identity : Formalism.FourierDecayAlt.C3.SignE :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.sign_permutation_identity

theorem Formalism.FourierDecayAlt.P.derivative_leading_zb : Formalism.FourierDecayAlt.C3.DleadZb :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb

theorem Formalism.FourierDecayAlt.P.minors_first_case : Formalism.FourierDecayAlt.C3.MinorsFirstCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.minors_first_case

theorem Formalism.FourierDecayAlt.P.third_polynomial_expansion : Formalism.FourierDecayAlt.C3.MinorsThirdCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_polynomial_expansion

theorem Formalism.FourierDecayAlt.P.first_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_identity

theorem Formalism.FourierDecayAlt.P.second_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_peeling_identity

theorem Formalism.FourierDecayAlt.P.third_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_peeling_identity

theorem Formalism.FourierDecayAlt.P.first_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_expansion_identity

theorem Formalism.FourierDecayAlt.P.second_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_expansion_identity

theorem Formalism.FourierDecayAlt.P.column_indicator_expansion : Formalism.FourierDecayAlt.C3.ExpansionCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion

theorem Formalism.FourierDecayAlt.P.chain_first_identity : Formalism.FourierDecayAlt.C3.LastColumnChain :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.chain_first_identity

theorem Formalism.FourierDecayAlt.P.leading_term_identity : Formalism.FourierDecayAlt.C3.LeadAA :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity

theorem Formalism.FourierDecayAlt.P.leading_term_vector_identity : Formalism.FourierDecayAlt.C3.LeadAAv :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_vector_identity

theorem Formalism.FourierDecayAlt.P.dpsi_is_derivation : Formalism.FourierDecayAlt.C3.DpsiDerivation :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_is_derivation

theorem Formalism.FourierDecayAlt.P.isotropicNormalFormFull_statement : Formalism.FourierDecayAlt.C3.IsotropicNormalFormFull :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.isotropicNormalFormFull_statement
end

