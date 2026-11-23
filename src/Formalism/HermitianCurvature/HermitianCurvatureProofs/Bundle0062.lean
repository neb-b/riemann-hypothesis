module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaConjOfParts
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CptInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (C : Set (B.Mat k r)),
    B.CkOn ⊤ (B.GV k r) F → IsCompact C → (∀ g, g ∉ C → F g = 0) → ∀ (A : ℝ) (m : ℕ), B.InCC A m F

theorem thr_big (k r m : ℕ) :
    TransportedAlt k r (9 * ((r : ℝ) + 1) * ((((2 * r + k + 1 : ℕ) : ℝ)) ^ 2 + 1) + 6 * (r : ℝ) * (m : ℝ)) m := by
  unfold TransportedAlt
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) r, sq_nonneg (((2 * r + k + 1 : ℕ) : ℝ))]

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPeelingMinorMemIdeal
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem pe_lt {k r p : ℕ} (h : p < 2 * r + k + 1) : (pe k r p).val = p := by
  rw [pe_val]
  omega

theorem herm_wsum (k r : ℕ) (v y : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    herm (Hpk k r) v y = ∑ w : Fin (k + 1), v (wI k r w) * herm (Hpk k r) (bvec (wI k r w)) y := by
  have hv' : v = ∑ w : Fin (k + 1), v (wI k r w) • bvec (wI k r w) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, bvec, smul_eq_mul]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [Finset.sum_eq_single ⟨i.val - r, by omega⟩]
      · have e : wI k r ⟨i.val - r, by omega⟩ = i := Fin.ext (by simp only [wI]; omega)
        rw [e, Pi.single_eq_same, mul_one]
      · intro w _ hw
        rw [Pi.single_eq_of_ne, mul_zero]
        intro e
        apply hw
        apply Fin.ext
        have := congrArg Fin.val e
        simp only [wI, Fin.val_mk] at this ⊢
        omega
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [hv i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro w _
      rw [Pi.single_eq_of_ne, mul_zero]
      intro e
      have := congrArg Fin.val e
      simp only [wI] at this
      omega
  conv_lhs => rw [hv']
  simp only [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem dpsi_e_w (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (p : ℕ) (hp : p < r) (w : Fin (k + 1)) :
    dpsiP k r z' (pe k r p) (wI k r w) = if p + 1 = r then z' (wI k r w) else 0 := by
  have h1 : min p (2 * r + k) = p := by omega
  have hw : (wI k r w).val = r + w.val := rfl
  have hwk := w.isLt
  simp only [dpsiP, pe_val, h1, hw]
  rw [if_neg (by omega), if_pos (by omega)]

theorem dpsi_last_basis_shift (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (a b : ℕ) (ha : a < r) (hb : b < r) :
    dpsiP k r z' (ps k r a) (ps k r b) = if b + 1 = a then 1 else 0 := by
  have c1 : ¬(2 * r + k - a < r ∧ 2 * r + k - b < r) := by omega
  have c2 : ¬(2 * r + k - a < r ∧ r ≤ 2 * r + k - b ∧ 2 * r + k - b ≤ r + k) := by omega
  have c3 : ¬(r ≤ 2 * r + k - a ∧ 2 * r + k - a ≤ r + k ∧ r + k < 2 * r + k - b) := by omega
  have c4 : r + k < 2 * r + k - a ∧ r + k < 2 * r + k - b := by omega
  have c5 : (2 * r + k - b = 2 * r + k - a + 1) ↔ (b + 1 = a) := by omega
  have c6 : ¬(2 * r + k - a ≤ r + k) := by omega
  simp only [dpsiP, ps_val, c1, c2, c3, c4, c5, c6, if_false, if_true, and_self, and_false, false_and, and_true]

theorem third_peeling_minor_mem_ideal {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel E) (ell : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => ps k r (if l.val < i then l.val else l.val + 1)) (fun l : Fin m => ps k r l.val)
        (ell + (m : ℂ) - 1) -
      qminor E (fun l : Fin i => ps k r l.val) (fun l : Fin i => ps k r l.val) (ell + (i : ℂ) - 1) ∈
      Ideal.span (rgen k r z' E) := by
  intro m
  induction m with
  | zero =>
    intro i hi _
    have hi0 : i = 0 := by omega
    subst hi0
    have e : (fun l : Fin 0 => ps k r (if l.val < 0 then l.val else l.val + 1)) = fun l : Fin 0 => ps k r l.val :=
      funext fun l => l.elim0
    rw [e, sub_self]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro i hi hr
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · have hih := ih i (by omega) (by omega)
      have hu : ell + ((m + 1 : ℕ) : ℂ) - 1 = ell + (m : ℂ) := by push_cast; ring
      rw [hu]
      have hstep : qminor E (fun l : Fin (m + 1) => ps k r (if l.val < i then l.val else l.val + 1))
            (fun l : Fin (m + 1) => ps k r l.val) (ell + (m : ℂ)) -
          qminor E (fun l : Fin m => ps k r (if l.val < i then l.val else l.val + 1))
            (fun l : Fin m => ps k r l.val) (ell + (m : ℂ) - 1) ∈ Ideal.span (rgen k r z' E) := by
        have hc := peel_core (Ideal.span (rgen k r z' E)) (ι := Unit) (fun _ => (1 : ℂ))
          (fun l : Fin (m + 1) => qminor E
              ((fun l : Fin (m + 1) => ps k r (if l.val < i then l.val else l.val + 1)) ∘ Fin.castSucc)
              ((fun l : Fin (m + 1) => ps k r l.val) ∘ l.succAbove) (ell + (m : ℂ) - 1))
          (fun l _ => Tm E (ell + (m : ℂ)) (ps k r (m + 1)) (ps k r l.val)) 1 ?_
        · rw [Formalism.FourierDecayAlt.P.expansion_last_line A (2 * r + k + 1) m E hG]
          have hm : ¬ (m < i) := by omega
          simpa [Fin.succAbove_last, Fin.val_last, hm, Function.comp_def, Fin.coe_castSucc] using hc
        · intro l
          have hl := l.isLt
          have hne : ps k r (m + 1) ≠ ps k r l.val := by
            intro e
            have := congrArg Fin.val e
            simp only [ps_val] at this
            omega
          have hin : InNp k r (ps k r (m + 1)) (ps k r l.val) := by
            simp only [InNp, ps_val]
            omega
          have hd : dpsiP k r z' (ps k r (m + 1)) (ps k r l.val) = if l.val = m then 1 else 0 := by
            rw [dpsi_last_basis_shift k r z' (m + 1) l.val (by omega) (by omega)]
            split_ifs <;> first | rfl | (exfalso; omega)
          simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, last_iff]
          rw [tm_offdiag _ _ hne, ← hd]
          exact mem_gen hin
      have hsum := (Ideal.span (rgen k r z' E)).add_mem hstep hih
      rwa [sub_add_sub_cancel] at hsum
    · have hi1 : i = m + 1 := by omega
      subst hi1
      have e : (fun l : Fin (m + 1) => ps k r (if l.val < m + 1 then l.val else l.val + 1)) =
          fun l : Fin (m + 1) => ps k r l.val := by
        funext l
        rw [if_pos l.isLt]
      rw [e, sub_self]
      exact Submodule.zero_mem _

private theorem sR_eq_ps (k r j : ℕ) (hj : j ≤ r) : sR k r j hj = fun l : Fin j => ps k r l.val := by
  funext l
  apply Fin.ext
  simp only [sR, Formalism.QuantumDeterminants.esI, Fin.coe_castLE, ps_val]

private theorem sR_succAbove_eq_ps (k r m : ℕ) (hm : m + 1 ≤ r) (i : Fin (m + 1)) :
    (fun l : Fin m => sR k r (m + 1) hm (i.succAbove l)) =
      fun l : Fin m => ps k r (if l.val < i.val then l.val else l.val + 1) := by
  funext l
  apply Fin.ext
  simp only [sR, Formalism.QuantumDeterminants.esI, Fin.coe_castLE, ps_val, succAbove_val]

theorem third_peeling_identity : PeelingDualColumn := by
  intro A _ _ k r z' E hG m hm i ell
  rw [sR_succAbove_eq_ps, sR_eq_ps, sR_eq_ps]
  exact third_peeling_minor_mem_ideal k r z' E hG ell m i.val (by have := i.isLt; omega) hm

theorem second_peeling_identity : PeelingCovector := by
  intro A _ _ k m z' yb E i u hz'
  have ha : xR k (m + 1) (m + 1) le_rfl = fun l : Fin (m + 1) => pe k (m + 1) l.val := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE]; rw [pe_lt (by omega)]
  have hb : (fun l : Fin m => xR k (m + 1) (m + 1) le_rfl (i.succAbove l)) =
      fun l : Fin m => pe k (m + 1) (if l.val < i.val then l.val else l.val + 1) := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE, succAbove_val, pe_val]; all_goals (split_ifs <;> omega)
  have hi : xR k (m + 1) i.val (by have := i.isLt; omega) = fun l : Fin i.val => pe k (m + 1) l.val := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE]; rw [pe_lt (by omega)]
  rw [hb, ha, hi]
  have step := peel_col (Ideal.span (rgen k (m + 1) z' E)) E (fun w => herm (Hpk k (m + 1)) (bvec (wI k (m + 1) w)) yb)
    (fun l : Fin (m + 1) => pe k (m + 1) l.val) (fun l : Fin m => pe k (m + 1) (if l.val < i.val then l.val else l.val + 1))
    (wI k (m + 1)) u (herm (Hpk k (m + 1)) z' yb) (by
      intro l
      have := l.isLt
      apply hT_of _ _ _ (fun w => dpsiP k (m + 1) z' (pe k (m + 1) l.val) (wI k (m + 1) w))
      · intro w
        have hw := w.isLt
        have hne : pe k (m + 1) l.val ≠ wI k (m + 1) w := by
          intro h2; have h3 := congrArg Fin.val h2; rw [pe_lt (by omega)] at h3; simp only [wI] at h3; omega
        rw [tm_offdiag _ _ hne]
        apply mem_gen
        simp only [InNp, wI]; rw [pe_lt (by omega)]; omega
      · simp only [dpsi_e_w k (m + 1) z' l.val (by omega), last_iff]
        by_cases hl : l.val = m
        · have e : l.val + 1 = m + 1 := by omega
          simp only [e, if_true, hl]
          rw [herm_wsum k (m + 1) z' yb hz']
          congr 1; ext w; ring
        · have e : ¬ (l.val + 1 = m + 1) := by omega
          simp [e, hl])
  have hc : ((fun l : Fin (m + 1) => pe k (m + 1) l.val) ∘ Fin.castSucc) = fun l : Fin m => pe k (m + 1) l.val := by
    funext l; simp
  rw [hc] at step
  have h2 := smul_mem' _ (herm (Hpk k (m + 1)) z' yb) (first_peeling_minor_mem_ideal k (m + 1) z' E u m i.val (by omega) (by omega))
  have := Ideal.add_mem _ step h2
  rw [smul_sub] at this
  simpa using this

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace UnipotentUpperFacts

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector

section gen

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

end gen

variable {k r : ℕ}

lemma N_upper {g : B.Mat k r} (hg : g ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hji : j ≤ i) :
    g i j = if i = j then 1 else 0 := by
  have hc := ((WeylGroupFacts.nset_iff g).mp hg).2
  by_cases hj : j.val ≤ r + k
  · exact hc i j hj (Or.inl hji)
  · push Not at hj
    have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
      apply Matrix.inv_eq_left_inv
      calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, WeylGroupFacts.hpk_sq]
    have hci := ((WeylGroupFacts.nset_iff _).mp (WeylGroupFacts.mem_n_inv hg)).2
    rw [hinv] at hci
    have hle : j.val ≤ i.val := hji
    have hsj := GBasic.sig_val k r j
    have hsi := GBasic.sig_val k r i
    rw [if_pos (Or.inr hj)] at hsj
    rw [if_pos (Or.inr (by omega))] at hsi
    have h := hci (GBasic.sig k r j) (GBasic.sig k r i) (by omega) (Or.inl (by omega))
    rw [Matrix.mul_assoc, Hpk_mul_apply, mul_Hpk_apply, Matrix.conjTranspose_apply, GBasic.sig_sig,
      GBasic.sig_sig] at h
    have hs1 : GBasic.sgn k r (GBasic.sig k r j) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    have hs2 : GBasic.sgn k r (GBasic.sig k r i) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    rw [hs1, hs2, one_mul, mul_one] at h
    have hiff : (GBasic.sig k r j = GBasic.sig k r i) ↔ (i = j) := by
      constructor
      · intro e; have := congrArg (GBasic.sig k r) e; rw [GBasic.sig_sig, GBasic.sig_sig] at this; exact this.symm
      · intro e; rw [e]
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : i = j
    · rw [if_pos (hiff.mpr e), if_pos e, star_one]
    · rw [if_neg (fun e' => e (hiff.mp e')), if_neg e, star_zero]

lemma N_unip {g : B.Mat k r} (hg : g ∈ Nset k r) : (g - 1) ^ (2 * r + k + 1) = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, N_upper hg i j hji, Matrix.one_apply, sub_self]

end UnipotentUpperFacts

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x6 FlagSpanVanishing HermitianXiVector UnipotentSums

private lemma mul_mem_Nset' {k r : ℕ} {A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hA : A ∈ Nset k r) (hB : B ∈ Nset k r) : A * B ∈ Nset k r := by
  obtain ⟨hAu, hAc, hAw⟩ := hA
  obtain ⟨hBu, hBc, hBw⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · have hAu' : Aᴴ * Hpk k r * A = Hpk k r := hAu
    have hBu' : Bᴴ * Hpk k r * B = Hpk k r := hBu
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [Matrix.conjTranspose_mul,
      show Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B by
        simp only [Matrix.mul_assoc], hAu', hBu']
  · intro a i hai
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
    · rw [hBc a (eI k r a) (le_refl a.val), if_pos rfl, mul_one]
      exact hAc a i hai
    · intro j _ hj
      by_cases hja : a.val ≤ j.val
      · rw [hBc a j hja, if_neg hj, mul_zero]
      · rw [not_le] at hja
        have hjr : j.val < r := lt_trans hja a.isLt
        have h1 := hAc ⟨j.val, hjr⟩ i (show j.val ≤ i.val by omega)
        rw [show eI k r ⟨j.val, hjr⟩ = j from Fin.ext rfl] at h1
        rw [h1, if_neg (by rintro rfl; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i j hj1 hj2 hi
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hBw j j hj1 hj2 hj1, if_pos rfl, mul_one]
      exact hAw i j hj1 hj2 hi
    · intro l _ hl
      by_cases hlr : r ≤ l.val
      · rw [hBw l j hj1 hj2 hlr, if_neg hl, mul_zero]
      · rw [not_le] at hlr
        have h1 := hAc ⟨l.val, hlr⟩ i (show l.val ≤ i.val by omega)
        rw [show eI k r ⟨l.val, hlr⟩ = l from Fin.ext rfl] at h1
        rw [h1, if_neg (by rintro rfl; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma dite_lt_eq_sum_smul_bvec {k r : ℕ} (g : Fin r → ℂ) :
    (fun p : Fin (2 * r + k + 1) => if hp : p.val < r then g ⟨p.val, hp⟩ else 0) =
      ∑ c, g c • bvec (eI k r c) := by
  funext p
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, bvec, smul_eq_mul, Pi.single_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single ⟨p.val, hp⟩]
    · rw [if_pos (show p = eI k r ⟨p.val, hp⟩ from Fin.ext rfl), mul_one]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro h
      apply hc
      apply Fin.ext
      show c.val = p.val
      rw [h]
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg, mul_zero]
    intro h
    apply hp
    rw [h]
    exact c.isLt

theorem c2_tau_mem : C2.TauMem := by
  intro k r z hz v hv
  set ξ : Fin r → ℂ := fun a => v a.castSucc (Fin.last r) with hξ
  set vX := v.submatrix Fin.castSucc Fin.castSucc with hvX
  have htau : C2.tauM k r z v = C2.nEich k r z ξ * C2.mX k r vX := rfl
  have hvX_mem : vX ∈ C2.UTset r :=
    ⟨fun i j hij => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij), fun i => hv.2 _⟩
  have hzW : ∀ i : Fin (2 * r + k + 1), r + k < i.val → z i = 0 := fun i hi => hz.1 i (Or.inr hi)
  have hxi : C2.xiV k r ξ = ∑ c, ξ c • bvec (eI k r c) := by
    rw [← dite_lt_eq_sum_smul_bvec]
    rfl
  have hfc : ∀ c : Fin r, fvec k r z c.castSucc = bvec (eI k r c) := by
    intro c
    simp [fvec]
  have hfl : fvec k r z (Fin.last r) = z := by
    simp [fvec]
  have hact : ∀ b, C2.tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a := by
    intro b
    rw [htau, ← Matrix.mulVec_mulVec, Fin.sum_univ_castSucc]
    simp only [hfc, hfl]
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · have hmz : C2.mX k r vX *ᵥ z = z := by
        funext p
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single p]
        · by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
          · rw [unipotent_apply_middle_column vX p p hp.1 hp.2, if_pos rfl, one_mul]
          · have : z p = 0 := by
              apply hz.1
              omega
            rw [this, mul_zero]
        · intro j _ hj
          by_cases hjW : r ≤ j.val ∧ j.val ≤ r + k
          · rw [unipotent_apply_middle_column vX p j hjW.1 hjW.2, if_neg (Ne.symm hj), zero_mul]
          · have : z j = 0 := by
              apply hz.1
              omega
            rw [this, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hfl, hmz, HermitianXiVector.nEich_apply]
      have h1 : herm (Hpk k r) z (C2.xiV k r ξ) = 0 :=
        HermitianXiVector.herm_X_right (C2.xiV k r ξ) z (HermitianXiVector.xiV_X ξ) hzW
      have h2 : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := hzz_real z
      have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hz.2)
      have hll : v (Fin.last r) (Fin.last r) = 1 := hv.2 _
      rw [h1, h2, hll, one_smul, ← hxi]
      have : ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) * (-(((-(Tz k r z) : ℝ) : ℂ))) = 1 := by
        push_cast
        field_simp
      rw [zero_smul, mul_zero, zero_smul, add_zero, add_zero, smul_smul, this, one_smul]
      exact add_comm _ _
    · have hmy : C2.mX k r vX *ᵥ bvec (eI k r b') =
          fun p => if hp : p.val < r then vX ⟨p.val, hp⟩ b' else 0 := by
        rw [FlagSpanVanishing.mulVec_bvec]
        funext p
        exact mX_col_X vX p b'
      have hyX : ∀ i : Fin (2 * r + k + 1), r ≤ i.val →
          (fun p : Fin (2 * r + k + 1) => if hp : p.val < r then vX ⟨p.val, hp⟩ b' else 0) i = 0 := by
        intro i hi
        simp only
        rw [dite_eq_right (by omega)]
      have h1 := HermitianXiVector.herm_X_left _ z hyX hzW
      have h2 := HermitianXiVector.herm_X_left _ (C2.xiV k r ξ) hyX (HermitianXiVector.xiV_apply_last_block_zero ξ)
      have hlow : v (Fin.last r) b'.castSucc = 0 := hv.1 _ _ (Fin.castSucc_lt_last b')
      rw [hfc, hmy, HermitianXiVector.nEich_apply, h1, h2, hlow, zero_smul, add_zero]
      simp only [neg_zero, zero_smul, mul_zero, add_zero, smul_zero]
      exact (dite_lt_eq_sum_smul_bvec (k := k) (fun c => vX c b')).trans rfl
  refine ⟨?_, hact, uMap_eq hz _ v hact⟩
  rw [htau]
  exact mul_mem_Nset' (HermitianXiVector.nEich_mem hz ξ) (mX_mem vX hvX_mem)

end Formalism.FourierDecayAlt.P
end

