module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
public import Formalism.DoubleCosetMeasures.Statement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainX1
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem chainX1' {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ) (c : Fin r → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (hG : GlRel E) (m : ℕ) (hm : m + 2 ≤ r)
    (u : ℂ)
    (hR0 : ∀ (x : A) (l : ℕ) (hl : l < m), La (x * E (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0)
    (hR1 : ∀ x : A, La (x * E (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = La x)
    (hL : ∀ (x : A) (q : ℕ) (hq : q ≤ m), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
      (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • La x) :
    La (qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.castSucc l)) = eI k r ⟨l.val, by omega⟩ := by ext; rw [hav]; simp [eI]
    have ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [ha1, ha2, hR0 _ l.val l.isLt, smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs]
    have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [h1]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.last m) := by
        intro h'; have := congrArg Fin.val h'; simp [eI, xR] at this
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.last m) = eI k r ⟨m, by omega⟩ := by ext; simp [xR, eI]
      rw [hx, hL _ m le_rfl, if_pos rfl]
      have hcs2 : xR k r (m + 1) (by omega) ∘ Fin.castSucc = xR k r m (by omega) := by funext q; ext; simp [xR, eI]
      rw [hcs2, smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hqv : (xR k r (m + 1) (by omega) (Fin.castSucc q)).val = q.val := by simp [xR, eI]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.castSucc q) := by
        intro h'; have := congrArg Fin.val h'; rw [hqv] at this; simp [eI] at this; omega
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.castSucc q) = eI k r ⟨q.val, by omega⟩ := by ext; simp [xR, eI]
      have hq := q.isLt
      rw [hx, hL _ q.val (by omega), if_neg (by omega), zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.last m)) = eI k r ⟨m, by omega⟩ := by ext; rw [hav]; simp [eI]
    have ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [ha1, ha2, hR1]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.PBN
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBesselEigen
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP

theorem thr_of_budget (k r : ℕ) (N A₀ : ℝ) (hk : 2 ≤ k) (hN : 0 ≤ N)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * (N * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    JF.TransportedAlt k r A₀ (2 * r + k + 1) := by
  unfold JF.TransportedAlt
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  rw [hcast, lt_div_iff₀ (by positivity)]
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    calc (r : ℝ) + 1 = ((r : ℝ) + 1) * 1 := by ring
      _ ≤ ((r : ℝ) + 1) * ((r : ℝ) + 1) ^ 3 := by gcongr
      _ = ((r : ℝ) + 1) ^ 4 := by ring
  have h3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 = n ^ 2 * 1 := by ring
      _ ≤ n ^ 2 * n := by gcongr
      _ = n ^ 3 := by ring
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  have hstep : 100 * ((r : ℝ) + 1) * n ^ 2 ≤ A₀ := by
    calc 100 * ((r : ℝ) + 1) * n ^ 2 ≤ 100 * ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
          have : ((r : ℝ) + 1) * n ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
            calc ((r : ℝ) + 1) * n ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * n ^ 2 := by gcongr
              _ ≤ ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by gcongr; linarith
          linarith
      _ ≤ A₀ := hA
  have hrn : (r : ℝ) * n ≤ ((r : ℝ) + 1) * n ^ 2 := by
    have : (r : ℝ) ≤ (r : ℝ) + 1 := by linarith
    calc (r : ℝ) * n ≤ ((r : ℝ) + 1) * n := by gcongr
      _ = ((r : ℝ) + 1) * n * 1 := by ring
      _ ≤ ((r : ℝ) + 1) * n * n := by gcongr
      _ = ((r : ℝ) + 1) * n ^ 2 := by ring
  have hpos : 0 < ((r : ℝ) + 1) * n ^ 2 := by positivity
  nlinarith

theorem bessel_eigenvalue_equation_holds : BesselEigen := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Y x hx
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, hCk, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, hCC, heig⟩ := hv v
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA
  have hT : Tz S.G.k S.G.r (T v).base.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r (T v).base.z' = S.T' := hplace.2.2.2.2.1
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hg : B.gq (T v).base x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' :=
    Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base x hq
  have hgG : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg.1
  have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) (f v) :=
    Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (hCk v)
  rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ p ∂(T v).base.μSS,
      JF.xiP (T v).base p • Q.CV S.G.k S.G.r (Y : ℂ) (B.rho (T v).base p (f v)) (B.gq (T v).base x) =
        ((S.P v Y : ℝ) : ℂ) • (JF.xiP (T v).base p • B.rho (T v).base p (f v) (B.gq (T v).base x)) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS (T v).base] with p hp
    rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ (T v).base (Y : ℂ) (f v) p hp hCkn _ hgG]
    have hs := Formalism.FourierDecayAlt.P.B7.sgs_mem (T v).base hp hgG
    simp only [B.rho]
    rw [heig Y _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopCut
section
noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

def MkTopCut : Prop :=
  ∀ r : ℕ, ∃ β : (Fin r → Fin r → ℂ) → ℝ,
    ContDiffOn ℝ ∞ β {Z | (Matrix.of Z).det ≠ 0} ∧
    (∀ Z : Fin r → Fin r → ℂ, (Matrix.of Z).det ≠ 0 →
      Integrable (fun v : G.UT r → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) ∧
        ∫ v : G.UT r → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1) ∧
    ∀ (X : Type) [TopologicalSpace X] (K : Set ((Fin r → Fin r → ℂ) × X)), IsCompact K →
      (∀ q ∈ K, (Matrix.of q.1).det ≠ 0) →
      ∃ K' : Set ((Fin r → Fin r → ℂ) × X), IsCompact K' ∧
        (∀ q ∈ K', (Matrix.of q.1).det ≠ 0 ∧ ∃ q₀ ∈ K, q.2 = q₀.2) ∧
        ∀ q : (Fin r → Fin r → ℂ) × X, (Matrix.of q.1).det ≠ 0 → β q.1 ≠ 0 →
          (∃ u : Matrix (Fin r) (Fin r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
          q ∈ K'

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem toSm_of_mem (P : M.Par) {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) (q : MA.Qp P.r P.TT) :
    (MA.toSm P u : MA.Qp P.r P.TT → ℂ) q = u q := by
  unfold MA.toSm
  rw [dite_eq_left h]

theorem assumption_on_sections_holds : AsmSec := by
  intro hFL hGQ hML hRS hRaw hQL Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl
  obtain ⟨e, he, hQQ⟩ := hGQ Wp Wq P Bs hPl hk hsec X
  refine ⟨e, he, fun Dc Φ hΦ Y a b ρ => ?_⟩
  apply Subtype.ext
  funext q
  have hLsm := hRaw Wp Wq P Bs hPl hk e he Dc _ (hQL Wp Wq P Bs hPl hk Dc Φ hΦ Y a b) ρ
  rw [toSm_of_mem P hLsm q]
  obtain ⟨Φt, V, hV, hagree⟩ := hFL Wp Wq P Bs hPl hk X Dc Φ hΦ q
  have h1 : rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ q =
      rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φt : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    unfold rawR
    rw [((hagree q.1.2 (mem_of_mem_nhds hV)).2 (Y : ℂ) a b).symm]
  rw [h1, ← toSm_of_mem P (hRS Wp Wq P Bs hPl hk e he (X.t (Y : ℂ) a b Φt) ρ) q]
  show (trR P Bs e (X.t (Y : ℂ) a b Φt) ρ : MA.Qp P.r P.TT → ℂ) q = _
  rw [hQQ Φt (Y : ℂ) a b]
  refine hML P (trR P Bs e Φt) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) q.1.1 (interior V) isOpen_interior
    (fun ρ' q' hq'c hq'V => ?_) (Y : ℂ) a b ρ q rfl (mem_interior_iff_mem_nhds.2 hV)
  show (MA.toSm P (rawR P Bs.μsec e (Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ') : MA.Qp P.r P.TT → ℂ) q' =
    (MA.toSm P (rawR P Bs.μsec e Φ ρ') : MA.Qp P.r P.TT → ℂ) q'
  rw [toSm_of_mem P (hRS Wp Wq P Bs hPl hk e he Φt ρ') q',
    toSm_of_mem P (hRaw Wp Wq P Bs hPl hk e he Dc Φ hΦ ρ') q']
  unfold rawR
  rw [hq'c, (hagree q'.1.2 (interior_subset hq'V)).1]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_space_smoothness : RadSpSmooth := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ e he Φ ρ
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  have hz : inWb P.k P.r Bs.z := hpl.2.1
  have hz' : inWb P.k P.r Bs.z' := hpl.2.2.1
  set Qs := MA.Qset P.r P.TT with hQs
  have hζ : ∀ x ∈ Qs, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq x.2 := by
    intro x hx
    rw [hT, hT']
    exact hx.2
  have hmZ : ContDiffOn ℝ ∞ (fun x : MA.E P.r => NF.muZ P.k P.r Bs.μsec x.2) Qs :=
    (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).comp contDiff_snd.contDiffOn fun x hx => hζ x hx
  have hm : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) Qs :=
    contDiffOn_fst.prodMk hmZ
  have hGl : ∀ x ∈ Qs, NF.muZ P.k P.r Bs.μsec x.2 ∈ Q.Glev P.k P.r (Fin.last P.r) := fun x hx =>
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec (hζ x hx))
  have hD : ∀ x ∈ Qs, (x.1, NF.muZ P.k P.r Bs.μsec x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' := fun x hx =>
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := x) ⟨hx.1, hζ x hx⟩
  have hΦq : ContDiffOn ℝ ∞ (fun x : MA.E P.r =>
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (NF.muZ P.k P.r Bs.μsec x.2)) Qs := by
    refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := Φ.2.2.1 _ (hD x₀ hx₀)
    refine ⟨Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U,
      hm.continuousOn.isOpen_inter_preimage (MA.Qset_open P.r P.TT) hU, ⟨hx₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun x : MA.E P.r => F (x.1, NF.muZ P.k P.r Bs.μsec x.2))
        (Qs ∩ (Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U)) :=
      hF.comp (hm.mono fun x hx => hx.1) fun x hx => hx.2.2
    exact hc.congr fun x hx => hΦF _ hx.2.2 (hGl x hx.1)
  have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) Qs :=
    (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
  have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => ((wR P.k P.TT x.2 : ℝ) : ℂ)) Qs := by
    refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
    unfold wR
    refine (((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt
      fun x hx => ?_
    have h2 : P.TT < Complex.normSq x.2 := hx.2
    exact (pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'
  have hin : ContDiffOn ℝ ∞ (fun x : MA.E P.r =>
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (NF.muZ P.k P.r Bs.μsec x.2)))) Qs :=
    (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn hΦq)
  have hall := hw.mul hin
  show ContDiffOn ℝ MA.sm (MA.ext _) Qs
  refine hall.congr fun x hx => ?_
  exact dif_pos hx

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def absTy (P : M.Par) (ρ : M.Ty P) : ℝ := ∑ i ∈ Finset.Icc 1 (P.k - 1), M.rho P ρ i

def ThetaC {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) : A :=
  d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs + d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))

def GTCCurvPoly : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel → 2 ≤ P.k →
    d.L.TT = (P.TT : ℂ) →
    MAx3.G.PolyIn (fun u => d.QQ u 0 0 - u ^ (P.k + 1) • (1 : A) - u ^ P.k • ThetaC d) (P.k - 1) ∧
    MAx3.G.PolyIn (fun u => d.QQ u 1 0) P.k

def GTCCurvRTT : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (f g : ℂ → A) (Θ : A), 1 ≤ n →
    (∀ u v : ℂ, (u - v) • (f u * g v - g v * f u) = g u * f v - g v * f u) →
    MAx3.G.PolyIn (fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ) (n - 1) →
    MAx3.G.PolyIn g n → ∀ v, Θ * g v - g v * Θ = - g v

def GTCCurvBlock : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel →
    (∀ v : ℂ, ThetaC d * d.QQ v 1 0 - d.QQ v 1 0 * ThetaC d = - d.QQ v 1 0) →
    ∀ ρ : M.Ty P, (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
      algebraMap ℂ A ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)

def GTCCurvIdOfCut : Prop := GTCCurvPoly → GTCCurvRTT → GTCCurvBlock → GTCCurvId

theorem gTCCurvId_of_cut : GTCCurvIdOfCut := by
  intro hPo hR hB Wp Wq _ _ _ _ _ _ P Bs X d hyp ρ
  obtain ⟨hPl, hk, -, hAL, -, hRel, hQQ⟩ := hyp
  have hS : Wd.IsStart d.QQ (M.qC P) := by
    have h0 := (Formalism.FourierDecayAlt.P.actual_start Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X).1
    rwa [show X.QQ = d.QQ from funext hQQ] at h0
  have hTT : d.L.TT = (P.TT : ℂ) := by
    rw [hAL.2.2.2.2.2.2.2.2.2.2.2.2, Formalism.FourierDecayAlt.P.NFx4.TT_eq hPl]
  obtain ⟨h1, h2⟩ := hPo P _ d hRel hk hTT
  have hc := hR _ P.k (fun u => d.QQ u 0 0) (fun u => d.QQ u 1 0) (ThetaC d) (by omega)
    (fun u v => Formalism.FourierDecayAlt.P.NFx4.SX.rtt_ent d hS u v 0 0 1 0) h1 h2
  exact hB P _ d hRel hc ρ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesLeft
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep in
theorem gauge_left_line_holds : GLLeft := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk ζ hζ Fr hFr
  obtain ⟨-, hz, hz', hTz, hTz', -, -⟩ := hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hU : μ ∈ UH (Hpk P.k P.r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hUi : μ⁻¹ ∈ UH (Hpk P.k P.r) := hGi.1
  have hT := Bs.T_pos

  set y := μ *ᵥ Bs.z' with hydef
  have hy : inWb P.k P.r y := Qx8.inWb_mulVec hG hz'
  have hyz : herm (Hpk P.k P.r) y Bs.z = ζ := by
    rw [← NFRadRedA.zeta_eq]; exact NFRadRedA.zeta_muZ hz hz' Bs.sec hζ'
  have hyy : herm (Hpk P.k P.r) y y = -((Tz P.k P.r Bs.z' : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hU, FrameEntries.herm_self]
  have hpos : 0 < Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z' := by
    rw [sub_pos, lt_div_iff₀ hT]; linarith
  set p := SSn.prWv P.k P.r Bs.z y with hpdef
  have hpp := DU.prWv_norm hT hy hyy hyz
  have hre : (herm (Hpk P.k P.r) p p).re = Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z' := by
    rw [hpp]; simp
  have hν : SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ =
      (((Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z'))⁻¹ : ℝ) : ℂ) • p := by
    show SSn.unitH P.k P.r p = _
    unfold SSn.unitH
    rw [hre]
  have hsne : (((Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z'))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z') := Real.sqrt_pos.2 hpos
    exact_mod_cast (inv_pos.2 this).ne'

  have hFz : ∀ a, herm (Hpk P.k P.r) (Fr a) Bs.z = 0 := fun a => hFr.2.2 a Bs.z (by simp)
  have hFy : ∀ a, herm (Hpk P.k P.r) (Fr a) y = 0 := by
    intro a
    have h1 : herm (Hpk P.k P.r) (Fr a) (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 := hFr.2.2 a _ (by simp)
    rw [hν, DU.hsmul_r] at h1
    have h2 : herm (Hpk P.k P.r) (Fr a) p = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) hsne
      · exact h
    rw [hpdef, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hFz a, mul_zero, add_zero] at h2
    exact h2
  have hmi : μ⁻¹ * μ = 1 := Gauge.GC.KLAM.inv_mul_uh hU
  have hmm : μ * μ⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  have hz'e : Bs.z' = μ⁻¹ *ᵥ y := by
    rw [hydef, Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hF' : Q.IsFrameOf P.k P.r [μ⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => μ⁻¹ *ᵥ Fr a) := by
    refine ⟨fun a => Qx8.inWb_mulVec hGi (hFr.1 a), fun a b => ?_, fun a w hw => ?_⟩
    · rw [Qx2.herm_uh hUi]; exact hFr.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rw [Qx2.herm_uh hUi]; exact hFz a
      · rw [hz'e, Qx2.herm_uh hUi]; exact hFy a
  refine ⟨hF', fun X hX w v => ?_⟩
  have hXF : X ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hX (h, h') ⟨hh, hh', he⟩
  have hint := Qx8.capRep_intertwine hF' Bs.π'_rep Bs.π'_cont hU X
    (fun h' hh' hy' u => Gauge.GC.KLAM.fib_intertwine Bs.π_rep hG hXF hh' hy' u) w v
  have hback : (fun a => μ *ᵥ (μ⁻¹ *ᵥ Fr a)) = Fr := by
    funext a
    rw [Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  rw [hint, hback]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

