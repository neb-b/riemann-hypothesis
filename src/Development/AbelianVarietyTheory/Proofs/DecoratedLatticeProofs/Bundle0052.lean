module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiveLeHalfKfk
section
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem exp_neg_five_lt : Real.exp (-5) < 1 / 128 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2.7 : ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : (128 : ℝ) < Real.exp 5 := by
    rw [h5]; exact lt_trans (by norm_num) h2
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) h3

theorem five_le_half_kfk (D : D7) : 5 ≤ kfk D / 2 := by
  have hk : 5 ≤ D.R.k := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    omega
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hlog : 1 ≤ Real.log (D.R.k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hkf : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f := by nlinarith
  have : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * Real.log (D.R.k : ℝ) := by nlinarith
  unfold kfk
  linarith

theorem two_eDiag_lt : ∀ (D : D7) (u : D.what₂.Word) (L C : ℝ), 5 ≤ C * mfL D L → 4 * D.R.f + 1 ≤ (D.mem u).A.T → 2 * eDiag D L C < 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) := by
  intro D u L C hC hT
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hTR : 4 * (D.R.f : ℝ) + 1 ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT
  have hden : 0 < ((D.mem u).A.T : ℝ) - 1 := by linarith
  have hq : (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ hden]
    linarith
  have h5 := exp_neg_five_lt
  have hA : Real.exp (-(C * mfL D L)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith)
  have hB : Real.exp (-(kfk D / 2)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith [five_le_half_kfk D])
  unfold eDiag
  linarith

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagBasisLiftGramSignedPermutation
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FlagBasis.GramLift
open Formalism.L2.SG.Pf.unitaryCongruence

theorem hatL_eq (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩; exact ⟨y, hy, rfl⟩

theorem col_mem (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hF : IsFrame β I.L) (j : Fin I.n) :
    (fun i => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j) ∈ I.Lf := by
  rw [← hatL_eq]
  refine (hF _).2 fun i => ?_
  have h1 : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β = 1 := Units.inv_mul β
  have h2 : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).mulVec
      (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) i = (1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j := by
    rw [← h1]; rfl
  have h3 : (1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ IntAf I.F I.E := by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← h2] at h3
  exact h3

section
variable (I : AutInst) (g : ℕ)

theorem Z_of_eq {a b : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : a = b) (hb : ZMod' I g b) : ZMod' I g a := h ▸ hb

theorem Z_symm {x y : VA I} (h : ZMod' I g (hA I x y)) : ZMod' I g (hA I y x) := by
  rw [hA_symm]; exact Z_sig I g h

theorem Z_symm_sub {x y : VA I} {c : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : ZMod' I g (hA I x y - c)) :
    ZMod' I g (hA I y x - sigA I c) := by
  rw [hA_symm, ← map_sub]; exact Z_sig I g h

theorem Z_sub_zero {a : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : ZMod' I g a) : ZMod' I g (a - 0) := by rwa [sub_zero]

theorem Z_addR {x y z : VA I} (h : ZMod' I g (hA I x y)) (h' : ZMod' I g (hA I x z)) :
    ZMod' I g (hA I x (y + z)) := by
  rw [hA_add_right]; exact Z_add I g h h'

theorem idem_sum {z0 : VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hz : z0 ∈ I.Lf) (hzz : ZMod' I g (hA I z0 z0 + 1))
    (hint : ew ∈ IntAf I.F I.E) (hfull : ∀ y ∈ I.Lf, (1 - ew - sigA I ew) • y ∈ mL I g) :
    ZMod' I g (1 - ew - sigA I ew) := by
  have hc : (1 - ew - sigA I ew) ∈ IntAf I.F I.E := sub_mem (sub_mem (one_mem _) hint) (sigA_mem I hint)
  have h1 : ZMod' I g (hA I z0 ((1 - ew - sigA I ew) • z0)) := mL_Qs I g hz (hfull z0 hz)
  rw [hA_smul_right] at h1
  exact Z_of_eq I g (by ring) (Z_sub I g (Z_smul I g hc hzz) h1)

theorem middle {k : ℕ} {bw bwd : Fin k → VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (horth : ew * sigA I ew = 0)
    (hbw : ∀ i, bw i = ew • bw i) (hbwd : ∀ i, bwd i = sigA I ew • bwd i)
    (hdual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0))
    (hsum : ZMod' I g (1 - ew - sigA I ew)) (l m : Fin k) :
    ZMod' I g (hA I (bw l + bwd l.rev) (bw m + bwd m.rev) - if m = l.rev then 1 else 0) := by
  have hbb : hA I (bw l) (bw m) = 0 := by
    calc hA I (bw l) (bw m) = hA I (ew • bw l) (ew • bw m) := by rw [← hbw l, ← hbw m]
      _ = (ew * sigA I ew) * hA I (bw l) (bw m) := by rw [hA_smul_left, hA_smul_right]; ring
      _ = 0 := by rw [horth, zero_mul]
  have hdd : hA I (bwd l.rev) (bwd m.rev) = 0 := by
    calc hA I (bwd l.rev) (bwd m.rev) = hA I (sigA I ew • bwd l.rev) (sigA I ew • bwd m.rev) := by
          rw [← hbwd l.rev, ← hbwd m.rev]
      _ = (ew * sigA I ew) * hA I (bwd l.rev) (bwd m.rev) := by
          rw [hA_smul_left, hA_smul_right, sigA_sigA]; ring
      _ = 0 := by rw [horth, zero_mul]
  have h3 := hdual l.rev m
  have h4 := Z_symm_sub I g (hdual m.rev l)
  rw [hA_add_left, hA_add_right, hA_add_right, hbb, hdd]
  by_cases hml : m = l.rev
  · rw [if_pos hml.symm] at h3
    rw [if_pos (by rw [hml, Fin.rev_rev])] at h4
    rw [if_pos hml]
    exact Z_of_eq I g (by ring) (Z_sub I g (Z_add I g h3 h4) hsum)
  · rw [if_neg (fun h => hml h.symm)] at h3
    rw [if_neg (fun h => hml (by rw [← h, Fin.rev_rev])), map_zero] at h4
    rw [if_neg hml]
    exact Z_of_eq I g (by ring) (Z_add I g h3 h4)

end

theorem flagVec_cases {V : Type} [AddCommGroup V] {ρ k : ℕ} (e0 f0 : Fin ρ → V) (z0 : V) (bw bwd : Fin k → V)
    (j : ℕ) (hj : j < 2 * ρ + k + 1) :
    (∃ a : Fin ρ, j = a.1 ∧ dualIdx ρ k j = 2 * ρ + k - a.1 ∧ flagVec e0 f0 z0 bw bwd j = e0 a) ∨
    (∃ l : Fin k, j = ρ + l.1 ∧ dualIdx ρ k j = ρ + (k - (l.1 + 1)) ∧
      flagVec e0 f0 z0 bw bwd j = bw l + bwd l.rev) ∨
    (j = ρ + k ∧ dualIdx ρ k j = ρ + k ∧ flagVec e0 f0 z0 bw bwd j = z0) ∨
    (∃ a : Fin ρ, j = 2 * ρ + k - a.1 ∧ dualIdx ρ k j = a.1 ∧ flagVec e0 f0 z0 bw bwd j = f0 a) := by
  by_cases h1 : j < ρ
  · refine Or.inl ⟨⟨j, h1⟩, rfl, ?_, ?_⟩
    · unfold dualIdx; rw [if_pos h1]
    · unfold flagVec; rw [dite_eq_left h1]
  by_cases h2 : j - ρ < k
  · refine Or.inr (Or.inl ⟨⟨j - ρ, h2⟩, ?_, ?_, ?_⟩)
    · show j = ρ + (j - ρ); omega
    · show dualIdx ρ k j = ρ + (k - (j - ρ + 1)); unfold dualIdx; split_ifs <;> omega
    · unfold flagVec; rw [dite_eq_right h1, dite_eq_left h2]
  by_cases h3 : j = ρ + k
  · refine Or.inr (Or.inr (Or.inl ⟨h3, ?_, ?_⟩))
    · unfold dualIdx; split_ifs <;> omega
    · unfold flagVec; rw [dite_eq_right h1, dite_eq_right h2, if_pos h3]
  have h4 : 2 * ρ + k - j < ρ := by omega
  refine Or.inr (Or.inr (Or.inr ⟨⟨2 * ρ + k - j, h4⟩, ?_, ?_, ?_⟩))
  · show j = 2 * ρ + k - (2 * ρ + k - j); omega
  · show dualIdx ρ k j = 2 * ρ + k - j; unfold dualIdx; split_ifs <;> omega
  · unfold flagVec; rw [dite_eq_right h1, dite_eq_right h2, if_neg h3, dite_eq_left h4]

section
variable {R : Type} [CommRing R] {n ρ k : ℕ} {i j : Fin n}

theorem flagGram_zero (h : j.val ≠ dualIdx ρ k i.val) : flagGram R n ρ k i j = 0 := if_neg h

theorem flagGram_neg (h : j.val = dualIdx ρ k i.val) (h' : i.val = ρ + k) : flagGram R n ρ k i j = -1 :=
  (if_pos h).trans (if_pos h')

theorem flagGram_ite {p : Prop} [Decidable p] (h : j.val = dualIdx ρ k i.val ↔ p) (h' : i.val ≠ ρ + k) :
    flagGram R n ρ k i j = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp]; exact (if_pos (h.2 hp)).trans (if_neg h')
  · rw [if_neg hp]; exact if_neg fun hh => hp (h.1 hh)

end

section
variable {I : AutInst} {g : ℕ} {ρ k : ℕ} {e0 f0 : Fin ρ → VA I} {z0 : VA I} {bw bwd : Fin k → VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)}

theorem flagVec_mem (hR : IsRefFrame I g e0 f0 z0 bw bwd ew) (j : ℕ) (hj : j < 2 * ρ + k + 1) :
    flagVec e0 f0 z0 bw bwd j ∈ I.Lf := by
  obtain ⟨⟨hef, hz, hb⟩, -⟩ := hR
  rcases flagVec_cases e0 f0 z0 bw bwd j hj with ⟨a, -, -, hv⟩ | ⟨l, -, -, hv⟩ | ⟨-, -, hv⟩ | ⟨a, -, -, hv⟩ <;> rw [hv]
  · exact (hef a).1
  · exact add_mem (hb l).1 (hb _).2
  · exact hz
  · exact (hef a).2

theorem flagVec_gram (hR : IsRefFrame I g e0 f0 z0 bw bwd ew) {n : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    ZMod' I g (hA I (flagVec e0 f0 z0 bw bwd i.val) (flagVec e0 f0 z0 bw bwd j.val) - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) n ρ k i j) := by
  obtain ⟨⟨hef, hz, hb⟩, hgram, ⟨hzz, hez⟩, hW, ⟨hid, horth, hint, hfull⟩, ⟨hbw, hbwd⟩, hdual, -⟩ := hR
  have hsum := idem_sum I g hz hzz hint hfull
  have hec : ∀ a m, ZMod' I g (hA I (e0 a) (bw m + bwd m.rev)) := fun a m =>
    Z_addR I g ((hW m).2.2 a).1 ((hW m.rev).2.2 a).2.2.1
  have hfc : ∀ a m, ZMod' I g (hA I (f0 a) (bw m + bwd m.rev)) := fun a m =>
    Z_addR I g ((hW m).2.2 a).2.1 ((hW m.rev).2.2 a).2.2.2
  have hzc : ∀ m, ZMod' I g (hA I z0 (bw m + bwd m.rev)) := fun m =>
    Z_addR I g (hW m).1 (hW m.rev).2.1
  have hi0 : i.val < 2 * ρ + k + 1 := hn ▸ i.isLt
  have hj0 : j.val < 2 * ρ + k + 1 := hn ▸ j.isLt
  rcases flagVec_cases e0 f0 z0 bw bwd i hi0 with ⟨a, hi, hd, hv⟩ | ⟨a, hi, hd, hv⟩ | ⟨hi, hd, hv⟩ | ⟨a, hi, hd, hv⟩ <;>
    rcases flagVec_cases e0 f0 z0 bw bwd j hj0 with ⟨b, hj, -, hw⟩ | ⟨b, hj, -, hw⟩ | ⟨hj, -, hw⟩ | ⟨b, hj, -, hw⟩ <;>
    rw [hv, hw]
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hgram a b).1
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hec a b)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hez a).1
  · rw [flagGram_ite (p := a = b) (by rw [Fin.ext_iff]; omega) (by omega)]; exact (hgram a b).2.2
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hec b a))
  · rw [flagGram_ite (p := b = a.rev) (by rw [Fin.ext_iff, Fin.val_rev]; omega) (by omega)]
    exact middle I g horth hbw hbwd hdual hsum a b
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hzc a))
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hfc b a))
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hez b).1)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hzc b)
  · rw [flagGram_neg (by omega) hi, sub_neg_eq_add]; exact hzz
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hez b).2)
  · rw [flagGram_ite (p := b = a) (by rw [Fin.ext_iff]; omega) (by omega)]
    have h := Z_symm_sub I g (hgram b a).2.2
    rwa [apply_ite (sigA I), map_one, map_zero] at h
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hfc a b)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hez a).2
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hgram a b).2.1

end

theorem gramIn_lift : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 →
    ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β →
      ZMod' I g (1 - ew - sigA I ew) ∧
        (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) := by
  intro I g ρ k e0 f0 z0 bw bwd ew hR hn β hL
  refine ⟨idem_sum I g hR.1.2.1 hR.2.2.1.1 hR.2.2.2.2.1.2.2.1 hR.2.2.2.2.1.2.2.2, fun i j => ?_⟩
  have h0 := flagVec_gram hR hn i j
  have hi0 : i.val < 2 * ρ + k + 1 := by have := i.isLt; omega
  have h1 := Z_symm I g (mL_Qs I g (col_mem I hL.1 j) (hL.2 i))
  have h2 : ZMod' I g (hA I _ _) := mL_Qs I g (flagVec_mem hR i hi0) (hL.2 j)
  rw [hA_sub_right] at h2
  have h3 := hA_add_left I ((fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l i) - flagVec e0 f0 z0 bw bwd i.val)
    (flagVec e0 f0 z0 bw bwd i.val) (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j)
  rw [sub_add_cancel] at h3
  refine Z_of_eq I g ?_ (Z_add I g (Z_add I g h1 h2) h0)
  unfold gramIn
  rw [h3]; ring

end GlobalTheory.FlagBasis.GramLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagRootSumDualEqSymmetricEdgeSum
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RootSumDual

theorem dualIdx_lt {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : ℕ) (hi : i < n) : dualIdx ρ k i < n := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_invol {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : ℕ) (hi : i < n) :
    dualIdx ρ k (dualIdx ρ k i) = i := by
  unfold dualIdx; split_ifs <;> omega

def tau {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (fun i => ⟨dualIdx ρ k i.val, dualIdx_lt hn i.val i.2⟩)
    (fun i => Fin.ext (dualIdx_invol hn i.val i.2))

theorem tau_val {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : (tau hn i).val = dualIdx ρ k i.val := rfl

theorem tau_tau {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : tau hn (tau hn i) = i :=
  Fin.ext (dualIdx_invol hn i.val i.2)

def sgn (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : K := if i.val = ρ + k then -1 else 1

theorem sgn_tau (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) :
    sgn K ρ k (tau hn i) = sgn K ρ k i := by
  unfold sgn; rw [tau_val]; unfold dualIdx; split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : sgn K ρ k i * sgn K ρ k i = 1 := by
  unfold sgn; split_ifs <;> simp

theorem flagGram_apply (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if j = tau hn i then sgn K ρ k i else 0 := by
  unfold flagGram sgn; simp only [Fin.ext_iff, tau_val]

theorem flagGram_mul (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (flagGram K n ρ k * X) i j = sgn K ρ k i * X (tau hn i) j := by
  rw [Matrix.mul_apply]; simp only [flagGram_apply K hn, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mul_flagGram (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (X * flagGram K n ρ k) i j = X i (tau hn j) * sgn K ρ k j := by
  rw [Matrix.mul_apply]
  have e : ∀ b : Fin n, (j = tau hn b) ↔ (b = tau hn j) := fun b =>
    ⟨fun h => by rw [h, tau_tau], fun h => by rw [h, tau_tau]⟩
  simp only [flagGram_apply K hn, e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sgn_tau]

theorem flagGram_mul_self (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) :
    flagGram K n ρ k * flagGram K n ρ k = 1 := by
  ext i j
  rw [flagGram_mul K hn, flagGram_apply K hn, tau_tau, Matrix.one_apply, sgn_tau]
  split_ifs with h h' h'
  · exact sgn_mul_self K ρ k i
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · exact mul_zero _

end GlobalTheory.RootSumDual

namespace GlobalTheory.RootSumDual

theorem inv_adj {K : Type} [CommRing K] {n ρ k : ℕ} {M : GL (Fin n) K} (hM : M ∈ unipSym K n ρ k) (i j : Fin n)
    (hij : j.val = i.val + 1) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = - (M : Matrix (Fin n) (Fin n) K) i j := by
  have h1 : M ∈ unip K n := hM.1
  have h := unip_mul_entry ((unip K n).inv_mem h1) h1 (show i < j by show i.val < j.val; omega)
    (fun l hil hlj => by
      have a : i.val < l.val := hil
      have b : l.val < j.val := hlj
      omega)
  rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (by intro e; rw [e] at hij; omega)] at h
  linear_combination -h

theorem dual_entry {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k)
    (i j : Fin n) :
    (M' : Matrix (Fin n) (Fin n) K) (tau hn j) (tau hn i) =
      sgn K ρ k i * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j * sgn K ρ k j := by
  set G := flagGram K n ρ k
  set Mi := ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hMM : (M : Matrix (Fin n) (Fin n) K) * Mi = 1 := Units.mul_inv M
  have h2 : (M' : Matrix (Fin n) (Fin n) K)ᵀ * G = G * Mi := by
    conv_rhs => rw [← h, Matrix.mul_assoc _ (M : Matrix (Fin n) (Fin n) K), hMM, Matrix.mul_one]
  have h3 : (M' : Matrix (Fin n) (Fin n) K)ᵀ = G * Mi * G := by
    rw [← h2, Matrix.mul_assoc, flagGram_mul_self K hn, Matrix.mul_one]
  have h4 := congrFun (congrFun h3 (tau hn i)) (tau hn j)
  rw [transpose_apply] at h4
  rw [h4, mul_flagGram K hn, flagGram_mul K hn, tau_tau, tau_tau, sgn_tau, sgn_tau]

theorem sum_reindex {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (f : Fin n → Fin n → K) :
    ∑ i, ∑ j, f i j = ∑ i, ∑ j, f (tau hn j) (tau hn i) := by
  rw [Finset.sum_comm]
  refine (Equiv.sum_comp (tau hn) _).symm.trans (Finset.sum_congr rfl fun x _ => ?_)
  exact (Equiv.sum_comp (tau hn) (fun i => f i (tau hn x))).symm

theorem rootSum_dual_edges : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ ε ε' a₁ a₂ : K, (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1) → a₁ ≠ 0 → a₂ ≠ 0 → ∃ a : Fin n → Fin n → K, (∀ i j, symEdge ρ k i j → a i j ≠ 0) ∧ ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → a₁ * rootSum ρ k ε (M : Matrix (Fin n) (Fin n) K) + a₂ * rootSum ρ k ε' (M' : Matrix (Fin n) (Fin n) K) = ∑ i, ∑ j, if symEdge ρ k i j then a i j * (M : Matrix (Fin n) (Fin n) K) i j else 0 := by
  intro K _ n ρ k hn ε ε' a₁ a₂ hε ha₁ ha₂
  refine ⟨fun i _ => if i.val < ρ then a₁ else if i.val < ρ + k then ε * a₁ - ε' * a₂
    else if i.val = ρ + k then a₂ else -a₂, ?_, ?_⟩
  · intro i j _
    rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp only <;> split_ifs <;> simp [ha₁, ha₂]
  · intro M M' h hM
    unfold rootSum
    rw [sum_reindex hn (fun i j => if (i.val + 1 < ρ ∧ j.val = i.val + 1) ∨ (i.val + 1 = ρ ∧ j.val = ρ + k)
      then (M' : Matrix (Fin n) (Fin n) K) i j
      else if ρ ≤ i.val ∧ j.val = i.val + 1 ∧ j.val < ρ + k then ε' * (M' : Matrix (Fin n) (Fin n) K) i j else 0)]
    simp only [dual_entry hn M M' h]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hi := i.2
    have hj := j.2
    have c1 : (((tau hn j).val + 1 < ρ ∧ (tau hn i).val = (tau hn j).val + 1) ∨
        ((tau hn j).val + 1 = ρ ∧ (tau hn i).val = ρ + k)) ↔ (j.val = i.val + 1 ∧ ρ + k ≤ i.val) := by
      simp only [tau_val]; unfold dualIdx; split_ifs <;> omega
    have c2 : (ρ ≤ (tau hn j).val ∧ (tau hn i).val = (tau hn j).val + 1 ∧ (tau hn i).val < ρ + k) ↔
        (ρ ≤ i.val ∧ j.val = i.val + 1 ∧ j.val < ρ + k) := by
      simp only [tau_val]; unfold dualIdx; split_ifs <;> omega
    have c3 : symEdge ρ k i j ↔ ((j.val = i.val + 1 ∧ i.val + 1 ≠ ρ ∧ i.val + 1 ≠ ρ + k) ∨
        (i.val + 1 = ρ ∧ j.val = ρ + k)) := Iff.rfl
    simp only [c1, c2, c3]
    by_cases hij : j.val = i.val + 1
    · rw [inv_adj hM i j hij]
      unfold sgn
      split_ifs <;> first | (exfalso; omega) | ring1
    · split_ifs <;> first | (exfalso; omega) | ring1

end GlobalTheory.RootSumDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagVecMemAndSpan
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagBasis

theorem flagVec_mem_and_span (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I)
    (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 →
      (∀ j, flagVec e0 f0 z0 bw bwd j ∈ I.Lf) ∧
        ∀ y ∈ I.Lf, InMod I g (Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val) y := by
  intro hF hn
  obtain ⟨⟨hef, hz, hb⟩, -, -, -, ⟨hidem, horth, hint, -⟩, ⟨hbw, hbwd⟩, -, hspan⟩ := hF
  refine ⟨fun j => ?_, fun y hy => ?_⟩
  · unfold flagVec
    split_ifs with h1 h2 h3 h4
    · exact (hef _).1
    · exact I.Lf.add_mem (hb _).1 (hb _).2
    · exact hz
    · exact (hef _).2
    · exact I.Lf.zero_mem
  · set R : Set (VA I) := Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val with hR
    have hmem : ∀ j, j < I.n → flagVec e0 f0 z0 bw bwd j ∈ Submodule.span (IntAf I.F I.E) R :=
      fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    have hsig : sigA I ew ∈ IntAf I.F I.E := Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I hint
    have hc : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.val) = bw l + bwd (Fin.rev l) := by
      intro l
      have h1 : ¬ (ρ + l.val < ρ) := by omega
      have h2 : ρ + l.val - ρ < k := by omega
      unfold flagVec
      rw [dite_eq_right h1, dite_eq_left h2]
      congr <;> simp
    have hcl : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.val) ∈ Submodule.span (IntAf I.F I.E) R :=
      fun l => hmem _ (by omega)
    have hsub : Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ⊆
        (Submodule.span (IntAf I.F I.E) R : Set (VA I)) := by
      rintro v ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hv) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
      · have h := hmem a.val (by omega)
        unfold flagVec at h
        rwa [dite_eq_left a.isLt] at h
      · have h := hmem (2 * ρ + k - a.val) (by omega)
        have h1 : ¬ (2 * ρ + k - a.val < ρ) := by omega
        have h2 : ¬ (2 * ρ + k - a.val - ρ < k) := by omega
        have h3 : ¬ (2 * ρ + k - a.val = ρ + k) := by omega
        have h4 : 2 * ρ + k - (2 * ρ + k - a.val) < ρ := by omega
        unfold flagVec at h
        rw [dite_eq_right h1, dite_eq_right h2, if_neg h3, dite_eq_left h4] at h
        have e : (⟨2 * ρ + k - (2 * ρ + k - a.val), h4⟩ : Fin ρ) = a := by ext; simp; omega
        rwa [e] at h
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        have h := hmem (ρ + k) (by omega)
        have h1 : ¬ (ρ + k < ρ) := by omega
        have h2 : ¬ (ρ + k - ρ < k) := by omega
        unfold flagVec at h
        rwa [dite_eq_right h1, dite_eq_right h2, if_pos rfl] at h
      · have h := Submodule.smul_mem _ (⟨ew, hint⟩ : IntAf I.F I.E) (hcl l)
        rw [hc l] at h
        have e : ((⟨ew, hint⟩ : IntAf I.F I.E) • (bw l + bwd (Fin.rev l)) : VA I) = bw l := by
          show ew • (bw l + bwd (Fin.rev l)) = bw l
          rw [smul_add, hbwd (Fin.rev l), smul_smul, horth, zero_smul, add_zero, ← hbw l]
        rwa [e] at h
      · have h := Submodule.smul_mem _ (⟨sigA I ew, hsig⟩ : IntAf I.F I.E) (hcl (Fin.rev l))
        rw [hc (Fin.rev l), Fin.rev_rev] at h
        have e : ((⟨sigA I ew, hsig⟩ : IntAf I.F I.E) • (bw (Fin.rev l) + bwd l) : VA I) = bwd l := by
          show sigA I ew • (bw (Fin.rev l) + bwd l) = bwd l
          rw [smul_add, hbw (Fin.rev l), smul_smul, mul_comm, horth, zero_smul, zero_add,
            hbwd l, smul_smul, ← map_mul, hidem]
        rwa [e] at h
    have := hspan y hy
    exact sup_le_sup_right (Submodule.span_le.2 hsub) _ this

end GlobalTheory.FlagBasis
end

