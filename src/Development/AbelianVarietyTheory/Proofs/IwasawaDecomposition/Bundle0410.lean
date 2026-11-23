module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricCharResidueConjEqWeightedUnipotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.ResBar

variable {D : D7}

theorem unip_inv_sup {κ : Type} [CommRing κ] {r : ℕ} {N : GL (Fin r) κ} (hN : N ∈ unip κ r) (i j : Fin r)
    (hij : j.val = i.val + 1) :
    ((N⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = -(N : Matrix (Fin r) (Fin r) κ) i j := by
  have hi := Subgroup.inv_mem _ hN
  have h := unip_mul_entry hi hN (i := i) (j := j) (show i.val < j.val by omega) (fun l h1 h2 => by
    exfalso
    have : i.val < l.val := h1
    have : l.val < j.val := h2
    omega)
  rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (by intro e; rw [e] at hij; omega)] at h
  linear_combination -h

abbrev QW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Type :=
  (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ (wInt X w).toAddSubgroup

abbrev mkW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) →+ QW X w :=
  QuotientAddGroup.mk' _

theorem mkW_eq {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {a b : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (h : a - b ∈ wInt X w) : mkW X w a = mkW X w b := by
  show (QuotientAddGroup.mk a : QW X w) = QuotientAddGroup.mk b
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact h

theorem mkW_zero {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (h : a ∈ wInt X w) : mkW X w a = 0 := by
  rw [← map_zero (mkW X w)]
  exact mkW_eq (by rw [sub_zero]; exact h)

theorem phi_exists (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ) [NeZero g]
    (hg : ((g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w) :
    ∃ φ : ZMod g →+ QW X w, ∀ t : ZMod g, φ t = t.val • mkW X w 1 := by
  refine ⟨ZMod.lift g ⟨zmultiplesHom _ (mkW X w 1), ?_⟩, fun t => ?_⟩
  · rw [zmultiplesHom_apply, natCast_zsmul, ← map_nsmul, nsmul_one]
    exact mkW_zero hg
  · conv_lhs => rw [← ZMod.natCast_zmod_val t]
    have e : ((t.val : ℕ) : ZMod g) = ((t.val : ℤ) : ZMod g) := by simp
    rw [e, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]

theorem modW_of {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    {φ : ZMod g →+ QW X w} (hφ : ∀ t : ZMod g, φ t = t.val • mkW X w 1)
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} {t : ZMod g} (h : mkW X w c = φ t) : ModW X w c t := by
  unfold ModW
  rw [hφ, ← map_nsmul, nsmul_one] at h
  show (c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈ (wInt X w).toAddSubgroup
  rw [← QuotientAddGroup.eq_iff_sub_mem]
  exact h

theorem read (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hM : GlobalTheory.Mem.SymFrame.IsMatIn X w u x M)
    {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (p q : Fin D.R.r) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hG : ∀ j, hA X.B.I v (u j) - (if j = q then c else 0) ∈ wInt X w) :
    mkW X w (hA X.B.I v (X.B.I.fmat x *ᵥ u p)) = (M q p).val • mkW X w c := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mkW_eq (hA_isMatIn X w hM hv p), map_sum]
  have e : ∀ j, mkW X w ((((M j p).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I v (u j)) =
      if j = q then (M q p).val • mkW X w c else 0 := by
    intro j
    rw [← nsmul_eq_mul, map_nsmul, mkW_eq (hG j)]
    split_ifs with hj
    · rw [hj]
    · rw [map_zero, smul_zero]
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem r_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem symVec_mem (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.r) :
    GlobalTheory.Mem.SymFrame.symVec X w j ∈ X.B.I.Lf := by
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV GlobalTheory.Mem.SymFrame.epsW
  split_ifs
  · exact (X.vectorsInLattice.1 _).1
  · exact (X.vectorsInLattice.2.2 _).1
  · exact (X.vectorsInLattice.2.2 _).2
  · exact X.vectorsInLattice.2.1
  · exact (X.vectorsInLattice.1 _).2
  · exact zero_mem _

theorem symmetricOrderFrameModPlace_last_block (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) (p : Fin D.R.r)
    (hp : p.val = 2 * D.R.rS + D.R.k - a.val) : GlobalTheory.Mem.SymFrame.symVec X w p = X.f0 a := by
  have hr := r_eq D
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1
  ext
  simp only
  omega

theorem symVec_bwd (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hE : ¬ GlobalTheory.Mem.SymFrame.EwAt X w)
    (i : Fin D.R.k) (p : Fin D.R.r) (hp : p.val = D.R.rS + D.R.k - 1 - i.val) :
    GlobalTheory.Mem.SymFrame.symVec X w p = X.bwd i := by
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV GlobalTheory.Mem.SymFrame.epsW
  rw [if_neg hE, dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1
  ext
  simp only [Fin.val_rev]
  omega

theorem ite_val {r : ℕ} {R : Type} [Zero R] (j q : Fin r) (n : ℕ) (hq : q.val = n) (c : R) :
    (if j.val = n then c else 0) = (if j = q then c else 0) := by
  by_cases h : j = q
  · subst h; simp [hq]
  · have : j.val ≠ n := fun e => h (Fin.ext (by omega))
    simp [h, this]

theorem resBar : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I (GlobalTheory.Mem.SymChar.argS X k)) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j else 0) := by
  intro D X h hι hg kv k hk N hN hNu
  classical
  have hgw := hg kv
  set w := D.naut.plGw kv.1 kv.2 with hw
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  have hgA : (((D.host.g kv.1 : ℕ)) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E), ⟨_, hgw, ?_⟩, ?_⟩
    · simp
    · simp
  obtain ⟨φ, hφ⟩ := phi_exists X w _ hgA
  have hr := r_eq D
  set u := GlobalTheory.Mem.SymFrame.symVec X w with hu_def
  have hu : ∀ i, u i ∈ X.B.I.Lf := symVec_mem X w
  have hNi := _root_.GlobalTheory.Mem.SymFrame.isMatIn_inv D X kv hgw u hu k hk N hN
  have hU : N ∈ unip _ _ := unipCol_le _ _ _ hNu
  rw [_root_.GlobalTheory.Mem.SymChar.Comb.weighted_sum_eq _ _ _ hr]
  apply modW_of hφ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [argS, map_add (f := _), map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    have e := GlobalTheory.St.G.FrameClose.hA_move k⁻¹ (nxt X.e0 X.z0 a) (X.f0 a)
    rw [inv_inv] at e
    rw [← e, ← symmetricOrderFrameModPlace_last_block X w a ⟨2 * D.R.rS + D.R.k - a.val, by omega⟩ rfl]
    by_cases ha : a.val + 1 < D.R.rS
    · rw [dite_eq_left ha]
      have hn : nxt X.e0 X.z0 a = X.e0 ⟨a.val + 1, ha⟩ := by unfold nxt; rw [dite_eq_left ha]
      rw [hn, read X w hNi (X.vectorsInLattice.1 _).1 _ ⟨2 * D.R.rS + D.R.k - a.val - 1, by omega⟩ 1 (fun j => by
        rw [← ite_val j _ (2 * D.R.rS + D.R.k - (a.val + 1)) (by simp only; omega)]
        exact _root_.GlobalTheory.Mem.SymChar.hA_e0_symVec D X kv hgw ⟨a.val + 1, ha⟩ j), ← hφ, unip_inv_sup hU _ _ (by simp only; omega)]
    · rw [dite_eq_right ha]
      have hn : nxt X.e0 X.z0 a = X.z0 := by unfold nxt; rw [dite_eq_right ha]
      have hp : (⟨2 * D.R.rS + D.R.k - a.val, by omega⟩ : Fin D.R.r) = ⟨D.R.rS + D.R.k + 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
      rw [hn, hp, read X w hNi X.vectorsInLattice.2.1 _ ⟨D.R.rS + D.R.k, by omega⟩ (-1) (fun j => by
        rw [← ite_val j _ (D.R.rS + D.R.k) rfl]
        exact _root_.GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec D X kv hgw j), map_neg, smul_neg, ← hφ, ← map_neg, unip_inv_sup hU _ _ (by simp only),
        neg_neg]
  · by_cases hE : GlobalTheory.Mem.SymFrame.EwAt X w
    · have hs : side X w = true := by simp [side, hE]
      rw [hs, if_pos rfl, map_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i.val + 1 < D.R.k
      · rw [dite_eq_left hi]
        apply mkW_zero
        rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
        have hb : X.bwd i ∈ wLf X w := by
          have h1 := hE (X.bwd i) (X.vectorsInLattice.2.2 i).2
          have e : (1 - X.ew) • X.bwd i = X.bwd i := by
            conv_lhs => rw [X.bwd_w i]
            rw [smul_smul, sub_mul, one_mul, X.ew_orth, sub_zero, ← X.bwd_w i]
          rwa [e] at h1
        exact hA_mem_wInt X w (Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1) hb
      · rw [dite_eq_right hi, map_zero, map_zero]
    · have hs : side X w = false := by simp [side, hE]
      have hew := _root_.GlobalTheory.Mem.SymChar.sigA_ew_sub_one_mem_wInt D X h hι kv hgw hE
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hs, if_neg (by simp), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i.val + 1 < D.R.k
      · rw [dite_eq_left hi, dite_eq_left hi]
        rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
        have e := GlobalTheory.St.G.FrameClose.hA_move k⁻¹ (X.bw ⟨i.val + 1, hi⟩) (X.bwd i)
        rw [inv_inv] at e
        rw [← e, ← symVec_bwd X w hE i ⟨D.R.rS + D.R.k - 1 - i.val, by omega⟩ rfl,
          read X w hNi (X.vectorsInLattice.2.2 _).1 _ ⟨D.R.rS + D.R.k - 2 - i.val, by omega⟩ 1 (fun j => by
            rw [← ite_val j _ (D.R.rS + D.R.k - 1 - (i.val + 1)) (by simp only; omega)]
            exact _root_.GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt D X kv hgw hE hew ⟨i.val + 1, hi⟩ j), ← hφ, unip_inv_sup hU _ _ (by simp only; omega)]
      · rw [dite_eq_right hi, dite_eq_right hi, map_zero, map_zero, map_zero]

end GlobalTheory.Mem.SymChar.ResBar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EdgeReindex

theorem sum_edge {Q : Type} [AddCommMonoid Q] {r t : ℕ} (ht : t < r) (P : Fin r → Prop) [DecidablePred P]
    (hP : ∀ j, P j ↔ j.val = t) (f : Fin r → Q) : (∑ j, if P j then f j else 0) = f ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · rw [if_pos ((hP _).2 rfl)]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext ((hP b).1 h))
  · simp

def extF {Q : Type} [AddCommGroup Q] {r : ℕ} (F : Fin r → Fin r → Q) (a b : ℕ) : Q :=
  if h : a < r ∧ b < r then F ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def termAt {Q : Type} [AddCommGroup Q] (ρ k : ℕ) (s : Bool) {r : ℕ} (F : Fin r → Fin r → Q) (n : ℕ) : Q :=
  if n < ρ then extF F n (if n + 1 < ρ then n + 1 else ρ + k)
  else if n + 1 < ρ + k then (if s then extF F n (n + 1) else 0) else 0

theorem inner_eq {Q : Type} [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool)
    (F : Fin r → Fin r → Q) (i : Fin r) :
    (∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) =
      termAt ρ k s F i.1 := by
  have hi := i.2
  unfold termAt
  by_cases h1 : i.1 < ρ
  · by_cases h2 : i.1 + 1 < ρ
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_pos h2, extF, dite_eq_left ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
    · rw [sum_edge (t := ρ + k) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_neg h2, extF, dite_eq_left ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
  · by_cases h2 : i.1 + 1 < ρ + k
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_neg h1, if_pos h2]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_pos h2]
      cases s
      · simp
      · rw [extF, dite_eq_left ⟨i.2, by omega⟩]
        simp
    · rw [if_neg h1, if_neg h2]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_neg h2, zero_smul, ite_self]

theorem sum_symEdge_wtA : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  intro Q _ ρ k r hr s F
  rw [Finset.sum_congr rfl (fun i _ => inner_eq ρ k r hr s F i)]
  rw [Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) r]
  have e : Finset.range r = Finset.range (ρ + (k + (ρ + 1))) := congrArg Finset.range (by omega)
  rw [e, Finset.sum_range_add, Finset.sum_range_add]
  have h3 : (∑ x ∈ Finset.range (ρ + 1), termAt ρ k s F (ρ + (k + x))) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    unfold termAt
    rw [if_neg (by omega), if_neg (by omega)]
  rw [h3, add_zero]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) ρ]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    unfold termAt extF
    rw [if_pos ha, dite_eq_left ⟨by omega, by split_ifs <;> omega⟩]
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F (ρ + n)) k]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    by_cases h : i.1 + 1 < k
    · rw [dite_eq_left h]
      unfold termAt
      rw [if_neg (by omega), if_pos (by omega)]
      cases s
      · rfl
      · simp only [if_true]
        unfold extF
        rw [dite_eq_left ⟨by omega, by omega⟩]
    · rw [dite_eq_right h]
      unfold termAt
      rw [if_neg (by omega), if_neg (by omega)]

end GlobalTheory.Mem.SymChar.EdgeReindex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Resid

theorem hA_bwd_symVec : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.SymFrame.EwAt X w → 1 - X.ew ∈ GlobalTheory.Mem.SymChar.wInt X w → ∀ (i : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bwd i) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posB D i then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg hw hew i j
  have hZ : ∀ {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}, ZMod' X.B.I X.B.g c → c ∈ wInt X w :=
    fun hc => wInt_of_zmod X k hg hc
  have he : GlobalTheory.Mem.SymFrame.epsW X w = X.bw := by
    unfold GlobalTheory.Mem.SymFrame.epsW; rw [if_pos hw]
  have hr := rank_eq D
  have hp : (j = posB D i) ↔ j.1 = D.R.rS + i.1 := by rw [Fin.ext_iff]; rfl
  have hi := i.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  rw [he]
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 _).2.2.1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]
    have hd := X.bw_dual i ⟨j.1 - D.R.rS, by omega⟩
    by_cases hl : j.1 = D.R.rS + i.1
    · rw [if_pos (hp.2 hl)]
      rw [if_pos (Fin.ext (by simp only; omega))] at hd
      have := sub_mem (hZ hd) hew
      convert this using 1
      ring
    · rw [if_neg (fun h => hl (hp.1 h))]
      rw [if_neg (fun h => hl (by have := congrArg Fin.val h; simp only at this; omega))] at hd
      simpa using hZ hd
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.weightVectorsIntegral i).2.1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 _).2.2.2
  · rw [dite_eq_right h3, if_neg (by rw [hp]; omega), sub_zero, hA_zero_right']
    exact zero_mem _

end GlobalTheory.Mem.SymChar.Resid
end

