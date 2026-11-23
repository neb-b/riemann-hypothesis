module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FamRaise
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0013
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0011

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVec
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

section Std

variable {K : Type} [Field K] (σ : K →+* ℂ) (r : ℕ) (g : ℝ)

theorem blk_std (s o : ℕ) (hs : 1 ≤ s) (hos : o + s ≤ r + 1) :
    blkF (-Complex.I * ((g / (2 * Real.pi) : ℝ) : ℂ)) r o (o + s - 1) * (-1) ^ (r + 1 - (o + 1 + s - 1)) =
      (((g / (2 * Real.pi)) ^ Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((o + 1 : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) := by
  set a : ℝ := g / (2 * Real.pi)
  set m := (r - o) + (r - (o + s - 1)) with hm
  set e := r + 1 - (o + 1 + s - 1) with he
  have hnu : Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((o + 1 : ℕ) : ℤ) (s : ℤ) = (m : ℤ) := by
    unfold Formalism.FourierDecayAlt.S6.nuBlock; rw [hm]; push_cast; omega
  have hme : m = 2 * e + (s - 1) := by rw [hm, he]; omega
  rw [hnu, zpow_natCast]
  unfold blkF
  rw [← hm, mul_pow, ← mul_assoc, ← mul_pow, neg_mul, one_mul, neg_neg, Complex.ofReal_pow, hme, pow_add, pow_mul,
    Complex.I_sq]
  have h1 : ((-1 : ℂ) ^ e) * ((-1 : ℂ) ^ e) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h2 : ((-1 : ℂ) ^ e) = (-1) ^ e := rfl
  calc (-1 : ℂ) ^ e * Complex.I ^ (s - 1) * (a : ℂ) ^ (2 * e + (s - 1)) * (-1) ^ e
      = (((-1 : ℂ) ^ e) * ((-1 : ℂ) ^ e)) * ((a : ℂ) ^ (2 * e + (s - 1)) * Complex.I ^ (s - 1)) := by ring
    _ = (a : ℂ) ^ (2 * e + (s - 1)) * Complex.I ^ (s - 1) := by rw [h1, one_mul]

theorem lptOf_toStd : ∀ (L : Formalism.FourierDecayAlt.TB.Pt K) (o : ℕ), (∀ b ∈ L, 1 ≤ b.1) → o + (L.map Prod.fst).sum ≤ r + 1 →
    lptOf σ (-Complex.I * ((g / (2 * Real.pi) : ℝ) : ℂ)) r o ((Formalism.L2.SG.DataInst.signAux r (o + 1) L).map Prod.swap) =
      Formalism.FourierDecayAlt.D.toStd r g (o + 1) (Formalism.FourierDecayAlt.C.loc σ L)
  | [], _, _, _ => rfl
  | (s, t) :: rest, o, hL, ho => by
    simp only [List.map_cons, List.sum_cons] at ho
    have hs : 1 ≤ s := hL (s, t) (List.mem_cons_self)
    simp only [Formalism.L2.SG.DataInst.signAux, List.map_cons, Prod.swap_prod_mk, lptOf, Formalism.FourierDecayAlt.C.loc,
      Formalism.FourierDecayAlt.D.toStd, List.cons.injEq, true_and]
    constructor
    · rw [map_mul, map_pow, map_neg, map_one, ← mul_assoc, blk_std r g s o hs (by omega)]
    · have := lptOf_toStd rest (o + s) (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (by omega)
      rw [show o + s + 1 = o + 1 + s by omega] at this
      exact this

end Std

end Formalism.L2.SG.Pf.Bridge
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeRel
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

section RelGen

theorem mulVec_single_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    (M *ᵥ Pi.single j (1 : ℂ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem herm_smul_right' (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v w : Fin (2 * r + k + 1) → ℂ)
    (s : ℂ) : Formalism.QuantumDeterminants.herm H v (s • w) = star s * Formalism.QuantumDeterminants.herm H v w := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_fd_Q (hT : TrHyp F Qm Qim c) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    hJ ε (F.fd a) (Qm *ᵥ v) = c a * v (Formalism.QuantumDeterminants.eI k r a) := by
  have e1 : F.fd a = Qm *ᵥ (Qim *ᵥ F.fd a) := by rw [Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec]
  rw [e1, ← herm_Q hT, Qi_f hT, herm_smul_right', star_star, Formalism.L2.SG.Pf.CarrierBase.herm_bvec,
    Formalism.L2.SG.Pf.CarrierBase.hpk_mulVec_esI]

theorem rootCoord_Q (hT : TrHyp F Qm Qim c) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) (hκ0 : κ ≠ 0)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) :
    rootCoord ε F.e F.fd F.z (Qm * ρ * Qim) a =
      κ * (if h : a.val + 1 < r then ρ (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
        else (ρ *ᵥ (Qim *ᵥ F.z)) (Formalism.QuantumDeterminants.eI k r a)) := by
  unfold rootCoord nxt
  by_cases h : a.val + 1 < r
  · rw [dite_eq_left h, dite_eq_left h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qi_e hT, Matrix.mulVec_smul,
      Matrix.mulVec_smul, PtRepPf.hJ_smul_right, hJ_fd_Q hT, hc, hc]
    unfold Formalism.QuantumDeterminants.bvec
    rw [mulVec_single_apply]
    have he : r - a.val = (r - (a.val + 1)) + 1 := by omega
    simp only
    rw [he, pow_succ]
    field_simp
  · rw [dite_eq_right h, dite_eq_right h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJ_fd_Q hT, hc]
    have he : r - a.val = 1 := by have := a.2; omega
    rw [he, pow_one]

theorem sum_rootCoord (hT : TrHyp F Qm Qim c) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) (hκ0 : κ ≠ 0)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∑ a, rootCoord ε F.e F.fd F.z (Qm * ρ * Qim) a = κ * Formalism.QuantumDeterminants.ell k r (Qim *ᵥ F.z) ρ := by
  simp only [rootCoord_Q hT hc hκ0, ← Finset.mul_sum]
  rfl

theorem psiR_Q (hT : TrHyp F Qm Qim c) (gg : ℕ) (hgg : 0 < gg) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val))
    (hκ : κ = -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ)) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psiR ε gg F.e F.fd F.z (Qm * ρ * Qim) = Formalism.QuantumDeterminants.psi k r (Qim *ᵥ F.z) Formalism.QuantumDeterminants.cStd ρ := by
  have hg : (0 : ℝ) < gg := by exact_mod_cast hgg
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    have : (0 : ℝ) < (gg : ℝ) / (2 * Real.pi) := div_pos hg (by positivity)
    exact_mod_cast this.ne'
  unfold psiR Formalism.QuantumDeterminants.psi
  congr 1
  rw [Finset.sum_add_distrib, ← star_sum, sum_rootCoord hT hc hκ0]
  set ℓ := Formalism.QuantumDeterminants.ell k r (Qim *ᵥ F.z) ρ
  rw [show star (κ * ℓ) = (starRingEnd ℂ) (κ * ℓ) from rfl, Complex.add_conj]
  rw [hκ]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Formalism.QuantumDeterminants.cStd, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

theorem psiR_conj {H Hi g : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hiH : Hi * H = 1) (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHf : ∀ a, H *ᵥ F.fd a = F.fd a) (hHz : H *ᵥ F.z = F.z)
    (gg : ℕ) : psiR ε gg F.e F.fd F.z (H * g * Hi) = psiR ε gg F.e F.fd F.z g := by
  have hHi : ∀ x, H *ᵥ x = x → Hi *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hrc : ∀ a, rootCoord ε F.e F.fd F.z (H * g * Hi) a = rootCoord ε F.e F.fd F.z g a := by
    intro a
    unfold rootCoord
    have hn : H *ᵥ nxt F.e F.z a = nxt F.e F.z a := by
      unfold nxt; split_ifs; · exact hHe _
      · exact hHz
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHi _ hn, fixed_left hH (hHf a)]
  unfold psiR
  simp only [hrc]

theorem spanLt_map {H : Matrix (Fin n) (Fin n) ℂ} (hHe : ∀ a, H *ᵥ F.e a = F.e a) (m : ℕ) {x : Fin n → ℂ}
    (hx : x ∈ spanLt F.e m) : H *ᵥ x ∈ spanLt F.e m := by
  have hle : spanLt F.e m ≤ (spanLt F.e m).comap (Matrix.mulVecLin H) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hHe]
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  exact hle hx

theorem span_range_le (hT : TrHyp F Qm Qim c) : Submodule.span ℂ (Set.range F.e) ≤ spanLt F.e r := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, a.2, rfl⟩

theorem inN_Q (hT : TrHyp F Qm Qim c) {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hρ : ρ ∈ Formalism.QuantumDeterminants.Nset k r) : InN ε F.e F.z (Qm * ρ * Qim) := by
  have hsub : ∀ x, (Qm * ρ * Qim - 1) *ᵥ x = Qm *ᵥ ((ρ - 1) *ᵥ (Qim *ᵥ x)) := fun x => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Qm Qim, hT.h2, Matrix.one_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hsub, Qi_e hT, Matrix.mulVec_smul, Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ ?_
    set v := (ρ - 1) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) with hv
    have hva : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → v i = 0 := by
      intro i hi
      rw [hv, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      unfold Formalism.QuantumDeterminants.bvec
      rw [mulVec_single_apply, hρ.2.1 a i hi, sub_eq_zero]
      simp [Pi.single_apply]
    have hvX : IsXv v := fun i hi => hva i (by have := a.2; omega)
    rw [isXv_eq v hvX, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b.val < a.val
    · rw [Matrix.mulVec_smul, hT.he, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hva _ (by simp only [Formalism.QuantumDeterminants.eI]; omega), zero_smul, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  · rw [hsub]
    exact span_range_le hT (Q_X hT _ (N_sub_X hρ _ (Qi_noXs hT F.z F.ez)))
  · rw [hsub]
    exact span_range_le hT (Q_X hT _ (N_sub_X hρ _ (Qi_noXs hT y hy)))

theorem inN_conj {H Hi g : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hHi : H * Hi = 1) (hiH : Hi * H = 1) (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHz : H *ᵥ F.z = F.z)
    (hg : InN ε F.e F.z g) : InN ε F.e F.z (H * g * Hi) := by
  have hHi' : ∀ x, H *ᵥ x = x → Hi *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hsub : ∀ x, (H * g * Hi - 1) *ᵥ x = H *ᵥ ((g - 1) *ᵥ (Hi *ᵥ x)) := fun x => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ H Hi, hHi, Matrix.one_mulVec]
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hsub, hHi' _ (hHe a)]; exact spanLt_map hHe _ (h1 a)
  · rw [hsub, hHi' _ hHz]; exact spanLt_map hHe _ h2
  · rw [hsub]
    refine spanLt_map hHe _ (h3 _ fun a => ?_)
    rw [← fixed_left hH (hHe a), Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec, hy a]

end RelGen

end Formalism.L2.SG.Pf.Bridge
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
section
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Formalism.L2.SG.RowsU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure UC where
  c3 : ℝ
  cH : ℝ
  cV : ℝ
  cS : ℝ
  c4 : ℝ
  CaF : ℝ → ℝ
  secondOrderBound : ℝ → ℝ
  ChF : ℝ → ℝ

def c0ND (CT A C0 : ℝ) (U : UC) : ℝ :=
  let c := max (max U.c3 1) (max (|U.cH| + 2) (|U.cV| + 2))
  max c (4 + (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (6 * c + 2))

def degenerateConstant (CT : ℝ) (U : UC) : ℝ :=
  let c := max (max (max U.c3 (max (max 1 CT) (|U.cH| + 2))) 1) (max (|U.cH| + 2) (|U.cV| + 2))
  max (max c (4 + (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (6 * c + 2)))
    (max (2 * U.secondOrderBound (9 * c + 3)) |U.CaF (9 * c + 3)|)

def corankOneConstant (CT A C0 CGam : ℝ) (U : UC) : ℝ :=
  let c := max (max U.c3 1) (max (max (|U.cH| + 2) (|U.cV| + 2)) (max (|U.cS| + 2) (|U.c4| + 2)))
  max (max (4 * Real.sqrt A) (2 * Real.sqrt (2 * C0) * c))
    (max (CGam + U.secondOrderBound (9 * c + 3)) (4 + 2 * (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (c + 1)))

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)
  (Cg cb Cu cT CT C0 A : ℝ)

def UAdm (U : UC) : Prop :=
  (∀ C ≥ U.c3, OwnEv Fm fun C' Cl x i => ∀ u u',
    VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.cH) ∧
  (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A U.cV) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.cS) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.c4) ∧
  ∀ Cpr : ℝ, 0 ≤ U.ChF Cpr ∧ 0 ≤ U.CaF Cpr ∧ ∀ δ > 0, OwnEv Fm fun C' Cl x i =>
    VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr (U.CaF Cpr) (U.secondOrderBound Cpr) (U.ChF Cpr) δ

theorem rowsKBU (U : UC) (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ c ≥ max (max 1 CT) (|U.cH| + 2), OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → rows_KBound (Y x hx i u u') c := by
  intro c hc
  obtain ⟨_, h27, _⟩ := hU
  refine OwnEv.mono ?_ h27
  intro C' Cl x i h hx u u' hH
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hCT : CT ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hcH : |U.cH| + 2 ≤ c := le_trans (le_max_right _ _) hc
  exact rows_KBound_of (Y x hx i u u') hH (rows_stHH_mono (by linarith [le_abs_self U.cH])
    (by linarith [neg_abs_le U.cH]) (h u u')) hc1 hCT

def c0U (CT A C0 CGam : ℝ) (U : UC) : ℝ := max (c0ND CT A C0 U) (max (degenerateConstant CT U) (corankOneConstant CT A C0 CGam U))

end Fam

end Formalism.L2.SG.RowsU
end
end

