module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHClosed
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut

namespace Formalism.L2.SG.Pf

theorem foldOKC_holds_of (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hU : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), IUnfold X u hK) :
    Formalism.L2.SG.Full.FoldOKC := by
  intro D X Y u hKL hW
  exact foldOK_of_steps X u Y.hK hKL (foldReadyX_holds X) (hS D X u) (hN D X u) (hL D X u) (hP D X u) hW
    (sratFund_holds X u) (Formalism.L2.SG.Closed.MultPoly_holds X) (hU D X u Y.hK)

theorem inHHC_holds_of (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hFB : ∀ (D : D7) (X : HidaSetting D), FundBridge X)
    (hPM : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserMeas X u hK)
    (hRph : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserRph X u hK)
    (hRF : ∀ (D : D7) (X : HidaSetting D), ArchimedeanConvolutionFixesInvariantL2 X) (hEF : ∀ (D : D7) (X : HidaSetting D), IdempotentFixesInvariantL2 X) :
    Formalism.L2.SG.Full.InHHC := by
  intro D X Y u hI hOK
  have hR := foldReadyX_holds X
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  exact inHH_of X u Y.hK hR
    (@Formalism.L2.SG.Closed.fold_L2_first X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (@Formalism.L2.SG.Closed.fold_L2_second X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (hFB D X) hOK (phProps_closed X u Y.hK (hS D X u) (hN D X u) (hL D X u) (hP D X u))
    (poincare_well_defined X u Y.hK (hS D X u) (hN D X u)) (hPM D X u Y.hK) (hRph D X u Y.hK) hI (hRF D X) (hEF D X)
    hKL (level_subgroup_measurable X Y.hK hKL)

theorem inHHC_holds_of' (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u)
    (hRph : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserRph X u hK) :
    Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of hS hN hL hP (fun _ X => fundBridge_holds X) (fun _ X u hK => pserMeas_holds X u hK) hRph
    (fun _ X => regular_fixes_invariant_L2 X) (fun _ X => idempotent_fixes_invariant_L2 X)

theorem inHHC_holds_of'' (hS : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), KsetSplit X u)
    (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u)
    (hL : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PsiProd X u) :
    Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of' hS hN hL hP fun _ X u hK => pserRph_holds X u hK

theorem inHHC_holds : Formalism.L2.SG.Full.InHHC :=
  inHHC_holds_of'' (fun _ X u => ksetSplit_holds X u) (fun _ X u => unipotent_in_level X u)
    (fun _ X u => ratLevi_holds X u) (fun _ X u => psiProd_holds X u)

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipReal
section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical

namespace Formalism.L2.SG.Pf.UnipB

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)

theorem mulVec_eq_sum_cols {m p : Type*} [Fintype p] [DecidableEq p] (M : Matrix m p ℂ) (c : p → ℂ) :
    M *ᵥ c = ∑ k, c k • (M *ᵥ Pi.single k 1) := by
  ext i
  rw [Finset.sum_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem Bv_mulVec (c : Kap X → ℂ) : Bv X v *ᵥ c = ∑ k, c k • rv X.B.I v (bv X k) := by
  rw [mulVec_eq_sum_cols]
  simp only [Bv_col]

theorem Bv_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → ℂ) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bv X v *ᵥ c ∈ Submodule.span ℂ ((fun b => rv X.B.I v (X.eR b)) '' S) := by
  rw [Bv_mulVec]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem Bv'_mulVec_supp (S : Set (Fin D.R.rS)) {y : Fin X.B.I.n → ℂ}
    (hy : y ∈ Submodule.span ℂ ((fun b => rv X.B.I v (X.eR b)) '' S)) :
    ∀ k, k ∉ Sum.inl '' S → (Bv' X v *ᵥ y) k = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro k hk
    show (Bv' X v *ᵥ rv X.B.I v (bv X (Sum.inl b))) k = 0
    rw [Bv'_rv, Pi.single_apply, if_neg]
    rintro rfl
    exact hk ⟨b, hb, rfl⟩
  | zero => intro k _; simp
  | add x y _ _ hx hy => intro k hk; rw [Matrix.mulVec_add, Pi.add_apply, hx k hk, hy k hk, add_zero]
  | smul c x _ hx => intro k hk; rw [Matrix.mulVec_smul, Pi.smul_apply, hx k hk, smul_zero]

theorem hJ_e_Bv (a : Fin D.R.rS) (c : Kap X → ℂ) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (Bv X v *ᵥ c) = c (Sum.inr (Sum.inr a)) := by
  rw [Bv_mulVec, hJ_sum_right']
  have e : ∀ k, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (bv X k)) =
      X.B.I.φ v (JB X (Sum.inl a) k) := by
    intro k
    rw [hJ_rv_sc]
    rfl
  simp only [e, JB_e_row]
  simp

theorem hermitian_basis_e_z_orthogonal (a : Fin D.R.rS) : hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 := by
  rw [hJ_rv_sc]
  have := hE_ez X u a
  simp only [hE] at this
  rw [this, map_zero]

theorem hJ_rv_e_w (a : Fin D.R.rS) (i : Fin (mW X)) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (bv X (Sum.inr (Sum.inl i)))) = 0 := by
  rw [hJ_rv_sc]
  have := (wb_mem X i a).1
  simp only [hE] at this
  simp only [bv, Sum.elim_inr, Sum.elim_inl]
  rw [this, map_zero]

@[simp] theorem lvk_inl (a : Fin D.R.rS) : lvk X (Sum.inl a) = a.1 + 1 := rfl
@[simp] theorem lvk_w (i : Fin (mW X)) : lvk X (Sum.inr (Sum.inl i)) = D.R.rS + 1 := rfl
@[simp] theorem lvk_f (a : Fin D.R.rS) : lvk X (Sum.inr (Sum.inr a)) = 2 * D.R.rS + 1 - a.1 := rfl

theorem lvk_notinl (k : Kap X) (hk : ∀ b, k ≠ Sum.inl b) : D.R.rS + 1 ≤ lvk X k := by
  rcases k with a | i | a
  · exact (hk a rfl).elim
  · simp
  · rw [lvk_f]
    have := a.2
    omega

theorem inN_of_pat (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hpat : InPat (lvk X) 1 (Bv' X v * g * Bv X v - 1)) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) g := by
  set M := Bv' X v * g * Bv X v with hM
  have hg : g - 1 = Bv X v * (M - 1) * Bv' X v := by
    rw [hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bv_mul_Bv']
    simp only [← Matrix.mul_assoc, Bv_mul_Bv', Matrix.one_mul]
    rw [Matrix.mul_assoc, Bv_mul_Bv', Matrix.mul_one]
  have hgv : ∀ y, (g - 1) *ᵥ y = Bv X v *ᵥ ((M - 1) *ᵥ (Bv' X v *ᵥ y)) := by
    intro y
    rw [hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

  have hperp : ∀ y, (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) y = 0) →
      (g - 1) *ᵥ y ∈ spanLt (fun a => rv X.B.I v (X.eR a)) D.R.rS := by
    intro y hy
    set c := Bv' X v *ᵥ y with hc
    have hyc : y = Bv X v *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, Bv_mul_Bv', Matrix.one_mulVec]
    have hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0 := by
      intro a
      have := hJ_e_Bv X v a c
      rw [← hyc, hy a] at this
      exact this.symm
    rw [hgv, ← hc]
    refine Bv_mulVec_mem X v _ _ fun k hk => ?_
    have hk' : ∀ b, k ≠ Sum.inl b := by
      rintro b rfl
      exact hk ⟨b, b.2, rfl⟩
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hlk := lvk_notinl X k hk'
    rcases j with b | i | b
    · rw [hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
    · rw [hpat k _ (by rw [lvk_w]; omega), zero_mul]
    · rw [hcf b, mul_zero]
  refine ⟨⟨fun a => ?_, hperp _ fun a => hermitian_basis_e_z_orthogonal X u v a⟩, hperp⟩
  rw [hgv]
  show Bv X v *ᵥ ((M - 1) *ᵥ (Bv' X v *ᵥ rv X.B.I v (bv X (Sum.inl a)))) ∈ _
  rw [Bv'_rv]
  refine Bv_mulVec_mem X v {b | b.1 < a.1} _ fun k hk => ?_
  rw [mulVec_single_one]
  refine hpat k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem half_of_inN {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ}
    (hg : InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) g) :
    ∀ i j, lvk X j ≤ D.R.rS + 1 → lvk X j < lvk X i + 1 →
      ((Bv' X v * g * Bv X v - 1 : Matrix (Kap X) (Kap X) ℂ)) i j = 0 := by
  intro i j hj hij
  have hM : Bv' X v * g * Bv X v - 1 = Bv' X v * (g - 1) * Bv X v := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bv'_mul_Bv]
  have hcol : ((Bv' X v * g * Bv X v - 1 : Matrix (Kap X) (Kap X) ℂ)) i j =
      (Bv' X v *ᵥ ((g - 1) *ᵥ rv X.B.I v (bv X j))) i := by
    rw [hM, ← Bv_col, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_single_one]
    rfl
  rw [hcol]
  rcases j with a | w | a
  · refine Bv'_mulVec_supp X v {b | b.1 < a.1} (hg.1.1 a) i ?_
    rintro ⟨b, hb, rfl⟩
    simp only [lvk, Sum.elim_inl, Set.mem_setOf_eq] at hij hb
    omega
  · have h := hg.2 _ fun a => hJ_rv_e_w X v a w
    refine Bv'_mulVec_supp X v {b | b.1 < D.R.rS} h i ?_
    rintro ⟨b, -, rfl⟩
    simp only [lvk, Sum.elim_inl, Sum.elim_inr] at hij
    have := b.2
    omega
  · simp only [lvk, Sum.elim_inr] at hj
    have := a.2
    omega

theorem pat_of_mem {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) : InPat (lvk X) 1 (Mv X v s - 1) := by
  have hs' : s⁻¹ ∈ X.NinfU u := (NinfSub X.eR (X.zR u)).inv_mem hs
  have hMN : Mv X v s = sharp (JBv X v) (JBv' X v) (Mv X v s⁻¹) := by
    have := Mv_inv X v s⁻¹
    rwa [inv_inv] at this
  exact half_to_full (JBv_graded X v) (JBv'_graded X v) (JBv'_mul X v) (h₀ := D.R.rS + 1) (by omega) hMN
    (half_of_inN X u v (hs' v)) (half_of_inN X u v (hs v))

end Formalism.L2.SG.Pf.UnipB
end
end

