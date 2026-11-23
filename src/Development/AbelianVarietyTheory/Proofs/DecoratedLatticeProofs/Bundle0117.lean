module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarAdelicUpperUnitriangularEntryTranslateInvari
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IwaFlag

variable {D : D7}

theorem cA_mem_idAt' {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  obtain ⟨ε, -, hc, -, hε, -⟩ := (_root_.GlobalTheory.FinPl.localComponents D (· = v)).1
  rw [hε] at h ⊢
  have := congrArg (cA D) h
  rwa [map_mul, hc] at this

theorem mul_left_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} (A : Matrix (Fin l) (Fin m) R)
    {M : Matrix (Fin m) (Fin k) R} (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (A * M) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (h x j)

theorem mul_right_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} {M : Matrix (Fin l) (Fin m) R}
    (B : Matrix (Fin m) (Fin k) R) (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (M * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (h i x)

end GlobalTheory.IwaFlag

namespace GlobalTheory.IwaFlag

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem flag_stab : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S g ⬝ d.jX = d.jX ⬝ a) → ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), g = n * d.levi t * d.emb0 γ := by
  intro D S S₀ ρ d v g hg ⟨a, hup, hgX⟩
  have hG' : ∀ i j, (mt S g - 1) i j ∈ idAt D (· = v) := fun i j => by
    rw [Matrix.sub_apply]; exact (mem_congGrp_iff S (idAt D (· = v)) g).1 hg i j

  have hba : (adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ d.jX)) * a = 1 := by
    have h1 : adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ (mt S g ⬝ d.jX)) = 1 := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
      exact d.gram_YX
    rw [hgX] at h1
    simpa only [Matrix.mul_assoc] using h1
  have hab : a * (adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ d.jX)) = 1 := mul_eq_one_comm.1 hba
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin ρ) (AE D), A.1 = a := ⟨⟨a, _, hab, hba⟩, rfl⟩

  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hba
  rw [Matrix.det_of_upperTriangular (M := a) (fun ⦃i j⦄ h => hup i j h)] at hdet
  have hu : ∀ i, IsUnit (a i i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => a k k) (Finset.mem_univ i)) hdet
  obtain ⟨t, ht1, htinv⟩ : ∃ t : GL (Fin ρ) (AE D), t.1 = diagonal (fun i => a i i) ∧
      (t⁻¹).1 = diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) :=
    ⟨⟨diagonal (fun i => a i i), diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)),
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.mul_val_inv, diagonal_one],
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.val_inv_mul, diagonal_one]⟩, rfl, rfl⟩
  have ht_diag : ∀ i j, i ≠ j → t.1 i j = 0 := fun i j h => by rw [ht1]; exact diagonal_apply_ne _ h

  have hAt : (A * t⁻¹).1 =
      a * diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) := by
    rw [Units.val_mul A t⁻¹, htinv, hA]
  have hUX : A * t⁻¹ ∈ UX D ρ := fun i j =>
    ⟨fun h => by rw [hAt, mul_diagonal, hup i j h, zero_mul],
      by rw [hAt, mul_diagonal]; exact IsUnit.mul_val_inv (hu i)⟩
  have hR' : mt S (g * (d.levi t)⁻¹) ⬝ d.jX = d.jX ⬝ (A * t⁻¹).1 := by
    rw [Units.val_mul A t⁻¹, hA, ← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.levi_jX]
    simpa only [Matrix.mul_assoc] using congrArg (fun M : Mx D S.rank ρ => M ⬝ (t⁻¹).1) hgX
  have hR : g * (d.levi t)⁻¹ ∈ GlobalTheory.Unf.Rgrp S (rat d.e) := ⟨A * t⁻¹, hUX, hR'⟩
  rw [GlobalTheory.Unf.Rgrp_eq d] at hR
  obtain ⟨n, hn, γ, hnγ⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.2.1 _).1 hR

  have hcomm : d.levi t * d.emb0 γ = d.emb0 γ * d.levi t := by
    refine d.ga_ext ?_ ?_ ?_
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclY, d.levi_jY, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]
  have hgfac : g = n * d.levi t * d.emb0 γ := by
    rw [mul_assoc, hcomm, ← mul_assoc, ← hnγ, inv_mul_cancel_right]

  have hmtγ : mt S₀ γ = d.p0 ⬝ (mt S g ⬝ d.j0) := by
    have e1 : mt S (g * (d.levi t)⁻¹) ⬝ d.j0 = mt S g ⬝ d.j0 := by
      rw [← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]
    have e2 : d.p0 ⬝ (mt S (n * d.emb0 γ) ⬝ d.j0) = mt S₀ γ := by
      rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc,
        GlobalTheory.Unf.flagUnipotent_anisotropic_projection_eq_one d hn, Matrix.one_mul]
    rw [← e2, ← hnγ, e1]
  have hγ : γ ∈ grpAt S₀ (· = v) := (mem_congGrp_iff S₀ _ γ).2 fun i j => by
    have e : mt S₀ γ - 1 = d.p0 ⬝ ((mt S g - 1) ⬝ d.j0) := by
      rw [hmtγ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.p0_j0]
    rw [← Matrix.sub_apply, e]
    exact mul_left_mem _ (mul_right_mem _ hG') i j

  have haI : ∀ i j, (a - 1) i j ∈ idAt D (· = v) := by
    have e : a - 1 = d.pX ⬝ ((mt S g - 1) ⬝ d.jX) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.pX_jX, hgX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    intro i j
    rw [e]
    exact mul_left_mem _ (mul_right_mem _ hG') i j
  have ht1I : ∀ i j, (t.1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [ht1, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply] at this
      rwa [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have htiI : ∀ i j, ((t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [htinv, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      rw [diagonal_apply_eq, Matrix.one_apply_eq]
      have e : (((hu i).unit⁻¹ : (AE D)ˣ) : AE D) - 1 = -((((hu i).unit⁻¹ : (AE D)ˣ) : AE D) * (a i i - 1)) := by
        rw [mul_sub, IsUnit.val_inv_mul (hu i)]; ring
      rw [e]
      exact (idAt D (· = v)).neg_mem (Ideal.mul_mem_left _ _ this)
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have hadjI : ∀ i j, (adj (t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [← adj_one, ← adj_sub]
    exact cA_mem_idAt' (htiI j i)
  have hlevI : d.levi t ∈ grpAt S (· = v) := by
    have e : mt S (d.levi t) - 1 = d.jX ⬝ (t.1 - 1) ⬝ d.pX + d.jY ⬝ (adj (t⁻¹).1 - 1) ⬝ d.pY := by
      rw [d.mt_levi, ← d.sum_eq_one]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      abel
    refine (mem_congGrp_iff S _ _).2 fun i j => ?_
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact add_mem (mul_right_mem _ (mul_left_mem _ ht1I) i j) (mul_right_mem _ (mul_left_mem _ hadjI) i j)
  have hnI : n ∈ grpAt S (· = v) := by
    have e : n = g * (d.levi t * d.emb0 γ)⁻¹ := eq_mul_inv_of_mul_eq ((mul_assoc _ _ _).symm.trans hgfac.symm)
    rw [e]
    exact mul_mem hg (inv_mem (mul_mem hlevI (wittCoreEmbedding_preserves_supportedUnitarySubgroup d hγ)))
  exact ⟨n, hn, hnI, t, ht_diag, hlevI, γ, hγ, hgfac⟩

end GlobalTheory.IwaFlag

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLaw
section
namespace I195MixedCoordinates_da3d54e6b295c596ea3330b3

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_da3d54e6b295c596ea3330b3

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlatShiftPf

variable {D : D7}

theorem psiE_mul_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AE D) :
    psiE ψ a * star (psiE ψ a) = 1 := by
  have h1 : ‖psiE ψ a‖ = 1 := hψ.1.2.1 _
  rw [Complex.star_def, Complex.mul_conj', h1]; simp

theorem measEmb_val (ρ : ℕ) : MeasurableEmbedding (fun u : UX D ρ => u.1.1) := by
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  exact (GlobalTheory.UnitU.isClosedEmbedding_val D ρ).measurableEmbedding

theorem measEmb_add {ρ : ℕ} (N : Mx D ρ ρ) : MeasurableEmbedding (fun m : Mx D ρ ρ => m + N) := by
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  exact (Homeomorph.addRight N).isClosedEmbedding.measurableEmbedding

theorem flatAt_shift {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ σ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (μS : Measure (Mx D W.rank ρ)) (𝓕S : Set (Mx D W.rank ρ))
    (μT : Measure (Mx D σ V₀.rank)) (𝓕T : Set (Mx D σ V₀.rank)) (νU : Measure (UX D ρ)) (hν : νU.IsHaarMeasure)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (f : WO V W → ℂ) (N : Mx D ρ ρ) (hN : ∀ i j, j ≤ i → N i j = 0) :
    flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y (heisO ψ V W (dV.extX W (x ⬝ N)) f) =
      psiE ψ (upSum N) • flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y f := by
  funext w
  simp only [flatAt, flatFun, evalAt, Pi.smul_apply, smul_eq_mul, Check.mixS_heis_extX]
  set c := psiE ψ (upSum N) with hcdef
  have hc : c * star c = 1 := psiE_mul_star hψ _
  set H : Mx D ρ ρ → ℂ := fun m => (_root_.I195MixedCoordinates_da3d54e6b295c596ea3330b3.target dW) V₀ ψ μT 𝓕T ((_root_.I195MixedCoordinates_da3d54e6b295c596ea3330b3.source dV) W ψ μS 𝓕S f (x ⬝ m)) y w with hH
  set K : Mx D ρ ρ → ℂ := fun m => c * (star (psiE ψ (upSum m)) * H m) with hK
  have hpt : ∀ u : UX D ρ, star (psiUni ψ u.1) * (_root_.I195MixedCoordinates_da3d54e6b295c596ea3330b3.target dW) V₀ ψ μT 𝓕T ((_root_.I195MixedCoordinates_da3d54e6b295c596ea3330b3.source dV) W ψ μS 𝓕S f (x ⬝ u.1.1 + x ⬝ N)) y w =
      K (u.1.1 + N) := by
    intro u
    simp only [hK, hH, Matrix.mul_add, upSum_add, psiE_add, star_mul', psiUni]
    linear_combination (-(star (psiE ψ (upSum u.1.1)) * (_root_.I195MixedCoordinates_da3d54e6b295c596ea3330b3.target dW) V₀ ψ μT 𝓕T ((_root_.I195MixedCoordinates_da3d54e6b295c596ea3330b3.source dV) W ψ μS 𝓕S f (x ⬝ u.1.1 + x ⬝ N)) y w)) * hc
  have hs (u : UX D ρ) :
      (_root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV) W ψ μS 𝓕S
          (heisO ψ V W (dV.extX W (x ⬝ N)) f) (x ⬝ u.1.1) =
        (_root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV) W ψ μS 𝓕S
          f (x ⬝ u.1.1 + x ⬝ N) := by
    change dV.mixS W ψ μS 𝓕S (heisO ψ V W (dV.extX W (x ⬝ N)) f) (x ⬝ u.1.1) =
      dV.mixS W ψ μS 𝓕S f (x ⬝ u.1.1 + x ⬝ N)
    exact Check.mixS_heis_extX dV μS 𝓕S f (x ⬝ N) (x ⬝ u.1.1)
  simp_rw [hs, hpt]
  have hinv := (_root_.GlobalTheory.UnitTransl.haar_val_add_invariant D ρ νU hν).2.2 N (fun i j h => hN i j (not_lt.1 h))
  calc ∫ u, K (u.1.1 + N) ∂νU = ∫ m, K (m + N) ∂(νU.map (fun u : UX D ρ => u.1.1)) :=
        ((measEmb_val ρ).integral_map (fun m => K (m + N))).symm
    _ = ∫ m, K m ∂((νU.map (fun u : UX D ρ => u.1.1)).map (fun m => m + N)) :=
        ((measEmb_add N).integral_map K).symm
    _ = ∫ m, K m ∂(νU.map (fun u : UX D ρ => u.1.1)) := by rw [hinv]
    _ = ∫ u, K u.1.1 ∂νU := (measEmb_val ρ).integral_map K
    _ = c * ∫ u, star (psiUni ψ u.1) * H u.1.1 ∂νU := by
        simp only [hK, psiUni]; rw [integral_const_mul]

theorem flatShift : ∀ D : D7, GlobalTheory.FinPl.FlatShift D := by
  intro D ψ P
  refine ⟨fun ρ B J s f _ N _ hN => ?_, fun σ J B s f _ N _ hN => ?_⟩
  · exact flatAt_shift s.weil.std B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν s.vU.unit.1 _ _ f N hN
  · exact flatAt_shift s.weil.std J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν s.vU.unit.1 _ _ f N hN

end GlobalTheory.FlatShiftPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosets
section
noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd Lifts InDual)

namespace GlobalTheory.FinPl.Comm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]


open Classical in
theorem integral_vecInd_eq_zero [MeasurableSpace k] [BorelSpace k] (χ : AddChar k Circle) (e : k)
    (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) (η : n → k) {y₀ : n → k}
    (hy₀ : y₀ ∈ L) (hne : χ (e * (η ⬝ᵥ y₀)) ≠ 1) :
    ∫ y, vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
  have h := integral_add_right_eq_self (μ := μ) (fun y => vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) y₀
  have e2 : ∀ y, vecInd L (y + y₀) * (χ (e * (η ⬝ᵥ (y + y₀))) : ℂ) =
      (χ (e * (η ⬝ᵥ y₀)) : ℂ) * (vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) := fun y => by
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, vecInd, vecInd,
      if_congr (L.add_mem_iff_left hy₀) rfl rfl]
    ring
  simp only [e2] at h
  rw [integral_const_mul] at h
  by_contra h0
  exact hne (Circle.ext (by simpa using (mul_eq_right₀ h0).1 h))

theorem exists_lifts_value (L : Submodule 𝒪[k] (n → k)) {f : Module.Dual 𝓀[k] (Red L)} (hf : f ≠ 0)
    {F : n → k} (hF : Lifts L F f) (b : 𝓀[k]) :
    ∃ y₀ ∈ L, ∃ s : 𝒪[k], (s : k) = F ⬝ᵥ y₀ ∧ residue 𝒪[k] s = b := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  obtain ⟨y, rfl⟩ := Red.mk_surjective L x
  obtain ⟨t, ht⟩ := residue_surjective (R := 𝒪[k]) (b * (f (Red.mk L y))⁻¹)
  obtain ⟨s, hs, hs'⟩ := hF (t • y)
  refine ⟨_, (t • y).2, s, hs, ?_⟩
  rw [hs', map_smul, ← Red.residue_smul, map_smul, ht, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]

theorem integral_vecInd_coset [MeasurableSpace k] [BorelSpace k] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (he : e = 1 ∨ e = -1) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (L : Submodule 𝒪[k] (n → k)) {f : Module.Dual 𝓀[k] (Red L)} (hf : f ≠ 0) {F η : n → k}
    (hF : Lifts L F f) (hη : InDual L (η - q.inv • F)) :
    ∫ y, vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, resChar χ hχ q a ≠ 1 := by
    by_contra h
    push Not at h
    exact resChar_ne_one hχ q (by ext a; rw [h a, AddChar.one_apply])
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have heo : e ∈ 𝒪[k] := by
    rcases he with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  let ε : 𝒪[k] := ⟨e, heo⟩
  have hε : residue 𝒪[k] ε * residue 𝒪[k] ε = 1 := by
    rw [← map_mul, show ε * ε = 1 from Subtype.ext hee, map_one]
  obtain ⟨y₀, hy₀, s, hs, hs'⟩ := exists_lifts_value L hf hF (residue 𝒪[k] ε * a)
  refine integral_vecInd_eq_zero χ e μ L η hy₀ fun h => ha ?_
  have hl : e * ((η - q.inv • F) ⬝ᵥ y₀) ∈ 𝒪[k] := mul_mem heo (hη y₀ hy₀)
  have hsplit : e * (η ⬝ᵥ y₀) = q.inv * ((ε * s : 𝒪[k]) : k) + e * ((η - q.inv • F) ⬝ᵥ y₀) := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, Subring.coe_mul, hs]
    change _ = _ * (e * _) + _
    ring
  rw [hsplit, AddChar.map_add_eq_mul, apply_int_eq_one hχ ⟨_, hl⟩, mul_one] at h
  rw [show a = residue 𝒪[k] (ε * s) by rw [map_mul, hs', ← mul_assoc, hε, one_mul], resChar_residue, h]
  rfl

end GlobalTheory.FinPl.Comm

namespace GlobalTheory.FinPl.Comm

theorem fpair_vecInd_dualInd_add_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle), HasConductor χ 1 → ∀ (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k],
    fpair χ e μ (vecInd L) (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) =
      fpair χ e μ (vecInd L) (dualInd L) := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ L _
  unfold fpair
  congr 1
  funext η
  rw [Pi.add_apply, mul_add, Finset.sum_apply, Finset.mul_sum, add_eq_left]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  have hL : Q.lat = L := mem_withLat.1 hQ
  classical
  unfold cosetInd
  split_ifs with h
  · obtain ⟨F, hF, hD⟩ := h
    have h0 := integral_vecInd_coset q χ hχ e he μ Q.lat Q.red_ne hF hD
    rw [hL] at h0
    rw [h0, zero_mul]
  · rw [mul_zero]

end GlobalTheory.FinPl.Comm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorDualLatticeIndica
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

noncomputable section

namespace GlobalTheory.FinPl.Comm

theorem fpair_charInd_dualInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n),
      fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) = 0 := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  set r := resChar χ hχ q with hr
  obtain ⟨a, ha⟩ : ∃ a, r a ≠ 1 := by
    by_contra h
    push_neg at h
    exact resChar_ne_one hχ q (by ext x; simpa using h x)
  obtain ⟨e₁, he₁⟩ := Q.exists_hasVal_one
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (-a)
  have hy₀ : Q.HasVal (s • e₁) (-a) := by simpa [hs] using he₁.smul s
  have hI : ∫ y, charInd r Q y ∂μ = 0 := by
    have h1 := integral_add_right_eq_self (μ := μ) (charInd r Q) (s • e₁)
    have h2 : ∀ y, charInd r Q (y + s • e₁) = r a * charInd r Q y := fun y => by
      by_cases hy : y ∈ Q.lat
      · have hyy : y + s • e₁ ∈ Q.lat := add_mem hy hy₀.mem
        rw [charInd, charInd, vecInd, vecInd, if_pos hy, if_pos hyy, ((Pair.hasVal_ev hy).add hy₀).ev_eq,
          neg_add, neg_neg, AddChar.map_add_eq_mul]
        ring
      · have hyy : y + s • e₁ ∉ Q.lat := fun h => hy (by simpa using sub_mem h hy₀.mem)
        rw [charInd, charInd, vecInd, vecInd, if_neg hy, if_neg hyy]
        simp
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    by_contra h0
    exact ha ((mul_eq_right₀ h0).1 h1)
  unfold fpair
  have hF : ∀ η, (∫ y, charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * dualInd Q.lat η = 0 := fun η => by
    by_cases hη : GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.InDual Q.lat η
    · rw [dualInd, if_pos hη, mul_one]
      have : (fun y => charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ)) = fun y => charInd r Q y := by
        funext y
        by_cases hy : y ∈ Q.lat
        · have hm : e * (η ⬝ᵥ y) ∈ 𝒪[k] := by
            rcases he with rfl | rfl
            · simpa using hη y hy
            · simpa using hη y hy
          rw [show χ (e * (η ⬝ᵥ y)) = 1 from apply_int_eq_one hχ ⟨_, hm⟩]
          simp
        · rw [charInd, vecInd, if_neg hy]
          simp
      rw [this, hI]
    · rw [dualInd, if_neg hη, mul_zero]
  simp only [hF, integral_zero]

end GlobalTheory.FinPl.Comm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeDatumMainPartMemSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum qvec)

namespace GlobalTheory.FinPl.Comm

theorem mainDatum_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (ε : 𝓀[k]ˣ) (P : Pair k n') (Q : Pair k n) : mainDatum q χ ε P Q ∈ SB (Matrix n n' k) := by
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0}
  have h : mainDatum q χ ε P Q = ∑ f' : {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0},
      χ (-((ε : 𝓀[k]) * f'.1 (qvec q P))) • phiOne (ofDual P.ker f') Q := by
    funext x
    rw [mainDatum, finsum_eq_sum_of_fintype, Finset.sum_apply]
    rfl
  rw [h]
  exact Submodule.sum_mem _ fun f' _ => Submodule.smul_mem _ _ (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _)

end GlobalTheory.FinPl.Comm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMemStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a b : GA D S), InK S L P a → InK S L P b → InK S L P (a * b) := by
  first | exact @GlobalTheory.FinPl.inK_mul | exact GlobalTheory.FinPl.inK_mul | (intros; apply GlobalTheory.FinPl.inK_mul <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGLStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_determines_sphericalHeckeCharacter_GL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (B : Multiset ℂˣ), ∀ φ ∈ Hecke ℂ (KGL w (n := n)), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V), IsSatVecGL w ρ x B → heckeVec ρ (KGL w (n := n)) φ x = z • x := by
  first | exact @GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL | exact GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL | (intros; apply GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL <;> assumption)
end

