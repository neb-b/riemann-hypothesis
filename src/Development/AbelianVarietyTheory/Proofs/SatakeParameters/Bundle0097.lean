module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSubspacesKerTransposeEqCardRange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem card_le_ker_transpose_eq_card_range_le :
    ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  intro k _ m n j z
  set B : LinearMap.BilinForm k (Fin m → k) := Matrix.toBilin' (1 : Matrix (Fin m) (Fin m) k) with hBdef
  have hB : ∀ x y, B x y = x ⬝ᵥ y := by
    intro x y
    rw [hBdef, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hrefl : B.IsRefl := by
    intro x y h
    rw [hB] at h ⊢
    rw [dotProduct_comm]; exact h
  have hnd : B.Nondegenerate := by
    rw [hBdef]
    exact Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have hinv : ∀ W : Submodule k (Fin m → k), B.orthogonal (B.orthogonal W) = W :=
    fun W => LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W
  have hdim : ∀ W : Submodule k (Fin m → k),
      Module.finrank k W + Module.finrank k (B.orthogonal W) = m := by
    intro W
    have h1 := LinearMap.BilinForm.finrank_orthogonal hnd W
    have h2 := Submodule.finrank_le W
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  have hker : LinearMap.ker zᵀ.mulVecLin = B.orthogonal (LinearMap.range z.mulVecLin) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff, Matrix.mulVecLin_apply]
    constructor
    · rintro h _ ⟨y, rfl⟩
      show B (z.mulVecLin y) x = 0
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, h, zero_dotProduct]
    · intro h
      ext i
      have h1 : B (z.mulVecLin (Pi.single i 1)) x = 0 := h _ ⟨_, rfl⟩
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, dotProduct_single, mul_one] at h1
      simpa using h1
  let e : Submodule k (Fin m → k) ≃ Submodule k (Fin m → k) :=
    ⟨B.orthogonal, B.orthogonal, hinv, hinv⟩
  refine Nat.card_congr (e.subtypeEquiv fun W => ?_)
  show _ ↔ Module.finrank k (B.orthogonal W) = j ∧ LinearMap.range z.mulVecLin ≤ B.orthogonal W
  have hd := hdim W
  refine and_congr ⟨fun h => by omega, fun h => by omega⟩ ?_
  rw [hker]
  constructor
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosEqZeroOfMulMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos : ∀ {R : Type} [CommRing R] [IsDomain R] (p : ℕ), p.Prime → IsUnit ((p : ℕ) : R) → ∀ (π : R), π ≠ 0 →
  (∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) → ∀ (S : Subring R),
  (∀ s ∈ S, ∀ i : ℕ, π ^ i ∣ s → ∃ s' ∈ S, s = π ^ i * s') →
  (∀ y : R, (∀ k : ℕ, ∃ s ∈ S, π ∣ y - ((p : ℕ) : R) ^ k * s) → π ∣ y) →
  ∀ u : R, (∀ m : ℕ, 1 ≤ m → ∃ s ∈ S, ∃ e : R, (e = 1 ∨ e = -1) ∧
    π ^ (2 * p ^ m) ∣ ((p : ℕ) : R) * (((p : ℕ) : R) ^ (m - 1) * u - s) - e * π ^ (p ^ m)) →
  ∀ (a : R) (r : ℕ), a ∈ Clos S π → ((p : ℕ) : R) ^ r * a * u ∈ Clos S π → a = 0 := by
  first | exact @GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem | exact GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem | (intros; apply GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameColumnsScaledStandardVectors
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem frameM_coef_eq_chgB : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), (∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y)) → ∀ (X : Fields) (s : Seam D X) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (r : ∀ z, Fin (n z) → ℂ_[p]) (cκ c0 : Bool × HH D → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E), (∀ z, GlobalTheory.DFrame.rho D ι z (σ z : D.host.E) ≠ 0) → (∀ z, GlobalTheory.DFrame.rho D ι z (σ' z : D.host.E) ≠ 0) → (∀ z, (P (tauPl D z)).det ≠ 0) → (∀ z (τ' : D.what₂.Tau), ∑ k, r z k * TaylorLogMetric.tauEmb D lm τ' (a z k) = if τ' = tauPl D z then c0 z else 0) → ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'), frameM (ι : ℂ →+* ℂ_[p]) (fun j => GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.coef D ι cκ r σ σ') i x = cκ x.1 * c0 x.1 * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  intro D p _ lm ι hι X s n N N' a r cκ c0 P P' σ σ' hσ hσ' hdet hsum i x
  unfold frameM
  have hJ : ∀ f : GlobalTheory.DFrame.JJ D n N N' → ℂ_[p], ∑ j, f j = ∑ α, ∑ l, ∑ l', f (α, l, l') := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hJ, Fintype.sum_sigma]
  simp only [GlobalTheory.DFrame.coef, GlobalTheory.DFrame.gc, GlobalTheory.DFrame.pc]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
  rw [Finset.sum_eq_single x.1 (fun z _ hz => by simp [hz]) (by simp)]
  simp only [if_true, GlobalTheory.DFrame.vecF, GlobalTheory.DFrame.mat, GlobalTheory.DFrame.colR, GlobalTheory.DFrame.rowL, Matrix.of_apply, map_mul, RingEquiv.coe_toRingHom]
  have hsum' := hsum x.1 (s.iT i.1)
  simp only [hι] at hsum'
  have e : ∀ k, ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k)) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (cκ x.1 * r x.1 k * (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) =
      (cκ x.1 * (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) *
      (r x.1 k * ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k))) := fun k => by ring
  rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.mul_sum, hsum']
  by_cases h : s.iT i.1 = tauPl D x.1
  · rw [if_pos h, TaylorLogMetric.chgB, if_pos h.symm]
    simp only [h]
    set tp := tauPl D x.1 with htp
    have hm : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin m) D.host.E),
        Q.map (TaylorLogMetric.tauEmb D lm tp) = Q.map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      intro m Q; ext u v; simp [hι]
    have hinv : ((P tp).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)))⁻¹ =
        ((P tp)⁻¹).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x.1)), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hm, hm, hinv]
    clear e hsum' hJ hsum hm hinv
    have h1 := hσ x.1
    have h2 := hσ' x.1
    simp only [GlobalTheory.DFrame.rho, RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1 h2 ⊢
    simp only [Matrix.map_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← htp] at h1 h2 ⊢
    field_simp
    try ring
  · rw [if_neg h, TaylorLogMetric.chgB, if_neg (fun e => h e.symm)]
    simp

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameHermitianFormTraceRealPlaces
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem hOK_vecF : ∀ (D : D7) (X : Fields) (s : Seam D X) (L : PeriodPair) (Λ : AddSubgroup ℂ), L.lattice.toAddSubgroup = Λ → Function.Bijective (tauPl D) → ∀ (N N' : ℕ) (A B : Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area Λ)⁻¹) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
  intro D X s L Λ hΛ hbij N N' A B p _ ι
  subst hΛ
  have hA : (0 : ℝ) < Formalism.L2.Th1.F.area L := Formalism.L2.Th1.F.areaPos_thm L
  have hconj : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      TaylorLogMetric.embT D τ (D.host.conj x) = starRingEnd ℂ (TaylorLogMetric.embT D τ x) := fun τ x =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) x
  have hL : Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area L.lattice.toAddSubgroup)⁻¹)
      (vecF D s A) (vecF D s B) =
      ∑ τ : X.Tau, TaylorLogMetric.embT D (s.iT τ) (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
    rw [GlobalTheory.FourthRootStd.area_eq]
    unfold Formalism.L2.Th1.GD.hOK Formalism.L2.AlgTh.hSc
    show ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) * ∑ i, ∑ j, _ = _
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hconj, vecF]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have h0 : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    push_cast
    field_simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, map_sum]
  rw [← Equiv.sum_comp s.iT.symm]
  simp only [Equiv.apply_symm_apply]
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  rfl

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFramePairedBlocksDiagonalModRoot
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem GlobalTheory.DFrame.pairedBlock_diag : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (X : Fields) (s : Seam D X) (L : PeriodPair) (sc : ℝ) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E) (th : ℂ_[p]), ‖th‖ ≤ 1 → (∀ A B : Matrix (Fin N') (Fin N) D.host.E, ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k))) → (∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)), ∑ α, GlobalTheory.DFrame.gc D cκ r τ α * GlobalTheory.DFrame.rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0) → (∀ t, ‖GlobalTheory.DFrame.uu D ι cκ r a t‖ ≤ 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) → (∀ (t : HH D) (b₁ b₂ : Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ' (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P' σ' r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' r₂ i)) * GlobalTheory.DFrame.pc D ι σ' (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) → ∀ (t : HH D) (ab ab' : Fin N × Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ j, ∑ k, GlobalTheory.DFrame.coef D ι cκ r σ σ' j ((false, t), ab) * ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' k))) * GlobalTheory.DFrame.coef D ι cκ r σ σ' k ((true, t), ab') = (if ab = ab' then GlobalTheory.DFrame.uu D ι cκ r a t else 0) + th * e := by
  intro D p _ ι X s L sc n N N' a cκ r P P' σ σ' th hth hOK hvan hu hL hR t ab ab'
  obtain ⟨e, he, hE⟩ := Formalism.L2.Th1.GD.tripleTensorAlmostOrthonormal ℂ_[p] D.host.E (HH D) (GlobalTheory.DFrame.rho D ι)
    (Σ z : Bool × HH D, Fin (n z)) ((Bool × HH D) × Fin N) ((Bool × HH D) × Fin N')
    (fun α α' => a α.1 α.2 * D.host.conj (a α'.1 α'.2))
    (fun (l l₂ : (Bool × HH D) × Fin N) => ∑ j : Fin N, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j))
    (fun (q q₂ : (Bool × HH D) × Fin N') => ∑ i : Fin N', GlobalTheory.DFrame.colR D P' σ' q i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' q₂ i))
    N N' (GlobalTheory.DFrame.gc D cκ r) (GlobalTheory.DFrame.pc D ι σ) (GlobalTheory.DFrame.pc D ι σ') th
    (GlobalTheory.DFrame.uu D ι cκ r a) hth hvan (fun _ => rfl) hu hL hR t ab ab'
  refine ⟨e, he, ?_⟩
  rw [← hE]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hOK]
  unfold GlobalTheory.DFrame.coef
  congr 2
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1
  simp only [GlobalTheory.DFrame.mat, Matrix.of_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesPairDualModRootMinusD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem pair_value_eq {D : D7} {p : ℕ} [Fact p.Prime] {ι : ℂ ≃+* ℂ_[p]} {th : ℂ_[p]} (hth : th ≠ 0)
    {z₁ z₂ : Bool × HH D} {s₁ s₂ : D.host.E} (h₁ : ‖rho D ι z₁ s₁‖ = 1) (h₂ : ‖rho D ι z₂ s₂‖ = 1)
    (hc : ‖rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂‖ ≤ ‖th‖) {N : ℕ} {a b : Fin N} {X : D.host.E}
    (hX : X = s₁ * D.host.conj s₂ * (if a = b then 1 else 0)) :
    ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ (rho D ι z₁ s₁)⁻¹ * rho D ι z₁ X * (rho D ι z₂ s₂)⁻¹ =
      (if a = b then 1 else 0) + th * e := by
  have n₁ : rho D ι z₁ s₁ ≠ 0 := fun h => by simp [h] at h₁
  have n₂ : rho D ι z₂ s₂ ≠ 0 := fun h => by simp [h] at h₂
  by_cases hab : a = b
  · refine ⟨(rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂) / (rho D ι z₂ s₂ * th), ?_, ?_⟩
    · rw [norm_div, norm_mul, h₂, one_mul]
      exact div_le_one_of_le₀ hc (norm_nonneg _)
    · subst hX
      simp only [hab, if_true, mul_one, map_mul]
      field_simp
      ring
  · refine ⟨0, by simp, ?_⟩
    subst hX
    simp [hab]

theorem sum_pc_pc {D : D7} {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ}
    (σ : Bool × HH D → 𝓞 D.host.E) (z₁ z₂ : Bool × HH D) (a₁ a₂ : Fin N)
    (F : (Bool × HH D) × Fin N → (Bool × HH D) × Fin N → ℂ_[p]) :
    ∑ l, ∑ l₂, pc D ι σ z₁ l a₁ * F l l₂ * pc D ι σ z₂ l₂ a₂ =
      (rho D ι z₁ (σ z₁ : D.host.E))⁻¹ * F (z₁, a₁) (z₂, a₂) * (rho D ι z₂ (σ z₂ : D.host.E))⁻¹ := by
  rw [Finset.sum_eq_single (z₁, a₁), Finset.sum_eq_single (z₂, a₂)]
  · simp [pc]
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem dual_local_bases_pair : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (th : ℂ_[p]), th ≠ 0 → (∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖th‖) → ∀ {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E), (∀ z, ‖GlobalTheory.DFrame.rho D ι z (σ z : D.host.E)‖ = 1) → (∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) ∧ (∀ (t : HH D) (b₁ b₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P σ r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P σ r₂ i)) * GlobalTheory.DFrame.pc D ι σ (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) := by
  intro D p _ ι th hth h2 N P σ hσ hP
  have key : ∀ t : HH D, (P (tauPl D (false, t)))⁻¹ = ((P (tauPl D (true, t))).map D.host.conj).transpose ∧
      (P (tauPl D (true, t)))⁻¹ * P (tauPl D (true, t)) = 1 := by
    intro t
    have h := hP t
    refine ⟨Matrix.inv_eq_left_inv h, ?_⟩
    apply Matrix.nonsing_inv_mul
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hd' : (P (tauPl D (true, t))).det ≠ 0 := by
      intro h0
      have : ((P (tauPl D (true, t))).map D.host.conj).det = D.host.conj (P (tauPl D (true, t))).det := by
        simpa using (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) (P (tauPl D (true, t)))).symm
      rw [this, h0] at hd
      simp at hd
    exact isUnit_iff_ne_zero.mpr hd'
  refine ⟨fun t a₁ a₂ => ?_, fun t b₁ b₂ => ?_⟩
  · rw [sum_pc_pc ι σ (false, t) (true, t) a₁ a₂
      (fun l l₂ => rho D ι (false, t) (∑ j, rowL D P σ l j * D.host.conj (rowL D P σ l₂ j)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    obtain ⟨k₁, k₂⟩ := key t
    have e := congrFun (congrFun k₂ a₂) a₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    have e' := congrArg D.host.conj e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rowL, k₁, map_mul, map_sum, Matrix.transpose_apply, Matrix.map_apply] at e' ⊢
    have e'' : D.host.conj (if a₂ = a₁ then 1 else 0) = if a₁ = a₂ then 1 else 0 := by
      by_cases h : a₁ = a₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e', Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [sum_pc_pc ι σ (false, t) (true, t) b₁ b₂
      (fun l l₂ => rho D ι (false, t) (∑ i, colR D P σ l i * D.host.conj (colR D P σ l₂ i)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    have e := congrFun (congrFun (hP t) b₂) b₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e
    simp only [colR, map_mul]
    have e'' : (if b₂ = b₁ then (1 : D.host.E) else 0) = if b₁ = b₂ then 1 else 0 := by
      by_cases h : b₁ = b₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLinearEquivMapEqOfFinrankEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem exists_linearEquiv_map_eq_of_finrank_eq {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (W W' : Submodule k V)
    (h : Module.finrank k W = Module.finrank k W') :
    ∃ e : V ≃ₗ[k] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank k U = Module.finrank k U' := by omega
  let a : W ≃ₗ[k] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[k] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[k] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

theorem exists_gl_map_residue_eq (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (W W' : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL (Fin n) O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' h
  let M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfield
section
open NumberField IsDedekindDomain

theorem GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal := by
  intro E _ _ _
  obtain ⟨d, s, hs, hsn, -⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hsn
    have : s = 0 := by simpa using hs
    rw [this]
    exact zero_mem _
  have h2d : (2 * d : 𝓞 (maximalRealSubfield E)) ≠ 0 := mul_ne_zero two_ne_zero hd0
  refine ⟨Ideal.absNorm (Ideal.span {2 * d}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h2d
  intro K _ _ _ _ w hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {2 * d}))
  haveI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  have hint : ∀ x : 𝓞 (maximalRealSubfield E),
      IsIntegral ℤ (algebraMap E K ((x : maximalRealSubfield E) : E)) := fun x =>
    (RingOfIntegers.isIntegral_coe x).map
      ((algebraMap E K).comp (maximalRealSubfield E).subtype).toIntAlgHom
  have hmem : algebraMap E K ((d : maximalRealSubfield E) : E) ∈ maximalRealSubfield K :=
    (GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).2 (d : maximalRealSubfield E).2
  have hai : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield K) :=
    (isIntegral_algHom_iff (maximalRealSubfield K).subtype.toIntAlgHom Subtype.val_injective).1 (hint d)
  let a : 𝓞 (maximalRealSubfield K) := ⟨_, hai⟩
  refine GlobalTheory.unramified_adjoin_sqrt_of_not_mem K a (algebraMap E K s) ?_ ?_ w ?_
  · rw [← map_pow, hs]; rfl
  · exact fun h => hsn ((GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).1 h)
  · intro h
    apply hw
    have h1 : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) ∈ w.asIdeal := h
    let c' : 𝓞 K := ⟨_, hint c⟩
    have h2 : ((Ideal.absNorm (Ideal.span {2 * d}) : ℕ) : 𝓞 K)
        = c' * algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      let f : 𝓞 (maximalRealSubfield E) →+* K :=
        ((algebraMap E K).comp (maximalRealSubfield E).subtype).comp (algebraMap _ _)
      have h3 := congrArg f hc
      rw [map_natCast, map_mul, map_mul, map_ofNat] at h3
      rw [map_natCast, ← h3, map_mul, map_mul, map_mul, map_ofNat, map_ofNat]
      rfl
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
end

