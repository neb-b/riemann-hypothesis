module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorOnFrameAndClassSummandPolynomial
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem polD_eq_map_polDY (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    GL3Theta.polD D s Q y' =
      MvPolynomial.map (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q) := by
  set v : GL3Theta.FrV D N' → ℂ := fun k => y' k.1 k.2.1 k.2.2
  have hmap : ∀ P : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ),
      MvPolynomial.map (MvPolynomial.eval v) P = MvPolynomial.mapAlgHom (MvPolynomial.aeval v) P := fun P => rfl
  rw [hmap]
  unfold GL3Theta.polD polDY
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun k => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.mapAlgHom_apply]
  split_ifs with h
  · simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.C_mul]
    simp [v]
  · simp

theorem applyFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame := by
  intro D N N' s Q G y'
  rw [polD_eq_map_polDY]
  unfold GL3Theta.applyAt0 framePol GL3Theta.evFr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  symm
  rw [← Finset.sum_subset (MvPolynomial.support_map_subset
    (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q))]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.eval_C, mul_assoc]
  · intro α _ hα
    rw [MvPolynomial.notMem_support_iff] at hα
    rw [MvPolynomial.coeff_map] at hα
    rw [map_mul, hα, zero_mul]

theorem entQFrame : Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ i c Q c' y'
  unfold Formalism.L2.KerInert.SecondKernelDifference.entQ
  rw [applyFrame]
  rfl

theorem applyFrame_and_entQFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame :=
  ⟨applyFrame, entQFrame⟩

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZero
section
noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MvPolynomial

theorem sum_castLE_of_vanish {M : Type} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (F : Fin b → M)
    (hF : ∀ r : Fin b, a ≤ r.1 → F r = 0) : ∑ r, F r = ∑ r : Fin a, F (Fin.castLE h r) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)
  intro r hr
  apply hF
  by_contra hlt
  exact hr ⟨⟨r.1, by omega⟩, rfl⟩

theorem polDY_colSub (D : D7) {N N' : ℕ} (hN : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (β : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (hβ : ∀ τ r c, c < r → β τ r c = 0) :
    MvPolynomial.map (colSub β : MvPolynomial (GL3Theta.FrV D N') ℂ →+* MvPolynomial (GL3Theta.FrV D N') ℂ) (polDY D s Q (N' := N')) =
      polDY D s (colSub (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN)) Q) (N' := N') := by
  have e : (MvPolynomial.mapAlgHom (colSub β : MvPolynomial (GL3Theta.FrV D N') ℂ →ₐ[ℂ] MvPolynomial (GL3Theta.FrV D N') ℂ)).comp
      (aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
        C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
          X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))) =
      (aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
        C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
          X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))).comp (colSub (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, i, c⟩
    have hc : (c : ℕ) < N' := lt_of_lt_of_le c.2 hN
    have h1 : ∀ r : Fin N, (r : ℕ) < N' := fun r => lt_of_lt_of_le r.2 hN
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, aeval_X, colSub, dif_pos hc, dif_pos (h1 _), map_sum, map_mul, MvPolynomial.mapAlgHom_apply,
      map_X, map_C, algHom_C, algebraMap_eq, Matrix.submatrix_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.coe_coe, aeval_C, aeval_X, map_sum, map_mul, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [sum_castLE_of_vanish hN]
    · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.castLE, MvPolynomial.algebraMap_apply, algebraMap_eq]
      ring
    · intro r hr
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [hβ τ r ⟨c, hc⟩ (Fin.lt_def.2 (lt_of_lt_of_le c.2 hr))]
      simp
  exact DFunLike.congr_fun e Q

theorem wt_polDY_framePol : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, AddMonoidAlgebra.coeff (polDY D s Q (N' := N')) α ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  intro D N N' hN s ν Q hQ
  have hc : ∀ α, AddMonoidAlgebra.coeff (polDY D s Q (N' := N')) α ∈ WtPol ℂ (extNu N' ν) := by
    intro α β hβ
    have hβ0 : ∀ τ r c, c < r → β τ r c = 0 := fun τ r c h => (hβ τ).1 r c h
    have hB : IsBor (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN)) :=
      fun τ => ⟨fun r c h => (hβ τ).1 _ _ h, fun r => (hβ τ).2 _⟩
    have e1 := congrArg (AddMonoidAlgebra.coeff · α) (polDY_colSub D hN s Q β hβ0)
    have e2 : ∀ (c : ℂ) (P : MvPolynomial (GL3Theta.FrV D N) ℂ), polDY D s (c • P) (N' := N') = c • polDY D s P (N' := N') :=
      fun c P => by unfold polDY; exact map_smul _ c P
    rw [MvPolynomial.coeff_map, hQ _ hB, e2, MvPolynomial.coeff_smul] at e1
    have e3 : (∏ τ, ∏ r, β τ r r ^ extNu N' ν τ r) = ∏ τ, ∏ r, (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN) r r ^ ν τ r := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      symm
      refine Fintype.prod_of_injective (Fin.castLE hN) (Fin.castLE_injective hN) _ _ ?_ ?_
      · intro r hr
        have hr' : ¬ (r : ℕ) < N := fun h => hr ⟨⟨r, h⟩, rfl⟩
        simp only [extNu, dif_neg hr', pow_zero]
      · intro r
        simp only [extNu, Matrix.submatrix_apply, Fin.coe_castLE, dif_pos r.2]
    rw [e3]
    exact e1
  refine ⟨hc, fun Θ => ?_⟩
  unfold framePol
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (hc α)

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevels
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.LastEnt

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem succ_mul_succ_sub_one_div_succ (l t : ℕ) : ((l + 1) * (t + 1) - 1) / (t + 1) = l := by
  have h : (l + 1) * (t + 1) - 1 = t + (t + 1) * l := by rw [Nat.succ_mul]; ring_nf; omega
  rw [h, Nat.add_mul_div_left _ _ (Nat.succ_pos t), Nat.div_eq_of_lt (Nat.lt_succ_self t), zero_add]

theorem eT_zero (τ : D.what₂.Tau) : eT X D pos 0 τ =
    lamAt (X.G.P.lam0 (pos.symm τ).1) (pos.symm τ).2 (Fin.last X.G.P.m) := rfl

theorem eT_succ (l : ℕ) (τ : D.what₂.Tau) : eT X D pos (l + 1) τ =
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 (pos.symm τ).1 s) (fun i => X.Fl.w (pos.symm τ).1 i s) (l + 1))
      (pos.symm τ).2 (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) := rfl

theorem lamAt_last0 (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (X.G.P.lam0 v) s (Fin.last X.G.P.m) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else X.G.P.lam0 v s (Fin.last X.G.P.m) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [if_pos h, if_neg (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
  · rw [if_neg h, if_pos (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]

theorem lamAt_lastS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (l + 1)) s
        (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else -(X.Fl.w v (l + 1) s) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [if_pos h, if_neg (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
    unfold liftWt
    beta_reduce
    have h1 : 1 ≤ (l + 1) * (X.Fl.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [dite_eq_right (by simp only [Fin.val_last]; omega)]
    simp only [Fin.val_last]
    have h2 : X.G.P.m + (l + 1) * (X.Fl.t + 1) - (X.G.P.m + 1) = (l + 1) * (X.Fl.t + 1) - 1 := by omega
    rw [h2, succ_mul_succ_sub_one_div_succ]
  · rw [if_neg h, if_pos (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]
    unfold liftWt
    beta_reduce
    rw [dite_eq_left (by simp)]
    rfl

theorem nuv_one (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (j + 1) s 1 = X.G.P.lam0 v s 0 + X.w v (j + 1) s := by
  unfold Sys.nuv nu
  rw [if_pos ⟨le_refl 1, by omega⟩]
  unfold lamI
  rw [dite_eq_left ⟨le_refl 1, by omega⟩]
  rfl

theorem nuv_one_at_firstLevelIndex (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v 1 s (NN X.G.P.m X.t 0) = X.G.P.lam0 v s (Fin.last X.G.P.m) + X.w v 1 s := by
  unfold Sys.nuv nu NN
  rw [if_pos ⟨by omega, by omega⟩]
  unfold lamI
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 2
  ext
  simp

theorem nuv_NNS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (l + 1 + 1) s (NN X.G.P.m X.t (l + 1)) = -X.w v (l + 1) s + X.w v (l + 1 + 1) s := by
  have h1 : 1 ≤ (l + 1) * (X.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h3 : (l + 1) * (X.t + 1) + (X.t + 1) = (l + 1 + 1) * (X.t + 1) := by ring
  unfold Sys.nuv nu
  rw [if_neg (by unfold NN; omega), if_pos ⟨by unfold NN; omega, by unfold NN; omega⟩]
  have h2 : NN X.G.P.m X.t (l + 1) - (X.G.P.m + 2) = (l + 1) * (X.t + 1) - 1 := by unfold NN; omega
  rw [h2, succ_mul_succ_sub_one_div_succ]

end GlobalTheory.TwV.DelA.LastEnt


open GlobalTheory.TwV.DelA.LastEnt in
theorem GlobalTheory.TwV.DelA.eT_last_pair : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  intro p _ X D pos j τ
  have hc1 : cT1 X D pos j τ = X.G.P.lam0 (pos.symm τ).1 (pos.symm τ).2 0 + wT X D pos j τ :=
    nuv_one X j (pos.symm τ).1 (pos.symm τ).2
  have hw : wT X D pos j τ = X.w (pos.symm τ).1 (j + 1) (pos.symm τ).2 := rfl
  rw [hc1, eT_succ X D pos j τ, lamAt_lastS X j]
  cases j with
  | zero =>
    rw [eT_zero, lamAt_last0, nuv_one_at_firstLevelIndex, hw]
    constructor <;> split_ifs <;> ring
  | succ l =>
    rw [eT_succ X D pos l τ, lamAt_lastS X l, nuv_NNS, hw]
    constructor <;> split_ifs <;> ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReindexRenamePointDetLatK
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem reindex_rename_point_det_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N n : ℕ} (h : N = n) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (y : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb : Submodule (𝓞 E) (Fin N → E)), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y ∧ Matrix.GeneralLinearGroup.det (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = Matrix.GeneralLinearGroup.det y ∧ HEq ((latK sp (J.reindex (finCongr h) (finCongr h)) a (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) (Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E)))).map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N n h J a y Lb
  subst h
  have hr : ∀ {A : Type} [CommRing A] (g : GL (Fin N) A), Formalism.L2.PairingIndexBounds.F.reGL (finCongr (rfl : N = N)) g = g := by
    intro A _ g
    ext i j
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have hJ : J.reindex (finCongr (rfl : N = N)) (finCongr (rfl : N = N)) = J := by
    ext i j
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, hr]
  · rw [hr]
  · apply heq_of_eq
    rw [hJ, hr, map_reE_rfl, map_reE_rfl]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SgRevNeZero
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

def twF {n : ℕ} (c : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos y τ).det ^ (-(c τ)) else 1) * GL3Theta.evFr D Q (zT X D pos y)

theorem zT_zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) :
    zT X D pos (zT X D pos f) = f := by
  funext τ
  unfold zT
  split_ifs with h
  · have hu : IsUnit (f τ).det := isUnit_iff_ne_zero.2 (hf τ)
    rw [show ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix (Equiv.refl (Fin n)) (Fin.revPerm : Equiv.Perm (Fin n)) from rfl,
      Matrix.inv_submatrix_equiv, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu]
    ext i j
    simp
  · rfl

theorem det_zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det = if IsOddPos (pos.symm τ).2 then sgRev n * ((f τ).det)⁻¹ else (f τ).det := by
  unfold zT
  split_ifs with h
  · rw [show ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) from rfl,
      Matrix.det_permute', Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp [sgRev]
  · rfl

theorem sgRev_ne_zero (n : ℕ) : sgRev n ≠ 0 := by
  unfold sgRev
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdHNatsmulRight
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  exact (IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem stdH_adj (D : D7) {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) (x : Fin N → D.host.E)
    (y : Fin N' → D.host.E) :
    stdH D.host.E N x ((A.map D.host.conj)ᵀ *ᵥ y) = stdH D.host.E N' (A *ᵥ x) y := by
  unfold stdH
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [star_eq_hostConj, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem stdH_natsmul_left (D : D7) {N : ℕ} (s : ℕ) (x y : Fin N → D.host.E) :
    stdH D.host.E N ((s : D.host.E) • x) y = (s : D.host.E) * stdH D.host.E N x y := by
  unfold stdH
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem stdH_natsmul_right (D : D7) {N : ℕ} (s : ℕ) (x y : Fin N → D.host.E) :
    stdH D.host.E N x ((s : D.host.E) • y) = (s : D.host.E) * stdH D.host.E N x y := by
  unfold stdH
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem adj_maps_sd : ∀ (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E) (s : ℕ), IsSDLat D.host.E N L → IsSDLat D.host.E N' L' → (∀ x ∈ L, (s : D.host.E) • (A *ᵥ x) ∈ L') → ∀ y ∈ L', (s : D.host.E) • ((A.map D.host.conj)ᵀ *ᵥ y) ∈ L := by
  intro D N N' L L' A s hL hL' hA y hy
  refine (hL.2.2 _).2 fun x hx => ?_
  rw [stdH_natsmul_right, stdH_adj, ← stdH_natsmul_left]
  exact (hL'.2.2 y).1 hy _ (hA x hx)

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelStatementsOfJoint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Port

theorem oneHyp_lev0At : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Joint0 g.herm.lev0 u (g.forms u) → OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y := by
  intro D Gt c g u w hg h
  exact oneHyp_rec u w hg g.cmp h

end GlobalTheory.Port
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorFirstFactorIntegersOntoLocalIntegers
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem ph_tensInt_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → ∀ v, (∀ s ∈ intV E (A.pl v).1, A.ph v s ∈ (A.pl v).1.adicCompletionIntegers F) ∧ ∀ x ∈ (A.pl v).1.adicCompletionIntegers F, ∃ s ∈ intV E (A.pl v).1, A.ph v s = x := by
  intro F E _ _ _ _ _ n p G A hA v
  have h1 : ∀ y : (A.pl v).1.adicCompletion F, A.ph v ((1 : E) ⊗ₜ[F] y) = y := by
    intro y
    show ((A.spl v) ((1 : E) ⊗ₜ[F] y)).1 = y
    rw [hA v y]
  refine ⟨?_, ?_⟩
  · intro s hs
    have hle : intV E (A.pl v).1 ≤ ((A.pl v).1.adicCompletionIntegers F).toSubring.comap (A.ph v) := by
      refine (Subring.closure_le).2 ?_
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · obtain ⟨r, rfl⟩ := hx
        show A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) ∈ (A.pl v).1.adicCompletionIntegers F
        have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E r) := (RingOfIntegers.isIntegral r).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E)
        obtain ⟨q, hq, hev⟩ := h0
        let f : E →+* (A.pl v).1.adicCompletion F := (A.ph v).comp (Algebra.TensorProduct.includeLeftRingHom)
        have hf : f (algebraMap (𝓞 E) E r) = A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) := rfl
        have hint' : IsIntegral ((A.pl v).1.adicCompletionIntegers F) (A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))) := by
          refine ⟨q.map (Int.castRingHom _), hq.map _, ?_⟩
          rw [Polynomial.eval₂_map, ← hf]
          have := congrArg f hev
          rw [map_zero, Polynomial.hom_eval₂] at this
          have e : (algebraMap ((A.pl v).1.adicCompletionIntegers F) ((A.pl v).1.adicCompletion F)).comp
              (Int.castRingHom ((A.pl v).1.adicCompletionIntegers F)) = f.comp (algebraMap ℤ E) := RingHom.ext_int _ _
          rw [e]
          exact this
        obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
        rw [← hz]
        exact z.2
      · show A.ph v ((1 : E) ⊗ₜ[F] y) ∈ (A.pl v).1.adicCompletionIntegers F
        rw [h1]
        exact hy
    exact hle hs
  · intro x hx
    refine ⟨(1 : E) ⊗ₜ[F] x, ?_, h1 x⟩
    exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)

end GlobalTheory.TwV
end

