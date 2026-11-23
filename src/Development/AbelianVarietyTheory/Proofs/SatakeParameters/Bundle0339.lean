module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteNormalisingCharPowValuesInCoeffField
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.ChiPow

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem exists_upts_det {n : ℕ} (hn : 0 < n) (Gm : Matrix (Fin n) (Fin n) E) (C : GL (Fin n) E)
    (hC : cT (σ : E →+* E) C.1 * C.1 = Gm) (x : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ)
    (hx : (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * sigR σ _ x = 1) :
    ∃ Y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), Y ∈ UPts σ Gm (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det Y = x := by
  set R := FiniteAdeleRing (𝓞 F) F
  let f : Fin n → (E ⊗[F] R)ˣ := Pi.mulSingle ⟨0, hn⟩ x
  have hf : f = Pi.mulSingle ⟨0, hn⟩ x := rfl
  let d : GL (Fin n) (E ⊗[F] R) := Units.map (Matrix.diagonalRingHom (Fin n) (E ⊗[F] R)).toMonoidHom
    (MulEquiv.piUnits.symm f)
  have hd : (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Matrix.diagonal (fun k => ((f k : (E ⊗[F] R)ˣ) : E ⊗[F] R)) := rfl
  let Cb := bc (inclE (F := F) R) C
  refine ⟨Cb⁻¹ * d * Cb, ?_, ?_⟩
  · have hsig : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE R) := by
      ext e
      simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
    have hG : Gm.map (inclE (F := F) R) = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
      rw [← hC, Matrix.map_mul, ← Formalism.UG.P.cT_map (σ : E →+* E) (sigR σ R) (inclE R) hsig]
      rfl
    have hdd : cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [hd]
      unfold cT
      rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      by_cases hk : k = ⟨0, hn⟩
      · subst hk
        rw [hf, Pi.mulSingle_eq_same, mul_comm]
        exact hx
      · rw [hf, Pi.mulSingle_eq_of_ne hk, Units.val_one, map_one, one_mul]
    have h1 : cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
        cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    have h2 : (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 :=
      Units.mul_inv Cb
    show cT (sigR σ R) (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * Gm.map (inclE (F := F) R) *
      (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Gm.map (inclE (F := F) R)
    rw [hG, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
    calc _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          ((Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            simp only [Matrix.mul_assoc]
      _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            rw [h1, h2]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hdd, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, hd, Matrix.det_diagonal]
    rw [← Units.coe_prod, hf, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]
    calc _ = (Matrix.det ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          Matrix.det (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) * (x : E ⊗[F] R) := by ring
      _ = _ := by rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

end Gen

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc.ChiPow


set_option maxHeartbeats 4000000 in
theorem tw_ch_rat {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}
    (S : StepIn M i hi G) (β : S.Ch) (hr : S.ChRat β)
    (X : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = ((S.tw β).ch X : ℂ) := by
  obtain ⟨cl, hcl⟩ := (S.K β).y_bij.2 (Quotient.mk'' X)
  have hrel := Quotient.eq''.1 hcl
  rw [DoubleCoset.rel_iff] at hrel
  obtain ⟨h, hh, k, hk, hX⟩ := hrel
  obtain ⟨γ, hγ, hγh⟩ := hh
  have h1 := (S.tw β).ch_rat γ hγ h hγh.symm
  have h2 := (S.tw β).ch_U k hk
  obtain ⟨rc, hrc⟩ := hr cl
  refine ⟨(∏ τ, (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ (cTw D i))⁻¹ * rc, ?_⟩
  rw [hX, map_mul (S.tw β).ch, map_mul (S.tw β).ch, h2, mul_one, Units.val_mul, map_mul D.what₂.embLL, hrc, map_inv₀, map_prod]
  congr 1
  have e1 : ∏ τ, D.what₂.embLL (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det ^ cTw D i) =
      ∏ τ, (embT D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ cTw D i :=
    Finset.prod_congr rfl fun τ _ => by rw [map_zpow₀, tEL_emb]
  rw [e1]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem chiI_pow_rat : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), (sysS H X std).Lv.comp j → ∀ x ∈ U1 (sigD D), ∃ r : D.what₂.LL, D.what₂.embLL r = chiI J x ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c x hx
  cases j with
  | zero => exact ⟨1, by simp⟩
  | succ i =>
    have hi : i + 1 ≤ D.R.m := hj
    have hxc : (x : AfE D.host.F D.host.E) * sigR (sigD D) _ x = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hx)
    obtain ⟨Y, hY, hYd⟩ := ChiPow.exists_upts_det (sigD D) Nat.one_pos (1 : Matrix (Fin 1) (Fin 1) D.host.E) 1
      (by rw [Units.val_one, cT_one, Matrix.one_mul]) x hxc
    have hex : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x := ⟨⟨Y, hY⟩, hYd⟩
    have hchi : chiI J x = ((D.chiD (J.dtU hex.choose) : ℂˣ) : ℂ) := by
      unfold chiI
      rw [dite_eq_left hex]
    obtain ⟨Z, hZ, hZd⟩ := ChiPow.exists_upts_det (sigD D) (D.R.N_pos (i + 1)) (gramN D (i + 1) hi) (J.A.crd (i + 1) hi)
      (J.pins.crd_orth (i + 1) hi) x hxc
    let β := ((I.at' i hi).st.eC.symm c).1
    have htw := J.tw i hi β ⟨Z, hZ⟩ hex.choose (hex.choose_spec.trans hZd.symm)
    obtain ⟨r, hr⟩ := ChiPow.tw_ch_rat (I.at' i hi).st β (H.core i hi β).chRat ⟨Z, hZ⟩
    have ht : (sysS H X std).t = D.R.t := (GlobalTheory.TwV.DelB.sysS_ranks S).2.1
    refine ⟨r, ?_⟩
    rw [hr, htw, hchi, ht, Units.val_zpow_eq_zpow_val]
    rfl

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoords
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem realAt_iff_realises : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) (e : D.what₂.Tau → ℤ) (φ : (D.chTw u μ).cls j → (D.chTw u μ).Y j → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), (∀ y, φ (clsAt X H j La.1 La.2) y = (∏ τ, (D.chTw u μ).de j y τ ^ e τ)⁻¹ * frPoly (t.O u μ) j P y) → ∀ V, RealAt d j hj h La φ V ↔ Realises (sysS H X std) D (hT.gat_pos u w hg) j h (fun τ => e τ - cTw D j) (sPt d j hj La • P) (actC (sysS H X std) D (hT.gat_pos u w hg) j h (mM d j hj La) V)) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj h La e φ P hφ V
  have hp := J.pins.frm j hj
  have hde := (t.O u μ).frm_de j hj

  have hdetU : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, IsUnit ((A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ)).det := by
    intro A τ
    have e1 := RingHom.map_det (embT D τ) (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)
    rw [RingHom.mapMatrix_apply] at e1
    rw [← e1]
    exact (Matrix.isUnits_det_units A).map _
  have hmul : ∀ (A A' : GL (Fin (D.R.N j)) D.host.E) τ, ((A * A' : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) =
      (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * (A' : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) := by
    intro A A' τ
    rw [Units.val_mul, Matrix.map_mul]
  have hinv : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, ((A⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
      (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) = 1 := by
    intro A τ
    rw [← hmul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv' : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
      ((A⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) = 1 := by
    intro A τ
    rw [← hmul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMB : mM d j hj La * (bAt J j hj La.1)⁻¹ = J.A.crd j hj * (d.gam j hj La)⁻¹ := by
    unfold mM
    exact mul_inv_cancel_right _ _
  have hat : ∀ τ, (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) =
      (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
        ((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ) := by
    intro τ
    rw [hMB, ← hmul]
    rfl

  have alg : ∀ (z' : Fr D j hj) (f : Fr1 D (D.R.N j)),
      (∀ τ, f.1 τ = (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ) →
      d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j *
          dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' *
          φ (clsAt X H j La.1 La.2) ((J.St j hj).eY.symm z') =
        (∏ τ, (f.1 τ).det ^ (-(e τ - cTw D j))) * GL3Theta.evFr D (sPt d j hj La • P) f.1 := by
    intro z' f hf
    have hfr : (t.O u μ).frm j ((J.St j hj).eY.symm z') = f.1 := by
      funext τ
      rw [hp, Equiv.apply_symm_apply, hf]
      rfl
    have hfp : frPoly (t.O u μ) j P ((J.St j hj).eY.symm z') = GL3Theta.evFr D P f.1 := by
      rw [← hfr]
      rfl
    have hdef : ∀ τ, (D.chTw u μ).de j ((J.St j hj).eY.symm z') τ = (f.1 τ).det := fun τ => by rw [hde, hfr]
    have hsm : GL3Theta.evFr D (sPt d j hj La • P) f.1 = sPt d j hj La * GL3Theta.evFr D P f.1 := by
      unfold GL3Theta.evFr
      rw [MvPolynomial.smul_eval]
    rw [hφ, hfp, hsm]
    simp only [hdef]
    have ha : ∀ τ, embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det ≠ 0 := fun τ =>
      ((Matrix.isUnits_det_units (J.A.crd j hj)).map (embT D τ)).ne_zero
    have hw : ∀ τ, (z'.1 τ).det ≠ 0 := fun τ => (z'.2 τ).ne_zero
    have hdf : ∀ τ, (f.1 τ).det = embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det * (z'.1 τ).det := by
      intro τ
      rw [hf, Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
    have huB : dPow (uB J j hj La.1).1 (fun _ => -(cTw D j)) =
        ∏ τ, (embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det *
          embT D τ (bAt J j hj La.1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det) ^ (-(cTw D j)) := by
      unfold dPow uB
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Units.val_mul, Matrix.det_mul, map_mul]
    have hprod : dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' * (∏ τ, (f.1 τ).det ^ e τ)⁻¹ =
        (∏ τ, (f.1 τ).det ^ (-(e τ - cTw D j))) * dPow (uB J j hj La.1).1 (fun _ => -(cTw D j)) := by
      rw [huB]
      unfold dPow detF
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hdf τ]
      have h1 := ha τ
      have h2 := hw τ
      rw [mul_zpow, mul_zpow, mul_zpow, neg_sub, zpow_sub₀ h1, zpow_sub₀ h2, zpow_neg, zpow_neg]
      field_simp
    unfold sPt
    linear_combination (d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j * GL3Theta.evFr D P f.1) * hprod
  unfold RealAt Realises
  constructor
  · intro hR f
    let z' : Fr D j hj := ⟨fun τ => ((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ) * f.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (f.2 τ)⟩
    let z : Fr D j hj := ⟨fun τ => (d.gam j hj La : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (z'.2 τ)⟩
    have hzz : IsTr (atInf (embT D) (d.gam j hj La).1) z' z := fun τ => rfl
    have hf' : ∀ τ, f.1 τ = (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ := by
      intro τ
      show _ = _ * (_ * _)
      rw [← Matrix.mul_assoc, hinv', Matrix.one_mul]
    have hfz : ∀ τ, f.1 τ = (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) * z.1 τ := by
      intro τ
      rw [hat]
      show _ = _ * _ * (_ * _)
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ)), hinv, Matrix.one_mul, hf']
    have key := (GlobalTheory.T.evalBasisCoords_against_blockAction (sysS H X std) D (hT.gat_pos u w hg) j h (gramC (gramN D j hj) (embT D)) (bAt J j hj La.1)
      (mM d j hj La) V z f hfz).1
    rw [← key, hR z z' hzz, alg z' f hf']
  · intro hR z z' hzz
    let f : Fr1 D (D.R.N j) := ⟨fun τ => (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (z'.2 τ)⟩
    have hfz : ∀ τ, f.1 τ = (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) * z.1 τ := by
      intro τ
      rw [hat, hzz τ]
      show _ = _ * _ * ((d.gam j hj La : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * _)
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ)), hinv, Matrix.one_mul]
    have key := (GlobalTheory.T.evalBasisCoords_against_blockAction (sysS H X std) D (hT.gat_pos u w hg) j h (gramC (gramN D j hj) (embT D)) (bAt J j hj La.1)
      (mM d j hj La) V z f hfz).1
    rw [key, hR f, alg z' f (fun τ => rfl)]

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivariance
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ) g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P
  by_cases hP : P.1 ∈ t.Pr.vGs
  · exact _root_.GlobalTheory.TwTop.locAt_vG A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP
  · exact _root_.GlobalTheory.TwTopQ.locq_twist A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP

end GlobalTheory.TwTop

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levAt_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU →
    ∀ i hi, i = t.m2 + 1 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hEx hMu i hi hieq _hAway
  subst hieq
  intro β β' x x' x₁ x₁' κ κ' hx hx' z
  have key : ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' → ∀ Z,
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p₁ p₁' Z) =
        muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (t.m2 + 1 + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p p' Z) := by
    intro p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    have hxi : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' Z =
        _root_.Formalism.L2.Col.XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' Z := by
      intro q q'
      unfold xiPt
      rw [dite_eq_right (by omega), if_neg (by omega)]
    have e1 := hxi p₁ p₁'
    have e2 := hxi p p'
    have e3 := _root_.GlobalTheory.TwV.PhiTLev.phiT_mul_lev A dtU a hPin hTie (t.m2 + 1) hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    simp only [e1, e2, xiTop_eq_prod, e3]
    have hC := hTie.levCpl β
    have hT2 := hTie.levTop β'
    have hLe := hC.1
    have hChi := hC.2.2
    have hLe' := hT2.1
    have hChi' := hT2.2
    have hU := (((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U_eq κ.1).1 κ.2
    have hU' := (((St (t.m2 + 1 + 1) hi).K β').lev.U_eq κ'.1).1 κ'.2
    have hov : ∀ P : SB t μ, IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      intro P
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    choose g zz hg using fun P : SB t μ => hLe P _ (hov P) κ.1 hU.1 (hU.2 _)
    choose g' zz' hg' using fun P : SB t μ => hLe' P _ (hov P) κ'.1 hU'.1 (hU'.2 _)
    have c1 := hChi κ g zz hg
    have c2 := hChi' κ' g' zz' hg'
    have hm := _root_.GlobalTheory.TwTop.muOf_det_top A dtU a hPin hTie hMu hi β β' κ κ' g zz g' zz' hg hg'
    have hprod : (∏ P, zz' P) * (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
        (∏ P, zz P) * ∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [← locAt A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P (g P) (zz P) (g' P) (zz' P)
        (hg P).1 (hg P).2 (hg' P).1 (hg' P).2 Z]
      ring
    have e := congrArg t.seam.σ₀ hprod
    simp only [map_mul] at e ⊢
    have hA : t.seam.σ₀ (∏ P, zz P) ≠ 0 := right_ne_zero_of_mul_eq_one c1
    have hB : t.seam.σ₀ (∏ P, zz' P) ≠ 0 := right_ne_zero_of_mul_eq_one c2
    apply mul_right_cancel₀ (mul_ne_zero hA hB)
    linear_combination
      (-(((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, zz P) * t.seam.σ₀ (∏ P, zz' P))) * hm +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, zz' P) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))) * c1 +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z)) * e -
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) *
        t.seam.σ₀ (∏ P, zz P)) * c2
  have h₁ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p' :=
    ⟨hEx _ _ β x₁, hEx _ _ β' x₁'⟩
  have h₀ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' :=
    ⟨hEx _ _ β x, hEx _ _ β' x'⟩
  unfold xiAd
  rw [dite_eq_left h₁, dite_eq_left h₀]
  exact key _ _ _ _ h₀.1.choose_spec h₀.2.choose_spec h₁.1.choose_spec h₁.2.choose_spec _

end GlobalTheory.TwTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleKernelEqSmulPullbackClassKernel
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem reV_pull_submatrix {D : D7} (T : TaylorLogMetric.Tor D) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    (e : Matrix (Fin N) (Fin N) D.host.E) (e' : Matrix (Fin N') (Fin N') D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    reV ha hb (TaylorLogMetric.pull D T e e' G) =
      TaylorLogMetric.pull D T (e.submatrix (Fin.cast ha) (Fin.cast ha)) (e'.submatrix (Fin.cast hb) (Fin.cast hb)) (reV ha hb G) := by
  subst ha hb
  rfl

theorem pullAt_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.PullAt S j) := by
  intro D _ _ _ _ _ _ _ _ u μ w hg Lv I H X _ std t J S hD d j hj La La' hLa hLa' z
  have hj1 : j + 1 ≤ D.R.m := hj
  have hj0 : j ≤ D.R.m := Nat.le_of_succ_le hj1
  obtain ⟨-, -, hr, -⟩ := _root_.GlobalTheory.TwV.DelB.sysS_ranks S
  rw [_root_.GlobalTheory.TwV.DelB.kerTh_pair_eq S hD j hj1 (hr j) (hr (j + 1)) La La' hLa hLa']
  have hV := _root_.GlobalTheory.TwV.SPull.kerTh_eq_pull J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj1 (clsAt X H j La.1 La.2)
    (clsAt X H (j + 1) La'.1 La'.2) (J.pt std j _ La) (J.pt std (j + 1) hj1 La') (d.gam j _ La) (d.mem j _ La)
    (d.gam (j + 1) hj1 La') (d.mem _ _ _) (d.kap j _ La) (d.kap (j + 1) hj1 La') (d.eq j _ La hLa) (d.eq _ _ La' hLa')
  have hN := (_root_.GlobalTheory.TwV.mu_det_rat_y_lev J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj (j + 1) hj1 (clsAt X H (j + 1) La'.1 La'.2)
    (J.pt std (j + 1) hj1 La') (d.gam (j + 1) hj1 La') (d.mem _ _ _) (d.kap (j + 1) hj1 La') (d.eq _ _ La' hLa')).2.2
  have e1 : d.eM j La = (gMat J j hj0 (d.gam j hj0 La)).submatrix (Fin.cast (hr j)) (Fin.cast (hr j)) := by
    unfold Dec.eM; rw [dite_eq_left ⟨hj0, hr j⟩]
  have e2 : d.eM (j + 1) La' = (gMat J (j + 1) hj1 (d.gam (j + 1) hj1 La')).submatrix (Fin.cast (hr (j + 1))) (Fin.cast (hr (j + 1))) := by
    unfold Dec.eM; rw [dite_eq_left ⟨hj1, hr (j + 1)⟩]
  have e3 : thCl (X := sysS H X std) t u μ (clsAt X H) j La La' =
      reV (hr j) (hr (j + 1)) ((t.rd u μ).Th t.seam t.amb j (clsAt X H j La.1 La.2) (clsAt X H (j + 1) La'.1 La'.2)) := by
    unfold thCl; rw [dite_eq_left ⟨hr j, hr (j + 1)⟩]
  have e4 : d.sP S j La La' = S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap j hj0 La).1) * d.chi (j + 1) hj1 La' /
      (S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap (j + 1) hj1 La').1) * d.chi j hj0 La) := by
    unfold Dec.sP; rw [dite_eq_left hj1]
  rw [e1, e2, e3, e4, ← reV_pull_submatrix]
  have key : ∀ a b c e k p : ℂ, c ≠ 0 → e ≠ 0 → c * e * k = a * b * p → k = a * b / (c * e) * p := by
    intro a b c e k p hc he h
    field_simp
    linear_combination h
  exact key _ _ _ _ _ _ hN (Units.ne_zero _)
    (hV (fun τ i k => z τ (Fin.cast (hr (j + 1)).symm i) (Fin.cast (hr j).symm k)))

end GlobalTheory.TwV.DelB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarMemAlgebraicClosure
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' ∈ TaylorLogMetric.Qbar := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hj La La' hLa hLa'
  have hjm : j < D.R.m := lt_of_lt_of_eq hj X.fl_m
  have hj' : j + 1 ≤ D.R.m := hjm
  have hχ := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).1
  have h1 : S.muT (j + 1) ((J.fd std).dt j La) ∈ TaylorLogMetric.Qbar := by
    rw [(hD j hjm.le La hLa).2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D j hjm.le _)
  have h2 : S.muT (j + 1) ((J.fd std).dt (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    rw [(hD (j + 1) hj' La' hLa').2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D (j + 1) hj' _)
  have k1 := _root_.GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN t std J hD j hjm.le La hLa
  have k2 := _root_.GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN t std J hD (j + 1) hj' La' hLa'
  exact mul_mem (mul_mem (mul_mem h2 (inv_mem h1)) (zpow_mem (hχ _ _ k1.1 k1.2) _)) (zpow_mem (hχ _ _ k2.1 k2.2) _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPowStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m), FillAt (hT := hT) (H := H) (X := X) std j hj → ∀ x ∈ U1 (sigD D), ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * ordA (A0 J) v x)) := by
  first | exact @GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos | exact GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos | (intros; apply GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos <;> assumption)
end

