module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaInnerProductEqRealTorusMean
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeanRealTorusNormalisedThetaMulConj
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCtxBase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ctx_base : ∀ (D : D7) (n p q : ℕ), ∃ (S T : HSp D) (C : Ctx S T), S.rank = 2 * n ∧ C.X.p0 = p ∧
    C.q0 = q ∧ S.SigOK ∧ T.SigOK ∧ ∃ (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (f : WO S T → ℂ),
      IdemTwo Lv.w ∧ C.IsB B ∧ C.IsBase Lv B f := by
  intro D n p q
  obtain ⟨S, T, C, h1, h2, h3, h4, h5, B, hB⟩ := exists_ctx_sig D n p q
  obtain ⟨⟨Lv, hw⟩, h6, -⟩ := GlobalTheory.Ker.Base.level_base_fam D S T C
  obtain ⟨f, hf⟩ := h6 Lv B hB
  exact ⟨S, T, C, h1, h2, h3, h4, h5, Lv, B, f, hw, hB, hf⟩

theorem inhabitants :
    (∀ (D : D7) (S T : HSp D) (p q : ℕ) (L : Lt D.host.E T.rank), S.gram = 1 → Even S.rank → p + q = T.rank →
      T.SigOK → (∀ τ, T.sig (tauE D τ) = (p, q)) → IsSelfDualC T L →
      ∃ C : Ctx S T, C.X.p0 = p ∧ C.q0 = q ∧ IsAA C.X.Λ L ∧ ∃ B : C.Bas, C.IsB B) ∧
    ∀ (D : D7) (n p q : ℕ), ∃ (S T : HSp D) (C : Ctx S T), S.rank = 2 * n ∧ C.X.p0 = p ∧ C.q0 = q ∧ S.SigOK ∧
      T.SigOK ∧ ∃ (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (f : WO S T → ℂ),
        IdemTwo Lv.w ∧ C.IsB B ∧ C.IsBase Lv B f :=
  ⟨exists_ctx, exists_ctx_base⟩

end GlobalTheory.Ker.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestFunctionOfFockVacuumThetaFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockOnto

theorem differentiable_of_fderiv_I {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Φ : V → ℂ}
    (h : Differentiable ℝ Φ) (hI : ∀ z u, fderiv ℝ Φ z (I • u) = I * fderiv ℝ Φ z u) : Differentiable ℂ Φ := by
  intro z
  have hs : ∀ (c : ℂ) (u : V), fderiv ℝ Φ z (c • u) = c * fderiv ℝ Φ z u := by
    intro c u
    have e : c • u = c.re • u + c.im • (I • u) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    rw [e, map_add (f := _), map_smul, map_smul, hI, Complex.real_smul, Complex.real_smul, ← mul_assoc, ← add_mul,
      Complex.re_add_im]
  let A : V →L[ℂ] ℂ :=
    { toFun := fderiv ℝ Φ z
      map_add' := map_add _
      map_smul' := hs
      cont := (fderiv ℝ Φ z).continuous }
  exact (hasFDerivAt_of_restrictScalars ℝ (f' := A) (h z).hasFDerivAt (by ext; rfl)).differentiableAt

variable {D : D7} {S T : HSp D}

theorem differentiable_comp {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (R : V →+ WO S T)
    (hR : Continuous R) (hr : ∀ v, IsRealPt (R v)) : Differentiable ℝ fun v => f (R v) := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  have h1 := hf.smooth _ (R.comp e.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom) (hR.comp e.symm.continuous)
    (fun t => hr _) 0
  have h2 := (h1.differentiable (by simp)).comp e.differentiable
  refine (funext fun v => ?_ : (fun v => f (R v)) = _) ▸ h2
  change f (R v) = f (0 + R (e.symm (e v)))
  rw [zero_add, e.symm_apply_apply]

theorem finW_neg_nsmul (N : ℕ) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (-(N • y)) = N • finW S T (-y) := by
  have key : ∀ {F A E : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E] (p : A) (x : E),
      p ⊗ₜ[F] (-(N • x)) = N • (p ⊗ₜ[F] (-x)) := by
    intro F A E _ _ _ _ _ p x
    rw [← smul_neg]
    exact map_nsmul (TensorProduct.mk F A E p) N (-x)
  funext a k
  exact key (pairA D.host.F 0 1) (y k a)

theorem finW_mem_hatA {A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)}
    {y : Matrix (Fin S.rank) (Fin T.rank) D.host.E} (hy : y ∈ A) : finW S T y ∈ hatA S T A :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, y, hy, rfl⟩

theorem isRealPt_sub (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    IsRealPt (S := S) (T := T) (ratW T S yᵀ - finW S T y) := by
  ext a k
  change finPart D (incA D (y k a) - (pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a) = 0
  rw [RingHom.map_sub]
  exact sub_eq_zero.2 rfl

theorem realPt_sub (C : Ctx S T) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    C.realPt (ratW T S yᵀ - finW S T y) = embR C.X y := by
  funext σ k a
  change conj (C.θ (C.m.e.symm σ) (infPart D (incA D (y k a) - (pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a))) =
    σ.1 (y k a)
  have h0 : infPart D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a) = 0 := by
    have : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a := rfl
    rw [this, TensorProduct.zero_tmul]
  have h1 : infPart D (incA D (y k a)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a := rfl
  have h2 := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at h2
  rw [RingHom.map_sub, h0, h1, sub_zero, (C.inf _).1, h2, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.Ker.FockOnto


open GlobalTheory.Ker.FockOnto in
theorem GlobalTheory.Ker.exists_test_of_fock : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ f = C.Th (C.xB B) φ := by
  intro D S T C B hB f hf hF
  obtain ⟨R, hRc, -, hadd, hR, hR', -⟩ := _root_.GlobalTheory.KerReal.real_points D S T C
  have hx : C.xB B ∈ C.X.dom := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  obtain ⟨⟨L, hL⟩, -⟩ := GlobalTheory.Ker.zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx
  have hg0 : ∀ z : Fin S.rank → Fin C.g → ℂ, gaussR C.X C.bas C.idx (C.xB B) z ≠ 0 := fun z => Complex.exp_ne_zero _
  set Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ := fun z => (gaussR C.X C.bas C.idx (C.xB B) z)⁻¹ * f (R (L.symm z))
    with hΦ
  have hd : Differentiable ℝ Φ :=
    (((RealHeis.contDiff_gaussR C.X C.bas C.idx (C.xB B)).differentiable (by simp)).inv hg0).mul
      ((differentiable_comp hf R hRc fun v => (hR v).1).comp L.symm.differentiable)
  have hv : ∀ v, f (R v) = gaussR C.X C.bas C.idx (C.xB B) (zR C.X C.idx (C.xB B) v) *
      Φ (zR C.X C.idx (C.xB B) v) := by
    intro v
    simp only [hΦ]
    rw [mul_inv_cancel_left₀ (hg0 _), ← hL, L.symm_apply_apply]
  have hw : ∀ w, IsRealPt w → f w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w) := by
    intro w hw
    rw [Ctx.zOf, ← hv, hR' w hw]
  have hone : ∀ ζ (σ : C.X.Ψ) (c : Fin S.rank → Fin T.rank → ℂ),
      fderiv ℝ Φ ζ (I • L (Pi.single σ c)) = I * fderiv ℝ Φ ζ (L (Pi.single σ c)) := by
    intro ζ σ c
    have h1 := (_root_.GlobalTheory.Ker.annih_crea_coord D S T C B hB f Φ hd hw (C.m.e.symm σ) (Matrix.of fun a k => conj (c k a))
      (L (Pi.single σ c)) (by simp [hL]) (R (L.symm ζ)) (hR _).1).1
    have h2 : C.zOf (C.xB B) (R (L.symm ζ)) = ζ := by rw [Ctx.zOf, (hR _).2, ← hL, L.apply_symm_apply]
    rw [hF, h2, Pi.zero_apply] at h1
    have h3 := (mul_eq_zero.1 h1.symm).resolve_left (hg0 _)
    linear_combination (-I) * h3 + (fderiv ℝ Φ ζ (I • L (Pi.single σ c))) * Complex.I_mul_I
  have hC : Differentiable ℂ Φ := by
    refine differentiable_of_fderiv_I hd fun ζ u => ?_
    obtain ⟨v, rfl⟩ := L.surjective u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single v, map_sum, Finset.smul_sum, map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => hone ζ σ _
  obtain ⟨-, hext, hth⟩ := _root_.GlobalTheory.ThetaSpace.theta_space_laws D S T C
  obtain ⟨-, -, -, hfin, -, N, hN, hlev⟩ := hth f hf
  obtain ⟨φ, hφ, hθ⟩ := _root_.GlobalTheory.Ker.Onto.exists_thA_eq D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx N hN
    Φ hC (by
      intro y hy v
      have h1 := hfin (-(N • y)) (R v) (hR v).1
      have h2 : embR C.X (-(N • y)) = -(N • embR C.X y) := by
        funext σ k a
        simp [embR]
      have h3 : ratW T S (-(N • y))ᵀ - finW S T (-(N • y)) = R (-(N • embR C.X y)) := by
        rw [← hR' _ (isRealPt_sub _), realPt_sub, h2]
      have h4 : EFR C.X v (-(N • embR C.X y)) = -EFR C.X v (N • embR C.X y) := by
        generalize N • embR C.X y = a
        simp only [EFR, hermC, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib, Complex.neg_re, neg_mul,
          neg_neg]
      rw [h3, finW_neg_nsmul, hlev _ (finW_mem_hatA (neg_mem ((TensLat.mem_tens_stdL _ _).2 hy))), (hR v).2, h2,
        ← map_sub, sub_neg_eq_add, h4, hv, hv] at h1
      rw [h1]
      simp)
  refine ⟨φ, hφ, (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx φ hφ).2 f ⟨hf, fun w hw' => ?_⟩⟩
  rw [hw w hw', thR, hθ, Ctx.zOf]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem bijective_aeval_scale_rename {σ σ' : Type} (e : σ ≃ σ') (c : σ → ℂ) (hc : ∀ v, c v ≠ 0) :
    Function.Bijective
      (MvPolynomial.aeval fun v => MvPolynomial.C (c v) * MvPolynomial.X (e v) :
        MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ) := by
  let F : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
    MvPolynomial.aeval fun v => MvPolynomial.C (c v) * MvPolynomial.X (e v)
  let G : MvPolynomial σ' ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
    MvPolynomial.aeval fun v => MvPolynomial.C (c (e.symm v))⁻¹ * MvPolynomial.X (e.symm v)
  have h1 : F.comp G = AlgHom.id ℂ _ := by
    ext1 v
    simp only [F, G, AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul, MvPolynomial.algHom_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply, Equiv.apply_symm_apply]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hc _), map_one, one_mul]
  have h2 : G.comp F = AlgHom.id ℂ _ := by
    ext1 v
    simp only [F, G, AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul, MvPolynomial.algHom_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply, Equiv.symm_apply_apply]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc _), map_one, one_mul]
  exact (AlgEquiv.ofAlgHom F G h1 h2).bijective

variable {D : D7} {S T : HSp D}

theorem Ctx.fockScale_pos (C : Ctx S T) (τ : D.what₂.Tau) : 0 < fockScale D τ := by
  have h0 : D.host.xi0 ≠ 0 := by
    intro h
    have h1 := C.X.κ0_sign (C.m.e τ)
    rw [C.m.ka, h] at h1
    simp at h1
  have h2 : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 h0)
  unfold fockScale
  have := Real.pi_pos
  positivity

theorem Ctx.toH_bijective (C : Ctx S T) : Function.Bijective C.toH :=
  bijective_aeval_scale_rename (C.m.e.prodCongr ((rowIdx C.hr).symm.prodCongr (Equiv.refl (Fin S.rank))))
    (fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)) fun v => by
      have := C.fockScale_pos v.1
      exact Complex.ofReal_ne_zero.2 (by positivity)

theorem fvec_Th_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), Function.Bijective C.toH ∧ ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsFock B (C.Th (C.xB B) φ) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B (C.Th (C.xB B) φ) Q 0 = thP C.X C.hr C.bas C.idx φ (C.toH Q) (C.xB B) := by
  intro D S T C
  refine ⟨C.toH_bijective, fun B hB φ hφ => ?_⟩
  have hx : C.xB B ∈ C.X.dom := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  have hZ := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx φ hφ).1
  have hd : Differentiable ℂ (thA C.X C.bas C.idx φ (C.xB B)) := fun z =>
    ((GlobalTheory.SW.theta_holomorphic_weight _ _ C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (fun _ _ => 0)
      (fun _ _ => 0) φ hφ 0 (Submodule.zero_mem _)).2.2.2 _ hx z trivial).differentiableAt
  have hG : ∀ w, IsRealPt w → C.Th (C.xB B) φ w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) *
      thA C.X C.bas C.idx φ (C.xB B) (C.zOf (C.xB B) w) := hZ.2
  refine ⟨fun τ z => ?_, fun Q => _root_.GlobalTheory.Ker.FockOrigin.fvec_zero_eq_polyDeriv D S T C B hB _ _ hd hG Q⟩
  obtain ⟨h0, h1, h2⟩ := _root_.GlobalTheory.ThetaSpace.theta_space_laws D S T C
  have hth : C.IsTh (annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z (C.Th (C.xB B) φ)) :=
    (h1 _ _ (_root_.GlobalTheory.Ker.HeisDeriv.dRho_laws D S T C _ hZ.1 τ z).1
      ((h2 _ (_root_.GlobalTheory.Ker.HeisDeriv.dRho_laws D S T C _ hZ.1 τ (cplxO 1 (C.sB B τ) z)).1).1 I)).1
  refine (h1 _ _ hth h0).2 fun w hw => ?_
  rw [(_root_.GlobalTheory.Ker.annih_crea_coord D S T C B hB _ _ (hd.restrictScalars ℝ) hG τ z _ rfl w hw).1,
    ((hd _).hasFDerivAt.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, Pi.zero_apply]
  rw [← mul_assoc I I, I_mul_I]
  ring

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InnerProductTranslatedVacuaEqGaussianKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.GaussKer

theorem EFR_sub_right {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)
    (v a b : WR X n) : EFR X v (a - b) = EFR X v a - EFR X v b := by
  simp only [EFR, hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]

theorem isRealPt_add {D : D7} {S T : HSp D} {w w' : WO S T} (h : IsRealPt w) (h' : IsRealPt w') :
    IsRealPt (w + w') := by
  unfold IsRealPt at h h' ⊢
  rw [Matrix.map_add (finPart D) (map_add _), h, h', add_zero]

theorem ipO_rho_Th : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ x₁ ∈ C.X.dom, ∀ x₂ ∈ C.X.dom, ∀ φ₁ φ₂ : TF S.rank C.g, SW.IsSB φ₁ → SW.IsSB φ₂ → ∀ w₁ w₂, IsRealPt w₁ → IsRealPt w₂ → ipO μ 𝓕 (C.rho w₁ (C.Th x₁ φ₁)) (C.rho w₂ (C.Th x₂ φ₂)) = dbl C.X C.bas C.idx φ₁ φ₂ 0 * (gaussR C.X C.bas C.idx x₁ (C.zOf x₁ w₁) * conj (gaussR C.X C.bas C.idx x₂ (C.zOf x₂ w₂)) * kZero C.X C.idx x₁ x₂ (C.zOf x₁ w₁) (fun k i => conj (C.zOf x₂ w₂ k i))) := by
  intro D S T C μ 𝓕 hF x₁ hx₁ x₂ hx₂ φ₁ φ₂ hφ₁ hφ₂ w₁ w₂ hw₁ hw₂
  obtain ⟨R, -, -, hadd, -⟩ := _root_.GlobalTheory.KerReal.real_points D S T C
  have hψ := (_root_.GlobalTheory.FormMatch.forms_match D S T C).2.1
  have hZ₁ := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C x₁ hx₁ φ₁ hφ₁).1
  have hZ₂ := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C x₂ hx₂ φ₂ hφ₂).1
  have hth := _root_.GlobalTheory.ThetaSpace.theta_space_laws D S T C
  have hT₁ : C.IsTh (C.rho w₁ (C.Th x₁ φ₁)) := (hth.2.2 _ hZ₁.1).2.1 w₁
  have hT₂ : C.IsTh (C.rho w₂ (C.Th x₂ φ₂)) := (hth.2.2 _ hZ₂.1).2.1 w₂

  have hval : ∀ (w w₀ : WO S T) (x : Frame C.X.Ψ T.rank) (φ : TF S.rank C.g), C.IsZak x φ (C.Th x φ) →
      IsRealPt w → IsRealPt w₀ → C.rho w₀ (C.Th x φ) w =
        cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w₀) : ℝ)) *
          thR C.X C.bas C.idx φ x (C.realPt w + C.realPt w₀) := by
    intro w w₀ x φ hZ hw hw₀
    simp only [Ctx.rho]
    unfold heisO
    rw [hψ w w₀ hw hw₀, hZ.2 _ (isRealPt_add hw hw₀), hadd]
  obtain ⟨N₀, hN₀, hip⟩ := _root_.GlobalTheory.Ker.TorusMean.ipO_eq_mean D S T C μ 𝓕 hF _ _ hT₁ hT₂
  obtain ⟨N₁, hN₁, hsw⟩ := _root_.GlobalTheory.Ker.Mean.mean_thR_mul_conj D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
    x₁ hx₁ x₂ hx₂ φ₁ φ₂ hφ₁ hφ₂
  obtain ⟨⟨Fd, hFd⟩, hint⟩ := hip (N₀ * N₁) (Nat.mul_pos hN₀ hN₁) (dvd_mul_right _ _)
  rw [hint Fd hFd (fun v => cexp (π * I * (EFR C.X v (C.realPt w₁ - C.realPt w₂) : ℝ)) *
    (thR C.X C.bas C.idx φ₁ x₁ (v + C.realPt w₁) * conj (thR C.X C.bas C.idx φ₂ x₂ (v + C.realPt w₂)))) ?_]
  · exact hsw (N₀ * N₁) (Nat.mul_pos hN₀ hN₁) (dvd_mul_left _ _) Fd hFd (C.realPt w₁) (C.realPt w₂)
  · intro w hw
    rw [hval w w₁ x₁ φ₁ hZ₁ hw hw₁, hval w w₂ x₂ φ₂ hZ₂ hw hw₂, EFR_sub_right, map_mul, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    have e : (π : ℂ) * I * ((EFR C.X (C.realPt w) (C.realPt w₁) - EFR C.X (C.realPt w) (C.realPt w₂) : ℝ) : ℂ) =
        π * I * (EFR C.X (C.realPt w) (C.realPt w₁) : ℂ) + π * -I * (EFR C.X (C.realPt w) (C.realPt w₂) : ℂ) := by
      push_cast; ring
    rw [e, Complex.exp_add]
    ring

end GlobalTheory.Ker.GaussKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ZakLaws

theorem embR_neg {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)
    (y : Matrix (Fin n) (Fin r) E) : embR X (-y) = -embR X y := by
  funext τ k a
  simp only [embR, Matrix.neg_apply, map_neg, Pi.neg_apply]

theorem EFR_neg_right {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)
    (v v' : WR X n) : EFR X v (-v') = -EFR X v v' := by
  unfold EFR hermC
  simp only [Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib, Complex.neg_re]

variable {D : D7} {S T : HSp D}

theorem inf_incA (C : Ctx S T) (τ : D.what₂.Tau) (e : D.host.E) :
    C.θ τ (infPart D (incA D e)) = tauE D τ e := by
  have h := (C.inf τ).1 e
  simp only [infPart, Formalism.L2.Theta.incA] at h ⊢
  exact h

theorem realPt_actO (C : Ctx S T) {ga : GL (Fin T.rank) D.host.E} {γ : GA D T} (h : IsRatOf T ga γ)
    (w : WO S T) :
    C.realPt (actO S T 1 γ w) =
      fun σ k => ((ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map σ.1) *ᵥ C.realPt w σ k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hact⟩ := _root_.GlobalTheory.KerReal.real_points D S T C
  funext σ k a
  have he : ∀ z, (σ.1 : D.host.E →+* ℂ) z = conj (tauE D (C.m.e.symm σ) z) := by
    intro z
    have hz := C.m.e_emb (C.m.e.symm σ)
    rw [Equiv.apply_symm_apply] at hz
    rw [hz, ComplexEmbedding.conjugate_coe_eq]
  have hm : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by
    simp [Formalism.L2.Theta.mt]
  have hg : Formalism.L2.Theta.mt T γ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) := h
  have h1 : compAt C.θ (C.m.e.symm σ) (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 1 := by
    ext i j
    simp [compAt, Matrix.one_apply, apply_ite]
  simp only [Ctx.realPt]
  rw [(hact 1 γ w).2.2 (C.m.e.symm σ), hm, hg, h1, Matrix.mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [compAt, Matrix.map_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    inf_incA C, he, Ctx.realPt]

end GlobalTheory.Ker.ZakLaws

namespace GlobalTheory.Ker

theorem Ctx.th_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → (∀ φ', SW.IsSB φ' → C.Th x (φ + φ') = C.Th x φ + C.Th x φ' ∧ (C.Th x φ = C.Th x φ' → φ = φ')) ∧ (∀ a : ℂ, C.Th x (a • φ) = a • C.Th x φ) ∧ (∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.rho (finW S T y) (C.Th x φ) = C.Th x (heisG C.X C.bas (-y) φ)) ∧ ∀ (ga : GL (Fin T.rank) D.host.E) (γ : GA D T), IsRatOf T ga γ → ∀ w, C.Th (lact ga x) (wG C.X C.bas C.idx ga φ) w = C.Th x φ (actO S T 1 γ⁻¹ w) := by
  intro D S T C x hx φ hφ
  obtain ⟨R, -, -, hadd, hR, -, -, hfin0, -, hact⟩ := _root_.GlobalTheory.KerReal.real_points D S T C
  have hth := _root_.GlobalTheory.ThetaSpace.theta_space_laws D S T C
  have hzak := _root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C
  have hlaws := thR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
  have hZ : C.IsZak x φ (C.Th x φ) := (hzak x hx φ hφ).1
  have huniq : ∀ ψ, SW.IsSB ψ → ∀ f, C.IsZak x ψ f → f = C.Th x ψ := fun ψ hψ => (hzak x hx ψ hψ).2
  have hsub : ∀ w u, C.realPt (w - u) = C.realPt w - C.realPt u := by
    intro w u
    have hwu := hadd (w - u) u
    rw [sub_add_cancel] at hwu
    rw [hwu, add_sub_cancel_right]
  refine ⟨fun φ' hφ' => ⟨?_, ?_⟩, fun a => ?_, fun y => ?_, fun ga γ hγ w => ?_⟩
  · have hsb := (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ' hφ hφ').1
    have hZ' := (hzak x hx φ' hφ').1
    refine (huniq _ hsb _ ⟨(hth.2.1 _ _ hZ.1 hZ'.1).1, fun w hw => ?_⟩).symm
    rw [Pi.add_apply, hZ.2 w hw, hZ'.2 w hw, ((hlaws x hx φ hφ).2.2.2.1 φ' hφ').2, Pi.add_apply]
  · intro heq
    have hZ' := (hzak x hx φ' hφ').1
    apply ((hlaws x hx φ hφ).2.2.2.1 φ' hφ').1
    funext v
    obtain ⟨hR1, hR2⟩ := hR v
    have e1 := hZ.2 (R v) hR1
    have e2 := hZ'.2 (R v) hR1
    rw [hR2] at e1 e2
    rw [← e1, ← e2, heq]
  · have hsb := (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1 a
    refine (huniq _ hsb _ ⟨(hth.2.2 _ hZ.1).1 a, fun w hw => ?_⟩).symm
    rw [Pi.smul_apply, hZ.2 w hw, (hlaws x hx φ hφ).2.2.2.2 a, Pi.smul_apply]
  · have hsb := ((heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 (-y) φ hφ).1
    refine huniq _ hsb _ ⟨(hth.2.2 _ hZ.1).2.1 _, fun w hw => ?_⟩
    obtain ⟨hrat, hfinW, hreal, -⟩ := (_root_.GlobalTheory.FormMatch.forms_match D S T C).2.2.2.2.2.2.2 y
    have hw' : IsRealPt (w - (ratW T S yᵀ - finW S T y)) := by
      unfold IsRealPt at hw hreal ⊢
      rw [Matrix.map_sub _ (map_sub (finPart D)), hw, hreal, sub_zero]
    rw [(hth.2.2 _ hZ.1).2.2.2.1 y w hw, hZ.2 _ hw', hsub, hsub, hrat, hfin0 _ hfinW, sub_zero,
      (hlaws x hx φ hφ).2.1 (-y), ZakLaws.embR_neg, ZakLaws.EFR_neg_right]
    simp only [Complex.ofReal_neg, mul_neg, neg_neg, sub_eq_add_neg]
  · have hq := (_root_.GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.1
    have hinv : IsRatOf T ga⁻¹ γ⁻¹ := (hq γ γ ga ga hγ hγ).2.1
    have hun : IsUn C.X ga := (hq γ γ ga ga hγ hγ).2.2.2.1
    have hGQ : γ⁻¹ ∈ GQ T := (hq _ _ _ _ hinv hinv).2.2.1
    have hx' : lact ga x ∈ C.X.dom := IsUn.lact_mem hun hx
    have hsbw := (wG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even ga hun φ hφ).1
    have hZw : C.IsZak (lact ga x) (wG C.X C.bas C.idx ga φ) (fun w => C.Th x φ (actO S T 1 γ⁻¹ w)) := by
      refine ⟨(hth.2.2 _ hZ.1).2.2.2.2.1 1 (one_mem _) γ⁻¹ hGQ, fun w hw => ?_⟩
      dsimp only
      have hwr : IsRealPt (actO S T 1 γ⁻¹ w) := (hact 1 γ⁻¹ w).1 hw
      rw [hZ.2 _ hwr, ZakLaws.realPt_actO C hinv w,
        ← (hlaws x hx φ hφ).2.2.1 ga hun]
      congr 1
      funext τ k
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact (congrFun ((hzak (lact ga x) hx' _ hsbw).2 _ hZw) w).symm

end GlobalTheory.Ker
end

