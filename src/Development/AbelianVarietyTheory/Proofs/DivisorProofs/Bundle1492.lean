module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesDivJacobianIndependent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanJac

theorem derivation_eq_zero {F N : Type} [Field F] [NumberField F] [AddCommGroup N] [Module F N]
    (δ : Derivation ℤ F N) (a : F) : δ a = 0 := by
  haveI : Algebra.FormallyEtale ℤ ℚ := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  rw [← δ.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D ℤ F a) 0,
    map_zero]

theorem snd_eq_zero {F K : Type} [Field F] [NumberField F] [Field K] (χ : F →+* DualNumber K)
    (a : F) : (χ a).snd = 0 := by
  letI : Module F K := ((TrivSqZeroExt.fstHom K K K).toRingHom.comp χ).toModule
  let δ : Derivation ℤ F K := Derivation.mk'
    { toFun := fun x => (χ x).snd
      map_add' := fun x y => by rw [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun n x => by
        rw [map_zsmul, TrivSqZeroExt.snd_smul]
        rfl }
    (fun x y => by
      change (χ (x * y)).snd = (χ x).fst * (χ y).snd + (χ y).fst * (χ x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, mul_comm (χ x).snd])
  exact derivation_eq_zero δ a

theorem exists_forms_map {k A K : Type} [CommRing k] [CommRing A] [Field K] {D : ℕ}
    (α : k →+* A) (ψ : A →+* K) (φ : Fin D → A →+* DualNumber K)
    (hφ : ∀ b x, (φ b x).fst = ψ x) (hc : ∀ b a, (φ b (α a)).snd = 0) :
    ∃ Λ : Forms α D →ₛₗ[ψ] K,
      ∀ f, Λ (dForm α f) = (Matrix.of fun a b => (φ b (f a)).snd).det := by
  letI := α.toAlgebra
  letI := ψ.toAlgebra
  letI : Algebra k K := (ψ.comp α).toAlgebra
  haveI : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let δ (f : A) : Fin D → K := fun b => (φ b f).snd
  have hmul (f g : A) : δ (f * g) = f • δ g + g • δ f := by
    funext b
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    simp only [δ, map_mul, TrivSqZeroExt.snd_mul, hφ, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    change _ = ψ f * _ + ψ g * _
    ring
  have hδc (a : k) : δ (algebraMap k A a) = 0 := funext fun b => hc b a
  let d : Derivation k A (Fin D → K) := Derivation.mk'
    { toFun := δ
      map_add' := fun f g => by
        funext b
        simp only [δ, map_add (f := _), TrivSqZeroExt.snd_add, Pi.add_apply]
      map_smul' := fun a f => by
        rw [Algebra.smul_def, hmul, hδc, smul_zero, add_zero, algebraMap_smul]
        rfl } hmul
  let det : (Fin D → K) [⋀^Fin D]→ₗ[A] K :=
    { (Matrix.detRowAlternating (n := Fin D) (R := K)).toMultilinearMap.restrictScalars A with
      map_eq_zero_of_eq' := (Matrix.detRowAlternating (n := Fin D) (R := K)).map_eq_zero_of_eq }
  let Λ := exteriorPower.alternatingMapLinearEquiv (det.compLinearMap d.liftKaehlerDifferential)
  refine ⟨⟨Λ.toAddHom, Λ.map_smul⟩, fun f => ?_⟩
  refine (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans ?_
  simp only [AlternatingMap.compLinearMap_apply, Derivation.liftKaehlerDifferential_comp_D]
  rfl

end GlobalTheory.TanJac

namespace GlobalTheory.TanJac

theorem det_mul_jacobian_comm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι)
    (w : Fin (dimFlag Dw) → (Sp (DualNumber K) ⟶ M.X))
    (hw : ∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z)
    (O O' : M.X.Opens) (hO : O ≤ M.K.bundle.U i) (hO' : O' ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (g' : Fin (dimFlag Dw) → Γ(M.X, O'))
    (hz : ⊤ ≤ z ⁻¹ᵁ O) (hz' : ⊤ ≤ z ⁻¹ᵁ O') (hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O) (hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O'), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det * evalPt z O' hz' (M.K.jacobian i hO' g') =
      (Matrix.of fun a b => (evalPt (w b) O' (hwO' b) (g' a)).snd).det * evalPt z O hz (M.K.jacobian i hO g) := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ z i w hw O O' hO hO' g g' hz hz' hwO hwO'
  let x0 := z.base (IsLocalRing.closedPoint K)
  have hx0 : x0 ∈ O ⊓ O' := ⟨hz (Set.mem_univ _), hz' (Set.mem_univ _)⟩
  obtain ⟨V, hV, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hx0
  have hV' : IsAffineOpen V := hV
  have hVO : V ≤ O := hVle.trans inf_le_left
  have hVO' : V ≤ O' := hVle.trans inf_le_right
  have hzV : ⊤ ≤ z ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (z ⁻¹ᵁ V)).1 hxV).ge
  have hwV : ∀ b, ⊤ ≤ w b ⁻¹ᵁ V := fun b =>
    GlobalTheory.CompHS.le_preimage_of_dualNumber _ (w b) V (by rw [hw b]; exact hzV)
  have hfst : ∀ b f, (evalPt (w b) V (hwV b) f).fst = evalPt z V hzV f := by
    intro b f
    have e := evalPt_spMap_comp (TrivSqZeroExt.fstHom K K K).toRingHom (w b) V (hwV b)
      (by rw [hw b]; exact hzV) f
    have e' : ∀ (x : Sp K ⟶ M.X) (_ : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = x)
        (h₁ : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) ⁻¹ᵁ V) (h₂ : ⊤ ≤ x ⁻¹ᵁ V),
        evalPt (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) V h₁ f = evalPt x V h₂ f := by
      rintro x rfl h₁ h₂
      rfl
    rw [← e' z (hw b) (by rw [hw b]; exact hzV) hzV, e]
    rfl
  obtain ⟨Λ, hΛ⟩ := exists_forms_map (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str V) (evalPt z V hzV)
    (fun b => evalPt (w b) V (hwV b)) hfst
    (fun b a => snd_eq_zero ((evalPt (w b) V (hwV b)).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str V)) a)
  have hVi : V ≤ M.K.bundle.U i := hVO.trans hO
  have key : ∀ (P : M.X.Opens) (hP : P ≤ M.K.bundle.U i) (hVP : V ≤ P)
      (f : Fin (dimFlag Dw) → Γ(M.X, P)) (hzP : ⊤ ≤ z ⁻¹ᵁ P) (hwP : ∀ b, ⊤ ≤ w b ⁻¹ᵁ P),
      (Matrix.of fun a b => (evalPt (w b) P (hwP b) (f a)).snd).det =
        evalPt z P hzP (M.K.jacobian i hP f) * Λ (resForm hVi (M.K.om i)) := by
    intro P hP hVP f hzP hwP
    have e := congrArg Λ (M.K.jacobian_smul_om i hV' hVi (fun a => resG M.X hVP (f a)))
    have e1 : Λ (dOn M.str (fun a => resG M.X hVP (f a))) =
        (Matrix.of fun a b => (evalPt (w b) V (hwV b) (resG M.X hVP (f a))).snd).det :=
      hΛ (fun a => resG M.X hVP (f a))
    have e2 : Λ (M.K.jacobian i hVi (fun a => resG M.X hVP (f a)) • resForm hVi (M.K.om i)) =
        evalPt z V hzV (M.K.jacobian i hVi (fun a => resG M.X hVP (f a))) *
          Λ (resForm hVi (M.K.om i)) :=
      Λ.map_smulₛₗ _ _
    rw [← evalPt_res z hVP hzP hzV, GlobalTheory.CanonLB.resG_jacobian, ← e2, e, e1]
    congr 1
    ext a b
    exact (congrArg TrivSqZeroExt.snd (evalPt_res (w b) hVP (hwP b) (hwV b) (f a))).symm
  have alg : ∀ (d d' A B C : K), d = A * C → d' = B * C → d * B = d' * A := by
    intro d d' A B C h h'
    rw [h, h']
    ring
  exact alg _ _ _ _ _ (key O hO hVO g hz hwO) (key O' hO' hVO' g' hz' hwO')

end GlobalTheory.TanJac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralEqNonzeroMulDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegelUnfold

open MeasureTheory


set_option maxHeartbeats 1000000 in
theorem diag_theta_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ S T JA JB ξ hJA hJB κ _ co hrat ν 𝓕 hν μ hμ
  letI mV : MeasurableSpace (κ → AF D.host.F) := borel _
  haveI : BorelSpace (κ → AF D.host.F) := ⟨rfl⟩
  letI mVV : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  have hψc : IsCharAF D.host.F ψ := hψ.1
  obtain ⟨lam, 𝓖, hlam, h𝓖, -, htr⟩ := GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar D S T κ co.e (GlobalTheory.T.ratDarbouxCoords_rationalMatrix_iff_ratPair D S T κ co.e hrat) ν 𝓕 hν
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain D.host.F κ μ hμ
  obtain ⟨c₁, hc₁, hiter⟩ := GlobalTheory.T.integral_ratPairFundamentalDomain_adelic_iterated D.host.F κ μ hμ lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ htop
  have hpos : 0 < μ.real 𝓕₁ := ENNReal.toReal_pos h0 htop
  refine ⟨((c₁ * μ.real 𝓕₁ : ℝ) : ℂ), Complex.ofReal_ne_zero.mpr (mul_pos hc₁ hpos).ne', fun Φ hΦ => ?_⟩

  set G : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ := fun p =>
    GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) Φ) with hGdef
  have hdiag : ∀ w, GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ (GlobalTheory.DiagSiegel.diagMat w) =
      G (co.e w) := by
    intro w
    have h1 : (GlobalTheory.DblSchr.ddr co).e (GlobalTheory.DiagSiegel.diagMat w) =
        (Sum.elim (co.e w).1 (co.e w).1, Sum.elim (co.e w).2 (-(co.e w).2)) := by
      rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e]
      have h2 : (GlobalTheory.DiagSiegel.diagMat w).submatrix id finSumFinEquiv.symm.symm = Matrix.fromCols w w := by
        ext i j
        simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_apply_apply, id]
      rw [h2]
      rfl
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, h1, hGdef]

  obtain ⟨B, hB⟩ := _root_.GlobalTheory.UniformTranslateBound.tsum_norm_translate_le D.host.F (κ ⊕ κ) Φ hΦ
  have hsumΦ : ∀ z : κ ⊕ κ → AF D.host.F, Summable fun ξ : κ ⊕ κ → D.host.F =>
      ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + z)‖ := fun z => by
    have h1 := GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F z hΦ)
    exact h1
  have hGbd : ∃ B : ℝ, ∀ w, ‖G w‖ ≤ B := by
    refine ⟨B, fun w => ?_⟩
    have hn : ∀ ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ =
        ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ := by
      intro ξ
      simp only [GlobalTheory.WeilM.schr, norm_mul, hψc.2.1, one_mul]
    have hs : Summable fun ξ : κ ⊕ κ → D.host.F => ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := by
      simp_rw [hn]
      exact hsumΦ _
    calc ‖G w‖ ≤ ∑' ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
          (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' ξ : κ ⊕ κ → D.host.F, ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ :=
          tsum_congr hn
      _ ≤ B := hB _
  have hGm : Measurable G := by
    letI mW : MeasurableSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := borel _
    haveI : BorelSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := ⟨rfl⟩
    have hm := GlobalTheory.ThetaTransformMeas.main D.host.F ψ hψc (κ ⊕ κ) Φ hΦ
    have hc : Continuous fun p : (κ → AF D.host.F) × (κ → AF D.host.F) =>
        ((Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) : (κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := by
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_) <;> rcases i with i | i
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_snd
      · exact ((continuous_apply i).comp continuous_snd).neg
    exact hm.comp hc.measurable
  have hGper : ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, ∀ w, G (γ + w) = G w :=
    fun γ hγ w => _root_.GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv D.host.F ψ hψc κ Φ γ hγ w

  set h : (κ → AF D.host.F) → ℂ := fun u => Φ (Sum.elim u u) with hhdef
  have hcont : Continuous h :=
    (GlobalTheory.ThetaUnfold.schA_continuous D.host.F hΦ).comp
      (continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i)
  have hhbd : ∃ B : ℝ, ∀ x : κ → AF D.host.F, Summable (fun η : κ → D.host.F =>
      ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖) ∧
      ∑' η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ ≤ B := by
    refine ⟨B, fun x => ?_⟩
    have hj : Function.Injective fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F) := by
      intro η η' e
      funext i
      exact congrFun e (Sum.inl i)
    have key : ∀ η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ =
        ((fun ξ : κ ⊕ κ → D.host.F => ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim x x)‖) ∘
          fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F)) η := by
      intro η
      simp only [hhdef, Function.comp_apply]
      congr 2
      funext i
      rcases i with i | i <;> rfl
    simp_rw [key]
    exact ⟨(hsumΦ _).comp_injective hj,
      (tsum_comp_le_tsum_of_inj (hsumΦ _) (fun _ => norm_nonneg _) hj).trans (hB _)⟩
  have hinner : ∀ x, ∫ y in 𝓕₁, G (x, y) ∂μ = (μ.real 𝓕₁ : ℂ) *
      ∑' η : κ → D.host.F, h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x) := by
    intro x
    exact GlobalTheory.T.integral_diagonalTheta_secondVariable_diagonal D.host.F ψ hψc κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ x
  calc GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ)
      = ∫ w in 𝓕, G (co.e w) ∂ν := by
        unfold GlobalTheory.DiagSiegel.thetaDiagInt
        simp_rw [hdiag]
    _ = ∫ p in 𝓖, G p ∂lam := htr G
    _ = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := hiter G hGm hGper hGbd
    _ = c₁ * ((μ.real 𝓕₁ : ℂ) * ∫ u, h u ∂μ) := by
        simp_rw [hinner]
        rw [integral_const_mul, GlobalTheory.T.integral_fundamentalDomain_tsum_rationalTranslates D.host.F κ μ hμ 𝓕₁ h𝓕₁ htop h hcont hhbd]
    _ = ((c₁ * μ.real 𝓕₁ : ℝ) : ℂ) * GlobalTheory.DiagSiegel.diagInt μ Φ := by
        push_cast
        rw [mul_assoc]
        rfl

end GlobalTheory.DiagSiegelUnfold

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroTangentOfJacobianDerivsVanish
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TopForm

theorem derivation_eq_zero_of_jacobian {k B F : Type} [CommRing k] [CommRing B] [Field F]
    {D : ℕ} {α : k →+* B} (hα : α.IsStandardSmoothOfRelativeDimension D) {ω : Forms α D}
    (hω : IsFreeGen B ω) (g : Fin D → B) {J : B} (hJ : J • ω = dForm α g) (φ : B →+* F)
    (hJ0 : φ J ≠ 0) (δ : B → F) (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hmul : ∀ x y, δ (x * y) = φ x * δ y + φ y * δ x) (hc : ∀ c, δ (α c) = 0)
    (hg : ∀ a, δ (g a) = 0) (b : B) : δ b = 0 := by
  classical
  letI := α.toAlgebra
  letI : Algebra B F := φ.toAlgebra
  letI : Algebra k F := (φ.comp α).toAlgebra
  haveI : IsScalarTower k B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial B := φ.domain_nontrivial
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k B := hα
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D (R := k) (S := B)
  have hr : Module.finrank B Ω[B⁄k] = D := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := B) D)
  let e := Module.finBasisOfFinrankEq B Ω[B⁄k] hr
  let δ' : Derivation k B F := Derivation.mk'
    { toFun := δ
      map_add' := hadd
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, hmul]
        rw [show δ (algebraMap k B c) = 0 from hc c, mul_zero, add_zero, Algebra.smul_def]
        rfl }
    (fun x y => hmul x y)
  let ℓ := δ'.liftKaehlerDifferential
  have hℓ (x : B) : ℓ (KaehlerDifferential.D k B x) = δ x :=
    Derivation.liftKaehlerDifferential_comp_D δ' x
  let m : Matrix (Fin D) (Fin D) B := Matrix.of fun a c => e.repr (KaehlerDifferential.D k B (g a)) c
  have hsum (a : Fin D) : KaehlerDifferential.D k B (g a) = ∑ c, m a c • e c :=
    (e.sum_repr _).symm
  obtain ⟨c, hc'⟩ := hω.2 (exteriorPower.ιMulti B D e)
  have h1 : dForm α g = m.det • exteriorPower.ιMulti B D e := by
    rw [dForm_eq, ← alternating_map_sum_smul_eq_det_smul]
    exact congrArg _ (funext hsum)
  have h2 : J = m.det * c := by
    apply hω.1
    change J • ω = (m.det * c) • ω
    rw [hJ, h1, mul_smul]
    exact congrArg _ hc'.symm
  have h3 : (φ.mapMatrix m).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    exact hJ0 (by rw [h2, map_mul, h0, zero_mul])
  have h4 : (φ.mapMatrix m).mulVec (fun c => ℓ (e c)) = 0 := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hg a, ← hℓ, hsum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  have h5 := Matrix.eq_zero_of_mulVec_eq_zero h3 h4
  have h6 : ℓ = 0 := e.ext fun c => congrFun h5 c
  rw [← hℓ, h6, LinearMap.zero_apply]

end GlobalTheory.TopForm

namespace GlobalTheory.CanonLB

open TopForm
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem spMap_fst_surjective_field (F : Type) [Field F] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom F F F).toRingHom) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal F) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem eq_zero_tangent_of_jacobian {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}
    {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type}
    [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i) (g : Fin D → Γ(Y, K.bundle.U i))
    (hJ : evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0) (w : Sp (DualNumber F) ⟶ Y)
    (hw : ⊤ ≤ w ⁻¹ᵁ K.bundle.U i)
    (hfst : spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ w = z)
    (hp : w ≫ p = spMap (TrivSqZeroExt.inlHom F F) ≫ z ≫ p)
    (hg : ∀ a, (evalPt w _ hw (g a)).snd = 0) : w = spMap (TrivSqZeroExt.inlHom F F) ≫ z := by
  classical
  have hU : IsAffineOpen (K.bundle.U i) := K.affine i
  haveI : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  let y0 : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  have hx : z y0 ∈ K.bundle.U i := hz (Set.mem_univ y0)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨K.bundle.U i, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, K.bundle.U i)), z y0 ∈ Y.basicOpen (t : Γ(Y, K.bundle.U i)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hU).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hU (t : Γ(Y, K.bundle.U i))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, K.bundle.U i))))
  have hVU : Y.basicOpen (t : Γ(Y, K.bundle.U i)) ≤ K.bundle.U i := Y.basicOpen_le _
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, K.bundle.U i)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p hVU]
    exact h₁
  have hV : IsAffineOpen (Y.basicOpen (t : Γ(Y, K.bundle.U i))) := hU.basicOpen _
  generalize Y.basicOpen (t : Γ(Y, K.bundle.U i)) = V at hxt hVU h₂ hV
  have hzV : ⊤ ≤ z ⁻¹ᵁ V := fun y _ => by
    obtain rfl : y = y0 := Subsingleton.elim _ _
    exact hxt
  have hwV : ⊤ ≤ w ⁻¹ᵁ V := fun y _ => by
    obtain ⟨y', rfl⟩ := spMap_fst_surjective_field F y
    have := hzV (Set.mem_univ y')
    rw [← hfst] at this
    exact this
  have hinlV : ⊤ ≤ (spMap (TrivSqZeroExt.inlHom F F) ≫ z) ⁻¹ᵁ V := fun y _ =>
    hzV (Set.mem_univ _)
  have key : ∀ (y : Sp F ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ V),
      spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ w = y →
      ∀ b, (evalPt w V hwV b).fst = evalPt y V hy b := by
    rintro y hy rfl b
    exact (evalPt_spMap_comp _ w V hwV hy b).symm
  have hfstV := key z hzV hfst
  have hconst (c : k) : (evalPt w V hwV (algX p V c)).snd = 0 := by
    have e1 : evalPt w V hwV (algX p V c) = evalPt (w ≫ p) ⊤ le_rfl
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) := evalPt_constFn p w V hwV c
    have key2 : ∀ (q : Sp (DualNumber F) ⟶ Sp k), q = spMap (TrivSqZeroExt.inlHom F F) ≫ z ≫ p →
        (evalPt q ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)).snd = 0 := by
      rintro q rfl
      rw [evalPt_spMap_comp _ (z ≫ p) ⊤ le_rfl le_rfl]
      simp
    rw [e1]
    exact key2 _ hp
  have hJV : evalPt z V hzV (K.jacobian i hVU fun a => resG Y hVU (g a)) ≠ 0 := by
    rw [show (K.jacobian i hVU fun a => resG Y hVU (g a)) =
        resG Y hVU (K.jacobian i le_rfl g) from (K.resG_jacobian i le_rfl hVU g).symm,
      evalPt_res z hVU hz hzV]
    exact hJ
  have hδ := derivation_eq_zero_of_jacobian h₂ ((K.isFrame i).res hV hVU).gen
    (fun a => resG Y hVU (g a)) (K.jacobian_smul_om i hV hVU _) (evalPt z V hzV) hJV
    (fun b => (evalPt w V hwV b).snd) (fun x y => by simp)
    (fun x y => by
      simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, hfstV]
      ring)
    hconst (fun a => by rw [evalPt_res w hVU hw hwV]; exact hg a)
  refine ext_evalPt hV hwV hinlV (RingHom.ext fun b => ?_)
  rw [evalPt_spMap_comp _ z V hzV hinlV]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [hfstV]
    rfl
  · rw [hδ b]
    rfl

end GlobalTheory.CanonLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProducStatement
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_character_good_idempotent_cuspidal_product' : ∀ (D : D7) [Fintype (G0g D.nd)], (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∃ θ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GL (Fin D.R.r) (ZMod (D.host.g kv.1)) → ℂ, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩; GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (θ kv)) ∧ ∀ g, χ g = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv (g kv) := by
  first | exact @GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product | exact GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product | (intros; apply GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product <;> assumption)
end

