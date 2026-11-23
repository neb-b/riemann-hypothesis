module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameRelationIntegerExponentSectionBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FrameRelBC

open Formalism.L2.LamCM GlobalTheory.Frames GlobalTheory.LamT.FieldPoly

theorem relation_baseChange_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    e none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ (S : Type) [Field S] [Algebra c.F S] (φ : K →ₐ[c.F] S) (z z' : FrPt Xo c S)
        (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S) (s : Sˣ),
        (∀ b, (Y b).det ≠ 0) → FrMap φ y₀ z → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : S) z z' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F z' = Formalism.L2.LamCM.evalFr (MvPolynomial.map φ.toRingHom G) Y := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k he F hF G hG S _ _ φ z z' Y s hY hz hz'
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  haveI : Infinite K := inferInstance
  obtain ⟨P, N, hP⟩ := GlobalTheory.FrameDenseZ.exists_poly_div_det_secZ E H Dw l Xo c K y₀ e F hF

  have hevK : ∀ (n : (E →+* ℂ) → ℕ) (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      evalFr (∏ b, blockDetPoly K Dw.mult b ^ n b) X = ∏ b, (X b).det ^ n b := fun n X => by
    simp only [← evalFr_blockDetPoly Dw.mult _ X]
    simp only [evalFr, map_prod, map_pow]
  have hevS : ∀ (n : (E →+* ℂ) → ℕ) (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S),
      evalFr (MvPolynomial.map φ.toRingHom (∏ b, blockDetPoly K Dw.mult b ^ n b)) X = ∏ b, (X b).det ^ n b :=
    fun n X => by
    simp only [← evalFr_map_blockDetPoly φ.toRingHom Dw.mult _ X]
    simp only [evalFr, map_prod, map_pow]

  have hid : (∏ b, blockDetPoly K Dw.mult b ^ N) * G = (∏ b, blockDetPoly K Dw.mult b ^ k b) * P := by
    by_contra hne
    obtain ⟨X, hX, hX0⟩ := GlobalTheory.FrameDenseZ.exists_frame_evalFr_ne_zero Dw.mult _ (sub_ne_zero.2 hne)
    obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
      (fun b => by rw [Matrix.det_transpose]; exact (hX b).isUnit)
    rw [Units.val_one] at hy'
    have h1 := hG y' X hX hy'
    have h2 := hP K (AlgHom.id c.F K) y₀ y' X (fun b => (hX b).isUnit)
      (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K K (AlgHom.id c.F K) y₀).2.1 hy'
    rw [show (AlgHom.id c.F K).toRingHom = RingHom.id K from rfl, MvPolynomial.map_id] at h2
    apply hX0
    have e1 : evalFr ((∏ b, blockDetPoly K Dw.mult b ^ N) * G - (∏ b, blockDetPoly K Dw.mult b ^ k b) * P) X
        = evalFr (∏ b, blockDetPoly K Dw.mult b ^ N) X * evalFr G X
          - evalFr (∏ b, blockDetPoly K Dw.mult b ^ k b) X * evalFr P X := by
      simp only [evalFr, map_mul, map_sub]
    rw [e1, hevK, hevK, ← h1, ← h2, Finset.prod_pow]
    ring

  have hidS : (∏ b, (Y b).det ^ N) * evalFr (MvPolynomial.map φ.toRingHom G) Y
      = (∏ b, (Y b).det ^ k b) * evalFr (MvPolynomial.map φ.toRingHom P) Y := by
    have h := congrArg (fun Q => evalFr (MvPolynomial.map φ.toRingHom Q) Y) hid
    rw [← hevS, ← hevS]
    simpa only [evalFr, map_mul] using h

  have hYt : ∀ b, IsUnit ((Y b).transpose.det) := fun b => by
    rw [Matrix.det_transpose]; exact (hY b).isUnit
  obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (Y b).transpose) 1 hYt
  obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z1 (fun _ => 1) s (fun _ => by simp)
  have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
  have e' : z2 = z' := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (Y b).transpose) s hYt).unique h3 hz'
  subst e'
  let t : Formalism.L2.Pj.Ix Dw → Sˣ := fun i => match i with
    | none => s
    | some _ => 1
  have hb : FrBor t z1 z2 := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S z1 z2 z2).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF S t z1 z2 hb
  have ht1 : ((∏ i, t i ^ e i : Sˣ) : S) = 1 := by
    simp [Fintype.prod_option, t, he]
  rw [ht1, _root_.one_mul] at hw
  have hv := hP S φ z z1 Y (fun b => (hY b).isUnit) hz h1
  rw [hw]
  have hu : (∏ b, (Y b).det ^ N) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hY b)
  apply mul_left_cancel₀ hu
  rw [hidS, ← hv, Finset.prod_pow]
  ring

end GlobalTheory.FrameRelBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorEqIntegralFrameTangentOnModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameVector_eq_integralFrameTangent_on_model : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ → ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y → ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (w : epsOver T.V T.V ⟶ G.G) (u' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ w.left → ∀ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v = GlobalTheory.FlagMod.frVec Y y rfl τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro y x e G t' m1 m2 ψ ρ hρ0 hρh hρm τ i w u' hu1 hu2 v hv
  have hb : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2,
      Category.assoc, Over.w]
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) = _
    rw [spMap_comp', spMap_comp', dualMap_comp_alg]
  refine ((GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ⟨u' ≫ ρ, ?_, ?_, ?_⟩).symm
  · rw [Category.assoc, hρh, ← Category.assoc, hb]
  · rw [Category.assoc, hρ0, hu1]
  · rw [Category.assoc, hρm, ← Category.assoc, hu2,
      GlobalTheory.FlagMod.tanPull_left (algebraMap T.V T.Fr) e v, Category.assoc, hv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorsEqEigenFrameMulInvertible
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open Matrix

theorem frVec_eq_eigFrame_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (b : A.B) (S₀ : Type) [CommRing S₀] [Algebra c.F S₀] (P₀ : FrPt Xo c S₀), ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V → ∀ σ : E →+* ℂ, ∃ T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S₀, IsUnit T.det ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S₀ →ₐ[c.F] S') (P' : FrPt Xo c S'), FrMap ψ P₀ P' → ∀ (h' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).V) (hM' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).M.U) (j : Fin (Dw.mult σ)), frVec Y P' rfl σ j = vec (A.k b).M.toMChart _ hM' (fun r => ((((A.k b).u σ).map (ev _ _ h')) * T.map ψ) r j) := by
  intro E _ _ _ H Dw l Xo c Y p A b S₀ _ _ P₀ h σ
  have hM : ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h
  set U := ((A.k b).u σ).map (ev (frX P₀ ≫ Y.j) _ h) with hUdef
  set W := ((A.k b).w σ).map (ev (frX P₀ ≫ Y.j) _ h) with hWdef
  have hWU : W * U = 1 := by
    rw [hUdef, hWdef, ← Matrix.map_mul, (A.k b).wu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfix : ∀ v : Fin (A.k b).M.n → S₀, vec (A.k b).M.toMChart _ hM v ∈ eigLie c (frX P₀ ≫ Y.j) σ →
      U *ᵥ (W *ᵥ v) = v := by
    intro v hv
    obtain ⟨a, ha⟩ := ((A.k b).fix_iff σ _ h hM v).1
      (((LowRank.pm_gen p (A.k b).M.toMChart σ (frX_snd P₀) hM).1 v).1 ((vec_mem_eigLie _ _ hM σ v).1 hv))
    rw [← ha, Matrix.mulVec_mulVec (M := W) (N := U), hWU, Matrix.one_mulVec]
  have hspan := LowRank.initSpan_frVec_top P₀ (A.k b).M.toMChart hM σ
  have hmem : ∀ j, frVec Y P₀ rfl σ j ∈ eigLie c (frX P₀ ≫ Y.j) σ := fun j => by
    rw [← hspan]
    exact Submodule.subset_span ⟨j, j.isLt, rfl⟩
  let cv : Fin (Dw.mult σ) → Fin (A.k b).M.n → S₀ := fun j => (vec (A.k b).M.toMChart _ hM).symm (frVec Y P₀ rfl σ j)
  have hcvv : ∀ j, vec (A.k b).M.toMChart _ hM (cv j) = frVec Y P₀ rfl σ j := fun j =>
    LinearEquiv.apply_symm_apply _ _
  have hcv : ∀ j, U *ᵥ (W *ᵥ cv j) = cv j := fun j => hfix _ (by rw [hcvv]; exact hmem j)
  let C : Matrix (Fin (A.k b).M.n) (Fin (Dw.mult σ)) S₀ := Matrix.of fun i j => cv j i
  have hUT : U * (W * C) = C := by
    ext i j
    have := congrFun (hcv j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, C, Matrix.of_apply]
    exact this
  refine ⟨W * C, ?_, ?_⟩
  · have hcol : ∀ r, vec (A.k b).M.toMChart _ hM (U *ᵥ Pi.single r 1) ∈ eigLie c (frX P₀ ≫ Y.j) σ := fun r =>
      (vec_mem_eigLie _ _ hM σ _).2 (((LowRank.pm_gen p (A.k b).M.toMChart σ (frX_snd P₀) hM).1 _).2
        (((A.k b).fix_iff σ _ h hM _).2 ⟨_, rfl⟩))
    have hc : ∀ r, ∃ a : Fin (Dw.mult σ) → S₀, ∑ j, a j • cv j = U *ᵥ Pi.single r 1 := fun r => by
      have := hcol r
      rw [← hspan, mem_initSpan] at this
      obtain ⟨a, -, ha⟩ := this
      refine ⟨a, (vec (A.k b).M.toMChart _ hM).injective ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← ha]
      simp only [map_smul, hcvv]
    choose a ha using hc
    have hCT : C * Matrix.of (fun j r => a r j) = U := by
      ext i r
      have := congrFun (ha r) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at this
      simp only [Matrix.mul_apply, C, Matrix.of_apply]
      rw [Matrix.col_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h1 : W * C * Matrix.of (fun j r => a r j) = 1 := by rw [Matrix.mul_assoc, hCT, hWU]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact IsUnit.of_mul_eq_one _ h2
  · intro S' _ _ ψ P' hP h' hM' j
    have e : spMap ψ.toRingHom ≫ (frX P₀ ≫ Y.j) = frX P' ≫ Y.j := by rw [← Category.assoc, frX_frMap hP]
    rw [← tanPull_frVec hP rfl rfl e σ j, ← hcvv j, tanPull_vec (A.k b).M.toMChart ψ.toRingHom e hM hM']
    congr 1
    funext i
    have hev : ((A.k b).u σ).map (ev (frX P' ≫ Y.j) _ h') = U.map ψ := by
      ext r s
      simp only [Matrix.map_apply, hUdef]
      rw [ev_congr e.symm _ h' (e ▸ h'), ev_spMap ψ.toRingHom _ _ h]
      rfl
    have hm : U.map ψ * (W * C).map ψ = (U * (W * C)).map ψ := (Matrix.map_mul (f := (ψ : S₀ →+* S'))).symm
    rw [hev, hm, hUT]
    rfl

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullMulVec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl.TwistExp

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

theorem full_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    d.full σ S *ᵥ x = d.full σ 0 *ᵥ x + fun i => Sum.elim (0 : Fin g' → ℂ) (S *ᵥ tP σ x) (σ i) := by
  ext i
  simp only [CD.full, Matrix.submatrix_mulVec_equiv, Function.comp_apply, Pi.add_apply, Matrix.fromBlocks_mulVec]
  rcases h : σ i with j | j
  · simp [tP]
  · simp [tP, Matrix.add_mulVec, add_assoc]
    rfl

theorem leftComponent_fullMatrix_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    zP σ (d.full σ S *ᵥ x) = zP σ (d.full σ 0 *ᵥ x) := by
  rw [full_mulVec]; ext i; simp [zP]

theorem secondBlock_full_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    tP σ (d.full σ S *ᵥ x) = tP σ (d.full σ 0 *ᵥ x) + S *ᵥ tP σ x := by
  rw [full_mulVec]; ext i; simp [tP]

theorem dot_full (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    x ⬝ᵥ d.full σ S *ᵥ x = x ⬝ᵥ d.full σ 0 *ᵥ x + tP σ x ⬝ᵥ S *ᵥ tP σ x := by
  rw [full_mulVec, dotProduct_add]
  congr 1
  simp only [dotProduct]
  rw [← σ.symm.sum_comp, Fintype.sum_sum_type]
  simp [tP]

theorem co_form {k : ℕ} (β : N.Form k) (x y : N.X) :
    co bX x ⬝ᵥ bmat bX β *ᵥ co bX y = (β.be x y : ℂ) := by
  conv_rhs => rw [← bX.sum_repr x, ← bX.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, co, bmat,
    Matrix.of_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring

theorem co_sum (σ : Fin g ≃ Fin g' ⊕ Fin r) (Nn : Fin g → ℤ) :
    co bX (∑ l, tP σ Nn l • bX l) = tP σ (cv Nn) := by
  ext l; simp [co, tP, cv, Finsupp.single_apply]

end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl.TwistExp
open GlobalTheory.MBLow.Cl.TwistExp

theorem main_eq {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (k m : ℕ) (β : N.Form k) (hm : 1 ≤ m) (hk : m ^ 2 ∣ k) (w : ℂ) (M Nn : Fin g → ℤ)
    (χ : N.X) (Z : Fin g → ℂ) :
    d.term σ (w • bmat bX β) m M Nn χ Z = d.term σ 0 m M Nn χ Z * Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) ^
      (β.be ((∑ l, tP σ Nn l • bX l) + m • χ) ((∑ l, tP σ Nn l • bX l) + m • χ) / (2 * m ^ 2)).toNat := by
  set S := w • bmat bX β with hS
  have hz : ∀ S' : Matrix (Fin r) (Fin r) ℂ, zP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ S') M Nn) =
      zP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ 0) M Nn) := fun S' => by
    ext i
    have := congrFun (leftComponent_fullMatrix_mulVec d σ S' (cv Nn)) i
    simp only [zP, perV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
  have ht : tP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ S) M Nn) =
      tP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ 0) M Nn) + (m:ℂ)⁻¹ • (S *ᵥ tP σ (cv Nn)) := by
    ext i
    have := congrFun (secondBlock_full_mulVec d σ S (cv Nn)) i
    simp only [tP, perV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  unfold CD.term trFac CD.fj
  rw [hz S, ht, dot_full d σ S (cv Nn)]

  set y : N.X := ∑ l, tP σ Nn l • bX l with hy
  have hn : tP σ (cv Nn) = co bX y := (co_sum σ Nn).symm
  have hSv : ∀ u v : Fin r → ℂ, ∀ x x' : N.X, u = co bX x → v = co bX x' → u ⬝ᵥ S *ᵥ v = w * (β.be x x' : ℂ) := by
    intro u v x x' hu hv
    rw [hS, Matrix.smul_mulVec, dotProduct_smul, hu, hv, co_form, smul_eq_mul]
  have h1 := hSv _ _ y y hn hn
  have h2 := hSv _ _ χ χ rfl rfl
  have h3 := hSv _ _ χ y rfl hn
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hsymm : β.be y χ = β.be χ y := β.symm y χ
  have hα : β.be (y + m • χ) (y + m • χ) = β.be y y + 2 * m * β.be χ y + m ^ 2 * β.be χ χ := by
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hsymm]; ring
  have hdvd : (2 * m ^ 2 : ℤ) ∣ β.be (y + m • χ) (y + m • χ) :=
    (mul_dvd_mul_left 2 (by exact_mod_cast hk)).trans (β.dvd _ _)
  have hnn : 0 ≤ β.be (y + m • χ) (y + m • χ) := by
    by_cases h0 : y + m • χ = 0
    · rw [h0]; simp
    · exact (β.pos _ h0).le
  have hK : (((β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat : ℕ) : ℂ) =
      ((β.be y y : ℂ) + 2 * m * β.be χ y + m ^ 2 * β.be χ χ) / (2 * m ^ 2) := by
    obtain ⟨q, hq⟩ := hdvd
    have hm2 : (2 * m ^ 2 : ℤ) ≠ 0 := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq] at hnn
      have hp : (0:ℤ) < 2 * m ^ 2 := by positivity
      by_contra hc; push_neg at hc
      have := mul_neg_of_pos_of_neg hp hc; linarith
    rw [hq, Int.mul_ediv_cancel_left _ hm2]
    have : ((q.toNat : ℕ) : ℂ) = (q : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hq0
    rw [this, eq_div_iff (by simpa using hm0)]
    have hc : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℂ) = ((2 * m ^ 2 * q : ℤ) : ℂ) := by rw [hq]
    rw [hα] at hc; push_cast at hc; linear_combination -hc
  have key : ∀ a b a' b' f t : ℂ, a + b = a' + b' + f →
      Complex.exp a * (Complex.exp b * t) = Complex.exp a' * (Complex.exp b' * t) * Complex.exp f := by
    intro a b a' b' f t h
    have : Complex.exp a * Complex.exp b = Complex.exp a' * Complex.exp b' * Complex.exp f := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination t * this
  rw [← Complex.exp_nat_mul]
  refine key _ _ _ _ _ _ ?_
  simp only [Matrix.add_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, add_zero, Matrix.zero_mulVec,
    dotProduct_zero, h1, h2, h3, hK]
  field_simp
  ring

end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl.TwistExp

theorem term_differentiable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (m : ℕ) (M Nn : Fin g → ℤ) (χ : N.X) :
    Differentiable ℂ (d.term σ S m M Nn χ) := by
  have hθ := (thetaChar_entire_ne_zero_automorphy g' d.τ d.a d.b d.symm d.pos d.ha d.hb).1
  have hzP : Differentiable ℂ (fun Z : Fin g → ℂ => zP σ Z) := differentiable_pi.2 fun i => differentiable_apply _
  have htP : Differentiable ℂ (fun Z : Fin g → ℂ => tP σ Z) := differentiable_pi.2 fun i => differentiable_apply _
  have hdot : ∀ {n : Type} [Fintype n] (v : n → ℂ), Differentiable ℂ (fun Z : n → ℂ => v ⬝ᵥ Z) := by
    intro n _ v
    simp only [dotProduct]
    fun_prop
  have haff : Differentiable ℂ (fun Z : Fin g → ℂ => (m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) := by fun_prop
  unfold CD.term trFac CD.fj
  have e1 : Differentiable ℂ (fun Z : Fin g → ℂ => thetaChar d.τ d.a d.b
      (zP σ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) + d.t12 *ᵥ co bX χ)) :=
    hθ.comp ((hzP.comp haff).add_const _)
  have e2 : Differentiable ℂ (fun Z : Fin g → ℂ => co bX χ ⬝ᵥ (tP σ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) + d.b2)) :=
    by have := (hdot (co bX χ)).comp ((htP.comp haff).add_const d.b2); exact this
  have e3 : Differentiable ℂ (fun Z : Fin g → ℂ => cv Nn ⬝ᵥ Z) := hdot _
  refine Differentiable.mul ?_ (Differentiable.mul ?_ e1)
  · fun_prop
  · fun_prop
end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl

theorem term_smul_bmat : AllCD fun {N} {g'} {r} {g} {bX} d σ => (∀ S m M Nn χ, Differentiable ℂ (d.term σ S m M Nn χ)) ∧ ∀ (k m : ℕ) (β : N.Form k), 1 ≤ m → m ^ 2 ∣ k → ∀ (w : ℂ) (M Nn : Fin g → ℤ) (χ : N.X) (Z : Fin g → ℂ), d.term σ (w • bmat bX β) m M Nn χ Z = d.term σ 0 m M Nn χ Z * Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) ^ (β.be ((∑ l, tP σ Nn l • bX l) + m • χ) ((∑ l, tP σ Nn l • bX l) + m • χ) / (2 * m ^ 2)).toNat := by
  intro N g' r g bX d σ
  exact ⟨fun S m M Nn χ => TwistExp.term_differentiable d σ S m M Nn χ,
    fun k m β hm hk w M Nn χ Z => TwistExp.main_eq d σ k m β hm hk w M Nn χ Z⟩

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreComponentClosureOpenIsIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_open_compactOf_isIntegral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ V : (gen Y).Opens, (V : Set (gen Y)) = compactOf Y U ∧ IsIntegral V.toScheme := by
  intro E _ _ _ H D l Xo c O _ β Y U hn _ hU
  have hint := isIntegral_open_of_geometricallyConnected E H D l Xo c U hU
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsReduced (gen Y) := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have := Y.jQ_open
  have hop : IsOpen (compactOf Y U) := GlobalTheory.FlatRow.isOpen_closure_of_isOpen_components
    (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z))
    (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)
  have hUirr : IsIrreducible (U : Set (Xo.XF c)) :=
    isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hirr : IsIrreducible (compactOf Y U) :=
    (hUirr.image _ Y.jQ.continuous.continuousOn).closure
  let V : (gen Y).Opens := ⟨compactOf Y U, hop⟩
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  exact ⟨V, rfl, isIntegral_of_irreducibleSpace_of_isReduced _⟩

end GlobalTheory.DetLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericThetaExpansionScalarNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericThetaExpansion_scalar_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := by
  first | exact @GlobalTheory.KeyScalarNe.scalar_ne_zero | exact GlobalTheory.KeyScalarNe.scalar_ne_zero | (intros; apply GlobalTheory.KeyScalarNe.scalar_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM.ProjExt

theorem eq_pt_of_secCoord {o : Type} [CommRing o] {m : ℕ} {A : Type} [CommRing A] (c : o →+* A)
    (y : Sp A ⟶ PSpace o m) (hy : y ≫ PSpace.str o m = spMap c) (v : Fin (m + 1) → A)
    (h : SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v) :
    ∃ hv : Ideal.span (Set.range v) = ⊤, y = GlobalTheory.ProjSpace.pt c v hv := by
  have h1 := (RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) (𝟙 _) y v).2
    (by rwa [Category.comp_id])
  obtain ⟨hv, e⟩ := (ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c y (by rwa [Category.comp_id]) v).1 h1
  exact ⟨hv, (Category.comp_id _).symm.trans e⟩

end GlobalTheory.ZM.ProjExt
end

