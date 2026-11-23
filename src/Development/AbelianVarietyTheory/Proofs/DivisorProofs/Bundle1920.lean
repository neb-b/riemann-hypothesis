module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.FlatVal

variable {D : D7} {L : SizeData₂ D}

theorem isComplexData {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) {Y : Deep T.toCore j} {e : ℕ} {o : ℝ}
    (hG : Y.Good e o) : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict := by
  have hV : Formalism.L2.Pj.FinVol (D.sp.W j) := by
    have h := hT.finVol j hj _ T.good_σ₀
    rwa [hT.spaceW j hj _ T.good_σ₀] at h
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hG.lev.1.2.1, hT.pins.2.1.1]
  refine ⟨hG.lev.2, fun σ hσ => ⟨hG.unf σ hσ, ?_, hV, hG.xiAbs σ hσ⟩⟩
  obtain ⟨th, hr, h1, h2⟩ := hG.dictU σ hσ
  exact ⟨Y.Kf, th, hr, hM ▸ hG.levelK, h1, h2⟩

theorem abs_log_sub_lrd_le {PP A M : ℝ} (h : HostNum D L PP A M) :
    |Real.log (D.host.d : ℝ) - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E| ≤ 3 * L.sc.L := by
  have hL := h.big.2.1
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast h.f8
  have h0 : 0 ≤ Real.log |(discr D.host.E : ℝ)| := by rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
    rw [rootDiscr_def, Int.cast_abs, Real.log_rpow (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero _))), h.deg]; push_cast; ring
  have h2 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E := by rw [h1]; positivity
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
    rw [h1, div_le_iff₀ (by linarith)]; linarith [h.disc]
  have h4 := Real.log_natCast_nonneg D.host.d
  exact abs_le.2 ⟨by linarith, by linarith [h.logd]⟩

theorem log_level_le (P : ParameterChoice' D L) {PP A M : ℝ} (h : HostNum D L PP A M) :
    Real.log ((LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 : ℕ) : ℝ) ≤ 40 * L.sc.L := by
  have hL := h.big.2.1
  have hc0 : (LevelStarExponents.condE D : ℝ) ≠ 0 := by
    have := (GlobalTheory.BadLog.log_level_le P).1
    exact_mod_cast left_ne_zero_of_mul (left_ne_zero_of_mul this)
  have a0 : (D.host.g 0 : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have a1 : (D.host.g 1 : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  have hc := (Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.log_cond_le P).1
  have l15 : Real.log 15 ≤ 14 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]
  push_cast
  rw [Real.log_mul (mul_ne_zero hc0 (mul_ne_zero a0 a1)) (by norm_num), Real.log_mul hc0 (mul_ne_zero a0 a1),
    Real.log_mul a0 a1]
  linarith [h.logg 0, h.logg 1]

end GlobalTheory.CovTop.FlatVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LieBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem card_frameIdx (Dw : Datum H) :
    Fintype.card (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have h := FlagTan.isHalf_psiSet H
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [h.sum_univ (fun σ => Dw.mult σ), ← h.card, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rcases FlagTan.mult_conj (Dw := Dw) τ with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
  exact add_comm _ _

theorem isSplitting_embK {l : Level H} (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => (algebraMap c.F K).comp (embK c σ) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  refine EigenSplit.isSplitting_of_isDomain (S := c.F) (σ := fun σ : E →+* ℂ => embK c σ) (fun σ σ' e => ?_)
    (NumberField.Embeddings.card E ℂ) _ (isUnit_iff_ne_zero.2 (by exact_mod_cast NumberField.discr_ne_zero E))
  have e' : embF c σ = embF c σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e
  ext x
  have := congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) e'
  exact this

theorem finrank_quot_fil (P : GlobalTheory.Published.AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {g : ℕ}
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Module.Finite K (HdR A ⧸ Fil A) ∧ Module.finrank K (HdR A ⧸ Fil A) = g := by
  obtain ⟨-, -, hfin, -, hrk⟩ := P.2.1 K A g hA hg
  have hF : Module.finrank K (PrimitiveSubmodule A) = g := by
    have := hrk ⟨⊥, Ideal.isPrime_bot⟩
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  let e : (HdR A ⧸ Fil A) ≃ₗ[K] Module.Dual K (PrimitiveSubmodule A) := Subspace.quotAnnihilatorEquiv (PrimitiveSubmodule A)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Subspace.dual_finrank_eq, hF]

theorem span_eq_top {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* K} (hχ : EigenSplit.IsSplitting χ)
    {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hub : ∀ σ k, IsTangent (ub σ k))
    (hbasis : ∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w) :
    Submodule.span K (Set.range fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)) = ⊤ := by
  let ρ : O →+* Module.End K (Serre.Lie a) := Module.toModuleEnd K (S := O) (Serre.Lie a)
  rw [eq_top_iff]
  intro x _
  rw [← EigenSplit.sum_proj hχ ρ x]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hx := EigenSplit.proj_mem hχ ρ σ x
  obtain ⟨cf, hcf⟩ := hbasis σ (EigenSplit.proj hχ ρ σ x).hom (EigenSplit.proj hχ ρ σ x).isTangent fun z =>
    congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hx z)
  have e : EigenSplit.proj hχ ρ σ x = ∑ i, cf i • Serre.Lie.mk a (ub σ i) (hub σ i) :=
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff cf (fun i => Serre.Lie.mk a (ub σ i) (hub σ i)) _).1 hcf)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, i⟩, rfl⟩)

end GlobalTheory.LieBasis

namespace GlobalTheory.LieBasis

theorem lifts_basis_mod_fil : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    (y : FrPt Xo c K) {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π →
    ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) →
    ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) →
    Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ ∧
      LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  intro P E _ _ _ H Dw l Xo c K _ _ y A _ π hπ ub hub hb hhb
  classical
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have : IsCommMonObj A := hA.comm
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  obtain ⟨ub', hub', htan, -, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  have e : ub' = ub := funext fun σ => funext fun k => Over.OverMorphism.ext
    (hπ.1.hom_ext ((hub' σ k).trans (hub σ k).symm) ((Over.w (ub' σ k)).trans (Over.w (ub σ k)).symm))
  subst e
  have L := (P.2.1 K A _ hA gA).1
  let v : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub' k.1 k.2) (htan _ _)
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    span_eq_top a (isSplitting_embK c K) ub' htan hbasis
  obtain ⟨hfin, hdim⟩ := finrank_quot_fil P hA gA
  have hcard : Fintype.card (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) = Module.finrank K (Serre.Lie a) := by
    rw [← (L.quotEquiv a).finrank_eq, hdim, card_frameIdx]
  have hind : LinearIndependent K v := linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hcard
  have hv : (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = (L.quotEquiv a).symm ∘ v := by
    funext k
    rw [Function.comp_apply, LinearEquiv.eq_symm_apply, LieExact.quotEquiv_mk, L.toLie_eq_iff]
    exact hhb k
  refine ⟨?_, hv ▸ hind.map' _ (L.quotEquiv a).symm.ker⟩
  have h1 : Submodule.map (Fil A).mkQ (Submodule.span K (Set.range hb)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span K (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = ⊤
    rw [hv, Set.range_comp, eq_top_iff]
    intro q _
    have hq : (L.quotEquiv a) q ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
    simpa using hq
  have h2 := congrArg (Submodule.comap (Fil A).mkQ) h1
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] at h2

end GlobalTheory.LieBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialIntegerExponentDegreeEq
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
namespace GlobalTheory.FrameHom

open Formalism.L2.LamCM GlobalTheory.LamT.FieldPoly

theorem prod_zpow_eq_zpow_sum {K ι : Type} [Field K] {a : K} (ha : a ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ ha]

theorem two_zpow_injective {K : Type} [Field K] [CharZero K] {m n : ℤ} (h : (2 : K) ^ m = 2 ^ n) : m = n := by
  have h' : (((2 : ℚ) ^ m : ℚ) : K) = (((2 : ℚ) ^ n : ℚ) : K) := by
    rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]; exact h
  exact (zpow_right_inj₀ (by norm_num : (0 : ℚ) < 2) (by norm_num)).1 (Rat.cast_injective h')

theorem degree_eq_of_scaling_zpow {K σ : Type} [Field K] [CharZero K] (G P : MvPolynomial σ K) (hP : P ≠ 0) (d : ℤ)
    (h : ∀ x : σ → K, MvPolynomial.eval x P ≠ 0 →
      MvPolynomial.eval (fun v => 2 * x v) G = (2 : K) ^ d * MvPolynomial.eval x G)
    (μ : σ →₀ ℕ) (hμ : AddMonoidAlgebra.coeff G μ ≠ 0) : (μ.degree : ℤ) = d := by
  have h1 : P * (MvPolynomial.aeval (fun v => MvPolynomial.C (2 : K) * MvPolynomial.X v : σ → MvPolynomial σ K) G -
      MvPolynomial.C ((2 : K) ^ d) * G) = 0 := by
    apply MvPolynomial.funext
    intro x
    by_cases hx : MvPolynomial.eval x P = 0
    · simp [hx]
    · have e : MvPolynomial.eval x
          (MvPolynomial.aeval (fun v => MvPolynomial.C (2 : K) * MvPolynomial.X v : σ → MvPolynomial σ K) G) =
          MvPolynomial.eval (fun v => 2 * x v) G := by
        clear h hμ
        induction G using MvPolynomial.induction_on with
        | C r => simp
        | add p q hp hq => simp only [map_add (f := _), hp, hq]
        | mul_X p v hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [map_mul, map_sub, e, h x hx]
      simp
  have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hP)
  have h3 := congrArg (AddMonoidAlgebra.coeff · μ) h2
  rw [coeff_aeval_scale, MvPolynomial.coeff_C_mul] at h3
  have h4 : (2 : K) ^ μ.degree = 2 ^ d := mul_right_cancel₀ hμ h3
  rw [← zpow_natCast] at h4
  exact two_zpow_injective h4

theorem frPoly_secZ_degree_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    e none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ μ, AddMonoidAlgebra.coeff G μ ≠ 0 →
        (μ.degree : ℤ) = ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k _he0 F hF G hG μ hμ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]
  have hDp : (∏ b, blockDetPoly K Dw.mult b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  refine degree_eq_of_scaling_zpow G _ hDp _ (fun x hx => ?_) μ hμ
  let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K :=
    fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
  have hX : ∀ b, (X b).det ≠ 0 := fun b => by
    have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact hx
    exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
  have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
  obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
  obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
  rw [Units.val_one] at h₁ h₂
  have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
  let t : Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some _ => Units.mk0 2 h2
  have hb : FrBor t z₁ z₂ := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => ?_, h₂⟩
    · simp [T, Matrix.transpose_apply, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
    · simp [T, t]
  have e₁ := hG z₁ X hX h₁
  have e₂ := hG z₂ (fun b' => X b' * T b')
    (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
  have e₃ := evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb
  have p₁ : ((∏ i, t i ^ e i : Kˣ) : K) = (2 : K) ^ (∑ b, ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
    rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
    simp only [t, one_zpow, Units.val_one, _root_.one_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← prod_zpow_eq_zpow_sum h2]
    exact Finset.prod_congr rfl fun b _ => prod_zpow_eq_zpow_sum h2 _ _
  have p₂ : (∏ b, (X b * T b).det ^ k b) = (2 : K) ^ (∑ b, (Dw.mult b : ℤ) * (k b : ℤ)) * ∏ b, (X b).det ^ k b := by
    rw [← prod_zpow_eq_zpow_sum h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Matrix.det_mul]
    simp only [T, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show ((Dw.mult b : ℤ) * (k b : ℤ)) = ((Dw.mult b * k b : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
    ring
  have p₃ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
    unfold evalFr
    congr 2
    funext v
    simp [X, T, Matrix.mul_diagonal, mul_comm]
  have p₄ : evalFr G X = MvPolynomial.eval x G := rfl
  rw [← p₃, ← e₂, p₂, e₃, p₁, ← p₄, ← e₁, Finset.sum_add_distrib, zpow_add₀ h2]
  ring

end GlobalTheory.FrameHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointFieldAlgebraicallyClosed
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem mem_smul_top_of_coprime {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (I J : Ideal R) (hIJ : J ⊔ I = ⊤)
    (f : N →ₗ[R] N) (h : ∀ z ∈ J • (⊤ : Submodule R N), f z ∈ I • (⊤ : Submodule R N)) (x : N) :
    f x ∈ I • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : R) ∈ J ⊔ I)
  have e : f x = f (a • x) + b • f x := by rw [map_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact add_mem (h _ (Submodule.smul_mem_smul ha Submodule.mem_top)) (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem natCast_not_isUnit {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : g.Prime) : ¬ IsUnit (g : 𝓞 K) := by
  intro hu
  have h1 := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
  have e : ((g : 𝓞 K)) = algebraMap ℤ (𝓞 K) (g : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap] at h1
  have hn : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hn, Int.isUnit_iff] at h1
  have := hg.two_le
  rcases h1 with h1 | h1 <;> omega

theorem sup_span_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    {g : ℕ} (hg : g.Prime) (hd : g ∣ l.M) : l.Mb ⊔ Ideal.span {(g : 𝓞 E)} ≠ ⊤ := by
  intro htop
  have hb : Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    have := congrArg (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E)) htop
    rwa [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_top] at this
  have hle : (⊤ : Ideal (𝓞 E)) ≤ Ideal.span {(g : 𝓞 E)} := by
    calc (⊤ : Ideal (𝓞 E)) = (l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) * (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) := by
          rw [htop, hb, Ideal.top_mul]
      _ ≤ Ideal.span {(g : 𝓞 E)} := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
          refine sup_le (sup_le ?_ (Ideal.mul_le_inf.trans inf_le_right)) (sup_le (Ideal.mul_le_inf.trans inf_le_left) (Ideal.mul_le_inf.trans inf_le_left))
          rw [Ideal.span_singleton_le_span_singleton]
          exact_mod_cast (Nat.cast_dvd_cast hd : ((g : 𝓞 E)) ∣ (l.M : 𝓞 E))
  exact natCast_not_isUnit hg (Ideal.span_singleton_eq_top.1 (top_le_iff.1 hle))

end GlobalTheory.DefFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecResidueFieldCompAutEqOfFixes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

theorem algebraMap_stalkCongr_of_eq {X : Scheme.{0}} [IsIntegral X] {x y : X} (h : x = y)
    (a : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk y) X.functionField ((X.presheaf.stalkCongr (.of_eq h)).hom a) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
  subst h
  simp

theorem fromSpecResidueField_comp_eq_of_fixes (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ]
    (ρ : Γ →* Aut X) (γ : Γ) (x : X) (hx : (ρ γ).asIso.hom x = x)
    (h : ∀ u : X.functionFieldˣ, RegAt x u → ZeroAt x ((fnAct ρ γ u : X.functionField) - u)) :
    X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x := by
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  set φ := (ρ γ).asIso.hom with hφ
  have key : (X.residueFieldCongr hx.symm).hom ≫ φ.residueFieldMap x = 𝟙 _ := by
    rw [← cancel_epi (X.residue x), Category.comp_id, X.residue_residueFieldCongr_assoc,
      Scheme.residue_residueFieldMap]
    ext a
    change IsLocalRing.residue _ (φ.stalkMap x ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom a)) =
      IsLocalRing.residue _ a
    set b := (X.presheaf.stalkCongr (.of_eq hx.symm)).hom a with hb
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    by_cases ha : a = 0
    · rw [hb, ha, map_zero, map_zero, sub_zero]
      exact zero_mem _
    · have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
      obtain ⟨c, hc, e⟩ := h (Units.mk0 _ hne) ⟨a, rfl⟩
      have e2 : ((fnAct ρ γ (Units.mk0 _ hne) : X.functionFieldˣ) : X.functionField) =
          GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) := rfl
      have e4 : GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) =
          algebraMap (X.presheaf.stalk x) X.functionField (φ.stalkMap x b) := by
        rw [← algebraMap_stalkCongr_of_eq hx.symm a, ← hb]
        exact GlobalTheory.functionFieldMap_algebraMap φ x b
      rw [e2, Units.val_mk0, e4, ← map_sub] at e
      rwa [← IsFractionRing.injective _ _ e]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← X.residueFieldCongr_fromSpecResidueField hx.symm, ← Category.assoc, ← Spec.map_comp, key,
    Spec.map_id, Category.id_comp]

end GlobalTheory.OrbitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnframePt

open GlobalTheory.RealGeo GlobalTheory.Unframe Formalism.IndefR.FWT

abbrev fullHeckeRealDatMovedReadings {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ) : RealDat3 D A3 Ks :=
  { Rl with toRealDat := moveR Rl.toRealDat w }

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def geoHalf (p : PtAt ex Csz) : GeoHalf p.T p.R.toRealDat (fun _ => 1) :=
  ⟨p.κ, p.v₀, p.fw, p.bar, p.O, p.pins, p.rhoGeo, p.equivAll, p.cTie, fun i hu => by
    have e : phEff p.R = fun _ => (1 : ℂ) := funext p.phEff_one
    rw [← e]
    exact p.phase i hu⟩

end Pt

end GlobalTheory.UnframePt
end
end

