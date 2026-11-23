module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelMetricsSemiPositive
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModelSemi

open GlobalTheory.CxPts GlobalTheory.TrueGeo.OfLattice ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem semiPos_of_isModelOf : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → L.SemiPos D := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs
  intro τ
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := ⟨_, extEmb_comp τ⟩
  let M : Matrix (Fin n) (Fin N) ℂ := fun k a => ∑ m, σ (c k m) * A σ m a
  have hz : Weight.NoCommonZero fun a =>
      ∑ j, M j a • secVal p (σ.comp (algebraMap (𝓞 K) K)) (s (gw j)) := by
    intro i y hy
    by_contra! h0
    have hS : ∑ a, ‖∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      have h1 := h0 a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [show (∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)) = 0 from h1]
      simp
    obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.bpf.ge (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ))))
    have hne := (secVal_ne_zero_iff (s w) hy).2 (mem_ptsIn.2 hw)
    have hb := _root_.GlobalTheory.frame_semilinear_sq_le K V Nm W N n b g A c gw σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hF hg hc
      (fun m β u x hx => _root_.GlobalTheory.ImageModel.valR_section_sum K V Ω Nm W ev D X p L ψ s hM hev _ i y hy m β u x hx) w
    rw [hS, mul_zero] at hb
    exact hne (by
      have : ‖valR y.1 (L.B.U i) ((s w).f i)‖ = 0 := by nlinarith [norm_nonneg (valR y.1 (L.B.U i) ((s w).f i))]
      exact norm_eq_zero.1 this)
  have key : (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ = (combWeight L.isLB (fun k => s (gw k)) M hz).φ :=
    funext fun i => funext fun y => (hφ σ i y).trans (combWeight_φ L.isLB (fun k => s (gw k)) M hz i y).symm
  intro i ch y hy ξ
  have := semiPosReg_combWeight L.isLB (fun k => s (gw k)) M hz D i ch y hy ξ
  rw [key]
  exact this

end GlobalTheory.ImageModelSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastTail
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstLin GlobalTheory.FinitePartGeneric

noncomputable section
namespace GlobalTheory.ToricTorsionSpec

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ τ : Multiplicative D.toPre.X →* Rˣ, τ ^ k = 1 → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G, s ^ k = 1 ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev₀ : R →+* V), IsLocalHom ev₀ → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf ev₀)).obj G), IsMonHom bc.hom → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (hD : IsPullDeg ev₀ D.toPre D'.toPre) (U' : Unif (maximalIdeal V) D' A' G'), IsPullUnif ev₀ hD bc U U' → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (τ' : Multiplicative D'.toPre.X →* Kˣ), (∀ χ', ((τ' χ' : Kˣ) : K) = algebraMap (FractionRing V) K (algebraMap V (FractionRing V) (ev₀ ((τ (Multiplicative.ofAdd (hD.xe (Multiplicative.toAdd χ'))) : Rˣ) : R)))) → ∀ (q : QkPt D'.toPre K k) (x' : TFK (R := V) K ⟶ A'.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU U'.toUnifPre K k q x' → x'.left ≫ genMap U' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = spMap ((algebraMap (FractionRing V) K).comp ((algebraMap V (FractionRing V)).comp ev₀)) ≫ s.left := by
  intro R _ _ _ hB G _ _ hG D A U k hk τ hτ
  obtain ⟨hR, hC⟩ := hB
  haveI := hC
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ := GlobalTheory.ToricTorsionSecUnif.exists_torsion_toG R hR G D A U k hk
  let u : D.toPre.X →+ Additive Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : k • u = 0 := by
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  obtain ⟨gT, hgT⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D.toPre) (T := 𝟙_ (Over (Sp R))) u
  obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k u hu hgT
  obtain ⟨h, hh, -⟩ := hU _ _ ⟨g', h₁, h₂⟩
  refine ⟨h ≫ x₀, by rw [← MonObj.comp_pow, htors, MonObj.comp_one], ?_⟩
  intro V _ _ _ _ hVc ev₀ hev G' _ _ bc hbc D' A' hD U' hUU' K _ _ _ τ' hτ' q x' hq htor hqx'
  have hV : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hVc⟩
  have hG' : IsSemiAbelian G' := GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (specOf ev₀) G hG)
  have hL := firstFiveLaws
  have hL2 := abelianSchemeLaws_all
  let ξ : Sp V ⟶ N.left := spMap ev₀ ≫ h.left
  have hh' : ξ ≫ N.hom = (𝟙_ (Over (Sp V))).hom ≫ spMap ev₀ := by
    simp only [ξ, Category.assoc, Over.w h]
    rfl
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp V))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh' g₀
  let x₁' : 𝟙_ (Over (Sp V)) ⟶ (Over.pullback (specOf ev₀)).obj G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp V))).hom (by rw [Category.assoc, Over.w]; exact hh'))
      (pullback.lift_snd _ _ _)
  let x₁ : 𝟙_ (Over (Sp V)) ⟶ G' := x₁' ≫ bc.inv
  have e₁ : x₁'.left ≫ pullback.fst G.hom (specOf ev₀) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = ξ ≫ x₀.left := by
    rw [Over.comp_left, Category.assoc, ← Category.assoc bc.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
      Category.id_comp, e₁]
  have gG := isGrpPullback_pullback G (spMap ev₀)
  have hk₁' : x₁' ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ spMap ev₀) ⟶ N := Over.homMk ξ hh'
    have e : pushHom gG _ x₁' = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])
  haveI : IsMonHom bc.inv := inferInstance
  have hk₁ : x₁ ^ k = 1 := by
    show (x₁' ≫ bc.inv) ^ k = 1
    rw [← MonObj.pow_comp, hk₁', MonObj.one_comp]
  have hp := isPointOf_thru hUU' hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)
  have gpg := pull_grp hD
  have hb : gp.b = 1 := Over.OverMorphism.ext (gpg.1.hom_ext (((hgp 0).1 2).trans (Eq.trans ?_ ((hgp 0).1 3).symm))
    ((Over.w _).trans (Over.w _).symm))
  swap
  · show ξ ≫ g₀.b.left = ξ ≫ (1 : N ⟶ D.toPre.P.A).left
    have e1 : h.left ≫ g₀.b.left = h.left ≫ (1 : N ⟶ D.toPre.P.A).left := by
      have t1 : gT.b.left = h.left ≫ g₀.b.left := hh.1
      have t2 : gT.b = 1 := (hgT 0).1
      have t3 : h ≫ (1 : N ⟶ D.toPre.P.A) = 1 := MonObj.comp_one h
      rw [← t1, t2, ← t3]
      rfl
    simp only [ξ, Category.assoc, e1]
  let uV : D'.toPre.X → Γ((𝟙_ (Over (Sp V))).left, ⊤)ˣ := fun y =>
    unitOn (Units.map ev₀.toMonoidHom (τ (Multiplicative.ofAdd (hD.xe y))))
  have hgpT : ∀ y, TorusVal gp y (uV y) := by
    intro y
    refine ⟨hb, corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
    have v := hgp.val_id y z hJ hJ'
    rw [GlobalTheory.TorusTorsion.val_unitGen _ _ hJ']
    generalize Geo.Tor.val (gp.s y) (𝟙 _) z J' = s at v ⊢
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at v
    rw [← v]
    have c := val_corr hJ (hh.2 (hD.xe y)) (spMap ev₀)
    have c2 := GlobalTheory.TorusTorsion.TorusVal.val_eq (hgT (hD.xe y)) (spMap ev₀) hJ
    have c3 : Geo.Tor.val (g₀.s (hD.xe y)) ξ z J = gm (spMap ev₀) z ⊤ (Additive.toMul (u (hD.xe y))) := by
      first
      | exact ((val_pull hJ _ _ _).symm.trans (c.symm.trans c2))
      | exact ((val_pull hJ _ _ _).symm.trans (c.trans c2))
      | exact (c.symm.trans c2)
      | exact (c.trans c2)
    rw [c3]
    refine Units.ext ?_
    rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
    have e := GlobalTheory.ToricTorsionSec.appTop_unitOn ev₀ (τ (Multiplicative.ofAdd (hD.xe y)))
    first
    | (simp only [uV]; rw [← e]; rfl)
    | (rw [show (uV y).val = _ from e.symm]; rfl)
    | (erw [← e]; rfl)
  let fK : V →+* K := (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V))
  let uK : D'.toPre.X →+ Additive Γ((Over.mk (spMap fK)).left, ⊤)ˣ :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ' (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  obtain ⟨gK, hgK⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D'.toPre) (T := Over.mk (spMap fK)) uK
  have hpK := GlobalTheory.ToricTorsionSec.isPullF_torusPt τ' gK hgK q.g htor
  let ρ : Over.mk (spMap fK) ⟶ 𝟙_ (Over (Sp V)) := toUnit _
  have hρ : GtPt.IsPull ρ.left gp gK := GlobalTheory.TorusTorsion.isPull_of_units ρ hgpT hgK fun χ => by
    refine (GlobalTheory.ToricTorsionSec.appTop_unitOn fK _).trans ?_
    congr 2
    refine Units.ext ?_
    have := hτ' (Multiplicative.ofAdd χ)
    simp only [toAdd_ofAdd] at this
    exact this.symm
  have hpF := GlobalTheory.ToricTorsionSec.isPullF_trans hρ hpK
  have hTF : (toUnit (TF (R := V) K)).left = 𝟙 _ ≫ ρ.left := by
    rw [Category.id_comp]
    have e₁ := Over.w (toUnit (TF (R := V) K))
    have e₂ := Over.w ρ
    simp only [Over.mk_hom] at e₁ e₂
    rw [← Category.comp_id (toUnit (TF (R := V) K)).left, ← Category.comp_id ρ.left]
    exact e₁.trans ((GlobalTheory.ToricTorsionSec.spMap_comp _ _).symm.trans e₂.symm)
  have hpF' : GtPt.IsPullF K (toUnit (TF (R := V) K)).left gp q.g := by
    rw [hTF]; exact hpF
  let yK : TFK (R := V) K ⟶ (Over.pullback (jK V)).obj G' :=
    Over.homMk (pullback.lift ((toUnit (TF (R := V) K)).left ≫ x₁.left) (jFK (R := V) K)
      (by rw [Category.assoc, Over.w x₁]; exact Over.w (toUnit (TF (R := V) K)))) (pullback.lift_snd _ _ _)
  let xF : TFK (R := V) K ⟶ A'.A := yK ≫ U'.gen.hom
  have hxF : xF.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) = (toUnit (TF (R := V) K) ≫ x₁).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hQ := qkToAkU_of_integral_torsion hL.1 V (maximalIdeal V) hV (maximalIdeal.isMaximal V).ne_top D' A' G' U' k hk
    x₁ gp hk₁ (fun e => ?_) K q xF hq hpF' hxF
  · have hEq := GlobalTheory.TorsionImage.qkToAkU_unique hL2.1 hL2.2 V (maximalIdeal V) hV D' A' G' hG' U' K k hk q x' xF hqx' hQ
    subst hEq
    have hρl : ρ.left = spMap fK := by
      have e₂ := Over.w ρ
      rw [← Category.comp_id ρ.left]
      exact e₂
    show xF.left ≫ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = _
    rw [← Category.assoc, hxF, Over.comp_left, Category.assoc, e₂, hTF, Category.id_comp, hρl, Over.comp_left]
    simp only [ξ, ← Category.assoc]
    congr 1
    rw [← GlobalTheory.ToricTorsionSec.spMap_comp]
  · let xe : Over.mk (thick V (maximalIdeal V) e) ⟶ (Over.map (thick V (maximalIdeal V) e)).obj
        (thickObj V (maximalIdeal V) e G') :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick V (maximalIdeal V) e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick V (maximalIdeal V) e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩

end GlobalTheory.ToricTorsionSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeft
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSphLeft

open GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_eq_left {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ j, ∑ l, JB j l * (xᵀ * JA * y.map c) j l := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (γ := β)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem symp_mul_left {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] (ξ : A) (JA : Matrix α α A)
    (JB : Matrix β β A) (g : Matrix α α A) (hg : gᵀ * JA * g.map c = JA) (x : Matrix α β A) :
    symp c ξ JA JB (g * x) (g * x) = symp c ξ JA JB x x := by
  have e : (g * x)ᵀ * JA * (g * x).map c = xᵀ * JA * x.map c := by
    have hm : (g * x).map c = g.map c * x.map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul]
    calc xᵀ * gᵀ * JA * (g.map c * x.map c) = xᵀ * (gᵀ * JA * g.map c) * x.map c := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_left, hTens_eq_left, e]

variable {σ : E →ₐ[F] E}

theorem vecMulVec_mem_latAtV_left {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fin d → E} (hy : y ∈ W.L)
    {z : Fin n → AE F E} (hz : z ∈ latAt X v) :
    Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i)) ∈ latAtV X W v := by
  let f : (Fin n → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i))
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun z z' => by ext i j; simp [Matrix.vecMulVec_apply, add_mul] }
  have : latAt X v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hz

theorem mul_left_inv_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {g : UA σ X.J}
    (hg : g ∈ KAt σ X v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    mat g⁻¹ * γ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => mat g⁻¹ * γ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.mul_add] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show mat g⁻¹ * (a • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (x i)) ∈ latAt X v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    have e : mat g⁻¹ * (a • incM F (Matrix.vecMulVec x y)) =
        Matrix.vecMulVec (mat g⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (x i)))
          (fun j => inclR (F := F) (AF F) (y j)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_latAtV_left X W v hy (hg.2 _ hz).2
  exact this hγ

theorem acts_vacCond_of_mem_KAt_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (k, 1)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v θ hθ k hk φ hφ φ₁ hφ₁ hAct hvac γ hγ r hr
  have hS := IsUWeilPair.isUSplitting hTr.weil'
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v φ₁ φ r h0 hφ hr
  set γ' := actAB (cA σ) (k⁻¹, (1 : UA σ G.W.J)) γ
  have eγ' : γ' = mat k⁻¹ * γ := by
    simp [γ', actAB, mat]
  have hγ' : γ' ∈ latAtV G.V' G.W v := by
    rw [eγ']; exact mul_left_inv_mem_latAtV G.V' G.W v hk hγ
  have hsym : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ' γ' =
      symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ := by
    rw [eγ']
    exact symp_mul_left (cA σ) _ _ _ (mat k⁻¹) (k⁻¹).2 γ
  have e1 : actAB (cA σ) (k, (1 : UA σ G.W.J)) γ' = γ := by
    simp only [γ', actAB]
    simp [← Matrix.mul_assoc]
  have hi := hS.impl (k, (1 : UA σ G.W.J)) γ' _ hrφ.2
  rw [e1] at hi
  rw [← hAct r hrφ, ← hi, hvac γ' hγ' r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.InertSphLeft

namespace GlobalTheory.InertSphLeft

theorem vac_fixed_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hv k hk
  obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v k hk.1
  obtain ⟨hφ₁, hact⟩ := hS _ hSB
  have h1 := acts_vacCond_of_mem_KAt_left F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB _ hφ₁ hact hvac
  obtain ⟨c, hc'⟩ := GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul F E σ B a a' G X om om' hTr v w hw θ hθ hvac _ hφ₁ h1
  rw [hc'] at hact
  have hc := GlobalTheory.T.inertPlace_latticeStabilizer_vacuumScalar_eq_one F E σ B a a' G X om om' hTr v w hw hv k hk c hact
  rwa [hc, one_smul] at hact

end GlobalTheory.InertSphLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionExtendsSemiAbelianThetaModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

theorem GlobalTheory.UPoinc.exists_endo_of_generic {Z W : Scheme.{0}} [IsIntegral W] {G : Over Z} [GrpObj G] {G₀ : Over W}
    [GrpObj G₀] (hab : IsAbelianScheme G₀) {q : W ⟶ Z} {Φ : G₀.left ⟶ G.left} (hΦ : IsGrpPullback G₀ G q Φ)
    {Ω : Type} [Field Ω] (pt : Sp Ω ⟶ W) (hd : Dense (Set.range pt)) (m : Sp Ω ⟶ Z) (hm : pt ≫ q = m)
    (hendo : ∀ f : (Over.pullback m).obj G ⟶ (Over.pullback m).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback m).map F = f)
    (f₀ : G₀ ⟶ G₀) (hf₀ : IsMonHom f₀) : ∃ F : G ⟶ G, IsMonHom F ∧ Φ ≫ F.left = f₀.left ≫ Φ := by
  have hgen := isGrpPullback_pullback G m
  have wk : pullback.fst G.hom m ≫ G.hom = (pullback.snd G.hom m ≫ pt) ≫ q := by
    rw [Category.assoc, hm, pullback.condition]
  let k : pullback G.hom m ⟶ G₀.left := hΦ.1.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pt) wk
  have hk : IsGrpPullback ((Over.pullback m).obj G) G₀ pt k :=
    hΦ.cancel (hgen.congr hm.symm (hΦ.1.lift_fst _ _ _).symm) (hΦ.1.lift_snd _ _ _)
  obtain ⟨e, he, hek⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hk f₀ hf₀
  obtain ⟨F, ⟨hF, hFe⟩, -⟩ := hendo e he
  obtain ⟨F₀, hF₀, hF₀e⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hΦ F hF
  have wθ : (pullback.fst G₀.hom pt ≫ Φ) ≫ G.hom = pullback.snd G₀.hom pt ≫ m := by
    rw [Category.assoc, hΦ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hm]
  let θ : pullback G₀.hom pt ⟶ pullback G.hom m := pullback.lift _ _ wθ
  have hθk : θ ≫ k = pullback.fst _ _ := by
    apply hΦ.1.hom_ext
    · rw [Category.assoc, hΦ.1.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hΦ.1.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.condition]
  have hFm : ((Over.pullback m).map F).left ≫ pullback.fst G.hom m = pullback.fst G.hom m ≫ F.left := by
    first | exact pullback.lift_fst _ _ _ | (simp [Over.pullback, pullback.map]) | (erw [pullback.lift_fst])
  have key : F₀ = f₀ := by
    apply _root_.GlobalTheory.abelianScheme_end_ext_of_dense W G₀ hab Ω pt hd
    apply hΦ.1.hom_ext
    · calc (pullback.fst G₀.hom pt ≫ F₀.left) ≫ Φ = pullback.fst G₀.hom pt ≫ Φ ≫ F.left := by
            rw [Category.assoc, hF₀e]
        _ = θ ≫ pullback.fst G.hom m ≫ F.left := by rw [← Category.assoc θ, pullback.lift_fst, Category.assoc]
        _ = θ ≫ e.left ≫ pullback.fst G.hom m := by rw [← hFm, hFe]
        _ = θ ≫ e.left ≫ k ≫ Φ := by rw [hΦ.1.lift_fst]
        _ = θ ≫ k ≫ f₀.left ≫ Φ := by rw [← Category.assoc e.left, hek, Category.assoc]
        _ = (pullback.fst G₀.hom pt ≫ f₀.left) ≫ Φ := by rw [← Category.assoc θ, hθk, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w F₀, Over.w f₀]
  exact ⟨F, hF, by rw [← hF₀e, key]⟩

theorem GlobalTheory.UPoinc.act_extends_ratModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ ∀ (K : Type) [Field K] (ξ₀ : Sp K ⟶ U₀.toScheme) (y : Sp K ⟶ Xo.XF c), X₁.Lies (ξ₀ ≫ out.u₀) y → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G (ξ₀ ≫ U₀.ι) γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  haveI := X₁.ar.char
  obtain ⟨hW, pt, hpt, hd⟩ := _root_.GlobalTheory.UPoinc.isIntegral_pullback_toRat X₁.o₁ X₁.Ω₁ M U₀ X₁.S.R out.u₀ hAdm.1.ne out.u₀_gen
  haveI := hW
  obtain ⟨G₁, _, α, β, hα, hβ, hL⟩ := X₁.pulled
  let s : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Sp (ratHull X₁.S.R) := pullback.snd _ _
  let G₀ : Over (pullback out.u₀ (spMap (toRat X₁.S.R))) := (Over.pullback s).obj G₁
  have h₀ : IsGrpPullback G₀ G₁ s (pullback.fst G₁.hom s) := isGrpPullback_pullback G₁ s
  let w : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Xo.XF c := s ≫ X₁.u
  have hβ₀ : IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) (pullback.fst G₁.hom s ≫ β) :=
    (h₀.comp hβ).congr (Category.assoc _ _ _).symm rfl
  obtain ⟨f₀, hf₀, hT⟩ := _root_.GlobalTheory.PullAction.exists_action_pull E H Dw l Xo c _ w G₀ _ hβ₀
  have hα₀ := h₀.comp hα
  have wψ : (pullback.fst G₁.hom s ≫ α) ≫ X₁.ρ.P.A.hom = (G₀.hom ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ≫ out.u₀ := by
    rw [hα₀.1.w, Category.assoc, pullback.condition]
  let ψ : G₀.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift _ _ wψ
  have hψ : IsGrpPullback G₀ ((Over.pullback out.u₀).obj X₁.ρ.P.A) (pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ψ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (hα₀.congr pullback.condition.symm (pullback.lift_fst _ _ _).symm)
      (pullback.lift_snd _ _ _)
  have hΦ := hψ.comp out.cart
  have hm : pt ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R)) ≫ U₀.ι = M.pt := hpt
  have hab : IsAbelianScheme G₀ := PolPull.isAbelianScheme_of_isGrpPullback X₁.ρ.P.isAb hα₀
  choose F hF hFe using fun a => exists_endo_of_generic hab hΦ pt hd M.pt hm out.endo (f₀ a) (hf₀ a).1
  refine ⟨F, hF, ?_⟩
  intro K _ ξ₀ y hLies tK ⟨mm⟩
  obtain ⟨x', hx', hxy⟩ := hLies
  let x : Sp K ⟶ pullback out.u₀ (spMap (toRat X₁.S.R)) := pullback.lift ξ₀ x' hx'.symm
  have hxw : x ≫ w = y := by
    show x ≫ pullback.snd _ _ ≫ X₁.u = y
    rw [← Category.assoc, pullback.lift_snd, hxy]
  have mm' : SABMap tK Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _) := by rw [hxw]; exact mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hact⟩ := hT (Sp K) x tK mm'
  refine ⟨γ₀ ≫ ψ ≫ out.φ, (hγ₀.comp hΦ).congr (by rw [← Category.assoc, pullback.lift_fst]) rfl, ?_, fun a => ?_⟩
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hO := out.L.isLB
    have i1 : LBIso (out.L.L.pull out.φ) (X₁.ρ.P.L.pull (pullback.fst X₁.ρ.P.A.hom out.u₀)) := ⟨out.w, out.w_gen⟩
    have i2 : LBIso (out.L.L.pull (ψ ≫ out.φ)) (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) :=
      GenSpread.lbIso_pull_comp ψ rfl (pullback.lift_fst _ _ _).symm i1
    have i3 : LBIso (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) (Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp (pullback.fst G₁.hom s) rfl rfl hL
    have i4 := LBIso.trans (pull_isLB hO _) (pull_isLB hP _) (pull_isLB hU _) i2 i3
    have i5 : LBIso (out.L.L.pull (γ₀ ≫ ψ ≫ out.φ)) (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp γ₀ rfl rfl i4
    have i6 : LBIso (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β))
        ((Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)).pull γ₀) := GenSpread.lbIso_pull_pull hU γ₀ rfl
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hO _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB hO _) i6.symm i5.symm)
  · rw [← Category.assoc, hact a, Category.assoc, Category.assoc, ← hFe a, Category.assoc]

end
end

