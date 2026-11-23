module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionsExtendGermRingsAndSpanFibres
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOfSameRatios

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOrigin
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanRed
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem comp_gtφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A) (hb : ρ ≫ b = b') (χ : D.X) (k : Fin 4) :
    ρ.left ≫ DegPre.gtφT D T b χ k = DegPre.gtφT D T' b' χ k := by
  subst hb
  fin_cases k
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D T χ) b).trans
      (congrArg (· * (ρ ≫ b)) (comp_cP D ρ χ)))
  · exact congrArg (fun q => q.left) (comp_cP D ρ χ)
  · rfl
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one ρ)

theorem val_eq_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y Y' : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {ψ : K → (Y ⟶ B₀)} {ψ' : K → (Y' ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {u : LB.Gen (LB.LinComb M₀ ψ ε)} {u' : LB.Gen (LB.LinComb M₀ ψ' ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (hu : u.IsGen) (hu' : u'.IsGen) {h : Sp A ⟶ Y} {h' : Sp A' ⟶ Y'} (H : GenRelR w t (LB.pullGen _ _ _ u h))
    (H' : GenRelR w t' (LB.pullGen _ _ _ u' h')) (q : Sp A ⟶ Sp A') (hq : ∀ k, q ≫ pt' k = pt k)
    {Z : Scheme.{0}} (r : Z ⟶ Sp A) (z : Z)
    (hv : ∀ J, Good M₀ z J → val u' ((r ≫ q) ≫ h') z J = val u (r ≫ h) z J) {J'} (hJ' : Good M z J') :
    val t' (r ≫ q) z J' = val t r z J' := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists M₀ hM₀ z
  have hw' := (isGen_iff w).1 hw
  have e := CubTransport.val_pmaps (fun k => (H.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (pullGen_isGen _ _ _ _ hu h) H) r hJ hJ'
  have e' := CubTransport.val_pmaps (fun k => (H'.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht' (pullGen_isGen _ _ _ _ hu' h') H') (r ≫ q) hJ hJ'
  rw [val_pull hJ, Category.comp_id] at e e'
  rw [hv J hJ, e] at e'
  simp only [Category.assoc r q, hq] at e'
  exact (mul_left_cancel e').symm

theorem corr_pull_of_valR {A F : Type} [CommRing A] [IsLocalRing A] [Field F] (p : A →+* F) [IsLocalHom p]
    {B : Scheme.{0}} {M : LB B} (hM : M.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp A ⟶ B)} (t : LB.Gen (LB.LinComb M pt ε)) (t' : LB.Gen (LB.LinComb M pt' ε))
    (hp : ∀ k, spMap p ≫ pt' k = pt k)
    (hv : ∀ j, ⊤ ≤ LB.wchart M pt' j → p (valR (𝟙 (Sp A)) (LB.wchart M pt' j) (t'.s j).val) =
      valR (𝟙 (Sp F)) (LB.wchart M pt j) (t.s j).val) :
    LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ t' (spMap p)) t := by
  refine corr_of_val hM fun y J hJ => ?_
  obtain rfl : y = cpt F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hc : spMap p (cpt F) = cpt A := IsLocalRing.comap_closedPoint p
  rw [val_pull hJ, Category.id_comp, val_of t' _ _ J (fun k => J (pt k)) (fun k => by rw [hp]),
    val_of t _ _ J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  have m : ⊤ ≤ (𝟙 (Sp F)) ⁻¹ᵁ LB.wchart M pt (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => hJ (pt k))
  have m' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M pt' (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => by
      have := hJ (pt k)
      rw [← hc]
      exact (congrArg (fun q => q (cpt F) ∈ M.U (J (pt k))) (hp k)).mpr this)
  have m'' := FormalValue.top_le_comp m' (spMap p)
  have e := FormalValue.valR_spMap p _ _ m' (t'.s (fun k => J (pt k))).val
  rw [Category.comp_id] at m'' e
  refine Units.ext ?_
  exact (toStkA_valR _ _ _ m'' _).symm.trans ((congrArg _ (e.trans (hv _ m'))).trans (toStkA_valR _ _ _ m _))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (Ξ : ConstPts W Λ) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v.left = (Ξ.x 0).left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ g h z₀ ν Ξ v g₁ hd ht hf
  haveI := isLocalRing_dual ℂ
  haveI := isLocalRing_dual ℂ⟦X⟧
  let p : DualNumber ℂ⟦X⟧ →+* ℂ⟦X⟧ := (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom
  let p₀ : DualNumber ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  haveI : IsLocalHom p₀ := ⟨fun x hx => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hx⟩
  obtain ⟨h₁, h₂, -⟩ := hd
  have h₁' := h₁.1
  simp only [map_zero] at h₁' h₂
  have sq : spMap p ≫ spMap constEps = spMap (PowerSeries.C (R := ℂ)) ≫ spMap p₀ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun x => fst_dualMapR _ x)
  let ρ₀ : TF (R := ℂ) ℂ ⟶ epsR ℂ := Over.homMk (spMap p₀) (by
    show spMap p₀ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap (FractionRing ℂ) ℂ) ≫ spMap (algebraMap ℂ (FractionRing ℂ))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl)
  let ρ : selfR ⟶ epsR ℂ⟦X⟧ := Over.homMk (spMap p) (by
    show spMap p ≫ spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)
  have hb₀ : ρ₀ ≫ ν.b = (Λ.ex0 0).b := Over.OverMorphism.ext h₁'
  have hb : ρ ≫ g₁.b = (Ξ.g 0).b := Over.OverMorphism.ext (W.spec.1.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (spMap p ≫ ·) ((ht 0).1 2)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ν.b.left) sq).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) h₁').trans ((Ξ.g_rel 0 0).1 2).symm))))))
    ((Over.w _).trans (Over.w _).symm))
  have hc : ∀ x, LB.Gen.Corr a.D₀.P.L _ _ _ _ (LB.pullGen a.D₀.P.L _ _ (ν.s x) (spMap p₀)) ((Λ.ex0 0).s x) :=
    fun x => corr_pull_of_valR p₀ a.D₀.P.isLB _ _ (comp_gtφT a.D₀ ρ₀ ν.b _ hb₀ x) fun j hj =>
      (congrArg p₀ (h₂ x j hj)).trans ((TrivSqZeroExt.fst_add _ _).trans (add_zero _))
  have hv : ∀ y (Z : Scheme.{0}) (r : Z ⟶ Sp ℂ⟦X⟧) (z : Z) J', Good W.P.D.toPre.P.L z J' →
      val (g₁.s y) (r ≫ spMap p) z J' = val ((Ξ.g 0).s y) r z J' := fun y Z r z J' hJ' => by
    obtain ⟨x, rfl⟩ := W.e.surjective y
    refine val_eq_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g 0).isGen _) (g₁.isGen _)
      ((Λ.ex0 0).isGen x) (ν.isGen x) (Ξ.g_rel 0 x) (ht x) (spMap p) (comp_gtφT W.P.D.toPre ρ g₁.b _ hb _) r z
      (fun J hJ => ?_) hJ'
    have e : (r ≫ spMap p) ≫ spMap constEps = (r ≫ spMap (PowerSeries.C (R := ℂ))) ≫ spMap p₀ := by
      rw [Category.assoc, sq, Category.assoc]
    exact (congrArg (fun q => val (ν.s x) q z J) e).trans ((val_pull hJ _ _ _).symm.trans (val_corr hJ (hc x) _))
  let I : Ideal ℂ⟦X⟧ := (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
  haveI : IsAdicComplete I ℂ⟦X⟧ := by
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine hom_ext_of_isHausdorff I fun e => ?_
  obtain ⟨xe, hxe⟩ := FormalValue.exists_lift_thick (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}) W.t.G
    (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (ρ ≫ v).left (Over.w (ρ ≫ v)) e
  have hs : spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) = adicLevelι I (e + 1) ≫ spMap p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hk : idealEps ^ (e + 1) ≤ RingHom.ker ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) := fun s hs => by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (mem_idealEps_pow hs).1
  have H₁ := hf.hasCoords _ hk (xe := xe) (hxe.trans (by rw [hs, Category.assoc]; rfl))
  rw [hs] at H₁
  obtain ⟨k₁, k₂⟩ := (FormalPoint.hasCoords_iff W.P.U.toUnifPre e g₁ _ xe).1 H₁.2
  have H₂ : FormalPoint.HasCoords W.P.U.toUnifPre e (Ξ.g 0) (adicLevelι I (e + 1)) xe :=
    (FormalPoint.hasCoords_iff W.P.U.toUnifPre e _ _ xe).2
      ⟨k₁.trans ((Category.assoc _ _ _).trans (congrArg (fun q => adicLevelι I (e + 1) ≫ q.left) hb)),
        fun y z J hJ => (k₂ y z J hJ).trans (hv y _ _ z J hJ)⟩
  exact hxe.symm.trans ((Ξ.x_pt 0).comp_fstG_eq H₂)

end GlobalTheory.ConstTanRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfMulEventually
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ.AnFrEx

theorem eq_zero_of_mul_eventually {g : ℕ} (θ φ : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : ∃ z, θ z ≠ 0)
    (hφ : ContinuousAt φ 0) (h : ∀ᶠ z in nhds 0, θ z * φ z = 0) : φ 0 = 0 := by
  by_contra h0
  obtain ⟨z₀, hz₀⟩ := hne
  have h1 : ∀ᶠ z in nhds (0 : Fin g → ℂ), θ z = 0 := by
    filter_upwards [h, hφ.eventually_ne h0] with z a b
    exact (mul_eq_zero.1 a).resolve_right b
  have hl : Differentiable ℂ (fun t : ℂ => t • z₀) := differentiable_id.smul_const z₀
  have ht : Filter.Tendsto (fun t : ℂ => t • z₀) (nhds 0) (nhds 0) := by
    have := hl.continuous.tendsto 0
    simpa using this
  have han : AnalyticOnNhd ℂ (fun t : ℂ => θ (t • z₀)) Set.univ := fun t _ => (hθ.comp hl).analyticAt t
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (ht.eventually h1) (Set.mem_univ 1)
  exact hz₀ (by simpa using this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem isOpen_ex {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) (V : Xo.univ.t.G.left.Opens) :
    IsOpen {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ V} := by
  have h := ((F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1
  have h2 := h.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
  convert h2 using 1
  ext z
  simp

theorem gen_unique (hT : Out.SecTwistSt) {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P)
    (θ : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : ∃ z, θ z ≠ 0) (κ : ℂ) (hκ : κ ≠ 0)
    (fr fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (hf : IsThetaFrameAt Xo.univ.t.PP (F.u k P) (fun w => (F.ex k P w).left) θ fr)
    (hf' : IsThetaFrameAt Xo.univ.t.PP (F.u k P) (fun w => (F.ex k P w).left) θ fr')
    (s s' : LB.Sec (PPx (F.u k P))) (hs : GlobalTheory.Frames.SecGen (F.u k P) s)
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx (F.u k P)), pt ≫ Formalism.L2.PjFree.gxFst (F.u k P) = (F.ex k P z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (F.u k P) = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (F.u k P)).U (fun _ => j)) (s.f (fun _ => j)) = κ * θ z * fr j z)
    (hv' : ∀ j z (pt : Sp ℂ ⟶ Gx (F.u k P)), pt ≫ Formalism.L2.PjFree.gxFst (F.u k P) = (F.ex k P z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (F.u k P) = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (F.u k P)).U (fun _ => j)) (s'.f (fun _ => j)) = κ * θ z * fr' j z) :
    ∀ i, s'.f i = s.f i := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo (F.u k P) s
  obtain ⟨a, ha, -⟩ := hs s'
  have hw : ∀ z, (F.ex k P z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ F.u k P := fun z =>
    (Over.w (F.ex k P z)).trans (Category.id_comp _).symm
  obtain ⟨j, hj⟩ := GlobalTheory.FrameUnif.ThetaPtEx.exists_chart_top Xo.univ.t.PP.isLB (F.ex k P 0).left
  have hn : {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} ∈ nhds (0 : Fin g → ℂ) :=
    (isOpen_ex F k P hP _).mem_nhds hj
  have key : fr' j 0 - a * fr j 0 = 0 := by
    refine eq_zero_of_mul_eventually θ (fun z => fr' j z - a * fr j z) hθ hne
      (((hf'.1 j).differentiableAt hn).continuousAt.sub
        (continuousAt_const.mul ((hf.1 j).differentiableAt hn).continuousAt)) ?_
    filter_upwards [hn] with z hz
    let pt : Sp ℂ ⟶ Gx (F.u k P) :=
      pullback.lift (f := (Over.mk (F.u k P)).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (F.ex k P z).left (hw z).symm
    have p1 : pt ≫ Formalism.L2.PjFree.gxFst (F.u k P) = (F.ex k P z).left := pullback.lift_snd _ _ _
    have p2 : pt ≫ Formalism.L2.PjFree.gxSnd (F.u k P) = 𝟙 (Sp ℂ) := pullback.lift_fst _ _ _
    have e' := (congrArg (valAt' pt ((PPx (F.u k P)).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt p2)
    rw [hv j z pt p1 p2 hz, hv' j z pt p1 p2 hz] at e'
    refine mul_left_cancel₀ hκ ?_
    linear_combination e'
  have h00 : fr' j 0 = fr j 0 := (hf'.2.2.2.1 j hj).trans (hf.2.2.2.1 j hj).symm
  have ha1 : a = 1 := by
    refine mul_right_cancel₀ (hf.2.1 j 0 hj) ?_
    rw [h00] at key
    linear_combination -key
  refine h3 s' fun i pt hp => ?_
  have e' := (congrArg (valAt' pt ((PPx (F.u k P)).U i)) (ha i)).trans (h1 a _ pt hp)
  rw [e', ha1, one_mul]

theorem sum_single_of_support {J : Type} {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : J, Fin (m τ)) (τ : J)
    (v : Fin g → ℂ) (hv : ∀ jj, v jj ≠ 0 → (e jj).1 = τ) :
    ∑ k : Fin (m τ), v (e.symm ⟨τ, k⟩) • (Pi.single (e.symm ⟨τ, k⟩) 1 : Fin g → ℂ) = v := by
  funext jj
  rw [Finset.sum_apply]
  by_cases h : (e jj).1 = τ
  · obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective jj
    obtain rfl : τ' = τ := by simpa using h
    rw [Finset.sum_eq_single k (fun b _ hb => ?_) (by simp)]
    · simp
    · have : e.symm ⟨τ', k⟩ ≠ e.symm ⟨τ', b⟩ := fun hh => hb (by simpa using (e.symm.injective hh).symm)
      simp [Pi.single_eq_of_ne this]
  · have h0 : v jj = 0 := by_contra fun h' => h (hv jj h')
    rw [h0]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : jj ≠ e.symm ⟨τ, b⟩ := fun hh => h (by rw [hh]; simp)
    simp [Pi.single_eq_of_ne this]

theorem isUnit_det_of_support {J : Type} {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : J, Fin (m τ)) (τ : J)
    (v : Fin (m τ) → Fin g → ℂ) (hl : LinearIndependent ℂ v) (hv : ∀ i jj, v i jj ≠ 0 → (e jj).1 = τ) :
    IsUnit (Matrix.of fun i k : Fin (m τ) => v i (e.symm ⟨τ, k⟩)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
  rw [Fintype.linearIndependent_iff] at hl ⊢
  intro cf hc
  refine hl cf (funext fun jj => ?_)
  by_cases h : (e jj).1 = τ
  · obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective jj
    obtain rfl : τ' = τ := by simpa using h
    have := congrFun hc k
    simpa [Finset.sum_apply, Matrix.row] using this
  · rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have h0 : v b jj = 0 := by_contra fun h' => h (hv b jj h')
    simp [h0]

theorem existsUnique_anFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ w : ℂ, Ha.T < w.im → ∃! y, AnFr Ha Θ z w y := by
  intro _ L2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha th Θ z _ hz w hw
  have hT := L2.secTwist
  have hP := Ha.period w hw
  obtain ⟨hsym, hpos⟩ := Θ.pos w hw
  obtain ⟨hd, w₀, hw₀⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero Uw.g Θ.c₁ Θ.c₂ Θ.half₁ Θ.half₂).1 _ hsym hpos
  have hθd : Differentiable ℂ (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) :=
    hd.comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Θ.h)).differentiable
  have hθ : ∃ v, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v) ≠ 0 := by
    refine ⟨∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)), ?_⟩
    have : Θ.h.mulVec (∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = w₀ := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' w₀).symm
    rwa [this]
  obtain ⟨-, hder, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Uw.F Ha.i _ hP
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨u, hu, htan, heig, hbas⟩ := GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ Uw.g Uw.e Uw.F Ha.i _ hP
    obtain ⟨fr, hfr⟩ := Θ.frame w hw
    obtain ⟨s, hs⟩ := hfr.2.2.2.2
    obtain ⟨t, ht, hval⟩ := GlobalTheory.FrameUnif.ThetaPtEx.exists_gen hT (Uw.F.u Ha.i (Ha.Pw w)) (Uw.F.ex Ha.i (Ha.Pw w))
      (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) fr Θ.κ Θ.κ_ne hθ hfr.2.1 s hs
    let y₀ : FrPt Xo c (CAt σ) := ⟨Uw.F.u Ha.i (Ha.Pw w), Uw.F.over_σ _ _ hP, u, htan, heig, hbas, t, ht⟩
    have hch := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c (CAt σ) y₀
    obtain ⟨⟨x', xo', u', tan', eig', basis', s', gen'⟩, ⟨hx, hc, -⟩, -⟩ :=
      hch (fun τ => (Matrix.of fun i k : Fin (Dw.mult τ) => z τ i (Uw.e.symm ⟨τ, k⟩) : Matrix _ _ ℂ)) 1
        (fun τ => isUnit_det_of_support Uw.e τ (z τ) (hz τ).1 (hz τ).2)
    dsimp only [y₀] at hx hc
    subst hx
    refine ⟨⟨Uw.F.u Ha.i (Ha.Pw w), xo', u', tan', eig', basis', t, ht⟩, ⟨rfl, fun τ i => ?_⟩, fr, hfr, hval⟩
    have := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F Ha.i _ hP _ (u τ) _ (hu τ)
      (fun k => z τ i (Uw.e.symm ⟨τ, k⟩)) (u' τ i)).1 (hc τ i)
    rwa [sum_single_of_support Uw.e τ (z τ i) ((hz τ).2 i)] at this
  · rintro ⟨x, xo, u, tan, eig, basis, s, gen⟩ ⟨x', xo', u', tan', eig', basis', s', gen'⟩
      ⟨⟨hx, hu⟩, fr, hfr, hs⟩ ⟨⟨hx', hu'⟩, fr', hfr', hs'⟩
    dsimp only at hx hu hs hx' hu' hs'
    subst hx hx'
    obtain rfl : u = u' := funext fun τ => funext fun i => (hder _).unique (hu τ i) (hu' τ i)
    have hss := gen_unique hT Uw.F Ha.i _ hP _ hθd hθ Θ.κ Θ.κ_ne fr fr' hfr hfr' s s' gen hs hs'
    obtain rfl : s = s' := by
      cases s; cases s'
      congr 1
      exact (funext hss).symm
    rfl

end GlobalTheory.ArcQ.AnFrEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfRationalPoints
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecLevel

theorem eq_zero_of_rational_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((Points.le_preimage_basicOpen_iff _ hU f).1 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem fib_fst {R : Type} [CommRing R] {S : Scheme.{0}} {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) :
    fib x ≫ pullback.fst G.hom y = x.left := pullback.lift_fst _ _ _

theorem sec_eq_zero {S : Scheme.{0}} (P : Out.PolAV S) {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (m : ℕ)
    (u : SecP P.L (pullback.fst P.A.hom y) m)
    (h : ∀ (x : Over.mk y ⟶ P.A) j, ⊤ ≤ x.left ⁻¹ᵁ P.L.U j → ArcPts.sval u (fib x) j = 0) (i) : u.f i = 0 := by
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  haveI : IsIntegral (pullback P.A.hom y) :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom).geometrically_isIntegral y _ _
      (IsPullback.of_hasPullback P.A.hom y)
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  refine eq_zero_of_rational_points (pullback.snd P.A.hom y) _ _ fun x hx hU => ?_
  let a : Over.mk y ⟶ P.A := Over.homMk (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
    exact Category.id_comp _)
  have e : fib a = x := by
    apply pullback.hom_ext
    · exact fib_fst a
    · rw [hx]
      exact pullback.lift_snd _ _ _
  have := h a j fun p hp => Set.mem_iInter.1 (hU hp) 0
  rw [e] at this
  exact this

theorem pow_mem_Theta {O : Type} [CommRing O] [StarRing O] (A : AnArc O) {th : (Fin A.gB → ℂ) → ℂ}
    (h : th ∈ A.Theta 1 0) (n : ℕ) : th ^ (n + 1) ∈ A.Theta (n + 1) 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa [pow_succ] using A.mul_mem_Theta ih h

theorem map_nsmul_eq_pow {V M : Type} [AddGroup V] [Group M] (x : V → M) (h : ∀ v v', x (v + v') = x v * x v')
    (n : ℕ) (v : V) : x (n • v) = x v ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, SpecGroup.map_zero_eq_one x h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem left_toUnit_comp {S : Scheme.{0}} {G T T' : Over S} (ξ : 𝟙_ (Over S) ⟶ G) (r : T'.left ⟶ T.left)
    (hr : r ≫ T.hom = T'.hom) : (toUnit T' ≫ ξ).left = r ≫ (toUnit T ≫ ξ).left := by
  rw [Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left, ← Category.assoc, hr]

theorem exists_germ_shift {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (Γ : Germs) (k : ℕ) [NeZero k] :
    ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im → ∀ la : A.La, (∀ α, (k : ℤ) ∣ A.be la.y α) → ∀ α, ∀ th ∈ A.Theta k α, ∀ z,
      ∃ F : Γ.R w, IsFShift A k α th la z F ∧ Γ.ev w F = A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) := by
  obtain ⟨T₀, h₀⟩ := exists_formal_convergence O A
  refine ⟨T₀, fun w hw la hla α th hth z => ?_⟩
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  obtain ⟨hm, hev⟩ := ((h₀ T₀ le_rfl k).1 _ _ (A.shift_mem_Theta hth la)).1 z
  refine ⟨Subalgebra.inclusion (Γ.le T₀ w hw)
    (⟨_, Conv.single_mem_halfRing T₀ (A.be la.y α / k) (Complex.exp (A.lin la z))⟩ * ⟨_, hm⟩),
    ⟨⟨NeZero.ne k, hla α⟩, fun n => ?_⟩, ?_⟩
  · rw [Subalgebra.coe_inclusion, MulMemClass.coe_mul,
      ← A.FSumShift_eq k la (Int.mul_ediv_cancel' (hla α)).symm, AnArc.coeff_FSumShift]
    refine (finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_).symm
    rw [AnArc.mem_level, eq_sub_iff_add_eq]
  · rw [Γ.ev_eq T₀ w hw, map_mul, hev w hw, Conv.ev_single hw, ← AnArc.e_mul_intCast]
    obtain ⟨m, hm⟩ := hla α
    rw [A.Sum_add_Pw_div, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
    congr 3
    push_cast
    field_simp

theorem level_on_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (k : ℕ) [NeZero k], ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → Function.Surjective (Ψ.pi w) → (∀ la, Ψ.pi w (A.Pw w la) = 1) → ∀ (ξ : 𝟙_ (Over S) ⟶ o.t.G) (la : A.La), ξ ^ k = 1 → Φ.LevelPt k (toUnit _ ≫ ξ) la → toUnit _ ≫ ξ = Ψ.pi w ((k : ℂ)⁻¹ • A.Pw w la) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hR k _
  obtain ⟨T₁, hT₁, hsec⟩ := _root_.GlobalTheory.FibreFrame.sections_extend_and_span hL hL2 E H D l B bb S s o A y Φ Γ Ψ hA hR k
  obtain ⟨T₂, hsh⟩ := exists_germ_shift A Γ k
  obtain ⟨T₃, hT₃⟩ := A.exists_isConvLine
  refine ⟨max T₁ (max T₂ T₃), hT₁.trans (le_max_left _ _), fun w hw' surj per ξ la hξ hlev => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ : T₁ < w.im ∧ T₂ < w.im ∧ T₃ < w.im := by simpa using hw'
  have hw : Ψ.T < w.im := lt_of_le_of_lt hT₁ h₁
  obtain ⟨σt, hσt, σ₀, hσ₀, hval, hspan⟩ := hsec w hw h₁
  have hk : k ≠ 0 := NeZero.ne k
  obtain ⟨θ, hθ, hθ0⟩ := hA.2
  have hθk : θ ^ k ∈ A.Theta k 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact pow_mem_Theta A hθ n
  have hθk0 : θ ^ k ≠ 0 := fun e => hθ0 (funext fun z => pow_eq_zero_iff hk |>.1 (congrFun e z))
  have hv : ∀ α, ∀ th ∈ A.Theta k α, ∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
      ArcPts.sval (σ₀ α th) (fib (Ψ.pi w v)) j = A.Sum k α th w v * Ψ.fr w j v ^ k := fun α th hth v j hj =>
    hval α th hth v j (by rw [fib_fst]; exact hj)
  refine LevelUnique.torsion_eq_of_same_ratios hL hL2 E H D l B bb S s o ℂ (Ψ.yw w) A.V (Ψ.pi w) k _ _
    (fun _ => True) (σ₀ 0 (θ ^ k)) (Nat.one_le_iff_ne_zero.2 hk) ?_ ?_ (fun m _ u hu => ?_) ?_
    (fun _ _ _ _ => trivial) fun v _ t₁ t₂ j j' hj hj' => ?_
  · rw [← MonObj.comp_pow, hξ, MonObj.comp_one]
  · rw [← map_nsmul_eq_pow _ (SpecGroup.pi_add Ψ hw), ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk), one_smul, per]
  · refine sec_eq_zero (objPolAV o) (Ψ.yw w) m u fun x j hj => ?_
    obtain ⟨v, rfl⟩ := surj x
    exact hu v j hj
  · obtain ⟨v, hv0⟩ := A.exists_Sum_ne_zero hk 0 hθk0 fun z => AnArc.summable_term hT₃ hk hθk h₃ (0, z)
    obtain ⟨j, hj⟩ := exists_chart o.t.PP.isLB ((Ψ.pi w v).left (default : PrimeSpectrum ℂ))
    have hj' := (HolHom.le_preimage_iff (Ψ.pi w v).left _).2 hj
    refine ⟨fun _ => j, fun e => ?_⟩
    have h0 : ArcPts.sval (σ₀ 0 (θ ^ k)) (fib (Ψ.pi w v)) j = 0 := by
      rw [ArcPts.sval, e]
      refine Points.valR_zero _ _ fun p hp => Set.mem_iInter.2 fun _ => ?_
      have := hj' hp
      rw [← fib_fst] at this
      exact this
    rw [hv 0 _ hθk v j hj'] at h0
    exact mul_ne_zero hv0 (pow_ne_zero _ ((SpecGroup.pi_frm Ψ hw v).1 j hj').ne_zero) h0
  · have e₀ : (Ψ.pi w v * (toUnit _ ≫ ξ)).left =
        spMap (Γ.ev w).toRingHom ≫ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left :=
      SpecGroup.left_mul_of_comp (T' := Over.mk (Ψ.yw w)) _ (SpecGroup.ev_base Ψ hw) (Ψ.pi_eq w hw v)
        (left_toUnit_comp ξ _ (SpecGroup.ev_base Ψ hw))
    have e₁ : (Φ.x v * (toUnit _ ≫ ξ)).left =
        spMap (Γ.R w).val.toRingHom ≫ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left :=
      SpecGroup.left_mul_of_comp (T' := Over.mk y) _ (SpecGroup.val_base Ψ hw) (Ψ.xt_gen w hw v).symm
        (left_toUnit_comp ξ _ (SpecGroup.val_base Ψ hw))
    have ht : ⊤ ≤ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left ⁻¹ᵁ o.t.PP.L.U j :=
      SpecGroup.le_preimage_of_unit (Γ.ev w).toRingHom (Γ.unit w) _ _ (e₀ ▸ hj)
    have hg : ⊤ ≤ (Φ.x v * (toUnit _ ≫ ξ)).left ⁻¹ᵁ o.t.PP.L.U j := by
      rw [e₁]
      exact fun p _ => ht (x := spMap (Γ.R w).val.toRingHom p) trivial
    have key : ∀ α α', ∀ th ∈ A.Theta k α, ∀ th' ∈ A.Theta k α',
        ArcPts.sval (σ₀ α th) (fib (Ψ.pi w v * (toUnit _ ≫ ξ))) j * A.Sum k α' th' w (v + (k : ℂ)⁻¹ • A.Pw w la) =
        ArcPts.sval (σ₀ α' th') (fib (Ψ.pi w v * (toUnit _ ≫ ξ))) j * A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) := by
      intro α α' th hth th' hth'
      obtain ⟨F, hF, hFe⟩ := hsh w h₂ la hlev.dvd α th hth v
      obtain ⟨F', hF', hFe'⟩ := hsh w h₂ la hlev.dvd α' th' hth' v
      have h := hlev.2.2 α α' th hth th' hth' v F F' j hF hF' hg
      rw [← hσt α th hth _ _ j e₁.symm ht, ← hσt α' th' hth' _ _ j e₁.symm ht, ← MulMemClass.coe_mul,
        ← MulMemClass.coe_mul, Subtype.val_inj] at h
      rw [hσ₀ α th _ _ j e₀ hj, hσ₀ α' th' _ _ j e₀ hj, ← hFe, ← hFe', ← map_mul, ← map_mul, h]
    obtain ⟨n₁, r₁, α₁, θ₁, m₁, s₁⟩ := hspan t₁
    obtain ⟨n₂, r₂, α₂, θ₂, m₂, s₂⟩ := hspan t₂
    rw [← SpecGroup.pi_add Ψ hw] at hj' ⊢
    rw [s₁ _ j hj, s₂ _ j hj, s₁ _ j' hj', s₂ _ j' hj', Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hv _ _ (m₁ b) _ j' hj', hv _ _ (m₂ a) _ j' hj']
    linear_combination (r₁ b * r₂ a * Ψ.fr w j' (v + (k : ℂ)⁻¹ • A.Pw w la) ^ k) * key _ _ _ (m₁ b) _ (m₂ a)

end GlobalTheory.SpecLevel
end
end

