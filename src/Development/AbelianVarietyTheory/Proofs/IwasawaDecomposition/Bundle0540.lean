module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnCharts
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeyInputAtChartPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtEx

theorem nonempty_basis_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n : ℕ} {v : Fin n → (epsR R ⟶ G')} (hb : IsLieBasis v) :
    Nonempty (Module.Basis (Fin n) R (TanM x G)) := by
  let u : Fin n → TanM x G := fun j => mkT (pushHom h (epsR R) (v j)) ((PullbackSections.isTangent_iff h _).1 (hb.1 j))
  have hcomb : ∀ (a : Fin n → R) (w : epsR R ⟶ G'), IsLieComb a v w ↔
      pushHom h (epsR R) w = tv (∑ i, a i • u i) := fun a w => by
    rw [PullbackSections.isLieComb_iff h, GlobalTheory.FlagMod.tv_sum']
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination R u) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact tv_mem W)
    refine (existsUnique_congr fun a => ?_).1 (hb.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (tanM_ext e).symm, fun e => by rw [e]⟩
  exact ⟨(Pi.basisFun R (Fin n)).map (LinearEquiv.ofBijective _ hbij)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_keyAt_of_sabMap (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hg : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, th, ⟨hw, hr⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev z M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev z M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ z he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp R ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  refine ⟨⟨GlobalTheory.GenericPol.toPolAV t M.n hg hp hA hK, hn, t.PP.rig, t.PP.rigGen, th, fun s => ?_, v, hb⟩, rfl,
    m.φ, he, w, rfl, m.cart, hw, hrig ▸ hr, fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, h₁, h₂⟩ := hne s
    exact ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  · refine (hth (j PUnit.unit) i _ h le_rfl).trans ?_
    exact congrArg (· * _) (GlobalTheory.LB.resG_self _ _)
  · exact hm' ▸ hv i

theorem smoothOfRelativeDimension_fibre {K : Type} [Field K] {z : Sp K ⟶ Y.X} {t : SAB H (Sp K)} (m : SABMap t Y.t z)
    (h : Set.range z ⊆ Set.range Y.j) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom := by
  obtain ⟨K', _, i, y, e⟩ := GlobalTheory.GenericPol.exists_lift z Y.j h
  obtain ⟨t', ⟨m₁⟩⟩ := GlobalTheory.ModFam.exists_sabPull (Out.specOf i) t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t' Y.j y Y.m (e ▸ n)
  have h₁ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m'.cart.1
      (GlobalTheory.ObjDim.smoothOfRelativeDimension Y.oF)
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace ↥t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have h₂ : SmoothOfRelativeDimension d t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m₁.cart.1 hd
  rw [← H1.dim_unique _ h₂ h₁ (eSec t'.G (default : PrimeSpectrum K'))]
  exact hd

theorem exists_keyAt_model (M : GChart Y) {K : Type} [Field K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (h : Set.range z ⊆ Set.range Y.j) (hpos : 1 ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) :
    ∃ x : KeyIn K, x.P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ KeyAt M z hz x := by
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull z Y.t
  obtain ⟨hp, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv m h
  have hg := smoothOfRelativeDimension_fibre m h
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis t.G hg
  obtain ⟨b⟩ := nonempty_basis_of_isLieBasis m.cart hv
  have hn : Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = M.n := by
    simpa using Fintype.card_congr (b.indexEquiv (GlobalTheory.FlagMod.lieBasis M.toMChart z hz))
  rw [hn] at hg hpos ⊢
  exact exists_keyAt_of_sabMap M z hz m hp hA hK hg hpos

end GlobalTheory.KeyAtEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_pow {K : Type} [Field K] [Algebra K ℂ] {A : Type} [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] [IsDomain (ℂ ⊗[K] A)] {n : ℕ} (hn : 0 < n) (u : Aˣ) {C : ℂ} (hC : C ≠ 0)
    (ρ : (A →ₐ[K] ℂ) → ℂ)
    (hρ : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (A →ₐ[K] ℂ)), IsOpen V →
      (∀ a : A, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V)
    (hu : ∀ ψ : A →ₐ[K] ℂ, ρ ψ ^ n = C * ψ (u : A)) : ∃ (a : K) (b : A), a ≠ 0 ∧ (u : A) = a • b ^ n := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (ℂ ⊗[K] A) inferInstance
  let res : (ℂ ⊗[K] A →ₐ[ℂ] ℂ) → (A →ₐ[K] ℂ) := fun χ =>
    (χ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let u' : (ℂ ⊗[K] A)ˣ := Units.map (algebraMap ℂ (ℂ ⊗[K] A) : ℂ →* _) (Units.mk0 C hC) *
    Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] ℂ ⊗[K] A) : A →* _) u
  have hu' : (u' : ℂ ⊗[K] A) = C ⊗ₜ[K] (u : A) := by
    simp [u', Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root (ℂ ⊗[K] A) n u' (fun χ => ρ (res χ)) hn
    (fun m V s hV hs => hρ m V (fun p => res (s p)) hV fun a => hs _) (fun χ => by
      rw [hu, hu']
      have : C ⊗ₜ[K] (u : A) = C • ((1 : ℂ) ⊗ₜ[K] (u : A)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl)
  exact _root_.GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul K A n w C u hn hC u.ne_zero (hw.trans hu')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem keySec_of_generic (h : GenFrEx Xo c) (b : ∀ Z : Comp Xo c, Om Z) (hb0 : ∀ Z, b Z ≠ 0)
    (hb : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R) : Nonempty (KeySec Xo c) := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨f, hf, hfb⟩ := _root_.GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (keyEx Dw) b fun C => (hb C).1
  obtain ⟨f', hf', hfb'⟩ := _root_.GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (-keyEx Dw) (fun Z => (b Z)⁻¹) fun C => by
    have := (hb C).2
    rw [mul_inv, ← Units.val_inv_eq_inv_val] at this
    simpa only [kch, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib] using this
  have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
    rw [← GlobalTheory.AllWt.secZ_nat]
    congr 1
    funext i
    cases i <;> rfl
  have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
  rw [add_neg_cancel, h0] at hm
  have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
  rw [h0] at h1
  have hff : f * f' = 1 := by
    refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
    have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
    have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
    have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
      (f * f') 1
    refine e₃.trans ?_
    change evC h Z (f * f') - evC h Z 1 = 0
    rw [e₁, e₂, hfb, hfb', mul_inv_cancel₀ (hb0 Z), sub_self]
  exact ⟨⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf⟩⟩

attribute [local instance 1100] Subalgebra.algebra in
theorem exists_chart_units {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.FamUnit κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (hpq : 1 ≤ Dw.p + Dw.q)
    (h : GenFrEx Xo c) : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧ GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
        ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨Φ, u, hΦ, hu, ?_⟩
  rw [← _root_.GlobalTheory.KeyFourth.rule_frBor κ h₁ h₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (_root_.GlobalTheory.KeyFourth.tied_keyPB E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem rule_eq_of_rootVal {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.ThetaOne κ) {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
      (fun j => Formalism.L2.PjFree.relab c σ (e j).1)} {r : ℕ} {M : ModelsOf F r} (T : ∀ k, ThetaData e F M k)
    {un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)} (hun : ∀ k, IsNormUn (T k) (un k)) (hpq : 1 ≤ Dw.p + Dw.q)
    {N : ℂ} (hN : N ≠ 0) (hNk : ∀ k, (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) = N)
    {y : FrPt Xo c (CAt σ)} {v : ℂ} (hv : RootVal (unfOf e F M un) y v) (Φ : FibKey Xo ℂ y.x)
    (hΦ : Tied (S := ℂ) e y.s y.u Φ) :
    v ^ 4 = (N / (2 * Real.pi * Complex.I) ^ g) ^ 4 * (κ ℂ Φ.key : ℂ) := by
  obtain ⟨k, x, t, ht, rfl⟩ : ∃ (k : Fin F.n) (x : (M.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) := hv
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (un k x).x, Tied (S := ℂ) e (un k x).s (un k x).u Ψ :=
    @_root_.GlobalTheory.KeyFourth.exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (un k x) hpq
  have e₁ : κ ℂ Φ.key = kch (S := ℂ) t ^ 4 * κ ℂ Ψ.key :=
    @_root_.GlobalTheory.KeyFourth.rule_frBor κ h₁ h₂ E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra t (un k x) y Ψ Φ ht hΨ hΦ
  obtain ⟨a, ha, hy⟩ := hun k x
  have hb : (T k).co.symm x.1 ∈ (T k).co ⁻¹' (M.X k).dom := by
    show (T k).co ((T k).co.symm x.1) ∈ (M.X k).dom
    rw [(T k).co.apply_symm_apply]; exact x.2
  have d1 := ((T k).norm _ hb).1.ne_zero
  rw [hNk] at ha
  have a0 : a ≠ 0 := fun h0 => mul_ne_zero hN d1 (by rw [← ha, h0]; simp)
  have e₂ := GlobalTheory.T.theta_key_rule_value_at_theta_point κ h₁ h₃ E H Dw l Xo c σ g e F r M k (T k) _ hb a (un k x) Ψ a0 hy hΨ
  have e₃ : N ^ 4 * (κ ℂ Ψ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g) ^ 4 := by
    refine mul_right_cancel₀ (pow_ne_zero 4 d1) ?_
    rw [show a ^ 8 = (a ^ 2) ^ 4 by ring, ha] at e₂
    linear_combination e₂
  have hπ : ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Complex.two_pi_I_ne_zero)
  have e₄ : (κ ℂ Φ.key : ℂ) = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) ^ 4 * (κ ℂ Ψ.key : ℂ) := by
    rw [e₁]
    rfl
  rw [e₄, div_pow, mul_left_comm, div_mul_eq_mul_div, e₃, div_self hπ, mul_one]


end GlobalTheory.KeyFourth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStep
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull ev_res ev_appLE le_preimage_inf le_preimage_map le_preimage_mono)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.GrCl

section Frames

variable {X Z : Scheme.{0}} {F : X.Modules} {S : Type} [CommRing S]

def frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') : Matrix (Fin n) (Fin n') Γ(X, U) :=
  ((hm'.basis h').toMatrix (hm.basis h)).transpose

theorem sum_frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (l : Fin n) :
    resM F h (m l) = ∑ l', frMat hm hm' h h' l l' • resM F h' (m' l') := by
  simp only [frMat, Matrix.transpose_apply, Module.Basis.toMatrix_apply, ← hm'.basis_apply h']
  rw [Module.Basis.sum_repr, hm.basis_apply]

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Lin

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : X.Opens}

def tanLin (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) : TanM x t.G →ₗ[S] (Fin n → S) where
  toFun v l := tanEv t (isTan_tv v) h (s l)
  map_add' v w := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 2 (fun i => (tv (![v, w] i)).left) (fun i => isTan_tv _) ![1, 1] _
      (isTan_tv (v + w)) ((LieMet.isComb_iff _ _ _).2 (by simp)) (s l)
    simpa using this
  map_smul' a v := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 1 (fun _ => (tv v).left) (fun _ => isTan_tv _) (fun _ => a) _
      (isTan_tv (a • v)) ((LieMet.isComb_iff (fun _ => v) _ _).2 (by simp)) (s l)
    simpa using this

theorem tanLin_apply (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) (l : Fin n) :
    tanLin t h s v l = tanEv t (isTan_tv v) h (s l) := rfl

theorem tanEv_sum_smul (h : ⊤ ≤ x ⁻¹ᵁ V) {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) {n : ℕ}
    (a : Fin n → Γ(X, V)) (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t hv h (∑ l, a l • s l) = ∑ l, ev x V h (a l) * tanEv t hv h (s l) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have := tanEv_smul t hv h 0 0
    simpa using this
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tanEv_add, tanEv_smul, ih]; rfl

theorem tanLin_tanPull {S' : Type} [CommRing S'] (φ : S →+* S') {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ V)
    (h' : ⊤ ≤ x' ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) :
    tanLin t h' s (tanPull φ e v) = φ ∘ tanLin t h s v := by
  subst e
  exact funext fun l =>
    GlobalTheory.LocM.tanEv_baseChange E H X t S x V h _ (isTan_tv v) S' φ _ h' (s l)

theorem tanLin_injective (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) {U : X.Opens} (e : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hs : VB.IsFrame fun l => resM _ e (s l)) : Function.Injective (tanLin t h s) := fun v w hvw =>
  tan_ext ((GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x U hU n _ hs (tanLin t h s w)).unique
    ⟨isTan_tv v, fun l => (tanEv_resM t _ hU e _).trans (congrFun hvw l)⟩
    ⟨isTan_tv w, fun _ => tanEv_resM t _ hU e _⟩)

end Lin

section Phi

variable {X X' X₀ Z : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {t₀ : SAB H X₀} {τ : X ⟶ X₀} {τ' : X' ⟶ X₀}
  (mu : SABMap t t₀ τ) (mu' : SABMap t' t₀ τ') {π : Z ⟶ X} {g : Z ⟶ X'} (e : g ≫ τ' = π ≫ τ)
  {S : Type} [CommRing S]

end Phi

end GlobalTheory.GrCl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CechPic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.InvertIdeal

section General

variable {X : Scheme.{0}} [IsIntegral X]

theorem exists_mul_pow {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) (α : Γ(X, U))
    (hα : genericPoint X ∈ X.basicOpen α) {f : X.functionField} (hf : ∀ x ∈ X.basicOpen α, RegAt x f) :
    ∃ (n : ℕ) (γ : Γ(X, U)), fnOf U h γ = f * fnOf U h α ^ n := by
  obtain ⟨β, rfl⟩ := exists_fnOf_eq hα hf
  have := hU.isLocalization_basicOpen α
  obtain ⟨n, γ, e⟩ := IsLocalization.Away.surj α β
  refine ⟨n, γ, ?_⟩
  have e' := congrArg (fnOf _ hα) e
  rw [map_mul, map_pow] at e'
  have r (a : Γ(X, U)) : fnOf _ hα (algebraMap _ Γ(X, X.basicOpen α) a) = fnOf U h a :=
    fnOf_resG (X.basicOpen_le α) hα a
  rw [r, r] at e'
  exact e'.symm

theorem exists_denom {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) {x : X} (hx : x ∈ U)
    {f : X.functionField} (hf : RegAt x f) :
    ∃ β γ : Γ(X, U), x ∈ X.basicOpen β ∧ fnOf U h γ = f * fnOf U h β := by
  obtain ⟨W, hW, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨α, hle, hα⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hW⟩ hx
  obtain ⟨n, γ, e⟩ := exists_mul_pow hU h α (gen_mem hα) fun y hy => regAt_fnOf (hle hy) (gen_mem hW) a
  refine ⟨α ^ (n + 1), γ * α, by rwa [X.basicOpen_pow α n.succ_pos], ?_⟩
  rw [map_mul, e, map_pow, pow_succ, mul_assoc]


theorem exists_unitAt {x : X} {ι : Type} [Fintype ι] {c g : ι → X.functionField} (hc : ∀ i, RegAt x (c i))
    (hg : ∀ i, RegAt x (g i)) (e : ∑ i, c i * g i = 1) : ∃ i, UnitAt x (g i) := by
  by_contra! H
  have : ZeroAt x (∑ i, c i * g i) := Finset.sum_induction _ _ (fun _ _ => ZeroAt.add) (zeroAt_zero x) fun i _ =>
    mul_comm (g i) (c i) ▸ (zeroAt_iff.2 ⟨hg i, H i⟩).mul (hc i)
  exact (zeroAt_iff.1 (e ▸ this)).2 (unitAt_one x)

theorem exists_common_open {x : X} {ι : Type} [Finite ι] {g : ι → X.functionField} (hg : ∀ i, RegAt x (g i)) :
    ∃ (W : X.Opens) (hx : x ∈ W), ∀ i, ∃ a : Γ(X, W), fnOf W (gen_mem hx) a = g i := by
  choose U hU a ha using fun i => (hg i).exists_fnOf
  let W : X.Opens := ⟨⋂ i, U i, isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hle (i) : W ≤ U i := Set.iInter_subset (fun i => (U i : Set X)) i
  exact ⟨W, Set.mem_iInter.2 hU, fun i => ⟨resG X (hle i) (a i), (fnOf_resG _ _ _).trans (ha i)⟩⟩

end General

variable {F : Type} [Field F] [NumberField F]

end GlobalTheory.InvertIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (Q : Di.La →+ (Letter Dw → ℂ)) (gm : Di.La ≃ₗ[𝓞 E] Di.La), IsPerBasis Di x hm → GoodPer c σ τ x hm Q → IsIsom Di gm → GoodPer c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) ∧ ‖perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom)‖ = ‖perVal c σ τ x hm Q‖ ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → IsLev l Di gm → perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) = perVal c σ τ x hm Q) := by
  first | exact @GlobalTheory.ShFam.HorIso.perVal_isom | exact GlobalTheory.ShFam.HorIso.perVal_isom | (intros; apply GlobalTheory.ShFam.HorIso.perVal_isom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinatePolynomialBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontalCoordinate_polynomial_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (g r : ℕ) (T₀ : Di.La ≃+ (Fin r → ℤ)) (ρ : Fin g → Fin r → ℂ), IsPerBasis Di x hm → ∃ (C : ℝ) (k : ℕ), ∀ (Q : Di.La →+ (Letter Dw → ℂ)) (W : Matrix (Letter Dw) (Fin g) ℂ) (Wi : Matrix (Fin g) (Letter Dw) ℂ) (lam : Fin r → Fin g → ℂ) (A : ℝ), GoodPer c σ τ x hm Q → W * Wi = 1 → Wi * W = 1 → (∀ v, ∑ z, Q v z • W z = ∑ m, T₀ v m • lam m) → (∀ j, ∑ m, ρ j m • lam m = Pi.single j 1) → 1 ≤ A → (∀ z j, ‖W z j‖ ≤ A) → (∀ j z, ‖Wi j z‖ ≤ A) → (∀ m j, ‖lam m j‖ ≤ A) → ‖perVal c σ τ x hm Q‖ ≤ C * A ^ k ∧ ‖(perVal c σ τ x hm Q)⁻¹‖ ≤ C * A ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.PolyBd.perVal_bound | exact GlobalTheory.ShFam.Hor.PolyBd.perVal_bound | (intros; apply GlobalTheory.ShFam.Hor.PolyBd.perVal_bound <;> assumption)
end

