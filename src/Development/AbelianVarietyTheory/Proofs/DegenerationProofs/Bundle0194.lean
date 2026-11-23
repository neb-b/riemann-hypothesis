module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0149
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.UU GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifNormal

theorem thetaNZ_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [Smooth G.hom] (L : LB G.left)
    (h : ∃ θ : LB.Sec L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) : ThetaNZ G L := by
  obtain ⟨θ, x, hx, hc⟩ := h
  refine ⟨θ, fun y => ?_⟩
  have ho : IsOpen (G.hom '' (nonzeroLocus θ : Set G.left)) := G.hom.isOpenMap _ (nonzeroLocus θ).isOpen
  have hy : y ∈ G.hom '' (nonzeroLocus θ : Set G.left) :=
    (IsLocalRing.specializes_closedPoint (R := R) y).mem_open ho ⟨x, hx, hc⟩
  obtain ⟨g, hg, e⟩ := hy
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hg
  exact ⟨g, i, e, hi⟩

theorem exists_polAV_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (W : S.Opens) (hG : IsSemiAbelian G) (hs : L.IsSymmetric) (hp : IsProper (pullback.snd G.hom W.ι))
    (ha : RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)))
    (hk : KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)))
    {K : Type} [Field K] (x : Sp K ⟶ S) (hx : Set.range x ⊆ W) :
    ∃ (A : PolAV (Sp K)) (gen : (Over.pullback x).obj G ≅ A.A), IsMonHom gen.hom ∧
      LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom x)) := by
  have hx' : Set.range x ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  let x' : Sp K ⟶ W.toScheme := IsOpenImmersion.lift W.ι x hx'
  have ex : x' ≫ W.ι = x := IsOpenImmersion.lift_fac _ _ _
  let φ : ((Over.pullback x).obj G).left ⟶ ((Over.pullback W.ι).obj G).left :=
    pullback.lift (pullback.fst G.hom x) (pullback.snd G.hom x ≫ x') (by
      rw [Category.assoc, ex]; exact pullback.condition)
  have eφ : φ ≫ pullback.fst G.hom W.ι = pullback.fst G.hom x := pullback.lift_fst _ _ _
  have h := isGrpPullback_pullback G x
  have hφ : IsGrpPullback ((Over.pullback x).obj G) ((Over.pullback W.ι).obj G) x' φ :=
    (isGrpPullback_pullback G W.ι).cancel (h.congr ex.symm eφ.symm) (pullback.lift_snd _ _ _)
  have hab : IsAbelianScheme ((Over.pullback W.ι).obj G) := by
    have := hG.comm
    have := hG.smooth
    have := hG.geomConnected
    refine ⟨inferInstance, ?_, hp, ?_⟩
    · change Smooth (pullback.snd G.hom W.ι)
      infer_instance
    · change GeometricallyConnected (pullback.snd G.hom W.ι)
      infer_instance
  have pull_isLB {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (F : Y ⟶ X) : (M.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hM (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g M F (𝟙 Y) y J J hy hy]
      exact gm_self hM _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g M F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g M F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g M F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hM _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have hL := pull_isLB L.isLB (pullback.fst G.hom x)
  have hiso : LBIso (L.L.pull (pullback.fst G.hom x)) ((L.L.pull (pullback.fst G.hom W.ι)).pull φ) :=
    LBIso.chartPull (chartPullSame L.L _ _ _ φ fun _ => eφ.symm) (Geo.Tor.chartPullPull _ φ φ rfl)
      (PolBaseChange.lbIso_refl (pull_isLB L.isLB (pullback.fst G.hom W.ι)))
  obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.pol_pull _ _ _ _ x' φ _ _ (pull_isLB L.isLB _) hL hab hφ hiso
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim K _ h₁
  obtain ⟨hL', hr, -, hs'⟩ := Out.CubePf.cubePull _ _ G _ (cubeMapOf h) L c
  obtain ⟨-, w, hw, -⟩ := hs' hs
  refine ⟨⟨(Over.pullback x).obj G, h₁, g, hg, L.L.pull (pullback.fst G.hom x), hL, ⟨_, hr⟩,
    fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩, h₂ ha, h₃ hk⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 _)), ?_⟩
  exact LBIso.chartPull (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (chartPullId _) (PolBaseChange.lbIso_refl hL)

theorem exists_unif_psiUnitOn : Laws → Laws2 → Laws3 → Laws4 → Laws5 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) := by
  intro h₁ h₂ h₃ h₄ h₅ R _ _ _ hz hn hi hc G _ _ L c W hG hs hS hE hθ hW hab hp ha hk
  have : (IsLocalRing.maximalIdeal R).IsMaximal := inferInstance
  have hadm : admitted R (IsLocalRing.maximalIdeal R) :=
    ⟨⟨hn, inferInstance, hi, hc⟩, hc, hz, inferInstance,
      inferInstanceAs (IsIntegrallyClosed (IsLocalRing.ResidueField R))⟩
  have hgen : Set.range (jK R) ⊆ W := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := hW
    refine Specializes.mem_open (y := y) ?_ W.isOpen hy
    refine (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 fun r hr => ?_
    have hz0 : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ z.2
    have hr' : algebraMap R (FractionRing R) r ∈ z.asIdeal := hr
    rw [hz0, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at hr'
    rw [hr']
    exact Ideal.zero_mem _
  obtain ⟨A, gen, hm, hL⟩ := exists_polAV_fibre G L c W hG hs hp ha hk (jK R) hgen
  obtain ⟨P, rfl, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric h₁ R A G hG gen hm L c hs
  have := hG.smooth
  obtain ⟨D, U, hU, -⟩ := _root_.GlobalTheory.PrimeUnif.exists_unif h₁ h₂ h₃ (GlobalTheory.LN.ega_of_laws h₁ h₂) (GlobalTheory.LN.uniformisation_dvr h₁ h₂ h₃ h₄ h₅) R _ hadm
    (inferInstanceAs (IsPrincipalIdealRing (IsLocalRing.ResidueField R))) G P hG hS hE
    (thetaNZ_of_closedPoint G _ hθ) A gen hm hL
  refine ⟨D, A, U, hU, ?_⟩
  rw [hab]
  exact _root_.GlobalTheory.PsiAbelian.psiUnitOn_abLocus h₁ h₂ h₃ h₄ h₅ R _ hadm D A G hG U (hab ▸ W.isOpen)

end GlobalTheory.UnifNormal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LiftValuationIntegralNorm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ModelData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

theorem exists_twisted_pull (hL : Laws) [IsLocalRing O'] [IsNoetherianRing O'] (a : ArcIn D l β O' b) {C : Type} [Field C]
    [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) C]
    (f : O' →+* R) (u₀ : R) (hu : (u : C) = algebraMap (FractionRing R) C (algebraMap _ _ u₀))
    (hf : ∀ x, algebraMap (FractionRing R) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)) :
    ∃ (DW : DegPre R) (_ : Module (𝓞 E) DW.X) (oW : letI := H.starRing; DW.OAct (𝓞 E)) (φ : _) (he : _) (w : _) (e : _)
      (νW : NumOf DW C (A.N.twist A.be u)), GlobalTheory.LN.Match a f u₀ DW oW φ he w e ∧ (∀ y, νW.eX y = e (A.ν.eX y)) ∧
      (∀ x, (νW.eA x).left ≫ φ = (A.ν.eA x).left) ∧ DW.PsiEven ∧ DW.TauBimult ∧ DW.P.g = a.D₀.P.g := by
  obtain ⟨D', hD, hg, hs⟩ := _root_.GlobalTheory.StrictPull.exists_isPullDeg_strict hL O' R f a.D₀ ⊤ (ArcPull.nonempty_psiOn_top _ a.gen) trivial
  obtain ⟨th', h₁, h₂⟩ := _root_.GlobalTheory.GeneratorPull.exists_generator_pull hL O' R f a.D₀.P D'.P _ hD.w (pull_grp hD) hD.w_gen A.ν.th A.ν.th_gen
  obtain ⟨ν', e₁, e₂⟩ := _root_.GlobalTheory.ValuesStrictPull.exists_numOf_strict_pull hL.globalFns O' R f a.D₀ D' hD hs C hf A.N A.ν th' h₁ h₂
  have h0 : algebraMap R (FractionRing R) u₀ ≠ 0 := fun h => u.ne_zero (by rw [hu, h, map_zero])
  let q : D'.X → (FractionRing R)ˣ := fun y => Units.mk0 _ h0 ^ (a.be (hD.xe y) (hD.xe y) / 2)
  obtain ⟨m, oW, he, w, e, hM, hx, hE, hB⟩ := GlobalTheory.T.arcDatum_pullback_rescaled_matches hL.globalFns E H D l c O β O' b a R f D' hD u₀ (Units.mk0 _ h0) rfl q
    _ rfl fun _ => rfl
  obtain ⟨νW, e₃, e₄⟩ := _root_.GlobalTheory.RescaleValues.exists_numOf_rescale R D' C A.N ν' _ A.be u q fun y => by
    simp only [q, e₁, A.be_eq, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hu]
  refine ⟨_, m, oW, _, he, w, e, νW, hM, fun y => hD.xe.injective ?_, fun x => ?_, hE, hB, hg⟩
  · exact ((congrArg hD.xe (e₃ y)).trans (e₁ y)).trans (hx _).symm
  · exact (congrArg (fun t => t.left ≫ PsiEvenPull.proj hD) (e₄ x)).trans (e₂ x)

theorem eq_zero_of_nsmul (D : Datum H) (k : ℕ) (x : D.La) (hk : 0 < k) (h : k • x = 0) : x = 0 := by
  refine D.unimod.1 (LinearMap.ext fun y => ?_)
  have := congrArg (fun t => D.EF t y) h
  simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, nsmul_eq_mul, mul_eq_zero,
    Nat.cast_eq_zero, hk.ne', false_or] at this
  rw [this, map_zero, LinearMap.zero_apply]

theorem local_of_arcBase {ϖ : O'} (h : GlobalTheory.LN.ArcBase O' ϖ) : IsLocalRing O' ∧ IsNoetherianRing O' := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

theorem exists_unitBall (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]; rfl⟩

theorem data_of_model : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) (o : Full D C) (M : Mdl o) (f : O' →+* M.W) (u₀ : M.W), A.ν.IntN → Roots u r → ‖(u : C)‖ < 1 → (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → (∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)) → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → (∀ j, o.I.ζ (n ^ j) = A.I.ζ (n ^ j) ∧ ∀ p : D.La → (A.N.twist A.be u).QT ((n ^ j) ^ 2), (∀ x, TwRel A.be u (r ((n ^ j) ^ 2)) (A.q _ x) (p x)) → o.Theta (n ^ j) fun x => (A.N.twist A.be u).tx (n ^ j) (p x)) → ∃ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N'), (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) ∧ (∀ j x (p : (A.N.twist A.be u).QT (n ^ j)) (q' : N'.QT (n ^ j)) p' z, TwRel A.be u (r (n ^ j)) (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev (n ^ j) x).left ≫ M.φ → M.P.ToA C (n ^ j) p' z) ∧ ∃ (DW : DegPre M.W) (_ : Module (𝓞 E) DW.X) (oW : letI := H.starRing; DW.OAct (𝓞 E)) (φ : _) (he : _) (w : _) (e : _) (νW : NumOf DW C (A.N.twist A.be u)), GlobalTheory.LN.Match a f u₀ DW oW φ he w e ∧ (∀ y, νW.eX y = e (A.ν.eX y)) ∧ (∀ x, (νW.eA x).left ≫ φ = (A.ν.eA x).left) ∧ GeoIso νW ν' J.toIso := by
  intro hV _ _ _ hT _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hO C _ _ _ _ _ _ A u r o M f u₀ hI hr hu1 hu hf n hn ho hn1 hθ
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  obtain ⟨_, _⟩ := local_of_arcBase hO
  have hGt := _root_.GlobalTheory.Ex.GtValues.points_correspond
  have hFam := _root_.GlobalTheory.Ex.brFam hL hL2
  have hWp := _root_.GlobalTheory.WeilValues.weil_eq_values hGt hFam
  have hUth := _root_.GlobalTheory.ThetaInValues.brUth_of_laws hL
  have hUrec := _root_.GlobalTheory.Ex.Recognition.urec_of_abelian (_root_.GlobalTheory.Ex.AbPartIso.main hL hT hUth)
  have hDvr := M.cdv.1
  have hAdm : AdmBase M.W (IsLocalRing.maximalIdeal M.W) := ⟨inferInstance, inferInstance, inferInstance, M.cdv.2.1⟩
  have hn0 : (n : C) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hp : ∀ j, 0 < n ^ j := fun j => pow_pos hn.pos j
  have xO : CExt O' ⊥ C := ⟨fun x => hf x ▸ M.ext.1 _, fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
  have xW : CExt M.W ⊥ C := ⟨M.ext.1, fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
  obtain ⟨DW, mW, oW, φ, he, w, e, νW, hM, hX, hA, hE, hB, hg⟩ := exists_twisted_pull hL a A u f u₀ hu hf
  obtain ⟨S, hS⟩ := exists_unitBall C
  obtain ⟨N', ν', hI'⟩ := ValuesExist.exists_integral_values hL M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C S
    fun x => (hS _).2 (M.ext.1 x)
  have hI'' : ν'.IntN := ⟨S, hS, hI'⟩
  obtain ⟨Q', hQ'⟩ := _root_.GlobalTheory.Ex.IntVal.main M.W _ hAdm M.P.D C M.ext N' ν' hI''
  obtain ⟨Q, hQ, -⟩ := (_root_.GlobalTheory.Ex.UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hO C xO A hI).2.2 u hu1
  have tN : A.N.toNumB.Tors n a.D₀.P.g := _root_.GlobalTheory.ValuesTorsion.tors_of_integral hL hL2 hUth O' a.D₀ a.even a.bimult C xO A.N A.ν hI n hn ho hn1
  have tW : (A.N.twist A.be u).toNumB.Tors n DW.P.g := hg ▸ tN
  have tN' := _root_.GlobalTheory.ValuesTorsion.tors_of_integral hL hL2 hUth M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C xW N' ν' hI'' n hn ho hn1

  obtain ⟨lA, linA⟩ := GlobalTheory.T.torsionIsometry_values_isTorsionLabelSystem hGt hWp E H D O' a.D₀ a.oa a.even a.bimult C A.I A.N A.ν A.q A.hq
  have ex : ∀ (k : ℕ) (x : D.La), ∃ p : (A.N.twist A.be u).QT k, 0 < k → TwRel A.be u (r k) (A.q k x) p := fun k x => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨p, h, -⟩ := existsUnique_twRel A.be u (r k) (hr.pow hk) (A.q k x)
      exact ⟨p, fun _ => h⟩
  choose lab hlab using ex
  have lT := _root_.GlobalTheory.TwistLabels.labels_twist C A.N D.La D.EF A.I.ζ A.q _ A.be u r hr lA lab fun k hk x => hlab k x hk

  obtain ⟨I', hζ, hTo⟩ := GlobalTheory.T.exists_torsion_isometry_uniformised_model hV.1 hGt E H D C o M N' ν'
  have G' := hGt M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  choose lab' hlab' using fun (k : ℕ) (x : D.La) => ((G'.2.2.2.2 k).1 (I'.ev k x)).exists
  obtain ⟨lM, linM⟩ := GlobalTheory.T.torsionIsometry_values_isTorsionLabelSystem hGt hWp E H D M.W M.P.D.toPre M.P.oD M.P.D.psi_even M.P.D.tau_bimult C I' N' ν' lab' hlab'
  have qEqEquiv (k : ℕ) : Equivalence (N'.QEq (k := k)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨0, by simp, by simp⟩
    · rintro p p' ⟨z, h, h'⟩
      exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N'.io_neg, mul_inv_cancel_right]⟩
    · rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
      exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N'.io_add, _root_.mul_assoc]⟩
  have refl' : ∀ k x, QkPt.Equiv _ C (I'.ev k x) (I'.ev k x) := fun k x =>
    ((G'.2.2.2.2 k).2.2 _ _ _ _ (hlab' k x) (hlab' k x)).2 ((qEqEquiv k).refl _)
  have th := fun j => GlobalTheory.T.modelSeries_eq_unit_mul_thetaPoint hL (_root_.GlobalTheory.Ex.ThetaSeries.theta_const_eq_series hV hGt hFam) E H D C o M N' ν' (n ^ j) ho.pow (I'.ev _) (lab' _) _
    (fun x z hz => hTo _ (pow_pos (hp j) 2) x _ z (refl' _ x) hz) (hlab' _)
    ((hθ j).2 (lab _) fun x => hlab _ x (pow_pos (hp j) 2))
  have h3 : 3 ≤ n ^ 1 := by
    have := hn.two_le
    obtain ⟨t, rfl⟩ := ho
    rw [pow_one]; omega
  obtain ⟨c₀, hc₀, hc⟩ := GlobalTheory.T.torsionLabelSystems_series_scalar_independent_of_level C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n ho lT lM (fun j => (th j).1)
    (Function.ne_iff.1 ((th 1).2 h3))
  obtain ⟨mt, hmt⟩ := _root_.GlobalTheory.ModelData.LabelMatch.exists_match C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n hn ho (eq_zero_of_nsmul D) lT lM A.I.ζ_pow I'.ζ_pow
    (fun j => by rw [hζ]; exact (hθ j).1) c₀ hc₀ hc
  obtain ⟨J, hJ, hGeo⟩ := hUrec M.W DW M.P.D.toPre hE hB M.P.D.psi_even M.P.D.tau_bimult C _ N' νW ν' Q Q' n hn ho hn1
    hQ hQ' tW tN' mt
  have hJ' := fun j p p' h₁ h₂ => (hmt j p p').1 (hJ j p p' h₁ h₂)
  refine ⟨N', ν', J, fun x y => ?_, fun j x p q' p' z h₁ h₂ h₃ h₄ h₅ => ?_,
    DW, mW, oW, φ, he, w, e, νW, hM, hX, hA, hGeo⟩
  · have key := _root_.GlobalTheory.ModelData.iso_comm_of_labels C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n hn.one_lt lT lM J hJ'
      (fun j => (_root_.GlobalTheory.Ex.QStr.qStructure C _ n _ hn0 tW j).2.2.1)
      (A.ν.eX.symm.toAddMonoidHom.comp ((DistribSMul.toAddMonoidHom _ x).comp A.ν.eX.toAddMonoidHom))
      (ν'.eX.symm.toAddMonoidHom.comp ((DistribSMul.toAddMonoidHom _ x).comp ν'.eX.toAddMonoidHom)) (x • ·)
      (fun j v => by
        obtain ⟨z, hz⟩ := linA _ (hp j) x v
        refine ⟨A.ν.eX.symm z, ?_⟩
        rw [(hlab _ _ (hp j)).1, (hlab _ _ (hp j)).1]
        exact (A.ν.eX.symm_apply_apply _).symm.trans ((congrArg A.ν.eX.symm hz).trans
          ((map_add _ _ _).trans (congrArg _ (map_nsmul _ _ _)))))
      (fun j v => by
        obtain ⟨z, hz⟩ := linM _ (hp j) x v
        exact ⟨ν'.eX.symm z, (ν'.eX.symm_apply_apply _).symm.trans ((congrArg ν'.eX.symm hz).trans
          ((map_add _ _ _).trans (congrArg _ (map_nsmul _ _ _))))⟩) y
    exact (congrArg ν'.eX key).trans (ν'.eX.apply_symm_apply _)
  · obtain rfl : p = lab _ x :=
      (existsUnique_twRel A.be u (r (n ^ j)) (hr.pow (hp j)) (A.q _ x)).unique h₁ (hlab _ x (hp j))
    obtain ⟨x₁, a₁, a₂⟩ := hJ' j _ q' h₂ h₃
    have a₃ := (lM.2.1 _ (hp j) x₁ x).2 ((lT.2.1 _ (hp j) x₁ x).1 a₁)
    have E' := qEqEquiv (n ^ j)
    exact hTo _ (hp j) x p' z (((G'.2.2.2.2 _).2.2 _ _ _ _ (hlab' _ x) h₄).2 (E'.trans (E'.symm a₃) a₂)) h₅

end GlobalTheory.ModelData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusOperatorEigenOfExpansionSingleClassStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusOperator_eigen_of_expansion_single_class : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (w₀ : W0 u.U.toUnifPre), w₀.IsGen → ∀ (α : u.D.toPre.X) (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N) (Φ : Fam u.D.toPre (PadicAlgCl p) S.N), IsComb u.A s b σ → u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ → (∀ β, (∀ z : u.D.toPre.X, β ≠ α + S.N • z) → ∀ j, (Φ.s β).f j = 0) → ∀ (t : S.perp l.yy.ker) (h : S.Gam), ∑ j, (∑ i, y₀ (algebraMap o S.R (S.ρ t j i)) * b i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩ = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val * ∑ j, b j * y₀ ⟨S.ev h j, S.ev_mem h j⟩ := by
  first | exact @GlobalTheory.TestFibre.eigen_of_expansion_in_class | exact GlobalTheory.TestFibre.eigen_of_expansion_in_class | (intros; apply GlobalTheory.TestFibre.eigen_of_expansion_in_class <;> assumption)
end

