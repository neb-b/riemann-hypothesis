module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LeOfClosedPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGradedChartsNearGenericPointClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.GradedCharts
open GlobalTheory.ProjSpace GlobalTheory.ZJ Matrix

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem split_geoTest (hL : GlobalTheory.UT.LL) [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (hBig : S.Big)
    {l : Q.Λ} {A A' : Matrix S.J S.J Ω} (hAA : A' * A = 1) {T : AddSubgroup S.Gam} [Finite (T →+ ZMod S.N)]
    {wt : S.J → (T →+ ZMod S.N)}
    (hwt : ∀ i, (S.proj _ (wt i)).map (algebraMap o Ω) *ᵥ (A * Q.B l) i = (A * Q.B l) i)
    {X : Scheme.{0}} (a : X ⟶ Q.P.left) (b : X ⟶ M.Z) {H : LB X} {s : S.J → H.Sec}
    (haff : ∀ i, wt i = 0 → IsAffineOpen (nonzeroLocus (s i))) (hcov : ⨆ i : {i // wt i = 0}, nonzeroLocus (s i.1) = ⊤)
    (hcrd : ∀ (K : Type) [Field K] (x : Sp K ⟶ X),
      ∃ x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme, x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x ≫ a ∧
        ∀ w, Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w → Crd H s x (A.map (M.val (x ≫ b)) *ᵥ w))
    {p : ℕ} [Fact p.Prime] {y : Sp (ZH.OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} (g : ρ.GeoTest p y₀) (c : Q.Fac y g.u)
    (tm : Q.TMap g c) (hU : Set.range (ZH.gPt p ≫ y) ⊆ U₀) (hl : y (ZH.cPt p) ∈ Q.W l)
    (hT : T = S.TT M (y (ZH.cPt p))) (hO : ∀ i j, A i j ∈ M.O (y (ZH.cPt p)) ∧ A' i j ∈ M.O (y (ZH.cPt p)))
    (φ : g.mod.Φ.G.left ⟶ X) [IsAffineHom φ] (hφ1 : φ ≫ a = g.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι)
    (hφ2 : φ ≫ b = g.mod.Φ.G.hom ≫ ZH.rPt p ≫ y) :
    ∃ d ≤ S.g, ∃ cc : Fin d → (T →+ ZMod S.N), ((ofSec wt 0 s haff hcov).pull φ).Split (H := g.mod.Φ.G) cc := by
  obtain ⟨m, cl, hm, hcl, hcl0, hmw, hmv⟩ := exists_matrix hB Q hAA hwt g c tm hU hl hT hO
  have : IsAlgClosed (ZH.kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have := g.mod.smooth
  have : Smooth g.u.G.hom := SmoothOfRelativeDimension.smooth S.g _
  have : Smooth g.mod.Φ.G.hom := MorphismProperty.of_isPullback g.mod.cart.1 this
  have : IsReduced g.mod.Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced g.mod.Φ.G.hom
  choose F hF using fun i => (GlobalTheory.SecRatio.existsUnique_isLin g.mod.Φ.G.hom g.mod.F (m i)).exists
  have hlr := locus_ratio g.mod.Φ.G.hom φ s F fun u hu => by
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (g.mod.Φ.H_isLB 1) g.mod.F u
    obtain ⟨x', hx', hc⟩ := hcrd _ (u ≫ φ)
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) x'
    rw [Category.assoc, hφ1] at hx'
    obtain ⟨k, hk⟩ := hmv u x' v w hu hx' hv hw
    have h3 := hc w hw
    rw [Category.assoc, hφ2, reassoc_of% hu, hk] at h3
    have h4 := crd_lin hF (ψ := RingHom.id _) (hu.trans (Spec.map_id _).symm) hv
    exact ⟨_, CrdCalc.crd_smul k h4, h3⟩
  exact ⟨_, le_of_add_le_right g.mod.dim.le,
    GlobalTheory.T.exists_torus_action_weighted_charts hL.1 hL.2.1 _ g.mod.Φ S.g S.N (S.r * S.N) _ S.J _ g.mod.F F g.mod.pol m
    ((ofSec wt 0 s haff hcov).pull φ) (Equiv.refl _) (fun α => cl (g.mod.xe α))
    ⟨(GlobalTheory.ZH.utest_dim_and_split hL o Ω S ρ p y₀ g.u).2.2.2.1, hBig.1, hBig.2.1⟩ g.mod.good g.mod.dim hm hF
    (fun α β => (hcl _ _).trans ⟨fun ⟨n, hn⟩ => ⟨g.mod.xe.symm n, g.mod.xe.injective (by simpa using hn)⟩,
      fun ⟨n, hn⟩ => ⟨g.mod.xe n, by simp [hn]⟩⟩)
    ((congrArg cl (map_zero _)).trans hcl0)
    (fun i j hij => (hmw i j hij).trans (congrArg cl (g.mod.xe.apply_symm_apply _).symm))
    fun i => hlr i.1⟩

theorem hasCharts : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.HasCharts := by
  intro hL o Ω _ _ _ hA S ρ M U₀ EE hB Q ex hBig hGeo hFib z
  change M.Z at z
  obtain ⟨W, l, A, A', wt, hW, hz, hle, hsup, hO, hAA, hwt⟩ := exists_adapted hB Q z
  obtain ⟨R, _, _, t, ht, htz, htW⟩ := exists_immersion hW hz
  have hT : ∀ q, S.TT M z = S.TT M (t q) := fun q => by
    have h1 : z ⤳ t q := htz ▸ ((PrimeSpectrum.le_iff_specializes ⊥ q).1 bot_le).map t.continuous
    have h2 : S.supI M z = S.supI M (t q) :=
      (hsup _ (htW (Set.mem_univ q))).antisymm fun a ha => RatModel.Div.of_specializes ha h1
    exact congrArg (fun I => S.perp (AddSubgroup.closure I)) h2
  obtain ⟨H, s, haff, hcov, hcrd⟩ := exists_sections hB Q hAA hwt ⟨z, hz⟩ hle hO t htW hT
  have := FreeNear.finite_char S (S.TT M z)
  refine ⟨R, inferInstance, inferInstance, t, ht, htz, ofSec wt 0 s haff hcov, fun p _ y τ x hx h hh h1 h2 => ?_⟩
  have hU := cl_of_test τ
  obtain ⟨y₀, g, c, ⟨tm⟩⟩ := (_root_.GlobalTheory.ZH.exists_geoTest_tMap_and_centre hL o Ω S ρ M U₀ EE hB Q hBig hGeo).1 p y hU
  obtain ⟨e, he, hef⟩ := _root_.GlobalTheory.ZH.exists_iso_special_fibre_of_test hL o Ω S ρ M U₀ EE hB Q ex p y y₀ g c tm τ hBig hFib
  have hy : t (x (IsLocalRing.closedPoint _)) = y (ZH.cPt p) :=
    (congrArg (fun f => f (IsLocalRing.closedPoint (ZH.kb p))) hx).trans
      (congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (ZH.OO p))))
  have hyW := (congrArg (· ∈ W) hy).mp (htW (Set.mem_univ _))
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hie : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  obtain ⟨h', hh'⟩ : ∃ h' : ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H).left ⟶
    pullback (Q.G.ι ≫ Q.P.hom) t, h' = h := ⟨h, rfl⟩
  subst hh'
  have : IsAffineHom h' := hh
  have hφ1 : (e.inv.left ≫ h') ≫ pullback.fst _ _ ≫ Q.G.ι = g.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    have h3 : h' ≫ pullback.fst (Q.G.ι ≫ Q.P.hom) t ≫ Q.G.ι =
        e.hom.left ≫ g.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι :=
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h1).trans (Category.assoc _ _ _))).trans hef.symm
    rw [Category.assoc, h3, reassoc_of% hei]
  have hφ2 : (e.inv.left ≫ h') ≫ pullback.snd _ _ ≫ t = g.mod.Φ.G.hom ≫ ZH.rPt p ≫ y := by
    have h3 : h' ≫ pullback.snd (Q.G.ι ≫ Q.P.hom) t ≫ t =
        ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H).hom ≫ ZH.rPt p ≫ y :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) h2).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) hx)))
    rw [Category.assoc, h3]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ZH.rPt p ≫ y) (Over.w e.inv))
  obtain ⟨d, hd, cc, hs⟩ := split_geoTest hL hB Q hBig hAA hwt _ _ haff hcov hcrd g c tm hU (hle hyW)
    ((hT _).trans (congrArg (S.TT M) hy)) (hO _ hyW) (e.inv.left ≫ h') hφ1 hφ2
  exact ⟨d, hd, cc, split_pull_of_comp e _ h' _ (by rw [reassoc_of% hie]) hs⟩

end GlobalTheory.ZH.GradedCharts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.SymLevelDescent

open GlobalTheory.ThetaDescent

theorem hypS_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)} {A : Over (Sp K)}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A₀) {φ : A.left ⟶ A₀.left}
    (h : IsGrpPullback A A₀ (spMap i) φ) {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hb : LBIso L (L₀.pull φ)) {w wd : A ⟶ A} {w₀ wd₀ : A₀ ⟶ A₀} (e : φ ≫ w₀.left = w.left ≫ φ)
    (ed : φ ≫ wd₀.left = wd.left ≫ φ) (hw : IsMonHom w) (hwd : IsMonHom wd) (hs : w * wd = 𝟙 A)
    (hp : LBIso L (cubeLB A ![𝟙 A, w] L))
    (ha : LBIso (cubeLB A ![fst A A ≫ w, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ wd] L)) :
    GlobalTheory.ZH.HypS A₀ L₀ := by
  have F := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i
  have pa := fun {T : Over (Sp K)} (x : T ⟶ A) => GlobalTheory.SymSpread.pushPt_comp h e x
  have pd := fun {T : Over (Sp K)} (x : T ⟶ A) => GlobalTheory.SymSpread.pushPt_comp h ed x
  have hc : ∀ {T : Over (Sp K)} {n : ℕ} (x : Fin n → (T ⟶ A)), (cubeLB A x L).IsLB :=
    fun x => DVR.linComb_isLB _ hL _ _
  have hc₀ : ∀ {T : Over (Sp K₀)} {n : ℕ} (x : Fin n → (T ⟶ A₀)), (cubeLB A₀ x L₀).IsLB :=
    fun x => DVR.linComb_isLB _ hL₀ _ _
  refine ⟨w₀, wd₀, (F.2 A₀ A₀ A A φ φ w₀ w h h e).1 hw, (F.2 A₀ A₀ A A φ φ wd₀ wd h h ed).1 hwd, ?_, ?_, ?_⟩
  · let U := pushPt h.1.w (𝟙 A)
    have hU : U.left = φ := Category.id_comp _
    haveI : Epi U.left := hU ▸ (F.1 _ _ _ _ φ h.1).1
    apply preHom_injective U
    have b : pushPt h.1.w (w * wd) = pushPt h.1.w w * pushPt h.1.w wd := map_mul (pushHom h A) _ _
    have c := pa (𝟙 A)
    have d := pd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [hs, c, d, ← MonObj.comp_mul] at b
    exact b.symm.trans (Category.comp_id _).symm
  · let U := pushPt h.1.w (𝟙 A)
    have hU : U.left = φ := Category.id_comp _
    have h₁ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![𝟙 A₀, w₀] ![𝟙 A, w] U (fun i => by
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rw [hU] at h₁
    refine (lb_gen_iso_descend_field K₀ K i _ _ A₀.hom A.hom φ hA.smooth hA.proper hA.geomConnected h.1).2 _ _ hL₀
      (hc₀ _) ?_
    exact LBIso.trans (pull_isLB hL₀ _) hL (pull_isLB (hc₀ _) _) hb.symm
      (LBIso.trans hL (hc _) (pull_isLB (hc₀ _) _) hp h₁)
  · have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
    let U := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
    have h₁ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![fst A₀ A₀ ≫ w₀, snd A₀ A₀] ![fst A A ≫ w, snd A A] U (fun i => by
      fin_cases i
      · exact (pa _).trans (by simp [U])
      · simp [U])
    have h₂ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![fst A₀ A₀, snd A₀ A₀ ≫ wd₀] ![fst A A, snd A A ≫ wd] U (fun i => by
      fin_cases i
      · simp [U]
      · exact (pd _).trans (by simp [U]))
    refine (lb_gen_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom (A ⊗ A).hom U.left A₂.smooth A₂.proper A₂.geomConnected
      (GlobalTheory.SymSpread.isPullback_square h)).2 _ _ (hc₀ _) (hc₀ _) ?_
    exact LBIso.trans (pull_isLB (hc₀ _) _) (hc _) (pull_isLB (hc₀ _) _) h₁.symm
      (LBIso.trans (hc _) (hc _) (pull_isLB (hc₀ _) _) ha h₂)

theorem unitOn_zpow {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn u ^ n = unitOn (u ^ n) :=
  (map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom) _ n).symm

theorem isPrimitiveRoot_unitOn_iff {R : Type} [CommRing R] (u : Rˣ) (k : ℕ) :
    IsPrimitiveRoot (unitOn u) k ↔ IsPrimitiveRoot u k :=
  IsPrimitiveRoot.map_iff_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom)
    (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1)

theorem level_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (Q : Out.PolAV (Sp K))
    (A₀ : Over (Sp K₀)) [GrpObj A₀] (hab : IsAbelianScheme A₀) (hdim : SmoothOfRelativeDimension Q.g A₀.hom)
    (L₀ : LB A₀.left) (hL : L₀.IsLB) (hr : Out.Rigidified A₀ L₀) (hs : Out.Sym A₀ L₀) (hamp : Out.RelAmple A₀ L₀)
    (hk : Out.KTriv A₀ L₀) {φ : Q.A.left ⟶ A₀.left} (hp : IsGrpPullback Q.A A₀ (spMap i) φ)
    (hw : LBIso Q.L (L₀.pull φ)) (k : ℕ) (z : K₀ˣ) (t : Out.Level Q k (unitOn (Units.map i.toMonoidHom z)))
    (pt₀ : Fin (2 * Q.g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (hpt : ∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) :
    Nonempty (Out.Level ⟨A₀, hab, Q.g, hdim, L₀, hL, hr, hs, hamp, hk⟩ k (unitOn z)) := by
  let U : Over.mk ((Out.baseOver (Sp K)).hom ≫ spMap i) ⟶ Out.baseOver (Sp K₀) := Over.homMk (spMap i) (by simp)
  haveI : Epi U.left := epi_spMap i
  have hU : ∀ a, pushHom hp _ (t.pt a) = preHom U (pt₀ a) := fun a => Over.OverMorphism.ext (hpt a)
  have key : ∀ (K' : Type) [Field K'] (x : Sp K' ⟶ Sp K₀), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (s : Sp Ω ⟶ Sp K) (N : Type) (_ : Monoid N) (P : (Over.mk s ⟶ Q.A) →* N) (R : (Over.mk x ⟶ A₀) →* N),
      Function.Bijective P ∧ Function.Injective R ∧
      ∀ a, P ((Over.homMk s (by simp) : Over.mk s ⟶ Out.baseOver _) ≫ t.pt a) =
        R ((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver _) ≫ pt₀ a) := by
    intro K' _ x
    obtain ⟨x', rfl⟩ := Spec.map_surjective x
    obtain ⟨Ω, _, _, j, j', hj⟩ := GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i x'.hom
    have hc : spMap j' ≫ Spec.map x' = spMap j ≫ spMap i := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hj.symm
    let V : Over.mk ((Over.mk (spMap j)).hom ≫ spMap i) ⟶ Over.mk (Spec.map x') := Over.homMk (spMap j') hc
    haveI : Epi V.left := epi_spMap j'
    refine ⟨Ω, inferInstance, inferInstance, spMap j, _, inferInstance, pushHom hp (Over.mk (spMap j)), preHom V,
      pushHom_bijective hp _, preHom_injective V, fun a => ?_⟩
    apply Over.OverMorphism.ext
    show (spMap j ≫ (t.pt a).left) ≫ φ = spMap j' ≫ Spec.map x' ≫ (pt₀ a).left
    rw [Category.assoc, hpt, ← Category.assoc, ← hc, Category.assoc]
  refine ⟨{ pt := pt₀, prim := ?_, torsion := fun a => ?_, indep := ?_, span := ?_, pairing := fun a a' => ?_ }⟩
  · exact (isPrimitiveRoot_unitOn_iff _ _).2 (((isPrimitiveRoot_unitOn_iff _ _).1 t.prim).of_map_of_injective
      (Units.map_injective i.injective))
  · apply preHom_injective U
    rw [map_pow, ← hU, ← map_pow, t.torsion, map_one, map_one]
  · intro K' _ _ x c c' hc
    obtain ⟨Ω, _, _, s, N, _, P, R, hP, hR, H⟩ := key K' x
    refine t.indep Ω s c c' (hP.1 ?_)
    have := congrArg R hc
    unfold Out.linComb at this ⊢
    rw [map_prod_pow, map_prod_pow] at this ⊢
    simpa only [H] using this
  · intro K' _ _ x y₀ hy
    obtain ⟨Ω, _, _, s, N, _, P, R, hP, hR, H⟩ := key K' x
    obtain ⟨y, hy'⟩ := hP.2 (R y₀)
    obtain ⟨c, hc⟩ := t.span Ω s y (hP.1 (by rw [map_pow, hy', ← map_pow, hy, map_one, map_one]))
    refine ⟨c, hR ?_⟩
    have := (congrArg P hc).trans hy'
    unfold Out.linComb at this ⊢
    rw [map_prod_pow] at this ⊢
    simpa only [H] using this
  · haveI := hab.comm
    have h₁ := (GlobalTheory.weilIs_grpPullback_of_comm _ _ A₀ Q.A (spMap i) φ L₀ Q.L hL Q.isLB hp hw _ k (t.pt a) (t.pt a')
      (U ≫ pt₀ a) (U ≫ pt₀ a') _ (hpt a).symm (hpt a').symm).1 (t.pairing a a')
    rw [unitOn_zpow] at h₁ ⊢
    refine (_root_.GlobalTheory.weilIs_fieldExt_iff _ A₀ K₀ K i (𝟙 _) L₀ k (pt₀ a) (pt₀ a') _ hab hL).1 ?_
    rw [map_zpow]
    exact (weilIs_congr (by simp) L₀ k _ _ _ _ rfl rfl _).1 h₁

theorem exists_fg_subalgebra {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) :
    letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
    ∃ R₀ : Subalgebra o (gen β s), R₀.FG ∧ ∀ x : gen β s, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b := by
  letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
  let s₀ : Set (gen β s) := (gen β s).subtype ⁻¹' (s : Set K)
  have hfin : s₀.Finite := s.finite_toSet.preimage (gen β s).subtype.injective.injOn
  refine ⟨Algebra.adjoin o s₀, Subalgebra.fg_def.2 ⟨s₀, hfin, rfl⟩, fun x => ?_⟩
  have hle : Subring.closure (Set.range β ∪ (s : Set K)) ≤
      (Algebra.adjoin o s₀).toSubring.map (gen β s).subtype := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨a, rfl⟩ | hy)
    · exact ⟨algebraMap o _ a, Subalgebra.algebraMap_mem _ a, rfl⟩
    · exact ⟨⟨y, subset_gen β le_rfl hy⟩, Algebra.subset_adjoin hy, rfl⟩
  obtain ⟨a, ha, b, hb, e⟩ := Subfield.mem_closure_iff.1 x.2
  obtain ⟨a, ha', rfl⟩ := hle ha
  obtain ⟨b, hb', rfl⟩ := hle hb
  exact ⟨a, ha', b, hb', Subtype.ext e.symm⟩

theorem descends_to_fg_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Q : Out.PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) → Nonempty (Out.Level Q M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) → ∃ (Ω₀ : Type) (_ : Field Ω₀) (_ : Algebra o Ω₀) (j : Ω₀ →ₐ[o] Ω) (R₀ : Subalgebra o Ω₀) (Q₀ : Out.PolAV (Sp Ω₀)) (φ : Q.A.left ⟶ Q₀.A.left), R₀.FG ∧ (∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) ∧ Q₀.g = Q.g ∧ IsGrpPullback Q.A Q₀.A (spMap j.toRingHom) φ ∧ (letI := Q₀.isAb.comm; GlobalTheory.ZH.HypS Q₀.A Q₀.L) ∧ Nonempty (Out.Level Q₀ M (unitOn (Units.map (algebraMap o Ω₀).toMonoidHom ze))) := by
  intro o K _ _ _ t M ze ⟨w, wd, hw, hwd, hsum, hpol, hadj⟩ ⟨lev⟩
  classical
  let β : o →+* K := algebraMap o K
  let act : Bool → (t.A ⟶ t.A) := fun j => cond j w wd
  obtain ⟨s₀, H₀⟩ := _root_.GlobalTheory.exists_finset_isProjOver_descends K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := _root_.GlobalTheory.LBDescent.exists_lb_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := _root_.GlobalTheory.morphisms_descend_to_large_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ Bool (fun j => (act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := _root_.GlobalTheory.morphisms_descend_to_large_subfield K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * t.g)) (fun a => (lev.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : Bool → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * t.g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  have hpt : ∀ a, (lev.pt a).left ≫ ψ = spMap (gen β s).subtype ≫ (pt₁ a).left := fun a => by
    have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
    have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm
  have hact : ∀ j, (act j).left ≫ ψ = ψ ≫ (act₁ j).left := fun j => by
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  obtain ⟨hab, hdim⟩ := _root_.GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend _ K (gen β s).subtype A₁ t.A ψ hG t.isAb
  obtain ⟨hr, hs, hk⟩ := _root_.GlobalTheory.PolDescent.rigidified_sym_kTriv_descend _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
    t.ample
  letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
  obtain ⟨R₀, hfg, hfrac⟩ := exists_fg_subalgebra β s
  refine ⟨gen β s, inferInstance, inferInstance, ⟨(gen β s).subtype, fun _ => rfl⟩, R₀,
    ⟨A₁, hab, t.g, hdim _ t.smoothDim, L₁, hL₁, hr t.rigid, hs t.sym, hamp, hk t.ktriv⟩, ψ, hfg, hfrac, rfl, hG, ?_, ?_⟩
  · have := t.isAb.comm
    have := hab.comm
    exact hypS_descend (gen β s).subtype hab hG hL₁ t.isLB hL (hact true).symm (hact false).symm hw hwd hsum hpol hadj
  · exact level_descend (gen β s).subtype t A₁ hab _ L₁ hL₁ _ _ _ _ hG hL M _ lev pt₁ hpt

end GlobalTheory.SymLevelDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionValuedFieldTwistedUniformisationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCondition_valuedField_twistedUniformisation : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  first | exact @GlobalTheory.Ex.Trait.LevelClause.level_clause | exact GlobalTheory.Ex.Trait.LevelClause.level_clause | (intros; apply GlobalTheory.Ex.Trait.LevelClause.level_clause <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoValuesConstantOfSameCubeThetaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_values_constant_of_same_cube_theta : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (f : R' →+* R) (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N : NumD F) (k : ℕ) (β : N.Form k) (u : Fˣ) (ν : NumOf D F (N.twist β u)) (ν' : NumOf D' F N) (φ : D.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D.P.L (D'.P.L.pull φ)), IsGrpPullback D.P.A D'.P.A (spMap f) φ → w.IsGen → (∀ x, (ν.eA x).left ≫ φ = (ν'.eA x).left) → ∀ n : ℕ, (∀ x : N.A, ∃ y, y ^ n = x) → (∀ a : N.A, ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0) → ∃ (w' : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ))) (c : Fˣ), w'.IsGen ∧ ∀ x, valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w'.s (fun _ => ν'.J (ν'.eA x).left, fun _ => ν.J (ν.eA x).left)).val = c := by
  first | exact @GlobalTheory.IsoValConst.exists_iso_val_const | exact GlobalTheory.IsoValConst.exists_iso_val_const | (intros; apply GlobalTheory.IsoValConst.exists_iso_val_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelIsoOfValuedAgreementOverFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelIso_of_valued_agreement_over_field : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  first | exact @GlobalTheory.FitMatch.match_of_fit | exact GlobalTheory.FitMatch.match_of_fit | (intros; apply GlobalTheory.FitMatch.match_of_fit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_model_ultrametric_points : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra (FractionRing W) C], CDV W → CExt W (IsLocalRing.maximalIdeal W) C → ∀ (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K] (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) → ∀ (y : Sp K ⟶ Xo.XF c) (b : c.V W₀ →+* W), y ≫ Y.j ≫ Y.s = spMap (algebraMap (FractionRing W) K) ≫ jK W ≫ spMap b → ∀ o : Full D C, FullAt Y (spMap gam ≫ y) o → ∃ (M : Mdl o) (f : W →+* M.W) (χ : Sp M.W ⟶ Y.X) (mp : SABMap M.t Y.t χ), f.Finite ∧ (∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing W) C (algebraMap _ _ x)) ∧ jFK (R := M.W) C ≫ jK M.W ≫ χ = spMap gam ≫ y ≫ Y.j ∧ M.P.U.LG = M.t.PP := by
  first | exact @GlobalTheory.Ex.UnifModel.exists_mdl | exact GlobalTheory.Ex.UnifModel.exists_mdl | (intros; apply GlobalTheory.Ex.UnifModel.exists_mdl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianPullbackLineBundleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_abelian_pullback_line_bundle : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  first | exact @GlobalTheory.Ex.Trait.act_comm_of_torsion | exact GlobalTheory.Ex.Trait.act_comm_of_torsion | (intros; apply GlobalTheory.Ex.Trait.act_comm_of_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidifiedBundleTwoPullbacksCompareStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_bundle_two_pullbacks_compare : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (S S' : Scheme.{0}) (x : S ⟶ Z) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → ∀ (φ : G.left ⟶ G₀.left) (φ' : G'.left ⟶ G₀.left) (w : LB.Iso L (L₀.pull φ)) (w' : LB.Iso L' (L₀.pull φ')) ρ ρ', RigPull G G₀ x φ w ρ ρ₀ → RigPull G' G₀ (f ≫ x) φ' w' ρ' ρ₀ → ∃ (ψ : G'.left ⟶ G.left) (ω : LB.Iso L' (L.pull ψ)), RigPull G' G f ψ ω ρ' ρ ∧ ∀ (k : ℕ) (T₀ : Over Z) (T : Over S) (T' : Over S') (p : T.left ⟶ T₀.left) (q : T'.left ⟶ T.left), p ≫ T₀.hom = T.hom ≫ x → q ≫ T.hom = T'.hom ≫ f → ∀ s₀ s s', Thru w k (T' := T) (T := T₀) p s₀ s → Thru w' k (T' := T') (T := T₀) (q ≫ p) s₀ s' → Thru ω k (T' := T') (T := T) q s s' := by
  first | exact @GlobalTheory.OneBasis.Compare.rigPull_compare | exact GlobalTheory.OneBasis.Compare.rigPull_compare | (intros; apply GlobalTheory.OneBasis.Compare.rigPull_compare <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionNonzeroClosedFibreGeneratesExpansionZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_nonzero_closedFibre_generates_expansion_zero : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : H0 U.LG.L 1, (∃ g, G.hom g = closedPoint V ∧ g ∈ nonzeroLocus σ) → (∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s σ) ∧ ∀ σ' : U.SecGF F 1, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) → ∃ ϑ, U.ExpandsG F 1 σ' ϑ ∧ Prim D Q v ϑ := by
  first | exact @GlobalTheory.Ex.PrimitiveExpansion.main | exact GlobalTheory.Ex.PrimitiveExpansion.main | (intros; apply GlobalTheory.Ex.PrimitiveExpansion.main <;> assumption)
end

