module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnifOfCmp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveOfFormalEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PrimeUnif

theorem exists_cdvr (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (I : Ideal R) [I.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V), CDvr V ∧ Function.Injective φ ∧
      (IsLocalRing.maximalIdeal V).comap φ = I := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · let K := FractionRing R
    let φ : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
    have hφ : Function.Injective φ := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, φ,
      ⟨inferInstance, ?_, charZero_of_injective_ringHom hφ⟩, hφ, ?_⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
    · refine eq_bot_iff.2 fun r hr => ?_
      rw [Ideal.mem_comap, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
        PowerSeries.X_dvd_iff] at hr
      have : algebraMap R K r = 0 := by simpa [φ] using hr
      exact (Ideal.mem_bot).2 (IsFractionRing.injective R K (this.trans (map_zero _).symm))
  · obtain ⟨V, _, _, hV, hc, φ, h1, h2⟩ := exists_complete_discreteValuationRing_of_prime_lt ⊥ I (bot_lt_iff_ne_bot.2 hI)
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    exact ⟨V, inferInstance, inferInstance, inferInstance, φ, ⟨hV, hc, charZero_of_injective_ringHom hφ⟩, hφ, h2⟩

theorem isCPMap_of_eq (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] {A : PolAV (Sp (FractionRing V))}
    {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G'] [Smooth G'.hom] (gen : (Over.pullback (jK V)).obj G' ≅ A.A)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : CP G} {f : Sp V ⟶ S} {F : G'.left ⟶ G.left}
    {hw : F ≫ G.hom = G'.hom ≫ f} (P₁ P₂ : CP G') (e : P₂.L = P₁.L) {w} (h : IsCPMap P₁ P f F hw w) :
    ∃ w', IsCPMap P₂ P f F hw w' := by
  obtain ⟨L, c, s, hs, hr, hc⟩ := P₂
  obtain rfl : L = P₁.L := e
  let P₂ : CP G' := ⟨P₁.L, c, s, hs, hr, hc⟩
  have : Flat (G3 G').hom := by
    show Flat (pullback.fst G'.hom (pullback.fst G'.hom G'.hom ≫ G'.hom) ≫ G'.hom)
    infer_instance
  have h1 : Function.Surjective (pullback.snd G'.hom (jK V)).appTop.hom := by
    have hw : gen.hom.left ≫ A.A.hom = pullback.snd G'.hom (jK V) := Over.w gen.hom
    have : IsIso gen.hom.left := ((Over.forget _).mapIso gen).isIso_hom
    have : IsIso gen.hom.left.appTop := inferInstanceAs (IsIso (gen.hom.left.app ⊤))
    rw [← hw]
    exact surj_comp (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2 (hG _ _ A.isAb).2
  let o : Over.mk (jK V) ⟶ G' := 1
  let o₃ : Over.mk (jK V) ⟶ G3 G' := lift o (lift o o)
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (J), Good P₁.L.L z J → val P₁.sym r z J = val s r z J :=
    ValueForm.gen_unique_of_injective P₁.L.isLB (fun _ _ _ => rfl) (pullback.fst G'.hom (jK V))
      (ValueForm.app_generic_injective _) (pullback.snd _ _)
      (pullback.lift o.left (𝟙 _) ((Over.w o).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) h1
      P₁.sym_gen hs fun y J hJ => by
        rw [pullback.lift_fst]
        exact (P₁.val_sym_one hJ).trans (P₂.val_sym_one hJ).symm
  have ec : ∀ (T : Over (Sp V)) (z : T.left) (J), Good P₁.L.L z J → ∀ x y u : T ⟶ G',
      cubV P₁.c z J x y u = cubV c z J x y u := fun T z J hJ x y u =>
    ValueForm.gen_unique_of_injective P₁.L.isLB (φ := thφ G' (x3 G')) (ε := thε) (φ' := thφ G' (x3 G')) (ε' := thε)
      (fun _ _ _ => rfl) (pullback.fst (G3 G').hom (jK V))
      (ValueForm.app_generic_injective _) (pullback.snd _ _)
      (pullback.lift o₃.left (𝟙 _) ((Over.w o₃).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
      (ValueForm.surjective_cube_baseChange hG _ A.isAb gen) P₁.c.isGen c.isGen
      (fun y J hJ => by
        rw [pullback.lift_fst]
        exact ((isCub_cubV P₁.c (T := Over.mk (jK V)) hJ).face 1 1).trans
          ((isCub_cubV c (T := Over.mk (jK V)) hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨w, h.mul, h.gen, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨a₁, a₂, a₃⟩ := h.vals T z J' J hJ' hJ W hW
  exact ⟨a₁, fun x => (a₂ x).trans (congrArg (W x⁻¹ * ·) (es _ x.left z J' hJ')),
    fun x y u => (a₃ x y u).trans (congrArg (W (x * y * u) * W x * W y * W u * ·) (ec T z J' hJ' x y u))⟩

section Psi
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
  [IsCommMonObj G']
  (psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)))
  (h : ∀ χ, (psi χ).IsGen)

def gtWithPsi {e : ℕ} (g : GtCoord I D e G) : GtCoord I (withPsi D psi h) e G :=
  ⟨g.q, g.q_hom, g.q_flat, g.q_surj, g.q_affine, g.i, g.i_hom, g.isKernel, g.t, g.t_gen, g.t_mul, g.t_unit, g.t_weight⟩

def preWithPsi (U : PreU I D A G) : PreU I (withPsi D psi h) A G :=
  ⟨U.semi, U.gen, U.gen_hom, U.P, U.wA, U.wA_gen, fun e => gtWithPsi psi h (U.gt e), U.gt_q, U.gt_t, U.w, U.w_gen,
    U.w_vals, U.w_compat⟩

def cmpWithPsi {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left} (C : Cmp φ U U' F) :
    Cmp φ (preWithPsi psi h U) U' F :=
  ⟨C.pb, C.wL, C.wL_map, C.β, C.pbB, C.v, C.v_gen, C.xe, C.c_pr, C.lev, C.map_le⟩

theorem exists_move {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left} (C : Cmp φ U U' F)
    (hD : IsPullDeg φ (withPsi D psi h) D') (D₂ : DegPre R) (e : D₂ = withPsi D psi h)
    (h₁ : hD.e.hom.left ≫ pullback.fst _ _ = C.β) (h₂ : HEq hD.w C.v) (h₃ : hD.xe = C.xe) :
    ∃ (U₂ : PreU I D₂ A G) (C₂ : Cmp φ U₂ U' F) (hD₂ : IsPullDeg φ D₂ D'), U₂.P = U.P ∧ U₂.gen = U.gen ∧
      hD₂.e.hom.left ≫ pullback.fst _ _ = C₂.β ∧ HEq hD₂.w C₂.v ∧ hD₂.xe = C₂.xe := by
  subst e
  exact ⟨preWithPsi psi h U, cmpWithPsi psi h C, hD, rfl, rfl, h₁, h₂, h₃⟩

end Psi


set_option maxHeartbeats 1600000 in
theorem exists_setting (hL : Laws) (hL2 : Laws2) (hL3 : Laws3) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G)
    (hW : HypW G P.L.L) (hsp : SplitOver G I) (A : PolAV (Sp (FractionRing R)))
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (g : R →+* V) (hg : Function.Injective g)
    (hI : I ≤ (IsLocalRing.maximalIdeal V).comap g) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap g)).obj G)) (w : _),
      IsCPMap s.P P (spMap g) (pullback.fst G.hom (spMap g)) pullback.condition w := by
  let G' : Over (Sp V) := (Over.pullback (spMap g)).obj G
  have pb : IsGrpPullback G' G (spMap g) (pullback.fst G.hom (spMap g)) := isGrpPullback_pullback G _
  have hS' : IsSemiAbelian G' := IsSemiAbelian.pullback _ G hS
  obtain ⟨P', w, hP', hw⟩ := exists_cp_pull _ _ (spMap g) G G' _ pullback.condition (toBase_mul_pullback G _) P
  have hW' : HypW G' P'.L.L :=
    SymBaseChange.hypS_baseChange _ _ G G' _ _ _ _ P.L.isLB P'.L.isLB pb ⟨w, hw.gen⟩ hW

  let gam : FractionRing R →+* FractionRing V :=
    IsFractionRing.lift (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap V _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  have sq : spMap gam ≫ jK R = jK V ≫ spMap g :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp g _))
  obtain ⟨A', gA, pA, -, mA, tA⟩ := hL.polBaseChange _ _ (spMap gam) A
  have gpA : IsGrpPullback A'.A A.A (spMap gam) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
    have : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
    exact ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have gp' : IsGrpPullback ((Over.pullback (jK V)).obj G') G (spMap gam ≫ jK R)
      (pullback.fst G'.hom (jK V) ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback G' (jK V)).comp pb).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A'.L.pull eA.hom.left) (P'.L.L.pull (pullback.fst G'.hom (jK V))) := by
    rw [hP']
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB (pull_isLB P.L.isLB _) _)
      ((LBIso.symm tA).chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl) (Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ gen.inv.left)
      (Geo.Tor.chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => gen.hom.left) _ _ fun _ => ?_)
      (Geo.Tor.chartPullLinComb P.L.L _ _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) hA
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  obtain ⟨wA, hwA⟩ := wA
  have hpr : IsProper (pullback.snd G'.hom (jK V)) := by
    have hw : eA.hom.left ≫ A'.A.hom = pullback.snd G'.hom (jK V) := Over.w eA.hom
    have : IsIso eA.hom.left := ((Over.forget _).mapIso eA).isIso_hom
    have := A'.isAb.proper
    rw [← hw]; infer_instance

  let m := IsLocalRing.maximalIdeal V
  obtain ⟨E₀, hE₀⟩ := hsp
  let k : R ⧸ I →+* V ⧸ m ^ (0 + 1) := Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp g) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact hI ha)
  obtain ⟨E₁, -, -, -, -, hE₁⟩ := hL3.gtBaseChange _ _ (spMap k) E₀ _ hE₀
  have hc : spMap k ≫ spMap (Ideal.Quotient.mk I) = thick V m 0 ≫ spMap g :=
    (spMap_comp _ k).symm.trans (spMap_comp g (Ideal.Quotient.mk _))
  obtain ⟨e, he, -⟩ := grpPullback_iso (((isGrpPullback_pullback _ (spMap k)).comp
    (isGrpPullback_pullback G (spMap (Ideal.Quotient.mk I)))).congr hc rfl)
    ((isGrpPullback_pullback G' (thick V m 0)).comp pb)
  have := E₁.free
  have := E₁.finite
  obtain ⟨Dat⟩ := isGt_of_iso e hE₁
  obtain ⟨Q₀, -⟩ := exists_tq_of_gtDatum _ E₁ _ Dat
  obtain ⟨P₀, v, hP₀⟩ := exists_isLevelCP m 0 P'
  have hm : (m ^ (0 + 1)).IsMaximal := by rw [zero_add, pow_one]; infer_instance
  have hS₀ : IsSemiAbelian (thickObj V m 0 G') := IsSemiAbelian.pullback _ G' hS'
  have hb : Nonempty (BiTriv P₀.c Q₀.i) := by
    letI : Field (V ⧸ m ^ (0 + 1)) := Ideal.Quotient.field _
    exact @BiextTriv.main (V ⧸ m ^ (0 + 1)) _ E₁.X _ _ _ (thickObj V m 0 G') _ _ hS₀.smooth hS₀.geomConnected
      P₀.L P₀.c Q₀.i Q₀.i_hom
  obtain ⟨w₀, -, hw₀, -, -, hp, -⟩ := hW'
  have hev := EvenTriv.exists_even_cubTriv hL hL2 V G' hS' hpr P' w₀ hw₀ hp _ _ E₁.X Q₀ P₀ _ _
    (IsPullback.of_hasPullback G'.hom (thick V m 0)) v hP₀ hb
  exact ⟨A', ⟨hV, hS', eA, mE, P', wA, hwA, E₁.X, Q₀, P₀, ⟨v, hP₀⟩, hev⟩, w, hw⟩

theorem exists_unif : Laws → Laws2 → Laws3 → Ega → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → SplitOver G I → ThetaNZ G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegData R I) (U : Unif I D A G), U.LG = P.L ∧ U.gen = gen := by
  intro hL hL2 hL3 hE hU R _ _ _ I hR hpi G _ _ P hS hW hsp hθ A gen hgen hA
  have := hR.1.1
  have := hR.2.2.1
  have hI := hR.2.2.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := exists_cdvr R I
  have := hV.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : I.map φ ≤ IsLocalRing.maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨A', s, w, hw⟩ := exists_setting hL hL2 hL3 P hS hW hsp A gen hA hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  obtain ⟨D, U, rfl, rfl⟩ := _root_.GlobalTheory.PreUnifLocal.exists_preU_local hL hL2 hL3 hE hU R I hR hpi G P hS hW hsp A gen hgen hA
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := _root_.GlobalTheory.LN.PreCompare.exists_cmp hL hL2 hE R V I _ hR.1 hB (IsLocalRing.maximalIdeal.isMaximal V).ne_top φ hle D _ A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  obtain ⟨psi, h, Dd, hD, e, h₁, h₂, h₃⟩ := _root_.GlobalTheory.PsiRing.exists_degData_of_thetaNZ hL hL2 hE R I hR V hV φ hφ hc D D' A A' G _ U U' U₀ _ C hU' hθ
  obtain ⟨U₂, C₂, hD₂, eP, eg, k₁, k₂, k₃⟩ := exists_move psi h C hD Dd.toPre e h₁ h₂ h₃
  obtain ⟨U₁, -, hU₁, -⟩ := GlobalTheory.UnifDescent.exists_unif_of_cmp hL hL2 hE R V I _ hR.1 hB hI.ne_top φ hφ hle Dd D' A A' G _ U₂ U' U₀ _ C₂ hD₂
    hU' k₁ k₂ k₃
  exact ⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg CP.L eP), hU₁.1.symm.trans eg⟩

end GlobalTheory.PrimeUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomOfThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.LocalMorAlg

open GlobalTheory.MorAlg

theorem exists_section_local (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y P : Over (Spec (CommRingCat.of V))) (q : P ⟶ Y)
    [IsSeparated q.left] [IsProper Y.hom] [Flat Y.hom] (hP : IsProjBy P.hom)
    (j : ∀ e, (thickObj V (IsLocalRing.maximalIdeal V) e Y).left ⟶ P.left)
    (hq : ∀ e, j e ≫ q.left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e))
    (hj : ∀ e, thickMap V (IsLocalRing.maximalIdeal V) e Y ≫ j (e + 1) = j e) :
    ∃ g : Y ⟶ P, ∀ e, pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e) ≫ g.left = j e := by
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  choose t ht using fun (e : ℕ) => exists_isPull (j e) hH s
  have hv : ∀ e, IsPull (thickMap V (IsLocalRing.maximalIdeal V) e Y) (t (e + 1)) (t e) := fun e =>
    IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)
  choose v hv cv using hv
  have hjV : ∀ e, j e ≫ P.hom = (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom ≫ thick V (IsLocalRing.maximalIdeal V) e := fun e => by
    rw [← Over.w q, ← Category.assoc, hq]
    exact pullback.condition
  have hci : ∀ e, IsClosedImmersion (thick V (IsLocalRing.maximalIdeal V) e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hva : VeryAmpleBy (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (H.pull (j 0)) (t 0) := by
    obtain ⟨w, hw, c⟩ := ht 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1))) _ _ (j 0) (hjV 0) ?_ _ w _
      (hL 0) hw c
    have h₁ : IsClosedImmersion (j 0 ≫ q.left) := by
      rw [hq]
      have := hci 0
      infer_instance
    have h₂ : IsClosedImmersion (j 0) := IsClosedImmersion.of_comp _ q.left
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (hjV 0) ≫
        pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0)) := by
      rw [pullback.lift_fst]
      exact h₂
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0))
  have hpb : ∀ e, IsPullback (thickMap V (IsLocalRing.maximalIdeal V) e Y) (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom (thickObj V (IsLocalRing.maximalIdeal V) (e + 1) Y).hom
      (thickTrans V (IsLocalRing.maximalIdeal V) e) := fun e => by
    refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) (e + 1))) (h₂₂ := thick V (IsLocalRing.maximalIdeal V) (e + 1))
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.LocalEmb.exists_projective_of_formal_embedding V (fun e => thickObj V (IsLocalRing.maximalIdeal V) e Y)
    (fun e => thickMap V (IsLocalRing.maximalIdeal V) e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick V (IsLocalRing.maximalIdeal V) e))))
    (fun e => H.pull (j e)) v (fun e => ⟨hL e, hv e⟩) n t cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy V P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => heq d F hF fun e k => by
      rw [← hjV]
      exact (ht e).eqn P.hom hH hF h0 k
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections V P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjV]
    exact (hb e).w
  let φ' : B ⟶ P := Over.homMk φ hφ
  have hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e) := fun e => by
    rw [← hq, ← hbφ]
    exact (Category.assoc _ _ _).symm
  have hB : IsProper ((φ' ≫ q).left ≫ Y.hom) := by
    rw [Over.w]
    exact GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ ⟨H', hH', n, s', hs'⟩
  have hp : IsProper (φ' ≫ q).left := IsProper.of_comp _ Y.hom
  have hiso : IsIso (φ' ≫ q) := GlobalTheory.IsoLimit.main V B Y (φ' ≫ q) fun e => by
    have h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q)).left = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [← hbp e, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]
        exact (hb e).isoPullback_hom_snd
    have h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q))) :=
      @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩
  rw [← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]
  exact hbφ e

theorem exists_hom_local : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y Z : Over (Spec (CommRingCat.of V))), IsProjBy Y.hom → IsProjBy Z.hom → Flat Y.hom → ∀ f : ∀ e, (thickObj V (IsLocalRing.maximalIdeal V) e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG (IsLocalRing.maximalIdeal V) e Y).left ≫ Y.hom) → (∀ e, thickMap V (IsLocalRing.maximalIdeal V) e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Z, ∀ e, (fstG (IsLocalRing.maximalIdeal V) e Y).left ≫ g.left = f e := by
  intro V _ _ _ _ _ Y Z hY hZ hfl f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hZ
  have hsep : IsSeparated (fst Y Z).left := inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))
  obtain ⟨g, hg⟩ := exists_section_local V Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor V Y Z hY hZ)
    (fun e => pullback.lift (pullback.fst Y.hom (thick V _ e)) (f e) (hf e).symm)
    (fun e => pullback.lift_fst _ _ _) (fun e => by
      apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])
  refine ⟨g ≫ snd Y Z, fun e => ?_⟩
  have := congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)
  exact ((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)

theorem comp_eq_of_compatible {R : Type} [CommRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R)))
    {Z T : Scheme.{0}} (f : ∀ e, (thickObj R I e Y).left ⟶ Z) (hc : ∀ e, thickMap R I e Y ≫ f (e + 1) = f e)
    {e n : ℕ} (a : T ⟶ (thickObj R I e Y).left) (b : T ⟶ (thickObj R I n Y).left)
    (h : a ≫ pullback.fst Y.hom (thick R I e) = b ≫ pullback.fst Y.hom (thick R I n)) : a ≫ f e = b ≫ f n := by
  have up : ∀ (e : ℕ) (a : T ⟶ (thickObj R I e Y).left) (k : ℕ), e ≤ k → ∃ a' : T ⟶ (thickObj R I k Y).left,
      a' ≫ pullback.fst Y.hom (thick R I k) = a ≫ pullback.fst Y.hom (thick R I e) ∧ a' ≫ f k = a ≫ f e := by
    intro e a k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨a, rfl, rfl⟩
    | succ k _ ih =>
      obtain ⟨a', h₁, h₂⟩ := ih
      have t : thickMap R I k Y ≫ pullback.fst Y.hom (thick R I (k + 1)) = pullback.fst Y.hom (thick R I k) :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      exact ⟨a' ≫ thickMap R I k Y, (Category.assoc _ _ _).trans ((congrArg (a' ≫ ·) t).trans h₁),
        (Category.assoc _ _ _).trans ((congrArg (a' ≫ ·) (hc k)).trans h₂)⟩
  obtain ⟨a', ha, ha'⟩ := up e a (e + n) (by omega)
  obtain ⟨b', hb, hb'⟩ := up n b (e + n) (by omega)
  have : IsClosedImmersion (thick R I (e + n)) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hm : Mono (pullback.fst Y.hom (thick R I (e + n))) := inferInstance
  have e' : a' = b' := hm.right_cancellation _ _ (ha.trans (h.trans hb.symm))
  rw [← ha', ← hb', e']

theorem existsUnique_hom_of_thickenings : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), GlobalTheory.AbLaw.IsProjBy Y.hom → GlobalTheory.AbLaw.IsProjBy Z.hom → Smooth Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG I e Y).left ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃! g : Y ⟶ Z, ∀ e, (fstG I e Y).left ≫ g.left = f e := by
  intro _ _ R _ _ _ _ I hI _ _ Y Z hY hZ hsm f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hZ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hJ : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson _
  have hρ : ∀ e, ∃ ρ : (thickObj R (IsLocalRing.maximalIdeal R) e Y).left ⟶ (thickObj R I e Y).left,
      ρ ≫ pullback.fst Y.hom (thick R I e) = pullback.fst Y.hom (thick R (IsLocalRing.maximalIdeal R) e) := fun e =>
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ GlobalTheory.LocalEmb.fac (Ideal.pow_right_mono hIm (e + 1)))
      (by rw [Category.assoc, GlobalTheory.LocalEmb.fac_quo]; exact pullback.condition), pullback.lift_fst _ _ _⟩
  choose ρ hρ using hρ
  obtain ⟨g, hg⟩ := exists_hom_local R Y Z hY hZ inferInstance (fun e => ρ e ≫ f e)
    (fun e => (Category.assoc _ _ _).trans ((congrArg (ρ e ≫ ·) (hf e)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Y.hom) (hρ e)))))
    (fun e => (Category.assoc _ _ _).symm.trans (comp_eq_of_compatible I Y f hc _ _
      ((Category.assoc _ _ _).trans ((congrArg (thickMap R _ e Y ≫ ·) (hρ (e + 1))).trans
        (((pullback.lift_fst _ _ _).trans (Category.comp_id _)).trans (hρ e).symm)))))
  have key : ∀ e, (fstG I e Y).left ≫ g.left = f e := fun e => by
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.fst Y.hom (thick R I e) ≫ Y.hom)
    have pY' : IsProper Y'.hom := inferInstanceAs (IsProper (pullback.fst Y.hom (thick R I e) ≫ Y.hom))
    let u : Y' ⟶ Z := Over.homMk (pullback.fst Y.hom (thick R I e) ≫ g.left)
      ((Category.assoc _ _ _).trans (congrArg (pullback.fst Y.hom (thick R I e) ≫ ·) (Over.w g)))
    let u' : Y' ⟶ Z := Over.homMk (f e) (hf e)
    refine congrArg CommaMorphism.left (GlobalTheory.hom_eq_of_thickenings_of_isProper R _ hJ Y' Z u u' fun n => ?_)
    obtain ⟨l, hl⟩ : ∃ l : pullback Y'.hom (thick R (IsLocalRing.maximalIdeal R) n) ⟶
        (thickObj R (IsLocalRing.maximalIdeal R) n Y).left,
        l ≫ pullback.fst Y.hom (thick R (IsLocalRing.maximalIdeal R) n) =
          pullback.fst Y'.hom (thick R (IsLocalRing.maximalIdeal R) n) ≫ pullback.fst Y.hom (thick R I e) :=
      ⟨pullback.lift _ (pullback.snd _ _) ((Category.assoc _ _ _).trans pullback.condition), pullback.lift_fst _ _ _⟩
    have h₁ := comp_eq_of_compatible I Y f hc (l ≫ ρ n) (pullback.fst Y'.hom (thick R (IsLocalRing.maximalIdeal R) n))
      ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (hρ n)).trans hl))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.left) hl.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (l ≫ ·) (hg n)).trans ((Category.assoc _ _ _).symm.trans h₁))))
  exact ⟨g, key, fun g' hg' => GlobalTheory.hom_eq_of_thickenings_of_isProper R I (hIm.trans hJ) Y Z g' g
    fun e => (hg' e).trans (key e).symm⟩

end GlobalTheory.LocalMorAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeriesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierSeries_product_eq_product_series : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  first | exact @GlobalTheory.ZH.SeriesProd.main | exact GlobalTheory.ZH.SeriesProd.main | (intros; apply GlobalTheory.ZH.SeriesProd.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusOnTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_on_torsion_alt : ∀ (k : Type) [Field k] [IsAlgClosed k] (p l : ℕ) [Fact p.Prime] [CharP k p], l.Prime → l ≠ p → ∀ (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), AmpleCub G L → ∀ (F : End G) (q : ℕ), 2 ≤ q → FrobG G F q → ∃ (t a m C : ℕ) (P : Polynomial ℤ) (W : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)), 1 ≤ m ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < (q : ℝ) ^ m) ∧ (∀ x ∈ W, x ≫ ((F ^ m).asHom) = x ^ (q ^ m)) ∧ (∀ n, Finite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ l ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : W // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ (x : (𝟙_ (Over (Sp k)) ⟶ G)) n, x ^ l ^ n = 1 → polyPt (F ^ m) P x ∈ W) ∧ (g ≤ t + a → Nonempty (TorusExtension G)) := by
  first | exact @GlobalTheory.SS.frobenius_on_torsion | exact GlobalTheory.SS.frobenius_on_torsion | (intros; apply GlobalTheory.SS.frobenius_on_torsion <;> assumption)
end

