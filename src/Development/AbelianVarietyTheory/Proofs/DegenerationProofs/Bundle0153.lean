module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesSymmetryValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPartIso_carries_symmetry_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x, (N'.σ (f x) : F) * wVal ν ν' w f x = (N.σ x : F) * wVal ν ν' w f x⁻¹ := by
  first | exact @GlobalTheory.AbPartSym.sym_values | exact GlobalTheory.AbPartSym.sym_values | (intros; apply GlobalTheory.AbPartSym.sym_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataDescendsFromCompleteDVR
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ArcDataDescent


set_option maxHeartbeats 3200000 in
theorem hasArcData_descends : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → ∀ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t), P.TorsionIso → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ g : R →+* V, Function.Injective g → I.map g ≤ IsLocalRing.maximalIdeal V → ¬ IsUnit (g u) → (∀ x, x ≠ 0 → IsUnit (g (f x))) → Y.HasArcData a (IsLocalRing.maximalIdeal V) (g.comp f) (g u) (spMap g ≫ χ) → Y.HasArcData a I f u χ := by
  intro hL h2 h3 h4 h5 h6 hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a R _ _ _ _ I f u hR _ hf χ y hy t m P hT V _ _ _ hV g hg hI
    _ _ hA
  letI := H.starRing
  obtain ⟨hV₁, hV₂, -⟩ := hV
  have hV : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV₂⟩
  have := hR.1
  have := hR.2.2.1
  obtain ⟨t', m₀, P', hD, bc, mbc, hPU, hm₀, xl, el⟩ :=
    exists_pelUnif_pull h3.cubePull hL.polBaseChange h4.unifBaseChange h5 hR hV t P g hg hI
  obtain ⟨m', hm'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₀
  obtain ⟨W₁⟩ := (Y.hasArcData_iff a _ _ _ _).1 hA
  obtain ⟨W, rfl, k₁, k₂⟩ := WitnessMove.exists_wit h4.unifBaseChange h5 h6.unifUniq (qkPullExists hL.globalFns) hV W₁
    t' m' P'
  obtain rfl : m' = W.m := (eq_of_heq k₁).symm
  obtain rfl : P' = W.P := (eq_of_heq k₂).symm
  have hm : W.m.φ = (bc.hom.left ≫ pullback.fst t.G.hom (specOf g)) ≫ m.φ := by rw [hm', hm₀]
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  have gD := pull_grp hD
  obtain ⟨φ, gφ, hφ, wφ⟩ := exists_desc_pol hL h2 hH f hg a.D₀.P P.D.toPre.P W.P.D.toPre.P gD s1 ⟨hD.w, hD.w_gen⟩
    ⟨W.w, s2⟩ (fun F _ _ i₁ i₂ => agree hL h2 h5 hR hV hf hg y hy m P hT W hD bc mbc hPU hm xl el F i₁ i₂)
  have he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A := (cubeMapOf gφ).e_comm
  obtain ⟨w, gw, rw'⟩ := Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap f) a.D₀.P.A P.D.toPre.P.A φ he
    ⟨a.D₀.P.L, a.D₀.rig, a.D₀.P.isLB, a.D₀.rig_gen⟩ ⟨P.D.toPre.P.L, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩ wφ
  have pw := (isGen_iff w).1 gw
  have pD := (isGen_iff hD.w).1 hD.w_gen
  obtain ⟨w', T⟩ := exists_comp P.D.toPre.P.isLB w hD.w pw pD a.D₀.P.isLB W.P.D.toPre.P.isLB
  have tr : ∀ {F : Type} [Field F] {K : Type} [Fintype K] {pt : K → (Sp F ⟶ W.P.D.toPre.P.A.left)}
      {pt₀ : K → (Sp F ⟶ a.D₀.P.A.left)} {ε : K → ℤ} (s : LB.Gen (LB.LinComb W.P.D.toPre.P.L pt ε))
      (s₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ ε)) (x : F), GenRel w' s s₀ x ↔ GenRel W.w s s₀ x := by
    have r₀ := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.D.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le φ (spMap f) he a.D₀.P.L) (fun _ => rfl)).1 rw'
    have r₂ := T.pmaps_comp P.D.toPre.P.isLB (fun _ => hD.he) r₀ (pmaps_rig' hD)
    rw [← spMap_comp] at r₂
    have g' := (isGen_iff w').2 (T.pgen_comp P.D.toPre.P.isLB pw pD)
    have key : ∀ (ψ : W.P.D.toPre.P.A.left ⟶ a.D₀.P.A.left) (v : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ψ)), ψ = W.φ →
        v.IsGen → PMaps v (K := PUnit) (fun _ => eSec W.P.D.toPre.P.A) (fun _ => eSec a.D₀.P.A) (fun _ => 1)
          W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) →
        ∀ {F : Type} [Field F] {K : Type} [Fintype K] {pt : K → (Sp F ⟶ W.P.D.toPre.P.A.left)}
          {pt₀ : K → (Sp F ⟶ a.D₀.P.A.left)} {ε : K → ℤ} (s : LB.Gen (LB.LinComb W.P.D.toPre.P.L pt ε))
          (s₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ ε)) (x : F), GenRel v s s₀ x ↔ GenRel W.w s s₀ x := by
      rintro _ v rfl gv pv F _ K _ pt pt₀ ε s s₀ x
      rw [rigidified_iso_unique hL.globalFns W.P.D.toPre.P a.D₀.P.isLB W.φ v W.w gv s2 _ _
        ((maps_iff v _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) _
          (rigPull_le W.φ (spMap (g.comp f)) W.he a.D₀.P.L) (fun _ => rfl)).2 pv) s3]
    intro F _ K _ pt pt₀ ε s s₀ x
    exact key _ w' hφ g' r₂ s s₀ x
  let xD : W.P.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  have := P.D.toPre.P.isAb.smooth
  have := a.D₀.P.isAb.proper
  let gam : FractionRing R →+* FractionRing V :=
    IsFractionRing.lift (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap V _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  refine ⟨t, m, P, φ, he, w, W.e.trans xD, gφ, gw, rw', fun x => ?_, fun z => ?_, fun F _ _ _ _ uF ha hu => ?_⟩
  · refine ext_of_injective hg gD.1 a.D₀.P.A.hom ?_ ?_
    · rw [Category.assoc, gφ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, gφ.1.w]
    · rw [← Category.assoc, ← act_proj hD (el x), Category.assoc, hφ, s4 x, ← Category.assoc, hφ]
  · refine ext_of_injective (p := 𝟙 _) (p' := 𝟙 _) hg (IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩) a.D₀.P.A.hom ?_ ?_
    · rw [Category.assoc, gφ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · have k := hD.c_pr (W.e z)
      refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) k.symm)).trans ?_
      rw [Category.assoc, hφ, s5 z, spMap_comp, Category.assoc]
  · obtain ⟨F', _, _, σ, ρ, hσρ⟩ := exists_common_field (algebraMap (FractionRing R) F) gam
    letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap (FractionRing R) F)).toAlgebra
    letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap (FractionRing O') F)).toAlgebra
    letI : Algebra (FractionRing V) F' := ρ.toAlgebra
    have hF : ∀ r : R, algebraMap (FractionRing R) F' (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) (g r)) := fun r =>
      (RingHom.congr_fun hσρ _).trans (congrArg ρ (hgam r))
    have ha' : ∀ x, algebraMap (FractionRing O') F' (algebraMap O' _ x) =
        algebraMap (FractionRing R) F' (algebraMap R _ (f x)) := fun x => congrArg σ (ha x)
    have hu' : σ uF = algebraMap (FractionRing R) F' (algebraMap R _ u) := congrArg σ hu
    have hj := jFK_comm hF
    have jR : jFK (R := R) F' = spMap σ ≫ jFK (R := R) F := spMap_comp _ _
    have jO : jFK (R := O') F' = spMap σ ≫ jFK (R := O') F := spMap_comp _ _
    refine ⟨fun z => ?_, fun yF hyF k p₀ s hs q₀ q x e₁ e₂ e₃ e₄ => ?_⟩
    · have k := (s6 F' (σ uF) (fun x => (ha' x).trans (hF _)) (hu'.trans (hF _))).1 z
      obtain ⟨n₁, n₂⟩ := pmaps_psi' hD hj (χ' := W.e z) rfl
      have k' := (genRel_transfer T P.D.toPre.P.isLB W.P.D.toPre.P.isLB (fun _ => n₁) n₂ _ _).2 ((tr _ _ _).2 k)
      rw [← map_zpow₀] at k'
      refine (genRel_pull_iff σ w _ _ _).1 ((genRel_congr P.D.toPre.P.isLB a.D₀.P.isLB w ?_ ?_
        (DVR.pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen _) _)
        (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen _) _) _)
        (DVR.pullGen_isGen _ _ _ _ (a.D₀.psi_gen _) _)
        (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (a.D₀.psi_gen _) _) _)
        (fun p J hJ => ?_) (fun p J hJ => ?_) _).1 k')
      · exact funext fun _ => (congrArg (· ≫ _) jR).trans (Category.assoc _ _ _)
      · exact funext fun _ => (congrArg (· ≫ _) jO).trans (Category.assoc _ _ _)
      · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm)
        exact congrArg (fun r => val (P.D.toPre.psi (hD.xe (W.e z))) r p J)
          ((congrArg (𝟙 _ ≫ ·) jR).trans (Category.assoc _ _ _).symm)
      · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm)
        exact congrArg (fun r => val (a.D₀.psi z) r p J) ((congrArg (𝟙 _ ≫ ·) jO).trans (Category.assoc _ _ _).symm)
    · have hk : 1 ≤ k := by
        rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact l.A_pos
        · exact le_trans (by norm_num) l.three_le
      obtain ⟨q₀', hq₀, -⟩ := TorusExt.existsUnique_qkExt a.bimult σ (F' := F') rfl q₀
      obtain ⟨q', hq, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ (F' := F') rfl q
      let x' : TFK (R := R) F' ⟶ P.A.A := Over.homMk (spMap σ ≫ x.left) (by
        have w₂ : x.left ≫ P.A.A.hom = jFK (R := R) F := Over.w x
        show (spMap σ ≫ x.left) ≫ P.A.A.hom = jFK (R := R) F'
        rw [Category.assoc, w₂, jR])
      let σ' : F →ₐ[FractionRing R] F' := ⟨σ, fun _ => rfl⟩
      refine (TorsionExt.qkToAkU_iff_of_qkExt ⟨hL, h2, h3, h4, h5⟩ R I hR P.D P.A t.G t.semi P.U F F' σ' k hk q q' x x' hq
        rfl).2 ?_
      obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv hL h2 R V g P.D.toPre W.P.D.toPre hD P.D.tau_bimult W.P.D.tau_bimult F' hF k
      obtain ⟨k₁, k₂⟩ := (hτ q' _).1 rfl
      refine toA_down hL hR hV m P W hD bc mbc hPU hm F' hF (σ uF) ha' hu' (spMap σ ≫ yF)
        (by rw [Category.assoc, hyF, jR, Category.assoc]) k p₀ s hs q₀' q' (τ q') x' (ArcSpecialise.qkExt_trans e₁ hq₀)
        k₁ k₂ ?_ (fun z => ?_) ?_
      · rw [k₁, AddEquiv.symm_apply_eq, hq.1, hq₀.1]; exact e₂
      · obtain ⟨n₁, n₂⟩ := pmaps_of_isPullGtF k₂ (χ' := W.e z) rfl
        refine (tr _ _ _).1 ((genRel_transfer T P.D.toPre.P.isLB W.P.D.toPre.P.isLB n₁ n₂ _ _).1 ?_)
        rw [← map_zpow₀, hq₀.1]
        exact (genRel_congr P.D.toPre.P.isLB a.D₀.P.isLB w (gtφ_ext rfl hq _) (gtφ_ext rfl hq₀ _) (q'.g.isGen _)
          (DVR.pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (DVR.pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
          (fun p J hJ => val_corr hJ (hq.2.2 _) _) (fun p J hJ => val_corr hJ (hq₀.2.2 _) _) _).2
          ((genRel_pull_iff σ w _ _ _).2 (e₃ z))
      · show (spMap σ ≫ x.left) ≫ _ = _
        rw [Category.assoc, e₄, Category.assoc]

end GlobalTheory.ArcDataDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumPullbackRescaledMatchesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcDatum_pullback_rescaled_matches : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] (f : O' →+* R) (D' : DegPre R) (hD : IsPullDeg f a.D₀ D') (u₀ : R) (uK : (FractionRing R)ˣ), (uK : FractionRing R) = algebraMap R _ u₀ → ∀ (q : D'.X → (FractionRing R)ˣ) (Φ : D'.P.A.left ⟶ a.D₀.P.A.left), Φ = PsiEvenPull.proj hD → (∀ y, q y = uK ^ (a.be (hD.xe y) (hD.xe y) / 2)) → ∃ (_ : Module (𝓞 E) (TauTwist.rescale D' q).X) (oW : letI := H.starRing; (TauTwist.rescale D' q).OAct (𝓞 E)) (he : _) (w : _) (e : _), GlobalTheory.LN.Match a f u₀ (TauTwist.rescale D' q) oW Φ he w e ∧ (∀ y, hD.xe (e y) = y) ∧ (TauTwist.rescale D' q).PsiEven ∧ (TauTwist.rescale D' q).TauBimult := by
  first | exact @GlobalTheory.RescaleMatch.exists_match_rescale | exact GlobalTheory.RescaleMatch.exists_match_rescale | (intros; apply GlobalTheory.RescaleMatch.exists_match_rescale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionLabelsActionCompat
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel
open GlobalTheory.TorusExt

theorem b_eq_of_equiv {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {j : ℕ} (hj : 0 < j) {p p' : QkPt D F j}
    (h : QkPt.Equiv D F p p') (hy : p.y = 0) (hy' : p'.y = 0) : p'.g.b = p.g.b := by
  letI := gtGroup D F
  obtain ⟨z, h₁, t, ht, h₂⟩ := h
  rw [hy, hy', zero_add] at h₁
  have hz : z = 0 := by
    have : (j : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h₁.symm
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hj.ne')
  obtain ⟨z₀, hz₀, t₀, ht₀, ht₁⟩ := qk_equiv_refl hB p
  have hz₀' : z₀ = 0 := by
    have h : j • z₀ = 0 := add_left_cancel (hz₀.symm.trans (add_zero _).symm)
    have h' : (j : ℤ) • z₀ = 0 := by rw [natCast_zsmul]; exact h
    exact (smul_eq_zero.1 h').resolve_left (by exact_mod_cast hj.ne')
  have htzero : t = 0 := by
    have he := (isAdd_iff_eq _ _ _).1 ht₁
    have hz0 : t₀ = 0 := add_left_cancel (he.symm.trans (add_zero _).symm)
    exact (isIota_unique (hz ▸ ht) (hz₀' ▸ ht₀)).trans hz0
  have he := (isAdd_iff_eq _ _ _).1 h₂
  rw [he, htzero, add_zero]

theorem act_compat_on_torsion : Laws → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (A : ArcF D R C) (o : Full D C) (M : Mdl o), M.P.TorsionIso → ∀ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : A.N.Form k) (u r : Cˣ) (J : NumD.Iso (A.N.twist β u) N') (j : ℕ), 0 < j → r ^ j = u → (∀ x (p : (A.N.twist β u).QT j) (q' : N'.QT j) p' z, TwRel β u r (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev j x).left ≫ M.φ → M.P.ToA C j p' z) → ∀ (x : 𝓞 E) (b : A.N.A), b ^ j = 1 → J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' M.P.oD.onB x (J.φ b) := by
  intro hL hBr E _ _ _ H D R _ _ C _ _ _ A o M hT N' ν' k β u r J j hj hr hlab x b hb
  letI := H.starRing
  have hG := hL.globalFns
  have hB := A.bimult
  have hB' : M.P.D.toPre.TauBimult := M.P.D.tau_bimult
  obtain ⟨-, -, -, -, br⟩ := hBr R A.D₀ A.even A.bimult C A.N A.ν
  obtain ⟨-, -, -, -, br'⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even hB' C N' ν'
  obtain ⟨e1, -, e3⟩ := br j
  obtain ⟨-, e2', e3'⟩ := br' j
  obtain ⟨τ, hτ, hQ, -⟩ := (twJ_mulEquiv C A.N N' k β u J).1 r j hr
  obtain ⟨f, f1, -, f3, -, f5, -⟩ := hT C j hj

  have actzero : ∀ {V : Type} [CommRing V] [IsDomain V] {D₁ : DegPre V}
      {O : Type} [CommRing O] [StarRing O] [Module O D₁.X]
      [Algebra (FractionRing V) C] (hB₁ : D₁.TauBimult) (oa : D₁.OAct O)
      (a : O) (p : QkPt D₁ C j), p.y = 0 →
      ∃ q : QkPt D₁ C j, q.y = 0 ∧ q.g.b = p.g.b ≫ oa.onB.act a ∧ QkAct oa a p q := by
    intro V _ _ D₁ O _ _ _ _ hB₁ oa a p hy
    letI := gtGroup D₁ C
    obtain ⟨z, hz, t, ht, ha⟩ := qk_equiv_refl hB₁ p
    have hz' : z = 0 := by
      have h : j • z = 0 := add_left_cancel (hz.symm.trans (add_zero _).symm)
      have h' : (j : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h
      exact (smul_eq_zero.1 h').resolve_left (by exact_mod_cast hj.ne')
    have ht' : t = 0 := by
      have he := (isAdd_iff_eq _ _ _).1 ha
      exact add_left_cancel (he.symm.trans (add_zero _).symm)
    have iz : GtPtF.IsIota (D := D₁) (F := C) 0 0 := by simpa [hz', ht'] using ht
    obtain ⟨g, hg, hi⟩ := p.eq
    have hp : j • p.g = 0 := by
      have hg' := (isNsmul_iff_eq _ _ _).1 hg
      have hi' : g = 0 := isIota_unique (hy ▸ hi) iz
      exact hg'.symm.trans hi'
    have hq : j • gtSmul hG oa a p.g = 0 := by
      change j • (gtSmulHom hG oa C a) p.g = 0
      rw [← map_nsmul (gtSmulHom hG oa C a), hp, map_zero]
    let q : QkPt D₁ C j := ⟨0, gtSmul hG oa a p.g, 0,
      (isNsmul_iff_eq _ _ _).2 hq.symm, iz⟩
    exact ⟨q, rfl, gtSmul_b hG oa a p.g, ⟨q, by simp [q, hy], gtAct_gtSmul hG oa a p.g, qk_equiv_refl hB₁ q⟩⟩

  have key : ∀ (v : D.La) (p : QkPt A.D₀ C j), QkPt.Equiv A.D₀ C (A.I.ev j v) p → p.y = 0 →
      ∃ p' : QkPt M.P.D.toPre C j, p'.y = 0 ∧ p'.g.b = ν'.eA (J.φ (A.ν.eA.symm p.g.b)) ∧
        (f p').left = (o.I.ev j v).left ≫ M.φ := by
    intro v p hp hy
    obtain ⟨q, hq, -⟩ := e1 p
    obtain ⟨p', hp'⟩ := e2' (τ q)
    obtain ⟨pv, hpv⟩ := e2' (τ (A.q j v))
    have hE : QkPt.Equiv _ C pv p' := (e3' _ _ _ _ hpv hp').2 ((hQ _ _).1 ((e3 _ _ _ _ (A.hq j v) hq).1 hp))
    obtain ⟨t, t1, t2, t3⟩ := (hτ q _).1 rfl
    obtain ⟨s, s1, s2, s3⟩ := (hτ (A.q j v) _).1 rfl
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev j v).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (f1 _ _).1 (hlab v s _ pv z s1 s2 s3 hpv rfl)
    refine ⟨p', ?_, ?_, ?_⟩
    · have h0 : q.1.1.toAdd = 0 := A.ν.eX.injective (hq.1.trans (hy.trans (map_zero _).symm))
      rw [← hp'.1, t2, t1.1]
      erw [h0, map_zero, map_zero]
    · rw [← hp'.2.1, t3.1, t1.2.1, ← hq.2.1, MulEquiv.symm_apply_apply]
    · rw [← (f3 _ _).2 hE, ← hz]
      rfl
  obtain ⟨p₀, y₀, b₀⟩ := exists_qkPt_of_torsion (F := C) hB hj.ne' (b := A.ν.eA b) (by rw [← map_pow, hb, map_one])
  obtain ⟨v, hv⟩ := A.I.onto j hj p₀
  obtain ⟨p₁, y₁, a₀, hact₀⟩ := actzero hB A.oa x p₀ y₀
  have hv₁ : QkPt.Equiv A.D₀ C (A.I.ev j (x • v)) p₁ :=
    (qkAct_iff_of_equiv hB hG A.oa hv (A.I.lin j hj x v)).1 hact₀
  obtain ⟨p₀', c₀, d₀, g₀⟩ := key v p₀ hv y₀
  obtain ⟨p₁', c₁, d₁, g₁⟩ := key (x • v) p₁ hv₁ y₁
  obtain ⟨p₂', c₂, a₁, hact₁⟩ := actzero hB' M.P.oD x p₀' c₀
  have hf : f p₂' = f p₁' := by
    rw [f5 x _ _ hact₁]
    refine Over.OverMorphism.ext ?_
    rw [g₁, Over.comp_left, g₀, o.I.lin, Over.comp_left, Category.assoc, Category.assoc, M.act]
  have hb' := b_eq_of_equiv hB' hj ((f3 _ _).1 hf) c₂ c₁
  rw [d₁, a₁, a₀, d₀, b₀, MulEquiv.symm_apply_apply] at hb'
  unfold actV
  rw [← hb', MulEquiv.symm_apply_apply]

end GlobalTheory.Relabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedPointMemRange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) (e : ℕ) :
    IsLocalRing.closedPoint R ∈ Set.range (thick R I e) := by
  have h := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I ^ (e + 1)))
  refine h.ge ?_
  rw [Ideal.mk_ker]
  exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans (IsLocalRing.le_maximalIdeal hI)

theorem triv_of_forall_thick (hG : GlobalFnsSt) (hS : SecAlgSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {I : Ideal V} (hI : I ≠ ⊤) (hV : IsAdicComplete I V) (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) (N : LB B.left) (hN : N.IsLB)
    (ht : ∀ e, Triv (N.pull (fstG I e B).left)) : Triv N := by
  let o : Spec (CommRingCat.of V) ⟶ B.left := (η[B]).left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local N hN (K := PUnit) (fun _ => o) (fun _ => 1)
  have pb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) :=
    fun e => IsPullback.of_hasPullback B.hom (thick V I e)
  choose t tg tv using fun e => AbTriv.exists_normalised hN ho c hc (pb e) (ht e)
  have tm : ∀ e, thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have compat : ∀ e z J, Good N z J → val (t (e + 1)) (thickMap V I e B) z J = val (t e) (𝟙 _) z J := by
    intro e z J hJ
    let a := (pb e).lift (thick V I e ≫ o) (𝟙 _) (by rw [Category.assoc, ho, Category.comp_id, Category.id_comp])
    have a₁ : a ≫ (fstG I e B).left = thick V I e ≫ o := (pb e).lift_fst _ _ _
    have key := gen_unique' hN (fun U _ k => by simp only [tm e]) (thickObj V I e B).hom a ((pb e).lift_snd _ _ _)
      (hG _ _ (TLinPf.isAb_pullback (thick V I e) B hB)).2 (tg e)
      (DVR.pullGen_isGen _ _ _ _ (tg (e + 1)) (thickMap V I e B))
      (fun y J hJ => (tv e _ a _ y J hJ a₁).trans ((val_pull hJ _ _ _).trans
        (tv (e + 1) _ _ _ y J hJ (by rw [Category.assoc, tm e, a₁]))).symm) _ (𝟙 _) z J hJ
    rw [val_pull hJ, Category.id_comp] at key
    exact key.symm
  obtain ⟨s, hs, -⟩ := hS V I hV B hB.smooth hp N hN (fun e => genSec (t e) (tg e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (compat e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have := hB.proper
  have top : nonzeroLocus s = ⊤ := AbTriv.eq_top_of_closed_fibre B.hom _ fun x hx => by
    have hm : x ∈ Set.range (pullback.fst B.hom (thick V I 0)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact closedPoint_mem_range hI 0
    obtain ⟨z, rfl⟩ := hm
    choose J hJ using fun ψ : ((Over.map (thick V I 0)).obj (thickObj V I 0 B)).left ⟶ B.left =>
      exists_chart hN (ψ z)
    refine (TwistZero.mem_nonzeroLocus_iff s (fstG I 0 B).left z hJ).2 ?_
    rw [hs 0 z J hJ, sval_genSec _ _ _ z hJ]
    exact Units.isUnit _
  refine AbTriv.triv_of_pull_id (TwistZero.triv_of_sec hN s fun y J hJ => ?_)
  exact (TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)

theorem triv_pull_of_gen {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (r : Z ⟶ Y') (π : Z ⟶ Y)
    (hc : ∀ k, (r ≫ φ' k) ≫ F = π ≫ φ k) : Triv ((LB.LinComb L φ ε).pull π) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨t, ht, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' _ (DVR.pullGen_isGen _ _ _ _ ha r)
  refine (KerPow.pull_iff φ ε π).2 ?_
  rw [← (funext hc : (fun k => (r ≫ φ' k) ≫ F) = fun k => π ≫ φ k)]
  exact ⟨t, ht⟩

section Level
variable {S S' Z : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
  {f : S' ⟶ S} {F : B'.left ⟶ B.left}


omit [IsCommMonObj B] [IsCommMonObj B'] in
theorem toBase_mul (h : IsGrpPullback B' B f F) (T : Over S') (x y : T ⟶ B') :
    toBase h.1.w (x * y) = toBase h.1.w x * toBase h.1.w y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem triv_theta (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ (G3 B).left) (z : Z ⟶ S') (hz : π ≫ (G3 B).hom = z ≫ f) :
    Triv ((Theta B L).pull π) := by
  let ρ : Over.mk ((Over.mk z).hom ≫ f) ⟶ G3 B := Over.homMk π hz
  let x : Fin 3 → (Over.mk z ⟶ B') := fun i =>
    Over.homMk (h.1.lift (ρ ≫ x3 B i).left z (Over.w (ρ ≫ x3 B i))) (h.1.lift_snd _ _ _)
  let β := toBaseHom (toBase_mul h) (Over.mk z)
  have hx : ∀ i, β (x i) = ρ ≫ x3 B i := fun i => Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  let r : Over.mk z ⟶ G3 B' := lift (x 0) (lift (x 1) (x 2))
  have hr : ∀ i, r ≫ x3 B' i = x i := fun i => by fin_cases i <;> simp [r, x3]
  refine triv_pull_of_gen hL M'.L.isLB hw (φ := thφ B (x3 B)) (φ' := thφ B' (x3 B')) (ε := thε) M'.c.t M'.c.isGen
    r.left π fun I => ?_
  have e : β (r ≫ psum B' (x3 B') I.down) = ρ ≫ psum B (x3 B) I.down :=
    (psum_hom (β.comp (preHom r)) (x3 B') I.down).trans ((congrArg (fun q => psum B q I.down) (funext fun i =>
      (congrArg β (hr i)).trans (hx i))).trans (psum_hom (preHom ρ) (x3 B) I.down).symm)
  exact congrArg (fun q => q.left) e

theorem triv_sym (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ B.left) (z : Z ⟶ S') (hz : π ≫ B.hom = z ≫ f) :
    Triv ((LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).pull π) := by
  let x : Over.mk z ⟶ B' := Over.homMk (h.1.lift π z hz) (h.1.lift_snd _ _ _)
  have hx : x.left ≫ F = π := h.1.lift_fst _ _ _
  refine triv_pull_of_gen hL M'.L.isLB hw M'.sym M'.sym_gen x.left π fun k => ?_
  fin_cases k
  · exact (inv_left_comp (toBase_mul h) x).trans (congrArg (· ≫ _) hx)
  · exact ((congrArg (· ≫ F) (Category.comp_id _)).trans hx).trans (Category.comp_id _).symm

end Level

section Pack
variable (hG : GlobalFnsSt) (hS : SecAlgSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  (hI : I ≠ ⊤) (hc : IsAdicComplete I R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (N : ∀ e, CP (Y e)) {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
  [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {b : ∀ e, (Y e).left ⟶ B.left}
  (hg : ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) {M : LB B.left} (hM : M.IsLB)
  (hiso : ∀ e, LBIso (N e).L.L (M.pull (b e)))
include hG hS hI hc hB hp hg hM hiso

theorem triv_theta_alg : Triv (Theta B M) :=
  triv_of_forall_thick hG hS hI hc (G3 B)
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB))
    (isProjBy_tensor R _ _ hp (isProjBy_tensor R _ _ hp hp)) (Theta B M) (LB.isLB_linComb hM _ _) fun e =>
      triv_theta (hg e) (N e) hM (hiso e) (fstG I e (G3 B)).left (pullback.snd (G3 B).hom (thick R I e))
        (pullback.condition (f := (G3 B).hom) (g := thick R I e))

theorem triv_sym_alg : Triv (LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) :=
  triv_of_forall_thick hG hS hI hc B hB hp _ (LB.isLB_linComb hM _ _) fun e =>
    triv_sym (hg e) (N e) hM (hiso e) (fstG I e B).left (pullback.snd B.hom (thick R I e))
      (pullback.condition (f := B.hom) (g := thick R I e))

theorem exists_cp_alg (hY : ∀ e, IsAbelianScheme (Y e)) :
    ∃ Q : CP B, Q.L.L = M ∧ ∀ e, IsCPPullback (N e) Q (thick R I e) (b e) := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_local M hM (K := PUnit) (fun _ => eSec B) (fun _ => 1)
  obtain ⟨Q, hQ⟩ := AbPackage.exists_cp hG hB ⟨M, r, hM, hr⟩ (triv_theta_alg hG hS hI hc N hB hp hg hM hiso)
    (triv_sym_alg hG hS hI hc N hB hp hg hM hiso)
  have e₀ : Q.L.L = M := congrArg (fun q => q.L) hQ
  refine ⟨Q, e₀, fun e => ⟨hg e, ?_⟩⟩
  obtain ⟨w, hw⟩ : LBIso (N e).L.L (Q.L.L.pull (b e)) := by rw [e₀]; exact hiso e
  exact AbPackage.exists_isCPMap_of_iso hG (hY e) Q (N e) (toBase_mul (hg e)) w hw

end Pack

end GlobalTheory.TowerAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductIsoOfFibreIsoFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_product_iso_of_fibre_iso_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ → ∃ (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) (w : BunIso φ), HomF φ ∧ w.IsGen ∧ ∀ (a : TF (R := R) F ⟶ D.P.A) (a' : TF (R := R) F ⟶ D'.P.A), (∀ x : baseOver (Sp F) ⟶ Q.A, a.left = x.left ≫ Φ → a'.left = (x ≫ σ.hom).left ≫ Φ') → lift (𝟙 _) a ≫ φ.hom = lift (𝟙 _) a' := by
  first | exact @GlobalTheory.Ex.AbPartIso.exists_iso_of_isFib | exact GlobalTheory.Ex.AbPartIso.exists_iso_of_isFib | (intros; apply GlobalTheory.Ex.AbPartIso.exists_iso_of_isFib <;> assumption)
end

