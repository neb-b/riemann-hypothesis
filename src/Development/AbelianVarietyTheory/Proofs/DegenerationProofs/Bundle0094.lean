module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralSectionsCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G')
  (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G)

def LevelIso : Prop :=
  ∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧
    (U'.gt e).pG.left ≫ prA hD = (j e).hom.left ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ prA hD =
        (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧
      PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x)
        ((U.gt e).t (hD.xe x)) (j e).hom.left

def AgreeAll (k : ℕ) (σ : H0 U.LG.L k) (σ' : H0 U'.LG.L k) : Prop :=
  ∀ e : ℕ, Agree U U' hD e k (j e).hom.left σ σ'

def Enough : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ') ∧
    ∀ σ₀ : H0 U'.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ'.f i = resTop _ (scal G'.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ'

def GenericRel (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G)
    (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R)))
      (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))) : Prop :=
  w.IsGen ∧ ∀ k : ℕ, 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), AgreeAll U U' hD j k σ σ' →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL →
      (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' →
      gs (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL))
          (σ.f (fun _ => jL)) =
        (Geo.Tor.gw w r z jL (fun _ => jL') ^ k).val *
          gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL'))
            (σ'.f (fun _ => jL'))

open ThickIso TorusCoordPull in
theorem exists_levelIso (hG : GlobalFnsSt) : ∃ j, LevelIso U U' hD j := by
  choose j hm hj using fun e : ℕ => exists_iso hD (U.gt e) (U'.gt e) hG
  refine ⟨j, fun e => ?_⟩
  have h₀ := hj e _ (𝟙 _)
  have hp : (U'.gt e).pG.left ≫ abMap hD = (j e).hom.left ≫ (U.gt e).pG.left := by
    simpa only [Category.id_comp] using h₀.1
  have hO := Oφ_pull hD (U.gt e).pG (U'.gt e).pG (j e).hom.left hp
  refine ⟨hm e, (hj (e + 1) _ (thickMap R I e G')).unique_right ?_, hp, fun x => ⟨hO x,
    pmaps_of_good ((isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB (hO x) ((U'.gt e).t_gen x)
      ((U.gt e).t_gen _) fun y J J' hJ hJ' => h₀.2 x y J J' hJ hJ'⟩⟩
  simpa only [Category.id_comp] using h₀.succ (U.gt_q e) (U.gt_t e) (U'.gt_q e) (U'.gt_t e)

variable {U U' hD j}

theorem LevelIso.agreeAll (hj : LevelIso U U' hD j) {k : ℕ} {σ : H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D'.toPre.SecB k α} (hE : ∀ e, U.ExpandsAt e k σ f)
    (hE' : ∀ e, U'.ExpandsAt e k σ' f')
    (hf : ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
      (f (hD.xe x))) : AgreeAll U U' hD j k σ σ' := fun e =>
  agree_of_expandsAt _ _ hD e k _ (hj e).2.2.1 (fun x => ((hj e).2.2.2 x).1) (fun x => ((hj e).2.2.2 x).2)
    (hE e) (hE' e) hf

theorem LevelIso.enough (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) (hU : ∀ k, 1 ≤ k → U.ExpBij k)
    (hU' : ∀ k, 1 ≤ k → U'.ExpBij k) : Enough U U' hD j := by
  intro k hk
  constructor
  · intro σ₀
    obtain ⟨s, hs⟩ := exists_restrict U k σ₀
    obtain ⟨F, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).1 s
    obtain ⟨F', hF⟩ := exists_pull hD _ hG k F
    obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).2 F'
    exact ⟨r' * r, _, _, mul_ne_zero hr' hr, scale_of_restrict _ hs h₁ r', hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩
  · intro σ₀
    obtain ⟨s', hs⟩ := exists_restrict U' k σ₀
    obtain ⟨F', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).1 s'
    obtain ⟨F, hF⟩ := exists_push hD _ hG k F'
    obtain ⟨s, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).2 F
    exact ⟨r * r', _, _, mul_ne_zero hr hr', scale_of_restrict _ hs h₁' r, hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩


open LinearUnifIso in
theorem LevelIso.act_comm (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O]
    [Module O D.toPre.X] [Module O D'.toPre.X] {o : D.OAct O} {o' : D'.OAct O} {oA : A.OAct O} {oA' : A'.OAct O}
    {oG : RingAct G O} {oG' : RingAct G' O} (lin : U.OLinear O o oA oG) (lin' : U'.OLinear O o' oA' oG')
    (hx : ∀ (x : O) y, hD.xe (x • y) = x • hD.xe y)
    (hB : ∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x))
    (a : O) (e : ℕ) : (Over.pullback (thick R I e)).map (oG'.act a) ≫ (j e).hom =
      (j e).hom ≫ (Over.pullback (thick R I e)).map (oG.act a) := by
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  have P : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback t).map c).left ≫ pullback.fst Y.hom t =
        pullback.fst X.hom t ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : o'.onB.act a ≫ ψ = ψ ≫ o.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ, Category.assoc, ← P, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, hB])
  obtain ⟨hm, -, hp, ht⟩ := hj e
  have hq : (j e).hom ≫ (U.gt e).q = (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
      Category.assoc, Category.assoc, P, eψ]
    exact hp.symm.trans (Category.assoc _ _ _)
  obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
    (fun x => (ht x).2)
  obtain ⟨t, tc, ti⟩ := lin.i_lin e a
  obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
  have := oG.hom a
  have := oG'.hom a
  have hts : t' ≫ s = s ≫ t := by
    refine PowTorus.torus_ext _ _ fun χ z => ?_
    obtain ⟨x, rfl⟩ := hD.xe.surjective χ
    rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
      ← gm_torusEnd tc', Category.id_comp]
  refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
      ← Functor.map_comp, ← Functor.map_comp, hψa]
  · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]

end GlobalTheory.GenericIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section

namespace GlobalTheory.ZH.CoordMap

variable {X Y : Scheme.{0}}

def pullOn (B : LB X) (V : X.Opens) (g : Y ⟶ X) : LB Y where
  ι := B.ι
  U j := g ⁻¹ᵁ (V ⊓ B.U j)
  g j j' := Units.map (g.appLE (B.U j ⊓ B.U j') (g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j'))
    (inf_le_inf (g.preimage_mono inf_le_right) (g.preimage_mono inf_le_right))).hom.toMonoidHom (B.g j j')

def pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V) :
    (pullOn B V g).Sec where
  f j := (g.appLE (V ⊓ B.U j) (g ⁻¹ᵁ (V ⊓ B.U j)) le_rfl).hom (σ j)
  compat j j' := by
    have hW : g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j') ≤ g ⁻¹ᵁ (V ⊓ B.U j ⊓ B.U j') :=
      le_inf inf_le_left (inf_le_right.trans (g.preimage_mono inf_le_right))
    have e := congrArg (g.appLE _ _ hW).hom (h j j')
    rw [map_mul, ProjSpace.appLE_resG, ProjSpace.appLE_resG, ProjSpace.appLE_resG] at e
    exact (ProjSpace.resG_appLE g le_rfl inf_le_left _).trans (e.trans
      (congrArg (_ * ·) (ProjSpace.resG_appLE g le_rfl inf_le_right _).symm))

theorem resG_pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V)
    (j : B.ι) {T : Y.Opens} (hj : T ≤ g ⁻¹ᵁ (V ⊓ B.U j)) :
    resG Y (U := (pullOn B V g).U j) hj ((pullSecOn g σ h).f j) = (g.appLE _ T hj).hom (σ j) :=
  ProjSpace.resG_appLE g le_rfl hj _

theorem preimage_basicOpen_le {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j))
    (h : σ ∈ secOn B V) (j : B.ι) : g ⁻¹ᵁ X.basicOpen (σ j) ≤ nonzeroLocus (pullSecOn g σ h) := by
  refine le_trans ?_ (le_iSup (fun k => Y.basicOpen ((pullSecOn g σ h).f k)) j)
  refine le_trans ?_ (Scheme.basicOpen_appLE g (g ⁻¹ᵁ (V ⊓ B.U j)) _ le_rfl (σ j)).ge
  exact le_inf (g.preimage_mono (X.basicOpen_le _)) le_rfl

theorem exists_coordMap : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  intro o _ X Z f s B V J σ m e hσ hne
  let t : Fin (m + 1) → (pullOn B V V.ι).Sec := fun k => pullSecOn V.ι (σ (e k)) (hσ _)
  have ht : ⨆ i, nonzeroLocus (t i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, j, hij⟩ := hne (V.ι y) y.2
    obtain ⟨k, rfl⟩ := e.surjective i
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, preimage_basicOpen_le V.ι _ (hσ _) j hij⟩
  have key : ∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens)
      (hi : T ≤ ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht ⁻¹ᵁ ProjSpace.chart o m i)
      (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧
        ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) =
          ProjSpace.pullRatio _ T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j) := by
    intro i j T hi hj
    refine ⟨?_, fun k => ?_⟩
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.isUnit_resG_sec (t i) j (hi.trans (ProjSpace.toProj_preimage_chart _ t ht i).le) hj
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj, ← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.sec_eq_pullRatio_toProj_mul _ t ht i k j hi hj
  refine ⟨ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht, ProjSpace.toProj_str _ t ht, key, ?_⟩
  generalize ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht = π at key
  intro K _ x j hx
  obtain ⟨i, hi⟩ := Points.exists_le_preimage_of_iSup_eq_top (x ≫ π) (ProjSpace.iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ ProjSpace.chart o m i ⊓ V.ι ⁻¹ᵁ (V ⊓ B.U j)) :=
    fun z hz => ⟨hi hz, (x z).2, hx hz⟩
  obtain ⟨hu, hk⟩ := key i j _ inf_le_left inf_le_right
  have hu' := hu.map (Points.valMap x _ hT).hom
  rw [← Points.valR_eq] at hu'
  refine ⟨i, hu'.unit, hi, fun k => ?_⟩
  have := congrArg (valR x _) (hk k)
  rw [Points.valR_mul x _ hT, Points.valR_appLE x _ _ hT, ProjSpace.pullRatio, Points.valR_appLE x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end GlobalTheory.ZH.CoordMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsToStkAUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT

theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) (k : Fin 4) : DegPre.gtφ D F b χ k = b.left ≫ D.Oφ (𝟙 D.P.A) χ k := by
  rw [comp_Oφ_id]
  have h : padd D.P.A (DegPre.cF D F χ) b = padd D.P.A b (DegPre.cF D F χ) := _root_.mul_comm (DegPre.cF D F χ) b
  have h' : DegPre.gtφ D F b χ = D.Oφ b χ := by
    unfold DegPre.gtφ DegPre.Oφ
    rw [h]
  rw [h']

theorem Oφ_over {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (k : Fin 4) :
    D.Oφ (𝟙 D.P.A) χ k ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases k <;> exact Over.w _

theorem gs_scal {F : Type} [CommRing F] {Y : Scheme.{0}} (q : Y ⟶ Sp F) (r : Sp F ⟶ Y) (h : r ≫ q = 𝟙 _) (z : Sp F)
    (a : F) : gs r z ⊤ (scal q a) = toStkA z a :=
  (gs_pull r q z ⊤ trivial _).trans ((congrArg (fun t => gs t z ⊤ _) h).trans (gs_eq (𝟙 _) z ⊤ trivial _))

theorem toStkA_surj {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStkA z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s
  exact ⟨x, congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom hx⟩

theorem exists_toStkA_unit {F : Type} [Field F] (z : Sp F) (v : ((Sp F).presheaf.stalk z)ˣ) :
    ∃ t : F, t ≠ 0 ∧ toStkA z t = v.val := by
  obtain ⟨t, e⟩ := toStkA_surj z v.val
  exact ⟨t, fun e0 => v.ne_zero (by rw [← e, e0, map_zero]), e⟩

theorem top_le_of_mem {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U) :
    ⊤ ≤ x ⁻¹ᵁ U := fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ h

theorem exists_valF_secLin {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (h : Y ⟶ X)
    (q : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hq : r ≫ q = 𝟙 _) (x : Sp F ⟶ X) (hr : r ≫ h = x) (k : ℕ) {l l' : L.ι}
    (hl : ⊤ ≤ x ⁻¹ᵁ L.U l) (hl' : ⊤ ≤ x ⁻¹ᵁ L.U l') : ∃ τ : F, τ ≠ 0 ∧
      ∀ (σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ)))) (n : ℕ) (cc : Fin n → F)
        (σ : Fin n → H0 L k), GeneratorPullback.SecLin L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) σ'
          (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) σ h (fun i => scal q (cc i)) →
        valF r _ (σ'.f (fun _ => l)) = τ * ∑ i, cc i *
          valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => l')) ((σ i).f (fun _ => l')) := by
  subst hr
  let z : Sp F := cpt F
  obtain ⟨J, hJ, eJ⟩ := exists_good L hL z (fun _ : PUnit.{1} => r ≫ h) (fun _ => l')
    (fun _ _ _ => rfl) (fun _ => hl' trivial)
  replace eJ : J (r ≫ h) = l' := eJ PUnit.unit
  have hl₁ : ⊤ ≤ r ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => h) (fun _ => l) :=
    fun y hy => Set.mem_iInter.2 fun _ => hl hy
  have hl₂ : r z ∈ LB.wchart L (fun _ : Fin 1 => h) (fun _ => l') := Set.mem_iInter.2 fun _ => hl' trivial
  obtain ⟨τ, τ0, hτ⟩ := exists_toStkA_unit z (trF (L := L) (fun _ : Fin 1 => h)
    (fun _ => (k : ℤ)) r z (fun _ => l) (fun _ => l'))
  refine ⟨τ, τ0, fun σ' n cc σ hσ => (toStkA z).injective ?_⟩
  refine (toStkA_valR_eq_gs r _ z hl₁ _).trans ((sec_trans σ' r z (hl₁ trivial) hl₂).trans ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, hτ, map_sum, ← sval_of σ' r z J (fun _ => l') (fun _ => eJ), ExpGTrans.secLin_val hσ r z hJ]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, sval_of (σ i) _ z J (fun _ => l') (fun _ => by rw [Category.comp_id, eJ])]
  exact congrArg₂ (· * ·) (gs_scal _ r hq z _)
    (toStkA_valR_eq_gs (r ≫ h) (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => l')) z
      (fun y hy => Set.mem_iInter.2 fun _ => hl' hy) _).symm

theorem exists_coef_secLin {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : Frm D F k g.b) (hw : w.IsGen) (z : Sp F)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) : ∃ κ : F, κ ≠ 0 ∧
      ∀ (s : Fam D F k) (χ : D.X) (n : ℕ) (cc : Fin n → F) (f : Fin n → D.SecB k χ),
        GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) (s.s χ) (D.famφB χ) (DegPre.famε k) f
          (DegPre.prB D F).left (fun i => scal (fst (TF (R := R) F) D.P.A).left (cc i)) →
        ∀ (b : Sp F ⟶ D.P.A.left) (jf jt : Fin 4 → D.P.L.ι), b = g.b.left → (∀ i, J (b ≫ D.famφB χ i) = jf i) →
          (∀ i, J (b ≫ D.Oφ (𝟙 _) χ i) = jt i) →
          coef s g w χ = κ * ∑ i, cc i * (valR b _ ((f i).f jf) * valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) := by
  obtain ⟨Rg, R0, hR⟩ := exists_toStkA_unit z (rigV D (TF (R := R) F).hom z J)
  obtain ⟨W, W0, hW⟩ := exists_toStkA_unit z (val w (𝟙 _) z J)
  refine ⟨W * (Rg ^ k)⁻¹, by simp [R0, W0], fun s χ n cc f hs b jf jt hb hjf hjt => ?_⟩
  let rb : Sp F ⟶ (DegPre.BF D F).left := (lift (𝟙 (TF (R := R) F)) g.b).left
  have hrb : rb ≫ (DegPre.prB D F).left = b :=
    (congrArg (fun t => t.left) (lift_snd (𝟙 (TF (R := R) F)) g.b)).trans hb.symm
  have hrb' : rb ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun t => t.left) (lift_fst (𝟙 (TF (R := R) F)) g.b)
  have hcf : IsCoef k g w χ (s.s χ) (coef s g w χ) := Classical.epsilon_spec
    (((CoefBasic.coef_basic R D F k g).2.2 w hw).1 χ (s.s χ)).exists
  have e := hcf z J hJ
  have a₁ : sval (s.s χ) rb z J = toStkA z (∑ i, cc i * valR b _ ((f i).f jf)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ExpGTrans.secLin_val hs rb z hJ, hrb, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, sval_of (f i) _ z J jf hjf]
    refine congrArg₂ (· * ·) (gs_scal _ rb hrb' z _) (toStkA_valR_eq_gs b _ z (top_le_of_mem _ _ z ?_) _).symm
    have := hJ.mem (D.famφB χ) b
    rwa [funext hjf] at this
  have a₂ : (val (g.s χ) (𝟙 _) z J).val = toStkA z (valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) := by
    have c : ∀ i, J (𝟙 (Sp F) ≫ DegPre.gtφ D F g.b χ i) = jt i := fun i =>
      (congrArg J ((Category.id_comp _).trans ((gtφ_eq D F g.b χ i).trans
        (congrArg (· ≫ D.Oφ (𝟙 _) χ i) hb.symm)))).trans (hjt i)
    refine (congrArg Units.val (val_of (g.s χ) (𝟙 _) z J jt c)).trans ?_
    have toStkA_valR {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
        (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
        toStkA z (valF x U a.val) = (gm x z U a).val := by
      have hz : x z ∈ U := ht trivial
      rw [valF, dif_pos ht, gm, dif_pos hz]
      show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
      rw [Iso.hom_inv_id_apply]
      exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ht) z trivial _
    refine (toStkA_valR (𝟙 (Sp F)) _ z (top_le_of_mem _ _ z ?_) _).symm
    have := hJ.mem (DegPre.gtφ D F g.b χ) (𝟙 (Sp F))
    rwa [funext c] at this
  have e' : toStkA z (coef s g w χ) * toStkA z Rg ^ k = toStkA z (∑ i, cc i * valR b _ ((f i).f jf)) *
      toStkA z (valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) * toStkA z W := by
    have a₃ : toStkA z (coef s g w χ) = GlobalTheory.UT.cst (R := R) F z (coef s g w χ) := (CoefBasic.cst_eq (R := R) z _).symm
    rw [hR, hW, ← a₁, ← a₂, a₃]
    exact e
  rw [← map_pow, ← map_mul, ← map_mul, ← map_mul] at e'
  rw [(eq_mul_inv_iff_mul_eq₀ (pow_ne_zero k R0)).2 ((toStkA z).injective e'), Finset.sum_mul]
  simp only [_root_.mul_assoc]
  ring

end GlobalTheory.ZH.IntegralSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.fib_of_indep : ∀ C : Core, C.Indep → C.Fib := by
  intro C hI p _ y τ x hx
  obtain ⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, htest⟩ := _root_.GlobalTheory.ZJ.core_basic C
  have := C.lft
  have hne : ((C.GG.hom ⁻¹ᵁ C.U : C.G.toScheme.Opens) : Set C.G.toScheme).Nonempty := by
    obtain ⟨w, hw⟩ := hdom.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨w, hw⟩
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨b', hb'x, hb'U⟩ :=
    (@_root_.GlobalTheory.exists_integral_point_lifting_residue_point C.G.toScheme hint (C.GG.hom ≫ C.π) hflat hlft' (C.GG.hom ⁻¹ᵁ C.U) hne p _).1 x
  have hcl : C.Cl (b' ≫ C.GG.hom) := by
    rintro _ ⟨s, rfl⟩
    have := hb'U ⟨s, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact this
  obtain ⟨b, hby, hbx⟩ := hI p (b' ≫ C.GG.hom) y hcl (htest p y τ).1
    (by rw [← Category.assoc, hb'x, hx]) b' rfl
  obtain ⟨c, hc, hcb⟩ := τ.lift b hby
  refine ⟨rPt p ≫ c, by rw [Category.assoc, hc], ?_⟩
  rw [Category.assoc, hcb, hbx, hb'x]

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem immBy_of_spans (hA : AmpleSt) {R : Type} [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {N : ℕ}
    (hN : 4 ≤ N) {J : Type} [Fintype J] (s : J → LB.Sec (LPow P.A P.L N (baseOver (Sp R))))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), ∃ c : J → Γ((baseOver (Sp R)).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j) :
    ImmBy (baseOver (Sp R) ⊗ P.A).hom (LPow P.A P.L N (baseOver (Sp R))) s Set.univ := by
  have := P.isAb.proper
  have hT : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have hL : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  have key := (AmpleSpan.embedsBy_of_isPullback P.A P.isLB (hA _ P N hN).2 (isAffineOpen_top (Sp R))
    (g := (baseOver (Sp R)).hom ≫ (Sp R).topIso.inv) (φ := (snd (baseOver (Sp R)) P.A).left)
    (f' := (fst (baseOver (Sp R)) P.A).left) (K := Fin 1) (ε := fun _ => (N : ℤ))
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact (IsPullback.of_hasPullback _ P.A.hom).flip) (by simp) s
    (fun σ => hs σ)).1
  have e : (baseOver (Sp R) ⊗ P.A).hom = (fst (baseOver (Sp R)) P.A).left :=
    (Over.w (fst (baseOver (Sp R)) P.A)).symm.trans (Category.comp_id _)
  rw [SpanImm.immBy_iff, e]
  exact key

theorem ThetaSys.Real.immBy_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ImmBy (baseOver (Sp S.R) ⊗ ρ.P.A).hom (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s Set.univ := by
  intro hL o Ω _ _ _ _ S ρ
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have hN : 4 ≤ S.N := by
    have h : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h 2
  exact immBy_of_spans hL.1.ample ρ.P hN ρ.s fun σ => (ρ.s_basis σ).exists

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitGenericOfBasedWeightedCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Charts.split_generic_of_based : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hB
  obtain ⟨i, hi⟩ := GlobalTheory.T.exists_splitTorus_kernel_genericFibre R G C d c Sg hD hS a j hB
  obtain ⟨hst, hinv, hwt⟩ := GlobalTheory.T.torusStable_weights_genericFibre R G C d c Sg hD hS a j hB i hi
  obtain ⟨hc, hb⟩ := _root_.GlobalTheory.GenericSplit.geometricallyConnected_and_basePointFree_generic R G C d c Sg hD hS
  exact ⟨hc, i, GlobalTheory.T.isMonHom_generic_fibre_kernel_torus R G C d c Sg hD hS a j hB i hi, hst, hinv, hwt, hb,
    GlobalTheory.T.generic_invariants_generated_by_ratios R G C d c Sg hD hS a j hB i hi hst⟩
end GlobalTheory.ZJ
end

