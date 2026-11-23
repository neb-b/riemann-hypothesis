module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartBaseChangeRigGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory

theorem linComb_gen_eq_of_eSec (hGF : GlobalFnsSt) {S X : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (A.left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((𝟙_ (Over S)).left ⟶ X)} {ε' : K' → ℤ}
    {a b : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (hb : b.IsGen) {r : LB.Gen (LB.LinComb L φ' ε')}
    (har : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε a (eSec A)) r)
    (hbr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε b (eSec A)) r) : a = b := by
  have hcov : ∀ x : A.left, ∃ i, x ∈ (LB.LinComb L φ ε).U i := fun x => by
    choose I hI using fun k => exists_chart hL (φ k x)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  obtain ⟨u, hu⟩ := ChartFrameTrA.exists_ratio_gen hcov ha hb
  suffices hu1 : u = 1 by
    cases a
    cases b
    congr 1
    funext p
    exact (hu p).trans (by rw [hu1, map_one, _root_.one_mul])
  apply ChartFrameTrA.unit_eq_one_of_eSec hGF A hA u
  have key : pullU (eSec A) ⊤ u = 1 := by
    refine unit_ext fun z hz => ?_
    choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ X => exists_chart hL (χ z)
    have hJ' : Good L z J := hJ
    have e1 := (val_pull hJ' a (eSec A) (𝟙 _)).symm.trans ((val_corr hJ' har (𝟙 _)).trans
      ((val_corr hJ' hbr (𝟙 _)).symm.trans (val_pull hJ' b (eSec A) (𝟙 _))))
    have hm := hJ'.mem φ (𝟙 _ ≫ eSec A)
    have e2 : val a (𝟙 _ ≫ eSec A) z J = gm (𝟙 _ ≫ eSec A) z ⊤ u * val b (𝟙 _ ≫ eSec A) z J :=
      (congrArg (gm _ z _) (hu _)).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (gm_res _ z _ hm _) rfl))
    have e3 : gm (𝟙 _ ≫ eSec A) z ⊤ u = 1 := mul_eq_right.1 (e2.symm.trans e1)
    exact (gm_pull (𝟙 _) (eSec A) z ⊤ trivial u).trans (e3.trans (map_one _).symm)
  exact congrArg Units.val key

theorem isPrimG_unique : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t,
    IsPrimG t wP → IsPrimG t wP' → wP = wP' :=
  fun hGF _ _ _ _ _ _ t hA _ _ h h' =>
    linComb_gen_eq_of_eSec hGF t.G hA t.PP.isLB h.1 h'.1 h.2 h'.2

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ChartRigBC

open GlobalTheory.RawChartGermBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0) (d : ℕ)

theorem jetCoef_eq (κ : Type) (m : ℕ) : jetCoef ψ κ m = jetBC ψ κ m :=
  RingHom.ext fun a => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl

theorem subst_jetCoef (m n n' : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (φ' : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S') (h : ∀ p, φ' p = MvPolynomial.map ψ (φ p)) :
    (Formalism.L2.Pj.homAt x1 (jetSubstP m φ')).left ≫ spMap (jetCoef ψ (Fin n × Fin d) m) =
      spMap (jetCoef ψ (Fin n' × Fin d) m) ≫ (Formalism.L2.Pj.homAt x0 (jetSubstP m φ)).left := by
  obtain rfl : φ' = fun p => MvPolynomial.map ψ (φ p) := funext h
  rw [jetCoef_eq, jetCoef_eq]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem aug_jetCoef (m n : ℕ) :
    (Formalism.L2.Pj.homAt x1 (jetAug : Jet S' (Fin n × Fin d) m →ₐ[S'] S')).left ≫ spMap (jetCoef ψ (Fin n × Fin d) m) =
      spMap ψ ≫ (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S)).left := by
  rw [jetCoef_eq]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetAug_comp_jetBC ψ _ m)

theorem overAt_hom_comp :
    (overAt (spMap ψ ≫ x0) S').hom = spMap ψ ≫ (overAt x0 S).hom := by
  change spMap (algebraMap S' S') ≫ spMap ψ ≫ x0 = spMap ψ ≫ spMap (algebraMap S S) ≫ x0
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact spMap_comp_eq _ _ _ _ (RingHom.ext fun _ => rfl)

theorem val_eLG_bc (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G)
    (hx : ∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left)
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m)
    (he : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m))))
    (wP : PrimTyG t) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x1 d m 1).left) (z : Z) {J}
    (hJ : Good t.PP.L z J) :
    val (eLG t x1 d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP m) r z J =
      val (eLG t x0 d x act e wP m) (r ≫ spMap (jetCoef ψ (Fin 1 × Fin d) m)) z J := by
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine congrArg (fun q => val wP q z J) ?_
    exact (congrArg (r ≫ ·) (hx m)).trans (Category.assoc _ _ _).symm
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine (val_corr hJ (he m) _).trans ((val_pull hJ _ _ _).trans ?_)
    refine congrArg (fun q => val (e m) q z J) ?_
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine congrArg (r ≫ ·) (subst_jetCoef ψ x0 x1 d m 2 1 _ _ ?_)
    rintro ⟨i, j⟩
    fin_cases i
    · exact (MvPolynomial.map_X ψ _).symm
    · exact (map_psIn ψ d m _ _).symm

end GlobalTheory.ChartRigBC

namespace GlobalTheory


open ChartRigBC in
theorem rigidificationAtOrigin_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (wP : PrimTyG t), wP.IsGen → Rig0G t x0 d x act e wP → Rig0G t x1 d x' (fun a i => (MvPowerSeries.map ψ (act a i))) e' wP := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 hx1 d x x' hx e e' _ _ he act wP _ h0
  have hL := t.PP.isLB
  refine corr_of_val hL fun y J hJ => ?_
  refine (val_pull hJ _ _ _).trans ((val_eLG_bc t ψ x0 x1 d act x x' hx e e' he wP 0 _ y hJ).trans ?_)
  refine Eq.trans ?_ (GermB.val_rigT _ _ _ _ _ y J hJ).symm
  have h1 := (val_pull hJ _ _ _).symm.trans ((val_corr hJ h0 (spMap ψ)).trans (GermB.val_rigT _ _ _ _ _ y J hJ))
  refine (congrArg (fun q => val (eLG t x0 d x act e wP 0) q y J) ?_).trans
    (h1.trans (congrArg (fun q => val t.PP.rig q y J) ?_))
  · rw [Category.id_comp]; exact aug_jetCoef ψ x0 x1 d 0 1
  · subst hx1
    rw [Category.id_comp]; exact (overAt_hom_comp ψ x0).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginIffPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.RigOriginPull

theorem val_tie {X₁ X₂ Y Z : Scheme.{0}} {K : Type} [Fintype K] {L : LB X₁} {L' : LB X₂} {F : X₂ ⟶ X₁}
    (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X₂)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X₁) → L.ι} {J' : (Z ⟶ X₂) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val c r z J = (∏ k, Geo.Tor.gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  have H := (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 h Z r z (fun k => J ((r ≫ φ' k) ≫ F))
    (fun k => J' (r ≫ φ' k)) (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))
  · rw [Category.comp_id] at H
    exact (val_of c r z J _ (fun k => by rw [Category.assoc])).trans H
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem prod_prim (t : SAB H X0) {T : Over X0} {M : Type} [CommGroup M] (h : (T.left ⟶ t.G.left) → M) :
    ∏ k, h ((1 : T ⟶ t.G).left ≫ primφ t k) ^ primε k = h (1 : T ⟶ t.G).left := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), (1 : T ⟶ t.G).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, (1 : T ⟶ t.G) ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact Category.comp_id (1 : T ⟶ t.G)
    · rfl
  have hc : ∏ I, h ((1 : T ⟶ t.G).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I) ^ cε 2 I = 1 :=
    (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
      (GermB.cube_one_left t (fun p => h p.left) _)
  rw [Fintype.prod_sum_type]
  simp only [primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg,
    Finset.prod_inv_distrib, zpow_one]
  exact (congrArg (fun q => h (1 : T ⟶ t.G).left * q⁻¹) hc).trans (by rw [inv_one, _root_.mul_one])

theorem prod_cube_left (t : SAB H X0) {T T' : Over X0} {M : Type} [CommGroup M] (h : (T'.left ⟶ t.G.left) → M)
    (u : T' ⟶ T) (a b : T ⟶ t.G) (ha : u ≫ a = 1) :
    ∏ I, h (u.left ≫ cφG t ![a, b] I) ^ cε 2 I = 1 := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), u.left ≫ cφG t ![a, b] I = (psum t.G ![1, u ≫ b] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact ha
    · rfl
  exact (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
    (GermB.cube_one_left t (fun p => h p.left) _)

end GlobalTheory.RigOriginPull


open GlobalTheory.RigOriginPull in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.rigOrigin_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (wP : PrimTyG t) (wP' : PrimTyG t'), wP.IsGen → wP'.IsGen → (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d), (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (Rig0G t x0 d x act e wP ↔ Rig0G t' (𝟙 (Sp S)) d x' act e' wP') := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hrig d x x' hx e e' _ _ htie wP wP' _ _ hP act h0 _
  obtain ⟨c, hc₁, hc₂⟩ := htie 0
  obtain ⟨cP, hP₁, hP₂⟩ := hP
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig mp.cm.e _
    (rigPull_le mp.cm.F mp.cm.e mp.cm.e_comm t.PP.L) (fun _ => rfl)).1 hrig.2
  let o : Sp S ⟶ t'.G.left := (1 : overAt (𝟙 (Sp S)) S ⟶ t'.G).left
  have key : ∀ (y : Sp S) (J : (Sp S ⟶ t.G.left) → t.PP.L.ι) (J' : (Sp S ⟶ t'.G.left) → t'.PP.L.ι),
      Good t.PP.L y J → Good t'.PP.L y J' →
      val (LB.pullGen t.PP.L _ _ (eLG t x0 d x act e wP 0)
          (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 (Sp S)) y J =
        Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) *
          val (LB.pullGen t'.PP.L _ _ (eLG t' (𝟙 (Sp S)) d x' act e' wP' 0)
            (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 (Sp S)) y J' ∧
      val (rigT t.G t.PP.L t.PP.rig (overAt x0 S) 1) (𝟙 (Sp S)) y J =
        Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) *
          val (rigT t'.G t'.PP.L t'.PP.rig (overAt (𝟙 (Sp S)) S) 1) (𝟙 (Sp S)) y J' := by
    intro y J J' hJ hJ'
    constructor
    · let A := Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)
      let A' := Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)
      let σ : Jet S (Fin 2 × Fin d) 0 →ₐ[S] Jet S (Fin 1 × Fin d) 0 := jetSubstP 0 fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 1), j), fun j => psIn d 0 ![0] (act H.w0 j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2
      have ho : (𝟙 (Sp S) ≫ A'.left) ≫ (x' 0).left = o :=
        (congrArg (· ≫ (x' 0).left) (Category.id_comp _)).trans (congrArg (fun q => q.left) h0)
      have ho' : (𝟙 (Sp S) ≫ A.left) ≫ (x 0).left = o ≫ mp.φ := by
        rw [← ho, ← hx 0]
        exact (Category.assoc _ _ _).symm
      have p₁ : val wP ((𝟙 (Sp S) ≫ A.left) ≫ (x 0).left) y J =
          Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) * val wP' ((𝟙 (Sp S) ≫ A'.left) ≫ (x' 0).left) y J' := by
        rw [ho, ho']
        refine (val_pull hJ wP mp.φ o).symm.trans ((val_corr hJ hP₁ o).symm.trans
          ((val_tie w _ _ wP' cP hP₂ o y hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)))
        exact prod_prim t' (T := overAt (𝟙 (Sp S)) S) (fun q => Geo.Tor.gw w q y (J (q ≫ mp.φ)) (J' q))
      have hu : (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ) ≫ jptG t' (𝟙 (Sp S)) d x' 0 (0 : Fin 2) = 1 := by
        have hid : σ.comp (jetCopy d 0 (0 : Fin 2)) = AlgHom.id S _ := by
          apply GermD.jet_hom_ext
          rintro ⟨i, j⟩
          obtain rfl : i = 0 := Subsingleton.elim _ _
          simp [σ, jetSubstP, jetCopy, GermD.jetMap_mk]
        rw [jptG, Category.assoc, ← Category.assoc (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ), GermD.homAt_comp, hid,
          GermD.homAt_id, Category.id_comp]
        exact h0
      have p₂ : val (e 0) ((𝟙 (Sp S) ≫ A.left) ≫ (Formalism.L2.Pj.homAt x0 σ).left) y J =
          val (e' 0) ((𝟙 (Sp S) ≫ A'.left) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left) y J' := by
        have q : (𝟙 (Sp S) ≫ A'.left) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left =
            (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left := congrArg (· ≫ _) (Category.id_comp _)
        have q' : (𝟙 (Sp S) ≫ A.left) ≫ (Formalism.L2.Pj.homAt x0 σ).left =
            (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left := q
        rw [q, q']
        refine (val_corr hJ hc₁ _).symm.trans ((val_tie w _ _ (e' 0) c hc₂ _ y hJ hJ').trans ?_)
        exact (congrArg₂ (· * ·) (prod_cube_left t' (fun q => Geo.Tor.gw w q y (J (q ≫ mp.φ)) (J' q)) _ _ _ hu)
          rfl).trans (_root_.one_mul _)
      refine (val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans ((congrArg₂ (· * ·)
        ((val_pull hJ _ _ _).trans p₁) ((val_pull hJ _ _ _).trans p₂)).trans ((_root_.mul_assoc _ _ _).trans
          (congrArg₂ (· * ·) rfl (Eq.symm ?_)))))
      exact (val_pull hJ' _ _ _).trans ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ' _ _ _)
        (val_pull hJ' _ _ _)))
    · refine (GermB.val_rigT _ _ _ _ _ y J hJ).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl
        (GermB.val_rigT _ _ _ _ _ y J' hJ').symm))
      have b : (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) ≫ mp.cm.e = 𝟙 (Sp S) ≫ (overAt x0 S).hom := by
        rw [mp.base]
        simp
      have a₁ : (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) ≫ eSec t'.G = o :=
        congrArg (· ≫ eSec t'.G) (Category.id_comp _)
      have a₂ : (𝟙 (Sp S) ≫ (overAt x0 S).hom) ≫ eSec t.G = o ≫ mp.φ := by
        rw [← b, ← a₁, Category.assoc, ← mp.cm.e_comm]
        exact (Category.assoc _ _ _).symm
      have q := pm _ (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) y (fun _ => J (o ≫ mp.φ)) (fun _ => J' o)
        (fun _ => (congrArg (fun r => (r ≫ mp.φ) y ∈ t.PP.L.U (J (o ≫ mp.φ))) a₁).mpr (hJ _))
        (fun _ => (congrArg (fun r => r y ∈ t'.PP.L.U (J' o)) a₁).mpr (hJ' _))
      rw [Fintype.prod_unique, zpow_one, b, a₁] at q
      exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans (q.trans (congrArg₂ (· * ·) rfl
        (val_of _ _ y J' _ (fun _ => congrArg J' a₁)).symm))
  constructor
  · intro h
    refine corr_of_val hL' fun y J' hJ' => ?_
    choose J hJ using fun χ : Sp S ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨k₁, k₂⟩ := key y J J' hJ hJ'
    exact mul_left_cancel (k₁.symm.trans ((val_corr hJ h _).trans k₂))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    choose J' hJ' using fun χ : Sp S ⟶ t'.G.left => exists_chart hL' (χ y)
    obtain ⟨k₁, k₂⟩ := key y J J' hJ hJ'
    exact k₁.trans ((congrArg₂ (· * ·) rfl (val_corr hJ' h _)).trans k₂.symm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidifiedIsoMapsCubicalGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open TopologicalSpace Opposite Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigCub

theorem cover_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have h : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem div_cover {X : Scheme.{0}} {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (x : X) :
    ∃ p, x ∈ (LB.div M L).U p := by
  obtain ⟨i, hi⟩ := cover_of_isLB hM x
  obtain ⟨j, hj⟩ := cover_of_isLB hL x
  exact ⟨(i, j), hi, hj⟩

theorem unit_eq_one_of_local {X : Scheme.{0}} {κ : Type} (V : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ V i)
    (v : Γ(X, ⊤)ˣ) (h : ∀ i, res (le_top : V i ≤ ⊤) v = 1) : v = 1 := by
  refine Units.ext ?_
  apply TopCat.Presheaf.section_ext X.sheaf ⊤
  intro x _
  obtain ⟨i, hi⟩ := hcov x
  have e1 := X.presheaf.germ_res_apply (homOfLE (le_top : V i ≤ ⊤)) x hi v.val
  have e3 : (X.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op).hom v.val = 1 := congrArg Units.val (h i)
  rw [e3, map_one] at e1
  exact e1.symm.trans (map_one _).symm

theorem linCombIso_punit {X Y : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) (φ0 : Y ⟶ X)
    (p : (PUnit.{1} → M.ι) × (PUnit.{1} → L.ι)) :
    (LB.linCombIso w (K := PUnit.{1}) (fun _ => φ0) (fun _ => 1)).s p =
      res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit.{1} => φ0) p.1 ⟨⟩))
        (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit.{1} => φ0) p.2 ⟨⟩)))
        (pullU φ0 _ (w.s (p.1 ⟨⟩, p.2 ⟨⟩))) := by
  simp only [LB.linCombIso, zpow_one]
  exact Fintype.prod_subsingleton _ PUnit.unit

section Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_eq (hGF : GlobalFnsSt) {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S}
    (m : SABMap t' t f) (hab : IsAbelianScheme t'.G) {w w₀ : LB.Iso t'.PP.L (t.PP.L.pull m.φ)}
    (hw : RigIso m w) (hw₀ : w₀.IsGen)
    (hr₀ : LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (m.cm.rigPull t.PP.L t.PP.rig)) : w = w₀ := by
  have hLp : (t.PP.L.pull m.φ).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB t.PP.L t.PP.isLB _ _
  obtain ⟨u, hu⟩ := exists_ratio_gen (div_cover hLp t'.PP.isLB) hw.1 hw₀
  suffices hu1 : u = 1 by
    cases w
    cases w₀
    congr 1
    funext p
    exact (hu p).trans (by rw [hu1, map_one, _root_.one_mul])
  apply unit_eq_one_of_eSec hGF t'.G hab u
  have hA : ((t'.PP.L).pull (eSec t'.G)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB t'.PP.L t'.PP.isLB _ _
  have hB : ((t.PP.L.pull m.φ).pull (eSec t'.G)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hLp _ _
  have hloc : ∀ p : ((t.PP.L.pull m.φ).pull (eSec t'.G)).ι × ((t'.PP.L).pull (eSec t'.G)).ι,
      res (le_top : ((t.PP.L.pull m.φ).pull (eSec t'.G)).U p.1 ⊓ ((t'.PP.L).pull (eSec t'.G)).U p.2 ≤ ⊤)
        (pullU (eSec t'.G) ⊤ u : Γ((𝟙_ (Over S')).left, ⊤)ˣ) = 1 := by
    rintro ⟨p1, p2⟩
    have e3 := mul_right_cancel ((hw.2 (p1, p2)).symm.trans (hr₀ (p1, p2)))
    have e3' := (linCombIso_punit w (eSec t'.G) (p1, p2)).symm.trans (e3.trans (linCombIso_punit w₀ (eSec t'.G) (p1, p2)))
    have hu' : ∀ a b, w.s (a, b) = res le_top u * w₀.s (a, b) := fun a b => hu (a, b)
    rw [hu', map_mul] at e3'
    have e5 := mul_right_cancel (((map_mul _ _ _).symm.trans e3').trans (_root_.one_mul _).symm)
    rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res] at e5
    exact (ReciprocityTheory.ChartRestriction.G.DVR.res_res' _ _ _).symm.trans e5
  have hv1 := unit_eq_one_of_local _ (fun y => by
      obtain ⟨p1, hp1⟩ := cover_of_isLB hB y
      obtain ⟨p2, hp2⟩ := cover_of_isLB hA y
      exact ⟨(p1, p2), hp1, hp2⟩) (pullU (eSec t'.G) ⊤ u : Γ((𝟙_ (Over S')).left, ⊤)ˣ) hloc
  exact congrArg Units.val hv1

end Rig

theorem rigIso_cub : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → IsAbelianScheme t'.G → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) := by
  intro hGF E _ _ _ H X0 X1 t t' f mp w hw hab
  obtain ⟨w₀, h₀, h₁, h₂⟩ := mp.lin
  rw [rigIso_eq hGF mp hab hw h₀ h₁]
  exact h₂

end GlobalTheory.RigCub
end
end

