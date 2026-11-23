module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedIsoPullbackMulByMStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsKeyPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow

theorem exists_isKeyPow : ∀ (R : Type) [CommRing R] (x : KeyIn R) (j : ℕ), 1 ≤ j → ∃ y, GlobalTheory.KeyPow.IsKeyPow y x j := by
  intro R _ x j hj
  have := x.P.isAb.comm
  obtain ⟨hL, hS, hr⟩ := BoxPower.boxPower_basic R x.P j
  have hr' := hr x.rig x.rig_gen
  have hA : IsAbelianScheme (Out.powObj x.P.A j) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
    exact AbelianSchemeGerms.isAbelianScheme_powObj x.P.A x.P.isAb n
  let P' : Out.PolAV (Sp R) :=
    { A := Out.powObj x.P.A j
      isAb := hA
      g := j * x.P.g
      smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ j x.P.smoothDim
      L := Out.boxLB x.P.L (Out.powPr x.P.A (n := j))
      isLB := hL
      rigid := ⟨_, hr'⟩
      sym := hS
      ample := relAmple_powObj_boxLB R x.P j
      ktriv := kTriv_boxLB_powObj R x.P j }
  obtain ⟨th, hth, hne⟩ := BoxSection.exists_boxSec _ _ _ j (Out.powIsPowGrp x.P.A j) x.P.L (fun _ => x.th) x.P.isLB
  obtain ⟨v, hv, hvp⟩ := PowLie.isLieBasis_pow R _ _ j x.P.g (Out.powIsPowGrp x.P.A j) x.v x.basis
  refine ⟨⟨P', Nat.mul_pos hj x.g_pos, _, hr', th, fun s => hne s fun _ => x.th_ne s, v, hv⟩,
    ⟨Out.powIsPowGrp x.P.A j, idIso _, idIso_isGen hL⟩, rfl, fun p => hr' p.1 p.2, fun jj b h => ?_, hvp⟩
  refine Eq.trans ?_ (th.compat jj b)
  rw [hth jj fun i => LB.wchart_le x.P.L _ jj i, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (congrArg (fun f => f.hom (x.th.f (jj i))) (Scheme.Hom.appLE_map (Out.powPr x.P.A i).left
    (LB.wchart_le x.P.L (fun i => (Out.powPr x.P.A i).left) jj i) (homOfLE (inf_le_left (b := P'.L.U b))).op)).symm

end GlobalTheory.KeyPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBOn
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem exists_keyPB_on : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ y.P.A.left) (hg : 1 ≤ P'.g), P'.g = y.P.g → IsGrpPullback P'.A y.P.A (spMap f) φ → LBIso P'.L (y.P.L.pull φ) → ∃ rig hr th hth v hv, KeyPB ⟨P', hg, rig, hr, th, hth, v, hv⟩ y f := by
  intro R R' _ _ f x P' φ hg e h ⟨w, hw₀⟩
  have hL' := P'.isLB
  have hw := (isGen_iff _).1 hw₀
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr₀ : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨rig, hr, hm⟩ := Transport.exists_transport (LB.isLB_pull hL' (eSec P'.A))
    (LB.isLB_pull (LB.isLB_pull x.P.isLB φ) (eSec P'.A))
    (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) (DVR.linCombIso_isGen w hw₀ _ _) _ hr₀
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R R' f x.P.A P'.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  refine ⟨rig, hr, th', fun s => ?_, fun i => v' (i.cast e), isLieBasis_cast e hb',
    φ, he, w, e, Chart.dualMapR f, h, hw₀, hm,
    appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨k', hk'⟩ := exists_chart hL' y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨k', hk', ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e' := hth' _ (𝟙 _) y k k' hk hk'
    rw [Category.id_comp] at e'
    exact isUnit_of_mul_isUnit_right (e' ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyTf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_keyPB_ring {R R' : Type} [CommRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R') :
    ∃ x' : KeyIn R', KeyPB x' x f := by
  have h := isGrpPullback_pullback x.P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left := pullback.fst x.P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := LB.isLB_pull x.P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj x.P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb
      g := x.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 x.P.smoothDim
      L := x.P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h x.P.rigid
      sym := PolBaseChange.sym_pull h x.P.sym
      ample := relAmple_pull h.1 x.P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
      ktriv := kTriv_pull h x.P.isLB hL' hw x.P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R R' f x.P.A P'.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  refine ⟨⟨P', x.g_pos, _, hr, th', fun s => ?_, v', hb'⟩,
    φ, he, idIso _, rfl, Chart.dualMapR f, h, idIso_isGen hL', fun p => hr p.1 p.2,
    appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, hv'⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem keyIn_baseChange : Out.PolBaseChangeSt → ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R'),
    ∃ x' : KeyIn R', KeyPB x' x f :=
  fun _ _ _ _ _ x f => exists_keyPB_ring x f

end GlobalTheory.KeyPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSquareDeterminantComparisonIsAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilDet

theorem eq_zero_of_eigen {K B G Y N : Type} [Field K] [CommRing B] [IsDomain B] [Monoid G] [Fintype N]
    (κ : K →+* B) (χ : N → G →* B) (hχ : Function.Injective χ) (act : G → Y → Y) (F : N → Y → B)
    (hF : ∀ i v y, F i (act v y) = χ i v * F i y) (hne : ∀ i, ∃ y, F i y ≠ 0) (c : N → K)
    (h : ∀ y, ∑ i, κ (c i) * F i y = 0) : c = 0 := by
  funext i
  obtain ⟨y, hy⟩ := hne i
  have li := (linearIndependent_monoidHom G B).comp χ hχ
  have := Fintype.linearIndependent_iff.1 li (fun j => κ (c j) * F j y) (by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
    rw [← h (act v y)]
    exact Finset.sum_congr rfl fun j _ => by rw [hF]; ring) i
  exact κ.injective (((mul_eq_zero.1 this).resolve_right hy).trans (map_zero κ).symm)

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))

theorem gs_cst {R : Type} [CommRing R] {Y Z : Scheme.{0}} (f : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (cst f ⊤ a) = gs (r ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (gs_res r z (V := ⊤) le_top trivial _).trans (gs_pull r f z ⊤ trivial _)

section Map

variable {R : Type} [CommRing R] (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ)

theorem mul_comp_alMap {Z : Over (Sp R)} (a b : Z ⟶ Out.powObj x.P.A 4) (r : Fin 4) (ζ : Pt x) :
    (a * b) ≫ alMap x al r ζ = (a ≫ alMap x al r 1) * (b ≫ alMap x al r ζ) := by
  haveI := x.P.isAb.comm
  have e : ∀ (a : Z ⟶ Out.powObj x.P.A 4) (ζ : Pt x), a ≫ alMap x al r ζ =
      (∏ c, (a ≫ Out.powPr x.P.A c) ^ al r c) * (toUnit Z ≫ ζ) := fun a ζ => by
    simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
      GrpObj.comp_zpow, MonObj.comp_one, Fin.prod_univ_succ, Fin.prod_univ_zero, comp_toUnit_assoc]
  simp only [e, MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib, MonObj.comp_one, _root_.mul_one,
    _root_.mul_assoc]

def ker : Submonoid (𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) where
  carrier := {v | ∀ r, v ≫ alMap x al r 1 = 1}
  one_mem' := fun r => by
    haveI := x.P.isAb.comm
    have := mul_comp_alMap x al (1 : 𝟙_ (Over (Sp R)) ⟶ _) 1 r 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  mul_mem' := fun {a b} ha hb r => by rw [mul_comp_alMap, ha r, hb r, _root_.mul_one]

abbrev tr (v : 𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) : Out.powObj x.P.A 4 ⟶ Out.powObj x.P.A 4 :=
  (toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)

theorem tr_alMap (v : ker x al) (r : Fin 4) (ζ : Pt x) : tr x v.1 ≫ alMap x al r ζ = alMap x al r ζ := by
  rw [mul_comp_alMap, Category.assoc, v.2 r, MonObj.comp_one, _root_.one_mul, Category.id_comp]

theorem pt_tr (y v : 𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) : y ≫ tr x v = v * y := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

end Map

theorem exists_transl_ratio (laws : Out.Laws) {R : Type} [CommRing R] (x : KeyIn R) (m : ℕ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))))
    (hw : w.IsGen) (hw' : w'.IsGen) (v : ker x al) :
    ∃ a : Γ(Sp R, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) (J), Good x.P.L z J →
      (val w (r ≫ (tr x v.1).left) z J * (val w' (r ≫ (tr x v.1).left) z J)⁻¹ *
        (val w r z J * (val w' r z J)⁻¹)⁻¹).val = gs (r ≫ (Out.powObj x.P.A 4).hom) z ⊤ a := by
  have hu := DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.invGen_isGen _ _ _ _ hw')
  obtain ⟨a, ha⟩ := exists_ratio x.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Over.comp_left, tr_alMap, zpow_neg,
        Finset.prod_inv_distrib, zpow_one, inv_inv]
      simp only [mul_inv, inv_inv, mul_mul_mul_comm _ _⁻¹, inv_mul_cancel])
    (Out.powObj x.P.A 4).hom (laws.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_powObj _ x.P.isAb 3)).2
    (DVR.pullGen_isGen _ _ _ _ hu (tr x v.1).left) hu
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have := ha Z r z J hJ
  rwa [val_pull hJ, val_mul hJ, val_mul hJ, val_inv, val_inv] at this

theorem exists_l2Val : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → ∃ lam, IsSquareDeterminantComparison x m al b lam := by
  intro laws K _ _ x m al b hm hal hb
  classical
  have hm0 : m ≠ 0 := fun h => hm (by rw [h, Nat.cast_zero])
  have hL := x.P.isLB
  obtain ⟨ξ, hξ, hk⟩ := _root_.GlobalTheory.KeyKa.exists_enum_ker_transpose laws K x m al hm hal
  obtain ⟨mu, hmu, hmuv⟩ := GlobalTheory.T.exists_normalised_iso_pullback_mul_by_m laws K x m
  choose w hw using fun I => GlobalTheory.SimilPull.exists_gen_similitude_pull laws K x m al (ξ I) hal (hk I)
  choose rho hrho using fun I => GlobalTheory.T.exists_normalising_unit_similitude_origin K x m al (ξ I) mu (w I) hm0 hal (hk I) hmu (hw I)
  choose s hs using fun I => GlobalTheory.T.exists_section_boxProduct_div_generator _ _ x.P.L hL (Fin 4) (Fin 4) _ _ (m : ℤ) x.th (w I) (hw I)
  choose Q hQ using fun I => GlobalTheory.T.boxProducts_basis_span_powObj_sections K x m _ b hb 4 (s I)
  have hdet : (Matrix.of Q).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hcQ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨I₀, -⟩ := Function.ne_iff.1 hc
    refine hc ?_
    let S : Over (Sp K) := 𝟙_ _
    let T := Out.powObj x.P.A 4
    haveI : IsIntegral S.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of K)))
    haveI : Subsingleton S.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    let p : S.left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : S.left ⟶ x.P.A.left => exists_chart hL (χ p)
    replace hJ : Good x.P.L p J := hJ
    let ev : Γ(S.left, ⊤) →+* S.left.presheaf.stalk p := (S.left.presheaf.germ ⊤ p trivial).hom
    have hev : ∀ (y : S ⟶ T) a, gs (y.left ≫ T.hom) p ⊤ a = ev a := fun y a => by
      rw [Over.w y]
      exact gs_eq (𝟙 S.left) p ⊤ trivial a
    let κ : K →+* S.left.presheaf.stalk p := ev.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    choose a ha using fun I v => exists_transl_ratio laws x m al (ξ I₀) (ξ I) (w I₀) (w I) (hw I₀) (hw I) v
    let u : (Fin 4 → Fin (m ^ x.P.g)) → (S ⟶ T) → (S.left.presheaf.stalk p)ˣ := fun I y =>
      val (w I₀) y.left p J * (val (w I) y.left p J)⁻¹
    have hu : ∀ I (v : ker x al) (y : S ⟶ T), (u I (v.1 * y)).val = ev (a I v) * (u I y).val := fun I v y => by
      have := ha I v _ y.left p J hJ
      rw [hev, ← Over.comp_left, pt_tr] at this
      rw [← this, ← Units.val_mul, inv_mul_cancel_right]
    let χ : (Fin 4 → Fin (m ^ x.P.g)) → ker x al →* S.left.presheaf.stalk p := fun I =>
      { toFun := fun v => ev (a I v)
        map_one' := by
          have := hu I 1 1
          rw [Submonoid.coe_one, _root_.one_mul] at this
          exact (Units.mul_left_inj (u I 1)).1 (this.symm.trans (_root_.one_mul _).symm)
        map_mul' := fun v v' => by
          have := hu I (v * v') 1
          rw [Submonoid.coe_mul, _root_.mul_assoc, hu, hu, ← _root_.mul_assoc] at this
          exact ((Units.mul_left_inj (u I 1)).1 this).symm }
    have hχ : Function.Injective χ := fun I I' h => by
      by_contra hne
      obtain ⟨r, hr⟩ := hξ I I' hne p
      have e := GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant laws K x m al (ξ I) (ξ I') (w I) (w I') hm hal (hw I) (hw I') (fun v hv Z r z J hJ => by
        have e₁ : a I ⟨v, hv⟩ = a I' ⟨v, hv⟩ := fn_ext (X := S.left) fun y _ => by
          obtain rfl : y = p := Subsingleton.elim _ _
          exact (gs_eq (𝟙 S.left) p ⊤ trivial _).trans ((DFunLike.congr_fun h ⟨v, hv⟩).trans
            (gs_eq (𝟙 S.left) p ⊤ trivial _).symm)
        have e₂ := Units.ext ((ha I ⟨v, hv⟩ Z r z J hJ).trans (e₁ ▸ (ha I' ⟨v, hv⟩ Z r z J hJ).symm))
        have alg : ∀ {U : Type} [CommGroup U] (A B B' C D D' : U),
            A * B⁻¹ * (C * D⁻¹)⁻¹ = A * B'⁻¹ * (C * D'⁻¹)⁻¹ → B * D' = B' * D := fun A B B' C D D' h => by
          rw [mul_inv, mul_inv, inv_inv, inv_inv, _root_.mul_assoc, _root_.mul_assoc, mul_right_inj, mul_left_comm,
            mul_left_comm B'⁻¹, mul_right_inj, inv_mul_eq_iff_eq_mul] at h
          rw [h, mul_left_comm B', mul_inv_cancel_left]
        exact alg _ _ _ _ _ _ e₂)
      exact hr (by rw [e])
    let θ : (Fin 4 → Fin (m ^ x.P.g)) → (S ⟶ T) → S.left.presheaf.stalk p := fun I y =>
      ∏ r, gs (y.left ≫ (alMap x al r (ξ I r)).left) p _ (x.th.f (J (y.left ≫ (alMap x al r (ξ I r)).left)))
    refine eq_zero_of_eigen κ χ hχ (fun v y => v.1 * y) (fun I y => θ I y * (u I y).val) (fun I v y => ?_)
      (fun I => ?_) c (fun y => ?_)
    · have e : θ I (v.1 * y) = θ I y := Finset.prod_congr rfl fun r _ =>
        congrArg (fun ψ : S.left ⟶ x.P.A.left => gs ψ p _ (x.th.f (J ψ))) (by
          rw [← Over.comp_left, ← Over.comp_left, ← pt_tr, Category.assoc, tr_alMap])
      simp only [hu, e]
      exact mul_left_comm _ _ _
    · obtain ⟨y, hy⟩ := _root_.GlobalTheory.SimilNonvan.exists_pt_isUnit laws K x m al (ξ I) hm hal
      exact ⟨y, mul_ne_zero (Finset.prod_ne_zero_iff.2 fun r _ => (hy p J hJ r).ne_zero) (Units.ne_zero _)⟩
    · have e : ∀ I, θ I y * (u I y).val = (val (w I₀) y.left p J).val * ∑ I', κ (Q I I') *
          ∏ c, gs (y.left ≫ (Out.powPr x.P.A c).left) p _ ((b (I' c)).f (J (y.left ≫ (Out.powPr x.P.A c).left))) :=
        fun I => by
        have e₁ : θ I y = _ := hs I _ y.left p J hJ
        rw [e₁, hQ I _ y.left p J hJ, mul_right_comm, ← Units.val_mul, mul_comm (val (w I) y.left p J),
          inv_mul_cancel_right]
        refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
        rw [gs_cst, hev]
        rfl
      simp only [e, mul_left_comm _ (val (w I₀) y.left p J).val, ← Finset.mul_sum]
      refine mul_eq_zero_of_right _ ?_
      simp only [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun I' _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Finset.sum_mul, ← map_sum, show ∑ I, c I * Q I I' = 0 from congrFun hcQ I', map_zero, zero_mul]
  refine ⟨Units.mk0 _ hdet ^ (2 * m ^ 2) * ∏ I, rho I ^ 2, ξ, mu, w, Matrix.of Q, rho, hξ, hk, hmu, hw,
    fun p J hJ => ⟨hmuv p J hJ, fun I => hrho I p J hJ⟩, fun I y J hJ => ?_, by simp⟩
  have e := hs I _ (𝟙 _) y J hJ
  rw [hQ I _ (𝟙 _) y J hJ] at e
  have i : ∀ (f : ∀ j, Γ(x.P.A.left, x.P.L.U j)) (ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left),
      gs (𝟙 _ ≫ ψ) y _ (f (J (𝟙 _ ≫ ψ))) = gs ψ y _ (f (J ψ)) := fun f ψ => by rw [Category.id_comp]
  exact (Finset.prod_congr rfl fun r _ => (i _ _).symm).trans (e.trans (congrArg _ (Finset.sum_congr rfl fun I' _ =>
    congrArg _ (Finset.prod_congr rfl fun c _ => i (b (I' c)).f _))))

end GlobalTheory.SimilDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem keyPB_id : ∀ (R : Type) [CommRing R] (x : KeyIn R), KeyPB x x (RingHom.id R) :=
  fun _ _ x => GlobalTheory.KeyPow.keyPB_refl x

end GlobalTheory
end

