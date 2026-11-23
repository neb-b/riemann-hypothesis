module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDieudonneFunctorGluedConnectedEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0616

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueWeightDecompositionRaynaudAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtDec

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem cv_act (Y : Ray oa) {T : Over (Sp R)} (t : T ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (x : T ⟶ Y.H) (χ : Q.X)
    (y : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L y J) :
    (GlobalTheory.TorusModel.cv (Y.Φ T ((t ≫ Y.i) * x)) χ y J : T.left.presheaf.stalk y) =
      gs (𝟙 T.left) y ⊤ (t.left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val) *
        GlobalTheory.TorusModel.cv (Y.Φ T x) χ y J := by
  have h := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x (t ≫ Y.i))).2 χ y J hJ
  have C : IsCub (DVR.th Q (T := T) y J) := isCub_cubV Q.cub hJ
  rw [(Y.Φ_i t).1, C.face₃, _root_.mul_one] at h
  rw [mul_comm (t ≫ Y.i) x, h, Units.val_mul, (Y.Φ_i t).2 χ y J hJ, _root_.mul_comm]
  exact congrArg (fun s => gs (𝟙 T.left) y ⊤ s * _) (GlobalTheory.SplitTorusPoints.coord_single t χ)

theorem preimage_stable (Y : Ray oa) (W : Q.P.A.left.Opens) :
    (snd (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H).left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) ≤
      ((fst (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H ≫ Y.i) * snd (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H).left ⁻¹ᵁ
        (Y.q.left ⁻¹ᵁ W) := by
  have := Y.q_linear.isMonHom
  exact fun p hp => GlobalTheory.LevelExpansion.act_mem Y.isKernel _ _ p hp

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec


open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv in
theorem isAffineHom_q : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa), IsAffineHom Y.q.left := by
  intro R _ _ D O _ _ _ oa Y
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem isWt_of_uu : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (V : Y.H.left.Opens) (u : Γ(Y.H.left, V)) (χ : Q.X),
    GlobalTheory.UU.IsWt Y.i V u χ → IsWt Y χ V u := by
  intro R _ _ Q O _ _ _ oa Y V u χ h S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have w : (x' * x⁻¹) ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by
    rw [← Hom.one_def, MonObj.mul_comp, hq, ← MonObj.mul_comp, mul_inv_cancel, MonObj.one_comp]
  let t := Y.isKernel.lift (x' * x⁻¹) (toUnit _) w
  have ht : t ≫ Y.i = x' * x⁻¹ := Y.isKernel.lift_fst _ _ _
  have hx' : (t ≫ Y.i) * x = x' := by rw [ht, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  have key : t.left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c χ) := fn_ext fun y _ => by
    choose J hJ using fun ψ : Sp S ⟶ Q.P.A.left => exists_chart Q.P.isLB (ψ y)
    have e1 := cv_act Y t x χ y J hJ
    rw [hx'] at e1
    have e2 := congrArg Units.val (hc χ y J hJ)
    rw [Units.val_mul, ← gs_unit _ y ⊤ trivial] at e2
    exact (Units.mul_left_inj _).1 (e1.symm.trans e2)
  have h₁ : ⊤ ≤ ((t ≫ Y.i) * x).left ⁻¹ᵁ V := by rw [hx']; exact hV'
  rw [WtAlg.valR_eq' _ _ hV', WtAlg.valR_eq' _ _ hV, ← GlobalTheory.TorusGrading.val_congr hx' h₁ hV' u, h _ t x h₁ hV, map_mul,
    key, Iso.inv_hom_id_apply]

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem uu_of_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (V : Y.H.left.Opens) (u : Γ(Y.H.left, V)) (χ : Q.X),
    IsWt Y χ V u → GlobalTheory.UU.IsWt Y.i V u χ := by
  intro R _ _ Q O _ _ _ oa Y V u χ h
  refine (GlobalTheory.CubCompare.isWt_iff_germ _ _ _ _).2 fun T z t x hx hx' => ?_
  obtain ⟨U, hU, hzU, hUle⟩ := exists_isAffineOpen_mem_and_subset (x := z)
    (U := x.left ⁻¹ᵁ V ⊓ ((t ≫ Y.i) * x).left ⁻¹ᵁ V) ⟨hx, hx'⟩
  let ρ : Sp Γ(T.left, U) ⟶ T.left := hU.fromSpec
  let φ : R →+* Γ(T.left, U) := (Spec.preimage (ρ ≫ T.hom)).hom
  have hφ : ρ ≫ T.hom = spMap φ := by simp [spMap, φ]
  let k : Over.mk (spMap φ) ⟶ T := Over.homMk ρ hφ
  have hr : ∀ p, ρ p ∈ U := fun p => by
    have : ρ p ∈ Set.range ρ := ⟨p, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨z', rfl⟩ : z ∈ Set.range ρ := by rw [hU.range_fromSpec]; exact hzU
  have hV₁ : ⊤ ≤ (k ≫ x).left ⁻¹ᵁ V := fun p _ => (hUle (hr p)).1
  have hV₂ : ⊤ ≤ (k ≫ ((t ≫ Y.i) * x)).left ⁻¹ᵁ V := fun p _ => (hUle (hr p)).2
  let c : Q.X → (Γ(T.left, U))ˣ := fun χ' => Units.map (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).hom.hom.toMonoidHom
    (Units.map (k ≫ t).left.appTop.hom.toMonoidHom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ'))
  have hcv : ∀ χ', (unitOn (c χ')).val = (k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ').val := fun χ' => by
    show (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).hom.hom
      ((k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ').val)) = _
    exact Iso.hom_inv_id_apply _ _
  have e : k ≫ ((t ≫ Y.i) * x) = ((k ≫ t) ≫ Y.i) * (k ≫ x) := by rw [MonObj.comp_mul, Category.assoc]
  have hc : ∀ χ' y J, Good Q.P.L y J → val ((Y.Φ _ (k ≫ ((t ≫ Y.i) * x))).s χ') (𝟙 _) y J =
      gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ')) * val ((Y.Φ _ (k ≫ x)).s χ') (𝟙 _) y J := by
    intro χ' y J hJ
    rw [e]
    apply Units.ext
    rw [Units.val_mul, ← gs_unit _ y ⊤ trivial, hcv]
    exact cv_act Y (k ≫ t) (k ≫ x) χ' y J hJ
  have hq : (k ≫ ((t ≫ Y.i) * x)) ≫ Y.q = (k ≫ x) ≫ Y.q := by
    have := Y.q_linear.isMonHom
    exact Over.OverMorphism.ext (by simp only [Over.comp_left, Category.assoc, GlobalTheory.LevelExpansion.act_q Y.isKernel t x])
  have E := h Γ(T.left, U) φ (k ≫ x) (k ≫ ((t ≫ Y.i) * x)) c _ _ rfl rfl hV₁ hV₂ hq hc
  rw [WtAlg.valR_eq' _ _ hV₂, WtAlg.valR_eq' _ _ hV₁] at E
  have E' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom E
  rw [Iso.hom_inv_id_apply, map_mul, Iso.hom_inv_id_apply] at E'
  have E'' := congrArg (gs (𝟙 _) z' ⊤) E'
  rw [GlobalTheory.CubCompare.gs_appLE, gs_mul _ z' ⊤ trivial, GlobalTheory.CubCompare.gs_appLE] at E''
  have hcv' : (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom (c χ : Γ(T.left, U)) =
      (k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val := hcv χ
  have g1 : gs (𝟙 _) z' ⊤ ((k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val) =
      gs (k ≫ t).left z' ⊤ (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val :=
    (gs_pull (𝟙 _) (k ≫ t).left z' ⊤ trivial _).trans (by rw [Category.id_comp])
  rw [hcv', g1] at E''
  apply (ConcreteCategory.bijective_of_isIso (ρ.stalkMap z')).1
  show (ρ.stalkMap z').hom _ = (ρ.stalkMap z').hom _
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv.charV
  rw [map_mul, ← GlobalTheory.CubCompare.gs_comp ρ _ V z' hx' u, ← GlobalTheory.CubCompare.gs_comp ρ _ V z' hx u,
    ← gs_unit _ _ ⊤ trivial, ← GlobalTheory.CubCompare.gs_comp ρ _ ⊤ z' trivial]
  exact E''

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem existsUnique_weights : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t) := by
  intro R _ _ Q O _ _ _ oa Y W hW f
  have hi : IsMonHom Y.i := Y.i_linear.isMonHom
  have := isAffineHom_q Y
  obtain ⟨ex, un⟩ := GlobalTheory.functions_graded_by_weights (Sp R) Y.H (GlobalTheory.RayEv.Chr Q) Y.i hi _ (hW.preimage Y.q.left)
    (preimage_stable Y W)
  obtain ⟨a, ha, rfl⟩ := ex f
  refine ⟨a, ⟨fun χ => isWt_of_uu Y _ _ χ (ha χ), rfl⟩, fun F hF => ?_⟩
  let F' : GlobalTheory.RayEv.Chr Q →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W) := F
  have e := un (F' - a) (fun χ => uu_of_isWt Y _ _ χ (WtAlg.isWt_sub (hF.1 χ) (isWt_of_uu Y _ _ χ (ha χ))))
    (by rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]; exact sub_eq_zero.2 hF.2.symm)
  exact sub_eq_zero.1 e

end GlobalTheory.Heat.WtDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartOfPeriodTauMonomial
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTau

theorem commGroup_seven_term_product_rearrange {G : Type} [CommGroup G] (a b c A B C D : G) :
    a * b * c * A * (b * B)⁻¹ * (c * C)⁻¹ * D⁻¹ = a * (A * B⁻¹ * C⁻¹ * D⁻¹) := by
  simp only [mul_inv]
  calc _ = a * (A * B⁻¹ * C⁻¹ * D⁻¹) * (b * b⁻¹) * (c * c⁻¹) := by ac_rfl
    _ = _ := by simp


set_option maxHeartbeats 1000000 in
theorem exists_isUnitTau : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → (∀ i y z, gam i y z = gam i z y) → (∀ i, t i ≠ 0) → ∀ y z, ∃ τ₀, IsUnitTau Q t gam y z τ₀ := by
  intro R _ _ Q m t gam hM hsym ht y z
  obtain ⟨n1, p1, hp1⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM (y + z)
  obtain ⟨n2, p2, hp2⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM y
  obtain ⟨n3, p3, hp3⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM z
  have hc0 : Q.c 0 = η[Q.P.A] := by
    have h := Q.c_add 0 0
    rw [add_zero] at h
    have h' : Q.c 0 * Q.c 0 = Q.c 0 := h.symm
    have h1 : Q.c 0 = 1 := mul_eq_left.1 h'
    rw [h1, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hc0' : (Q.c 0).left = eSec Q.P.A := by rw [hc0]; rfl
  let T := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ p1 (LB.invGen Q.P.L _ _ p2))
    (LB.invGen Q.P.L _ _ p3)) (LB.invGen Q.P.L _ _ Q.rig)

  have hT : T.IsGen :=
    LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _
      (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ hp1.1 (LB.isGen_invGen (L := Q.P.L) _ _ _ hp2.1))
      (LB.isGen_invGen (L := Q.P.L) _ _ _ hp3.1)) (LB.isGen_invGen (L := Q.P.L) _ _ _ Q.rig_gen)
  have hF : FormEq (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (Q.c (y + z)).left) (fun _ : PUnit => (Q.c y).left))
      (fun _ : PUnit => (Q.c z).left)) (fun _ : PUnit => eSec Q.P.A))
      (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => -(-1 : ℤ))) (fun _ : PUnit => -(-1 : ℤ)))
        (fun _ : PUnit => -(1 : ℤ)))
      (K' := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hc0', neg_neg]
    simp [Matrix.vecHead, Matrix.vecTail, hc0']
  obtain ⟨τ₀, hτ, hv⟩ := exists_gen Q.P.isLB hF T hT
  refine ⟨τ₀, hτ, ?_⟩

  obtain ⟨-, hn1, e1, he1, hv1⟩ := hp1
  obtain ⟨-, hn2, e2, he2, hv2⟩ := hp2
  obtain ⟨-, hn3, e3, he3, hv3⟩ := hp3
  have hne : ∀ i, algebraMap R (FractionRing R) (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (ht i)
  let e' : (FractionRing R)ˣ := ∏ i, Units.mk0 _ (hne i) ^ gam i y z
  have he' : (e' : FractionRing R) = ∏ i, algebraMap R _ (t i) ^ gam i y z := by
    simp [e', Units.coe_prod]
  have hexp : ∀ i, (n1 i : ℤ) = gam i y z + n2 i + n3 i := by
    intro i
    have a := hn1 i
    have b := hn2 i
    have c := hn3 i
    have s := hsym i y z
    simp only [map_add (f := _), LinearMap.add_apply] at a
    linarith
  have hee : e1 = e' * e2 * e3 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he1, he2, he3, he']
    simp only [map_prod, map_pow]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i), hexp i]
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  refine ⟨e', he', fun zz J hJ => ?_⟩
  rw [hv _ _ zz J hJ]
  simp only [DegPre.tau, DegPre.rigK, T, val_mul hJ, val_inv, val_pull hJ]
  rw [hv1 zz J hJ, hv2 zz J hJ, hv3 zz J hJ, hee, hu, hu, map_mul, map_mul, Category.id_comp]
  exact commGroup_seven_term_product_rearrange _ _ _ _ _ _ _

end GlobalTheory.UnitTau
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartPeriodTauZeroValueOneStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  intro E _ _ _ H k _ _ m d t P gam mu
  exact GlobalTheory.UnitTauZero.exists_isUnitTau_zero_val_one E H k m d t P gam mu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitValueTranslatedBundleSectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_value_translated_bundleSection : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (α ν : Q.X) (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k))), (¬ ∀ j, s.f j = 0) → ∃ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J ∧ IsUnit (sval s (DegPre.trF Q (FractionRing R) ν).left z J) := by
  first | exact @GlobalTheory.UnitPt.exists_unit_sval | exact GlobalTheory.UnitPt.exists_unit_sval | (intros; apply GlobalTheory.UnitPt.exists_unit_sval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldCoeffsGluedFromAffineOpens
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffGlue

theorem affine_cover {X : Scheme.{0}} (O : X.Opens) :
    O ≤ ⨆ l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O}, l.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (O : Set X) from hx) O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, fun y hy => hle hy⟩, hxU⟩

theorem exists_coeff : ∀ {X : Scheme.{0}} {n : ℕ} (W : X.Opens) (δ : Fld X) (dd : Fin n → Fld X), IsField W δ → (∀ a, IsField ⊤ (dd a)) →
    (∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → V ≤ W → V' ≤ V →
      ∃! c : Fin n → Γ(X, V'), ∀ f : Γ(X, V), rsT (δ V f) V' = ∑ a, c a * rsT (dd a V f) V') →
    ∃ c : Fin n → Γ(X, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro X n W δ dd hδ hdd H
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  choose c hc using fun j : J => (H j.1 j.1 j.2.1 j.2.1 j.2.2 le_rfl).exists
  have hl : ∀ (l : J) (O : X.Opens) (h : l.1 ≤ O), O ≤ W → ∀ f : Γ(X, O),
      rsT (δ O f) l.1 = ∑ a, c l a * rsT (dd a O f) l.1 := by
    intro l O h hO f
    have e1 := hδ.2.2 O l.1 h hO f
    have e2 := hc l (resG X h f)
    simp only [GlobalTheory.KS.rsT_self] at e2
    rw [GlobalTheory.KS.rsT_of_le h, ← e1, e2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.2 O l.1 h le_top f, GlobalTheory.KS.rsT_of_le h]
  have sub : ∀ j l : J, l.1 ≤ j.1 → ∀ a, rsT (c j a) l.1 = c l a := by
    intro j l h a
    refine congrFun ((H j.1 l.1 j.2.1 l.2.1 j.2.2 h).unique (y₁ := fun a => rsT (c j a) l.1) (y₂ := c l) ?_ ?_) a
    · intro f
      have := hc j f
      simp only [GlobalTheory.KS.rsT_self] at this
      rw [this, GlobalTheory.KS.rsT_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [GlobalTheory.KS.rsT_mul]
    · exact hl l j.1 h j.2.2
  have glue : ∀ a, ∃ s : Γ(X, W), ∀ j : J, rsT s j.1 = c j a := fun a => by
    refine GlobalTheory.KS.exists_rsT_eq (fun j : J => j.1) (fun j => j.2.2) (affine_cover W) (fun j => c j a)
      fun j k => ?_
    refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ j.1 ⊓ k.1} => l.1)
      (fun l => l.2.2) (affine_cover _) _ _ fun l => ?_
    have hj : l.1 ≤ j.1 := l.2.2.trans inf_le_left
    have hk : l.1 ≤ k.1 := l.2.2.trans inf_le_right
    rw [GlobalTheory.KS.rsT_rsT inf_le_left l.2.2, GlobalTheory.KS.rsT_rsT inf_le_right l.2.2,
      sub j ⟨l.1, l.2.1, hj.trans j.2.2⟩ hj, sub k ⟨l.1, l.2.1, hk.trans k.2.2⟩ hk]
  choose s hs using glue
  refine ⟨s, fun O hO f => ?_⟩
  refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O} => l.1) (fun l => l.2.2)
    (affine_cover O) _ _ fun l => ?_
  rw [hl ⟨l.1, l.2.1, l.2.2.trans hO⟩ O l.2.2 hO f, GlobalTheory.KS.rsT_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_rsT hO l.2.2, hs a ⟨l.1, l.2.1, l.2.2.trans hO⟩]

end GlobalTheory.VertCoeffGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pairing_factor_mumford : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_finite_extension_mumford_bundle_polarisation R hR G
    (RetractGeneric.isAbelianScheme_generic R A' G' hG' U'.gen G hG inc pr hinc hpr hip) _
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb U'.LG.isLB _ _) _)
    (FactorSym.main R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_add R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_diag_relAmple R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (pairing_kernel_trivial R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTheoryMu
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

def theory (p : ℕ) [Fact p.Prime] : Theory p :=
  let Bc := (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose
  let Be := (_root_.GlobalTheory.dieuBase_isEt_of_isConn p Bc).choose
  let hB := _root_.GlobalTheory.Dieu.Glue.exists_katz_etDual p Bc Be (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose_spec (_root_.GlobalTheory.dieuBase_isEt_of_isConn p Bc).choose_spec
  let hV := _root_.GlobalTheory.Dieu.exists_V_of_base p hB.choose
  { base := hB.choose, katz := hB.choose_spec.1, etDual := hB.choose_spec.2, V := hV.choose,
    F_V := hV.choose_spec.1, V_F := hV.choose_spec.2 }

end GlobalTheory.Dieu
end
end

