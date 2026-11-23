module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2853

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartAppLEEq
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

namespace GlobalTheory.LocReg

theorem chart_appLE_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), ∃ hg : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1, ((ξ ≫ genι Y).appLE U.1 ⊤ hg).hom = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx) := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx
  have hx' : (ξ ≫ genι Y) (closedPoint (CommRingCat.of (ChartRing k m d))) ∈ U.1 := hx
  refine ⟨(Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ genι Y) hx').ge, ?_⟩
  have key : (gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) _ hx ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appLE (genι Y ⁻¹ᵁ U.1) ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  have e : (ξ ≫ genι Y).appLE U.1 ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ genι Y) hx').ge =
      (genι Y).app U.1 ≫ (gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) _ hx ≫ Scheme.stalkClosedPointTo ξ ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv := by
    rw [reassoc_of% key, Iso.hom_inv_id, Category.comp_id, Scheme.Hom.comp_appLE]
  rw [e]
  rfl

end GlobalTheory.LocReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionEqValueMulUnitPowFractionField
section
set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FracPt

theorem stalkIso_gs {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (f : Sp K ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (stalkClosedPointIso (CommRingCat.of K)).hom.hom (gs f (closedPoint K) U a) = valR f U a := by
  have e1 : gs f (closedPoint K) U a = (Sp K).presheaf.germ ⊤ (closedPoint K) trivial ((f.appLE U ⊤ h).hom a) := by
    erw [gs_eq f _ U (h trivial)]
    rw [← TopCat.Presheaf.germ_res_apply (Sp K).presheaf (homOfLE h) (closedPoint K) trivial]
    rfl
  erw [e1]
  rw [valR, dite_eq_left h]
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of K)]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.FracPt

namespace GlobalTheory.FracPt

theorem valR_spMap_const {Ω K : Type} [CommRing Ω] [CommRing K] (f : Ω →+* K) (ω : Ω) :
    valR (spMap f) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = f ω := by
  have h : ⊤ ≤ spMap f ⁻¹ᵁ ⊤ := le_rfl
  rw [valR, dite_eq_left h]
  calc _ = ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom f).hom
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) := by
          rw [← Scheme.ΓSpecIso_naturality]; rfl
    _ = f ω := by
          have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = ω := by
            rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
          rw [CommRingCat.hom_comp, RingHom.comp_apply, e, CommRingCat.hom_ofHom]

theorem chart_eq_value_mul_pow : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω]
    (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (j : L.ι) (O : X.Opens), O ≤ L.U j →
    ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → ∃ e₀ : (FractionRing Ω)ˣ,
      ∀ (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 _) L x g k σ ω →
        valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (rsT (σ.f fun _ => j) O) =
          algebraMap Ω (FractionRing Ω) ω * (e₀ : FractionRing Ω) ^ k := by
  intro X L hL Ω _ _ x g j O hO hxO
  let ηF := spMap (algebraMap Ω (FractionRing Ω))
  let z : Sp (FractionRing Ω) := closedPoint (FractionRing Ω)
  have hz : ((ηF ≫ x) ≫ 𝟙 X) z ∈ L.U j := by
    rw [Category.comp_id]; exact hO (hxO trivial)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := PUnit) (fun _ => (ηF ≫ x) ≫ 𝟙 X) (fun _ => j)
    (fun _ _ _ => rfl) (fun _ => hz)
  let φ := (stalkClosedPointIso (CommRingCat.of (FractionRing Ω))).hom.hom
  refine ⟨Units.map φ.toMonoidHom (val g ηF z J), fun k σ ω hv => ?_⟩
  have e := congrArg φ (hv _ ηF z J hJ)
  have hOW : O ≤ (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ))).U (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hO hy
  rw [sval_of σ (ηF ≫ x) z J (fun _ => j) (fun _ => hJj PUnit.unit)] at e
  erw [← gs_res (ηF ≫ x) z hOW (hxO trivial) (σ.f fun _ => j)] at e
  rw [map_mul, Units.val_pow_eq_pow_val, map_pow] at e
  have e1 := stalkIso_gs (ηF ≫ x) O hxO ((X.presheaf.map (homOfLE hOW).op).hom (σ.f fun _ => j))
  have e2 := stalkIso_gs ηF ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)
  rw [valR_spMap_const] at e2
  erw [e1, e2] at e
  rw [GlobalTheory.KS.rsT, dite_eq_left hOW]
  exact e

end GlobalTheory.FracPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionRelOfTranslateSectionValues
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

namespace GlobalTheory.HeatTrans

theorem chart_rel_of_sval : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (k : ℕ) (σ : SecM (GlobalTheory.HeatTrans.tr Y.H x ≫ Y.q.left) Q.P.L k) (τ : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ GlobalTheory.HeatTrans.tr Y.H x) z J) → ∀ (c : Q.P.L.ι) (U : Y.H.left.Opens), U ≤ Y.q.left ⁻¹ᵁ Q.P.L.U c → rsT (σ.f fun _ => c) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) = pbT (GlobalTheory.HeatTrans.tr Y.H x) (rsT (τ.f fun _ => c) U) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) := by
  intro R _ _ Q O _ _ _ oa Y x k σ τ hst c U hU
  have hWσ : tr Y.H x ⁻¹ᵁ U ≤ LB.wchart Q.P.L (fun _ : Fin 1 => tr Y.H x ≫ Y.q.left) (fun _ => c) := fun y hy =>
    Set.mem_iInter.2 fun _ => hU hy
  have hWτ : U ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => c) := fun y hy =>
    Set.mem_iInter.2 fun _ => hU hy
  have e1 : rsT (σ.f fun _ => c) (tr Y.H x ⁻¹ᵁ U) = resG _ hWσ (σ.f fun _ => c) := GlobalTheory.KS.rsT_of_le hWσ _
  have e2 : rsT (τ.f fun _ => c) U = resG _ hWτ (τ.f fun _ => c) := GlobalTheory.KS.rsT_of_le hWτ _
  rw [e1, e2, GlobalTheory.KS.pbT_of_le (tr Y.H x) le_rfl]
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, hJc⟩ := exists_good Q.P.L Q.P.isLB y (K := Fin 1) (fun _ => tr Y.H x ≫ Y.q.left) (fun _ => c)
    (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 (hWσ hy) 0)
  have h1 := hst Y.H.left (𝟙 _) y J hJ
  rw [sval_of σ (𝟙 _) y J (fun _ => c) (fun _ => by rw [Category.id_comp]; exact hJc 0),
    sval_of τ (𝟙 _ ≫ tr Y.H x) y J (fun _ => c) (fun _ => by rw [Category.id_comp]; exact hJc 0)] at h1
  have hTy : (tr Y.H x) ((𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y) ∈ U := hy
  refine (gs_res (𝟙 _) y hWσ hy _).trans (h1.trans ?_)
  rw [← Scheme.Hom.app_eq_appLE]
  exact ((gs_pull (𝟙 _) (tr Y.H x) y U hTy _).trans (gs_res _ y hWτ hTy _)).symm

end GlobalTheory.HeatTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreIsAbelianSchemeRelDimOfFrame
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FibreAbDim

theorem exists_isLieBasis_of_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x φ) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left))
    (hv : ∀ a, IsTanAtG t x (v a))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → R, IsCombAtG t x v cf w) :
    ∃ v' : Fin n → (epsR R ⟶ G'), IsLieBasis v' := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _)
  have h1 : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have := hσ 1
    rw [map_one] at this
    rw [this]
    congr 2
  have tan : ∀ w : epsR R ⟶ G', IsTangent w ↔ IsTanAtG t x (ρ w).left := by
    intro w
    constructor
    · intro hw
      refine ⟨Over.w (ρ w), ?_⟩
      rw [hρ, ← Category.assoc, hw, h1]
    · intro hw
      apply h.1.hom_ext
      · rw [Category.assoc, ← hρ, hw.2, h1]
      · rw [Category.assoc, Over.w w, Over.w η[G']]
        show spMap _ ≫ spMap _ = 𝟙 _
        unfold spMap
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
  let v' : Fin n → (epsR R ⟶ G') := fun a => ρ.symm (Over.homMk (v a) (hv a).1)
  have hv' : ∀ a, (v' a).left ≫ φ = v a := fun a => by
    rw [← hρ]
    simp [v']
  have comb : ∀ (c : Fin n → R) (w : epsR R ⟶ G'), IsLieComb c v' w ↔ IsCombAtG t x v c (ρ w).left := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun i => ρ (u i), fun i => ?_, ?_⟩
      · rw [hρ, hu, Category.assoc, hv']
        rfl
      · rw [map_list_prod, List.map_ofFn]
        rfl
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => ρ.symm (u i), fun i => ?_, ?_⟩
      · apply h.1.hom_ext
        · rw [← hρ, MulEquiv.apply_symm_apply, hu, Category.assoc, hv']
          rfl
        · rw [Category.assoc, Over.w, Over.w]
          show spMap _ = spMap _ ≫ spMap _
          unfold spMap
          rw [← Spec.map_comp]
          congr 1
          ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      · apply ρ.injective
        rw [map_list_prod, List.map_ofFn]
        refine (Over.OverMorphism.ext ?_)
        rw [← e]
        congr 3
        funext i
        exact (ρ.apply_symm_apply (u i)).symm
  refine ⟨v', fun a => (tan _).2 ?_, fun w hw => ?_⟩
  · rw [hρ, hv']
    exact hv a
  · simpa only [comb] using hb _ ((tan w).1 hw)

theorem isAbelianScheme_and_relDim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (j : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) j → IsAbelianScheme A ∧ SmoothOfRelativeDimension n A.hom := by
  intro E _ _ _ H X t hp U n v hv hb m hm A _ j hj
  have hG := GlobalTheory.HeckePoint.isAbelianScheme_of_proper t hp
  have pullAb : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
      [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left},
      IsAbelianScheme G → IsGrpPullback G' G f φ → IsAbelianScheme G' := by
    intro S S' f G G' _ _ φ hG h
    have := hG.comm
    have hc : IsCommMonObj G' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected⟩
  have hA := pullAb hG hj
  refine ⟨hA, ?_⟩
  have h₀ := isGrpPullback_pullback t.G (chart U)
  have hG' := pullAb hG h₀
  obtain ⟨v', hv'⟩ := exists_isLieBasis_of_frame t (chart U) h₀ v hv hb
  have w : j ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hj.1.w, Category.assoc]
  have h₁ := IsGrpPullback.cancel h₀ (hj.congr rfl (h₀.1.lift_fst _ _ w).symm) (h₀.1.lift_snd _ _ w)
  have := hG'.comm
  have := hA.comm
  have := hG.comm
  obtain ⟨v₁, hv₁, -⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ _ A _ h₁ hG'.smooth n v' hv'
  have : IsLocalRing (Γ(X, U.1) ⧸ m) := by
    letI := Ideal.Quotient.field m
    infer_instance
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim _ A hA
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  rw [GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis hj hv₁ hv₂]
  exact hg

end GlobalTheory.FibreAbDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSignatureSumEqTwiceDimension
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

namespace GlobalTheory.BalProj

theorem signature_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ),
    ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) =
      2 * (Module.finrank ℚ E / 2 * p * q) := by
  intro E _ _ _ H p q
  have hdpos : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 := H.sqrt_neg_disc_sq
  have hre : H.rt0.re = 0 := by
    have e1 := congrArg Complex.re h0
    have e2 := congrArg Complex.im h0
    have e3 : H.rt0.re * H.rt0.im = 0 := by
      simp only [pow_two, Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at e2
      linarith
    simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at e1
    rcases mul_eq_zero.mp e3 with h | h
    · exact h
    · exfalso
      rw [h] at e1
      nlinarith [sq_nonneg H.rt0.re]
  have hne : H.rt0 ≠ 0 := by
    intro h
    rw [h] at h0
    have : (H.d : ℂ) = 0 := by simpa using h0
    exact hdpos.ne' (by exact_mod_cast this)
  have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hnn : H.rt0 ≠ -H.rt0 := by
    intro h
    apply hne
    have : (2 : ℂ) * H.rt0 = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
    simpa using this
  have key : ∀ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = p * q := by
    intro τ
    have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      have hrtE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
        have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
        simpa using this
      rw [← map_pow, hrtE, h0]
      simp
    have hor : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rcases hor with h | h
    · rw [if_pos h, h, hconj, if_neg (Ne.symm hnn)]
    · rw [if_neg (by rw [h]; exact Ne.symm hnn), h, map_neg, hconj, neg_neg, if_pos rfl, mul_comm]
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card E ℂ, smul_eq_mul, NumberField.IsTotallyComplex.finrank]
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.BalProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

abbrev Bas : Type := {V : Z.affineOpens // ∃ i, V.1 ≤ W i}

abbrev incl : (Bas W)ᵒᵖ ⥤ AffOp Z :=
  (Monotone.functor (f := (Subtype.val : Bas W → Z.affineOpens)) fun _ _ h ↦ h).op

def resEquiv (hW : ⨆ i, W i = ⊤) : HO1 s ≃ₗ[R] CatCoh.H1 (incl W ⋙ OAff s) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s) (incl W)).pull1
    (GlobalTheory.CoverO.restrict_cover_affine_pull1_bijective R Z s J W hW)

def idx {W : J → Z.Opens} (V : Bas W) : J := V.2.choose

theorem le_idx {W : J → Z.Opens} (V : Bas W) : V.1.1 ≤ W (idx V) := V.2.choose_spec

theorem le_of_hom {W : J → Z.Opens} {V V' : (Bas W)ᵒᵖ} (a : V ⟶ V') : V'.unop.1.1 ≤ V.unop.1.1 :=
  leOfHom a.unop

def IsCocycle (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
    resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
      (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
      (c i i'')

def fc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : CatCoh.C1 (incl W ⋙ OAff s) :=
  fun V V' a ↦ resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
    (c (idx V.unop) (idx V'.unop))

theorem resG_resG' {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem fc_mem {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) : fc s W c ∈ Z1 (incl W ⋙ OAff s) := by
  intro V V' V'' a b
  have hV'' : V''.unop.1.1 ≤ W (idx V.unop) ⊓ W (idx V'.unop) ⊓ W (idx V''.unop) :=
    le_inf (le_inf ((le_of_hom b).trans ((le_of_hom a).trans (le_idx V.unop)))
      ((le_of_hom b).trans (le_idx V'.unop))) (le_idx V''.unop)
  have e := congrArg (resG Z hV'') (hc (idx V.unop) (idx V'.unop) (idx V''.unop))
  simp only [map_add (f := _), resG_resG'] at e
  have key : resG Z (le_inf ((le_of_hom (a ≫ b)).trans (le_idx V.unop)) (le_idx V''.unop))
      (c (idx V.unop) (idx V''.unop)) =
      resG Z (le_of_hom b) (resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop))) +
      resG Z (le_inf ((le_of_hom b).trans (le_idx V'.unop)) (le_idx V''.unop))
        (c (idx V'.unop) (idx V''.unop)) := by
    rw [resG_resG']
    exact e.symm
  exact key

def cmp (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : HO1 s := by
  classical
  exact if h : fc s W c ∈ Z1 (incl W ⋙ OAff s) then
    (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, h⟩) else 0

theorem cmp_of_isCocycle (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    cmp s W hW c = (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, fc_mem s W hc⟩) := by
  unfold cmp
  rw [dite_eq_left (fc_mem s W hc)]

theorem restrict_cmp (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    (CoefMap.restrict (OAff s) (incl W)).pull1 (cmp s W hW c) =
      H1.mk _ ⟨fc s W c, fc_mem s W hc⟩ := by
  rw [cmp_of_isCocycle s W hW hc]
  exact (resEquiv s W hW).apply_symm_apply _

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonal
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → Cohom (chartsA P) (fv f) (tanCoc P j v).neg := by
  intro H2' R _ A B _ _ g hA hB sA sB P hL φ hφ hO h' v hv c hc f hf j hj
  have hT : IsTangent v := hv.1
  obtain ⟨w, hw, hw0, hκ⟩ := _root_.GlobalTheory.PtExt.exists_chernRep_contr_of_orth H2' R A B g hA hB sA sB P hL φ hφ hO h' v hv c hc f hf
  obtain ⟨κ, hκc⟩ : ∃ κ : Fn1 A, IsContr w.1 v κ :=
    (GlobalTheory.PtExt.ContrMor.exists_contr R A B v hT).2 w.1
  obtain ⟨k1, h1⟩ := hκ κ hκc
  obtain ⟨u, hu, k2, h2⟩ := _root_.GlobalTheory.PtExt.contr_chern_eq_tanCoc R A B P hL v hT j hj w hw hw0 κ hκc
  obtain ⟨k3, h3⟩ := _root_.GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham H2' R A B g hA hB sA sB P hL v hT u hu
  refine ⟨fun D _ _ x ↦ k1 D x - k2 D x - k3 D x, fun D _ _ D' _ _ ψ x hx ↦ ?_⟩
  have e1 := h1 D D' ψ x (sm_whole x)
  have e2 := h2 D D' ψ x hx
  have e3 := h3 D D' ψ x hx
  simp only [Fn1.add, Fn1.neg, Fn1.zero, map_sub] at e1 e2 e3 ⊢
  linear_combination e1 - e2 - e3
end

