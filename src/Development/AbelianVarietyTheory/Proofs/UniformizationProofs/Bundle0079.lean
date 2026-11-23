module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfPullbackId
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LinearUnifIso

theorem exists_hom_of_pullback_id {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {f : S ⟶ S}
    (hf : f = 𝟙 S) (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ φ : G' ⟶ G, IsMonHom φ ∧ φ.left = bc.hom.left ≫ pullback.fst G.hom f := by
  have h₁ : IsGrpPullback G' G (𝟙 S) (bc.hom.left ≫ pullback.fst G.hom f) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G f)).congr ((Category.id_comp _).trans hf) rfl
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  obtain ⟨e, he, h⟩ := grpPullback_iso h₁ (isGrpPullback_of_iso (Iso.refl G))
  exact ⟨e.hom, he, (Category.comp_id _).symm.trans h⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I D' e G')

theorem mono_torus : Mono g.i := by
  refine ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩

theorem hom_ext_torus (hG : GlobalFnsSt) (f₁ f₂ : thickObj R I e G' ⟶ thickObj R I e G) [IsMonHom f₁] [IsMonHom f₂]
    (hq : f₁ ≫ g.q = f₂ ≫ g.q) (hi : g'.i ≫ f₁ = g'.i ≫ f₂) : f₁ = f₂ := by
  obtain ⟨τ, hτ⟩ := TorusCoord.exists_torus g f₁ f₂ hq
  have := mono_torus g
  have := g.i_hom
  have := g'.q_flat
  have := g'.q_surj
  have := g'.q_affine
  have hc : ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (a : Z ⟶ thickObj R I e G'),
      a ≫ f₁ = (a ≫ τ ≫ g.i) * (a ≫ f₂) := fun Z a => by
    rw [← MonObj.comp_mul, ← hτ]
  have h1 : τ = 1 := by
    refine (splitTorusPointsEquiv _ D.X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
    rw [map_one]
    refine (splitTorusPointsEquiv_val _ D.X _ τ χ.toAdd).trans ?_
    refine eq_one_of_fibre_const_of_section hG _ _ _ (TLinPf.isAb_pullback _ _ D'.P.isAb) g'.q _
      η[thickObj R I e G'] (fun Z a b hab => ?_) ?_
    · obtain ⟨σ, hσ⟩ := TorusCoord.exists_torus g' a b hab
      have e₁ : a ≫ τ = b ≫ τ := by
        rw [← cancel_mono g.i, Category.assoc, Category.assoc]
        have ha := hc Z a
        have hb := hc Z b
        have k₁ : a ≫ f₁ = (σ ≫ g'.i ≫ f₂) * (b ≫ f₁) := by
          rw [hσ, MonObj.mul_comp, Category.assoc, hi]
        have k₂ : a ≫ f₂ = (σ ≫ g'.i ≫ f₂) * (b ≫ f₂) := by
          rw [hσ, MonObj.mul_comp, Category.assoc]
        rw [k₁, k₂, hb, mul_left_comm] at ha
        rw [mul_left_comm] at ha
        rw [mul_left_comm (a ≫ τ ≫ g.i)] at ha
        exact (mul_right_cancel (mul_left_cancel ha)).symm
      rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, ← Over.comp_left,
        ← Over.comp_left, e₁]
    · have e₁ : η[thickObj R I e G'] ≫ τ = 1 := by
        rw [← cancel_mono g.i, MonObj.one_comp, Category.assoc]
        have ha := hc _ η[thickObj R I e G']
        rw [IsMonHom.one_hom f₁, IsMonHom.one_hom f₂] at ha
        exact (mul_eq_right.1 ha.symm)
      rw [← FunDescent.comp_appTop_apply, ← Over.comp_left, e₁]
      refine (splitTorusPointsEquiv_val _ D.X _ 1 χ.toAdd).symm.trans ?_
      rw [map_one]
      rfl
  rw [hτ, h1, MonObj.one_comp, _root_.one_mul]

theorem exists_torus_map (h : thickObj R I e G' ⟶ thickObj R I e G)
    (b : thickObj R I e D'.P.A ⟶ thickObj R I e D.P.A) [IsMonHom b] (hq : h ≫ g.q = g'.q ≫ b)
    {F : D'.P.A.left ⟶ D.P.A.left} (w : LB.Iso D'.P.L (D.P.L.pull F)) (xe : D'.X → D.X)
    (hψ : ∀ x κ, D'.Oφ g'.pG x κ ≫ F = h.left ≫ D.Oφ g.pG (xe x) κ)
    (H : ∀ x, PMaps w (D'.Oφ g'.pG x) (D.Oφ g.pG (xe x)) Oinvε (g'.t x) (g.t (xe x)) h.left) :
    ∃ s : splitTorus _ D'.X ⟶ splitTorus _ D.X, s ≫ g.i = g'.i ≫ h ∧
      ∀ x z, gm s.left z ⊤ (charUnit _ D.X (xe x)) = gm (𝟙 _) z ⊤ (charUnit _ D'.X x) := by
  have hd : (g'.i ≫ h) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g'.isKernel.w, Category.assoc, IsMonHom.one_hom]
  have hs := g.isKernel.lift_fst _ _ hd
  refine ⟨_, hs, fun x z => ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' D'.P.isLB z
  have v₁ := PowTorus.val_on_torus g (xe x) hJ (g.isKernel.lift _ _ hd)
  have v₂ := PowTorus.val_on_torus g' x hJ' (𝟙 _)
  rw [hs] at v₁
  rw [Category.id_comp] at v₂
  have v₃ : val (g.t (xe x)) (g'.i.left ≫ h.left) z J =
      (∏ k, gw w (g'.i.left ≫ D'.Oφ g'.pG x k) z (J ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F))
        (J' (g'.i.left ≫ D'.Oφ g'.pG x k)) ^ Oinvε k) * val (g'.t x) g'.i.left z J' :=
    (val_of _ (g'.i.left ≫ h.left) z J (fun k => J ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F)) (fun k => by
      rw [Category.assoc, Category.assoc, hψ])).trans
    (H x _ g'.i.left z _ _ (fun k => hJ ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F))
      (fun k => hJ' (g'.i.left ≫ D'.Oφ g'.pG x k)))
  rw [PowTorus.prod_on_torus g' x (fun ψ => gw w ψ z (J (ψ ≫ F)) (J' ψ)), _root_.one_mul] at v₃
  exact v₁.symm.trans (v₃.trans v₂)

theorem gm_torusEnd {S : Scheme.{0}} {X : Type} [AddCommGroup X] {u : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X u t) {Z : Scheme.{0}}
    (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X) :
    gm (r ≫ t.left) z ⊤ (charUnit S X χ) = gm r z ⊤ (charUnit S X (u χ)) := by
  rw [← ht χ]
  exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm

theorem gm_comp_of_id {X Y Z : Scheme.{0}} (s : Y ⟶ X) (a : Γ(X, ⊤)ˣ) (a' : Γ(Y, ⊤)ˣ)
    (h : ∀ y, gm s y ⊤ a = gm (𝟙 Y) y ⊤ a') (r : Z ⟶ Y) (z : Z) : gm (r ≫ s) z ⊤ a = gm r z ⊤ a' := by
  have e : pullU s ⊤ a = a' := unit_ext fun y _ =>
    (gm_pull (𝟙 Y) s y ⊤ trivial a).trans (by rw [Category.id_comp]; exact h y)
  rw [← e]
  exact (gm_pull r s z ⊤ trivial a).symm

end LinearUnifIso


open LinearUnifIso in
theorem act_comm_of_isPullUnif_id : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom bc.hom → IsPullUnif (RingHom.id R) hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' → (∀ (x : O) (y : D'.toPre.X), hD.xe (x • y) = x • hD.xe y) → (∀ x, (ιD'.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ (ιD.onB.act x).left) → ∀ x, ιG'.act x ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιG.act x) := by
  intro hG R _ _ _ I _ hI D D' A A' G G' _ _ _ _ _ sG' U U' hD bc hbc hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    lin lin' hx hB a
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨φ, hφ, eφ⟩ := exists_hom_of_pullback_id hs bc
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').1 hU
  have P : ∀ (e : ℕ) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback (thick R I e)).map c).left ≫ pullback.fst Y.hom (thick R I e) =
        pullback.fst X.hom (thick R I e) ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : ιD'.onB.act a ≫ ψ = ψ ≫ ιD.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ]; exact hB a)
  have key : ιG'.act a ≫ φ = φ ≫ ιG.act a := by
    have := sG'.smooth
    have := sG'.geomConnected
    have := U.separated
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I
      (hI ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥) G').2 G _ _ fun e => ?_
    obtain ⟨h, hf, ⟨hp, ht⟩, -⟩ := H e
    obtain rfl : h = ((Over.pullback (thick R I e)).map φ).left := by
      rw [← cancel_mono (pullback.fst G.hom (thick R I e)), P, eφ]
      exact hf
    have hq : (Over.pullback (thick R I e)).map φ ≫ (U.gt e).q =
        (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
        Category.assoc, Category.assoc, P, eψ]
      exact hp.symm.trans (Category.assoc _ _ _)
    obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
      (fun x => (ht x).2)
    obtain ⟨t, tc, ti⟩ := lin.i_lin e a
    obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
    have := ιG.hom a
    have := ιG'.hom a
    have hts : t' ≫ s = s ≫ t := by
      refine PowTorus.torus_ext _ _ fun χ z => ?_
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
        ← gm_torusEnd tc', Category.id_comp]
    have E : (Over.pullback (thick R I e)).map (ιG'.act a) ≫ (Over.pullback (thick R I e)).map φ =
        (Over.pullback (thick R I e)).map φ ≫ (Over.pullback (thick R I e)).map (ιG.act a) := by
      refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
          ← Functor.map_comp, ← Functor.map_comp, hψa]
      · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]
    rw [← Functor.map_comp, ← Functor.map_comp] at E
    exact (P e _).symm.trans ((congrArg (fun c => c.left ≫ pullback.fst G.hom (thick R I e)) E).trans (P e _))
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (ιG.act a)).left ≫
      pullback.fst G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (ιG.act a).left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, ← eφ, ← Category.assoc, ← eφ,
    ← Over.comp_left, key, Over.comp_left]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLevelPoint
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

theorem exp_alg {A X : Type} [CommRing A] {N : ℕ} {Wy Wxy Wx W1 cG cB vf vw : Aˣ} {σ : A} (s : Finset X) {f : X → A}
    {ty txy g θ : X → Aˣ} (h₁ : cB * Wxy ^ N * W1 ^ N = Wy ^ N * Wx ^ N * cG) (h₂ : vw * Wx ^ N = W1 ^ N * vf)
    (h₃ : ∀ α, txy α * θ α = g α * ty α) (h₄ : Wxy.val ^ N * σ = ∑ α ∈ s, f α * (txy α).val) :
    Wy.val ^ N * (σ * (cG * vf).val) = ∑ α ∈ s, (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val := by
  have key : cB * vw * Wxy ^ N = Wy ^ N * (cG * vf) := by
    apply mul_right_cancel (b := W1 ^ N)
    calc cB * vw * Wxy ^ N * W1 ^ N = vw * (cB * Wxy ^ N * W1 ^ N) := by ac_rfl
      _ = vw * (Wy ^ N * Wx ^ N * cG) := by rw [h₁]
      _ = Wy ^ N * cG * (vw * Wx ^ N) := by ac_rfl
      _ = Wy ^ N * cG * (W1 ^ N * vf) := by rw [h₂]
      _ = Wy ^ N * (cG * vf) * W1 ^ N := by ac_rfl
  have hα : ∀ α, (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val =
      (cB * vw).val * (f α * (txy α).val) := by
    intro α
    have ht : txy α = g α * ty α * (θ α)⁻¹ := eq_mul_inv_of_mul_eq (h₃ α)
    have hu : cB * vw * g α * (θ α)⁻¹ * ty α = cB * vw * txy α := by rw [ht]; ac_rfl
    calc (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val
        = f α * (cB * vw * g α * (θ α)⁻¹ * ty α).val := by rw [Units.val_mul _ (ty α), _root_.mul_assoc]
      _ = f α * (cB * vw * txy α).val := by rw [hu]
      _ = (cB * vw).val * (f α * (txy α).val) := by rw [Units.val_mul _ (txy α)]; ring
  rw [Finset.sum_congr rfl (fun α _ => hα α), ← Finset.mul_sum, ← h₄]
  have hv := congrArg Units.val key
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hv
  simp only [Units.val_mul]
  linear_combination (-σ) * hv

section Level
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))}
open ReciprocityTheory.ChartRestriction.G.DVR

def wv (e : ℕ) {Z : Scheme.{0}} (z : Z) (JG : (Z ⟶ G.left) → U.P.L.L.ι) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (a : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw (U.w e) a z (J (a ≫ (U.gt e).pG.left)) (fun _ => JG (a ≫ (fstG I e G).left))

def upHom (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (Z ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj Z ⟶ G) :=
  MonoidHom.mk' (fun a => (Over.map (thick R I e)).map a ≫ fstG I e G) FormalPoint.map_mul_fstG

def imHom (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (Z ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj Z ⟶ D.P.A) :=
  MonoidHom.mk' (TorusCoord.im (U.gt e)) (TorusCoord.im_mul (U.gt e))

def FrameRel (x : T ⟶ G) (b : T ⟶ D.P.A) (N : ℕ)
    (f : LB.Gen (LB.LinComb U.P.L.L (K := Fin 2) ![(1 : T ⟶ G).left, x.left] ![(N : ℤ), -(N : ℤ)]))
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, b.left] ![(N : ℤ), -(N : ℤ)])) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (o a : Z ⟶ (thickObj R I e G).left),
    o ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left → a ≫ (fstG I e G).left = r ≫ x.left →
    ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J →
      val w r z J * wv U e z JG J a ^ N = wv U e z JG J o ^ N * val f r z JG

variable {U}

theorem exists_level_point {x : T ⟶ G} {g : GtPt D T} (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1) {e : ℕ}
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : (Over.map (thick R I e)).obj Z ⟶ T) :
    ∃ a : Z ⟶ thickObj R I e G, upHom I e G Z a = τ ≫ x ∧ imHom U e Z a = τ ≫ g.b ∧ a ^ N = 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.FormalPoint.exists_lift_fstG (τ ≫ x)
  have hup : upHom I e G Z a = τ ≫ x := ha
  have hleft : a.left ≫ (fstG I e G).left = τ.left ≫ x.left := by
    have := congrArg CommaMorphism.left ha
    simpa using this
  refine ⟨a, hup, ?_, ?_⟩
  · show (Over.map (thick R I e)).map a ≫ (U.gt e).pG = τ ≫ g.b
    ext1
    simpa using (hr e _ τ.left a.left hleft).1
  · apply GlobalTheory.FormalPoint.eq_of_map_fstG
    change upHom I e G Z (a ^ N) = upHom I e G Z 1
    rw [map_pow, map_one, hup, ← CategoryTheory.MonObj.comp_pow, hx, CategoryTheory.MonObj.comp_one]

theorem exists_over_point {e : ℕ} {Z : Scheme.{0}} (y₀ : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (T ⊗ G).left)
    (rB : Z ⟶ (T ⊗ D.P.A).left) (e₁ : rG ≫ (snd T G).left = y₀ ≫ (fstG I e G).left)
    (e₂ : rB ≫ (snd T D.P.A).left = y₀ ≫ (U.gt e).pG.left) (e₃ : rB ≫ (fst T D.P.A).left = rG ≫ (fst T G).left) :
    ∃ τ : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T,
      rG = (lift τ (upHom I e G _ (Over.homMk y₀ rfl))).left ∧ rB = (lift τ (imHom U e _ (Over.homMk y₀ rfl))).left := by
  have h1 : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := by
    rw [Over.w (fst T G), Over.w (snd T G)]
  have h2 : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
  have hw : (rG ≫ (fst T G).left) ≫ T.hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    simp only [Category.assoc]
    rw [h1, reassoc_of% e₁, h2]
  have hG : rG ≫ (T ⊗ G).hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w (fst T G), ← Category.assoc]; exact hw
  have hB : rB ≫ (T ⊗ D.P.A).hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w (fst T D.P.A), ← Category.assoc, e₃]; exact hw
  refine ⟨Over.homMk (rG ≫ (fst T G).left) hw, ?_, ?_⟩
  · have key : (Over.homMk rG hG : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T ⊗ G) =
        lift (Over.homMk (rG ≫ (fst T G).left) hw) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]; ext1; simp
      · rw [lift_snd]
        show Over.homMk rG hG ≫ snd T G = (Over.map (thick R I e)).map (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) ≫ fstG I e G
        ext1; simpa using e₁
    exact congrArg CommaMorphism.left key
  · have key : (Over.homMk rB hB : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T ⊗ D.P.A) =
        lift (Over.homMk (rG ≫ (fst T G).left) hw) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]; ext1; simpa using e₃
      · rw [lift_snd]
        show Over.homMk rB hB ≫ snd T D.P.A = (Over.map (thick R I e)).map (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) ≫ (U.gt e).pG
        ext1; simpa using e₂
    exact congrArg CommaMorphism.left key

theorem expT_transl (hG : GlobalFnsSt) {x : T ⟶ G} {g : GtPt D T} (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1)
    {f₀ w} (hf : FrameRel U x g.b N f₀ w) {σ : U.SecGT (𝟙_ _) N} {σ' : U.SecGT T N}
    {f : ∀ α, SecBT D (𝟙_ _) N α} {f' : ∀ α, SecBT D T N α}
    (hσ : ∀ (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good U.P.L.L z J →
      sval σ' (lift τ y).left z J = sval σ (lift (toUnit T') ((τ ≫ x) * y)).left z J *
        (cubN (cubV U.P.c z J) N 1 (τ ≫ x) y * val f₀ τ.left z J).val)
    (hf' : ∀ α (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval (f' α) (lift τ y).left z J =
        sval (f α) (lift (toUnit T') ((τ ≫ g.b) * y)).left z J * (fac g N w α τ y z J).val)
    (h : U.ExpT (𝟙_ _) N σ f) : U.ExpT T N σ' f' := by
  intro e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, ?_⟩
  intro Z y₀ rG rB e₁ e₂ e₃ z JG J hJG hJ
  obtain ⟨τ, hτG, hτB⟩ := exists_over_point (U := U) y₀ rG rB e₁ e₂ e₃
  subst hτG hτB
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_level_point hr hx τ
  have hal : a.left ≫ (fstG I e G).left = τ.left ≫ x.left := congrArg CommaMorphism.left ha₁
  have hu : (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ fstG I e G =
      (τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) := by
    rw [show (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ fstG I e G =
      upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) from rfl, map_mul, ha₁]
  have hi : (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ (U.gt e).pG =
      (τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) := by
    rw [show (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ (U.gt e).pG =
      imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) from rfl, map_mul, ha₂]
  have c₁ := (congrArg CommaMorphism.left (lift_snd (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left hu).symm
  have c₂ := (congrArg CommaMorphism.left (lift_snd (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left hi).symm
  have c₃ := (congrArg CommaMorphism.left (lift_fst (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left (lift_fst (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).symm
  obtain ⟨hz, hsum⟩ := hs Z (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)).left
    (lift (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))).left
    (lift (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))).left c₁ c₂ c₃ z JG J hJG hJ
  refine ⟨fun α hα => ?_, ?_⟩
  · rw [hf' α _ τ _ z J hJ, hz α hα, zero_mul]
  have hcube : ∀ p q u : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G,
      @id (Z.presheaf.stalk z)ˣ (cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) D.cub z J (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) p) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) q)
        (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) u)) *
          wv U e z JG J (p * q).left * wv U e z JG J (p * u).left * wv U e z JG J (q * u).left *
          wv U e z JG J (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left =
        wv U e z JG J (p * q * u).left * wv U e z JG J p.left * wv U e z JG J q.left * wv U e z JG J u.left *
          @id (Z.presheaf.stalk z)ˣ (cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) U.P.c z JG (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) p) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) q)
            (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) u)) :=
    fun p q u => (U.w_vals e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) z JG J hJG hJ (fun q => wv U e z JG J q.left) (fun _ => rfl)).2.2 p q u
  have H1 := cubN_twist (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom))) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom))) (fun q => wv U e z JG J q.left)
    (θ := cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) D.cub z J) (θ' := cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) U.P.c z JG) hcube ha₃ (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)
  rw [ha₁, ha₂] at H1
  have h1o : (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left ≫ (fstG I e G).left = τ.left ≫ (1 : T ⟶ G).left := by
    have h1 : upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) 1 = τ ≫ (1 : T ⟶ G) := by rw [map_one, MonObj.comp_one]
    exact congrArg CommaMorphism.left h1
  have H2 := hf e Z τ.left (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left a.left h1o hal z JG J hJG hJ
  have ha₂' : (Over.map (thick R I e)).map a ≫ (U.gt e).pG = τ ≫ g.b := ha₂
  have H3 : ∀ α, @id (Z.presheaf.stalk z)ˣ (val ((U.gt e).t α) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)).left z J) *
      @id (Z.presheaf.stalk z)ˣ (th D z J (cP D ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom))) α) (τ ≫ g.b) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))) =
      @id (Z.presheaf.stalk z)ˣ (val (g.s α) τ.left z J) * @id (Z.presheaf.stalk z)ˣ (val ((U.gt e).t α) y₀ z J) := by
    intro α
    have ht := torus_coord_add hG R I D e G (U.gt e) (Over.mk (y₀ ≫ (thickObj R I e G).hom)) a (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) α z J hJ
    rw [ha₂'] at ht
    rw [← (hr e _ τ.left a.left hal).2 α z J hJ]
    exact ht
  rw [hσ _ τ _ z JG hJG]
  simp only [hf' _ _ τ _ z J hJ]
  exact exp_alg s H1 H2 H3 hsum

end Level

end GlobalTheory.UU.Transl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory

namespace PsiScalIn

open PsiInPull PsiInPow

variable {R : Type} [CommRing R] [IsDomain R]

def sig (z : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem gs_scal_id (z : Spec (CommRingCat.of (FractionRing R))) (c : FractionRing R) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing R)))) c) = sig z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_toOpen (z : Spec (CommRingCat.of (FractionRing R))) (V : (Spec (CommRingCat.of R)).Opens)
    (hz : jK R z ∈ V) (r : R) : gs (jK R) z V (DegPre.toOpen V r) = sig z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  refine (gs_res (jK R) z (le_top : V ≤ ⊤) hz _).trans ((gs_eq (jK R) z ⊤ trivial _).trans ?_)
  simp only [sig, RingHom.comp_apply]
  rw [nat]
  rfl

theorem key (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (q : D.P.L.ι)
    (V : (Spec (CommRingCat.of R)).Opens) (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q)
    (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ u : Γ(Spec (CommRingCat.of R), V)ˣ,
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val =
        sig z (a χ).val * gs (jK R) z V u.val := by
  have hle' : V ≤ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => q) := fun y hy =>
    mem_wchart _ _ _ _ (hle hy)
  obtain ⟨J, hJ, e⟩ := exists_good D.P.L D.P.isLB (Z := (TK R).left) z (K := PUnit) (fun _ => D.xK χ) (fun _ => q)
    (fun _ _ _ => rfl) (fun _ => hle hz)
  have e0 : J (D.xK χ) = q := e PUnit.unit
  have v := (h χ).2 (TK R) (𝟙 _) z J hJ
  have v1 := val_of (D.psi χ) (𝟙 _) z J (fun _ => q) (fun _ => (congrArg J (Category.id_comp _)).trans e0)
  have v2 := val_of (ga χ) (toUnit (TK R)).left z J (fun _ => q) (fun _ => e0)
  refine ⟨res hle' ((ga χ).s (fun _ => q)), (congrArg Units.val v1).symm.trans (v.trans ?_)⟩
  refine congrArg₂ (· * ·) (gs_scal_id z _) ?_
  refine (congrArg Units.val v2).trans ?_
  exact ((gs_unit _ _ _ hz _).trans (congrArg Units.val (gm_res _ _ hle' hz _))).symm

theorem main_local [IsLocalRing R] (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (J : Ideal R) :
    D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap R (FractionRing R) r = (a χ).val := by
  constructor
  · intro H
    obtain ⟨q, hq⟩ := exists_chart D.P.isLB ((D.c χ).left (IsLocalRing.closedPoint R))
    have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q := fun y _ =>
      (IsLocalRing.specializes_closedPoint y).mem_open ((D.c χ).left ⁻¹ᵁ D.P.L.U q).isOpen hq
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
    obtain ⟨r, hr, e⟩ := gs_of_psiIn D χ J H q ⊤ (isAffineOpen_top _) hle z trivial
    obtain ⟨u, hu⟩ := key D ga a h χ q ⊤ hle z trivial
    have hs : Function.Surjective (DegPre.toOpen (R := R) ⊤) := by
      intro b
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b, ?_⟩
      simp [DegPre.toOpen]
    obtain ⟨s, hsJ, es⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 (Ideal.mul_mem_right (u⁻¹).val _ hr)
    refine ⟨s, hsJ, (sig z).injective ?_⟩
    have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    rw [← gs_toOpen z ⊤ hz, es, gs_mul _ _ _ hz, e.trans hu, _root_.mul_assoc,
      ← gs_mul _ _ _ hz, Units.mul_inv, gs_eq _ _ _ hz, map_one, map_one, _root_.mul_one]
  · rintro ⟨r, hr, e⟩
    refine psiIn_of_gs D χ J fun q V _ hle z hz => ?_
    obtain ⟨u, hu⟩ := key D ga a h χ q V hle z hz
    refine ⟨DegPre.toOpen V r * u.val, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr), ?_⟩
    rw [gs_mul _ _ _ hz, gs_toOpen z V hz, e]
    exact hu.symm

end PsiScalIn

theorem psiIn_iff_scalar_mem : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → ∀ (χ : D.X) (J : Ideal V), J ≠ ⊥ → (D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap V (FractionRing V) r = (a χ).val) :=
  fun _ _ _ _ D ga a h χ J _ => PsiScalIn.main_local D ga a h χ J

end GlobalTheory
end
end

