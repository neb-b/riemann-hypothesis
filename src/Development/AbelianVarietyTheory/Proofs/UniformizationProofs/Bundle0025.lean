module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
section
noncomputable section

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CubTransport

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Down

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_down_units {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun Z r z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans
        (congrArg (·⁻¹) (hu p q _ _ z hz))) (gm_res _ z _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)
      (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ z inf_le_right hz s).symm.trans ((congrArg (gm _ z _) (hs p)).trans (hv Z r z p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q h₁ h₂ => ?_⟩
  · choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
    refine (hs j _ (𝟙 Y) y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y p m hj')).symm)
    rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv,
      _root_.mul_assoc]
  · exact (mul_inv_cancel_left _ _).symm.trans (congrArg (pw w φ' ε r z p q * ·) (hs q Z r z p h₁ h₂).symm)

theorem exists_pmaps {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  have key : ∀ (ψ : K → (Y' ⟶ X)) (_ : ∀ k, φ' k ≫ F = ψ k) (t₀ : LB.Gen (LB.LinComb L ψ ε)), t₀.IsGen →
      ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L ψ p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L ψ p) (t₀.s p) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro ψ hψ t₀ h₀
    obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
    exact exists_down_units hw hL hL' t₀ h₀
  obtain ⟨a, ha, hv⟩ := key _ hc (LB.pullGen L φ ε t h) (pullGen_isGen _ _ _ _ ht h)
  refine ⟨a, ha, fun Z r z p q hp hq => ?_⟩
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show φ k (h (r z)) ∈ L.U (p k)
    rw [pt_eq hc]; exact hp k
  refine Eq.trans ?_ (hv Z r z p q hm (Set.mem_iInter.2 hq))
  exact ((gm_res r z _ hm _).trans (gm_pull r h z (LB.wchart L φ p)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)).symm

theorem val_pmaps {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

end Down

theorem isCub_of_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] {θ : A → A → A → U}
    (hθ : IsCub θ) (β : A' →* A) (Ω : A' → U) {θ' : A' → A' → A' → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
      Ω c * (Ω 1)⁻¹ * θ' a b c) : IsCub θ' := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · have e := h 1 x y
    rw [map_one, hθ.face] at e
    simp only [_root_.one_mul] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hθ.s01 (β x) (β y) (β z)
    rw [h, h, mul_comm y x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.s12 (β x) (β y) (β z)
    rw [h, h, mul_comm z y, mul_right_comm x z y] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.coc (β x) (β x') (β x'') (β y)
    rw [← map_mul, ← map_mul, h, h, h, h] at e
    simp only [← _root_.mul_assoc x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'

section Cub

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

def thV (t : LB.Gen (Theta G L.L)) {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) (x x' y : T ⟶ G) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (lift x (lift x' y)).left z J

theorem val_thV (t : LB.Gen (Theta G L.L)) {T : Over S} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι}
    (hJ : Good L.L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift x (lift x' y)).left) (𝟙 T.left) z J = thV t z J x x' y := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [Category.id_comp]; rfl

theorem val_id_thV (t : LB.Gen (Theta G L.L)) {z : (G3 G).left} {J : ((G3 G).left ⟶ G.left) → L.L.ι} :
    val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (𝟙 (G3 G).left) z J = thV t z J (x3 G 0) (x3 G 1) (x3 G 2) := by
  have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
    ext <;> simp [x3]
  rw [thV, e]; rfl

def cubicalOfVal (t : LB.Gen (Theta G L.L)) (ht : t.IsGen)
    (h : ∀ (T : Over S) (z : T.left) (J), Good L.L z J → IsCub (thV t z J)) : CubicalStr G L where
  t := t
  isGen := ht
  face i := corr_of_val L.isLB fun y J hJ => by
    refine Eq.trans ?_ (val_one _).symm
    have C := h (G2 G) y J hJ
    fin_cases i
    · exact (val_thV t hJ _ _ _).trans (C.face _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₂ _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₃ _ _)
  cubeSymmetric_swap_first := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s01 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cubeSymmetric_swap_last := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s12 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cocycle := corr_of_val L.isLB fun y J hJ =>
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).trans
      (((h (G4 G) y J hJ).coc _ _ _ _).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).symm)

end Cub

end CubTransport


open CubTransport ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem cubical_symmetry_transport : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (hgp : Geo.Tor.IsGrpPullback G' G f Ψ) (L : RigLB G) (L' : RigLB G') (wL : LB.Iso L'.L (L.L.pull Ψ)) (he : eSec G' ≫ Ψ = f ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) → ∀ (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) → ∃ (c' : CubicalStr G' L') (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen ∧ LB.Gen.Corr L'.L _ _ _ _ (LB.pullGen L'.L _ _ s' (eSec G')) (LB.oneGen L'.L) ∧ Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (Geo.Tor.cubeMapOf hgp).F3 ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' s Ψ := by
  intro S S' f G _ _ G' _ _ Ψ hgp L L' wL he hw _ c s hs hs1
  have hw' := (isGen_iff wL).1 hw
  have good : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good L.L z J := fun {Z} z => by
    choose I hI using fun χ : Z ⟶ G.left => exists_chart L.isLB (χ z)
    exact ⟨I, hI⟩
  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ Ψ = (cubeMapOf hgp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf hgp).psum_comm I.down
  obtain ⟨t', ht', Ht⟩ := exists_pmaps hw' L.isLB L'.isLB (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (cubeMapOf hgp).F3 hc c.t c.isGen
  have hι : (ι[G']).left ≫ Ψ = Ψ ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom hgp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ Ψ) ≫ _ = _
    rw [Category.id_comp]
  have hc₂ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ Ψ = Ψ ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', Hs⟩ := exists_pmaps hw' L.isLB L'.isLB Ψ hc₂ s hs
  refine ⟨cubicalOfVal t' ht' fun T z J' hJ' => ?_, s', hs', corr_of_val L'.isLB fun y J' hJ' => ?_, Ht, Hs⟩
  · obtain ⟨J, hJ⟩ := good z
    refine isCub_of_twist (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ) (pushHom hgp T)
      (fun x => gw wL x.left z (J (x.left ≫ Ψ)) (J' x.left)) fun a b d => ?_
    have q : (lift a (lift b d)).left ≫ (cubeMapOf hgp).F3 =
        (lift (pushHom hgp T a) (lift (pushHom hgp T b) (pushHom hgp T d))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    have e := val_pmaps hc Ht (lift a (lift b d)).left hJ hJ'
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw wL q z (J (q ≫ Ψ)) (J' q))) rfl)
  · obtain ⟨J, hJ⟩ := good y
    have e := val_pmaps hc₂ Hs (eSec G') hJ hJ'
    have e₁ : val s (eSec G' ≫ Ψ) y J = 1 := by
      rw [he]
      exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hs1 f).trans (val_one _))
    have e₂ : eSec G' ≫ (ι[G']).left = eSec G' := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    rw [e₁, Fin.prod_univ_two] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₂, Category.comp_id, zpow_one, zpow_neg,
      mul_inv_cancel, _root_.one_mul] at e
    refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact e.symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk :
    ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
      [Algebra (FractionRing R) F], IsIntegral (DegPre.BF D F).left ∧
        ∀ y : (DegPre.BF D F).left, IsIntegrallyClosed ((DegPre.BF D F).left.presheaf.stalk y) := by
  intro R _ _ D F _ _
  have h₁ := D.P.isAb.smooth
  have h₂ := D.P.isAb.geomConnected
  let j : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) := DegPre.jFR (R := R) F
  let g : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := pullback.fst j D.P.A.hom
  have hs : Smooth g := inferInstanceAs (Smooth (pullback.fst j D.P.A.hom))
  have hc : ConnectedSpace (DegPre.BF D F).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.P.A.hom) j
      (pullback.snd j D.P.A.hom) (pullback.fst j D.P.A.hom) (IsPullback.of_hasPullback j D.P.A.hom).flip
  exact ⟨isIntegral_of_smooth_field_of_connectedSpace g, fun y ↦
    ((isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ g hs).2.1 y).2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UniformiserEval

open GlobalTheory.ChartRing

variable {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]

omit [IsAdicComplete (IsLocalRing.maximalIdeal V) V] in
theorem C_add_X_mem {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (PowerSeries.C a + PowerSeries.X : PowerSeries V) ∈ IsLocalRing.maximalIdeal (PowerSeries V) :=
  add_mem (C_mem_maximalIdeal_iff.2 ha) X_mem_maximalIdeal

def translate {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) : PowerSeries V →ₐ[V] PowerSeries V :=
  evalAdic V (IsLocalRing.maximalIdeal (PowerSeries V)) (C_add_X_mem ha)

theorem translate_X {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    translate ha PowerSeries.X = PowerSeries.C a + PowerSeries.X := evalAdic_X _ _

theorem translate_C {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) (x : V) :
    translate ha (PowerSeries.C x) = PowerSeries.C x := (translate ha).commutes x

theorem translate_neg_comp {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (translate (neg_mem ha)).comp (translate ha) = AlgHom.id V _ := by
  have h : (translate (neg_mem ha)).comp (translate ha) PowerSeries.X = PowerSeries.X := by
    rw [AlgHom.comp_apply, translate_X, map_add (f := _), translate_C, translate_X, map_neg]
    ring
  refine algHom_ext_of_isHausdorff (IsLocalRing.maximalIdeal (PowerSeries V)) ?_ h
  rw [h]
  exact X_mem_maximalIdeal

theorem translate_injective {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    Function.Injective (translate ha) :=
  Function.LeftInverse.injective (g := translate (neg_mem ha)) fun f =>
    DFunLike.congr_fun (translate_neg_comp ha) f

theorem dvr_admissibleBase_and_powerSeries_evalUniformiser : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → AdmBase V (Ideal.span {ϖ}) ∧ AdmBase (PowerSeries V) (Ideal.span {PowerSeries.X}) ∧ ∃ ev : PowerSeries V →+* V, (∀ x, ev (PowerSeries.C x) = x) ∧ ev PowerSeries.X = ϖ ∧ ∀ (F : Type) [Field F] (i : V →+* F), Function.Injective i → ∃ σ : PowerSeries V →+* PowerSeries F, Function.Injective σ ∧ (∀ x, σ (PowerSeries.C x) = PowerSeries.C (i x)) ∧ σ PowerSeries.X = PowerSeries.C (i ϖ) + PowerSeries.X ∧ ∀ f, PowerSeries.constantCoeff (σ f) = i (ev f) := by
  intro V _ _ _ ϖ hϖ hc
  have hm : ϖ ∈ IsLocalRing.maximalIdeal V := hϖ.not_isUnit
  refine ⟨⟨inferInstance, inferInstance, inferInstance, hϖ.maximalIdeal_eq ▸ hc⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    (PowerSeries.constantCoeff (R := V)).comp (translate hm : PowerSeries V →+* PowerSeries V),
    fun x => ?_, ?_, fun F _ i hi =>
      ⟨(PowerSeries.map i).comp (translate hm : PowerSeries V →+* PowerSeries V), ?_,
        fun x => ?_, ?_, fun f => ?_⟩⟩
  · simp [translate_C]
  · simp [translate_X]
  · exact (PowerSeries.map_injective i hi).comp (translate_injective hm)
  · simp [translate_C]
  · simp [translate_X]
  · simp only [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]

end GlobalTheory.UniformiserEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsGenTransl
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_of_isGen_transl : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b b' : TF (R := R) F ⟶ D.P.A) (r : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] ![1, -1])), r.IsGen → b = b' := by
  intro R _ _ D F _ _ b b' r hr
  have key : b * b'⁻¹ = 1 := by
    refine D.P.ktriv F (TF (R := R) F).hom (b * b'⁻¹) fun p => ⟨⊤, trivial, ?_⟩
    have h3 : (fun i => (DegPre.trPt D F b'⁻¹).left ≫ ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] i) =
        ![(lift (fst (TF (R := R) F) D.P.A ≫ (b * b'⁻¹)) (snd (TF (R := R) F) D.P.A) ≫ μ[D.P.A]).left, (snd (TF (R := R) F) D.P.A).left] := by
      have g : ∀ m : TF (R := R) F ⟶ D.P.A, DegPre.trPt D F b'⁻¹ ≫ DegPre.trPt D F m ≫ DegPre.prB D F =
          (fst (TF (R := R) F) D.P.A ≫ (m * b'⁻¹)) * DegPre.prB D F := fun m => by
        rw [DVR.tr_pr, MonObj.comp_mul, DVR.tr_pr, ← Category.assoc, DVR.tr_fst, MonObj.comp_mul]
        exact (_root_.mul_comm _ _).trans ((congrArg _ (_root_.mul_comm _ _)).trans (_root_.mul_assoc _ _ _).symm)
      funext i
      fin_cases i
      · exact congrArg (fun q => q.left) (g b)
      · refine congrArg (fun q => q.left) ((g b').trans ?_)
        rw [mul_inv_cancel, MonObj.comp_one, _root_.one_mul]
    have h4 : ∃ w : LB.Gen (LB.LinComb D.P.L (fun i => (DegPre.trPt D F b'⁻¹).left ≫ ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] i) ![1, -1]), w.IsGen :=
      ⟨_, DVR.pullGen_isGen _ _ _ r hr _⟩
    rw [h3] at h4
    obtain ⟨w, hw⟩ := h4
    exact exists_isGen_pull (translDiff D.P.A D.P.L (b * b'⁻¹)) w hw _
  exact mul_inv_eq_one.1 key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfFibreConstOfSection
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_one_of_fibre_const_of_section :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (B W : Over S) [GrpObj B], IsAbelianScheme B → ∀ (π : W ⟶ B) [Flat π.left] [Surjective π.left] [QuasiCompact π.left] (ρ : Γ(W.left, ⊤)) (σ : 𝟙_ (Over S) ⟶ W), (∀ (Z : Over S) (g₁ g₂ : Z ⟶ W), g₁ ≫ π = g₂ ≫ π → g₁.left.appTop.hom ρ = g₂.left.appTop.hom ρ) → σ.left.appTop.hom ρ = 1 → ρ = 1 := by
  intro hG S B W _ hB π _ _ _ ρ σ h hσ
  obtain ⟨a, rfl⟩ := FunDescent.exists_appTop_eq π.left ρ (by
    intro Z g₁ g₂ e
    let Z' : Over S := Over.mk (g₂ ≫ W.hom)
    let k₂ : Z' ⟶ W := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ W := Over.homMk g₁ (by
      change g₁ ≫ W.hom = g₂ ≫ W.hom
      rw [← Over.w π, reassoc_of% e])
    exact h Z' k₁ k₂ (Over.OverMorphism.ext e))
  obtain ⟨s, rfl⟩ := (hG S B hB).2 a
  rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, Category.assoc, Over.w π,
    Over.w σ] at hσ
  have hs : s = 1 := by
    have e : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [e] at hσ
    simpa using hσ
  rw [hs, map_one, map_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtTorsionPoints

section Values

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_val_pull (hL : L.IsLB) (ρ : Z ⟶ Y) (hinj : ∀ U, Function.Injective (ρ.app U).hom)
    (hρ : ∀ a b : Y ⟶ X, ρ ≫ a = ρ ≫ b → a = b)
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (hinj _ (fn_ext fun z hz => ?_))
  have hz' : ρ z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => ρ ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    rintro (a | a) (b | b) e <;> replace e := hρ _ _ e
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz'.1 a, Set.mem_iInter.1 hz'.2 a])
  have := h z J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  rw [gs_pull (𝟙 Z) ρ z _ hz', gs_pull (𝟙 Z) ρ z _ hz', Category.id_comp, gs_unit ρ z _ hz', gs_unit ρ z _ hz']
  exact congrArg Units.val ((gm_res ρ z _ hz' _).trans (this.trans (gm_res ρ z _ hz' _).symm))

end Values

section Valuation

variable {S F : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Algebra S F] [IsFractionRing S F]

end Valuation

section Main

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (ρ : TF (R := R) F ⟶ T)

variable {z : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}

end Main

end GlobalTheory.GtTorsionPoints
end
end

