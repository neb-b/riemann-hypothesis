module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegreesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ ψ : (TFK (R := R) F ⊗ A.A) ≅ (TFK (R := R) F ⊗ A.A), ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q ψ.hom := by
  first | exact @GlobalTheory.InducingAut.exists_aut | exact GlobalTheory.InducingAut.exists_aut | (intros; apply GlobalTheory.InducingAut.exists_aut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.EndData

theorem val_eq_of_flat {X Y Y' Y₁ Y₂ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₂ ⟶ X)} {ε : K → ℤ} (t₁ : LB.Gen (LB.LinComb L φ₁ ε))
    (t₂ : LB.Gen (LB.LinComb L φ₂ ε)) (m₁ : Y ⟶ Y₁) (m₂ : Y ⟶ Y₂) (hm : ∀ k, m₁ ≫ φ₁ k = m₂ ≫ φ₂ k)
    (π : Y' ⟶ Y) [Flat π] [Surjective π]
    (h : ∀ x J, Good L x J → val t₁ (π ≫ m₁) x J = val t₂ (π ≫ m₂) x J) (y : Y) (J) (hJ : Good L y J) :
    val t₁ m₁ y J = val t₂ m₂ y J := by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  let j : K → L.ι := fun k => J (m₁ ≫ φ₁ k)
  have h₁ : m₁ y ∈ LB.wchart L φ₁ j := hJ.mem φ₁ m₁
  have e₂ : ∀ k, J (m₂ ≫ φ₂ k) = j k := fun k => congrArg J (hm k).symm
  have h₂ : m₂ y ∈ LB.wchart L φ₂ j := (funext e₂ : _ = j) ▸ hJ.mem φ₂ m₂
  have key := UnifCompare.gm_eq_of_flat_surjective π (pullU m₁ (LB.wchart L φ₁ j) (t₁.s j))
    (pullU m₂ (LB.wchart L φ₂ j) (t₂.s j)) (fun x hx₁ hx₂ => by
      obtain ⟨J', hJ', e⟩ := exists_good L hL x (fun k => (π ≫ m₁) ≫ φ₁ k) j
        (fun a b e => congrArg J (by simpa only [Category.assoc, cancel_epi] using e))
        (fun k => Set.mem_iInter.1 hx₁ k)
      have := h x J' hJ'
      rw [val_of t₁ _ x J' j e, val_of t₂ _ x J' j (fun k => by
        rw [Category.assoc, ← hm, ← Category.assoc]; exact e k)] at this
      exact (gm_pull π m₁ x _ hx₁ _).trans (this.trans (gm_pull π m₂ x _ hx₂ _).symm)) (𝟙 Y) y h₁ h₂
  have k₁ := gm_pull (𝟙 Y) m₁ y _ h₁ (t₁.s j)
  have k₂ := gm_pull (𝟙 Y) m₂ y _ h₂ (t₂.s j)
  rw [Category.id_comp] at k₁ k₂
  rw [val_of t₂ m₂ y J j e₂]
  exact k₁.symm.trans (key.trans k₂)

theorem val_eq_one {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R] {X : Scheme.{0}} {L : LB X}
    (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ}
    (hf : FormEq (K' := PEmpty) φ ε PEmpty.elim PEmpty.elim) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen)
    (h : ∀ e z J, Good L z J → val c (thick R I e) z J = 1) (y) (J) (hJ : Good L y J) :
    val c (𝟙 _) y J = 1 := by
  obtain ⟨c', -, hv⟩ := exists_gen hL hf c hc
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart L (K := PEmpty) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J), Good L z J →
      val c r z J = gm r z ⊤ (res le (c'.s PEmpty.elim)) := fun Z r z J hJ =>
    (hv Z r z J hJ).symm.trans ((val_of c' r z J PEmpty.elim (fun k => k.elim)).trans
      (gm_res r z le trivial _).symm)
  have one : res le (c'.s PEmpty.elim) = 1 := by
    refine Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
      (SecAlg.eq_of_forall_mk I fun e => ?_))
    have key : ((thick R I e).app ⊤).hom (res le (c'.s PEmpty.elim)).val = ((thick R I e).app ⊤).hom 1 := by
      refine fn_ext fun z hz => ?_
      choose J hJ using fun ψ : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X => exists_chart hL (ψ z)
      rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp, gs_unit _ z ⊤ trivial,
        ← ev _ _ z J hJ, h e z J hJ, gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_one]
    have nat := fun x => congrArg (fun φ => φ.hom x)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
    exact (nat _).symm.trans ((congrArg _ key).trans (nat 1))
  rw [ev _ _ y J hJ, one, map_one]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem prod_unit (D : DegPre R) (p : D.P.A ⟶ D.P.A) [IsMonHom p] (χ : D.X) {U : Type} [CommGroup U]
    (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U) :
    ∏ k, h (eSec D.P.A ≫ D.Oφ p χ k) ^ Oε k = 1 ∧ ∏ k, h (eSec D.P.A ≫ D.Oφ p χ k) ^ Oinvε k = 1 := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  have o : η[D.P.A] ≫ p = (1 : T ⟶ D.P.A) := by simp [Hom.one_def, T]
  have e0 : ∀ k, eSec D.P.A ≫ D.Oφ p χ k = D.Oφ (1 : T ⟶ D.P.A) χ k :=
    fun k => (WeightPf.Oφ_comp η[D.P.A] p χ k).trans (congrArg (D.Oφ · χ k) o)
  simp only [e0]
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  constructor
  · show h ((1 : T ⟶ D.P.A) * (toUnit T ≫ D.c χ)).left ^ (1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
      h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  · show h ((1 : T ⟶ D.P.A) * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
      h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp

omit [IsDomain R] in
theorem map_fst (e : ℕ) {G G' : Over (Spec (CommRingCat.of R))} (a : G ⟶ G') :
    ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst G'.hom (thick R I e) =
      pullback.fst G.hom (thick R I e) ≫ a.left := pullback.lift_fst _ _ _

omit [IsDomain R] in
theorem trans_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)


omit [IsDomain R] in
theorem trans_map (e : ℕ) {G G' : Over (Spec (CommRingCat.of R))} (a : G ⟶ G') :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map a).left =
      ((Over.pullback (thick R I e)).map a).left ≫ thickMap R I e G' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, map_fst, trans_fst, map_fst, ← Category.assoc, trans_fst]
  · have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    have l : ∀ n, ((Over.pullback (thick R I n)).map a).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
      fun n => pullback.lift_snd _ _ _
    rw [Category.assoc, Category.assoc, l, k, k, ← Category.assoc, l]

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_abelian (hL : LL) (hR : AdmBase R I) (U : UnifPre I D A G) (aG : G ⟶ G) [IsMonHom aG] :
    ∃ aB : D.toPre.P.A ⟶ D.toPre.P.A, IsMonHom aB ∧ ∀ e,
      (Over.pullback (thick R I e)).map aG ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map aB := by
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => (gtCoord_end_torus_abelian hL R I hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R I e)).map aG) inferInstance).2.exists
  have hql : ∀ e, (U.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map aG).left ≫ (U.gt e).q.left :=
    fun e => (congrArg (·.left) (hq e)).symm
  obtain ⟨aB, haB⟩ := _root_.GlobalTheory.EndAlg.exists_end_of_thickenings R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _))
    (fun e => (b e).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w])
    (fun e => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      have : Epi (U.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U.gt (e + 1)).q.left, hql, ← Category.assoc (U.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D.toPre.P.isAb
    D.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact hq e

theorem exists_endU : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  intro hL R _ _ _ I hR D A G _ _ _ U aG aA hG hA hext
  have hC := hR.2.2.2
  have hB := D.toPre.P.isLB
  obtain ⟨aB, haB, hq⟩ := exists_abelian hL hR U.toUnifPre aG
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.unifPre_end_character_const hL R I hR D A G U.toUnifPre aG hG
  choose t ht hi using hh
  choose v hv vv using fun χ e => T.exists_gen_of_torusEnd_compat R I D.toPre e G (U.gt e) ((Over.pullback (thick R I e)).map aG) aB h (t e)
    inferInstance (ht e) (hi e) (hq e) χ
  have down : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      val ((U.gt (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((U.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) r)
  choose u hu uv using fun χ => _root_.GlobalTheory.Unif.exists_gen_of_thick R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L _ _ _ _ hB (fun _ _ => rfl)
    (v χ) (hv χ) (fun e z J hJ => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv χ (e + 1) _ (𝟙 _ ≫ thickMap R I e G) x J hJ
        have k₀ := vv χ e _ (𝟙 _) x J hJ
        rw [down _ _ _ _ _ _ hJ, Category.assoc, trans_map, ← Category.assoc, down _ _ _ _ _ _ hJ, k₀,
          Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨⟨aG, aA, aB, hG, hA, haB, h, hext, hq, fun e => ⟨t e, ht e, hi e⟩, u, fun χ => ⟨hu χ, ?_⟩,
    fun e χ Z x z J hJ => ?_⟩, rfl, rfl⟩
  · refine corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ (hu χ) _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_unit D.toPre (𝟙 _) (h χ) k).1
        (prod_unit D.toPre aB χ k).2).trans ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
    · have := (U.gt e).q_hom
      have k := vv χ e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul, ← uv χ e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.toPre.P.A) =
        η[thickObj R I e D.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val (u χ) p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D.toPre.P.A).symm).trans k.symm)
  · refine (vv χ e Z x z J hJ).trans (congrArg (_ * ·) ((uv χ e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val (u χ) p z J) (Category.assoc _ _ _)

end GlobalTheory.EndData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElementStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_sq_eq_of_symmetric_thetaElement : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (w₀ : W0 U.toUnifPre) (w : Frm D.toPre F N p.g.b), w₀.IsGen → w.IsGen → (∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s') → (∃ nu : LB.Gen (negLB A.A A.L N (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L N θ nu) (LB.oneGen A.L)) → ∀ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4) ![(𝟙 D.toPre.P.A ^ (N + 1)).left, (𝟙 D.toPre.P.A ^ N).left, 𝟙 _, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]), Normd ν → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J := by
  first | exact @GlobalTheory.SymFrame.sq_frame_of_symmetric | exact GlobalTheory.SymFrame.sq_frame_of_symmetric | (intros; apply GlobalTheory.SymFrame.sq_frame_of_symmetric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyAlgebraisationAbelianQuotientTower
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AlgTower

section Bundles
variable {X X' Y Y' Z : Scheme.{0}}

theorem triv_chart {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (t : Triv A) : Triv A' := by
  obtain ⟨t, ht⟩ := t
  exact gen_chartPull a t ht

def chartDivTriv (A : LB X) : ChartPull (LB.div A (Inh.trivLB X)) A (𝟙 X) where
  idx p := p.1
  le _ _ hy := hy.1
  g y p q hp hq := (gm_div (Inh.trivLB X) A (𝟙 X) y p q ⟨hp, hq⟩).trans
    ((congrArg (_ * ·⁻¹) (map_one _)).trans (by rw [inv_one, _root_.mul_one]))

def chartTrivDiv (A : LB X) : ChartPull A (LB.div A (Inh.trivLB X)) (𝟙 X) where
  idx i := (i, PUnit.unit)
  le _ _ hy := ⟨hy, trivial⟩
  g y i j hi hj := ((chartDivTriv A).g y (i, PUnit.unit) (j, PUnit.unit) ⟨hi, trivial⟩ ⟨hj, trivial⟩).symm

theorem triv_of_lbIso {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) (t : Triv A) : Triv B :=
  triv_chart (chartTrivDiv B) (LBIso.trans (Inh.trivLB_isLB X) hA hB (triv_chart (chartDivTriv A) t) h)

def chartPullDiv (H P : LB X) (f : Y ⟶ X) :
    ChartPull ((LB.div H P).pull f) (LB.div (H.pull f) (P.pull f)) (𝟙 Y) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have a' := mem_pull.1 hj'
    refine (gm_pull_g (LB.div H P) f (𝟙 Y) y J J' hj hj').trans ((gm_div P H _ y _ _ ⟨a, a'⟩).trans (Eq.symm ?_))
    refine (gm_div (P.pull f) (H.pull f) (𝟙 Y) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, mem_pull.2 a'.1, mem_pull.2 a'.2⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹) (gm_pull_g H f (𝟙 Y) y _ _ (mem_pull.2 a.1) (mem_pull.2 a'.1))
      (gm_pull_g P f (𝟙 Y) y _ _ (mem_pull.2 a.2) (mem_pull.2 a'.2))

theorem lbIso_factor {P H : LB X} {b : Y ⟶ X} (h : LBIso (P.pull b) (H.pull b)) (j : Z ⟶ Y) (f : Z ⟶ X)
    (e : f = j ≫ b) : LBIso (P.pull f) (H.pull f) :=
  h.chartPull (chartPullSame P _ _ _ j fun _ => e) (chartPullSame H _ _ _ j fun _ => e)

theorem triv_transfer {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : X' ⟶ X} (w : LBIso L' (L.pull F))
    {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ρ : Z ⟶ Y') (h : Z ⟶ Y)
    (e : ∀ k, (ρ ≫ φ' k) ≫ F = h ≫ φ k) (t : Triv (LB.LinComb L' φ' ε)) :
    Triv ((LB.LinComb L φ ε).pull h) := by
  obtain ⟨w, hw⟩ := w
  exact triv_chart (chartPullOut L φ ε h _ e) (triv_of_lbIso (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _)
    (iso_linComb ((isGen_iff w).1 hw) (fun k => ρ ≫ φ' k) ε)
    (triv_chart (chartPullSame L' _ φ' ε ρ fun _ => rfl) t))

end Bundles

section Points
variable {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
  {f : S' ⟶ S} {b : B'.left ⟶ B.left}


omit [IsCommMonObj B] [IsCommMonObj B'] in
theorem exists_lift (h : IsGrpPullback B' B f b) (T : Over S') (x : Over.mk (T.hom ≫ f) ⟶ B) :
    ∃ x' : T ⟶ B', pushPt h.1.w x' = x :=
  ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

variable {M : LB B.left} (hM : M.IsLB) (M' : CP B') (h : IsGrpPullback B' B f b) (w : LBIso M'.L.L (M.pull b))
include hM h w

theorem triv_theta (T : Over S') (U : Over.mk (T.hom ≫ f) ⟶ G3 B) : Triv ((Theta B M).pull U.left) := by
  choose x hx using fun i => exists_lift h T (U ≫ x3 B i)
  refine triv_transfer hM M'.L.isLB w (thφ B' (x3 B')) (thφ B (x3 B)) thε (lift (x 0) (lift (x 1) (x 2))).left U.left
    (fun I => ?_) ⟨M'.c.t, M'.c.isGen⟩
  have e : lift (x 0) (lift (x 1) (x 2)) ≫ psum B' (x3 B') I.down = psum B' x I.down :=
    (psum_hom (preHom _) (x3 B') I.down).trans (congrArg (fun z => psum B' z I.down) (funext fun i => by
      fin_cases i <;> simp [preHom, x3]))
  exact (congrArg (fun q => q.left ≫ b) e).trans (psum_push h x (x3 B) U hx I.down)

theorem triv_sym (T : Over S') (U : Over.mk (T.hom ≫ f) ⟶ B) :
    Triv ((LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).pull U.left) := by
  obtain ⟨x, hx⟩ := exists_lift h T U
  refine triv_transfer hM M'.L.isLB w _ _ _ x.left U.left (fun k => ?_) ⟨M'.sym, M'.sym_gen⟩
  have e : pushPt h.1.w x⁻¹ = U⁻¹ := hx ▸ map_inv (pushHom h T) x
  fin_cases k
  · exact congrArg (fun q => q.left) e
  · exact (congrArg (· ≫ b) (Category.comp_id _)).trans
      ((congrArg (fun q => q.left) hx).trans (Category.comp_id _).symm)

end Points

section Complete
variable (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (IsLocalRing.maximalIdeal V) V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B] [IsCommMonObj B]
  (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {M : LB B.left} (hM : M.IsLB)
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))}
  {b : ∀ e, (Y e).left ⟶ B.left}
include hG hB hp hM

theorem triv_theta_of_levels [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (P : ∀ e, CP (Y e))
    (h : ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e)) (w : ∀ e, LBIso (P e).L.L (M.pull (b e))) :
    Triv (Theta B M) :=
  GlobalTheory.AbTriv.triv_of_forall_thick hG V (G3 B)
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB))
    (isProjBy_tensor V _ _ hp (isProjBy_tensor V _ _ hp hp)) _ (DVR.linComb_isLB _ hM _ _)
    fun e => triv_theta hM (P e) (h e) (w e) (thickObj V _ e (G3 B))
      (Over.homMk (pullback.fst (G3 B).hom (thick V _ e)) pullback.condition)

theorem triv_sym_of_levels [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (P : ∀ e, CP (Y e))
    (h : ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e)) (w : ∀ e, LBIso (P e).L.L (M.pull (b e))) :
    Triv (LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) :=
  GlobalTheory.AbTriv.triv_of_forall_thick hG V B hB hp _ (DVR.linComb_isLB _ hM _ _)
    fun e => triv_sym hM (P e) (h e) (w e) (thickObj V _ e B)
      (Over.homMk (pullback.fst B.hom (thick V _ e)) pullback.condition)


omit [IsCommMonObj B] in
theorem lbIso_of_levels {H : LB B.left} (hH : H.IsLB) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick V _ e))
    (w : ∀ e, LBIso (M.pull (b e)) (H.pull (b e))) : LBIso M H :=
  GlobalTheory.AbTriv.triv_of_forall_thick hG V B hB hp (LB.div H M) (LB.isLB_div hH hM) fun e =>
    triv_chart (chartPullDiv H M _) (lbIso_factor (w e)
      ((hb e).lift (pullback.fst B.hom (thick V _ e)) (pullback.snd B.hom (thick V _ e)) pullback.condition) _
      ((hb e).lift_fst _ _ _).symm)

end Complete

theorem relAmple_of_lbIso {V : Type} [CommRing V] {B : Over (Spec (CommRingCat.of V))} {M H : LB B.left}
    (hM : M.IsLB) (hH : H.IsLB) {n d : ℕ} (hd : 1 ≤ d) {σ : Fin (n + 1) → LB.Sec H} (hva : VeryAmpleBy B.hom H σ)
    (h : LBIso (AbLaw.pw M d) H) : RelAmple B M := by
  have hP := isLB_pw hM d
  obtain ⟨w, hw⟩ : LBIso (AbLaw.pw M d) (H.pull (𝟙 _)) :=
    h.chartPull (chartPullId _) (Geo.Tor.chartPullPull H _ _ rfl)
  choose σ' hσ' using fun j => (GlobalTheory.SecPullIso.section_pull _ _ (𝟙 _) H _ w hH hP hw (σ j)).1.exists
  have hc : 𝟙 B.left ≫ B.hom = B.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id V)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
  have hci : IsClosedImmersion (pullback.lift (𝟙 B.left) B.hom hc) := by
    have : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id V))) := by
      rw [CommRingCat.ofHom_id, Spec.map_id]; infer_instance
    have : IsIso (pullback.lift (𝟙 B.left) B.hom hc ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; infer_instance
    have : IsIso (pullback.lift (𝟙 B.left) B.hom hc) := IsIso.of_isIso_comp_right _ (pullback.fst _ _)
    infer_instance
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B M hM).2
    ⟨d, hd, n, σ', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V _ B.hom H n σ hH hva V (RingHom.id V) _ B.hom (𝟙 _)
      hc hci _ w σ' hP hw hσ'⟩

theorem isPullback_of_grp {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {f : S' ⟶ S}
    {b : B'.left ⟶ B.left} (h : IsGrpPullback B' B f b) : IsPullback b B'.hom B.hom f := h.1

theorem exists_rig {V : Type} [CommRing V] [IsLocalRing V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B]
    {M : LB B.left} (hM : M.IsLB) : ∃ L : RigLB B, L.L = M := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_local (V := V) M hM (K := PUnit) (fun _ => eSec B) (fun _ => 1)
  exact ⟨⟨M, r, hM, hr⟩, rfl⟩

theorem lbIso_pw_pull {X Y : Scheme.{0}} {M H : LB X} {N : LB Y} (hM : M.IsLB) (hH : H.IsLB) (hN : N.IsLB)
    {b : Y ⟶ X} {d : ℤ} (h₁ : LBIso N (M.pull b)) (h₂ : LBIso (AbLaw.pw N d) (H.pull b)) :
    LBIso ((AbLaw.pw M d).pull b) (H.pull b) := by
  refine LBIso.trans (pull_isLB (isLB_pw hM d) _) (isLB_pw hN d) (pull_isLB hH _) ?_ h₂
  rw [GlobalTheory.Algebraise.pw_pull]
  exact (GlobalTheory.Algebraise.lbIso_pw h₁ d).symm

theorem exists_cp (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {M : LB B.left} (hM : M.IsLB)
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))}
    {b : ∀ e, (Y e).left ⟶ B.left} [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e))
    (P : ∀ e, CP (Y e)) (h : ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e))
    (w : ∀ e, LBIso (P e).L.L (M.pull (b e))) :
    ∃ Q : CP B, Q.L.L = M ∧ ∀ e, IsCPPullback (P e) Q (thick V _ e) (b e) := by
  obtain ⟨L, rfl⟩ := exists_rig hM
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB
  obtain ⟨Q, rfl⟩ := h₁ L (triv_theta_of_levels hG hB hp hM P h w) (triv_sym_of_levels hG hB hp hM P h w)
  exact ⟨Q, rfl, fun e => h₂ _ _ _ (hY e) Q (P e) _ (h e) ⟨(P e).L.rig, (P e).L.rigGen⟩ (w e)⟩

theorem exists_alg (hG : GlobalFnsSt) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    [∀ e, GrpObj (Y e)] [hc : ∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e)) (P : ∀ e, CP (Y e))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsCPPullback (P e) (P (e + 1)) (thickTrans V _ e) (β e)) (h₀ : RelAmple (Y 0) (P 0).L.L) :
    ∃ (B : Over (Spec (CommRingCat.of V))) (_ : GrpObj B) (_ : IsCommMonObj B) (M : CP B)
      (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ RelAmple B M.L.L ∧
      (∀ e, IsCPPullback (P e) M (thick V _ e) (b e)) ∧ ∀ e, β e ≫ b (e + 1) = b e := by
  have hg : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e) := fun e => by
    obtain ⟨h, -⟩ := hβ e
    exact h
  have hv : ∀ e, ∃ v : LB.Iso (P e).L.L ((P (e + 1)).L.L.pull (β e)), v.IsGen := fun e => by
    obtain ⟨_, v, h⟩ := hβ e
    exact ⟨v, h.gen⟩
  choose v hv using hv
  have hf : ∀ e, Flat (Y e).hom := fun e => by
    have := (hY e).smooth
    infer_instance
  obtain ⟨B, M, H, b, n, d, σ, hM, hH, -, hva, hd, hb, hbβ, hiso⟩ :=
    GlobalTheory.Algebraise.algebraisation V Y β (fun e => isPullback_of_grp (hg e)) hf (fun e => (P e).L.L) v
      (fun e => ⟨(P e).L.isLB, hv e⟩) h₀
  have hp : IsProjBy B.hom := ⟨H, hH, n, σ, hva⟩
  obtain ⟨grp, comm, hB, hgb⟩ := _root_.GlobalTheory.isAbelianScheme_of_thickenings V Y β hg B b hY hc hp hb hbβ
  have hamp : RelAmple B M := relAmple_of_lbIso hM hH hd hva (lbIso_of_levels hG hB hp (isLB_pw hM d) hH hb
    fun e => lbIso_pw_pull hM hH (P e).L.isLB (hiso e).1 (hiso e).2)
  obtain ⟨Q, rfl, hQ⟩ := exists_cp hG hB hp hM hY P hgb fun e => (hiso e).1
  exact ⟨B, grp, comm, Q, b, hB, hamp, hQ, hbβ⟩

theorem nonempty_alg : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ t : Tower s, Nonempty t.Alg := by
  intro hcard hL V _ _ _ A G _ _ s t
  haveI : IsDiscreteValuationRing V := s.cdvr.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := s.cdvr.2.1
  obtain ⟨B, _, _, M, b, hB, ha, hb, hbβ⟩ := exists_alg hL.globalFns V (fun e => (t.l e).Q.B)
    (fun e => (t.l e).Q.isAb) (fun e => (t.l e).D.M) t.β t.β_pb (_root_.GlobalTheory.UU.AmpleZero.relAmple_zero hcard hL V A G s t)
  exact ⟨{ B := B, isAb := hB, M := M, ample := ha, b := b, b_pb := hb, b_β := hbβ }⟩

end GlobalTheory.AlgTower
end
end

