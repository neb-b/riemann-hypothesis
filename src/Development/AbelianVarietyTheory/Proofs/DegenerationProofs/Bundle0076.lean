module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidificationComparisonUniformisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.RigCmpPf

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    eSec G' ≫ F = f ≫ eSec G := (cubeMapOf h).e_comm

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def upt (G : Over (Spec (CommRingCat.of R))) [GrpObj G] {e : ℕ} {Z : Scheme.{0}}
    (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) : Z ⟶ (thickObj R I e G).left :=
  a ≫ eSec (thickObj R I e G)

omit [IsDomain R] [IsCommMonObj G] in
theorem eSec_fst (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ (fstG I e G).left = (a ≫ thick R I e) ≫ eSec G :=
  (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (UnitValue.eSec_pullback_fst (thick R I e) G)).trans
    (Category.assoc _ _ _).symm)

theorem eSec_pG {e : ℕ} (g : GtCoord I D e G) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ g.pG.left = (a ≫ thick R I e) ≫ eSec D.P.A := by
  have := g.q_hom
  have h1 : (η[thickObj R I e G] ≫ g.q) = η[thickObj R I e D.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) := congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_fst (G := D.P.A) e a)
  unfold upt
  rw [← h2]
  exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm)

theorem rig_val (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (z : Z) {JG : (Z ⟶ G.left) → U.P.L.L.ι} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJG : Good U.P.L.L z JG)
    (hJ : Good D.P.L z J) :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw (U.w e) (upt G a) z (J ((upt G a) ≫ (U.gt e).pG.left))
          (fun _ => JG ((upt G a) ≫ (fstG I e G).left)) *
        val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z JG := by
  have h := (U.w_vals e (Over.mk a) z JG J hJG hJ _ (fun _ => rfl)).1
  rw [one_left] at h
  exact h

theorem rig_level {V : Type} [CommRing V] [IsDomain V] {I' : Ideal V} {D' : DegPre V}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}
    (C : Cmp φ U U' F) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (a' : Z ⟶ Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))
    (ha : a ≫ thick R I e = (a' ≫ thick V I' e) ≫ spMap φ) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw C.v (upt G' a' ≫ (U'.gt e).pG.left) z (J (upt G a ≫ (U.gt e).pG.left))
          (J' (upt G' a' ≫ (U'.gt e).pG.left)) *
        val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (a' ≫ thick V I' e) z J' := by
  have hG := eSec_comm C.pb
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨K', hK'⟩ := exists_good_pt U'.P.L.isLB z
  have e₁ := rig_val U e a z hK hJ
  have e₂ := rig_val U' e a' z hK' hJ'
  have e₃ := (C.wL_map.vals (Over.mk (a' ≫ thick V I' e)) z K' K hK' hK _ (fun _ => rfl)).1
  rw [one_left] at e₃
  have hx : upt G a ≫ (fstG I e G).left = (upt G' a' ≫ (fstG I' e G').left) ≫ F := by
    rw [eSec_fst e a, eSec_fst e a', ha]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hG.symm).trans (Category.assoc _ _ _).symm)
  have e₄ := ((C.lev e _ _ _ (hx.trans (Category.assoc _ _ _))).2 z J J' hJ hJ').2 _ _
    (hK (upt G a ≫ (fstG I e G).left)) (hK' (upt G' a' ≫ (fstG I' e G').left))
  have f₃ : val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z K =
      gw C.wL (upt G' a' ≫ (fstG I' e G').left) z (K (upt G a ≫ (fstG I e G).left))
        (K' (upt G' a' ≫ (fstG I' e G').left)) *
      val (L := U'.P.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) U'.P.L.rig
        (a' ≫ thick V I' e) z K' := by
    rw [ha, hx, eSec_fst e a']
    exact e₃
  exact e₁.trans ((congrArg _ f₃).trans ((_root_.mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄.symm).trans ((_root_.mul_assoc _ _ _).trans (congrArg _ e₂.symm)))))

end GlobalTheory.RigCmpPf

namespace GlobalTheory


open RigCmpPf in
theorem rigCmp_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I' ≠ ⊤ → I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), RigCmp φ D D' C.β C.v := by
  intro R V _ _ _ _ _ _ I I' φ hI' hφ D D' A G _ _ A' G' _ _ U U' F C
  have hB := eSec_comm C.pbB
  have key := AbelianPartIso.pmaps_of_thickenings hI' D.P.isLB D'.P.isLB C.v C.v_gen (eSec D'.P.A)
    (spMap φ ≫ eSec D.P.A) hB D'.rig D'.rig_gen
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (spMap φ))
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) fun e z p q hp hq => by
      have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono hφ _
      let a : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
        spMap (Ideal.quotientMap _ φ hle)
      have ha : a ≫ thick R I e = (𝟙 _ ≫ thick V I' e) ≫ spMap φ := by
        rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
        rfl
      obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (fun _ : Unit => thick V I' e ≫ spMap φ ≫ eSec D.P.A)
        (fun _ => p) (fun _ _ _ => rfl) (fun _ => hp)
      obtain ⟨J', hJ', eJ'⟩ := exists_good D'.P.L D'.P.isLB z (fun _ : Unit => thick V I' e ≫ eSec D'.P.A)
        (fun _ => q) (fun _ _ _ => rfl) (fun _ => hq)
      have E := rig_level C e a (𝟙 _) ha z hJ hJ'
      have hp' : (a ≫ thick R I e) ≫ eSec D.P.A = thick V I' e ≫ spMap φ ≫ eSec D.P.A := by
        rw [ha, Category.id_comp]
        exact Category.assoc _ _ _
      rw [eSec_pG (U.gt e) a, eSec_pG (U'.gt e) (𝟙 _), hp', ha, Category.id_comp, eJ (), eJ' (),
        val_of _ _ z J (fun _ => p) (fun _ => (congrArg J (Category.assoc _ _ _)).trans (eJ ())),
        val_of _ _ z J' (fun _ => q) (fun _ => eJ' ())] at E
      refine Eq.trans ?_ E
      have m₁ : thick V I' e z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      have m₂ : spMap φ (thick V I' e z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      exact (gm_res _ z _ m₁ _).trans (gm_pull _ (spMap φ) z _ m₂ _)
  intro Z r z p q hp hq
  have hm : (spMap φ ≫ eSec D.P.A) (r z) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun g => g (r z) ∈ D.P.L.U (p PUnit.unit)) hB).mp (hp PUnit.unit)
  refine Eq.trans ?_ (key Z r z p q hp hq)
  rw [Category.comp_id]
  have m₁ : r z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  have m₂ : spMap φ (r z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  exact ((gm_res r z _ m₁ _).trans (gm_pull r (spMap φ) z _ m₂ _)).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SameCoordsOfGermsCommonUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem toStk_valR_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valR x U a) = gs x z U a := by
  rw [valR, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem toStk_surjective {F : Type} [Field F] (y : Sp F) : Function.Surjective (toStk y) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp F).presheaf.exists_germ_eq s
  obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_mem (𝟙 (Sp F)) U y).2 hU)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom a, by simp [toStk]⟩

theorem crd_of_germs_unit : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (H : LB X) (H' : LB Y), H'.IsLB → ∀ (J : Type) (F : J → H.Sec) (σ : J → H'.Sec) (x : Sp k ⟶ X) (y : Sp k ⟶ Y), (∀ (z : Sp k) (l : H.ι) (l' : H'.ι), x z ∈ H.U l → y z ∈ H'.U l' → ∃ u : ((Sp k).presheaf.stalk z)ˣ, ∀ i, gs x z (H.U l) ((F i).f l) = u.val * gs y z (H'.U l') ((σ i).f l')) → ∀ v : J → k, GlobalTheory.ZH.Crd H F x v → GlobalTheory.ZH.Crd H' σ y v := by
  intro k _ X Y H H' hH' J F σ x y h v ⟨l, c, hl, hv⟩
  let z : Sp k := (⊥ : PrimeSpectrum k)
  obtain ⟨l', hl'⟩ := exists_chart hH' (y z)
  have hx := (top_le_iff_mem x _ z).1 hl
  obtain ⟨u, hu⟩ := h z l l' hx hl'
  obtain ⟨f, hf⟩ := toStk_surjective z u.val
  have f0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact u.ne_zero hf.symm
  refine ⟨l', c * Units.mk0 f f0, (top_le_iff_mem y _ z).2 hl', fun j => ?_⟩
  rw [hv j, Units.val_mul, Units.val_mk0, _root_.mul_assoc]
  congr 1
  apply (toStk z).injective
  rw [map_mul, toStk_valR_gs x _ z hx, toStk_valR_gs y _ z hl', hf, hu j]

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SeriesProportionalAddIotaIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IotaShift
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frame {k : ℕ} (y : D.X) (g : GtPtF D F) (w : Frm D F k g.b) (hw : w.IsGen)
    (b : TF (R := R) F ⟶ D.P.A) (hb : b = g.b * cP D _ y) :
    ∃ ω : Frm D F k b, ω.IsGen ∧ ∀ z J, Good D.P.L z J → val ω (𝟙 _) z J =
      val w (𝟙 _) z J * val (g.s y) (𝟙 _) z J ^ k *
        (val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J *
          val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J) := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      have a₁ : jFK (R := R) F ≫ D.xK y = (cP D (TF (R := R) F) y).left := (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      have a₃ : ∏ i, h (DegPre.gtφ D F g.b y i) ^ ((k : ℤ) * DegPre.gtε i) =
          (∏ i, h (DegPre.gtφ D F g.b y i) ^ DegPre.gtε i) ^ (k : ℤ) := by
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul, mul_comm]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [a₃, prod_gt, prod_line, prod_line, hb, mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (GeneratorPullback.powGen D.P.L _ _ (g.s y) k))
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k)
        (GeneratorPullback.powGen D.P.L _ _ D.rigK k)) (jFK (R := R) F)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (powGen_isGen _ _ _ _ (g.isGen y) k))
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen y) k)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _))
  refine ⟨u, hu, fun z J hJ => ?_⟩
  exact (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (map_pow _ _ _))) ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _))))

theorem coef_shift_frame (hG : GlobalFnsSt) {k : ℕ} {y : D.X} {g h g' : GtPtF D F} (hι : GtPtF.IsIota y h)
    (hadd : GtPtF.IsAdd g h g') (w : Frm D F k g.b) (hw : w.IsGen) :
    ∃ ω : Frm D F k g'.b, ω.IsGen ∧ ∀ (s : Fam D F k) α, coef s g w (α + k • y) = coef s g' ω α := by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  rw [ιb] at hb
  obtain ⟨ω, hω, vω⟩ := exists_frame y g w hw g'.b hb
  refine ⟨ω, hω, fun s α => coef_eq fun z J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k y α
  have e₁ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _
    (lift (𝟙 (TF (R := R) F)) g.b).left z J hJ
  have t : lift (𝟙 (TF (R := R) F)) g.b ≫ DegPre.trF D F y = lift (𝟙 (TF (R := R) F)) g'.b := by
    rw [trF_eq]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
    · rw [lift_snd, hb, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_
      rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
  rw [hv u hu hc _ _ z J hJ, ← Over.comp_left, t, val_famMult _ hJ, uVal, lift_fst_assoc, lift_fst, lift_snd,
    Category.id_comp, Over.id_left] at e₁
  have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g α y k
  rw [Category.id_comp, Over.id_left] at e₂
  have e₃ := hs α z J hJ
  have e₄ : th D z J (cP D _ α) g.b h.b = th D z J (cP D _ α) g.b (cP D _ y) := by rw [ιb]
  have e₅ : val (h.s α) (𝟙 _) z J = val (D.tau y α) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J := ιv α z J hJ
  rw [e₅, e₄] at e₃
  rw [isCoef_coef g' hω α s z J hJ, e₁, vω z J hJ]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
  linear_combination (norm := module) a₃ - a₂

theorem coef_shift (hG : GlobalFnsSt) {k : ℕ} {y : D.X} {g h g' : GtPtF D F} (hι : GtPtF.IsIota y h)
    (hadd : GtPtF.IsAdd g h g') (w : Frm D F k g.b) (hw : w.IsGen) (w' : Frm D F k g'.b) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (s : Fam D F k) α, coef s g' w' α = c * coef s g w (α + k • y) := by
  obtain ⟨ω, hω, e⟩ := coef_shift_frame hG hι hadd w hw
  obtain ⟨c, hc, -, e'⟩ := ((coef_basic R D F k g').2.2 ω hω).2.2.1 w' hw'
  exact ⟨c, hc, fun s α => by rw [e', e]⟩

end

theorem parAt_add_iota : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (a : u.PtC) (g h g' : GtPtF u.D.toPre (PadicAlgCl p)) (y : u.D.toPre.X), 1 ≤ k → GtPtF.IsIota y h → GtPtF.IsAdd g h g' → (u.ParAt k a g ↔ u.ParAt k a g') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k a g h g' y _ hι hadd
  constructor
  · intro H w' hw' l hl
    obtain ⟨w, hw⟩ := (coef_basic u.V u.D.toPre (PadicAlgCl p) k g).1
    obtain ⟨c, hc, e⟩ := coef_shift hL.1.globalFns hι hadd w hw w' hw'
    obtain ⟨κ, hκ, hs⟩ := H w hw l hl
    refine ⟨c * κ, mul_ne_zero hc hκ, fun σ s hσ => ?_⟩
    rw [_root_.mul_assoc, funext (e s)]
    exact ((Equiv.addRight (k • y)).hasSum_iff.2 (hs σ s hσ)).mul_left c
  · intro H w hw l hl
    obtain ⟨w', hw'⟩ := (coef_basic u.V u.D.toPre (PadicAlgCl p) k g').1
    obtain ⟨c, hc, e⟩ := coef_shift hL.1.globalFns hι hadd w hw w' hw'
    obtain ⟨κ, hκ, hs⟩ := H w' hw' l hl
    refine ⟨c⁻¹ * κ, mul_ne_zero (inv_ne_zero hc) hκ, fun σ s hσ => ?_⟩
    rw [_root_.mul_assoc]
    refine (Equiv.addRight (k • y)).hasSum_iff.1 ?_
    have := (hs σ s hσ).mul_left c⁻¹
    simp only [e s, inv_mul_cancel_left₀ hc] at this
    exact this

end GlobalTheory.ZH.IotaShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanRowsClassZeroEqInvariant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.WeightZero

theorem eq_zero_of_q_nonpos {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {α : X} (h : q α ≤ 0) : α = 0 := by
  by_contra h0
  have h1 : {x | ¬ 0 < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • α) (smul_left_injective ℤ h0)
    (fun n => ?_) h1
  rw [Set.mem_setOf_eq, q.map_smul, not_lt]
  exact smul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg n) h

theorem proj_congr {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t ht ht', c ⟨t, ht⟩ = c' ⟨t, ht'⟩) : S.proj T c = S.proj T' c' := by
  subst h
  rw [show c = c' from AddMonoidHom.ext fun t => hc t.1 t.2 t.2]

theorem nsmul_char {T : Type} [AddCommGroup T] (N : ℕ) (c : T →+ ZMod N) : N • c = 0 := by
  ext x
  rw [AddMonoidHom.nsmul_apply]
  simp

theorem map_add_nsmul {X T : Type} [AddCommGroup X] [AddCommGroup T] (N : ℕ) (w : X →+ (T →+ ZMod N)) (β m : X) :
    w (β + N • m) = w β := by
  rw [map_add (f := _), map_nsmul, nsmul_char, add_zero]

theorem span_eq_of_test {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] {S : ThetaSys o Ω}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀) (b : S.J → S.J → PadicAlgCl p)
    (a : S.J → τ.X) (ha : ∀ i v, τ.q (a i) ≤ τ.q (a i + S.N • v))
    (hE : τ.E = Submodule.span (OO p) (Set.range b))
    (hb : ∀ i, ((S.proj _ (τ.wt (a i))).map fun x => y₀ (algebraMap o S.R x)).mulVec (b i) = b i) :
    Submodule.span (OO p) (b '' {i | a i = 0}) =
      Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp τ.yy.ker) 0 j i))) := by
  have : IsDomain o := hA.inj.isDomain
  have := FreeNear.finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := FreeNear.proj_orthogonal S _ τ.isoFree
  have hz : ∀ α, (∀ v, τ.q α ≤ τ.q (α + S.N • v)) → 0 = τ.wt α → α = 0 := fun α hα h => by
    have h3 := TestBasis.q_le_of_wt_eq τ hα (β := 0) (by rw [map_zero, h])
    rw [map_zero] at h3
    exact eq_zero_of_q_nonpos _ τ.pos h3
  let φ : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  obtain ⟨Q, hQd⟩ : ∃ Q : (S.perp τ.yy.ker →+ ZMod S.N) → Matrix S.J S.J (PadicAlgCl p),
    ∀ c j i, y₀ (algebraMap o S.R (S.proj _ c j i)) = Q c j i := ⟨fun c => (S.proj _ c).map φ, fun _ _ _ => rfl⟩
  have hQe : ∀ c, Q c = φ.mapMatrix (S.proj _ c) := fun c => Matrix.ext fun j i => (hQd c j i).symm
  have hQ : ∀ c, Q 0 * Q c = if 0 = c then Q 0 else 0 := fun c => by
    rw [hQe, hQe, ← map_mul, hmul]
    split_ifs
    · rfl
    · exact map_zero _
  obtain ⟨L, hL⟩ : ∃ L : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p), ∀ v, L v = (Q 0).mulVec v :=
    ⟨(Q 0).mulVecLin.restrictScalars (OO p), fun _ => rfl⟩
  have hcol : ∀ c i, L (fun j => Q c j i) = fun j => (Q 0 * Q c) j i := fun c i => hL _
  have hb' : ∀ i, (Q (τ.wt (a i))).mulVec (b i) = b i := fun i => by
    rw [hQe]
    exact hb i
  simp only [hQd]
  have h1 : τ.E.map L ≤ Submodule.span (OO p) (Set.range fun i j => Q 0 j i) := by
    rw [ThetaSys.Test.E, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨α, l, i, hα, hl, rfl⟩, rfl⟩
    simp only [hQd]
    have h2 : L (fun j => l * Q (τ.wt α) j i) = l • fun j => (Q 0 * Q (τ.wt α)) j i := by
      rw [← hcol, hL, hL, ← Matrix.mulVec_smul]
      rfl
    rw [h2, hQ]
    split_ifs with h
    · rw [hz α hα h, map_zero, zero_div, Real.exp_zero] at hl
      exact Submodule.smul_mem _ (⟨l, (mem_OO_iff _).2 hl⟩ : OO p) (Submodule.subset_span ⟨i, rfl⟩)
    · rw [show (fun j => (0 : Matrix S.J S.J (PadicAlgCl p)) j i) = 0 from rfl, smul_zero]
      exact Submodule.zero_mem _
  have h2 : τ.E.map L ≤ Submodule.span (OO p) (b '' {i | a i = 0}) := by
    rw [hE, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases h : 0 = τ.wt (a i)
    · rw [hL, h, hb']
      exact Submodule.subset_span ⟨i, hz _ (ha i) h, rfl⟩
    · rw [hL, ← hb', Matrix.mulVec_mulVec, hQ, if_neg h, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, hi, rfl⟩
    refine h1 ⟨b i, hE ▸ Submodule.subset_span ⟨i, rfl⟩, ?_⟩
    have := hb' i
    rw [show a i = 0 from hi, map_zero] at this
    rw [hL, this]
  · rintro _ ⟨i, rfl⟩
    refine h2 ⟨fun j => Q 0 j i, Submodule.subset_span ⟨0, 1, i, fun v => ?_, ?_, ?_⟩, ?_⟩
    · rw [map_zero]
      by_contra! h
      rw [eq_zero_of_q_nonpos _ τ.pos h.le, map_zero] at h
      exact lt_irrefl _ h
    · simp
    · funext j
      rw [map_zero, _root_.one_mul, hQd]
    · rw [hcol, hQ, if_pos rfl]

theorem short_transfer {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] (e : X ≃+ Y) (f : Z ≃+ Y)
    (q : QuadraticMap ℤ X ℝ) (q' : QuadraticMap ℤ Y ℝ) (hq : ∀ α, q α = q' (e α)) {N : ℕ} {y : Y}
    (h : Short (q'.comp f.toIntLinearEquiv.toLinearMap) N (f.symm y)) (v : X) :
    q (e.symm y) ≤ q (e.symm y + N • v) := by
  have h3 : q' (f (f.symm y)) ≤ q' (f (f.symm y + N • f.symm (e v))) := h (f.symm (e v))
  simpa [hq] using h3

end GlobalTheory.ZH.WeightZero

namespace GlobalTheory.ZH


open WeightZero in
theorem span_rows_class_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → t.τ.yy.ker = t.l.yy.ker ∧ (∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m) ∧ Submodule.span (OO p) ((t.b.map (algebraMap _ (PadicAlgCl p))) '' {i | t.cls i = 0}) = Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp t.l.yy.ker) 0 j i))) := by
  intro o Ω _ _ _ hA S ρ p _ y₀ t _
  obtain ⟨e, hq, hy⟩ := t.mt
  have hker : t.τ.yy.ker = t.l.yy.ker := by
    ext a
    have := hy a 0
    rw [map_zero] at this
    exact this
  have hwt : ∀ α x h h', t.τ.wt α ⟨x, h⟩ = t.l.wt (e α) ⟨x, h'⟩ := fun α x h h' => by
    obtain ⟨a, ha⟩ := t.τ.yy_onto (QuotientAddGroup.mk α)
    rw [t.τ.wt_eq a α ha, t.l.wt_eq a _ ((hy a α).1 ha)]
  have hz : ∀ α, t.l.wt (e α) = 0 → ∃ v, α = S.N • v := fun α h =>
    TestBasis.exists_nsmul_of_wt_eq_zero t.τ α (AddMonoidHom.ext fun x => by
      rw [hwt α x.1 x.2 (hker ▸ x.2), h]
      rfl)
  have hcl : ∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m := fun α β => by
    constructor
    · intro h
      obtain ⟨v, hv⟩ := hz (e.symm (α - β)) (by rw [e.apply_symm_apply, map_sub, h, sub_self])
      refine ⟨e v, ?_⟩
      rw [← map_nsmul, ← hv, e.apply_symm_apply, add_sub_cancel]
    · rintro ⟨m, rfl⟩
      exact map_add_nsmul _ _ _ _
  refine ⟨hker, hcl, ?_⟩
  have h1 := span_eq_of_test t.τ (t.b.map (algebraMap _ (PadicAlgCl p))) (fun i => e.symm (t.cls i))
    (fun i => short_transfer e t.mod.xe _ _ hq (t.mod.good.short i)) t.span
    (fun i => by
      have h3 : S.proj _ (t.τ.wt (e.symm (t.cls i))) = S.proj _ (t.l.wt (t.cls i)) :=
        proj_congr S (congrArg S.perp hker) _ _ fun x h h' =>
          (hwt _ x h h').trans (by rw [e.apply_symm_apply])
      rw [h3]
      exact t.wt i)
  have h2 : {i | e.symm (t.cls i) = 0} = {i | t.cls i = 0} := Set.ext fun i => e.symm.map_eq_zero_iff
  have h3 : S.proj (S.perp t.τ.yy.ker) 0 = S.proj (S.perp t.l.yy.ker) 0 :=
    proj_congr S (congrArg S.perp hker) _ _ fun _ _ _ => rfl
  rw [h2, h3] at h1
  exact h1

end GlobalTheory.ZH
end

