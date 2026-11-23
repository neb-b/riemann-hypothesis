module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiCmpOfSecCmp
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiBaseChange

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R} {D' : DegPre V}
  {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)} {xe : D'.X ≃+ D.X}

theorem secCmp_val {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α} (h : SecCmp D D' β v xe f f')
    (α : D'.X) {T : Over (Spec (CommRingCat.of V))} (y : T ⟶ D'.P.A) (r : T.left ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = y.left ≫ β) (z : T.left) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (Ω : (T.left ⟶ D'.P.A.left) → (T.left.presheaf.stalk z)ˣ) (hΩ : ∀ q, Ω q = gw v q z (J (q ≫ β)) (J' q)) :
    sval (f (xe α)) r z J = (Ω (y * cT D' T α).left * (Ω (cT D' T α).left)⁻¹ * Ω (1 : T ⟶ D'.P.A).left).val *
      sval (f' α) (lift (toUnit T) y).left z J' := by
  have a : (lift (toUnit T) y).left ≫ (snd _ D'.P.A).left = y.left := congrArg (fun q => q.left) (lift_snd (toUnit T) y)
  refine (h α _ (lift (toUnit T) y).left r (by rw [hr, ← Category.assoc, a]) z J J' hJ hJ').trans ?_
  refine congrArg (fun u : (T.left.presheaf.stalk z)ˣ => u.val * sval (f' α) (lift (toUnit T) y).left z J') ?_
  simp only [← Category.assoc, ← hΩ, PsiExists.comp_famφT, lift_snd]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem val_psi (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β)
    (hc : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) (hrig : RigCmp φ D D' β v)
    {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α} (hf : SecCmp D D' β v xe f f')
    (h : PsiRel D (𝟙_ _) f) (h' : PsiRel D' (𝟙_ _) f') {gam : (TK V).left ⟶ (TK R).left}
    (hg : gam ≫ jK R = jK V ≫ spMap φ) (x : D'.X) {T : Over (Spec (CommRingCat.of V))} [IsIntegral T.left]
    (κ : T ⟶ TK V) (p : T ⟶ D'.P.A) (z : T.left) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (ne : sval (f' 0) (lift (toUnit T) p).left z J' ≠ 0) :
    val (D.psi (xe x)) (κ.left ≫ gam) z J =
      (gw v (κ.left ≫ D'.xK x) z (J ((κ.left ≫ D'.xK x) ≫ β)) (J' (κ.left ≫ D'.xK x)))⁻¹ *
        val (D'.psi x) κ.left z J' := by
  let T₀ : Over (Spec (CommRingCat.of R)) := Over.mk (T.hom ≫ spMap φ)
  let κ₀ : T₀ ⟶ TK R := Over.homMk (κ.left ≫ gam) (by
    have w : κ.left ≫ jK V = T.hom := Over.w κ
    show (κ.left ≫ gam) ≫ jK R = T.hom ≫ spMap φ
    rw [Category.assoc, hg, ← Category.assoc, w])
  let b : (T ⟶ D'.P.A) →* (T₀ ⟶ D.P.A) := pushHom gp T
  have bc : b (cT D' T x) = cT D T₀ (xe x) := Over.OverMorphism.ext (by
    show (T.hom ≫ (D'.c x).left) ≫ β = (T.hom ≫ spMap φ) ≫ (D.c (xe x)).left
    rw [Category.assoc, hc, Category.assoc])
  let Ω : (T.left ⟶ D'.P.A.left) → (T.left.presheaf.stalk z)ˣ := fun q => gw v q z (J (q ≫ β)) (J' q)
  let y : T ⟶ D'.P.A := p * (cT D' T x)⁻¹
  have hy : y * cT D' T x = p := inv_mul_cancel_right _ _
  have hyb : b y * cT D T₀ (xe x) = b p := by rw [← bc, ← map_mul, hy]
  have sn : ∀ q : T ⟶ D'.P.A, (lift (toUnit T₀) (b q)).left ≫ (snd _ D.P.A).left = q.left ≫ β := fun q =>
    congrArg (fun q => q.left) (lift_snd (toUnit T₀) (b q))
  have e₁ := h (xe x) T₀ (toUnit _) κ₀ (b y) z J hJ
  have e₂ := h' x T (toUnit _) κ y z J' hJ'
  have e₃ := secCmp_val hf x y _ (sn y) z hJ hJ' Ω fun _ => rfl
  have e₄ := secCmp_val hf 0 p _ (sn p) z hJ hJ' Ω fun _ => rfl
  have e₀ : ∀ α : D.X, α = 0 → sval (f α) (lift (toUnit T₀) (b p)).left z J =
      sval (f 0) (lift (toUnit T₀) (b p)).left z J := by
    rintro _ rfl; rfl
  rw [PsiExists.cT_zero, _root_.mul_one, inv_mul_cancel_right] at e₄
  rw [hy] at e₂ e₃
  rw [hyb] at e₁
  have e₅ : @id (T.left.presheaf.stalk z)ˣ (rigV D (T := T₀) z J) = Ω (1 : T ⟶ D'.P.A).left * rigV D' z J' := by
    have := CubTransport.val_pmaps (fun _ => (cubeMapOf gp).e_comm) hrig T.hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at this
    exact this
  have e₆ : κ.left ≫ D'.xK x = (cT D' T x).left :=
    congrArg (fun q => q.left) (show κ ≫ cT D' _ x = cT D' _ x by rw [← Category.assoc, comp_toUnit])
  have e₇ := e₃.symm.trans (e₁.trans (congrArg₂ (· * ·)
    (congrArg (fun u : (T.left.presheaf.stalk z)ˣ => (val (D.psi (xe x)) (κ.left ≫ gam) z J * u).val) e₅)
    ((e₀ _ (map_zero xe)).symm.trans e₄)))
  rw [e₂] at e₇
  rw [e₆]
  refine PsiCompare.unit_cancel (a := Ω p.left) (c := Ω (1 : T ⟶ D'.P.A).left) (q := rigV D' z J') ne ?_
  rw [mul_comm (sval _ _ _ _)]
  exact e₇.trans (mul_comm _ _)

end GlobalTheory.PsiBaseChange

namespace GlobalTheory


open PsiBaseChange in
theorem psiCmp_of_secCmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α), SecCmp D D' β v xe f f' → PsiRel D (𝟙_ _) f → PsiRel D' (𝟙_ _) f' → (∃ j, (f' 0).f j ≠ 0) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hrig f f' hf h h' hne gam hg x
  have hL := D.P.isLB
  have hL' := D'.P.isLB
  have pg := (isGen_iff v).1 hv
  have := D'.P.isAb.smooth
  have := D'.P.isAb.geomConnected
  have : IsIntegral (TF (R := V) (FractionRing V)).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of _)))
  have : IsIntegral (DegPre.BF D' (FractionRing V)).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D'.P.A (TF (R := V) (FractionRing V))
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    show (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc, ← Category.assoc gam, hg, Category.assoc]
  let T := DegPre.BF D' (FractionRing V)
  let π : T.left ⟶ (TK V).left := (fst (TF (R := V) (FractionRing V)) D'.P.A).left ≫ jFK (R := V) (FractionRing V)
  let κ : T ⟶ TK V := Over.homMk π
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := V) (FractionRing V)) D'.P.A)))
  obtain ⟨s, hs⟩ := PsiExists.exists_pullB D' (FractionRing V) (toUnit _) 1 f'
  have hs0 := (pullB_ne_zero_iff V D' _ 1 f' s hs 0).2 hne
  have wl : toUnit (TF (R := V) (FractionRing V)) ▷ D'.P.A = lift (toUnit T) (snd _ D'.P.A) :=
    CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ((whiskerRight_snd _ _).trans (lift_snd _ _).symm)
  have key : ∀ (z : T.left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (π ≫ gam) z J =
        (gw v (π ≫ D'.xK x) z (J ((π ≫ D'.xK x) ≫ β)) (J' (π ≫ D'.xK x)))⁻¹ * val (D'.psi x) π z J' :=
    fun z J J' hJ hJ' => val_psi gp hc hrig hf h h' hg x κ (snd _ D'.P.A) z hJ hJ' (by
      rw [← wl, ← hs 0 z J' hJ']
      exact (exists_ne_zero_iff_sval_ne_zero _ hJ').1 hs0)
  obtain ⟨t, ht, hv⟩ := exists_up pg hL hL' (φ' := fun _ : PUnit => D'.xK x) (D'.psi x) (D'.psi_gen x)
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi (xe x)) (π ≫ gam))
      (LB.pullGen D.P.L _ _ t π) :=
    corr_of_val hL fun z J hJ => by
      choose J' hJ' using fun ψ : T.left ⟶ D'.P.A.left => exists_chart hL' (ψ z)
      rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, key z J J' hJ hJ']
      refine Eq.trans ?_ (hv _ π z _ _ (Good.mem hJ _ π) (Good.mem hJ' _ π)).symm
      rw [pw, Fintype.prod_unique, zpow_neg_one, Category.assoc]; rfl
  have hz : (DegPre.zF D' (FractionRing V)).left ≫ π = 𝟙 (TK V).left := PsiCompare.zF_fst D'
  refine EvenPull.pmaps_of_section pg hL hL' gam (fun _ => hx) _ (D'.psi_gen x) _ (D.psi_gen _) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (by rw [Scheme.Hom.id_appTop]; exact Function.surjective_id) fun y J J' hJ hJ' => ?_
  have := val_corr hJ hcorr (DegPre.zF D' (FractionRing V)).left
  rw [val_pull hJ, val_pull hJ, ← Category.assoc, hz] at this
  refine this.trans ((hv _ (𝟙 _) y _ _ (Good.mem hJ _ _) (Good.mem hJ' _ _)).trans ?_)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [pw, Fintype.prod_unique, Fintype.prod_unique, Category.assoc]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpT
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiExpansion

theorem exists_sec_of_retract {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (m : Y ⟶ Y') (hm : h ≫ m = 𝟙 Y')
    (e : ∀ k, m ≫ φ' k = φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ g => by simp only [e]) (H1.SectionArithmetic.pullSec s' m)
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, Category.assoc, hm, Category.comp_id]

theorem snd_lift_unit {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ _) G).left ≫ (lift (toUnit G) (𝟙 G)).left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  have : snd (𝟙_ _) G ≫ lift (toUnit G) (𝟙 G) = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  exact congrArg CommaMorphism.left this

variable {R : Type} [CommRing R] [IsDomain R]


omit [IsDomain R] in
theorem exists_lift_of_retraction (F : Type) [Field F] [Algebra (FractionRing R) F] (g : F →+* FractionRing R)
    (hg : ∀ a, g (algebraMap (FractionRing R) F a) = a) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) F, κ'.left ≫ jFK (R := R) F = κ.left := by
  let i : (TK R).left ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom g)
  have hi : i ≫ jFK (R := R) F = 𝟙 (TK R).left := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    exact CommRingCat.hom_ext (RingHom.ext hg)
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by
    rw [Category.assoc, hi, Category.comp_id]
  exact ⟨Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ))), hκ⟩

theorem exists_lift_frac {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) (FractionRing R), κ'.left ≫ jFK (R := R) (FractionRing R) = κ.left :=
  exists_lift_of_retraction (FractionRing R) (RingHom.id _) (fun _ => rfl) κ


omit [IsDomain R] in
theorem exists_sameG {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ)))) :
    ∃ σ : H0 L k, SameG σ s :=
  exists_sec_of_retract hL _ _ (snd_lift_unit G)
    (fun _ => congrArg CommaMorphism.left (lift_snd (toUnit G) (𝟙 G))) s

theorem exists_sameB {D : DegPre R} {k : ℕ} (s : ∀ α, SecBT D (𝟙_ _) k α) : ∃ f : ∀ α, D.SecB k α, SameB f s := by
  have H : ∀ α, ∃ f : D.SecB k α, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval f (r ≫ (snd _ D.P.A).left) z J := fun α => by
    refine exists_sec_of_retract D.P.isLB _ _ (snd_lift_unit D.P.A) (fun i => ?_) (s α)
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.P.A) (𝟙 D.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫
        padd D.P.A (snd _ _) (toUnit _ ≫ D.c α) = padd D.P.A (𝟙 _) (toUnit _ ≫ D.c α) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ D.c α = toUnit _ ≫ D.c α from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ η[D.P.A] = toUnit _ ≫ η[D.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  choose f hf using H
  exact ⟨f, hf⟩

theorem psiRel_of_levelOneEq {D : DegPre R} {f₀ : ∀ α, D.SecB 1 α} {f : ∀ α, SecBT D (𝟙_ _) 1 α}
    (hs : SameB f₀ f) (h : PsiCompare.LevelOneEq D f₀) : PsiRel D (𝟙_ _) f := by
  intro χ T ρ κ y z J hJ
  obtain ⟨κ', hκ⟩ := exists_lift_frac κ
  have l : ∀ u : T ⟶ D.P.A, (lift ρ u).left ≫ (snd _ D.P.A).left = u.left := fun u =>
    congrArg CommaMorphism.left (lift_snd ρ u)
  have e := (h χ 0 rfl T κ' y z J hJ).trans (congrArg (fun q => sval (f₀ 0) (y * cT D T χ).left z J *
    (val (D.psi χ) q z J * rigV D z J).val) hκ)
  rw [hs χ _ _ z J hJ, hs 0 _ _ z J hJ, l, l]
  exact e.trans (mul_comm _ _)

theorem psiRel_of_expT : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal V), AdmBase V I → ∀ (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U₀ : Unif I D A G), Under U U₀.toUnifPre → ∀ (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D.toPre (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 σ f → PsiRel D.toPre (𝟙_ _) f := by
  intro h₁ h₂ V _ _ _ I hV D A G _ _ U U₀ hU σ f hE
  obtain ⟨σ₁, hσ₁⟩ := exists_sameG U.P.L.isLB σ
  obtain ⟨f₀, hf₀⟩ := exists_sameB f
  have ht : H0 U.P.L.L 1 = H0 U₀.toUnifPre.LG.L 1 := by rw [hU.2.1]
  have hc : HEq (cast ht σ₁) σ₁ := cast_heq ht σ₁
  have H := ((PreForm.under_exists_and_expands h₁ h₂ V I D A G U.semi).2.2 U U₀.toUnifPre hU 1 σ f (cast ht σ₁) f₀
    (fun τ hτ z J hJ => by
      obtain rfl : τ = σ₁ := eq_of_heq (hτ.trans hc)
      rw [hσ₁ _ _ z J hJ, Category.id_comp])
    (fun α z J hJ => by rw [hf₀ α _ _ z J hJ, Category.id_comp])).1 hE
  exact psiRel_of_levelOneEq hf₀
    (PsiCompare.levelOneEq_of_expandsAt h₁.globalFns hV U₀.toUnifPre (U₀.expand 1 le_rfl) _ f₀ H)

end GlobalTheory.PsiExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureEqZeroOfVanishingOnTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.PureZero

theorem lt_of_big {g N N' : ℕ} (h : Big g N N') (hg : 1 ≤ g) : N ^ g * g.factorial < N' := by
  have hs := h.sep
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast h.four
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ g := one_le_pow₀ (by norm_num)
  have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
    have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at this
    linarith
  have h3 : (1 / 2 : ℝ) ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
    have : (1 : ℝ) ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g := one_le_mul_of_one_le_of_one_le hg' h1
    nlinarith
  set C := (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)
  have hM : (0 : ℝ) ≤ ((N ^ g * g.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have h5 : (1 : ℝ) ≤ 2 * C * N := by nlinarith
  have : ((N ^ g * g.factorial : ℕ) : ℝ) < N' := by nlinarith
  exact_mod_cast this

theorem sec_eq_zero_of_dim_zero {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = 0)
    {M : LB (Out.baseOver (Sp K) ⊗ P.A).left} (s : M.Sec)
    (hs : ¬ ⊤ ≤ (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left ⁻¹ᵁ Out.nonzeroLocus s) (j : M.ι) :
    s.f j = 0 := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  have : IsDominant e := ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩
  have : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  let z : Sp K ⟶ (Out.baseOver (Sp K) ⊗ P.A).left := (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left
  have hz : z = e ≫ inv (snd (Out.baseOver (Sp K)) P.A).left := by
    rw [IsIso.eq_comp_inv]
    exact congrArg (·.left) (lift_snd (𝟙 _) (1 : Out.baseOver (Sp K) ⟶ P.A))
  have hd : IsDominant z := by rw [hz]; infer_instance
  have : IsReduced (Out.baseOver (Sp K) ⊗ P.A).left :=
    isReduced_of_isOpenImmersion (snd (Out.baseOver (Sp K)) P.A).left
  by_contra hne
  have hb : ((Out.baseOver (Sp K) ⊗ P.A).left.basicOpen (s.f j) : Set (Out.baseOver (Sp K) ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => hne ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
  obtain ⟨y, hy⟩ := hd.denseRange.exists_mem_open (TopologicalSpace.Opens.isOpen _) hb
  refine hs fun y' _ => ?_
  have : y' = y := Subsingleton.elim (α := PrimeSpectrum K) _ _
  subst this
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

theorem twist_eq_zero (h : Out.Laws) (h₂ : Out.Laws2) {K : Type} [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) {g N N' d : ℕ} (hB : Big g N N') (hN' : (N' : K) ≠ 0) (hg : P.g ≤ g) (hd : 1 ≤ d)
    (hd' : d ≤ N ^ g * g.factorial) (c : Out.baseOver (Sp K) ⟶ P.A)
    (s : LB.Sec (Out.twistLB P.A P.L (N * d) c))
    (hs : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ N' = 1 → ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s) :
    ∀ j, s.f j = 0 := by
  rcases Nat.eq_zero_or_pos P.g with h0 | h0
  · exact sec_eq_zero_of_dim_zero P h0 s (hs 1 (one_pow _))
  by_contra hne
  push Not at hne
  have hM1 : 1 ≤ N' := Nat.pos_of_ne_zero fun e => hN' (by rw [e, Nat.cast_zero])
  have hcard := (h.mulN (Sp K) P N' hM1).2.2.2.2 K (𝟙 _) hN'
  have h₄ := card_torsion_zeros_twist_le h h₂ K P N d N' c h0 hB.four hd hN' s hne
  have e : N' ^ (2 * P.g) = N' ^ 2 * N' ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (hs x)), hcard, e] at h₄
  have h₅ := Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)
  have h₆ := lt_of_big hB (h0.trans_le hg)
  have h₇ : N ^ P.g * P.g.factorial ≤ N ^ g * g.factorial :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by have := hB.four; omega) hg) (Nat.factorial_le hg)
  have h₈ := Nat.mul_le_mul h₇ hd'
  nlinarith

theorem pure_eq_zero_of_vanishing_on_torsion :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' d : ℕ) (π : Φ.Pol N), Big g N N' → (N' : k) ≠ 0 → π.PB.g ≤ g → 1 ≤ d → d ≤ N ^ g * g.factorial → ∀ (α : Φ.E.X) (φ : (Φ.H d).Sec), Φ.Pure α φ → (∀ x : Φ.Pt, x ^ N' = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ l, φ.f l = 0) := by
  intro h h₂ k _ _ Φ g N N' d π hB hN' hg hd hd' α φ hφ hx
  have hM1 : 1 ≤ N' := Nat.pos_of_ne_zero fun e => hN' (by rw [e, Nat.cast_zero])
  obtain ⟨s, hs0, hs⟩ := (_root_.GlobalTheory.ZH.TwSec.pure_sec_twist k Φ N d π α (by have := hB.four; omega) hd).1 φ hφ
  refine hs0 (twist_eq_zero h h₂ π.PB hB hN' hg hd hd' _ s fun b hb => ?_)
  have := π.hom
  have hb' : (b ≫ π.β.inv) ^ N' = 1 := by
    rw [← cancel_mono π.β.hom, MonObj.pow_comp, MonObj.one_comp, Category.assoc, π.β.inv_hom_id,
      Category.comp_id, hb]
  obtain ⟨x, hx1, hxq⟩ := (TorsLift.points_lift k Φ.E Φ.G Φ.D N' hM1).2.1 _ hb'
  have e : x ≫ Φ.D.q ≫ π.β.hom = b := by
    rw [← Category.assoc, hxq, Category.assoc, π.β.inv_hom_id, Category.comp_id]
  rw [← e]
  exact fun hh => hx x hx1 ((hs x).2 hh)

end GlobalTheory.PureZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetryHypExtendsSemiAbelianDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymExtendDvr

theorem isGrpPullback_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 _) (by simp)
  have e₁ : x₀ = u ≫ x ≫ e.hom := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have e₂ : y₀ = u ≫ y ≫ e.hom := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _

theorem hypS_of_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∀ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → HypS G L.L := by
  intro ext V _ _ _ A G _ _ hG H gen hgen L hL
  have := hG.smooth
  have := hG.geomConnected
  have hc : IsCommMonObj ((Over.pullback (jK V)).obj G) := Functor.isCommMonObj_obj
  have hA : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have H' : HypS ((Over.pullback (jK V)).obj G) (A.L.pull gen.hom.left) :=
    GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A _ (𝟙 _) gen.hom.left A.L _ A.isLB hA (isGrpPullback_of_iso gen)
      ((GlobalTheory.PrimNorm.lbIso_iff A.isLB _ _ _ _).2 rfl) H
  have : IsOpenImmersion (jK V) := GlobalTheory.DvrModel.isOpenImmersion_generic (K := FractionRing V) (f := 𝟙 _)
    (j := jK V) (fK := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
  refine GlobalTheory.SymExtend.hypS_extend (GlobalTheory.IsNormalScheme.pred _) (isGrpPullback_pullback G (jK V)) ?_ _ L hA hL.symm H'
  intro α hα
  obtain ⟨F, ⟨hF, eF⟩, u⟩ := ext V (FractionRing V) G G hG hG α hα
  have c : ∀ F : G ⟶ G, ((Over.pullback (jK V)).map F).left ≫ pullback.fst G.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ F.left := fun F => pullback.lift_fst _ _ _
  refine ⟨F, ⟨hF, ?_⟩, fun F' h' => u F' ⟨h'.1, ?_⟩⟩
  · rw [← eF]
    exact (c F).symm
  · refine Over.OverMorphism.ext (pullback.hom_ext ((c F').trans h'.2) ?_)
    exact (Over.w ((Over.pullback (jK V)).map F')).trans (Over.w α).symm

end GlobalTheory.SymExtendDvr
end
end

