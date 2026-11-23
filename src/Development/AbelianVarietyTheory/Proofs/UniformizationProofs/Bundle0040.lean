module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullLam
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiLift

section Gen
variable {X Y Y₀ : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_val_lift (hL : L.IsLB) (f : Y₀ ⟶ Y) [IsClosedImmersion f] [Surjective f] [IsAffine Y]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t₀ : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε)) (ht₀ : t₀.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₀) (z : Z) (J), Good L z J → val t (r ≫ f) z J = val t₀ r z J := by
  have le : ∀ j : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull f).U j ≤ LB.wchart L (fun k => f ≫ φ k) (j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  let c : LB.Gen ((LB.LinComb L φ ε).pull f) := ⟨fun j => res (le j) (t₀.s (j PUnit.unit))⟩
  have hc : c.IsGen := isGen_of_gm (M := LB.LinComb L φ ε) c fun y j j' hj hj' => by
    refine (gm_res _ y _ hj _).trans ((gen_trans ht₀ (𝟙 Y₀) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) ?_ (gm_res _ y _ hj' _).symm))
    unfold trF
    symm
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_linComb L φ ε (𝟙 Y₀ ≫ f) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
    simp only [Category.assoc]
  obtain ⟨t, ht, e⟩ := GenLift.exists_genPull_eq f (LB.isLB_linComb hL φ ε) c hc
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  rw [val_of t (r ≫ f) z J (fun k => J (r ≫ f ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => f ≫ φ k) r
  have hm' : r z ∈ ((LB.LinComb L φ ε).pull f).U (fun _ k => J (r ≫ f ≫ φ k)) :=
    mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k)
  have e' := congrArg (fun q : LB.Gen ((LB.LinComb L φ ε).pull f) => gm r z _ (q.s fun _ k => J (r ≫ f ≫ φ k))) e
  refine Eq.trans ?_ (e'.trans (gm_res r z _ hm' _))
  exact ((gm_res r z _ hm' _).trans (gm_pull r f z _ (mem_pull.1 hm') _)).symm

theorem unit_eq_one {u : Γ(Y, ⊤)ˣ}
    (h : ∀ y : Y, ∃ (W : Y.Opens) (hy : y ∈ W), gm W.ι (⟨y, hy⟩ : W.toScheme) ⊤ u = 1) : u = 1 :=
  unit_ext fun y _ => by
    obtain ⟨W, hy, e⟩ := h y
    exact gm_inj W.ι (⟨y, hy⟩ : W.toScheme) (U := ⊤) (U' := ⊤) trivial trivial (e.trans (map_one _).symm)

end Gen

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

def lam {Y : Over S} (a x : Y ⟶ G) : Fin 4 → (Y.left ⟶ G.left) := ![(a * x).left, a.left, x.left, (1 : Y ⟶ G).left]

theorem comp_lam {Y Z : Over S} (r : Z ⟶ Y) (a x : Y ⟶ G) (k : Fin 4) : r.left ≫ lam a x k = lam (r ≫ a) (r ≫ x) k := by
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul r a x)
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := G) r)

theorem prod_lam {Y : Over S} (a x : Y ⟶ G) {U : Type} [CommGroup U] (h : (Y.left ⟶ G.left) → U) :
    ∏ k, h (lam a x k) ^ Oε k = h (a * x).left * (h a.left)⁻¹ * (h x.left)⁻¹ * h (1 : Y ⟶ G).left := by
  simp [Fin.prod_univ_four, lam, Oε]

theorem exists_pull_lam {Y Z : Over S} (r : Z ⟶ Y) {a x : Y ⟶ G} {a' x' : Z ⟶ G} (ha : r ≫ a = a') (hx : r ≫ x = x')
    (s : LB.Gen (LB.LinComb L.L (lam a x) Oε)) (hs : s.IsGen) :
    ∃ s' : LB.Gen (LB.LinComb L.L (lam a' x') Oε), s'.IsGen ∧
      ∀ (W : Scheme.{0}) (q : W ⟶ Z.left) (z : W) (J), Good L.L z J → val s' q z J = val s (q ≫ r.left) z J := by
  subst ha hx
  obtain ⟨s', hs', e⟩ := exists_gen L.isLB (φ' := lam (r ≫ a) (r ≫ x)) (ε' := Oε)
    (fun U _ h => by simp only [comp_lam]) (LB.pullGen L.L _ _ s r.left) (DVR.pullGen_isGen _ _ _ _ hs _)
  exact ⟨s', hs', fun W q z J hJ => (e W q z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_defect {Y : Over S} (a b x : Y ⟶ G) {φ₁ φ₂ φ₃ : Fin 4 → (Y.left ⟶ G.left)}
    (h₁ : FormEq φ₁ Oε (lam (a * b) x) Oε) (h₂ : FormEq φ₂ Oε (lam a x) Oε) (h₃ : FormEq φ₃ Oε (lam b x) Oε)
    (s₁ : LB.Gen (LB.LinComb L.L φ₁ Oε)) (s₂ : LB.Gen (LB.LinComb L.L φ₂ Oε)) (s₃ : LB.Gen (LB.LinComb L.L φ₃ Oε))
    (g₁ : s₁.IsGen) (g₂ : s₂.IsGen) (g₃ : s₃.IsGen) :
    ∃ f : Γ(Y.left, ⊤)ˣ, ∀ (Z : Over S) (r : Z ⟶ Y) (z : Z.left) (J), Good L.L z J →
      val s₁ r.left z J = gm r.left z ⊤ f * (cubV c z J (r ≫ a) (r ≫ b) (r ≫ x) * val s₂ r.left z J * val s₃ r.left z J) := by
  obtain ⟨f, hf⟩ := TorusCoord.exists_ratio L.isLB (fun U _ h => by
      refine Eq.trans ?_ (DVR.prod_sum₂ (K := thK ⊕ Fin 4) (K' := Fin 4) (U := U) _
        (DVR.prod_sum₂ (K := thK) (K' := Fin 4) (U := U) _ (prod_cub a b x h) ((h₂ U h).trans (prod_lam a x h)))
        ((h₃ U h).trans (prod_lam b x h))).symm
      rw [h₁ U h, prod_lam]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) s₁ g₁
    (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b x)).left) s₂) s₃)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) g₂) g₃)
  refine ⟨f, fun Z r z J hJ => (hf _ r.left z J hJ).trans (congrArg _ ?_)⟩
  exact (val_mul hJ _ _ _).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_cub c r hJ _ _ _))))

omit [GrpObj G] [IsCommMonObj G] in
theorem formEq_refl {Y : Over S} (φ : Fin 4 → (Y.left ⟶ G.left)) : FormEq φ Oε φ Oε := fun _ _ _ => rfl

theorem formEq_symm {Y : Over S} (a x : Y ⟶ G) : FormEq (lam a x) Oε (lam x a) Oε := fun U _ h => by
  rw [prod_lam, prod_lam, mul_comm x a, mul_right_comm (h _) (h a.left)⁻¹]

variable {H Y : Over S} [GrpObj H] {i : H ⟶ G} [IsMonHom i] {x : Y ⟶ G}

theorem exists_defect₁ (s : LB.Gen (LB.LinComb L.L (lam (fst H Y ≫ i) (snd H Y ≫ x)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ H ⊗ Y).left, ⊤)ˣ, ∀ (Z : Over S) (t t' : Z ⟶ H) (y : Z ⟶ Y) (z : Z.left) (J), Good L.L z J →
      val s (lift (t * t') y).left z J = gm (lift t (lift t' y)).left z ⊤ f *
        (cubV c z J (t ≫ i) (t' ≫ i) (y ≫ x) * val s (lift t y).left z J * val s (lift t' y).left z J) := by
  let p : H ⊗ H ⊗ Y ⟶ H := fst _ _
  let p' : H ⊗ H ⊗ Y ⟶ H := snd _ _ ≫ fst _ _
  let q : H ⊗ H ⊗ Y ⟶ Y := snd _ _ ≫ snd _ _
  obtain ⟨s₁, g₁, e₁⟩ := exists_pull_lam (lift (p * p') q) (a' := p ≫ i * p' ≫ i) (x' := q ≫ x)
    (by rw [lift_fst_assoc, MonObj.mul_comp]) (lift_snd_assoc _ _ _) s hs
  obtain ⟨s₂, g₂, e₂⟩ := exists_pull_lam (lift p q) (lift_fst_assoc _ _ _) (lift_snd_assoc _ _ _) s hs
  obtain ⟨s₃, g₃, e₃⟩ := exists_pull_lam (lift p' q) (lift_fst_assoc _ _ _) (lift_snd_assoc _ _ _) s hs
  obtain ⟨f, hf⟩ := exists_defect c _ _ _ (formEq_refl _) (formEq_refl _) (formEq_refl _) s₁ s₂ s₃ g₁ g₂ g₃
  refine ⟨f, fun Z t t' y z J hJ => ?_⟩
  have e := hf Z (lift t (lift t' y)) z J hJ
  rw [e₁ _ _ z J hJ, e₂ _ _ z J hJ, e₃ _ _ z J hJ] at e
  simpa only [← Over.comp_left, comp_lift, MonObj.comp_mul, p, p', q, lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, Category.assoc] using e


omit [IsMonHom i] [GrpObj H] in
theorem exists_defect₂ (s : LB.Gen (LB.LinComb L.L (lam (fst H G ≫ i) (snd H G)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (Z : Over S) (t : Z ⟶ H) (y : Z ⟶ G ⊗ G) (z : Z.left) (J), Good L.L z J →
      val s (lift t (y ≫ fst _ _ * y ≫ snd _ _)).left z J = gm (lift t y).left z ⊤ f *
        (cubV c z J (t ≫ i) (y ≫ fst _ _) (y ≫ snd _ _) * val s (lift t (y ≫ fst _ _)).left z J *
          val s (lift t (y ≫ snd _ _)).left z J) := by
  let p : H ⊗ G ⊗ G ⟶ H := fst _ _
  let q : H ⊗ G ⊗ G ⟶ G := snd _ _ ≫ fst _ _
  let q' : H ⊗ G ⊗ G ⟶ G := snd _ _ ≫ snd _ _
  obtain ⟨s₁, g₁, e₁⟩ := exists_pull_lam (lift p (q * q')) (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨s₂, g₂, e₂⟩ := exists_pull_lam (lift p q) (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨s₃, g₃, e₃⟩ := exists_pull_lam (lift p q') (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨f, hf⟩ := exists_defect c _ _ _ (formEq_symm _ _) (formEq_symm _ _) (formEq_symm _ _) s₁ s₂ s₃ g₁ g₂ g₃
  refine ⟨f, fun Z t y z J hJ => ?_⟩
  have e := hf Z (lift t y) z J hJ
  rw [e₁ _ _ z J hJ, e₂ _ _ z J hJ, e₃ _ _ z J hJ, (isCub_cubV c hJ).s12, (isCub_cubV c hJ).s01] at e
  simpa only [← Over.comp_left, comp_lift, MonObj.comp_mul, p, q, q', lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, Category.assoc] using e

end GlobalTheory.UU.BiLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionOfIsPullDeg
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_oAct_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] (ιD : D.OAct O), ∃ (_ : Module O D'.X) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) := by
  intro hG R R' _ _ _ _ φ D D' hD O _ _ _ ιD
  have gp := pull_grp hD
  obtain ⟨o', ho'⟩ := polOActPull _ _ _ D.P D'.P _ gp (LBIso.symm ⟨hD.w, hD.w_gen⟩) O ιD.onB
  letI inst : Module O D'.X := hD.xe.module O
  have hs : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y := fun a y =>
    hD.xe.apply_symm_apply _
  have he : ∀ a, o'.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a) := fun a => by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have := ho' a
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at this ⊢
      exact this
    · exact (Over.w (o'.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))).symm
  refine ⟨inst, ⟨o', fun a y => ?_, fun a => ?_⟩, hs, he⟩
  · refine Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hs, ιD.c_lin, Over.comp_left, Over.comp_left, Category.assoc, ho', ← Category.assoc,
      ← Category.assoc (D'.c y).left, hD.c_pr]
  · exact tauBal_of_isPullDeg hG R R' φ D D' hD _ _ _ _ (ιD.onB.hom a) (ιD.onB.hom (star a)) (ιD.onB.rosati a)
      (he a) (he (star a)) _ _ _ _ (hs a) (hs (star a)) (ιD.c_lin a) (ιD.c_lin (star a)) (ιD.tau_bal a)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNonzeroLocusEqOfIsAffineOpenOfFactorial
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty → ∃ (L : LB X) (s : LB.Sec L), L.IsLB ∧ nonzeroLocus s = U :=
  fun X _ _ _ hX U hU hne => _root_.GlobalTheory.AffineComplement.exists_nonzeroLocus_eq X U hU hne hX

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfGenericFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_of_generic_fibre : ∀ (V : Type) [CommRing V] [IsDomain V] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y : Over (Spec (CommRingCat.of V))) [QuasiCompact Y.hom] [IsSeparated Y.hom] (K : Type) [Fintype K] (φ : K → (Y.left ⟶ Z)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L (fun k => (snd (TK V) Y).left ≫ φ k) ε)), ∃ (r : V) (_ : r ≠ 0) (σ : LB.Sec (LB.LinComb L φ ε)), ∀ (T : Scheme.{0}) (ρ : T ⟶ (TK V ⊗ Y).left) (z : T) (J), Good L z J → sval σ (ρ ≫ (snd (TK V) Y).left) z J = gs ρ z ⊤ (scal (TK V ⊗ Y).hom r) * sval s ρ z J := by
  intro V _ _ Z L hL Y _ _ K _ φ ε s
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have H : IsPullback (snd (TK V) Y).left (fst (TK V) Y).left Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :=
    (IsPullback.of_hasPullback (TK V).hom Y.hom).flip
  obtain ⟨t, ht, σ, hσ⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors V) H hL φ ε s
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, fun T ρ z J hJ => ?_⟩
  rw [sval_of σ (ρ ≫ (snd (TK V) Y).left) z J (fun k => J (ρ ≫ (snd (TK V) Y).left ≫ φ k))
    (fun k => by rw [Category.assoc])]
  refine (hσ T ρ z _ (hJ.mem (fun k => (snd (TK V) Y).left ≫ φ k) ρ)).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [Over.w (snd (TK V) Y)]
  exact (gs_pull ρ (TK V ⊗ Y).hom z ⊤ trivial _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitRatio
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiTrivUniq

variable {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem exists_unit_ratio (hM : M.IsLB) {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ a * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm

theorem gen_eq_of_val (hM : M.IsLB) {t t' : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y J, Good M y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  refine unit_ext (V := LB.wchart M φ j) fun y hy => ?_
  obtain ⟨I, hI⟩ := exists_good_pt hM y
  exact (gen_trans ht (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans
    (gen_trans ht' (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).symm)

end GlobalTheory.UU.BiTrivUniq

namespace GlobalTheory.UU
open BiTrivUniq

theorem biTriv_unique : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    [ConnectedSpace G.left] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus S X ⟶ G), IsMonHom i →
    ∀ s s' : BiTriv c i, s = s' := by
  intro S X _ G _ _ _ L c i _ s s'
  obtain ⟨ρ, hρ⟩ := exists_unit_ratio L.isLB s.gen s'.gen
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X G ρ fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom ρ =
        Units.map (lift t y).left.appTop.hom.toMonoidHom ρ * Units.map (lift t' y).left.appTop.hom.toMonoidHom ρ := by
      refine unit_ext fun z _ => ?_
      obtain ⟨J, hJ⟩ := exists_good_pt L.isLB z
      have a := s.law1 Z t t' y z J hJ
      rw [hρ _ _ z J hJ, hρ _ _ z J hJ, hρ _ _ z J hJ, s'.law1 Z t t' y z J hJ] at a
      rw [map_mul, ← gm_top, ← gm_top, ← gm_top]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      simp only [ofMul_mul] at a' ⊢
      linear_combination (norm := abel) a'
    exact congrArg Units.val e
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x : Z ⟶ G) (z : Z.left),
      gm (lift t x).left z ⊤ ρ = gm (𝟙 Z.left) z ⊤ (chV t χ) := fun Z t x z => by
    rw [gm_top]
    congr 1
    refine Units.ext ?_
    rw [chV_val]
    show (lift t x).left.appTop.hom ρ.val = _
    rw [hχ, Rosenlicht.over_appTop_comp, lift_fst]
  have hs : s.s = s'.s := gen_eq_of_val L.isLB s.gen s'.gen fun y J hJ => by
    have a := hρ _ (lift (fst (splitTorus S X) G) (1 : _ ⟶ G)).left y J hJ
    rw [s.val_one_right hJ, s'.val_one_right hJ, key, _root_.mul_one, ← key _ _ (snd _ _), lift_fst_snd,
      Over.id_left] at a
    rw [hρ _ _ y J hJ, ← a, _root_.one_mul]
  obtain ⟨s, _, _, _⟩ := s
  obtain ⟨s', _, _, _⟩ := s'
  obtain rfl : s = s' := hs
  rfl

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinFlatChartOfOpenImmersion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.Unif

theorem finFlatChart_of_openImmersion {X Y Z S B : Scheme.{0}} (f : X ⟶ B) (s : S ⟶ B)
    (j : Y ⟶ X) [IsOpenImmersion j] (i : Z ⟶ S) [IsOpenImmersion i] (p : Y ⟶ Z)
    [IsFinite p] [Flat p] [Surjective p] [Nonempty Z] (h : p ≫ i ≫ s = j ≫ f) :
    ∃ (W : X.Opens) (V : S.Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧
      IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ s = W.ι ≫ f := by
  obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary Z)
  refine ⟨j.opensRange, i.opensRange, j.isoOpensRange.inv ≫ p ≫ i.isoOpensRange.hom,
    ⟨j y, y, rfl⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, h]
  rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι_assoc]

theorem exists_finFlat_away (R A : Type) [CommRing R] [CommRing A] [IsDomain R]
    [IsNoetherianRing R] (φ : R →+* A) (hφ : φ.Finite) (hi : Function.Injective φ) :
    ∃ (Y Z : Scheme.{0}) (j : Y ⟶ Spec (CommRingCat.of A)) (i : Z ⟶ Spec (CommRingCat.of R))
      (p : Y ⟶ Z), IsOpenImmersion j ∧ IsOpenImmersion i ∧ IsFinite p ∧ Flat p ∧ Surjective p ∧
      Nonempty Z ∧ p ≫ i = j ≫ Spec.map (CommRingCat.ofHom φ) := by
  algebraize [φ]
  have : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) A) (FractionRing R)
  have hfree' : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] A) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) A)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.Away r) A)
  have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [IsFinite.SpecMap_iff]; exact hφ
  have h2 : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    ⟨hφ.to_isIntegral.comap_surjective hi⟩
  have h3 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    inferInstance
  have hd : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (Submonoid.powers_le.mpr hr)
  refine ⟨_, _, _, _, _, MorphismProperty.of_isPullback hpb h3, h3,
    MorphismProperty.of_isPullback hpb.flip h1, ?_, MorphismProperty.of_isPullback hpb.flip h2,
    inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away r))), hpb.w⟩
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff (R := Localization.Away r)
    (S := Localization.Away r ⊗[R] A)).mpr inferInstance

theorem exists_finite_flat_chart : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f], ∃ (g : ℕ) (W : X.Opens) (V : (Spec (CommRingCat.of (MvPolynomial (Fin g) K))).Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧ IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) = W.ι ≫ f := by
  intro K _ X _ f _
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  have hft : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  have hft' : ψ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  letI : Algebra K Γ(X, U) := ψ.hom.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hft'
  obtain ⟨g, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K Γ(X, U)
  obtain ⟨Y, Z, j, i, p, _, _, _, _, _, _, h⟩ :=
    exists_finFlat_away _ _ φ.toRingHom hfin hinj
  refine ⟨g, finFlatChart_of_openImmersion f _ (j ≫ hU.fromSpec) i p ?_⟩
  rw [reassoc_of% h, Category.assoc, ← hψ, ← Spec.map_comp]
  congr 2
  ext x
  exact φ.commutes x

end GlobalTheory.Unif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_eq_card_kernel_points_of_etale :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ φ : B ⟶ B, ∀ [IsFinite φ.left] [Etale φ.left], ∀ x : B.left, φ.left.finrank x = Nat.card {y : 𝟙_ _ ⟶ B // y ≫ φ = 1} := by
  intro K _ _ B _ _ hB φ _ _ x
  have := hB.geomConnected
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  let o : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B := 1
  let t : Spec (CommRingCat.of K) ⟶ B.left := o.left
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have ht : t ≫ B.hom = 𝟙 _ := Over.w o
  rw [(Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace x (t z),
    ← (GlobalTheory.FinEt.card_points_eq_finrank φ.left t z).2]
  refine Nat.card_congr
    { toFun := fun y ↦ ⟨Over.homMk y.1 ?_, Over.OverMorphism.ext y.2⟩
      invFun := fun y ↦ ⟨y.1.left, congrArg CommaMorphism.left y.2⟩
      left_inv := fun y ↦ rfl
      right_inv := fun y ↦ Subtype.ext (Over.OverMorphism.ext rfl) }
  change y.1 ≫ B.hom = 𝟙 _
  rw [← Over.w φ, ← Category.assoc, y.2, ht]

end GlobalTheory
end

