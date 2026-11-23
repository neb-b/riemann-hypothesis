module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsPullF
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteTorsionExt

theorem eq_of_isPullF {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T}
    {g₁ g₂ : GtPtF D F} (h₁ : GtPt.IsPullF F x g g₁) (h₂ : GtPt.IsPullF F x g g₂) : g₁ = g₂ := by
  obtain ⟨b₁, s₁, i₁, z₁, m₁⟩ := g₁
  obtain ⟨b₂, s₂, i₂, z₂, m₂⟩ := g₂
  obtain rfl : b₁ = b₂ := Over.OverMorphism.ext (h₁.1.trans h₂.1.symm)
  obtain rfl : s₁ = s₂ := funext fun χ => GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (i₁ χ) (i₂ χ)
    (DVR.corr_trans D.P.isLB (h₁.2 χ) (DVR.corr_symm (h₂.2 χ)))
  rfl

theorem main : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → I' ≠ ⊤ → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (x₁ : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ G') (gp : GtPt D'.toPre (𝟙_ (Over (Spec (CommRingCat.of R'))))), x₁ ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R' I' e) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G'), xe ≫ fstG I' e G' = toUnit _ ≫ x₁ ∧ xe ≫ (U'.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (LB.pullGen D'.toPre.P.L _ _ ((U'.gt e).t χ) xe.left) (LB.pullGen D'.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R' I' e))).left)) → ∀ (p : QkPt D.toPre F k) (g' : GtPtF D'.toPre F) (x : TFK (R := R) F ⟶ A.A), p.y = 0 → IsPullGtF φ hD F p.g g' → GtPt.IsPullF F (toUnit (TF (R := R') F)).left gp g' → x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R') F) ≫ x₁).left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) → QkToAkU U.toUnifPre F k p x := by
  intro hL R R' _ _ _ _ _ I I' hR hR' φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU hI' F _ _ _ hF k hk x₁ gp hx₁ hxe
    p g' x hp hg hg' hx
  obtain ⟨p', hp', hpg'⟩ := (GlobalTheory.T.torsionPoint_qk_alt hL.globalFns R' I' hR' hI' D' A' G' U'.toUnifPre k x₁ gp hx₁ hxe).2 F
  have e : p'.g = g' := eq_of_isPullF hpg' hg'
  let y : TFK (R := R') F ⟶ (Over.pullback (jK R')).obj G' :=
    Over.homMk (pullback.lift (toUnit (TF (R := R') F) ≫ x₁).left (jFK (R := R') F)
      (Over.w (toUnit (TF (R := R') F) ≫ x₁))) (pullback.lift_snd _ _ _)
  have hy : (y ≫ U'.gen.hom).left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') =
      (toUnit (TF (R := R') F) ≫ x₁).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine GlobalTheory.T.qkToAk_descends_along_baseChange hL.globalFns hL.secBaseChange R R' I I' hR hR' φ D A G U G' bc hbc A' D' hD U' hU F hF k hk
    p x p' (y ≫ U'.gen.hom) (by rw [hp, hp', map_zero]) (e ▸ hg) ?_
    (GlobalTheory.T.qkToAkU_of_integral_torsion_point hL R' I' hR' hI' D' A' G' U' k hk x₁ gp hx₁ hxe F p' _ hp' hpg' hy)
  rw [hx, ← hy]
  simp only [Category.assoc]

end GlobalTheory.FiniteTorsionExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Balanced
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem stalkMap_inj {Y Z : Scheme.{0}} (r : Z ⟶ Y) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)) := inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (r z)) (B := Z.presheaf.stalk z)
  exact FaithfulSMul.algebraMap_injective _ _

theorem surjective_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Surjective (spMap β) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have := surjective_spMap β
  exact Flat.epi_of_flat_of_surjective _

theorem val_descend {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (r : Z ⟶ Y) [Flat r] [Surjective r]
    (h : ∀ z J, Good L z J → val t r z J = val t' r z J) (y : Y) (J) (hJ : Good L y J) :
    val t (𝟙 Y) y J = val t' (𝟙 Y) y J := by
  have : Epi r := Flat.epi_of_flat_of_surjective r
  obtain ⟨z, rfl⟩ := r.surjective y
  obtain ⟨J', hJ', e⟩ := exists_good L hL z (fun ψ : Y ⟶ X => r ≫ ψ) J
    (fun a b e => congrArg J ((cancel_epi r).1 e)) (fun ψ => hJ ψ)
  have := h z J' hJ'
  rw [val_of t r z J' (fun k => J (𝟙 Y ≫ φ k)) (fun k => by rw [Category.id_comp]; exact e _),
    val_of t' r z J' (fun k => J (𝟙 Y ≫ φ' k)) (fun k => by rw [Category.id_comp]; exact e _)] at this
  have h₁ := hJ.mem φ (𝟙 Y)
  have h₂ := hJ.mem φ' (𝟙 Y)
  have k : ∀ (U : Y.Opens) (_ : r z ∈ U) (a : Γ(Y, U)ˣ),
      (gm r z U a).val = (r.stalkMap z).hom (gm (𝟙 Y) (r z) U a).val := fun U hU a => by
    rw [gm_val r z U hU, gm_val _ (r z) U hU]
    exact (Scheme.Hom.germ_stalkMap_apply r U z hU _).symm
  exact Units.ext (stalkMap_inj r z ((k _ h₁ _).symm.trans ((congrArg Units.val this).trans (k _ h₂ _))))

section Ext
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem gtExt_injective (D : DegPre R) : Function.Injective (gtExt D f hf) := fun g g' h => by
  have := epi_spMap f
  have := surjective_spMap f
  have : Flat (spMap f) := inferInstance
  refine gt_ext_val (Over.OverMorphism.ext ((cancel_epi (spMap f)).1 ?_)) fun χ y J hJ => ?_
  · exact ((eq_gtExt_iff f hf g _).1 rfl).1.symm.trans (((eq_gtExt_iff f hf g' _).1 h).1)
  · refine val_descend D.P.isLB (g.s χ) (g'.s χ) (spMap f) (fun z J hJ => ?_) y J hJ
    exact (gtExt_val f hf g χ hJ).symm.trans ((congrArg (fun q => charVal q χ z J) h).trans (gtExt_val f hf g' χ hJ))

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)

theorem act_unique {g g₁ g₂ : GtPtF D.toPre F} (h₁ : E.Act g g₁) (h₂ : E.Act g g₂) : g₁ = g₂ :=
  gt_ext_val (h₁.1.trans h₂.1.symm) fun χ y J hJ => (h₁.2 χ y J hJ).trans (h₂.2 χ y J hJ).symm

theorem act_gtExt {g g' : GtPtF D.toPre F} (h : E.Act g g') : E.Act (gtExt _ f hf g) (gtExt _ f hf g') := by
  refine ⟨by rw [gtExt_b, gtExt_b, h.1, Category.assoc], fun χ z J hJ => ?_⟩
  have c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (g'.s χ)
      (LB.mulGen D.toPre.P.L _ _ _ _ (g.s (E.h χ)) (LB.pullGen D.toPre.P.L _ _ (E.u χ) g.b.left)) :=
    corr_of_val D.toPre.P.isLB fun y J hJ => (h.2 χ y J hJ).trans (Eq.trans (congrArg₂ (· * ·) rfl (by
      rw [val_pull hJ, Category.id_comp])) (val_mul hJ _ _ _).symm)
  refine (gtExt_val f hf g' χ hJ).trans ((val_corr hJ c _).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (gtExt_val f hf g _ hJ).symm ((val_pull hJ _ _ _).trans ?_))))
  rw [gtExt_b]; rfl

end Ext

section Adjoint

theorem adj_add {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (a a' : G ⟶ G) (h : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L.L) (cubeLB G ![fst G G, snd G G ≫ a'] L.L)) (m : ℕ) :
    LBIso (cubeLB G ![fst G G ≫ (a * 𝟙 G ^ m), snd G G] L.L) (cubeLB G ![fst G G, snd G G ≫ (a' * 𝟙 G ^ m)] L.L) := by
  have hc := PrimNorm.diff₃_ptCls (T := G ⊗ G) L.isLB ⟨c.t, c.isGen⟩
  have p : ∀ (x y : G ⊗ G ⟶ G) (m : ℕ), PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) (x ^ m) y =
      PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) x y ^ m := fun x y m =>
    map_pow (MonoidHom.mk' (fun x => PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) x y)
      fun u v => PrimNorm.diff₂_mul_left hc u v y) x m
  have q : ∀ (x : G ⊗ G ⟶ G) (b : G ⟶ G), x ≫ (b * 𝟙 G ^ m) = (x ≫ b) * x ^ m := fun x b =>
    (map_mul (preHom x) _ _).trans (congrArg _ ((map_pow (preHom x) _ _).trans
      (congrArg (· ^ m) (Category.comp_id x))))
  refine (PrimNorm.lbIso_iff L.isLB _ _ _ _).2 ((PrimNorm.prod_square_id _ _ (PrimNorm.cls L.L)).trans
    (Eq.trans ?_ (PrimNorm.prod_square_id _ _ (PrimNorm.cls L.L)).symm))
  show PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) _ _ = PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) _ _
  rw [q, q, PrimNorm.diff₂_mul_left hc, PrimNorm.diff₂_mul_right hc, PrimNorm.diff₂_ptCls_adj L.isLB h, p,
    PrimNorm.diff₂_comm (fst G G) (snd G G ^ m), p, PrimNorm.diff₂_comm (snd G G)]

theorem adj_pull {B B' : Scheme.{0}} (f : B' ⟶ B) (G : Over B) [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {L' : LB ((Over.pullback f).obj G).left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hb : LBIso L' (L.pull (pullback.fst G.hom f))) (a a' : G ⟶ G)
    (ha : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a'] L)) :
    LBIso (cubeLB ((Over.pullback f).obj G) ![fst _ _ ≫ (Over.pullback f).map a, snd _ _] L')
      (cubeLB ((Over.pullback f).obj G) ![fst _ _, snd _ _ ≫ (Over.pullback f).map a'] L') := by
  have h := isGrpPullback_pullback G f
  let G' := (Over.pullback f).obj G
  let φ : G'.left ⟶ G.left := pullback.fst G.hom f
  have pa : ∀ (w : G ⟶ G) {T : Over B'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ (Over.pullback f).map w) = pushPt h.1.w x ≫ w := fun w T x =>
    Over.OverMorphism.ext (by
      have hw : ((Over.pullback f).map w).left ≫ φ = φ ≫ w.left := pullback.lift_fst _ _ _
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have hB : (L.pull φ).IsLB := pull_isLB hL φ
  have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ (Over.pullback f).map a, snd G' G'] (L.pull φ))
      (cubeLB G' ![fst G' G', snd G' G' ≫ (Over.pullback f).map a'] (L.pull φ)) := by
    let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
    refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) ha
    · fin_cases i
      · exact (pa _ _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
      (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

end Adjoint

theorem exists_add_injective {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X) :
    ∃ m : ℕ, (Function.Injective fun x => h x + m • x) ∧ Function.Injective fun x => h' x + m • x := by
  have key : ∀ h : X →+ X, {m : ℕ | ¬ Function.Injective fun x => h x + m • x}.Finite := fun h => by
    let f : Module.End ℤ X := h.toIntLinearMap
    have fin : (f.charpoly.rootSet ℤ).Finite := Polynomial.rootSet_finite _ _
    refine Set.Finite.subset (fin.preimage (f := fun m : ℕ => -(m : ℤ)) (fun a _ b _ e => by simpa using e)) ?_
    intro m hm
    simp only [Function.Injective, Set.mem_setOf_eq, not_forall] at hm
    obtain ⟨x, y, e, hxy⟩ := hm
    have ev : f.HasEigenvector (-(m : ℤ)) (x - y) := by
      refine ⟨Module.End.mem_eigenspace_iff.2 ?_, sub_ne_zero.2 hxy⟩
      show h (x - y) = _
      rw [map_sub, neg_smul, natCast_zsmul, smul_sub]
      linear_combination (norm := abel) e
    have := Module.End.aeval_apply_of_hasEigenvector (p := f.charpoly) ev
    rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at this
    refine (Polynomial.mem_rootSet).2 ⟨f.charpoly_monic.ne_zero, ?_⟩
    simpa [sub_ne_zero.2 hxy] using this.symm
  obtain ⟨m, hm⟩ := ((key h).union (key h')).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hm
  exact ⟨m, hm⟩

end GlobalTheory.Balanced
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinAffineCover
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.PrimNorm
noncomputable section
namespace GlobalTheory.PrimVan

variable {X Y Y' : Scheme.{0}}

theorem gm_tw_one (A B : LB Y) (y : Y) (p q : A.ι × B.ι) (hp : y ∈ A.U p.1 ⊓ B.U p.2)
    (hq : y ∈ A.U q.1 ⊓ B.U q.2) :
    gm (𝟙 Y) y (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ((tw A B 1).g p q) =
      gm (𝟙 Y) y _ (A.g p.1 q.1) * gm (𝟙 Y) y _ (B.g p.2 q.2) := by
  refine (gm_div (pw B (-1)) A (𝟙 Y) y p q ⟨hp, hq⟩).trans ?_
  congr 1
  change (gm (𝟙 Y) y (B.U p.2 ⊓ B.U q.2) (B.g p.2 q.2 ^ (-1 : ℤ)))⁻¹ = _
  rw [zpow_neg_one, map_inv, inv_inv]

def chartTw (M : LB X) (p q : Y ⟶ X) :
    ChartPull (tw (M.pull p) (M.pull q) 1) (LB.LinComb M (K := Fin 2) ![p, q] ![1, 1]) (𝟙 Y) :=
  have le : ∀ a : (M.pull p).ι × (M.pull q).ι, (M.pull p).U a.1 ⊓ (M.pull q).U a.2 ≤
      LB.wchart M (K := Fin 2) ![p, q] ![a.1 PUnit.unit, a.2 PUnit.unit] := fun a y hy =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [mem_pull.1 hy.1, mem_pull.1 hy.2]
  { idx := fun a => ![a.1 PUnit.unit, a.2 PUnit.unit]
    le := le
    g := fun y a b ha hb => by
      refine (gm_tw_one (M.pull p) (M.pull q) y a b ha hb).trans (Eq.trans ?_
        (gm_linComb M _ _ (𝟙 Y) y _ _ (le a ha) (le b hb)).symm)
      rw [gm_pull_g M p (𝟙 Y) y _ _ ha.1 hb.1, gm_pull_g M q (𝟙 Y) y _ _ ha.2 hb.2, Fin.prod_univ_two]
      exact congrArg₂ (· * ·) (zpow_one _).symm (zpow_one _).symm }

def chartTwTriv (N : LB Y) (q : Y ⟶ Y') :
    ChartPull (tw N ((Inh.trivLB Y').pull q) 1) N (𝟙 Y) where
  idx a := a.1
  le _ _ hy := hy.1
  g y a b ha hb := by
    refine (gm_tw_one N ((Inh.trivLB Y').pull q) y a b ha hb).trans ?_
    rw [Inh.linComb_triv_g, map_one, _root_.mul_one]

def chartInv (M : LB X) :
    ChartPull (pw M (-1)) (LB.LinComb M (K := PUnit) (fun _ => 𝟙 X) fun _ => -1) (𝟙 X) :=
  have le : ∀ i : M.ι, M.U i ≤ LB.wchart M (K := PUnit) (fun _ => 𝟙 X) fun _ => i := fun _ _ hy =>
    Set.mem_iInter.2 fun _ => hy
  { idx := fun i _ => i
    le := le
    g := fun y i j hi hj => by
      refine Eq.trans ?_ (gm_linComb M _ _ (𝟙 X) y _ _ (le i hi) (le j hj)).symm
      rw [Fintype.prod_unique, Category.id_comp]
      exact map_zpow _ _ _ }

theorem nontrivial_sec_of_lbIso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L M)
    (hn : Nontrivial (LB.Sec L)) : Nontrivial (LB.Sec M) := by
  obtain ⟨w, hw⟩ := h
  exact (((SecOn.topEquiv L).symm ≪≫ₗ SecOn.congr hL hM w hw ⊤) ≪≫ₗ
    SecOn.topEquiv M).injective.nontrivial

theorem nontrivial_sec_pull [IsIntegral X] (M : LB X) (e : X ⟶ X) [IsIso e]
    (hn : Nontrivial (LB.Sec M)) : Nontrivial (LB.Sec (M.pull e)) := by
  rw [TrivLocus.nontrivial_sec_iff] at hn ⊢
  obtain ⟨σ, i, hi⟩ := hn
  obtain ⟨x, hx⟩ := TrivLocus.nonempty_of_ne_zero hi
  obtain ⟨y, rfl⟩ := e.homeomorph.surjective x
  have hy : y ∈ (M.pull e).U fun _ => i := mem_pull.2 hx
  refine ⟨SecOn.topEquiv _ (SecOn.pullLE M e ⊤ ⊤ le_top (GlobalTheory.LB.ofSec σ ⊤)), fun _ => i, ?_⟩
  refine (SecOn.topEquiv_f _ _).trans_ne ?_
  refine TrivLocus.rs_ne_zero _ ⟨y, hy⟩ ?_
  refine (SecOn.coord_pullLE e le_top (GlobalTheory.LB.ofSec σ ⊤) fun _ => i).trans_ne ?_
  refine TrivLocus.rs_ne_zero (U := e ⁻¹ᵁ (⊤ ⊓ M.U i)) (V := ⊤ ⊓ (M.pull e).U fun _ => i)
    (fun _ hz => ⟨trivial, mem_pull.1 hz.2⟩) ⟨y, trivial, hy⟩ ?_
  refine (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso (e.app _)).1).2 ?_
  exact TrivLocus.rs_ne_zero (U := M.U i) (V := ⊤ ⊓ M.U i) inf_le_right ⟨_, trivial, hx⟩ hi

variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsCommMonObj B]
  {M : LB B.left}

theorem ptCls_mul (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen)
    {T : Over (Spec (CommRingCat.of K))} (x y : T ⟶ B) :
    ptCls M T (x * y) = ptCls M T x * ptCls M T y ∧ ptCls M T 1 = 1 := by
  have h1 : ptCls M T 1 = 1 := by
    obtain ⟨i, hi⟩ := exists_chart hM (η[B].left (IsLocalRing.closedPoint K))
    have := (hasGen_iff hM (K := PUnit) (fun _ => (1 : T ⟶ B).left) fun _ => 1).1
      (AbSquare.exists_gen_of_mem_chart hM _ _ (fun _ => i) fun _ z => by
        change η[B].left ((toUnit T).left z) ∈ _
        have : (toUnit T).left z = IsLocalRing.closedPoint K :=
          Subsingleton.elim (α := PrimeSpectrum K) _ _
        rw [this]; exact hi)
    rwa [Fintype.prod_unique, zpow_one] at this
  refine ⟨?_, h1⟩
  have h := (hasGen_iff hM _ _).1 (MulPull.HasGen.pull hu (lift x y).left)
  have h' := (prod_square (lift x y) (fst B B) (snd B B) (cls M)).symm.trans h
  rw [lift_fst, lift_snd] at h'
  change ptCls M T (x * y) * (ptCls M T x)⁻¹ * (ptCls M T y)⁻¹ * ptCls M T 1 = 1 at h'
  rw [h1, _root_.mul_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, _root_.mul_comm (ptCls M T y)] at h'
  exact h'

theorem lbIso_pull_mul (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen) :
    LBIso (M.pull μ[B].left) (tw (M.pull (fst B B).left) (M.pull (snd B B).left) 1) := by
  refine LBIso.chartPull (chartPullId _) (chartTw M _ _) ((lbIso_iff hM _ _ _ _).2 ?_)
  have h := (ptCls_mul hM hu (fst B B) (snd B B)).1
  have e : fst B B * snd B B = μ[B] := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [e] at h
  rw [Fintype.prod_unique, Fin.prod_univ_two]
  exact (zpow_one _).trans (h.trans (congrArg₂ (· * ·) (zpow_one _).symm (zpow_one _).symm))

theorem lbIso_pull_inv (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen) :
    LBIso (M.pull (𝟙 B : B ⟶ B)⁻¹.left) (pw M (-1)) := by
  refine LBIso.chartPull (chartPullId _) (chartInv M) ((lbIso_iff hM _ _ _ _).2 ?_)
  obtain ⟨h, h1⟩ := ptCls_mul hM hu (𝟙 B : B ⟶ B)⁻¹ (𝟙 B)
  rw [inv_mul_cancel, h1] at h
  rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_neg_one]
  exact eq_inv_of_mul_eq_one_left h.symm


omit [IsCommMonObj B] in
theorem isIntegral_left (hB : IsAbelianScheme B) : IsIntegral B.left :=
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  GeometricallyIntegral.geometrically_isIntegral (f := B.hom) _ _ _ (IsPullback.of_id_fst (f := B.hom))

theorem subsingleton_sec (hB : IsAbelianScheme B) (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen)
    (hn : ¬ Triv M) : Subsingleton (LB.Sec M) := by
  have := isIntegral_left hB
  have := hB.proper
  refine not_nontrivial_iff_subsingleton.1 fun h => hn ?_
  have hi : IsIso (𝟙 B : B ⟶ B)⁻¹ := by
    have e : (𝟙 B : B ⟶ B)⁻¹ ≫ (𝟙 B : B ⟶ B)⁻¹ = 𝟙 B := by
      rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
    exact ⟨_, e, e⟩
  have : IsIso (𝟙 B : B ⟶ B)⁻¹.left := inferInstanceAs (IsIso ((Over.forget _).map (𝟙 B : B ⟶ B)⁻¹))
  exact (TrivLocus.triv_iff (isField_of_universallyClosed K B.hom) M hM.cover).2
    ⟨h, nontrivial_sec_of_lbIso (LB.isLB_pull hM _) (isLB_pw hM _) (lbIso_pull_inv hM hu)
      (nontrivial_sec_pull M _ h)⟩

def homologyZeroEquiv {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X) {κ : Type}
    [LinearOrder κ] {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤) :
    (cechLB f N D).homology 0 ≃ₗ[R] SecOnR f N ⊤ :=
  (cechHomologyZeroIso (secCube f N D)).toLinearEquiv.trans
    ((LinearEquiv.ofEq (LinearMap.ker (GlobalTheory.Cube.d (secCube f N D) (0 + 1)))
      (LinearMap.ker ((cechLB f N D).d 0 1).hom) (by rw [cechLB_d f N D 0]; rfl)).trans
      (CechOne.kerEquiv N f (fun _ => le_top) hc.ge).symm)

theorem exists_fin_affine_cover (X : Scheme.{0}) [CompactSpace X] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨s, hs, e⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
    (U := (Set.univ : Set X))).1 ⟨isCompact_univ, isOpen_univ⟩
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin (α := s) (h := hs)
  refine ⟨n, fun i => (φ.symm i).1.1, fun i => (φ.symm i).1.2, top_unique fun x _ => ?_⟩
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (e.le (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨φ ⟨U, hU⟩, show x ∈ (φ.symm (φ ⟨U, hU⟩)).1.1 by
    rw [Equiv.symm_apply_apply]; exact hx⟩

theorem eq_zero_of_conv (h o : ℕ → ℕ) (h0 : h 0 = 0) (o0 : o 0 ≠ 0)
    (e : ∀ n, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * o x.2 = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * h x.2)
    (n : ℕ) : h n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hr : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * h x.2 = 0 := Finset.sum_eq_zero fun x hx => by
      have hx := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rcases Nat.eq_zero_or_pos x.2 with h2 | h2
      · rw [h2, h0, mul_zero]
      · rw [ih x.1 (by omega), zero_mul]
    have := Finset.sum_eq_zero_iff.1 ((e n).trans hr) (n, 0) (by simp)
    exact (mul_eq_zero.1 this).resolve_right o0


omit [IsCommMonObj B] in
theorem isPullback_mul_snd : IsPullback μ[B].left (snd B B).left B.hom B.hom := by
  have e : fst B B * snd B B = μ[B] := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  let α : B ⊗ B ≅ B ⊗ B :=
    { hom := lift (fst B B * snd B B) (snd B B)
      inv := lift (fst B B * (snd B B)⁻¹) (snd B B)
      hom_inv_id := by
        ext1
        · simp [MonObj.comp_mul, GrpObj.comp_inv]
        · simp
      inv_hom_id := by
        ext1
        · simp [MonObj.comp_mul]
        · simp }
  refine (IsPullback.of_hasPullback B.hom B.hom).of_iso ((Over.forget _).mapIso α).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [← e]
    exact congrArg (·.left) (show fst B B ≫ 𝟙 B = α.inv ≫ (fst B B * snd B B) by
      simp [α, MonObj.comp_mul])
  · exact congrArg (·.left) (show snd B B ≫ 𝟙 B = α.inv ≫ snd B B by simp [α])

theorem acyclic_of_kuenneth
    (kun : ∀ (K : Type) [Field K] (Y Y' Z : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of K)) (f' : Y' ⟶ Spec (CommRingCat.of K)) (p₁ : Z ⟶ Y) (p₂ : Z ⟶ Y') (M : LB Y) (M' : LB Y'), IsPullback p₁ p₂ f f' → M.IsLB → M'.IsLB → IsSeparated f → IsSeparated f' → ∀ (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y'.Opens) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ n, Module.Finite K ((cechLB f M U).homology n)) → (∀ n, Module.Finite K ((cechLB f' M' W).homology n)) → ∀ n, Module.finrank K ((cechLB (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) D).homology n) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, Module.finrank K ((cechLB f M U).homology x.1) * Module.finrank K ((cechLB f' M' W).homology x.2))
    (hB : IsAbelianScheme B) (hM : M.IsLB)
    (hadd : LBIso (M.pull μ[B].left) (tw (M.pull (fst B B).left) (M.pull (snd B B).left) 1))
    (hs : Subsingleton (LB.Sec M)) {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → B.left.Opens}
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hfM : ∀ n, Module.Finite K ((cechLB B.hom M D).homology n))
    (hfO : ∀ n, Module.Finite K ((cechLB B.hom (Inh.trivLB _) D).homology n)) :
    (cechLB B.hom M D).Acyclic := by
  have := isIntegral_left hB
  have := hB.proper
  have hO := Inh.trivLB_isLB B.left
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : CompactSpace (B ⊗ B).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst B.hom B.hom)
  obtain ⟨m, E, hE, hEc⟩ := exists_fin_affine_cover (B ⊗ B).left
  have k₁ := kun K _ _ _ _ _ _ _ M _ isPullback_mul_snd hM hO inferInstance inferInstance
    κ D κ D _ E hD hc hD hc hE hEc hfM hfO
  have k₂ := kun K _ _ (B ⊗ B).left _ _ (fst B B).left (snd B B).left M M
    (IsPullback.of_hasPullback B.hom B.hom) hM hM inferInstance inferInstance
    κ D κ D _ E hD hc hD hc hE hEc hfM hfM
  have l₁ := isLB_tw (LB.isLB_pull hM μ[B].left) (LB.isLB_pull hO (snd B B).left) 1
  have l₂ := isLB_tw (LB.isLB_pull hM (fst B B).left) (LB.isLB_pull hM (snd B B).left) 1
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartTwTriv _ (snd B B).left) (chartPullId _) hadd
  rw [Over.w μ[B], ← Over.w (fst B B)] at k₁
  have key := eq_zero_of_conv (fun n => Module.finrank K ((cechLB B.hom M D).homology n))
    (fun n => Module.finrank K ((cechLB B.hom (Inh.trivLB _) D).homology n)) ?_ ?_ fun n =>
      (k₁ n).symm.trans (Eq.trans (LinearEquiv.finrank_eq (HomologicalComplex.homologyMapIso
        (cechLBCongr _ E l₁ l₂ w hw) n).toLinearEquiv) (k₂ n))
  · intro n
    have := hfM n
    rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
    exact Module.finrank_zero_iff.1 (key n)
  · have : Subsingleton ((cechLB B.hom M D).homology 0) :=
      ((homologyZeroEquiv B.hom M hc).toEquiv.trans (SecOnR.topEquiv B.hom M).toEquiv).subsingleton
    exact Module.finrank_zero_of_subsingleton
  · have : Nontrivial (LB.Sec (Inh.trivLB B.left)) :=
      ((TrivLocus.triv_iff (isField_of_universallyClosed K B.hom) _ hO.cover).1 (triv_trivLB _)).1
    have : Nontrivial ((cechLB B.hom (Inh.trivLB _) D).homology 0) :=
      ((homologyZeroEquiv B.hom _ hc).toEquiv.trans (SecOnR.topEquiv B.hom _).toEquiv).nontrivial
    have := hfO 0
    exact Module.finrank_pos.ne'

end GlobalTheory.PrimVan
end
end

