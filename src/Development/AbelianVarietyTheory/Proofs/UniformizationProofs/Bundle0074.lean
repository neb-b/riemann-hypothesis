module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages

namespace GlobalTheory.GtCoordCompare

section Calc

variable {Y W W' Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {ψ : K → (W ⟶ Y)} {ψ' : K → (W' ⟶ Y)}
  {ε ε' : K → ℤ} {r : Z ⟶ W} {r' : Z ⟶ W'}

end Calc

section Image

variable {Y G B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] (q : G ⟶ B) {φ : K → (B ⟶ Y)} {φ' : K → (G ⟶ Y)}
  {ε ε' : K → ℤ}

variable {q} {x : LB.Gen (LB.LinComb L φ' ε')} {V : B.Opens}


end Image

section Group

variable {S Y : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B] {q : G ⟶ B}
  {i : splitTorus S X ⟶ G} {L : LB Y} {K : Type} [Fintype K] {ε ε' : K → ℤ}

def WtGen (i : splitTorus S X ⟶ G) {φ' : K → (G.left ⟶ Y)} (x : LB.Gen (LB.LinComb L φ' ε')) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
    val x ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val x g.left z J

theorem act_comp [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ i) * g).left ≫ q.left = g.left ≫ q.left := by
  have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, hi, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  exact congrArg (fun f => f.left) e

theorem isWt_of_gs {V : G.left.Opens} {a : Γ(G.left, V)} {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ V → ∀ z : Z.left,
      gs ((t ≫ i) * g).left z V a = (gm t.left z ⊤ (charUnit S X χ)).val * gs g.left z V a) : IsWt i V a χ :=
  fun Z t g h₁ h₂ => fn_ext fun z hz => by
    rw [gs_mul _ z _ hz, gs_appLE _ _ _ _ _ z hz, gs_appLE _ _ _ _ _ z hz, Category.id_comp, Category.id_comp,
      h Z t g h₂ z]
    congr 1
    refine ((gs_pull (𝟙 _) t.left z ⊤ trivial _).trans ?_).symm
    rw [Category.id_comp, gs_unit _ z ⊤ trivial]

section One

variable [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) (hL : L.IsLB) {φ : K → (B.left ⟶ Y)} {φ' : K → (G.left ⟶ Y)}
  (hφ : ∀ k, φ' k = q.left ≫ φ k) {x : LB.Gen (LB.LinComb L φ' ε')} (hx : x.IsGen) {χ : X} (hw : WtGen i x χ)
include hi hL hφ hx hw


end One

section All

variable [IsMonHom q] [IsMonHom i] [IsAffineHom q.left] (hL : L.IsLB) (hε : ∀ k, ε' k = -ε k)
  {φ : X → K → (B.left ⟶ Y)} {φ' : X → K → (G.left ⟶ Y)} (hφ : ∀ χ k, φ' χ k = q.left ≫ φ χ k)
  {x : ∀ χ, LB.Gen (LB.LinComb L (φ' χ) ε')} (hx : ∀ χ, (x χ).IsGen) (hw : ∀ χ, WtGen i (x χ) χ)
include hL hε hφ hx hw


end All

end Group

end GlobalTheory.GtCoordCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenVOfPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.FrameVal
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.CoefUnit

theorem genV_of_pow : AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (w₁ : Frm D.toPre F 1 p.g.b), w₁.IsGen → ∀ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ n) (4 * n ^ 2) 4), κ.IsGen → (∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J ^ (4 * n ^ 2) * val κ p.g.b.left z J = (@id ((TF (R := V) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := V) F) z J) * rigV D.toPre (TF (R := V) F).hom z J) ^ 4) → GenV hϖ hv w₁ ((Q p.y : ℚ) / (n : ℚ) ^ 2) := by
  intro V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv n hn p w hw κ hκ H
  have hL := D.toPre.P.isLB
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) p.g.b
  have hmy : cP D.toPre (TWM.TO hϖ hv) p.y = m ^ n := TWM.liftO_unique hϖ hv _ _ (by
    rw [comp_cP, cPoint_y, ← hm]; exact (map_pow (preHom (TWM.ιS hϖ hv)) m n).symm)
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local D.toPre.P.L hL (TWM.lineφO hϖ hv m) (DegPre.lineε 1)
  have hl : ∀ i, DegPre.lineφ D.toPre F p.g.b i = (TWM.ιS hϖ hv).left ≫ TWM.lineφO hϖ hv m i := by
    intro i; fin_cases i
    · show (DegPre.zeroF D.toPre F).left = (TWM.ιS hϖ hv).left ≫ (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
    · show p.g.b.left = (TWM.ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
  obtain ⟨x, hx0, hx⟩ := TWM.exists_ratio hL w hw (LB.pullGen D.toPre.P.L _ _ t₀ (TWM.ιS hϖ hv).left)
    (pullGen_isGen _ _ _ _ ht₀ _) (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hl])
  have hx' : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val =
      cst (R := V) F z x * (val t₀ (TWM.ιS hϖ hv).left z J).val := fun z J hJ => by
    have e := hx _ (𝟙 _) z J hJ
    rw [val_pull hJ] at e
    exact e
  refine ⟨TWM.lineφO hϖ hv m, hl, t₀, ht₀, x, ?_, hx'⟩
  obtain ⟨e, c, he, hc, hce⟩ := SectionScalarValuation.exists_val_genHasVal (hQ p.y)
  obtain ⟨u, hu, eu⟩ := exists_ratio_zero hϖ hv hL (fun U _ h => by
      have q : (TWM.TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left := rfl
      have q₁ : (TWM.TO hϖ hv).hom ≫ (D.toPre.c p.y).left = (m ^ n).left := hmy ▸ rfl
      have q₂ : m.left ≫ (𝟙 D.toPre.P.A ^ n).left = (m ^ n).left :=
        congrArg (·.left) ((map_pow (preHom m) (𝟙 D.toPre.P.A) n).trans (congrArg (· ^ n) (Category.comp_id m)))
      have q₃ : m.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left :=
        congrArg (·.left) (MonObj.comp_one (M := D.toPre.P.A) m)
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_unique (_ : PUnit → U), Fintype.prod_unique (_ : PUnit → U), q, q₁, Fin.prod_univ_two,
        Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        TWM.lineφO, DegPre.lineε, q₂, q₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen _ _ _ _ _ (GeneratorPullback.powGen _ _ _ t₀ (4 * n ^ 2)) (LB.pullGen _ _ _ κ m.left))
    (mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht₀ _) (DVR.pullGen_isGen _ _ _ _ hκ _))
    (GeneratorPullback.powGen _ _ _ (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ e (TWM.TO hϖ hv).hom)
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TWM.TO hϖ hv).hom)) 4)
    (DVR.powGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ he _)
      (DVR.pullGen_isGen _ _ _ _ D.toPre.rig_gen _)) _)
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have a := eu z J hJ
  rw [val_mul hJ, RatioVal.val_powGen, RatioVal.val_powGen, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ,
    Over.w (TWM.ιS hϖ hv), ← Over.comp_left, hm] at a
  have b := congrArg Units.val (H z J hJ)
  have d : (@id ((TF (R := V) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := V) F) z J)).val =
      cstH z (algebraMap (FractionRing V) F c) * (val e (TF (R := V) F).hom z J).val :=
    (hce _ (jFK (R := V) F) z J hJ).trans (congrArg (· * _) (RatioVal.gs_scal _ z c))
  have key : x ^ (4 * n ^ 2) * u = algebraMap (FractionRing V) F c ^ 4 := by
    apply cstH_inj (R := V) z
    apply ((val e (TF (R := V) F).hom z J * rigV D.toPre (TF (R := V) F).hom z J) ^ 4).isUnit.mul_right_cancel
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, d, hx' z J hJ, cst_eq, rigV, map_mul, map_pow, mul_pow] at a b ⊢
    linear_combination b - cstH z x ^ (4 * n ^ 2) * a
  have k := congrArg v key
  obtain ⟨q, hq⟩ := TWM.wt_coe_of_ne (v := v) hx0
  rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow, hu, hv _ _ hc, hq] at k
  have k' : (4 * n ^ 2) • q + 0 = 4 • ((Q p.y : ℤ) : ℚ) := by exact_mod_cast k
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [hq, WithTop.coe_inj, eq_div_iff (pow_ne_zero 2 hn0)]
  simp only [nsmul_eq_mul] at k'
  push_cast at k'
  linarith

end GlobalTheory.UT.FrameVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfIsPowGrp
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiPow

theorem nonempty_torusExtension {K : Type} [Field K] {G' G : Over (Spec (CommRingCat.of K))} [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (E : TorusExtension G) : Nonempty (TorusExtension G') := by
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Spec (CommRingCat.of K)) E.X (Fin j → E.X) j (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ G' G (powObj E.B j) E.B j p (powIsPowGrp E.B j) E.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ G' G j pT p E.i
  exact ⟨{ X := Fin j → E.X
           B := powObj E.B j
           isAbelian := (GlobalTheory.PowGrp.powers _ _ _ j (powIsPowGrp E.B j)).2.2.2.1 E.isAbelian
           q := q'
           q_hom := hq1 E.q_hom
           q_flat := hq2 E.q_flat
           q_surjective := hq3 E.q_surjective
           q_quasiCompact := hq4 E.q_quasiCompact
           i := i'
           i_hom := hi1 E.i_hom
           isKernel := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ j pT p (powIsPowGrp E.B j) E.i E.q i' q' hi hq
             E.isKernel }⟩

theorem isSemiAbelian_of_isPowGrp : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (j : ℕ) (_ : IsPowGrp G' G j), IsSemiAbelian G → IsSemiAbelian G' := by
  intro S G G' _ _ j p hG
  obtain ⟨h1, h2, -, -, h5⟩ := GlobalTheory.PowGrp.powers S G' G j p
  have hq := GlobalTheory.PowGrp.quasiCompact_geomConnected_pow S G' G j p
  refine ⟨h5 hG, h1 hG.smooth, h2 hG.separated, hq.1 hG.quasiCompact, hq.2 hG.smooth hG.geomConnected,
    fun Ω _ _ f => ?_⟩
  obtain ⟨p', -⟩ := GlobalTheory.isPowGrp_baseChange S _ f G' G j p
  obtain ⟨E⟩ := hG.fibres Ω f
  exact nonempty_torusExtension p' E

end GlobalTheory.SemiPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfRed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedAdd

open GlobalTheory.FormalPoint GlobalTheory.TorusCoord ReciprocityTheory.ChartRestriction.G.DVR

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

theorem red_iff_over (x : T ⟶ G) (g : GtPt D T) :
    U.Red x g ↔ ∀ (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (r : (Over.map (thick R I e)).obj Z ⟶ T) (a : Z ⟶ thickObj R I e G),
      (Over.map (thick R I e)).map a ≫ fstG I e G = r ≫ x → im (U.gt e) a = r ≫ g.b ∧
        ∀ χ z J, Good D.P.L z J →
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J = val (g.s χ) r.left z J := by
  constructor
  · intro h e Z r a ha
    obtain ⟨h₁, h₂⟩ := h e _ r.left ((Over.map (thick R I e)).map a).left (congrArg (fun q => q.left) ha)
    exact ⟨Over.OverMorphism.ext h₁, h₂⟩
  · intro h e Z r y hy
    have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
    obtain ⟨h₁, h₂⟩ := h e (Over.mk (y ≫ (thickObj R I e G).hom)) (Over.homMk r w) (Over.homMk y rfl)
      (Over.OverMorphism.ext hy)
    exact ⟨congrArg (fun q => q.left) h₁, h₂⟩

theorem map_one_fstG {e : ℕ} {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    (Over.map (thick R I e)).map (1 : Z ⟶ thickObj R I e G) ≫ fstG I e G = 1 := by
  have := map_mul_fstG (1 : Z ⟶ thickObj R I e G) 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem red_one {g : GtPt D T} (h : g.IsZero) : U.Red 1 g := by
  rw [red_iff_over]
  intro e Z r a ha
  obtain rfl : a = 1 := eq_of_map_fstG (by rw [ha, map_one_fstG, MonObj.comp_one])
  refine ⟨by rw [im_one, h.1]; exact (MonObj.comp_one r).symm, fun χ z J hJ => ?_⟩
  have t₁ := val_unit (U.gt e) χ (Z := Z) (z := z) hJ
  exact t₁.trans ((val_corr hJ (h.2 χ) r.left).trans (val_one _)).symm


variable {U} in
theorem red_mul (hG : GlobalFnsSt) {g g' g'' : GtPt D T} {x x' : T ⟶ G} (hx : U.Red x g)
    (hx' : U.Red x' g') (h : g.IsAdd g' g'') : U.Red (x * x') g'' := by
  rw [red_iff_over] at hx hx' ⊢
  intro e Z r y hy
  obtain ⟨a, ha⟩ := exists_lift_fstG (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift_fstG (r ≫ x')
  obtain rfl : y = a * b := eq_of_map_fstG (by rw [hy, map_mul_fstG, ha, hb, MonObj.comp_mul])
  obtain ⟨a₁, a₂⟩ := hx e Z r a ha
  obtain ⟨b₁, b₂⟩ := hx' e Z r b hb
  refine ⟨by rw [im_mul, a₁, b₁, h.1]; exact (MonObj.comp_mul _ _ _).symm, fun χ z J hJ => ?_⟩
  have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a * b)).left z J *
      th D z J (cP D _ χ) (im (U.gt e) a) (im (U.gt e) b) =
      val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J *
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map b).left z J :=
    val_t_mul_points (U.gt e) hG χ a b z J hJ
  have e₂ : val (g''.s χ) r.left z J * th D z J (r ≫ cP D T χ) (r ≫ g.b) (r ≫ g'.b) =
      val (g.s χ) r.left z J * val (g'.s χ) r.left z J :=
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub r hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) r.left).trans (val_mul hJ _ _ _))
  rw [a₁, b₁, a₂ χ z J hJ, b₂ χ z J hJ] at e₁
  rw [comp_cP] at e₂
  exact mul_right_cancel (e₁.trans e₂.symm)

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : PreU I D A G}


variable (I φ) in
abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (levelMap I φ e)


variable (I φ) in
def levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I φ e) ⟶ Over.mk (spMap φ) :=
  Over.homMk (thick S (I.map φ) e) (levelMap_thick I φ e).symm

variable [IsLocalRing S] [IsHausdorff (I.map φ) S]


omit [IsDomain R] in
theorem pt_ext {B : Over (Spec (CommRingCat.of R))} {b b' : Over.mk (spMap φ) ⟶ B}
    (h : ∀ e, levι I φ e ≫ b = levι I φ e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff (I.map φ) fun e => congrArg (·.left) (h e))

variable [IsNoetherianRing S]

theorem isAdd_of_red (hG : GlobalFnsSt) {x x' : Over.mk (spMap φ) ⟶ G} {g g' g'' : GtPt D (Over.mk (spMap φ))}
    (h : U.Red x g) (h' : U.Red x' g') (h'' : U.Red (x * x') g'') : GtPt.IsAdd g g' g'' := by
  rw [red_iff_over] at h h' h''
  choose a ha using fun e => exists_lift_fstG (levι I φ e ≫ x)
  choose a' ha' using fun e => exists_lift_fstG (levι I φ e ≫ x')
  have k := fun e => h e _ _ _ (ha e)
  have k' := fun e => h' e _ _ _ (ha' e)
  have k'' := fun e => h'' e _ (levι I φ e) (a e * a' e) (by rw [map_mul_fstG, ha, ha', MonObj.comp_mul])
  have hb : g''.b = g.b * g'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (k e).1, ← (k' e).1, ← (k'' e).1, im_mul]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.isGen χ) (g'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g''.b χ h) (prod_cub (DegPre.cT D _ χ) g.b g'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g.b χ h) (CoordAdd.prod_gtφT g'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e * a' e)).left z J *
        th D (T := (Over.map (thick R I e)).obj (lev I φ e)) z J (cP D _ χ) (im (U.gt e) (a e)) (im (U.gt e) (a' e)) =
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e)).left z J *
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a' e)).left z J :=
      val_t_mul_points (U.gt e) hG χ (a e) (a' e) z J hJ
    rw [(k e).1, (k' e).1, (k e).2 χ z J hJ, (k' e).2 χ z J hJ, (k'' e).2 χ z J hJ,
      ← comp_cP D (levι I φ e)] at e₁
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I φ e) hJ _ _ _))).trans
      (e₁.trans (val_mul hJ _ _ _).symm)

theorem isZero_of_red {g : GtPt D (Over.mk (spMap φ))} (h : U.Red 1 g) : g.IsZero := by
  rw [red_iff_over] at h
  have k := fun e => h e _ (levι I φ e) 1 (by rw [map_one_fstG, MonObj.comp_one])
  have hb : g.b = 1 := pt_ext (I := I) fun e => by rw [MonObj.comp_one, ← (k e).1, im_one]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (g.isGen χ) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (CoordAdd.prod_gtφT g.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · exact ((k e).2 χ z J hJ).symm.trans
      ((val_unit (U.gt e) χ (Z := lev I φ e) (z := z) hJ).trans (val_one _).symm)

end Complete

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (x x' x'' : TA V W ⟶ G) (g g' g'' : GtPt D (TA V W)), U.Red x g → U.Red x' g' → U.Red x'' g'' → (x'' = x * x' ↔ GtPt.IsAdd g g' g'') ∧ (x = 1 ↔ g.IsZero)) := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW x x' x'' g g' g'' h h' h''
  have := hV.1
  have := hW.1
  have := hW.2.2.2.2
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  refine ⟨⟨fun e => ?_, fun e => ?_⟩, ⟨fun e => ?_, fun e => ?_⟩⟩
  · exact isAdd_of_red (φ := algebraMap V W) hG h h' (e ▸ h'')
  · exact RedOnto.red_unique (φ := algebraMap V W) h'' (red_mul hG h h' e)
  · exact isZero_of_red (φ := algebraMap V W) (e ▸ h)
  · exact RedOnto.red_unique (φ := algebraMap V W) h (red_one U e)

end GlobalTheory.UU.RedAdd

end
end

