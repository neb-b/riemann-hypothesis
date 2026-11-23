module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivTranslateOrderTwo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.TranslateEvenTriv
open GlobalTheory.UU

theorem exists_gen_pull {X X' Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X' ⟶ X} {L' : LB X'} (e : L' = L.pull F)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε))
    (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J →
        (∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F))) → val a r z J' = val t r z J := by
  subst e
  have h := pull_isLB hL F
  have hc : ∀ k, φ k ≫ F = 𝟙 Y ≫ (fun k => φ k ≫ F) k := fun k => (Category.id_comp _).symm
  obtain ⟨a, ha, Ha⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen hL F)) hL h (𝟙 Y) hc t ht
  refine ⟨a, ha, fun Z r z J J' hJ hJ' => ?_⟩
  obtain rfl : J' = fun q _ => J (q ≫ F) := funext fun q => eq_of_heq (hJ' q)
  have hg : Good (L.pull F) z (fun q _ => J (q ≫ F)) := fun q => mem_pull.2 (hJ (q ≫ F))
  have := CubTransport.val_pmaps hc Ha r hJ hg
  rw [Category.comp_id, Finset.prod_eq_one, _root_.one_mul] at this
  · exact this.symm
  · intro k _
    have : gw (pullIso L F) (r ≫ φ k) z (J ((r ≫ φ k) ≫ F)) (fun _ => J ((r ≫ φ k) ≫ F)) = 1 :=
      gm_self h (r ≫ φ k) z (hg (r ≫ φ k))
    rw [this, one_zpow]

theorem exists_good_of_pull {X Z : Scheme.{0}} {L L' : LB X} {F : X ⟶ X} (hF : F ≫ F = 𝟙 X) (e : L' = L.pull F)
    {z : Z} {J' : (Z ⟶ X) → L'.ι} (hJ' : Good L' z J') :
    ∃ J : (Z ⟶ X) → L.ι, Good L z J ∧ ∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F)) := by
  subst e
  refine ⟨fun q => J' (q ≫ F) PUnit.unit, fun q => ?_, fun q => heq_of_eq ?_⟩
  · have : ((q ≫ F) ≫ F) z ∈ L.U (J' (q ≫ F) PUnit.unit) := (mem_pull (F := F)).1 (hJ' (q ≫ F))
    rwa [Category.assoc, hF, Category.comp_id] at this
  · show J' q = J' ((q ≫ F) ≫ F)
    rw [Category.assoc, hF, Category.comp_id]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]


omit [IsCommMonObj G] in
theorem comp_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (g : T ⟶ G) :
    g ≫ ((toUnit G ≫ a) * 𝟙 G) = (toUnit T ≫ a) * g := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]

variable {X : Type} [AddCommGroup X] (Q : TQ G X)


omit [IsCommMonObj G] in
theorem mul_torus_comp {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X) : (g * (x ≫ Q.i)) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  rw [MonObj.mul_comp, Category.assoc, e, MonObj.comp_one, _root_.mul_one]

theorem exists_gen_torus {P₁ : CP G} (D : Q.Desc P₁) (a : 𝟙_ (Over S) ⟶ G) :
    ∃ s : LB.Gen (LB.LinComb P₁.L.L (K := Fin 2) (fun k => ![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫
      ((toUnit G ≫ a) * 𝟙 G).left) ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (N) (J), Good D.M.L.L z N → Good P₁.L.L z J →
        ∀ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
          (∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left)) →
          val s x.left z J = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (x ≫ Q.i)))⁻¹ := by
  obtain ⟨t, ht, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := fun _ => ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left)
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have hc : ∀ k : Fin 2, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left =
      𝟙 _ ≫ ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left := fun k => by
    rw [Category.id_comp]
    fin_cases k
    · refine congrArg (fun q => q.left) (show (Q.i ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      have := mul_torus_comp Q (toUnit (splitTorus S X) ≫ a) (𝟙 _)
      rw [Category.id_comp] at this
      rw [comp_translate, this]
    · refine congrArg (fun q => q.left) (show ((1 : splitTorus S X ⟶ G) ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      rw [comp_translate, _root_.mul_one]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 D.map.gen) D.M.L.isLB P₁.L.isLB (𝟙 _) hc t ht
  refine ⟨s, hs, fun T x z N J hN hJ W hW => ?_⟩
  have e := CubTransport.val_pmaps hc Hs x.left hN hJ
  rw [v _ _ z N hN, val_one] at e
  have hτ : ∀ g : T ⟶ G, g.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * g).left := fun g =>
    congrArg (fun q => q.left) (comp_translate a g)
  have e₂ := CubTrivTorus.prod_cubTriv Q.i x (fun q => gw D.w (q ≫ ((toUnit G ≫ a) * 𝟙 G).left) z
    (N ((q ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left)) (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)))
  rw [hτ, hτ, _root_.mul_one, ← hW, ← hW] at e₂
  simp only [← Category.assoc x.left] at e
  have e₃ := e.trans (congrArg₂ (· * ·) e₂ rfl)
  apply Additive.ofMul.injective
  have e₄ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₄ ⊢
  linear_combination (norm := abel) -e₄

theorem exists_even_cubTriv : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  rintro S G _ _ X _ Q P₁ ⟨D⟩ a ha P hP hsym hcub
  have := Q.i_hom
  have hinv : ∀ T : Over S, (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := fun T => by
    rw [inv_eq_iff_mul_eq_one, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one]
  have hF : ((toUnit G ≫ a) * 𝟙 G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left = 𝟙 G.left := by
    refine congrArg (fun q => q.left) (show ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G from ?_)
    rw [comp_translate, ← _root_.mul_assoc, (inv_eq_iff_mul_eq_one.1 (hinv G)), _root_.one_mul]
  obtain ⟨s, hs, vs⟩ := exists_gen_torus Q D a
  obtain ⟨σ, hσ, vσ⟩ := exists_gen_pull P₁.L.isLB hP _ _ s hs
  have hq : ∀ {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X), (g * (x ≫ Q.i)).left ≫ Q.q.left = g.left ≫ Q.q.left :=
    fun g x => congrArg (fun q => q.left) (mul_torus_comp Q g x)
  refine ⟨⟨σ, hσ, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  all_goals
    obtain ⟨J, hJ, hJJ⟩ := exists_good_of_pull hF hP hJ'
    obtain ⟨N, hN⟩ := exists_good_pt D.M.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      ∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left) := ⟨_, fun _ => rfl⟩
    have v : ∀ t : T ⟶ splitTorus S X, val σ t.left z J' = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (t ≫ Q.i)))⁻¹ :=
      fun t => (vσ _ t.left z J J' hJ hJJ).trans (vs T t z N J hN hJ W hW)
    obtain ⟨-, a₂, a₃⟩ := D.map.vals T z J N hJ hN W hW
  · have b₁ := a₃ (x ≫ Q.i) (y ≫ Q.i) ((toUnit T ≫ a) * (u ≫ Q.i))
    have b₂ := a₃ (x ≫ Q.i) (y ≫ Q.i) (toUnit T ≫ a)
    have e : toBase (f := 𝟙 S) (g := Q.q.left) (by simp) ((toUnit T ≫ a) * (u ≫ Q.i)) =
        toBase (f := 𝟙 S) (g := Q.q.left) (by simp) (toUnit T ≫ a) := Over.OverMorphism.ext (hq _ u)
    rw [e] at b₁
    rw [hcub T _ _ _ z J J' hJ hJJ]
    simp only [v, MonObj.mul_comp]
    generalize x ≫ Q.i = x' at *
    generalize y ≫ Q.i = y' at *
    generalize u ≫ Q.i = u' at *
    generalize toUnit T ≫ a = A at *
    rw [mul_left_comm x' A, mul_left_comm y' A, mul_left_comm (x' * y') A] at b₁
    rw [mul_comm x' A, mul_comm y' A, mul_comm (x' * y') A] at b₂
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂
  · have b₁ := a₂ ((toUnit T ≫ a) * (x ≫ Q.i))
    have b₂ := a₂ (toUnit T ≫ a)
    rw [hq, mul_inv, hinv] at b₁
    rw [hinv] at b₂
    show val σ _ z J' = _ * val σ _ z J'
    rw [hsym T _ z J J' hJ hJJ, v, v, GrpObj.inv_comp]
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂

end GlobalTheory.TranslateEvenTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem IntFam.exists_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G), IsSemiAbelian G → ∀ k : ℕ, 1 ≤ k → ∀ F : IntFam (maximalIdeal R) D.toPre k, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ F.f := by
  intro R _ _ _ hB D A G _ _ U hG k hk F
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have : IsNoetherianRing R := hR.1
  have := hG.geomConnected
  obtain ⟨s, ⟨r, hr, σ₀, f₀, -, hf₀, hE⟩, -⟩ := (U.expand k hk).2 F.F
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    rw [scal, map_one, map_one]
  have h₁ : ∀ α j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (F.f α).f j := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB _
      (GlobalTheory.IntegralExpansion.prB_app_injective D.toPre) (h1 ▸ F.ext α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₀ α)
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R _ hR D A G U.toUnifPre k r hr σ₀ f₀ F.f h₁ hE
  exact ⟨σ, GlobalTheory.expandsAt_cancel_of_ne_zero R _ D A G U.toUnifPre k r hr σ σ₀ F.f f₀ hσ h₁ hE⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamCoefVal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.TorsionAnyChar

noncomputable section

namespace GlobalTheory.PeriodsAnyChar

end GlobalTheory.PeriodsAnyChar

open GlobalTheory.PeriodsAnyChar

namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

end GlobalTheory.UT.CoefVal

namespace GlobalTheory.UT.CoefUnit
open GlobalTheory.UT.CoefBasic

end GlobalTheory.UT.CoefUnit

namespace GlobalTheory.UT.SmallPoint
open CoefBasic

end GlobalTheory.UT.SmallPoint

namespace GlobalTheory.UT.SmallZero
open CoefBasic SmallPoint

end GlobalTheory.UT.SmallZero

namespace GlobalTheory.UT.EvalZero
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

end GlobalTheory.UT.EvalZero

namespace GlobalTheory.UT.MixedConv
open GlobalTheory.FieldBaseChange

section Core
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]

end Core

end GlobalTheory.UT.MixedConv

namespace GlobalTheory.UT

theorem _root_.GlobalTheory.PeriodsAnyChar.weilQkIs_iff_weilIs : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  intro hL R _ _ I _ D A G _ _ _ U F _ _ _ k hk p p' x x' hx hx' ζ
  have hG := hL.1.globalFns
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  obtain ⟨ρ, hρ, hcomm, -⟩ := thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG A.isAb A.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, Units.ext (by simp [unitOn])⟩
  let E : SecM A.A A.L (k : ℤ) (TFK (R := R) F) → Fam D.toPre F k := fun v => e (SecM.toSec A.A v)
  have hE : ∀ s, ∃ v, E v = s := fun s => ⟨SecM.ofSec A.A (e.symm s), e.apply_symm_apply s⟩
  have a : ∀ v, PhiRel D.toPre F k p w (E v) (E (ρ θ v)) := fun v =>
    h _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have a' : ∀ v, PhiRel D.toPre F k p' w' (E v) (E (ρ θ' v)) := fun v =>
    h' _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have b : ∀ v t, PhiRel D.toPre F k p w (E v) t → t = E (ρ θ v) := fun v t H =>
    phi_unique p w ((phiRel_iff hG p w hw _ _).1 H) ((phiRel_iff hG p w hw _ _).1 (a v))
  have b' : ∀ v t, PhiRel D.toPre F k p' w' (E v) t → t = E (ρ θ' v) := fun v t H =>
    phi_unique p' w' ((phiRel_iff hG p' w' hw' _ _).1 H) ((phiRel_iff hG p' w' hw' _ _).1 (a' v))
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' (z : F) (fun s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => by
    obtain ⟨v, rfl⟩ := hE s
    obtain rfl := b' _ _ h₁
    obtain rfl := b _ _ h₂
    obtain rfl := b _ _ h₃
    obtain rfl := b' _ _ h₄
    rw [hcomm θ θ' _ hc v]
    exact e.map_smul (z : F) (SecM.toSec A.A (ρ θ' (ρ θ v)))) (by
    obtain ⟨B, hB, -⟩ := BoxSpan.exists_basis hL.1.secBaseChange A k hk F (jFK (R := R) F)
    have : Nontrivial Γ((TFK (R := R) F).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    have hne := hB.ne_zero ⟨0, pow_pos hk _⟩
    refine ⟨_, _, _, a (B ⟨0, pow_pos hk _⟩), a' _, fun h0 => hne ?_⟩
    have h1 : SecM.toSec A.A (ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩))) = _ := e.map_eq_zero_iff.1 h0
    have h2 : ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩)) = 0 := congrArg (SecM.ofSec A.A) h1
    exact (ρ θ).map_eq_zero_iff.1 ((ρ θ').map_eq_zero_iff.1 h2)) hk (ζ : F)
  have hz := GlobalLift.weilIs_of_commIsOf hG A.isAb A.isLB hc
  rw [key]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG A.isAb A.isLB H hz))

end GlobalTheory.UT

namespace GlobalTheory.TorsionIso

theorem _root_.GlobalTheory.PeriodsAnyChar.torsion_map : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), (∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) ∧ ((k : F) ≠ 0 → ∀ x, x ^ k = 1 → ∃ p, f p = x) ∧ (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧ (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧ ∀ p p' (z : Fˣ), WeilQkIs D.toPre F k p p' z ↔ WeilIs A.A A.L k (f p) (f p') (unitOn z) := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k hk
  have hqk := indAtTransl_any hL R I hI D A G hG U F k hk
  have hcomp := indAtComp_any hL R I hI D A G hG U F k hk
  have huniq := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hinj := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hex : ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U.toUnifPre F k p x := fun p => by
    obtain ⟨x, hx⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
    exact ⟨x, (hqk p x).1 (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩
  choose f hf using hex
  have hwd : ∀ p p', QkPt.Equiv D.toPre F p p' → f p = f p' := fun p p' h =>
    huniq p' _ _ ((hqk _ _).1 ((hcomp p p' p' _ (𝟙 _) ((hqk _ _).2 (hf p))).2.1 h)) (hf p')
  have hpow : ∀ p, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.ext
    exact (hf p w hw).1
  refine ⟨f, fun p x => ⟨fun h => huniq p _ _ h (hf p), fun h => h ▸ hf p⟩, ?_,
    fun p p' => ⟨fun h => hinj p p' (f p) (hf p) (h ▸ hf p'), hwd p p'⟩, ?_,
    fun p p' z => GlobalTheory.PeriodsAnyChar.weilQkIs_iff_weilIs hL R I hI D A G hG U F k hk p p' _ _ (hf p) (hf p') z⟩
  · intro hkF x hx
    obtain ⟨p, hp⟩ := exists_qkToAkU R I hI D A G hG U F k hkF x hx
    exact ⟨p, huniq p _ _ (hf p) hp⟩
  · intro p p' p'' h
    have := (hcomp p p' p'' _ _ ((hqk _ _).2 (hf p))).1 ((hqk _ _).2 (hf p')) h
    rw [translT_comp] at this
    exact huniq p'' _ _ (hf p'') ((hqk _ _).1 this)

end GlobalTheory.TorsionIso

namespace GlobalTheory.LevelCompat
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem _root_.GlobalTheory.PeriodsAnyChar.qkToAkU_level : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n → N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, (q.y = n • p.y → q.g = p.g → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F N q x)) ∧ (p.y = q.y → GtPtF.IsNsmul n q.g p.g → QkToAkU U.toUnifPre F N q x → QkToAkU U.toUnifPre F k p (x ^ n)) := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨f, hf, -⟩ := GlobalTheory.PeriodsAnyChar.torsion_map hL R I hI D A G hG U F k hk
  obtain ⟨f', hf', -, -, hadd, -⟩ := GlobalTheory.PeriodsAnyChar.torsion_map hL R I hI D A G hG U F N hN1
  have key : ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → f p = f' q := by
    intro p q hy hg
    obtain ⟨x₀, h₀⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
    have a := (indAtTransl_any hL R I hI D A G hG U F k hk p x₀).1
      (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
    have b := (indAtTransl_any hL R I hI D A G hG U F N hN1 q x₀).1 (h₀ n N hn hN q hy hg)
    exact ((hf p x₀).1 a).symm.trans ((hf' q x₀).1 b)
  intro p q x
  refine ⟨fun hy hg => by rw [hf, hf', key p q hy hg], fun hy hg hx => ?_⟩
  have hx' : x = f' q := (hf' q x).1 hx
  have hp : ∀ j : ℕ, f' (qkNsmul D.tau_bimult (j + 1) q) = x ^ (j + 1) := by
    intro j
    induction j with
    | zero => rw [Nat.zero_add, qkNsmul_one, pow_one, hx']
    | succ j ih => rw [hadd _ _ _ (qkAdd_qkNsmul D.tau_bimult (j + 1) q), ih, ← hx', ← pow_succ]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [hf, ← hp j]
  exact (key p _ (by rw [hy]; rfl) ((isNsmul_iff_eq _ _ _).1 hg).symm).symm

end GlobalTheory.LevelCompat

namespace GlobalTheory.UT.EndTors
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic
attribute [local instance] gtGroup

end GlobalTheory.UT.EndTors

namespace GlobalTheory.UT.EndBaseChange
open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

end GlobalTheory.UT.EndBaseChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finEtale_section_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (a : Sp R' ⟶ U.left), FinExt ρ ∧ ρ.Etale ∧ a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  intro R _ _ _ hR U hU O hO
  obtain ⟨k', _, _, _, _, x, hx, hxO⟩ := _root_.GlobalTheory.Mum.exists_separable_point_of_smooth R U hU O hO
  obtain ⟨R', _, _, _, ρ, σ, hF, hE, hσ⟩ := _root_.GlobalTheory.Mum.exists_finExt_etale_of_isSeparable R hR k'
  have hN : IsNoetherianRing R' := hF.1.1
  have hc : IsAdicComplete (maximalIdeal R') R' := hF.1.2.2.2
  have hx₀ : (spMap σ ≫ x) ≫ U.hom = spMap ((residue R').comp ρ) := by
    rw [Category.assoc, hx, ← hσ, ← Spec.map_comp]; rfl
  have hr : Set.range (spMap σ ≫ x) ⊆ O := by
    rintro _ ⟨p, rfl⟩; exact hxO ⟨_, rfl⟩
  obtain ⟨a, ha, haO⟩ := GlobalTheory.T.exists_lift_residueFieldPoint_smooth_completeLocal R R' hc ρ U hU (spMap σ ≫ x) hx₀ O hr
  exact ⟨R', _, inferInstance, inferInstance, ρ, a, hF, hE, ha, haO⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionRealisingSubextension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_finExt_realising : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (E : IntermediateField (FractionRing R₁) (Kb R₁)), FiniteDimensional (FractionRing R₁) E → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ ∧ FinExt (i₁₂.comp ρ) ∧ IsLocalHom i₁₂ ∧ ∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r) := by
  intro R _ _ _ hR R₁ _ _ _ ρ hρ E hE
  obtain ⟨hadm, hinj, hfin⟩ := hρ
  haveI : CharZero R := hR.2
  haveI : CharZero R₁ := charZero_of_injective_ringHom hinj
  have hR₁ : Base R₁ := ⟨hadm, inferInstance⟩
  let E' := IntermediateField.normalClosure (FractionRing R₁) E (Kb R₁)
  haveI : IsGalois (FractionRing R₁) E' := inferInstance
  haveI : FiniteDimensional (FractionRing R₁) E' := inferInstance
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E') hR₁
  letI : Algebra R₁ E' := (baseMap R₁ E').toAlgebra
  haveI : IsScalarTower R₁ (FractionRing R₁) E' := IsScalarTower.of_algebraMap_eq' rfl
  set R₂ := integralClosure R₁ E'
  haveI : IsFractionRing R₂ E' := integralClosure.isFractionRing_of_finite_extension (FractionRing R₁) E'
  let incl : E →ₐ[FractionRing R₁] E' := IntermediateField.inclusion (IntermediateField.le_normalClosure E)
  let eqv : E' ≃ₐ[R₂] FractionRing R₂ := (FractionRing.algEquiv R₂ E').symm
  have hloc' : IsLocalHom (algebraMap R₁ R₂) := by
    haveI : Module.Finite R₁ R₂ := RingHom.finite_algebraMap.1 hfe.2.2
    have : (Ideal.comap (algebraMap R₁ R₂) (maximalIdeal R₂)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal R₂)
    exact ((local_hom_tfae (algebraMap R₁ R₂)).out 1 5).mpr (IsLocalRing.eq_maximalIdeal this)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R₁ R₂, eqv.toRingHom.comp incl.toRingHom, hfe,
    ⟨hfe.1, hfe.2.1.comp hinj, hfe.2.2.comp hfin⟩, hloc', fun r => ?_⟩
  have h1 : incl (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ E' (algebraMap R₁ R₂ r) :=
    incl.commutes _
  change eqv (incl _) = _
  rw [h1]
  exact eqv.commutes _

end GlobalTheory.GalClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuotiStatement
section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient : ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H] [Module.Finite k H], p ^ Module.finrank k (Cot k H) ≤ Module.finrank k (H ⧸ frobKerIdeal p k H) := by
  first | exact @GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le | exact GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le | (intros; apply GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le <;> assumption)
end

