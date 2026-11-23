module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivialIffCoboundary
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem push_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩


omit [GrpObj A] [GrpObj A'] in
theorem lift_sq (sq : IsSquare φ φ₂) {T : Over S} {T' : Over S'} (χ : T.left ⟶ T'.left) (x' y' : T' ⟶ A')
    {Z : Over S} (ψ : T.left ⟶ Z.left) (x y : Z ⟶ A) (hx : χ ≫ x'.left ≫ φ = ψ ≫ x.left)
    (hy : χ ≫ y'.left ≫ φ = ψ ≫ y.left) : χ ≫ (lift x' y').left ≫ φ₂ = ψ ≫ (lift x y).left := by
  refine pullback.hom_ext (f := A.hom) (g := A.hom) ?_ ?_
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (fst A A).left = (ψ ≫ (lift x y).left) ≫ (fst A A).left
    rw [Category.assoc, Category.assoc, sq.1, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_fst, hx,
      Category.assoc, ← Over.comp_left, lift_fst]
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (snd A A).left = (ψ ≫ (lift x y).left) ≫ (snd A A).left
    rw [Category.assoc, Category.assoc, sq.2, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_snd, hy,
      Category.assoc, ← Over.comp_left, lift_snd]


omit [GrpObj A] [GrpObj A'] in
theorem diag_iso (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (H : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  obtain ⟨u, hu⟩ := H
  have e : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (𝟙 A')
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  exact LBIso.chartPull (chartPullId _) (chartPullOut P _ _ φ _ fun _ => e)
    (iso_linComb ((isGen_iff u).1 hu) (fun _ : PUnit => (lift (𝟙 A') (𝟙 A')).left) (fun _ => 1))

theorem nondeg_pull (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂))
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ((hn _ (pushHom h T x) ?_).trans (map_one _).symm)
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

def secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S') ⟶ A' :=
  Over.homMk (h.1.lift (f ≫ x.left) (𝟙 S') (by
    rw [Category.assoc, Over.w x]; exact (Category.comp_id _).trans (Category.id_comp _).symm)) (h.1.lift_snd _ _ _)

theorem secPull_left (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : (secPull h x).left ≫ φ = f ≫ x.left :=
  h.1.lift_fst _ _ _

theorem push_secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) (T : Over S') :
    pushHom h T (toUnit T ≫ secPull h x) = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (secPull h x).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, secPull_left, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem push_secPull' (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) :
    pushHom h _ (secPull h x) = toUnit _ ≫ x := by
  have e := push_secPull h x (𝟙_ (Over S'))
  rwa [toUnit_unit, Category.id_comp] at e

end GlobalTheory.SiegelPull

namespace GlobalTheory

open SiegelPull

theorem siegPre_pullback : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (c : SiegPre h M ζ s), f ≫ s = s' → (∃ c' : SiegPre h M ζ s', SiegPB c' c f) ∧ ∀ c' : SiegPre h M ζ s', SiegPB c' c f → c.Principal → c'.Principal := by
  intro h M o _ ζ S S' s s' f c hs
  refine ⟨?_, ?_⟩
  · obtain ⟨p⟩ := siegPairPB_nonempty c f
    refine ⟨{
      A := p.A
      ab := p.ab
      P := p.P
      isLB := p.isLB
      rig₁ := p.rig₁
      rig₂ := p.rig₂
      symm := p.symm
      lev := fun a => GlobalTheory.SiegelPull.secPull p.pb (c.lev a)
      lev_add := fun a b => push_injective p.pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', c.lev_add, MonObj.comp_mul])
      lev_tors := fun a => push_injective p.pb _ (by
        rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
      geom := fun k _ _ x β z hx hz => ?_ }, p.φ, p.φ₂, p.pb, p.sq, p.iso, fun a => secPull_left p.pb _⟩
    obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (push_injective p.pb (Over.mk x)).eq_iff, push_secPull, map_one]
      rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom p.pb (Over.mk x) g) (by
        have := congrArg (pushHom p.pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, push_injective p.pb _ ((push_secPull p.pb _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S S' c.A p.A f p.φ _ _ (pull_isLB c.isLB _) (pull_isLB p.isLB _) p.pb
        (diag_iso p.sq p.iso) (Over.mk x) M _ _ _ _ _
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b)
  · rintro c' ⟨φ, φ₂, pb, sq, iso, -⟩ ⟨h₁, h₂⟩
    exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
      (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricBundleTrivialConstantFamilyDualNumber
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.EpsSym
open GlobalTheory.KS.EpsBundle

theorem period_eq_zero {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {I : Type} (U : I → Set (Fin g → ℂ))
    (h : I → (Fin g → ℂ) → ℂ) (t : Fin g → ℂ) (a : I → I → (Fin g → ℂ) → ℂ)
    (ho : ∀ i, IsOpen (U i)) (hl : ∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) (hc : ∀ z, ∃ i, z ∈ U i)
    (hh : ∀ i, DifferentiableOn ℂ (h i) (U i) ∧
      ∀ (l : Λ), ∀ z ∈ U i, h i (z + l) = h i z + t ⬝ᵥ star (l : Fin g → ℂ))
    (ha : ∀ i i', DifferentiableOn ℂ (a i i') {z | -z ∈ U i ∧ z ∈ U i'})
    (hp : ∀ i i' (l : Λ) z, a i i' (z + l) = a i i' z)
    (hg : ∀ i i' m m' z, -z ∈ U i → z ∈ U i' → -z ∈ U m → z ∈ U m' →
      (h m (-z) - h i (-z)) - (h m' z - h i' z) = a i i' z - a m m' z) : t = 0 := by
  choose s hs using hc
  let F : I → I → (Fin g → ℂ) → ℂ := fun i i' z => a i i' z + h i (-z) - h i' z
  let v : (Fin g → ℂ) → ℂ := fun z => F (s (-z)) (s z) z
  have hv : ∀ i i' z, -z ∈ U i → z ∈ U i' → v z = F i i' z := fun i i' z h1 h2 => by
    have := hg i i' _ _ z h1 h2 (hs _) (hs _)
    simp only [v, F]
    linear_combination this
  have hO : ∀ i i', IsOpen {z | -z ∈ U i ∧ z ∈ U i'} := fun i i' =>
    ((ho i).preimage continuous_neg).inter (ho i')
  have hF : ∀ i i', DifferentiableOn ℂ (F i i') {z | -z ∈ U i ∧ z ∈ U i'} := fun i i' =>
    ((ha i i').add ((hh i).1.comp differentiableOn_id.neg fun z hz => hz.1)).sub
      ((hh i').1.mono fun z hz => hz.2)
  have hdiff : Differentiable ℂ v := fun z => by
    have hz : {w | -w ∈ U (s (-z)) ∧ w ∈ U (s z)} ∈ nhds z := (hO _ _).mem_nhds ⟨hs _, hs _⟩
    refine ((hF _ _).differentiableAt hz).congr_of_eventuallyEq ?_
    filter_upwards [hz] with w hw using hv _ _ w hw.1 hw.2
  have key := (GlobalTheory.entire_antilinear_periods_const g Λ hd hf v (-(t + t)) hdiff fun l z => by
    have e : -(z + (l : Fin g → ℂ)) = -z + ((-l : Λ) : Fin g → ℂ) := by
      rw [Submodule.coe_neg]; abel
    rw [hv (s (-z)) (s z) (z + l) (by rw [e]; exact hl _ _ _ (hs _)) (hl _ _ _ (hs _))]
    simp only [v, F]
    rw [e, (hh _).2 (-l) _ (hs _), (hh _).2 l _ (hs _), hp, Submodule.coe_neg, star_neg,
      dotProduct_neg, neg_dotProduct, add_dotProduct]
    ring).1
  funext b
  have := congrFun key b
  simp only [Pi.neg_apply, Pi.add_apply, Pi.zero_apply] at this ⊢
  linear_combination (-1 / 2 : ℂ) * this

variable {Y Y' : Scheme.{0}} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}

theorem appLE_one_add_eps {ν' : Y' ⟶ Y'} {ν : Y ⟶ Y} (h₁ : ν' ≫ π = π) (h₂ : ν' ≫ ρ = ρ ≫ ν)
    {W W₁ : Y'.Opens} {O O₁ : Y.Opens} (hW : W₁ ≤ ν' ⁻¹ᵁ W) (h : W ≤ ρ ⁻¹ᵁ O) (hO : O₁ ≤ ν ⁻¹ᵁ O)
    (h' : W₁ ≤ ρ ⁻¹ᵁ O₁) (x : Γ(Y, O)) :
    (ν'.appLE W W₁ hW).hom (1 + constFn π W DualNumber.eps * (ρ.appLE O W h).hom x) =
      1 + constFn π W₁ DualNumber.eps * (ρ.appLE O₁ W₁ h').hom ((ν.appLE O O₁ hO).hom x) := by
  have gen : ∀ {Z : Scheme.{0}} (f f' : Y' ⟶ Z) (_ : f = f') (V : Z.Opens) e e',
      f.appLE V W₁ e = f'.appLE V W₁ e' := by
    intro Z f f' hf V e e'
    subst hf
    rfl
  rw [map_add (f := _), map_mul, map_one]
  congr 2
  · exact congrArg (fun f => CommRingCat.Hom.hom f
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps))
      ((Scheme.Hom.appLE_comp_appLE ν' π ⊤ W W₁ (fun _ _ => trivial) hW).trans (gen _ _ h₁ _ _ _))
  · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE, gen _ _ h₂]

theorem val_mul_inv {B : Type} [CommRing B] (e x y : B) (he : e * e = 0) (u : Fin 2 → Bˣ)
    (hu : (u 0 : B) = 1 + e * x) (hv : (u 1 : B) = 1 + e * y) :
    ((∏ k, u k ^ (![1, -1] : Fin 2 → ℤ) k : Bˣ) : B) = 1 + e * (x - y) := by
  rw [Fin.prod_univ_two]
  change ((u 0 ^ (1 : ℤ) * u 1 ^ (-1 : ℤ) : Bˣ) : B) = _
  rw [zpow_one, zpow_neg_one, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hu, hv]
  linear_combination (-(x - y) * y) * he

variable {q : Y ⟶ Sp ℂ} {j : Y ⟶ Y'}

theorem cocycle_val (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (Q : LB Y')
    (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (hQ : Q.IsLB)
    (hg : ∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))),
      (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i'))
    (i i' i'' : Q.ι) (x : Sp ℂ ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i' ⊓ Q.U i''))) :
    valAt' x _ (k i i') + valAt' x _ (k i' i'') = valAt' x _ (k i i'') := by
  obtain ⟨hO, -, hD⟩ := _root_.GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have le : ∀ W : Y'.Opens, W ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ W) := fun W => (hO W).ge
  have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i' ⊓ Q.U i'') ≤ j ⁻¹ᵁ (Q.U i ⊓ Q.U i') := fun _ hy => hy.1
  have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i' ⊓ Q.U i'') ≤ j ⁻¹ᵁ (Q.U i' ⊓ Q.U i'') := fun _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i' ⊓ Q.U i'') ≤ j ⁻¹ᵁ (Q.U i ⊓ Q.U i'') := fun _ hy => ⟨hy.1.1, hy.2⟩
  have E : resG Y' (inf_le_left : Q.U i ⊓ Q.U i' ⊓ Q.U i'' ≤ _) (Q.g i i').val *
      resG Y' (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (Q.g i' i'').val =
      resG Y' (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (Q.g i i'').val :=
    congrArg Units.val (hQ.cocycle i i' i'')
  rw [hg _ _ (le _), hg _ _ (le _), hg _ _ (le _)] at E
  simp only [map_add (f := _), map_mul, map_one, res_constFn'] at E
  rw [res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _), res_appLE ρ _ l₃ _ (le _)] at E
  have := (uniq (ρ.appLE _ _ (le (Q.U i ⊓ Q.U i' ⊓ Q.U i''))).hom _
    (fun F => decomp π ρ _ (hD _) _ (hO _) (le _) F) (a := 1) (a' := 1)
    (b := resG Y l₁ (k i i') + resG Y l₂ (k i' i'')) (b' := resG Y l₃ (k i i'')) (by
      rw [map_one, map_add (f := _)]
      linear_combination E - ((ρ.appLE _ _ (le _)).hom (resG Y l₁ (k i i')) *
        (ρ.appLE _ _ (le _)).hom (resG Y l₂ (k i' i''))) * eps_sq π (Q.U i ⊓ Q.U i' ⊓ Q.U i''))).2
  rw [← valAt'_res x l₁ _ hx, ← valAt'_res x l₂ _ hx, ← valAt'_res x l₃ _ hx, ← valAt'_add, this]

theorem odd_part_coboundary (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (Q : LB Y')
    (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (hQ : Q.IsLB)
    (hg : ∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))),
      (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i'))
    {ν' : Y' ⟶ Y'} {ν : Y ⟶ Y} (h₁ : ν' ≫ π = π) (h₂ : ν' ≫ ρ = ρ ≫ ν) (h₃ : j ≫ ν' = ν ≫ j)
    (ht : ∃ t : (LB.LinComb Q (K := Fin 2) ![ν', 𝟙 Y'] ![1, -1]).Gen, t.IsGen) :
    ∃ (W : Q.ι → Q.ι → Y.Opens) (a : ∀ i i', Γ(Y, W i i')),
      (∀ i i', W i i' = ν ⁻¹ᵁ (j ⁻¹ᵁ Q.U i) ⊓ j ⁻¹ᵁ Q.U i') ∧
      ∀ i i' m m' (x : Sp ℂ ⟶ Y), ⊤ ≤ x ⁻¹ᵁ W i i' → ⊤ ≤ x ⁻¹ᵁ W m m' →
        valAt' (x ≫ ν) _ (k i m) - valAt' x _ (k i' m') = valAt' x _ (a i i') - valAt' x _ (a m m') := by
  obtain ⟨hO, -, -⟩ := _root_.GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have le : ∀ W : Y'.Opens, W ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ W) := fun W => (hO W).ge
  let Q' := LB.LinComb Q (K := Fin 2) ![ν', 𝟙 Y'] ![1, -1]
  have hW : ∀ J : Fin 2 → Q.ι, j ⁻¹ᵁ Q'.U J = ν ⁻¹ᵁ (j ⁻¹ᵁ Q.U (J 0)) ⊓ j ⁻¹ᵁ Q.U (J 1) := fun J => by
    rw [← Scheme.Hom.comp_preimage, ← h₃]
    ext y
    exact Set.mem_iInter.trans Fin.forall_fin_two
  have l₀ : ∀ J J' : Fin 2 → Q.ι, j ⁻¹ᵁ (Q'.U J ⊓ Q'.U J') ≤ ν ⁻¹ᵁ (j ⁻¹ᵁ (Q.U (J 0) ⊓ Q.U (J' 0))) :=
    fun J J' y hy => ⟨((hW J).le hy.1).1, ((hW J').le hy.2).1⟩
  have l₁ : ∀ J J' : Fin 2 → Q.ι, j ⁻¹ᵁ (Q'.U J ⊓ Q'.U J') ≤ (𝟙 Y) ⁻¹ᵁ (j ⁻¹ᵁ (Q.U (J 1) ⊓ Q.U (J' 1))) :=
    fun J J' y hy => ⟨((hW J).le hy.1).2, ((hW J').le hy.2).2⟩
  obtain ⟨a, ha⟩ := (trivial_iff_coboundary Y Y' q π ρ j hp hj hq Q'
    (fun J J' => (ν.appLE _ _ (l₀ J J')).hom (k (J 0) (J' 0)) -
      (Scheme.Hom.appLE (𝟙 Y) _ _ (l₁ J J')).hom (k (J 1) (J' 1))) (LB.isLB_linComb hQ _ _) fun J J' h => by
      rw [map_sub]
      have m : ∀ n, Q'.U J ⊓ Q'.U J' ≤ (![ν', 𝟙 Y'] : Fin 2 → _) n ⁻¹ᵁ (Q.U (J n) ⊓ Q.U (J' n)) :=
        fun n y hy => ⟨LB.wchart_le Q _ J n hy.1, LB.wchart_le Q _ J' n hy.2⟩
      refine val_mul_inv _ _ _ (eps_sq π _) _ ?_ ?_
      · refine Eq.trans ?_ (appLE_one_add_eps h₁ h₂ (m 0) (le _) _ h _)
        rw [← hg]
        rfl
      · refine Eq.trans ?_ (appLE_one_add_eps (ν' := 𝟙 Y') (Category.id_comp _) (by simp) (m 1) (le _) _ h _)
        rw [← hg]
        rfl).1 ht
  refine ⟨fun i i' => j ⁻¹ᵁ Q'.U ![i, i'], fun i i' => a ![i, i'], fun i i' => hW _, ?_⟩
  intro i i' m m' x hx hx'
  have hxx : ⊤ ≤ x ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U ![i, i'] ⊓ Q'.U ![m, m'])) := fun p hp => ⟨hx hp, hx' hp⟩
  have E := congrArg (valAt' x _) (ha ![i, i'] ![m, m'])
  rw [valAt'_sub, valAt'_sub, valAt'_res _ _ _ hxx, valAt'_res _ _ _ hxx, valAt'_appLE _ _ _ _ _ _ hxx,
    valAt'_appLE _ _ _ _ _ _ hxx, Category.comp_id] at E
  exact E

theorem gen_of_sym (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (Q : LB A'.left) (h : Out.Sym A' Q) :
    ∃ t : (LB.LinComb Q (K := Fin 2) ![(GrpObj.inv : A' ⟶ A').left, 𝟙 A'.left] ![1, -1]).Gen, t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := h (IsLocalRing.closedPoint (DualNumber ℂ))
  have hU' : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  subst hU'
  let s : A'.left ⟶ (A'.hom ⁻¹ᵁ ⊤).toScheme := A'.left.topIso.inv
  have hs : s ≫ (A'.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := A'.left.topIso.inv_hom_id
  have e : (fun k => s ≫ (![(A'.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : A' ⟶ A').left, (A'.hom ⁻¹ᵁ ⊤).ι] :
      Fin 2 → _) k) = ![(GrpObj.inv : A' ⟶ A').left, 𝟙 A'.left] := by
    funext k
    fin_cases k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _))
    · exact hs
  rw [← e]
  exact ⟨_, DVR.pullGen_isGen_of_isGen _ _ t ht s⟩

theorem trivial_of_symmetric : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (Q : LB A'.left) (k : ∀ i i', Γ(P₀.A.left, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn A'.hom _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → Out.Sym A' Q → ∃ t : Q.Gen, t.IsGen := by
  intro laws P₀ u Hm χ hu A' _ ρ j hc Q k hQ hg hs
  obtain ⟨g₁, g₂, hj⟩ := hc
  have hq := g₂.1.w
  let U : Q.ι → Set (Fin P₀.g → ℂ) := fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (j ⁻¹ᵁ Q.U i)}
  have hper : ∀ z (l : u.Λ), u.ex (z + l) = u.ex z := fun z l => CubeValues.ex_add_period u z l l.2
  have hcov : ⨆ i, j ⁻¹ᵁ Q.U i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hQ.cover]; rfl
  have ho : ∀ i, IsOpen (U i) := fun i => (u.hol _ 0).1
  have hl : ∀ i (l : u.Λ) z, z ∈ U i → z + l ∈ U i := fun i l z hz => by
    simp only [U, Set.mem_setOf_eq, hper]; exact hz
  have hcv : ∀ z, ∃ i, z ∈ U i := fun z => by
    have h : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, j ⁻¹ᵁ Q.U i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  have hin : ∀ {i i' z}, z ∈ U i → z ∈ U i' → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i')) :=
    fun h h' p hp => ⟨h hp, h' hp⟩
  obtain ⟨t, h, hh, hk⟩ := GlobalTheory.holomorphic_periodic_cocycle_coboundary P₀.g u.Λ u.discrete u.full Q.ι U
    (fun i i' z => valAt' (u.ex z).left _ (k i i')) ho hl hcv
    (fun i i' => (u.hol _ (k i i')).2.mono fun z hz => hin hz.1 hz.2)
    (fun i i' l z _ => by simp only [hper])
    (fun i i' i'' z hz => cocycle_val g₁.1 hj hq Q k hQ hg i i' i'' _
      fun p hp => ⟨⟨hz.1.1 hp, hz.1.2 hp⟩, hz.2 hp⟩)
  obtain ⟨W, a, hW, ha⟩ := odd_part_coboundary g₁.1 hj hq Q k hQ hg (Over.w (GrpObj.inv : A' ⟶ A'))
    (PolBaseChange.inv_comm g₁) (PolBaseChange.inv_comm g₂).symm (gen_of_sym A' Q hs)
  have hW' : ∀ {i i' z}, -z ∈ U i → z ∈ U i' → ⊤ ≤ (u.ex z).left ⁻¹ᵁ W i i' := fun {i i' z} h h' => by
    rw [hW, top_le_preimage_inf, ← top_le_preimage_comp, SymmetricSemicharacter.ex_neg_left]
    exact ⟨h, h'⟩
  have ht : t = 0 := period_eq_zero u.Λ u.discrete u.full U h t
    (fun i i' z => valAt' (u.ex z).left _ (a i i')) ho hl hcv hh
    (fun i i' => (u.hol _ (a i i')).2.mono fun z hz => hW' hz.1 hz.2)
    (fun i i' l z => by simp only [hper])
    (fun i i' m m' z h₁ h₂ h₃ h₄ => by
      have E := ha i i' m m' _ (hW' h₁ h₂) (hW' h₃ h₄)
      rw [SymmetricSemicharacter.ex_neg_left] at E
      rw [← hk i m (-z) ⟨h₁, h₃⟩, ← hk i' m' z ⟨h₂, h₄⟩]
      exact E)
  subst ht
  choose b hb using algebraic_coboundary_of_holomorphic_coboundary laws P₀ u Hm χ hu Q.ι
    (fun i => j ⁻¹ᵁ Q.U i) (fun i i' => k i i') h hcov
    (fun i => ⟨(hh i).1, fun l z hz => by rw [(hh i).2 l z hz, zero_dotProduct, add_zero]⟩)
    (fun i i' z hz => hk i i' z ⟨fun p hp => (hz hp).1, fun p hp => (hz hp).2⟩)
  refine (trivial_iff_coboundary _ _ _ _ ρ j g₁.1 hj hq Q k hQ hg).2 ⟨fun i => - b i, fun i i' => ?_⟩
  refine (GlobalTheory.existsUnique_section_of_locally_regular P₀ u Hm χ hu (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))
    (fun z => valAt' (u.ex z).left _ (k i i'))
    (fun z hz => ⟨_, k i i', le_rfl, hz, fun _ _ => rfl⟩)).unique (fun _ _ => rfl) fun z hz => ?_
  have z₁ : z ∈ U i := fun p hp => (hz hp).1
  have z₂ : z ∈ U i' := fun p hp => (hz hp).2
  rw [valAt'_sub, valAt'_res _ _ _ hz, valAt'_res _ _ _ hz, valAt'_neg, valAt'_neg, hb i z z₁, hb i' z z₂]
  exact ((hk i i' z ⟨z₁, z₂⟩).trans (by ring)).symm

end GlobalTheory.KS.EpsSym
end
end

