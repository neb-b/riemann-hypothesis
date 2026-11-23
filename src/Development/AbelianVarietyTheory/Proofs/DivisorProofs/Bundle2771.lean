module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFunctionsExistsGlobalFunctionOfThickenings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FormalFunctions

theorem exists_of_thick : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ (X : Over (Sp A)), IsProper X.hom → ∀ f : ∀ e : ℕ, Γ((thickObj A I e X).left, ⊤), (∀ e, (thickMap A I e X).appTop.hom (f (e + 1)) = f e) → ∃ s : Γ(X.left, ⊤), ∀ e, (pullback.fst X.hom (thick A I e)).appTop.hom s = f e := by
  intro A _ _ I hI X hX f hf

  let Z : Over (Sp A) := Over.mk (𝔸(Unit; Sp A) ↘ Sp A)
  have hZs : IsSeparated Z.hom := by dsimp [Z]; infer_instance
  have hZl : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  have hZq : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let F : ∀ e, (thickObj A I e X).left ⟶ Z.left := fun e =>
    AffineSpace.homOfVector (pullback.fst X.hom (thick A I e) ≫ X.hom) (fun _ => f e)
  have hβ : ∀ e, thickMap A I e X ≫ pullback.fst X.hom (thick A I (e + 1)) =
      pullback.fst X.hom (thick A I e) := by
    intro e
    unfold thickMap
    first
      | (simp only [pullback.map, pullback.lift_fst, Category.comp_id]; done)
      | exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      | simp [pullback.map]
  have hF₁ : ∀ e, F e ≫ Z.hom = (thickObj A I e X).hom ≫ thick A I e := by
    intro e
    dsimp [F, Z]
    rw [AffineSpace.homOfVector_over]
    exact pullback.condition
  have hF₂ : ∀ e, thickMap A I e X ≫ F (e + 1) = F e := by
    intro e
    dsimp [F]
    rw [AffineSpace.comp_homOfVector, ← Category.assoc, hβ e]
    congr 1
    funext _
    exact hf e
  obtain ⟨g, hg, -⟩ := GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms A I hI X Z hX hZs hZl hZq
    (fun e => thickObj A I e X) (fun e => thickMap A I e X) (fun e => pullback.fst X.hom (thick A I e))
    (fun e => IsPullback.of_hasPullback _ _) hβ F hF₁ hF₂
  refine ⟨g.left.appTop (AffineSpace.coord (Sp A) ()), fun e => ?_⟩
  have h := congrArg (fun φ => φ.appTop (AffineSpace.coord (Sp A) ())) (hg e)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  rw [h]
  exact AffineSpace.homOfVector_appTop_coord _ _ _

end GlobalTheory.FormalFunctions
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubical
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Sep.LiesCube

theorem alternating_alg {M : Type} [CommGroup M] (u e w f t : Finset (Fin 3) → M) (a b c : M)
    (v : ∀ S, u S * e S * w S = f S * t S)
    (c₁ : f {0, 1, 2} * f {0} * f {1} * f {2} * (t {0, 1, 2} * t {0} * t {1} * t {2}) * b =
      a * (f {0, 1} * f {0, 2} * f {1, 2} * f ∅) * (t {0, 1} * t {0, 2} * t {1, 2} * t ∅))
    (c₂ : u {0, 1, 2} * u {0} * u {1} * u {2} * c = a * (u {0, 1} * u {0, 2} * u {1, 2} * u ∅)) :
    e {0, 1, 2} * e {0} * e {1} * e {2} * (w {0, 1, 2} * w {0} * w {1} * w {2}) * b =
      c * (e {0, 1} * e {0, 2} * e {1, 2} * e ∅) * (w {0, 1} * w {0, 2} * w {1, 2} * w ∅) := by
  have E := fun {p q : M} (e : p = q) => congrArg Additive.ofMul e
  have v₀ := E (v ∅); have v₁ := E (v {0}); have v₂ := E (v {1}); have v₃ := E (v {2})
  have v₄ := E (v {0, 1}); have v₅ := E (v {0, 2}); have v₆ := E (v {1, 2}); have v₇ := E (v {0, 1, 2})
  have d₁ := E c₁; have d₂ := E c₂
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) v₁ + v₂ + v₃ + v₇ - v₀ - v₄ - v₅ - v₆ + d₁ - d₂

theorem cube_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (g : Finset (Fin 3) → GtPtF D.toPre (FractionRing V)) (w : ∀ S, Frm D.toPre (FractionRing V) 1 (g S).b) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (e : ∀ S, FrAt (x S)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → (∀ S, (∃ o, GtPtF.IsNsmul N (g S) o ∧ o.IsZero) ∧ (w S).IsGen ∧ (e S).IsGen ∧ LiesOver U.toUnifPre w₀ (g S) (w S) (x S) (e S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good D.toPre.P.L z JB → @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {2}) (𝟙 _) z JA) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {2}) (𝟙 _) z JB)) * cubV D.toPre.cub z JB (g {0}).b (g {1}).b (g {2}).b = @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e ∅) (𝟙 _) z JA)) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w ∅) (𝟙 _) z JB)) := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ N hN ρ hρ c g w x e hx₀ hx₁ hx₂ hx₃ hx₄ hS z JA JB hJA hJB
  choose h g' f t hF hE hP hf ht hT using fun S => GlobalTheory.T.exists_integral_data_framed_torsion_point_torus_ext V hV D A G hG U w₀ hw₀ N hN (g S) (w S) (x S) (e S)
    (hS S).1 (hS S).2.1 (hS S).2.2.1 (hS S).2.2.2
  have hm : ∀ S T S', x S' = x S * x T → h S' = h S * h T ∧ (g' S').b = (g' S).b * (g' T).b := fun S T S' hx => by
    have a := GlobalTheory.T.uniformisation_sections_extending_points_multiply V hV D A G hG U (x S) (x T) (h S) (h T) (h S') (hE S) (hE T) (hx ▸ hE S')
    exact ⟨a, _root_.GlobalTheory.Poinc.Sep.FormalMul.b_mul V hV D A G hG U (h S) (h T) (g' S) (g' T) (g' S') (hF S) (hF T) (a ▸ hF S')⟩
  have m₀ := hm ∅ ∅ ∅ (by rw [hx₀, _root_.mul_one])
  have m₁ := hm _ _ _ hx₁
  have m₂ := hm _ _ _ hx₂
  have m₃ := hm _ _ _ hx₃
  have m₄ := hm {0, 1} {2} {0, 1, 2} (by rw [hx₄, hx₁])
  have a₀ : h ∅ = 1 := mul_eq_left.1 m₀.1.symm
  have b₀ : (g' ∅).b = 1 := mul_eq_left.1 m₀.2.symm
  have a₄ : h {0, 1, 2} = h {0} * h {1} * h {2} := m₄.1.trans (by rw [m₁.1])
  have b₄ : (g' {0, 1, 2}).b = (g' {0}).b * (g' {1}).b * (g' {2}).b := m₄.2.trans (by rw [m₁.2])
  obtain ⟨JG, hJG⟩ : ∃ J, Good U.LG.L z J := by
    choose I hI using fun χ : _ ⟶ G.left => exists_chart U.LG.isLB (χ z)
    exact ⟨I, hI⟩
  have v := fun S => GlobalTheory.T.torsionPointFrame_mul_eq_integralGenerators V hV D A G hG U w₀ hw₀ N hN (g S) (w S) (x S) (e S)
    (hS S).1 (hS S).2.1 (hS S).2.2.1 (hS S).2.2.2 (h S) (g' S) (f S) (t S) (hF S) (hE S) (hP S) (hf S) (ht S) (hT S)
    z JA JG JB hJA hJG hJB
  have c₁ := GlobalTheory.T.integral_frames_respect_cubical_structures V hV D A G hG U h g' f t a₀ m₁.1 m₂.1 m₃.1 a₄ b₀ m₁.2 m₂.2 m₃.2 b₄ hF hf ht hT z JG JB hJG hJB
  have c₂ := GlobalTheory.T.uniformisation_cubical_structure_generic_fibre V hV D A G hG U w₀ hw₀ ρ hρ c x h hx₀ hx₁ hx₂ hx₃ hx₄ a₀ m₁.1 m₂.1 m₃.1 a₄ hE z JA JG hJA hJG
  have hb : ∀ S, toUnit (TF (R := V) (FractionRing V)) ≫ (g' S).b = (g S).b := fun S =>
    Over.OverMorphism.ext (hP S).1.symm
  rw [hb, hb, hb] at c₁
  exact alternating_alg (M := ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ) _
    (fun S => val (Z := (TF (R := V) (FractionRing V)).left) (e S) (𝟙 _) z JA) (fun S => val (w S) (𝟙 _) z JB)
    (fun S => val (f S) (toUnit (TF (R := V) (FractionRing V))).left z JG)
    (fun S => val (t S) (toUnit (TF (R := V) (FractionRing V))).left z JB) _ _ _ v c₁ c₂

end GlobalTheory.Poinc.Sep.LiesCube
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.GradedForm

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}

def lineGram (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (x : Root m) (y z : CxPts X.str σ) :
    Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => ((grD (gramAt E H x.1 y z) x.2 : ℝ) : ℂ)

variable [Finite ι] {E : Fr (ratOf X) m m} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}

theorem grD_pos (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) : 0 < grD (gramAt E H x.1 y y) x.2 :=
  ((_root_.GlobalTheory.ChernCalc.ldPart_posDef_spec _ _ (h.posDef y _ (E.nonempty (under y)).choose_spec x.1)).2.1 x.2).1

theorem lineGram_smooth (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) :
    SmoothUnitAt (atlas X σ) (lineGram E H x y) y := by
  refine ⟨?_, fun c hc => ?_⟩
  · rw [Matrix.det_fin_one]
    exact isUnit_iff_ne_zero.2 (Complex.ofReal_ne_zero.2 (grD_pos h x y).ne')
  · filter_upwards [(_root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m m E H h y _ (E.nonempty (under y)).choose_spec x.1).2 c hc] with v hv
    intro a b
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp v ((_root_.GlobalTheory.ChernCalc.ldPart_grD_smooth _ _ _ v hv.1 hv.2).2 x.2)

theorem isGramPair_lineGram (h : IsMetricFr E H) (x : Root m) :
    IsGramPair (atlas X σ) (lineGram E H x) (lineGram E H x) := by
  refine ⟨fun y => ⟨lineGram_smooth h x y, lineGram_smooth h x y⟩, fun y => ?_⟩
  have hy := (E.nonempty (under y)).choose_spec
  filter_upwards [_root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m m E y _ hy] with z hyz
  have hz := (E.nonempty (under z)).choose_spec
  set A := (E.nonempty (under y)).choose with hA
  set B := (E.nonempty (under z)).choose with hB
  have hP := (Fr.mem_iff hyz).1 hz
  have hhol := _root_.GlobalTheory.ChernCalc.holUnitAt_ratVal F σ X _ ((B * A⁻¹) x.1) z (fun i j => mem_O_ratOf.1 ((hP x.1).1 i j)) (hP x.1).2.1
    (mem_O_ratOf.1 (hP x.1).2.2.1)
  have hval : ∀ w : CxPts X.str σ, A ∈ E.S (under w) → B ∈ E.S (under w) →
      Par m ⊤ ((B * A⁻¹).map (ratVal · w)) := fun w h1 h2 => by
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom w
    exact ((Fr.mem_iff h1).1 h2).map_of _ ψ hψ
  let T : CxPts X.str σ → Matrix (Fin 1) (Fin 1) ℂ := fun w _ _ => ratVal ((B * A⁻¹) x.1 x.2 x.2) w
  have hT : HolUnitAt (atlas X σ) T z := by
    refine ⟨?_, fun c hc _ _ => hhol.2 c hc x.2 x.2⟩
    rw [Matrix.det_fin_one]
    have hp := hval z hyz hz x.1
    have hd := hp.2.1
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hp.2.2.2 i j i.2 hij)] at hd
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hd x.2 (Finset.mem_univ _))
  refine ⟨T, T, T, hT, hT, hT, ?_⟩
  filter_upwards [_root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m m E z _ hyz, _root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m m E z _ hz] with w h1 h2
  rw [and_self]
  have hp := hval w h1 h2 x.1
  have e := (_root_.GlobalTheory.ChernCalc.ldPart_conj_lower _ _ _ (h.posDef w A h1 x.1) (fun i j hij => hp.2.2.2 i j i.2 hij)
    (isUnit_iff_ne_zero.2 hp.2.1)).2 x.2
  rw [← h.trans w A h1 B h2 x.1] at e
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply]
  change ((grD (H B w x.1) x.2 : ℝ) : ℂ) = ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2) * ((grD (H A w x.1) x.2 : ℝ) : ℂ) *
    star ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2)
  rw [e, mul_right_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem chernFld_lineGram (h : IsMetricFr E H) (x : Root m) :
    chernFld (atlas X σ) (lineGram E H x) 1 = grF E H x := by
  funext p
  have hs := ((lineGram_smooth h x p.pt).2 p.1.1 p.2).self_of_nhds
  have e := _root_.GlobalTheory.ChernTri.chernAt_tri _ 1 (fun v => lineGram E H x p.pt (p.ch.symm v))
    (fun _ v => grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2) p.crd hs
    (fun _ => by
      have : p.ch.symm p.crd = p.pt := p.ch.left_inv p.2
      rw [this]; exact grD_pos h x _)
    (Eventually.of_forall fun v => ⟨fun i j hij => absurd (Subsingleton.elim i j) hij.ne, fun _ => rfl⟩) 1
  refine e.trans ?_
  rw [esymm_one, Fin.sum_univ_one, aeval_X]
  rfl

theorem dbarCoh_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ x : Root m, DbarCoh (atlas X σ) (grF E H x) (grF E H x) := by
  intro F _ σ X ι _ m E H h x
  rw [← chernFld_lineGram h x]
  exact _root_.GlobalTheory.ChernCalc.dbarCoh_chernFld _ _ _ _ _ _ (isGramPair_lineGram h x) 1

end GlobalTheory.ChernCalc.GradedForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointsDivisible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pt_comp_id_pow {K : Type} [Field K] (A : AbVar K) (x : A.Pt) (n : ℕ) :
    x ≫ (𝟙 A.X) ^ n = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ k ih => rw [pow_succ, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem pt_divisible : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), n ≠ 0 → ∀ x : A.Pt, ∃ y : A.Pt, y ^ n = x := by
  intro K _ A n hn x
  have hz : ((n : ℤ)) ≠ 0 := by exact_mod_cast hn
  have hiso := (_root_.GlobalTheory.MulIsogeny.mul_isogeny K A (n : ℤ) hz).1
  have hs : Function.Surjective (ptMap ((n : ℤ) • 𝟙 A)) := (_root_.GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective K A A _).1 hiso.2
  obtain ⟨y, hy⟩ := hs x
  refine ⟨y, ?_⟩
  rw [← hy, ptMap_apply, natCast_zsmul, nsmul_hom, id_hom, pt_comp_id_pow]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmooth
section
open AlgebraicGeometry MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodTop

theorem goodTopChernForm : GlobalTheory.Published.GoodTopChernForm := by
  intro F _ σ X m E O H H₀ hH hG hH₀ t ht
  rw [hasChernIntegral_iff] at ht ⊢
  haveI := X.smooth_str
  haveI : SecondCountableTopology (CxPts X.str σ) := inferInstance
  have hp : ∀ y : CxPts X.str σ, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := fun y => by
    by_cases hy : y ∈ ptsIn X.str σ O
    · exact _root_.GlobalTheory.GoodTop.exists_goodPatch_of_mem E O H hH y hy
    · exact _root_.GlobalTheory.GoodTop.exists_goodPatch E O H hG y hy
  choose e S A W c hyW hP using hp
  obtain ⟨s, ρ, hρ, hsupp, hsum⟩ := _root_.GlobalTheory.GoodTop.exists_cInf_partition W fun y => (hP y).isOpen.mem_nhds (hyW y)
  choose a b ha hb hab using fun i : s => _root_.GlobalTheory.GoodTop.hasInt_patch_transgression E O H H₀ hH hH₀ (hP i) (hρ i) (hsupp i)
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hm : ∀ U : X.X.Opens, MeasurableSet (ptsIn X.str σ U) := fun U => (isOpen_ptsIn U).measurableSet
  have hc : ∀ i, Continuous (ρ i) := fun i => continuous_iff_continuousAt.2 fun y => (hρ i y).continuousAt
  have h₁ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) (∑ i, a i) := by
    refine _root_.GlobalTheory.GoodTop.hasInt_congr_on _ (hm O) (fun i y _ _ => ?_)
      (_root_.GlobalTheory.GoodTop.hasInt_sum _ hd hcov (hm O) (fun i => _root_.GlobalTheory.GoodTop.isTopForm_mul_topDens E O H hH (hc i)) ha)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₂ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H₀) (ptsIn X.str σ ⊤) (∑ i, b i) := by
    refine _root_.GlobalTheory.GoodTop.hasInt_congr_on _ (hm ⊤) (fun i y _ _ => ?_)
      (_root_.GlobalTheory.GoodTop.hasInt_sum _ hd hcov (hm ⊤) (fun i => _root_.GlobalTheory.GoodTop.isTopForm_mul_topDens E ⊤ H₀ hH₀ (hc i)) hb)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₃ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun _ _ => 0) (ptsIn X.str σ O) (∑ i, (a i - b i)) :=
    _root_.GlobalTheory.GoodTop.hasInt_congr_on _ (hm O) (fun i y _ hy => _root_.GlobalTheory.GoodTop.sum_corrDens_eq_zero E O H H₀ ρ hρ hsum i y hy)
      (_root_.GlobalTheory.GoodTop.hasInt_sum _ hd hcov (hm O) (fun i => _root_.GlobalTheory.GoodTop.isTopForm_corrDens E O H H₀ hH hH₀ (hρ i)) hab)
  have e₂ : ∑ i, b i = t := h₂.2.symm.trans ht.2
  have e₃ : ∑ i, (a i - b i) = 0 := h₃.2.symm.trans (_root_.GlobalTheory.GoodTop.hasInt_zero _ _).2
  rw [Finset.sum_sub_distrib, sub_eq_zero, e₂] at e₃
  exact e₃ ▸ h₁

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDualRepresentativeOfRelAmpleNoetherian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualPol

theorem hasRepAF_of_relAmple : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → HasRepAF A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg L hL ha
  obtain ⟨B, P, q, hP, hgood, hfa, hfin, hfl, hsu, hF, hK⟩ := _root_.GlobalTheory.DualQuot.exists_quotient_lam R A g hA hg L hL ha
  have hinj : Inj A P := _root_.GlobalTheory.DualCon.inj_of_quotient R A g hA hg L hL ha B P q hP hfin hfl hsu hF hK
  have hex : ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
      ∃ x : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ x)) := by
    intro T N hN
    obtain ⟨H, h, x, hhf, hhs, hhq, hx⟩ := _root_.GlobalTheory.DualCover.exists_cover R A g hA hg L hL ha T N hN
    have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H),
        evc hP.isLB a (y ≫ x ≫ q) = evc hN.isLB a (y ≫ h) := by
      intro Y a y
      rw [hx, ← Category.assoc, hF]
    have hc : ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ H.left), g₁ ≫ h.left = g₂ ≫ h.left →
        g₁ ≫ (x ≫ q).left = g₂ ≫ (x ≫ q).left := by
      intro Z g₁ g₂ e
      let Z' : Over (Sp R) := Over.mk (g₁ ≫ H.hom)
      have e2 : g₂ ≫ H.hom = g₁ ≫ H.hom := by
        rw [← Over.w h, ← Category.assoc, ← e, Category.assoc]
      let k₁ : Z' ⟶ H := Over.homMk g₁ rfl
      let k₂ : Z' ⟶ H := Over.homMk g₂ e2
      have hkh : k₁ ≫ h = k₂ ≫ h := Over.OverMorphism.ext e
      have hs : Same A P P (k₁ ≫ x ≫ q) (k₂ ≫ x ≫ q) := by
        rw [same_iff hP.isLB hP.isLB]
        have e₁ := key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₁)
        have e₂ := key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₂)
        simp only [Category.assoc] at e₁ e₂
        rw [e₁, e₂, hkh]
      have := congrArg (fun t => t.left) (hinj Z' _ _ hs)
      simpa [k₁, k₂] using this
    haveI : Flat h.left := hhf
    haveI : Surjective h.left := hhs
    haveI : QuasiCompact h.left := hhq
    let d : T.left ⟶ B.left := EffectiveEpi.desc h.left (x ≫ q).left hc
    have hd : h.left ≫ d = (x ≫ q).left := EffectiveEpi.fac h.left (x ≫ q).left hc
    have hdB : d ≫ B.hom = T.hom := by
      rw [← cancel_epi h.left, ← Category.assoc, hd, Over.w (x ≫ q), Over.w h]
    let xT : T ⟶ B := Over.homMk d hdB
    have hxT : h ≫ xT = x ≫ q := Over.OverMorphism.ext hd
    refine ⟨xT, (same_id_iff hN.isLB hP.isLB xT).1 ?_⟩
    refine _root_.GlobalTheory.DualCon.same_of_fpqc (Sp R) A hA T B T H N P hN hP (𝟙 T) xT h hhf hhs hhq ?_
    rw [same_iff hN.isLB hP.isLB, Category.comp_id, hxT, key]
  refine ⟨B, toUnit B, P, ⟨hP, fun T t N hN ↦ ?_⟩, hgood, hfa⟩
  obtain ⟨x, hx⟩ := hex T N hN
  refine ⟨x, ⟨toUnit_unique _ _, hx⟩, fun y hy ↦ hinj T y x ?_⟩
  have h1 := (cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hy.2
  have h2 := (cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hx
  exact (cls_eq_iff (pull_isLB hP.isLB _) (pull_isLB hP.isLB _)).1 (h1.symm.trans h2)

end GlobalTheory.DualPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_torsionFree : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℤ) (f : A ⟶ B), n ≠ 0 → n • f = 0 → f = 0 := by
  intro K _ A B n f hn h
  have hs := (_root_.GlobalTheory.MulIsogeny.mul_isogeny K A n hn).1.2
  refine _root_.GlobalTheory.AV.AbVar.cancel_of_surjective K A A (n • 𝟙 A) hs B f 0 ?_
  rw [Preadditive.zsmul_comp, Category.id_comp, Limits.comp_zero, h]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTail
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.range_π_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (η : F.X) (W : Set Z), (∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η) → closure {i η} = W → Set.range X₁.π = W := by
  intro g n F W8 Z i X₁ η W hη hW
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hW, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetric
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isForm_evalF_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  intro F _ σ X ι _ m k E H h R
  exact ((_root_.GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.1 _ (chernF E H) R fun x =>
    (_root_.GlobalTheory.ChernCalc.dbarCoh_chernFld _ _ (atlas X σ) _ _ _ (_root_.GlobalTheory.ChernCalc.isGramPair_of_isMetricFr F σ X ι m k E H H h h x.1) x.2).1).1

end GlobalTheory.ChernCalc
end

