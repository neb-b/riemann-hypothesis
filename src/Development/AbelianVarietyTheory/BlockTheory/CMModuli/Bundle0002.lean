module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.PeriodMapPresentation
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Topology

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


open Classical in
def sigMult (D : Datum H) (τ : E →+* ℂ) : ℕ := if τ (H.rt : E) = H.rt0 then D.p else D.q

def IsTypeFn (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, Nat.card {i : Fin g // ty i = τ} = sigMult D τ

def tyAct {g : ℕ} (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ :=
  fun i => ty i (a : E) * z i

def actR (D : Datum H) (a : 𝓞 E) : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
  (DistribSMul.toLinearMap ℤ D.La a).baseChange ℝ

def sigTrace (D : Datum H) (a : 𝓞 E) : ℂ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
    ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E)))

def domain (D : Datum H) : Set (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) :=
  {J | (∀ x, J (J x) = -x) ∧
    (∀ a : 𝓞 E, J ∘ₗ actR D a = actR D a ∘ₗ J) ∧
    (∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) ∧
    ∀ a : 𝓞 E, ((LinearMap.trace ℝ _ (actR D a) : ℝ) : ℂ) / 2 -
      Complex.I * ((LinearMap.trace ℝ _ (J ∘ₗ actR D a) : ℝ) : ℂ) / 2 = sigTrace D a}

def Presents (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))
    (J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) : Prop :=
  ∃ φ : (ℝ ⊗[ℤ] D.La) ≃ₗ[ℝ] (Fin g → ℂ),
    (∀ x : D.La, φ ((1 : ℝ) ⊗ₜ[ℤ] x) = P x) ∧ (∀ v, φ (J v) = Complex.I • φ v) ∧
      ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v)

theorem domain_nonempty (D : Datum H) : (domain D).Nonempty := by
  obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
  have key := fun a : 𝓞 E => h4 a (actR D a) (sigTrace D a) (fun x => rfl) rfl
  refine ⟨J, h1, fun a => (key a).1, h2, h3, fun a => ?_⟩
  rw [(key a).2.1, (key a).2.2]
  apply Complex.ext
  · simp
  · simp; ring

end Period

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

def HolOn (B : Set V) (y : V → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens), ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ U →
    (∀ᶠ b' in 𝓝[B] b, ⊤ ≤ y b' ⁻¹ᵁ U) ∧
      ∀ f : Γ(X, U), DifferentiableWithinAt ℂ (fun b' => valAt' (y b') U f) B b

end Hol

section Theta

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}} {G : Over S} [GrpObj G] {g : ℕ}

abbrev fibre (G : Over S) (y : Sp ℂ ⟶ S) : Scheme.{0} := pullback G.hom y

def fibrePt {y : Sp ℂ ⟶ S} (x : Over.mk y ⟶ G) : Sp ℂ ⟶ fibre G y :=
  pullback.lift x.left (𝟙 (Sp ℂ)) (by simpa using Over.w x)

def IsRigFrame (L : RigLB G) (B : Set V) (y : V → (Sp ℂ ⟶ S))
    (ex : ∀ b : V, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (fr : L.L.ι → V → (Fin g → ℂ) → ℂ) : Prop :=
  HolOn (B ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun p => ((ex p.1 p.2).left : Sp ℂ ⟶ G.left)) ∧
  (∀ b ∈ B, (ex b 0).left = y b ≫ eSec G) ∧
  (∀ i, DifferentiableOn ℂ (fun p : V × (Fin g → ℂ) => fr i p.1 p.2)
    {p | p.1 ∈ B ∧ ⊤ ≤ (ex p.1 p.2).left ⁻¹ᵁ L.L.U i}) ∧
  (∀ i, ∀ b ∈ B, ∀ z, ⊤ ≤ (ex b z).left ⁻¹ᵁ L.L.U i → fr i b z ≠ 0) ∧
  (∀ i j, ∀ b ∈ B, ∀ z, ⊤ ≤ (ex b z).left ⁻¹ᵁ (L.L.U i ⊓ L.L.U j) →
    fr i b z = valAt' (X := G.left) (ex b z).left (L.L.U i ⊓ L.L.U j) (L.L.g i j).val * fr j b z) ∧
  ∀ (j : (L.L.pull (eSec G)).ι), ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ (L.L.pull (eSec G)).U j →
    fr (j PUnit.unit) b 0 = valAt' (X := S) (y b) ((L.L.pull (eSec G)).U j) (L.rig.s j).val

def IsFibreFn (L : LB G.left) (y : Sp ℂ ⟶ S) (ex : (Fin g → ℂ) → (Over.mk y ⟶ G))
    (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (L.pull (pullback.fst G.hom y)).ι) (z : Fin g → ℂ),
    ⊤ ≤ fibrePt (ex z) ⁻¹ᵁ (L.pull (pullback.fst G.hom y)).U j →
      valAt' (fibrePt (ex z)) ((L.pull (pullback.fst G.hom y)).U j) (s.f j) = θ z * fr (j PUnit.unit) z

def IsThetaFrame (L : RigLB G) (B : Set V) (y : V → (Sp ℂ ⟶ S))
    (ex : ∀ b : V, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (θ : V → (Fin g → ℂ) → ℂ)
    (fr : L.L.ι → V → (Fin g → ℂ) → ℂ) : Prop :=
  IsRigFrame L B y ex fr ∧
    ∀ b ∈ B, ∃ s : (L.L.pull (pullback.fst G.hom (y b))).Sec, IsFibreFn L.L (y b) (ex b) (fun i => fr i b) s (θ b)

end Theta

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Prim

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def graphφ (f : A ⟶ A) : Fin 5 → (A.left ⟶ A.left) :=
  ![(padd A (𝟙 A) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left, 𝟙 A.left]

def graphε : Fin 5 → ℤ := ![1, -1, -1, 1, -1]

end Prim

variable {R : Type} [CommRing R] [IsDomain R]

section Data

variable {O : Type} [Ring O] [StarRing O] {D : DegPre R} [Module O D.X]

def IsRigGraphIso (D : DegPre R) (f : D.P.A ⟶ D.P.A)
    (v : LB.Gen (LB.LinComb D.P.L (graphφ D.P.A f) graphε)) : Prop :=
  v.IsGen ∧ LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ v (eSec D.P.A))
    (LB.invGen D.P.L _ _ D.rig)

def PsiThrough (ac : D.OAct O) (w : O) : Prop :=
  ∃ v : LB.Gen (LB.LinComb D.P.L (graphφ D.P.A (ac.onB.act w)) graphε),
    IsRigGraphIso D (ac.onB.act w) v ∧
    ∀ y : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau y (w • y)) (LB.pullGen D.P.L _ _ v (D.xK y)))
      (D.psi y)

end Data

def PsiGenOn (D : DegPre R) (χ : D.X) (U : Set (Spec (CommRingCat.of R))) : Prop :=
  ∀ x ∈ U, ∃ (j : PUnit → D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), x ∈ V ∧
    V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧
    ∃ (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
      (r : Γ(Spec (CommRingCat.of R), V)ˣ), pullU (jK R) V r = res h ((D.psi χ).s j)

section Points

variable {O : Type} [Ring O] [StarRing O] {D : DegPre R} [Module O D.X]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

def IsRigAdjIso (D : DegPre R) (f g : D.P.A ⟶ D.P.A)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)

def GtSmul (ac : D.OAct O) (a : O) (g g' : GtPtF D F) : Prop :=
  g'.b = g.b ≫ ac.onB.act a ∧
    ∃ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (ac.onB.act a) (ac.onB.act (star a))) rosatiε),
      IsRigAdjIso D (ac.onB.act a) (ac.onB.act (star a)) u ∧
      ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g'.s χ)
          (LB.pullGen D.P.L _ _ u (lift g.b (DegPre.cF D F χ)).left))
        (g.s (star a • χ))

def QkAdd {k : ℕ} (p p' p'' : QkPt D F k) : Prop :=
  ∃ q : QkPt D F k, q.y = p.y + p'.y ∧ GtPtF.IsAdd p.g p'.g q.g ∧ QkPt.Equiv D F q p''

def QkSmul (ac : D.OAct O) (a : O) {k : ℕ} (p p' : QkPt D F k) : Prop :=
  ∃ q : QkPt D F k, q.y = a • p.y ∧ GtSmul ac a p.g q.g ∧ QkPt.Equiv D F q p'

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']

abbrev specExt (σ : F →ₐ[FractionRing R] F') : (TF (R := R) F').left ⟶ (TF (R := R) F).left :=
  Spec.map (CommRingCat.ofHom (σ : F →+* F'))

def GtMap (σ : F →ₐ[FractionRing R] F') (g : GtPtF D F) (g' : GtPtF D F') : Prop :=
  g'.b.left = specExt σ ≫ g.b.left ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) (specExt σ))

def QkMap (σ : F →ₐ[FractionRing R] F') {k : ℕ} (p : QkPt D F k) (p' : QkPt D F' k) : Prop :=
  ∃ q : QkPt D F' k, q.y = p.y ∧ GtMap σ p.g q.g ∧ QkPt.Equiv D F' q p'

end Points

section Host

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h1
  exact h1

@[reducible] def hostStar (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive := bar_bar H
  star_mul := fun a b => by
    change H.bar (a * b) = H.bar b * H.bar a
    rw [map_mul, _root_.mul_comm]
  star_add := fun a b => map_add H.bar a b

def PsiThroughHost (H : Host E) {D : DegPre R} [Module (𝓞 E) D.X]
    (ac : letI := hostStar H; D.OAct (𝓞 E)) : Prop :=
  letI := hostStar H; PsiThrough ac H.w0

end Host

end GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
end
end

