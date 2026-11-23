module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleLocalSectionsGlueBasicOpenCover
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt.GlueSec

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} {u : Fn1 X}
  {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) {n : ℕ}
  (τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E)

def locVal (u : Fn1 X) (a : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (F : Type) [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F) : F :=
  τ a F (ρ.comp ψ) - u E F ρ (spOver ψ ≫ x)

theorem pt_comp {E F : Type} [CommRing E] [Algebra R E] [CommRing F] [Algebra R F]
    (ψ : D →ₐ[R] E) (ρ : E →ₐ[R] F) : spOver (ρ.comp ψ) ≫ x = spOver ρ ≫ (spOver ψ ≫ x) := by
  rw [← spOver_comp, Category.assoc]

theorem sm_comp {E F : Type} [CommRing E] [Algebra R E] [CommRing F] [Algebra R F]
    (ψ : D →ₐ[R] E) (ρ : E →ₐ[R] F) (h : Sm W (D := E) (spOver ψ ≫ x)) :
    Sm W (D := F) (spOver (ρ.comp ψ) ≫ x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun p _ ↦ ?_⟩
  rw [pt_comp]
  exact hi trivial

variable {x τ} {s : Fin n → D}

theorem locVal_map (hu : IsCoc W u)
    (hsec : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x))
    (a : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (hsm : Sm W (D := E) (spOver ψ ≫ x))
    {F G : Type} [CommRing F] [Algebra R F] [CommRing G] [Algebra R G] (ρ : E →ₐ[R] F) (θ : F →ₐ[R] G)
    (hunit : IsUnit (ρ (ψ (s a)))) :
    θ (locVal x τ u a ψ F ρ) = locVal x τ u a ψ G (θ.comp ρ) := by
  have h1 := hsec a F G (ρ.comp ψ) θ hunit
  have h2 := hu E F G ρ θ (spOver ψ ≫ x) hsm
  rw [pt_comp] at h1
  unfold locVal
  rw [map_sub, AlgHom.comp_assoc]
  linear_combination h2 - h1

theorem locVal_agree
    (hagree : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ)
    (a b : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    {F : Type} [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F)
    (ha : IsUnit (ρ (ψ (s a)))) (hb : IsUnit (ρ (ψ (s b)))) :
    locVal x τ u a ψ F ρ = locVal x τ u b ψ F ρ := by
  unfold locVal
  rw [hagree a b F (ρ.comp ψ) ha hb]

theorem span_range (hs : Ideal.span (Set.range s) = ⊤) {E : Type} [CommRing E] [Algebra R E]
    (ψ : D →ₐ[R] E) : Ideal.span (Set.range fun a ↦ ψ (s a)) = ⊤ := by
  change Ideal.span (Set.range ((ψ : D →+* E) ∘ s)) = ⊤
  rw [Set.range_comp ((ψ : D →+* E) : D → E) s, ← Ideal.map_span, hs, Ideal.map_top]

end GlobalTheory.PtExt.GlueSec

namespace GlobalTheory.PtExt.GlueSec

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} {u : Fn1 X}
  {D : Type} [CommRing D] [Algebra R D] {x : Pt X D} {n : ℕ}
  {τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E} {s : Fin n → D}

theorem isUnit_locAlg {E : Type} [CommRing E] [Algebra R E] (t : E) : IsUnit (locAlg R t t) := by
  change IsUnit (algebraMap E (Localization.Away t) t)
  exact IsLocalization.Away.algebraMap_isUnit t

theorem glue_exists (hs : Ideal.span (Set.range s) = ⊤) (hu : IsCoc W u)
    (hsec : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x))
    (hagree : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ)
    {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (hsm : Sm W (D := E) (spOver ψ ≫ x)) :
    ∃ e : E, ∀ (F : Type) [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F) (a : Fin n),
      IsUnit (ρ (ψ (s a))) → ρ e = locVal x τ u a ψ F ρ := by
  let T : Set E := Set.range fun a ↦ ψ (s a)
  have hT : Ideal.span T = ⊤ := span_range hs ψ
  have hc : ∀ t : T, ∃ a, ψ (s a) = t.1 := fun t ↦ t.2
  choose c hc using hc
  have hcu : ∀ t : T, IsUnit (locAlg R t.1 (ψ (s (c t)))) := fun t ↦ by
    rw [hc t]; exact isUnit_locAlg _
  let v : ∀ t : T, Localization.Away t.1 := fun t ↦ locVal x τ u (c t) ψ _ (locAlg R t.1)
  obtain ⟨e, he, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top T hT v (fun t₁ t₂ ↦ by
    change awR R t₁.1 t₂.1 (v t₁) = awL R t₁.1 t₂.1 (v t₂)
    have hm : IsUnit (locAlg R (t₁.1 * t₂.1) (t₁.1 * t₂.1)) := isUnit_locAlg _
    rw [map_mul] at hm
    simp only [v]
    rw [locVal_map hu hsec _ ψ hsm _ _ (hcu t₁), locVal_map hu hsec _ ψ hsm _ _ (hcu t₂), awR_comp, awL_comp]
    apply locVal_agree hagree
    · rw [hc t₁]; exact isUnit_of_mul_isUnit_left hm
    · rw [hc t₂]; exact isUnit_of_mul_isUnit_right hm)
  refine ⟨e, fun F _ _ ρ a ha ↦ ?_⟩
  apply Localization.algebraMap_injective_of_span_eq_top _ (span_range hs (ρ.comp ψ))
  funext ⟨_, b, rfl⟩
  let t : T := ⟨ψ (s b), b, rfl⟩
  let lam : F →ₐ[R] Localization.Away (ρ (ψ (s b))) := locAlg R (ρ (ψ (s b)))
  let mu : Localization.Away t.1 →ₐ[R] Localization.Away (ρ (ψ (s b))) := Localization.awayMapₐ ρ t.1
  have hmu : mu.comp (locAlg R t.1) = lam.comp ρ := AlgHom.ext fun z ↦ by
    simp [mu, lam, t, IsLocalization.Away.map, IsLocalization.map_eq]
  change lam (ρ e) = lam (locVal x τ u a ψ F ρ)
  have het : locAlg R t.1 e = v t := he t
  rw [locVal_map hu hsec a ψ hsm ρ lam ha]
  rw [show lam (ρ e) = mu (locAlg R t.1 e) from (DFunLike.congr_fun hmu e).symm, het]
  simp only [v]
  rw [locVal_map hu hsec _ ψ hsm _ _ (hcu t), hmu]
  apply locVal_agree hagree
  · rw [AlgHom.comp_apply, hc t]; exact isUnit_locAlg _
  · exact ha.map lam

end GlobalTheory.PtExt.GlueSec

namespace GlobalTheory.PtExt

open GlueSec in
theorem glue_sections :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens) (u : Fn1 X),
    IsCoc W u → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (n : ℕ) (s : Fin n → D),
    Ideal.span (Set.range s) = ⊤ → ∀ τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
    (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x)) →
    (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ) →
    ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
    ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (D := E) (spOver ψ ≫ x) →
      σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  intro R _ X K W u hu D _ _ x n s hs τ hsec hagree
  classical
  let σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E := fun E _ _ ψ ↦
    if h : Sm W (D := E) (spOver ψ ≫ x) then Classical.choose (glue_exists hs hu hsec hagree ψ h) else 0
  refine ⟨σ, fun E _ _ E' _ _ ψ θ hsm ↦ ?_⟩
  have hsm' : Sm W (D := E') (spOver (θ.comp ψ) ≫ x) := sm_comp x ψ θ hsm
  have P := Classical.choose_spec (glue_exists hs hu hsec hagree ψ hsm)
  have P' := Classical.choose_spec (glue_exists hs hu hsec hagree (θ.comp ψ) hsm')
  have e1 : σ E ψ = Classical.choose (glue_exists hs hu hsec hagree ψ hsm) := dite_eq_left hsm
  have e2 : σ E' (θ.comp ψ) = Classical.choose (glue_exists hs hu hsec hagree (θ.comp ψ) hsm') :=
    dite_eq_left hsm'
  rw [e1, e2]
  apply Localization.algebraMap_injective_of_span_eq_top _ (span_range hs (θ.comp ψ))
  funext ⟨_, a, rfl⟩
  let lam : E' →ₐ[R] Localization.Away ((θ.comp ψ) (s a)) := locAlg R ((θ.comp ψ) (s a))
  let lt : E →ₐ[R] Localization.Away ((θ.comp ψ) (s a)) := lam.comp θ
  change lam (Classical.choose (glue_exists hs hu hsec hagree (θ.comp ψ) hsm') - θ (Classical.choose (glue_exists hs hu hsec hagree ψ hsm))) = lam (u E E' θ (spOver ψ ≫ x))
  rw [map_sub, P' (Localization.Away ((θ.comp ψ) (s a))) lam a (isUnit_locAlg ((θ.comp ψ) (s a))),
    show lam (θ (Classical.choose (glue_exists hs hu hsec hagree ψ hsm))) =
      lt (Classical.choose (glue_exists hs hu hsec hagree ψ hsm)) from rfl,
    P (Localization.Away ((θ.comp ψ) (s a))) lt a (isUnit_locAlg (R := R) ((θ.comp ψ) (s a)))]
  have h2 := hu E E' (Localization.Away ((θ.comp ψ) (s a))) θ lam (spOver ψ ≫ x) hsm
  unfold locVal
  simp only [lt]
  rw [pt_comp x ψ θ, AlgHom.comp_assoc]
  linear_combination h2

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportional
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem defOver_of_coord_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 →
    ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K)
      (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K),
      GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) →
      (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  intro K _ _ k₀ hk₀ P₀ m hm hm3 hmK z v l r H hr hv
  classical
  let Ix := {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1}
  have Lw := GlobalTheory.abelianSchemeLaws_all
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm2K : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hmK
  have hcard := (Lw.1.mulN (Sp k₀) P₀ (m ^ 2) hm1).2.2.2.2 K (spMap k₀.subtype) hm2K
  have hfin : Finite Ix := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))

  have hσs : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
    intro σ hσ
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ w.2

  have hfix : ∀ (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) (y : Ix),
      (Over.homMk (spMap σ.toRingHom) (hσs σ hσ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1 = y.1 := by
    intro σ hσ y
    have hdef : DefOver k₀ y.1.left := by
      refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y' : Ix => y'.1.left).subset ?_)
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨⟨(Over.homMk (spMap τ.toRingHom) (hσs τ hτ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1, ?_⟩, ?_⟩
      · rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      · rfl
    obtain ⟨y₀, hy₀⟩ := hdef
    apply Over.OverMorphism.ext
    show spMap σ.toRingHom ≫ y.1.left = y.1.left
    rw [← hy₀, ← Category.assoc, hσs σ hσ]

  obtain ⟨-, U₂, -, U₄⟩ := CoordSep.coord_exists_unique_separate Lw.1 K (Sp k₀) P₀ (spMap k₀.subtype) m hm hmK Ix
    (fun i => i.1) (fun i => i.2)
  have hall : ∀ y : Over.mk (spMap k₀.subtype) ⟶ P₀.A, y ^ m ^ 2 = 1 → ∃ i : Ix, i.1 = y := fun y hy => ⟨⟨y, hy⟩, rfl⟩
  have hv0 : v ≠ 0 := (U₄ hm3 hall z z v H H).2
  have hl : l ≠ 0 := by
    intro h0
    apply hv0
    funext i
    rw [hv i, h0, zero_mul, Pi.zero_apply]
  have horb : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ z.left = z.left := by
    intro σ hσ
    let h : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype) := Over.homMk (spMap σ.toRingHom) (hσs σ hσ)
    have H2 := CoordReduce.isCoordPt_map Lw.2 P₀ σ.toRingHom (hσs σ hσ) (p := fun i : Ix => i.1)
      (fun i => i.2) (w := v) H
    have hp : (fun i : Ix => h ≫ i.1) = fun i => i.1 := funext fun i => hfix σ hσ i
    change GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => h ≫ i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (σ (v i))) at H2
    rw [hp] at H2
    have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl
    have H3 : GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (v i)) := by
      refine (U₂ (h ≫ z) (fun i => σ (v i)) v H2).2 ⟨Units.mk0 (l / σ l) (div_ne_zero hl hσl), ?_⟩
      funext i
      simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
      rw [hv i, map_mul, hσ _ (hr i)]
      field_simp
    have := (U₄ hm3 hall (h ≫ z) z v H3 H).1
    have e2 := congrArg CommaMorphism.left this
    exact e2
  refine defOver_of_finite_orbit K k₀ hk₀ _ z.left ((Set.finite_singleton z.left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  exact horb σ hσ

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfIsGrpPullbackOfInjectiveDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pow_eq_one_of_isGrpPullback_of_injective : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → ∀ (x : baseOver (Sp Ω) ⟶ A.A) (y : baseOver (Sp T) ⟶ P.A) (k : ℕ), x.left ≫ φ = spMap jT ≫ y.left → x ^ k = 1 → y ^ k = 1 := by
  intro Ω T _ _ _ jT hj A P φ hφ x y k hxy hx
  let U : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have e1 : pushHom hφ (baseOver (Sp Ω)) x = U ≫ y := Over.OverMorphism.ext hxy
  have e2 : U ≫ y ^ k = U ≫ 1 :=
    calc U ≫ y ^ k = preHom U (y ^ k) := rfl
      _ = (preHom U y) ^ k := map_pow _ _ _
      _ = (pushHom hφ (baseOver (Sp Ω)) x) ^ k := by rw [e1]; rfl
      _ = pushHom hφ (baseOver (Sp Ω)) (x ^ k) := (map_pow _ _ _).symm
      _ = 1 := by rw [hx, map_one]
      _ = preHom U 1 := (map_one _).symm
  have e3 : spMap jT ≫ (y ^ k).left = spMap jT ≫ (1 : baseOver (Sp T) ⟶ P.A).left :=
    congrArg (fun z => z.left) e2
  have : IsDominant (spMap jT) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical jT).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot jT).1 hj]; exact bot_le)⟩
  have := P.isAb.proper
  have : IsReduced (baseOver (Sp T)).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of T)))
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P.A.hom
    ((Over.w (y ^ k)).trans (Over.w (1 : baseOver (Sp T) ⟶ P.A)).symm) (spMap jT) e3)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
section
set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra TensorProduct

namespace GlobalTheory.PDiv.FrobKerOrder

theorem add_pow_of_cast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime)
    (h : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp, h]; simp

theorem cast_eq_zero_of_algebra (p : ℕ) (k A : Type*) [CommRing k] [CharP k p] [CommRing A]
    [Algebra k A] : (p : A) = 0 := by
  rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]

variable (p : ℕ) [hp : Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H]
  [HopfAlgebra k H]

theorem mk_pow_eq (x : H) :
    Ideal.Quotient.mkₐ k (frobKerIdeal p k H) x ^ p =
      algebraMap k _ (counit (R := k) x) ^ p := by
  have hx : x - algebraMap k H (counit (R := k) x) ∈ augIdeal k H := by
    simp [RingHom.mem_ker]
  have h0 : Ideal.Quotient.mkₐ k (frobKerIdeal p k H)
      ((x - algebraMap k H (counit (R := k) x)) ^ p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have e : x = (x - algebraMap k H (counit (R := k) x)) + algebraMap k H (counit (R := k) x) := by
    ring
  conv_lhs => rw [e, ← map_pow, add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k H),
    map_add, h0, zero_add, map_pow, AlgHom.commutes]

theorem map_pow_eq (t : H ⊗[k] H) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))
      (Ideal.Quotient.mkₐ k (frobKerIdeal p k H)) t ^ p =
    (1 : H ⧸ frobKerIdeal p k H) ⊗ₜ[k] (Ideal.Quotient.mkₐ k (frobKerIdeal p k H)
      (TensorProduct.lid k H (LinearMap.rTensor H (counit (R := k) (A := H)) t)) ^ p) := by
  induction t with
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k _),
      add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k _), hx, hy, tmul_add]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, mk_pow_eq,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, smul_pow, ← map_pow,
      Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem isHopfIdeal : (frobKerIdeal p k H).IsHopfIdeal k := by
  have : ((frobKerIdeal p k H).restrictScalars k).IsCoideal := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact frobKerIdeal_le_augIdeal hp.out.ne_zero k H hx
    · intro x hx
      have h : frobKerIdeal p k H ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))
            (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))).comp (comulAlgHom k H)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply, map_pow_eq,
          comulAlgHom_apply, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, ← map_pow]
        have : Ideal.Quotient.mkₐ k (frobKerIdeal p k H) (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [this, tmul_zero]
      exact h hx
  refine ⟨?_⟩
  · intro x hx
    have h : frobKerIdeal p k H ≤ (frobKerIdeal p k H).comap (HopfAlgebra.antipodeAlgHom k H) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
      apply pow_mem_frobKerIdeal
      have ha' : counit (R := k) a = 0 := ha
      simp [RingHom.mem_ker, ha']
    exact h hx

omit [CharP k p] in
theorem le_sq : frobKerIdeal p k H ≤ augIdeal k H ^ 2 := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact Ideal.pow_le_pow_right hp.out.two_le (Ideal.pow_mem_pow ha p)

theorem pow_le_finrank {n d : ℕ} {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (x : Fin d → A)
    (h : RingHom.ker (MvPolynomial.aeval (R := K) x) =
      Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) K) ^ n)) :
    n ^ d ≤ Module.finrank K A := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  have he : Function.Injective e := by
    intro a b hab
    funext i
    have := DFunLike.congr_fun hab i
    exact Fin.ext (by simpa [e] using this)
  have hli : LinearIndependent K fun a : Fin d → Fin n =>
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hmem : (∑ a, g a • MvPolynomial.monomial (e a) (1 : K)) ∈
        RingHom.ker (MvPolynomial.aeval (R := K) x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, map_sum]
      simpa only [map_smul] using hg
    have hr : (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) K) ^ n) =
        (fun s => MvPolynomial.monomial s (1 : K)) '' Set.range (fun i => Finsupp.single i n) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp [MvPolynomial.X_pow_eq_monomial]
    rw [h, hr, MvPolynomial.mem_ideal_span_monomial_image] at hmem
    by_contra hne
    have hc : AddMonoidAlgebra.coeff (∑ a, g a • MvPolynomial.monomial (e a) (1 : K)) (e a) = g a := by
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he.eq_iff]
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hmem (e a) (by rw [MvPolynomial.mem_support_iff, hc]; exact hne)
    have h1 := hi i
    have h2 := (a i).2
    simp [e] at h1
    omega
  simpa using hli.fintype_card_le_finrank

theorem pow_finrank_cot_le [Module.Finite k H] :
    p ^ Module.finrank k (Cot k H) ≤ Module.finrank k (H ⧸ frobKerIdeal p k H) := by
  haveI := isHopfIdeal p k H
  set J := frobKerIdeal p k H with hJ
  let π := Ideal.Quotient.mkₐ k J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective k J
  have hε : (counitAlgHom k (H ⧸ J)).comp π = counitAlgHom k H := rfl
  have hbij : Function.Bijective (AugCot.map π hε) := by
    refine ⟨?_, AugCot.map_surjective π hε hπ⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (AugCot.exact_kerMap_map π hε hπ y).1 hy
    rw [AugCot.kerMap_apply, AugCot.d_of_mem _ (AugCot.ker_le π hε z.2),
      Ideal.toCotangent_eq_zero]
    exact le_sq p k H (Ideal.Quotient.eq_zero_iff_mem.1 z.2)
  rw [(LinearEquiv.ofBijective _ hbij).finrank_eq]
  set ε := counitAlgHom k (H ⧸ J) with hεdef
  let b := Module.finBasis k (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin (Module.finrank k (AugCot ε)) → k,
      AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = ∑ i, l i • b i := by
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank k (AugCot ε)) → k,
      (∑ i, l i • (x i : H ⧸ J)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  refine pow_le_finrank (fun i => (x i : H ⧸ J))
    (GlobalTheory.HeightOneHopf.truncated_polynomial p k (H ⧸ J) _ _ ?_ (fun i => (x i).2) ?_ ?_).2
  · intro f hf
    obtain ⟨a, rfl⟩ := hπ f
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal (R := k) hf)
  · intro y hy
    refine ⟨b.repr (AugCot.d ε y), ?_⟩
    have h1 : AugCot.d ε (y - ∑ i, b.repr (AugCot.d ε y) i • (x i : H ⧸ J)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hy (hmem _)), Ideal.toCotangent_eq_zero] at h1
  · intro l hl
    have h1 : AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = 0 := by
      rw [AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]
      exact hl
    rw [hsum] at h1
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i

end GlobalTheory.PDiv.FrobKerOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueIsUnitOfPsiUnitOnLocalRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiValue_isUnit_of_psiUnitOn_localRing : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (χ : D.X), PsiUnitOn D χ W → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → spMap φ₁ (closedPoint T) ∈ W → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F) := by
  first | exact @GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn | exact GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn | (intros; apply GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn <;> assumption)
end

