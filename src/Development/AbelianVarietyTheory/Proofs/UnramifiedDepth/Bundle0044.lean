module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLaw
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGaugeBilinearTermOfTypeNe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartLiftSquareZeroUnitPoint
section
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem lift_of_smooth_affine {G B : Scheme.{0}} (q : G ⟶ B) [Smooth q] [IsAffineHom q]
    {S S' : Type} [CommRing S] [CommRing S'] (π : S →+* S') (hπ : Function.Surjective π)
    (hk : IsNilpotent (RingHom.ker π)) (y : Spec (CommRingCat.of S) ⟶ B) (x : Spec (CommRingCat.of S') ⟶ G)
    (h : x ≫ q = Spec.map (CommRingCat.ofHom π) ≫ y) :
    ∃ w : Spec (CommRingCat.of S) ⟶ G, w ≫ q = y ∧ Spec.map (CommRingCat.ofHom π) ≫ w = x := by
  have : IsAffine (pullback q y) := isAffine_of_isAffineHom (pullback.snd q y)
  let e := (pullback q y).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (pullback.lift x _ h ≫ e.hom)
  obtain ⟨α, hα⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q y)
  have hs : RingHom.Smooth α.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hα]
    infer_instance
  have hφα : α ≫ φ = CommRingCat.ofHom π := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hφ, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]
  letI : Algebra S Γ(pullback q y, ⊤) := α.hom.toAlgebra
  letI : Algebra S S' := π.toAlgebra
  haveI : Algebra.Smooth S Γ(pullback q y, ⊤) := hs
  let φ' : Γ(pullback q y, ⊤) →ₐ[S] S' := ⟨φ.hom, fun r => congr($hφα r)⟩
  let ψ := Algebra.FormallySmooth.liftOfSurjective φ' (Algebra.ofId S S') hπ hk
  have hψ : (Algebra.ofId S S').comp ψ = φ' :=
    Algebra.FormallySmooth.comp_liftOfSurjective φ' (Algebra.ofId S S') hπ hk
  let ψ' : Γ(pullback q y, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom ψ.toRingHom
  have h₁ : α ≫ ψ' = 𝟙 _ := by
    ext r
    exact ψ.commutes r
  have h₂ : ψ' ≫ CommRingCat.ofHom π = φ := by
    ext a
    exact congr($hψ a)
  refine ⟨Spec.map ψ' ≫ e.inv ≫ pullback.fst q y, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv, ← hα, ← Category.assoc,
      ← Spec.map_comp, h₁, Spec.map_id, Category.id_comp]
  · rw [← Category.assoc, ← Spec.map_comp, h₂, hφ, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

theorem qRel_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S') (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → RingHom.ker ρ ^ 2 = ⊥ → ∀ y : sp (R₀ := R) S ⟶ D.P.A, spMap ρ ≫ y = 1 → ∃ z : sp (R₀ := R) S ⟶ G, spMap ρ ≫ z = 1 ∧ QRel c S z y := by
  intro R _ _ I D k G _ _ c S _ _ hS S' _ _ ρ σ hρσ hk y hy
  have hS' : Kills I k S' := fun t ht => by rw [← ρ.commutes, hS t ht, map_zero]
  obtain ⟨hex, hmul⟩ := (qRel_existsUnique_mul_nat R I D k G c).1 S' hS'
  obtain ⟨y₀, hy₀, hu⟩ := hex 1
  have h1 : y₀ = 1 := by
    have h := hmul 1 1 y₀ y₀ hy₀ hy₀
    rw [_root_.mul_one] at h
    exact mul_eq_left.1 (hu _ h)
  subst h1
  obtain ⟨x, hx₁, hx₂⟩ := hy₀
  have := c.q_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have := (H1.torus_dim (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).smooth
  have : Smooth c.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hf : Mono (pullback.fst D.P.A.hom (Out.thick R I k)) := inferInstance
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
  have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let y' : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k D.P.A).left :=
    pullback.lift y.left t ((Over.w y).trans ht.symm)
  have hy' : y' ≫ pullback.fst D.P.A.hom (Out.thick R I k) = y.left := pullback.lift_fst _ _ _
  have hyl : Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ y.left = (1 : sp (R₀ := R) S' ⟶ D.P.A).left :=
    congrArg (·.left) hy
  obtain ⟨w, hw₁, hw₂⟩ := lift_of_smooth_affine c.q.left ρ.toRingHom
    (fun a => ⟨σ a, congr($hρσ a)⟩) ⟨2, hk⟩ y' x (by
      refine (cancel_mono (pullback.fst D.P.A.hom (Out.thick R I k))).1 ?_
      exact ((Category.assoc _ _ _).trans hx₂).trans
        (hyl.symm.trans ((congrArg (_ ≫ ·) hy'.symm).trans (Category.assoc _ _ _).symm)))
  have hq : w ≫ c.pG.left = y.left := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hw₁).trans hy')
  have hz : (w ≫ (Out.fstG I k G).left) ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    have a : (Out.fstG I k G).left ≫ G.hom = c.pG.left ≫ D.P.A.hom := (Over.w _).trans (Over.w _).symm
    exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) a).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.P.A.hom) hq).trans (Over.w y))))
  refine ⟨Over.homMk (w ≫ (Out.fstG I k G).left) hz, ?_, w, rfl, hq⟩
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Out.fstG I k G).left) hw₂).trans hx₁)

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLawStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.AddCvSt V := by
  first | exact @GlobalTheory.RowLaw.addCvSt_of_rlaw | exact GlobalTheory.RowLaw.addCvSt_of_rlaw | (intros; apply GlobalTheory.RowLaw.addCvSt_of_rlaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextPairingNondegenerateGeometricFibre
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem biext_pairing_nondegenerate_geometric_fibre :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (x : Over.mk f ⟶ G), x ^ N = 1 →
    ∃ σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left) (fun _ => 1)), σ.IsGen ∧
      ∀ y : Over.mk f ⟶ G, y ^ N = 1 → (∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) := by
  intro hD hS S G _ _ P β K _ _ f N hN hsm hfin hfl hsur hpr x hx hxy
  obtain ⟨σ, hσ, hinv⟩ := hS S G K f N P β x hx
  exact hpr x (hD S G K f N hN hsm hfin hfl hsur _ P β.isLB _ σ hσ
    (fun y hy => hinv y hy (hxy y hy)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextValAxioms
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem biextVal_pull {S : Scheme.{0}} {G : Over S} {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → ((G ⊗ G ⊗ G).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J : (T'.left ⟶ X) → L.ι} (hJ : Good L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L φ ε t (lift x (lift x' y)).left) ρ.left z J =
      val t (lift (ρ ≫ x) (lift (ρ ≫ x') (ρ ≫ y))).left z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift]


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem biext_val_axioms :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) := by
  intro S G _ _ P β T z J hJ t₁ t₂ h₁ h₂
  have a₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 0 = a := fun a b c d => by simp [x4]
  have a₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 1 = b := fun a b c d => by simp [x4]
  have a₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 2 = c := fun a b c d => by simp [x4]
  have a₃ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 3 = d := fun a b c d => by simp [x4]
  have b₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 0) (x4 G 1) = a * b :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  have b₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 1) (x4 G 2) = b * c :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  have b₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 2) (x4 G 3) = c * d :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃])
  have c₀ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 0 = a := fun a b c => by simp [x3]
  have c₁ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 1 = b := fun a b c => by simp [x3]
  have c₂ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 2 = c := fun a b c => by simp [x3]
  simp only [h₁, h₂]
  refine ⟨fun x x' x'' y => ?_, fun x x' y => ?_, fun x y y' y'' => ?_, fun x y y' => ?_, fun x x' y y' => ?_⟩
  · have := val_corr hJ β.assoc1 (lift x (lift x' (lift x'' y))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm1 (lift x (lift x' y)).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.assoc2 (lift x (lift y (lift y' y''))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₁, b₂, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm2 (lift x (lift y y')).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.compat (lift x (lift x' (lift y y'))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))).symm.trans
      (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₂, a₀, a₁, a₂, a₃] at e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawProduct
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BiextSym

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_iso {X : Scheme.{0}} {L : LB X} {F : X ⟶ X} (h : LBIso L (L.pull F)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![F, 𝟙 X] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![F, 𝟙 X] j ≤ (L.pull F).U (fun _ => j 0) ⊓ L.U (j 1) :=
    fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx 0), Set.mem_iInter.1 hx 1⟩
  refine ⟨⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have a := hp _ (𝟙 X) y (j 0) (j' 0) (j 1) (j' 1) (mem_pull.1 (le j hy.1).1) (mem_pull.1 (le j' hy.2).1)
    (le j hy.1).2 (le j' hy.2).2
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j) hy.1 _)).trans (a.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2).trans ?_)
    ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j') hy.2 _)))
  rw [Fin.prod_univ_two]
  show gm (𝟙 X ≫ F) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 X ≫ 𝟙 X) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) = _
  rw [_root_.zpow_neg, _root_.zpow_one, _root_.zpow_one, Category.id_comp (𝟙 X)]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

omit [GrpObj A] [IsCommMonObj A] in
theorem prod_sym {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i : Fin 2, h ((lift x y).left ≫ ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ) =
      h (lift y x).left * (h (lift x y).left)⁻¹ := by
  have e : lift x y ≫ lift (snd A A) (fst A A) = lift y x := by rw [comp_lift, lift_fst, lift_snd]
  rw [Fin.prod_univ_two]
  show h (lift x y ≫ lift (snd A A) (fst A A)).left ^ (1 : ℤ) * h ((lift x y).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [e, Category.comp_id, _root_.zpow_neg, _root_.zpow_one, _root_.zpow_one]

theorem biextension_first_law_product {T : Over S} (x x' y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by
  have a₀ : lift x (lift x' y) ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift x' y) ≫ x3 A 1 = x' := by simp [x3]
  have a₂ : lift x (lift x' y) ≫ x3 A 2 = y := by simp [x3]
  have b : lift x (lift x' y) ≫ padd A (x3 A 0) (x3 A 1) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift x' y) ≫ lift (padd A (x3 A 0) (x3 A 1)) (x3 A 2)).left ^ (1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 1) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem biextension_second_law_product {T : Over S} (x y y' : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift x (y * y')).left * (h (lift x y).left)⁻¹ * (h (lift x y').left)⁻¹ := by
  have a₀ : lift x (lift y y') ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift y y') ≫ x3 A 1 = y := by simp [x3]
  have a₂ : lift x (lift y y') ≫ x3 A 2 = y' := by simp [x3]
  have b : lift x (lift y y') ≫ padd A (x3 A 1) (x3 A 2) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift y y') ≫ lift (x3 A 0) (padd A (x3 A 1) (x3 A 2))).left ^ (1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 1)).left ^ (-1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem exists_norm {P : LB (A ⊗ A).left} (hP : P.IsLB) (h : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    ∃ s : LB.Gen (LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good P z J → val s (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso h
  obtain ⟨s, hs, hv⟩ := exists_gen hP (K' := Fin 2) (φ' := ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left])
    (ε' := ![1, -1]) (fun V _ k => by
      have p := prod_sym (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _
        (c := ∏ i : Fin 2, k (![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ)) rfl
        (DVR.prod_neg _ _ p)) ?_
      rw [mul_inv_cancel, inv_one, _root_.mul_one])
    (LB.mulGen P _ _ _ _ t (LB.invGen P _ _ (LB.pullGen P _ _ t (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨s, hs, fun T z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, comp_lift, MonObj.comp_one, mul_inv_cancel]

theorem val_pull₂ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C : Over S} {φ : K → ((B ⊗ C).left ⟶ X)}
    {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good P z J)
    (a : T ⟶ B) (b : T ⟶ C) :
    val (LB.pullGen P φ ε u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]

theorem val_pull₃ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C D : Over S}
    {φ : K → ((B ⊗ C ⊗ D).left ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good P z J) (a : T ⟶ B) (b : T ⟶ C) (c : T ⟶ D) :
    val (LB.pullGen P φ ε u (lift a (lift b c)).left) ρ.left z J =
      val u (lift (ρ ≫ a) (lift (ρ ≫ b) (ρ ≫ c))).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_lift]

theorem law_origin {P : LB (A ⊗ A).left} (β : IsBiext A P) {T : Over S} {z : T.left} {J} (hJ : Good P z J) :
    val β.law1 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J =
      val β.law2 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J := by
  let ρ := lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A)))
  have a₀ : ρ ≫ x4 A 0 = 1 := by simp [ρ, x4]
  have a₁ : ρ ≫ x4 A 1 = 1 := by simp [ρ, x4]
  have a₂ : ρ ≫ x4 A 2 = 1 := by simp [ρ, x4]
  have a₃ : ρ ≫ x4 A 3 = 1 := by simp [ρ, x4]
  have b₀ : ρ ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
  have b₁ : ρ ≫ padd A (x4 A 2) (x4 A 3) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃, _root_.mul_one])
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_pull₃ β.law1 ρ hJ _ _ _) (val_pull₃ β.law2 ρ hJ _ _ _))) (val_pull₃ β.law2 ρ hJ _ _ _))).symm.trans
    ((val_corr hJ β.compat ρ.left).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull₃ β.law2 ρ hJ _ _ _) (val_pull₃ β.law1 ρ hJ _ _ _))) (val_pull₃ β.law1 ρ hJ _ _ _))))
  rw [b₀, b₁, a₀, a₁, a₂, a₃, mul_comm (val β.law2 _ z J) (val β.law1 _ z J)] at e
  exact (mul_left_cancel e).symm

theorem main :
  (ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme A →
    ∀ (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (A ⊗ A).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext A P),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∃ s : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ (A ⊗ A).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ x x' y : T ⟶ A,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift y x).left z J = 1 ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift (x * x') y).left z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x' y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift y (lift x x')).left z J) := by
  intro hG S A _ _ hA P β hs
  obtain ⟨s, hs, h1⟩ := exists_norm β.isLB hs
  refine ⟨s, hs, fun T z J hJ x x' y => ⟨?_, ?_⟩⟩
  · have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift (fst A A) (snd A A)).left)
          (LB.pullGen P _ _ s (lift (snd A A) (fst A A)).left)) σ.left z J =
          val s (lift (σ ≫ fst A A) (σ ≫ snd A A)).left z J * val s (lift (σ ≫ snd A A) (σ ≫ fst A A)).left z J :=
      fun σ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))
    let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
    have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom := surj_comp (surj_snd hG hA _) (hG _ _ hA).2
    have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
    have key := gen_unique' β.isLB (u' := LB.oneGen P (Y := (A ⊗ A).left)) (fun V _ k => by
        refine (Fintype.prod_empty _).trans (Eq.symm ?_)
        refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym (fst A A) (snd A A) k)
          (prod_sym (snd A A) (fst A A) k)).trans ?_
        rw [_root_.mul_assoc, inv_mul_cancel_left, mul_inv_cancel]) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
      (fun y I hI => by
        refine (ev e hI).trans (Eq.trans ?_ (val_one _).symm)
        rw [lift_fst, lift_snd, h1 _ y I hI, _root_.mul_one]) _ (lift x y).left z J hJ
    have := (ev (lift x y) hJ).symm.trans (key.trans (val_one _))
    rwa [lift_fst, lift_snd] at this
  · let p₀ := x3 A 0
    let p₁ := x3 A 1
    let p₂ := x3 A 2
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (lift p₀ (lift p₁ p₂)).left)
          (LB.pullGen P _ _ s (lift (p₀ * p₁) p₂).left)) σ.left z J =
          val β.law1 (lift (σ ≫ p₀) (lift (σ ≫ p₁) (σ ≫ p₂))).left z J * val s (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J ∧
        val (LB.mulGen P _ _ _ _ (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift p₀ p₂).left)
          (LB.pullGen P _ _ s (lift p₁ p₂).left)) (LB.pullGen P _ _ β.law2 (lift p₂ (lift p₀ p₁)).left)) σ.left z J =
          val s (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val s (lift (σ ≫ p₁) (σ ≫ p₂)).left z J *
            val β.law2 (lift (σ ≫ p₂) (lift (σ ≫ p₀) (σ ≫ p₁))).left z J := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₃ β.law1 σ hJ _ _ _) (val_pull₂ s σ hJ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))) (val_pull₃ β.law2 σ hJ _ _ _))⟩
    let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
    have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
    have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
    have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
    have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
      surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
    have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    let ρ : T ⟶ G3 A := lift x (lift x' y)
    have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
    have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
    have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
    have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
    have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
    have := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' β.isLB (fun V _ k => by
        refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := ULift.{0} (Fin 3)) (U := V) _
          (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym p₀ p₂ k) (prod_sym p₁ p₂ k))
          (biextension_second_law_product p₂ p₀ p₁ k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := Fin 2) (U := V) _
            (biextension_first_law_product p₀ p₁ p₂ k) (prod_sym (p₀ * p₁) p₂ k)).symm)
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))
      (fun y I hI => by
        refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
        rw [o₁, e₀, e₁, e₂, h1 _ y I hI, law_origin β hI, _root_.mul_one, _root_.one_mul, _root_.one_mul])
      _ ρ.left z J hJ) (ev ρ hJ).2)
    rwa [s₁, r₀, r₁, r₂] at this

end GlobalTheory.BiextSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLawStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.CEqSt H := by
  first | exact @GlobalTheory.RowLaw.cEqSt_of_rLaw | exact GlobalTheory.RowLaw.cEqSt_of_rLaw | (intros; apply GlobalTheory.RowLaw.cEqSt_of_rLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGaugeBilinearTermOfTypeNeStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_gaugeBilinearTerm_of_type_ne : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, HasTeich X V g → ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)) := by
  first | exact @GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne | exact GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne | (intros; apply GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne <;> assumption)
end

