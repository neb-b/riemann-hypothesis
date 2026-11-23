module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldAbelianVarietyAlgebraic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS

theorem top_le_preimage_of_dualFst_comp {X : Scheme.{0}} (g : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ g) ⁻¹ᵁ U) : ⊤ ≤ g ⁻¹ᵁ U := by
  intro x _
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := fun c =>
    ⟨TrivSqZeroExt.inl c, by simp⟩

  have hker : ∀ p : PrimeSpectrum (DualNumber ℂ),
      (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom : Set (DualNumber ℂ)) ⊆ p.asIdeal := by
    intro p a ha
    have ha0 : a.fst = 0 := ha
    have hsq : a ^ 2 = 0 := by
      ext <;> simp [pow_two, ha0]
    exact p.isPrime.mem_of_pow_mem 2 (by rw [hsq]; exact p.asIdeal.zero_mem)
  have hx : x ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ hsurj]
    exact hker x
  obtain ⟨q, rfl⟩ := hx
  exact h (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)

private theorem valAt'_app' {X Z : Scheme.{0}} (y : Sp ℂ ⟶ X) (τ : X ⟶ Z) (O : Z.Opens) (f : Γ(Z, O)) :
    valAt' y (τ ⁻¹ᵁ O) ((τ.app O).hom f) = valAt' (y ≫ τ) O f := by
  unfold valAt'
  by_cases h : ⊤ ≤ y ⁻¹ᵁ τ ⁻¹ᵁ O
  · have h' : ⊤ ≤ (y ≫ τ) ⁻¹ᵁ O := h
    rw [dite_eq_left h, dite_eq_left h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (y ≫ τ) ⁻¹ᵁ O := h
    rw [dite_eq_right h, dite_eq_right h']

private theorem comp_mul_monObj {X Y M : Over (Sp ℂ)} [MonObj M] (f : X ⟶ Y) (g h : Y ⟶ M) :
    f ≫ (g * h) = (f ≫ g) * (f ≫ h) :=
  MonObj.comp_mul f g h

private theorem toUnit_left_eq_hom {T : Over (Sp ℂ)} (t : T ⟶ 𝟙_ (Over (Sp ℂ))) : t.left = T.hom := by
  have := Over.w t
  exact (Category.comp_id _).symm.trans this

def dualZero : 𝟙_ (Over (Sp ℂ)) ⟶ epsR ℂ :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

theorem exists_locDer_of_isDiff {g : ℕ} (A : Over (Sp ℂ)) [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
    (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) (hv : IsTangent v) (hd : u.IsDiff w v) :
    ∃ d, LocDer A.hom A.hom (𝟙 _) (fun _ => 0) ⊤ d ∧ ∀ O f z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O →
      valAt' (u.ex z).left ((𝟙 A.left) ⁻¹ᵁ O) (d O f) = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  classical
  unfold HolUnif.IsDiff at hd
  unfold IsTangent at hv
  have hse : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
    exact Over.w dualZero

  let ρ := pullback.fst A.hom (spMap (algebraMap ℂ (DualNumber ℂ)))
  let π := pullback.snd A.hom (spMap (algebraMap ℂ (DualNumber ℂ)))
  let B : Over (Sp ℂ) := Over.mk (π ≫ spMap (algebraMap ℂ (DualNumber ℂ)))
  let ρ' : B ⟶ A := Over.homMk ρ pullback.condition
  let v' : B ⟶ A := Over.homMk (π ≫ v.left) (by
    rw [Category.assoc, Over.w v]
    rfl)

  let Φ := (ρ' * v').left
  let j : A.left ⟶ pullback A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
    pullback.lift (𝟙 _) (A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (by
      rw [Category.assoc, hse, Category.comp_id, Category.id_comp])
  let j' : A ⟶ B := Over.homMk j (by
    change j ≫ π ≫ _ = _
    rw [pullback.lift_snd_assoc, Category.assoc, hse, Category.comp_id])
  have hj1 : j' ≫ ρ' = 𝟙 A := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hj2 : j' ≫ v' = 1 := by
    apply Over.OverMorphism.ext
    change j ≫ π ≫ v.left = (toUnit A ≫ η).left
    rw [pullback.lift_snd_assoc, Category.assoc, hv, Over.comp_left, toUnit_left_eq_hom]
  have hjΦ : j ≫ Φ = 𝟙 A.left := by
    have h1 : j' ≫ (ρ' * v') = 𝟙 A := by rw [comp_mul_monObj, hj1, hj2, _root_.mul_one]
    exact congrArg (fun t => t.left) h1
  have hΦp : Φ ≫ A.hom = π ≫ spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w (ρ' * v')
  obtain ⟨d, hd1, hd2⟩ := _root_.GlobalTheory.KS.EpsDer.exists_locDer A.left _ A.hom π ρ j (IsPullback.of_hasPullback _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) ℂ (algebraMap ℂ (DualNumber ℂ)) A.left A.hom
    (𝟙 A.left) Φ hjΦ hΦp
  refine ⟨d, ?_, ?_⟩
  · have hD : (fun r : ℂ => (algebraMap ℂ (DualNumber ℂ) r).snd) = fun _ => 0 :=
      funext fun r => rfl
    rw [hD] at hd1
    exact hd1
  · intro O f z hz

    let τ : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A
    have hτ : ∀ z', u.ex z' ≫ τ = u.ex (z + z') := by
      intro z'
      rw [u.ex_add, comp_mul_monObj, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp,
        Category.comp_id]
    have hy : (u.ex z).left ≫ A.hom = 𝟙 _ := Over.w (u.ex z)
    let yt : Sp (DualNumber ℂ) ⟶ pullback A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
      pullback.lift (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (u.ex z).left) (𝟙 _) (by
        rw [Category.assoc, hy]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
    let yt' : epsR ℂ ⟶ B := Over.homMk yt (by
      change yt ≫ π ≫ _ = _
      rw [pullback.lift_snd_assoc, Category.id_comp]
      rfl)
    have hv1 : yt' ≫ ρ' = toUnit _ ≫ u.ex z := by
      apply Over.OverMorphism.ext
      change yt ≫ ρ = _
      rw [pullback.lift_fst, Over.comp_left, toUnit_left_eq_hom]
      rfl
    have hv2 : yt' ≫ v' = v := by
      apply Over.OverMorphism.ext
      change yt ≫ π ≫ v.left = v.left
      rw [pullback.lift_snd_assoc, Category.id_comp]
    have hVz : yt ≫ Φ = v.left ≫ τ.left := by
      have h1 : yt' ≫ (ρ' * v') = v ≫ τ := by
        rw [comp_mul_monObj, hv1, hv2, comp_mul_monObj, ← Category.assoc, comp_toUnit, Category.comp_id]
      exact congrArg (fun t => t.left) h1

    have hfib : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left ≫ τ.left = (u.ex z).left := by
      have h1 : dualZero ≫ v = 1 := by
        apply Over.OverMorphism.ext
        change spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left =
          (toUnit (𝟙_ (Over (Sp ℂ))) ≫ η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left
        rw [hv, toUnit_unit, Category.id_comp]
      have h2 : dualZero ≫ v ≫ τ = u.ex z := by
        rw [← Category.assoc, h1, comp_mul_monObj, ← Category.assoc, comp_toUnit, toUnit_unit,
          Category.id_comp, Category.comp_id, _root_.mul_one]
      exact congrArg (fun t => t.left) h2
    have h0 : ⊤ ≤ (yt ≫ Φ) ⁻¹ᵁ O := by
      rw [hVz]
      apply top_le_preimage_of_dualFst_comp
      rw [hfib]
      exact hz
    rw [← hd2 (u.ex z).left yt (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) O h0 f]
    have hmain : ∀ (G : Sp (DualNumber ℂ) ⟶ A.left) (hG : G = v.left ≫ τ.left) (hG0 : ⊤ ≤ G ⁻¹ᵁ O),
        TrivSqZeroExt.snd (show DualNumber ℂ from
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((G.appLE O ⊤ hG0).hom f)) =
          fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
      rintro G rfl hG0
      have key := hd (τ.left ⁻¹ᵁ O) hG0 ((τ.left.app O).hom f)
      have hfun : (fun z' => valAt' (u.ex z').left (τ.left ⁻¹ᵁ O) ((τ.left.app O).hom f)) =
          fun z' => valAt' (u.ex (z + z')).left O f := by
        funext z'
        rw [valAt'_app', ← Over.comp_left, hτ]
      have hshift : fderiv ℂ (fun z' => valAt' (u.ex (z + z')).left O f) 0 =
          fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z := by
        simpa using fderiv_comp_add_left (𝕜 := ℂ) (f := fun y : Fin g → ℂ => valAt' (u.ex y).left O f)
          (x := (0 : Fin g → ℂ)) z
      rw [hfun, hshift] at key
      rw [← key]
      rw [Scheme.Hom.comp_appLE]
      rfl
    exact hmain _ hVz h0

theorem invariant_field_algebraic : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ w : (Fin P₀.g → ℂ), ∃ d, LocDer P₀.A.hom P₀.A.hom (𝟙 _) (fun _ => 0) ⊤ d ∧ ∀ O f z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → valAt' (u.ex z).left ((𝟙 P₀.A.left) ⁻¹ᵁ O) (d O f) = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  intro P₀ u Hm χ hU w
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := hU.tan₂ w
  exact exists_locDer_of_isDiff P₀.A u w v hv hd

end GlobalTheory.KS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackLocalOnBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GrpLoc

theorem hom_ext_loc {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp hfg using h
  exact Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) X W a
    (fun x => by obtain ⟨y, hy⟩ := hp x; exact ⟨x, y, hy⟩) ha) f g hfg

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X) : x ∈ Set.range a ↔ f x ∈ Set.range g := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨q, hq₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨h.isoPullback.inv q, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hq₁]

theorem mul_left_pre {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have ex : x' = Over.homMk k hk ≫ x := by ext; simp [hx]
  have ey : y' = Over.homMk k hk ≫ y := by ext; simp [hy]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left]
  rfl

theorem isGrpPullback_id_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simpa using w⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  apply hom_ext_loc
  intro t
  obtain ⟨W, xS, B, _, a, hxo, ⟨w0, hw0⟩, hB, hB'⟩ := h (T.hom t)
  refine ⟨pullback T.hom xS, pullback.fst T.hom xS, inferInstance,
    (range_of_isPullback (IsPullback.of_hasPullback T.hom xS) t).2 ⟨w0, hw0⟩, ?_⟩
  let TW : Over W := Over.mk (pullback.snd T.hom xS)
  have cx : (pullback.fst T.hom xS ≫ x.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w x, pullback.condition]
  have cy : (pullback.fst T.hom xS ≫ y.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w y, pullback.condition]
  have cx' : (pullback.fst T.hom xS ≫ x.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cx
  have cy' : (pullback.fst T.hom xS ≫ y.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cy
  let XB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cx) (hB.1.lift_snd _ _ cx)
  let YB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cy) (hB.1.lift_snd _ _ cy)
  let x' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ x.left) cx
  let y' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ y.left) cy
  let x₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ x.left ≫ φ) cx'
  let y₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ y.left ≫ φ) cy'
  have e1 : (x' * y').left = (XB * YB).left ≫ a :=
    hB.2 TW XB YB x' y' (hB.1.lift_fst _ _ cx).symm (hB.1.lift_fst _ _ cy).symm
  have e2 : (x₁ * y₁).left = (XB * YB).left ≫ a ≫ φ := by
    refine hB'.2 TW XB YB x₁ y₁ ?_ ?_
    · simp only [x₁, XB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cx), hB.1.lift_fst, Category.assoc]
    · simp only [y₁, YB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cy), hB.1.lift_fst, Category.assoc]
  have hk : pullback.fst T.hom xS ≫ T.hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have hk' : pullback.fst T.hom xS ≫ (Over.mk (T.hom ≫ 𝟙 S)).hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have m1 := mul_left_pre (pullback.fst T.hom xS) hk x y x' y' rfl rfl
  have m2 := mul_left_pre (pullback.fst T.hom xS) hk' x₀ y₀ x₁ y₁
    (by simp only [x₁, Over.homMk_left, hx]) (by simp only [y₁, Over.homMk_left, hy])
  rw [← m2, e2, ← Category.assoc, ← e1, m1, Category.assoc]

theorem isGrpPullback_local_on_base : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left), IsIso φ → φ ≫ A'.hom = A.hom → (∀ p : S, ∃ (V : Scheme.{0}) (x : V ⟶ S) (B : Over V) (_ : GrpObj B) (a : B.left ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) → IsGrpPullback A A' (𝟙 S) φ := by
  intro S A A' _ _ φ hφ w h
  exact isGrpPullback_id_of_loc φ w h

end GlobalTheory.GrpLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLieCombZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.SquareField
variable {K : Type} [Field K]

def zeroPt (K : Type) [Field K] : 𝟙_ (Over (Sp K)) ⟶ epsR K :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

theorem isTangent_iff {G : Over (Sp K)} [GrpObj G] (v : epsR K ⟶ G) :
    IsTangent v ↔ zeroPt K ≫ v = η[G] := by
  unfold IsTangent
  constructor
  · intro h
    ext1
    simpa [zeroPt] using h
  · intro h
    simpa [zeroPt] using congrArg (fun u => u.left) h

theorem isTangent_one {G : Over (Sp K)} [GrpObj G] : IsTangent (1 : epsR K ⟶ G) := by
  rw [isTangent_iff, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt K ≫ toUnit _) (𝟙 _),
    Category.id_comp]

theorem isTangent_lift {G H : Over (Sp K)} [GrpObj G] [GrpObj H] {v : epsR K ⟶ G} {w : epsR K ⟶ H}
    (hv : IsTangent v) (hw : IsTangent w) : IsTangent (lift v w) := by
  rw [isTangent_iff] at hv hw ⊢
  apply CartesianMonoidalCategory.hom_ext
  · simp [hv]
  · simp [hw]

theorem isLieComb_one {G : Over (Sp K)} [GrpObj G] (v : epsR K ⟶ G) :
    IsLieComb (fun _ : Fin 1 => (1 : K)) (fun _ => v) v := by
  refine ⟨fun _ => v, fun _ => ?_, by simp⟩
  simp only [epsScaleR, one_smul, TrivSqZeroExt.map_id]
  simp [spMap]

theorem isLieComb_zero {G : Over (Sp K)} [GrpObj G] :
    IsLieComb (fun _ : Fin 0 => (1 : K)) (fun _ => (1 : epsR K ⟶ G)) 1 := by
  exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem app_eq_pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (h : Γ(Y, W)) :
    (f.app W).hom h = pbT f h (f ⁻¹ᵁ W) := by
  unfold pbT
  rw [dite_eq_left le_rfl, Scheme.Hom.app_eq_appLE]

theorem constFn_one {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) : constFn q O 1 = 1 := by
  simp [constFn]

private theorem pbT_eq_rsT_pbT_preimage {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀))
    (O : Z.Opens) (hO : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = rsT (pbT f s (f ⁻¹ᵁ O₀)) O := by
  unfold pbT rsT
  rw [dite_eq_left hO, dite_eq_left hO, dite_eq_left (le_refl _), resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem rsT_zero_moduli {Y : Scheme.{0}} {O₀ : Y.Opens} (O : Y.Opens) :
    rsT (0 : Γ(Y, O₀)) O = 0 := by
  unfold rsT
  split <;> simp

section
variable {A₁ A₀ : Over (Sp K)} [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) [IsMonHom f]
  {w : epsR K ⟶ A₁} {dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)}

theorem field_pb {v : epsR K ⟶ A₀} {dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)}
    (hv : IsTangent v) (hd : IsInvDer v dd) (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = v)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = pbT f.left (dd W h) O := by
  obtain ⟨-, hprop⟩ := _root_.GlobalTheory.KS.InvField.main K A₁ w hw
  obtain ⟨-, -, hres, -, -⟩ := hprop dw hdw
  have hkey := _root_.GlobalTheory.KS.InvHom.invDer_along_hom K A₁ A₀ f 1 (fun _ => v) (fun _ => dd) w dw (fun _ => 1) inferInstance
    (fun _ => hv) hw (fun _ => hd) hdw (by rw [e]; exact isLieComb_one v) W h
  simp only [Fin.sum_univ_one, constFn_one] at hkey
  rw [pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, _root_.one_mul, app_eq_pbT,
    ← pbT_eq_rsT_pbT_preimage f.left (dd W h) O hO]

theorem field_pb_zero (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = 1)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = 0 := by
  obtain ⟨-, hprop⟩ := _root_.GlobalTheory.KS.InvField.main K A₁ w hw
  obtain ⟨-, -, hres, -, -⟩ := hprop dw hdw
  have hkey := _root_.GlobalTheory.KS.InvHom.invDer_along_hom K A₁ A₀ f 0 (fun _ => 1) (fun _ _ x => x) w dw (fun _ => 1) inferInstance
    (fun i => i.elim0) hw (fun i => i.elim0) hdw (by rw [e]; exact isLieComb_zero) W h
  simp only [Fin.sum_univ_zero] at hkey
  rw [pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, rsT_zero_moduli]
end

theorem main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] [IsCommMonObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), IsTangent v → IsInvDer v dd → ∀ (n n' : A₀ ⊗ A₀ ⟶ A₀), ((n = fst A₀ A₀ ∧ n' = snd A₀ A₀) ∨ (n = snd A₀ A₀ ∧ n' = fst A₀ A₀)) → ∃ dw : ∀ O : (A₀ ⊗ A₀).left.Opens, Γ((A₀ ⊗ A₀).left, O) → Γ((A₀ ⊗ A₀).left, O), (∀ W f f', dw W (f + f') = dw W f + dw W f') ∧ (∀ W f f', dw W (f * f') = f * dw W f' + f' * dw W f) ∧ (∀ W W' (f : Γ((A₀ ⊗ A₀).left, W)), W' ≤ W → dw W' (rsT f W') = rsT (dw W f) W') ∧ (∀ W a, dw W (constFn (A₀ ⊗ A₀).hom W a) = 0) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ (fst A₀ A₀ * snd A₀ A₀).left ⁻¹ᵁ W → dw O (pbT (fst A₀ A₀ * snd A₀ A₀).left h O) = pbT (fst A₀ A₀ * snd A₀ A₀).left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n.left ⁻¹ᵁ W → dw O (pbT n.left h O) = pbT n.left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n'.left ⁻¹ᵁ W → dw O (pbT n'.left h O) = 0) := by
  intro K _ A₀ _ _ v dd hv hd n n' hnn'
  obtain ⟨w, hw, hwn, hwn', hwm⟩ : ∃ w : epsR K ⟶ A₀ ⊗ A₀, IsTangent w ∧ w ≫ n = v ∧ w ≫ n' = 1 ∧
      w ≫ (fst A₀ A₀ * snd A₀ A₀) = v := by
    rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨lift v 1, isTangent_lift hv isTangent_one, lift_fst _ _, lift_snd _ _, by
        rw [MonObj.comp_mul, lift_fst, lift_snd, _root_.mul_one]⟩
    · exact ⟨lift 1 v, isTangent_lift isTangent_one hv, lift_snd _ _, lift_fst _ _, by
        rw [MonObj.comp_mul, lift_fst, lift_snd, _root_.one_mul]⟩
  have hn : IsMonHom n := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance
  have hn' : IsMonHom n' := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance
  have hm : IsMonHom (fst A₀ A₀ * snd A₀ A₀) := by
    rw [← MonObj.mul_eq_mul]
    infer_instance
  obtain ⟨-, hprop⟩ := _root_.GlobalTheory.KS.InvField.main K (A₀ ⊗ A₀) w hw
  obtain ⟨dw, hdw⟩ := (_root_.GlobalTheory.KS.InvField.main K (A₀ ⊗ A₀) w hw).1
  obtain ⟨hadd, hmul, hres, hconst, -⟩ := hprop dw hdw
  refine ⟨dw, hadd, hmul, hres, hconst, ?_, ?_, ?_⟩
  · intro W h O hO
    exact field_pb _ hv hd hw hdw hwm W h O hO
  · intro W h O hO
    exact field_pb _ hv hd hw hdw hwn W h O hO
  · intro W h O hO
    exact field_pb_zero _ hw hdw hwn' W h O hO

end GlobalTheory.KS.SquareField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem morphisms_descend_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  intro K _ K₀ X₀ X p₀ p φ Z q _ _ _ I _ f hX hf
  have hX' : IsPullback φ p p₀ (spMap (algebraMap K₀ K)) := hX
  obtain ⟨R, g, ⟨s, rfl⟩, -, hg⟩ := Spread.exists_fg_forall_comp_eq (A := K) p₀ q
    (fun j ↦ hX'.isoPullback.inv ≫ f j)
    (fun j ↦ by rw [Category.assoc, hf, IsPullback.isoPullback_inv_fst_assoc]) ⊥ Subalgebra.fg_bot
  refine ⟨s, fun K₁ h hs X₁ p₁ φ₁ ψ h₁ hψ₁ hψ₂ ↦ ?_⟩
  have hle : ∀ x ∈ Algebra.adjoin K₀ (s : Set K), x ∈ K₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let e : Algebra.adjoin K₀ (s : Set K) →+* K₁ :=
    (Algebra.adjoin K₀ (s : Set K)).val.toRingHom.codRestrict K₁ fun x ↦ hle x x.2
  have he₁ : spMap e ≫ spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K))) =
      spMap (Subfield.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have he₂ : spMap K₁.subtype ≫ spMap e =
      spMap (Algebra.adjoin K₀ (s : Set K)).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let u : X₁ ⟶ pullback p₀ (spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K)))) :=
    pullback.lift φ₁ (p₁ ≫ spMap e) (by rw [Category.assoc, he₁, h₁.w])
  have hu : ψ ≫ u = hX'.isoPullback.hom ≫ Spread.bcMap p₀ (Algebra.adjoin K₀ (s : Set K)).val := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst,
        pullback.lift_fst, hψ₁]
    · rw [Category.assoc, Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc,
        pullback.lift_snd, ← Category.assoc, hψ₂, Category.assoc, he₂]
  refine ⟨fun j ↦ u ≫ g j, fun j ↦ ⟨?_, ?_⟩⟩
  · rw [← Category.assoc, hu, Category.assoc, (hg j).2, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, (hg j).1, pullback.lift_fst_assoc]

end GlobalTheory
end

