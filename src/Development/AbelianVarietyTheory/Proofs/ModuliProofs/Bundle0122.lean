module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqOneOfTranslDiffTrivialModel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.PrincipalModel
open GlobalTheory.UU GlobalTheory.AbLaw

theorem exists_common_overfield {k A B : Type} [Field k] [Field A] [Field B] (f : k →+* A) (g : k →+* B) :
    ∃ (L : Type) (_ : Field L) (a : A →+* L) (b : B →+* L), a.comp f = b.comp g := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct k A B)
  refine ⟨TensorProduct k A B ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg _ (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := k) (A := A) (B := B))

theorem exists_valuationSubring {W F Ω : Type} [CommRing W] [IsLocalRing W] [Field F] [Field Ω] (φ : W →+* F)
    (f : W →+* Ω) [IsLocalHom f] : ∃ (O : ValuationSubring F) (j : W →+* O) (L : Type) (_ : Field L) (a : Ω →+* L)
      (g : O →+* L), (algebraMap O F).comp j = φ ∧ IsLocalHom g ∧ a.comp f = g.comp j := by
  obtain ⟨O, h, hl⟩ := IsLocalRing.exists_factor_valuationRing φ
  let j : W →+* O := φ.codRestrict O.toSubring h
  have : IsLocalHom j := hl
  obtain ⟨L, _, a, b, e⟩ := exists_common_overfield (IsLocalRing.ResidueField.lift f) (IsLocalRing.ResidueField.map j)
  refine ⟨O, j, L, inferInstance, a, b.comp (IsLocalRing.residue O), rfl, inferInstance, ?_⟩
  rw [← IsLocalRing.ResidueField.lift_comp_residue f, ← RingHom.comp_assoc, e, RingHom.comp_assoc,
    IsLocalRing.ResidueField.map_comp_residue, RingHom.comp_assoc]

theorem exists_embedding (V K W : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    [CommRing W] [IsDomain W] [Algebra V W] [Module.Finite V W] (h : Function.Injective (algebraMap V W)) :
    ∃ φ : W →+* AlgebraicClosure K, Function.Injective φ ∧ φ.comp (algebraMap V W) =
      (algebraMap K (AlgebraicClosure K)).comp (algebraMap V K) := by
  have i : Function.Injective (algebraMap V (AlgebraicClosure K)) := by
    rw [IsScalarTower.algebraMap_eq V K]
    exact (algebraMap K _).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  have : FaithfulSMul V (AlgebraicClosure K) := (faithfulSMul_iff_algebraMap_injective _ _).2 i
  let φ : W →ₐ[V] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    change Ideal.comap (algebraMap V W) (RingHom.ker φ.toRingHom) = ⊥
    rw [RingHom.comap_ker, show φ.toRingHom.comp (algebraMap V W) = algebraMap V _ from φ.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).1 i
  · rw [← IsScalarTower.algebraMap_eq]; exact φ.comp_algebraMap

theorem triv_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} (x : T ⟶ A) (g : T' ⟶ T)
    (h : Triv (translDiff A L x)) : Triv (translDiff A L (g ≫ x)) := by
  obtain ⟨d, hd⟩ := h
  have h4 : ∃ w : LB.Gen (LB.LinComb L _ _), w.IsGen := ⟨_, DVR.pullGen_isGen _ _ _ d hd (g ▷ A).left⟩
  have h3 : (fun k : Fin 2 => (g ▷ A).left ≫ ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k) =
      ![(lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext k
    fin_cases k
    · change (g ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (g ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

theorem cubWeil_generic (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : RigLB A} (c : CubicalStr A L) {O F k : Type} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F] [Field k] (g : O →+* k) [IsLocalHom g]
    {p : Sp O ⟶ S} {n : ℕ} (hn : IsUnit (n : O)) (X : Over.mk p ⟶ A) (hX : X ^ n = 1)
    {pk : Sp k ⟶ S} (ρk : Over.mk pk ⟶ Over.mk p) (hk : ρk.left = spMap g)
    {pF : Sp F ⟶ S} (ρF : Over.mk pF ⟶ Over.mk p) (hF : ρF.left = spMap (algebraMap O F))
    (ht : Triv (translDiff A L.L (ρk ≫ X))) (y : Over.mk pF ⟶ A) (hy : y ^ n = 1) :
    CubWeil c n (ρF ≫ X) y 1 := by
  have := hA.proper
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have w : y.left ≫ A.hom = spMap (algebraMap O F) ≫ p := (Over.w y).trans ((Over.w ρF).symm.trans (by rw [hF]; rfl))
  obtain ⟨l, hl₁, hl₂⟩ := (hE { R := O, K := F, commSq := ⟨w⟩, .. }).exists_lift
  let Y : Over.mk p ⟶ A := Over.homMk l hl₂
  have hYy : ρF ≫ Y = y := Over.OverMorphism.ext ((congrArg (· ≫ l) hF).trans hl₁)
  have hY : Y ^ n = 1 := by
    refine over_points_ext_of_injective S A O F _ (IsFractionRing.injective O F) p _ _ ?_
    have e : ρF ≫ Y ^ n = ρF ≫ 1 := by rw [MonObj.comp_pow, hYy, hy, MonObj.comp_one]
    have e' : ρF.left ≫ (Y ^ n).left = ρF.left ≫ (1 : Over.mk p ⟶ A).left := congrArg (fun q => q.left) e
    rw [hF] at e'
    exact e'
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil c hX hY
  have h₁ := hζ.comp ρk
  have h₂ := KerPair.cubWeil_of_gen hG S A hA L c n _ _ _ h₁.1 h₁.2.1 ht
  have h₃ := h₁.unique h₂
  rw [hk] at h₃
  have h₄ : ζ = 1 := unit_eq_one_of_localHom g hn hζ.pow_eq_one h₃
  have h₅ := hζ.comp ρF
  rwa [h₄, map_one, hYy] at h₅

theorem nondeg_of_isGrpPullback {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {B : Over S} [GrpObj B] [IsCommMonObj B]
    {L' : LB A.left} {L : LB B.left} (hL' : L'.IsLB) (hL : L.IsLB) {f : S' ⟶ S} {φ : A.left ⟶ B.left}
    (hp : IsGrpPullback A B f φ) (hi : LBIso L' (L.pull φ)) (T : Over S') (n : ℕ)
    (H : ∀ u : T ⟶ A, u ^ n = 1 → (∀ z : T ⟶ A, z ^ n = 1 → WeilIs A L' n u z 1) → u = 1)
    (x : Over.mk (T.hom ≫ f) ⟶ B) (hx : x ^ n = 1)
    (h : ∀ y : Over.mk (T.hom ≫ f) ⟶ B, y ^ n = 1 → WeilIs B L n x y 1) : x = 1 := by
  let β := pushHom hp T
  have inj : Function.Injective β := fun a b e =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))
  let u : T ⟶ A := Over.homMk (hp.1.lift x.left T.hom (Over.w x)) (hp.1.lift_snd _ _ _)
  have hu : β u = x := Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  have hun : u ^ n = 1 := inj (by rw [map_pow, hu, map_one]; exact hx)
  have : u = 1 := H u hun fun z hz =>
    (weilIs_grpPullback_of_comm _ _ B A f φ L L' hL hL' hp hi T n u z x (β z) 1
      (congrArg (fun q => q.left) hu.symm) rfl).2 (h _ (by rw [← map_pow, hz, map_one]))
  rw [← hu, this, map_one]

theorem eq_one_of_cubWeil (hL : Laws) {S S' : Scheme.{0}} (P : PolAV S') {B : Over S} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {L : RigLB B} (c : CubicalStr B L) {f : S' ⟶ S} {φ : P.A.left ⟶ B.left}
    (hp : IsGrpPullback P.A B f φ) (hi : LBIso P.L (L.L.pull φ)) {F : Type} [Field F] [IsAlgClosed F]
    (t : Sp F ⟶ S') {n : ℕ} (hn : (n : F) ≠ 0) (x : Over.mk (t ≫ f) ⟶ B) (hx : x ^ n = 1)
    (h : ∀ y : Over.mk (t ≫ f) ⟶ B, y ^ n = 1 → CubWeil c n x y 1) : x = 1 := by
  obtain ⟨P', g, hg, -, hmul, tw, htw⟩ := hL.polBaseChange S' _ t P
  have hp' : IsGrpPullback P'.A P.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  have := P.isAb.comm
  have H := nondeg_of_isGrpPullback P'.isLB P.isLB hp' (LBIso.symm ⟨tw, htw⟩) (baseOver _) n
    (hL.weilNondeg F P' n hn)
  have e : (baseOver (Sp F)).hom ≫ t = t := Category.id_comp t
  rw [e] at H
  exact nondeg_of_isGrpPullback P.isLB L.isLB hp hi (Over.mk t) n H x hx fun y hy =>
    (cubWeil_iff_weilIs hL.globalFns hB hx hy 1).1 (h y hy)

theorem torsion_eq_one_of_triv : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ n : ℕ, (n : Ω) ≠ 0 → ∀ x : Over.mk (spMap f) ⟶ B, x ^ n = 1 → GlobalTheory.AbLaw.Triv (translDiff B M.L.L x) → x = 1 := by
  intro hL _ V K _ _ _ _ _ _ P B _ _ M φ hB hp hi _ Ω _ _ f hf n hn x hx ht
  have := hB.smooth
  have := hB.proper
  have hnV : IsUnit (n : V) := isUnit_of_map_unit f _ (by rw [map_natCast]; exact hn.isUnit)
  obtain ⟨W, _, _, _, _, _, f', _, inj, _, _, hf', lifts⟩ := GlobalTheory.exists_finite_extension_torsion_lift hL.unramExt V B n
    hnV Ω f hf {x} (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hx)
  obtain ⟨X, hX, hXx⟩ := lifts x (Finset.mem_singleton_self x)
  obtain ⟨ψ, hψ, eψ⟩ := exists_embedding V K W inj
  obtain ⟨O, j, k, _, a, g, hj, _, e⟩ := exists_valuationSubring ψ f'
  have sp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C),
      spMap (v.comp u) = spMap v ≫ spMap u := fun u v => by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let TW : Over (Sp V) := Over.mk (spMap (algebraMap V W))
  let TO : Over (Sp V) := Over.mk (spMap j ≫ spMap (algebraMap V W))
  let σ : TO ⟶ TW := Over.homMk (spMap j) rfl
  let ρk : Over.mk (spMap a ≫ spMap f) ⟶ TO := Over.homMk (spMap g) (by
    show spMap g ≫ spMap j ≫ spMap (algebraMap V W) = spMap a ≫ spMap f
    rw [← sp, ← sp, ← sp, ← RingHom.comp_assoc, ← e, RingHom.comp_assoc, hf'])
  let ρF : Over.mk (spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap (algebraMap V K)) ⟶ TO :=
    Over.homMk (spMap (algebraMap O (AlgebraicClosure K))) (by
      show spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j ≫ spMap (algebraMap V W) =
        spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap (algebraMap V K)
      rw [← sp, ← sp, ← sp, ← RingHom.comp_assoc, hj, eψ])
  let τ : Over.mk (spMap a ≫ spMap f) ⟶ Over.mk (spMap f) := Over.homMk (spMap a) rfl
  have hτ : τ ≫ x = ρk ≫ σ ≫ X := Over.OverMorphism.ext (by
    show spMap a ≫ x.left = spMap g ≫ spMap j ≫ X.left
    rw [← hXx, ← Category.assoc, ← Category.assoc, ← sp, ← sp, e])
  have hσ : (σ ≫ X) ^ n = 1 := by rw [← MonObj.comp_pow, hX, MonObj.comp_one]
  have hnO : IsUnit (n : O) := by simpa using hnV.map (j.comp (algebraMap V W))
  have key : ρF ≫ σ ≫ X = 1 := eq_one_of_cubWeil hL P hB M.c hp hi _
    (by simpa using (hnO.map (algebraMap O (AlgebraicClosure K))).ne_zero) _
    (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one])
    (cubWeil_generic hL.globalFns hB M.c g hnO (σ ≫ X) hσ ρk rfl ρF rfl (hτ ▸ triv_comp x τ ht))
  have hX1 : X = 1 := by
    refine over_points_ext_of_injective _ B W _ ψ hψ _ _ _ ?_
    have e₁ : (ρF ≫ σ) ≫ X = (ρF ≫ σ) ≫ 1 := by rw [Category.assoc, key, MonObj.comp_one]
    have e₂ : (spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j) ≫ X.left =
        (spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j) ≫ (1 : TW ⟶ B).left := congrArg (fun q => q.left) e₁
    rw [← sp, hj] at e₂
    exact e₂
  let ρ : Over.mk (spMap f) ⟶ TW := Over.homMk (spMap f') (by
    show spMap f' ≫ spMap (algebraMap V W) = spMap f
    rw [← sp, hf'])
  have : x = ρ ≫ X := Over.OverMorphism.ext hXx.symm
  rw [this, hX1]
  exact MonObj.comp_one _

end GlobalTheory.PrincipalModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingDiagonalBundleOfEighthPowerForm
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.WeilDown

def qf (W : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) : ℤ := ∑ u, ∑ u', W u u' * (v u * v u')

theorem sum_symm (W : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) :
    ∑ u, ∑ u', (W + W.transpose) u u' * (v u * v u') = 2 * qf W v := by
  simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, two_mul, qf]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem qf_nonneg {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) (v : Fin 8 → ℤ) : 0 ≤ qf W v := by
  have h := hW.1.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
  have e : (((2 * qf W v : ℤ)) : ℝ) = star (fun i => (v i : ℝ)) ⬝ᵥ
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)).mulVec (fun i => (v i : ℝ)) := by
    rw [← sum_symm]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [← e] at h
  have : (0 : ℤ) ≤ 2 * qf W v := by exact_mod_cast h
  omega

theorem qf_add (W : Matrix (Fin 8) (Fin 8) ℤ) (a b : Fin 8 → ℤ) :
    qf W (a + b) = qf W a + qf W b + b ⬝ᵥ (W + W.transpose).mulVec a := by
  simp only [qf, dotProduct, Matrix.mulVec, Matrix.add_apply, Matrix.transpose_apply, Pi.add_apply, add_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have e₁ : ∑ u, ∑ u', W u u' * (b u * a u') = ∑ u, ∑ u', b u * (W u u' * a u') :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e₂ : ∑ u, ∑ u', W u u' * (a u * b u') = ∑ u, ∑ u', b u * (W u' u * a u') := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e₁, e₂]
  ring

theorem exists_qf_one {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) :
    ∃ a b, qf W (a + b) = qf W a + qf W b + 1 := by
  refine ⟨(W + W.transpose).adjugate.mulVec (Pi.single 0 1), Pi.single 0 1, ?_⟩
  rw [qf_add, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hW.2]
  simp

theorem eq_of_zpow_qf {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) {U : Type*} [CommGroup U] (a b : U)
    (h : ∀ v, a ^ qf W v = b ^ qf W v) : a = b := by
  obtain ⟨v, w, e⟩ := exists_qf_one hW
  have := h (v + w)
  rw [e, zpow_add, zpow_add, zpow_add, zpow_add, h v, h w, zpow_one, zpow_one] at this
  exact mul_left_cancel this

theorem omegaStd_smul {h : ℕ} (m n : ℤ) (x y : Fin h ⊕ Fin h → ℤ) :
    omegaStd (m • x) (n • y) = m * n * omegaStd x y := by
  simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

section Pairing

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} {T T' : Over S}

def q (π : Pic (A ⊗ A).left) (a b : T ⟶ A) : Pic T.left := pull (lift a b).left π

theorem qp (π : Pic (A ⊗ A).left) (t : T' ⟶ T) (a b : T ⟶ A) : pull t.left (q π a b) = q π (t ≫ a) (t ≫ b) := by
  rw [q, q, ← pull_comp, ← Over.comp_left, comp_lift]

theorem q_comm {π : Pic (A ⊗ A).left} (e : π = pull (lift (snd A A) (fst A A)).left π) (a b : T ⟶ A) :
    q π a b = q π b a := by
  have k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left := by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
  rw [q, q, ← k, pull_comp, ← e]

variable [GrpObj A]

theorem q_mul {P : LB (A ⊗ A).left} (hP : P.IsLB) (a a' b : T ⟶ A)
    (h : ∃ t : (LB.LinComb P (K := Fin 3) ![(lift (a * a') b).left, (lift a b).left, (lift a' b).left]
      ![1, -1, -1]).Gen, t.IsGen) : q (cls P hP) (a * a') b = q (cls P hP) a b + q (cls P hP) a' b := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 h
  rw [cls_linComb hP, Fin.sum_univ_three] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
  rw [← sub_eq_zero, ← e, q, q, q]
  abel

theorem cls_theta {D : LB A.left} (hD : D.IsLB) (k : ℤ) (x : T ⟶ A) (h : (Out.thetaLB A D k x).IsLB) :
    cls _ h = k • pull (snd T A).left (cls D hD) + (-k) • pull ((fst T A ≫ x) * snd T A).left (cls D hD) := by
  refine (cls_linComb hD _ _ h).trans ?_
  rw [Fin.sum_univ_two]
  rfl

variable [IsCommMonObj A]

theorem q_zpow {π : Pic (A ⊗ A).left} (ql : ∀ a a' b : T ⟶ A, q π (a * a') b = q π a b + q π a' b)
    (a b : T ⟶ A) (n : ℤ) : q π (a ^ n) b = n • q π a b := by
  have := BilinCalc.map_prod_zpow (fun z => q π z b) (fun s t => ql s t b) (fun _ : Fin 1 => a) (fun _ => n)
  simpa using this

theorem exists_theta {π : Pic (A ⊗ A).left} {D : LB A.left} (hD : D.IsLB) (cD : cls D hD = q π (𝟙 A) (𝟙 A))
    (ql : ∀ a a' b : T ⊗ A ⟶ A, q π (a * a') b = q π a b + q π a' b) (qs : ∀ a b : T ⊗ A ⟶ A, q π a b = q π b a)
    (k : ℕ) (x : T ⟶ A) (hx : x ^ k = 1) (h0 : q π x x = 0) : ∃ θ : Out.ThetaGrp A D k T, θ.pt = x := by
  have hz : cls (Out.thetaLB A D k x) (LB.isLB_linComb hD _ _) = 0 := by
    have e₁ : q π (fst T A ≫ x) (fst T A ≫ x) = 0 := by
      rw [← qp, h0, map_zero]
    have e₂ : (k : ℤ) • q π (fst T A ≫ x) (snd T A) = 0 := by
      rw [← q_zpow ql, zpow_natCast, ← MonObj.comp_pow, hx, MonObj.comp_one, ← zpow_zero 1, q_zpow ql, zero_smul]
    refine (cls_theta hD _ _ _).trans ?_
    rw [cD, qp, qp, Category.comp_id, Category.comp_id, ql, qs (fst _ _ ≫ _), qs (snd _ _) (_ * _),
      ql, ql, e₁, qs (snd _ _) (fst _ _ ≫ _)]
    simp only [smul_add, neg_smul, e₂, smul_zero]
    abel
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hz
  exact ⟨⟨x, t, ht⟩, rfl⟩

end Pairing


open GlobalTheory.CechPic in
theorem weilIs_diag : Out.GlobalFnsSt → ∀ (h k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left) (K : Type) [Field K] (p : Sp K ⟶ S) (lev : (Fin h ⊕ Fin h → ℤ) → (Over.mk p ⟶ A)) (c : Γ((Over.mk p).left, ⊤)ˣ), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ G), (∀ u, y ≫ pr u = lev (X u)) → (∀ u, y' ≫ pr u = lev (Y u)) → Out.WeilIs G L k y y' (c ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v))) → ∀ x y, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (lev x) (lev y) (c ^ (2 * omegaStd x y)) := by
  intro hG h k W S G A _ _ _ _ pr L P K _ p lev c hW hGab hA hpr hprod hL hP hsym hbi hLP hadd htor hweil x y
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have ql : ∀ {T : Over S} (a a' b : T ⟶ A), q (cls P hP) (a * a') b = q (cls P hP) a b + q (cls P hP) a' b :=
    fun {T} a a' b => q_mul hP a a' b (hbi T a a' b).1
  have qs : ∀ {T : Over S} (a b : T ⟶ A), q (cls P hP) a b = q (cls P hP) b a :=
    q_comm ((cls_eq_iff hP (pull_isLB hP _)).2 hsym)
  have cD : cls _ hD = q (cls P hP) (𝟙 A) (𝟙 A) := rfl
  have q0 : ∀ a b : Over.mk p ⟶ A, q (cls P hP) a b = 0 := fun a b =>
    (cls_eq_zero_iff (pull_isLB hP (lift a b).left)).2 (DVR.exists_gen_of_local (V := K) P hP _ _)
  have lift_ : ∀ z, ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (Over.mk p), θ.pt = lev z := fun z =>
    exists_theta hD cD ql qs k _ (htor z) (q0 _ _)
  have loc : ∀ z (s : (Over.mk p).left), ∃ V : (Over.mk p).left.Opens, s ∈ V ∧
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (Out.overRes V), θ.pt = Out.overResι V ≫ lev z :=
    fun z s => by
      obtain ⟨θ, e⟩ := lift_ z
      obtain ⟨θ', e'⟩ := CommutatorPairing.exists_pull hD θ (Out.overResι ⊤)
      exact ⟨⊤, trivial, θ', by rw [e', e]⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (loc x) (loc y)
  suffices c₀ = c ^ (2 * omegaStd x y) from this ▸ hc₀
  refine eq_of_zpow_qf hW _ _ fun v => ?_
  have levz : ∀ z (n : ℤ), lev (n • z) = lev z ^ n := fun z n => by
    let F : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (Over.mk p ⟶ A) :=
      MonoidHom.mk' (fun w => lev w.toAdd) fun a b => hadd _ _
    exact map_zpow F (Multiplicative.ofAdd z) n
  obtain ⟨ψ, hψ, -⟩ := hprod A fun u => 𝟙 A ^ v u
  have ext : ∀ {T : Over S} (a b : T ⟶ G), (∀ u, a ≫ pr u = b ≫ pr u) → a = b := fun {T} a b e =>
    (hprod T fun u => b ≫ pr u).unique e fun _ => rfl
  have hc : ∀ {T : Over S} (a : T ⟶ A) u, (a ≫ ψ) ≫ pr u = a ^ v u := fun a u => by
    rw [Category.assoc, hψ, GrpObj.comp_zpow, Category.comp_id]
  have hmon : IsMonHom ψ := by
    constructor
    · refine ext _ _ fun u => ?_
      have e₁ : (η[A] : 𝟙_ _ ⟶ A) = 1 := by rw [Hom.one_def]; simp
      rw [hc, IsMonHom.one_hom, e₁, one_zpow]
    · refine ext _ _ fun u => ?_
      have e₁ : μ[A] = fst A A * snd A A := by rw [Hom.mul_def]; simp
      have e₂ : (ψ ⊗ₘ ψ) ≫ μ[G] = (fst A A ≫ ψ) * (snd A A ≫ ψ) := by rw [Hom.mul_def]; congr 1
      rw [hc, e₁, e₂, MonObj.mul_comp, hc, hc, mul_zpow]
  have hd : ((qf W v).toNat : ℤ) = qf W v := Int.toNat_of_nonneg (qf_nonneg hW v)
  have hn : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (qf W v).toNat).IsLB := LB.isLB_linComb hD _ _
  have hiso : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (qf W v).toNat) (L.pull ψ.left) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← cls_eq_iff hn (pull_isLB hL _), cls_lbPow hD, cD, cls_pull hL,
      (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP, cls_linComb hP, map_sum, ← natCast_zsmul, hd, qf,
      ← Fintype.sum_prod_type', Finset.sum_smul]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul]
    refine Eq.trans ?_ (congrArg _ (qp (cls P hP) ψ (pr uv.1) (pr uv.2))).symm
    rw [hψ, hψ, q_zpow ql, qs _ (_ ^ _), q_zpow ql, smul_smul, smul_smul, _root_.mul_assoc]
  have key := (weilIs_along_hom hG S A G ψ _ L _ k _ (lev x) (lev y) c₀ _ hA hGab hD hL hmon hiso
    (hweil (fun u => v u • x) (fun u => v u • y) _ _ (fun u => by rw [hc, levz]) (fun u => by rw [hc, levz]))).2 hc₀
  rw [← hd, zpow_natCast, ← key, hd, ← zpow_mul]
  congr 1
  have e : ∀ a b : ℤ, a * (b * omegaStd x y) = a * b * omegaStd x y := fun a b => (_root_.mul_assoc _ _ _).symm
  simp only [omegaStd_smul, e, ← Finset.sum_mul]
  rw [sum_symm]
  ring

end GlobalTheory.WeilDown
end
end

