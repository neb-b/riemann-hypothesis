module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionMulCardToricTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace SemiAbTorsionCount

theorem card_pow_eq_one_of_extension {T G B : Type} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 ↔ ∃ t, i t = x)
    (hq : Function.Surjective q) (n : ℕ) (hT : ∀ t : T, ∃ s : T, s ^ n = t) :
    Nat.card {x : G // x ^ n = 1} =
      Nat.card {b : B // b ^ n = 1} * Nat.card {t : T // t ^ n = 1} := by
  let K : Subgroup G := (powMonoidHom n : G →* G).ker
  let f : K →* B := q.comp K.subtype
  have h0 : Nat.card {x : G // x ^ n = 1} = Nat.card K := rfl
  have h1 : Nat.card {b : B // b ^ n = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ⟨fun hb => ?_, ?_⟩)
    · obtain ⟨x, rfl⟩ := hq b
      obtain ⟨t, ht⟩ := (hk (x ^ n)).1 (by rw [map_pow, hb])
      obtain ⟨s, rfl⟩ := hT t
      refine ⟨⟨x / i s, ?_⟩, ?_⟩
      · change (x / i s) ^ n = 1
        rw [div_pow, ← map_pow, ht, div_self']
      · change q (x / i s) = q x
        rw [map_div, (hk _).2 ⟨s, rfl⟩, div_one]
    · rintro ⟨x, rfl⟩
      have hx : x.1 ^ n = 1 := x.2
      change q x.1 ^ n = 1
      rw [← map_pow, hx, map_one]
  have h2 : Nat.card {t : T // t ^ n = 1} = Nat.card f.ker := by
    refine Nat.card_eq_of_bijective (fun t => ⟨⟨i t.1, ?_⟩, (hk _).2 ⟨t.1, rfl⟩⟩) ⟨?_, ?_⟩
    · change i t.1 ^ n = 1
      rw [← map_pow, t.2, map_one]
    · intro a b h
      exact Subtype.ext (hi (congrArg (fun z : f.ker => z.1.1) h))
    · rintro ⟨⟨x, hx⟩, hx'⟩
      obtain ⟨t, rfl⟩ := (hk x).1 hx'
      have hx₁ : i t ^ n = 1 := hx
      exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩
  rw [h0, h1, h2, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem nonempty_hom_mulEquiv_pi (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (M : Type) [CommGroup M] :
    Nonempty ((Multiplicative X →* M) ≃* (Fin (Module.finrank ℤ X) → M)) := by
  let b := Module.finBasis ℤ X
  let ev : (Multiplicative X →* M) →* (Fin (Module.finrank ℤ X) → M) :=
    { toFun := fun t j => t (Multiplicative.ofAdd (b j))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨MulEquiv.ofBijective ev ⟨fun s t h => ?_, fun v => ?_⟩⟩
  · have : (MonoidHom.toAdditiveRight s).toIntLinearMap = (MonoidHom.toAdditiveRight t).toIntLinearMap :=
      b.ext fun j => congrArg Additive.ofMul (congrFun h j)
    ext x
    exact congrArg Additive.toMul (DFunLike.congr_fun this x)
  · refine ⟨AddMonoidHom.toMultiplicativeLeft
      (b.constr ℤ (fun j => Additive.ofMul (v j))).toAddMonoidHom, funext fun j => ?_⟩
    exact congrArg Additive.toMul (b.constr_basis ℤ (fun j => Additive.ofMul (v j)) j)

theorem nonempty_torus_points_mulEquiv (k : Type) [Field k] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] :
    Nonempty ((𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) ≃* (Fin (Module.finrank ℤ X) → kˣ)) := by
  obtain ⟨e₂⟩ := nonempty_hom_mulEquiv_pi X Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ
  let e₃ : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  exact ⟨((splitTorusPointsEquiv (Sp k) X (𝟙_ (Over (Sp k)))).trans e₂).trans
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv e₃.toMulEquiv)⟩

theorem divisible_and_card {k : Type} [Field k] [IsAlgClosed k] {T : Type} [Group T] {t : ℕ}
    (e : T ≃* (Fin t → kˣ)) (N : ℕ) (hN : (N : k) ≠ 0) :
    (∀ x : T, ∃ s : T, s ^ N = x) ∧ Nat.card {x : T // x ^ N = 1} = N ^ t := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  haveI : NeZero N := ⟨hN0⟩
  haveI : NeZero (N : k) := ⟨hN⟩
  constructor
  · intro x
    have : ∀ u : kˣ, ∃ s : kˣ, s ^ N = u := fun u => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) (Nat.pos_of_ne_zero hN0)
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow hN0] at hz
        exact u.ne_zero hz.symm
      exact ⟨Units.mk0 z hz0, Units.ext hz⟩
    choose r hr using this
    refine ⟨e.symm fun j => r (e x j), e.injective ?_⟩
    rw [map_pow, e.apply_symm_apply]
    exact funext fun j => hr _
  · have h1 : Nat.card {x : T // x ^ N = 1} = Nat.card (Fin t → rootsOfUnity N k) := by
      refine Nat.card_congr ((e.toEquiv.subtypeEquiv (q := fun v => ∀ j, v j ∈ rootsOfUnity N k)
        fun x => ?_).trans Equiv.subtypePiEquivPi)
      rw [← e.map_eq_one_iff, map_pow, funext_iff]
      rfl
    rw [h1, Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card,
      Fintype.card_fin]

theorem dim_eq {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g g' : ℕ)
    (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' E.B.hom) :
    g = g' + @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ := by
  letI := E.addCommGroup
  letI := E.grpB
  have := E.free
  have := E.finite
  obtain ⟨y⟩ : Nonempty ↥(Sp k) := inferInstance
  have := E.i_hom
  have := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim E.q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ E.X :=
    H1.dim_base (E.isKernel.map (Over.forget _)) d₁ (H1.torus_dim (Sp k) E.X) (eSec _ y)
      ((congrArg (fun f => f.left y ∈ W) (IsMonHom.one_hom E.i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w E.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

end SemiAbTorsionCount

open SemiAbTorsionCount

theorem card_torsion_mul_card_toric_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (T : TorusExtension G) (g N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} * Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ T.i} = N ^ (2 * g) := by
  intro k _ _ G _ E g N hG dG hN
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := hG.comm
  haveI := E.q_surjective
  haveI := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  have hk := E.isKernel
  obtain ⟨g', dB⟩ := GlobalTheory.AbelianDim.exists_relDim k E.B E.isAbelian
  have hg := dim_eq G E g g' dG dB
  obtain ⟨e⟩ := nonempty_torus_points_mulEquiv k E.X
  obtain ⟨hdiv, hcard⟩ := divisible_and_card e N hN
  have hB := _root_.GlobalTheory.card_torsion_abelianVariety k E.B g' N E.isAbelian dB hN
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  have h1 := card_pow_eq_one_of_extension i (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))) hi
    (fun x => ⟨fun hx => ?_, ?_⟩) (fun x => ?_) N hdiv
  · have h2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ E.i} =
        N ^ Module.finrank ℤ E.X := by
      rw [← hcard]
      refine (Nat.card_eq_of_bijective
        (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩).symm
      · intro a b h
        exact Subtype.ext (hi (congrArg Subtype.val h))
      · rintro ⟨x, hx, t, rfl⟩
        have hx₁ : i t ^ N = 1 := hx
        exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩
    rw [h2, h1, hB, hcard, hg]
    ring
  · have hx' : x ≫ E.q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · rintro ⟨t, rfl⟩
    change (t ≫ E.i) ≫ E.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  · obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := k) E.q.left x.left
    refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp.symm⟩
    rw [← Over.w E.q, ← Category.assoc, ← hp]
    exact Over.w x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.KTrivSpread

theorem exists_smul_eq_zero {R K J : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup J] [Module R J]
    [Module.Finite R J] (h : Subsingleton (K ⊗[R] J)) : ∃ f : R, algebraMap R K f ≠ 0 ∧ ∀ m : J, f • m = 0 := by
  obtain ⟨p, hp₀⟩ : ∃ p : PrimeSpectrum R, ∀ r, r ∈ p.asIdeal ↔ algebraMap R K r = 0 :=
    ⟨⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩, fun _ => Iff.rfl⟩
  let l : p.asIdeal.ResidueField →+* K := Ideal.ResidueField.lift p.asIdeal (algebraMap R K) (fun r hr => (hp₀ r).1 hr)
    (fun r hr => (IsUnit.mk0 _ (fun e => hr ((hp₀ r).2 e))))
  letI : Algebra p.asIdeal.ResidueField K := l.toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm
  have h₁ : Subsingleton (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] J)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField K K J).toEquiv.subsingleton
  have h₂ : Subsingleton (p.asIdeal.ResidueField ⊗[R] J) :=
    Module.FaithfullyFlat.lTensor_reflects_triviality p.asIdeal.ResidueField K _
  have h₃ : p ∉ Module.support R J := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact h₂
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at h₃
  obtain ⟨f, hf, hp⟩ := h₃
  exact ⟨f, fun e => hp ((hp₀ f).2 e), Module.mem_annihilator.1 hf⟩

theorem exists_mul_sub_eq_zero {R B K : Type} [CommRing R] [CommRing B] [Field K] (α : R →+* B) (hα : α.Finite)
    (σ : B →+* R) (hσ : ∀ r, σ (α r) = r) (x : R →+* K)
    (h : ∀ (C : Type) [CommRing C] (ψ : B →+* C) (κ : K →+* C), ψ.comp α = κ.comp x → ∀ b, ψ b = ψ (α (σ b))) :
    ∃ f : R, x f ≠ 0 ∧ ∀ b, α f * (b - α (σ b)) = 0 := by
  letI := α.toAlgebra
  letI := x.toAlgebra
  have : Module.Finite R B := hα
  let s : B →ₐ[R] R := { σ with commutes' := hσ }
  let P : B →ₗ[R] B := LinearMap.id - (Algebra.linearMap R B).comp s.toLinearMap
  have hP : ∀ b, P b = b - α (σ b) := fun b => rfl
  have hPP : ∀ b, P (P b) = P b := fun b => by
    rw [hP (P b), hP, map_sub, hσ, sub_self, map_zero, sub_zero]
  have h₀ : ∀ b, (1 : K) ⊗ₜ[R] P b = 0 := fun b => by
    have := h (K ⊗[R] B) (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom
      Algebra.TensorProduct.includeLeftRingHom (RingHom.ext fun r =>
        ((Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).commutes r).trans rfl) b
    rw [hP, TensorProduct.tmul_sub, sub_eq_zero]
    exact this
  have h₁ : ∀ m : LinearMap.range P, (1 : K) ⊗ₜ[R] m = 0 := by
    rintro ⟨_, b, rfl⟩
    have := congrArg (P.rangeRestrict.lTensor K) (h₀ b)
    rw [map_zero, LinearMap.lTensor_tmul] at this
    rw [← this]
    congr 1
    exact Subtype.ext (hPP b).symm
  have h₂ : Subsingleton (K ⊗[R] LinearMap.range P) := by
    refine subsingleton_of_forall_eq 0 fun z => ?_
    induction z with
    | tmul k m => rw [← _root_.mul_one k, ← smul_eq_mul, ← TensorProduct.smul_tmul', h₁, smul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  obtain ⟨f, hf, H⟩ := exists_smul_eq_zero h₂
  refine ⟨f, hf, fun b => ?_⟩
  have := congrArg Subtype.val (H ⟨P b, b, rfl⟩)
  rw [← hP]
  exact (Algebra.smul_def f (P b)).symm.trans this

theorem memKL_push {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) {Z : Scheme.{0}} (t : Z ⟶ S') (x : Over.mk t ⟶ A')
    (hx : MemKL A' L' x) : MemKL A L (pushPt h.1.w x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (t ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ t)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ t) ≫ f := pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ Over.mk t := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₁ : (lift a b).left ≫ (fst (Over.mk t) A').left = (fst T A).left := congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd (Over.mk t) A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst (Over.mk t) A' ≫ x) * snd (Over.mk t) A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst (Over.mk t) A' ≫ x) * snd (Over.mk t) A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst (Over.mk t) A').left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst (Over.mk t) A').left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L' _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (DVR.pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]

theorem exists_finite_rep (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left)
    (hA : IsAbelianScheme A) (hL : L.IsLB) (ha : Out.RelAmple A L) :
    ∃ (Z : Over (Sp R)) (i : Z ⟶ A), IsClosedImmersion i.left ∧ IsFinite Z.hom ∧
      ∀ (T : Over (Sp R)) (x : T ⟶ A), MemKL A L x ↔ ∃ z : T ⟶ Z, z ≫ i = x := by
  have := hA.comm
  obtain ⟨d, -, n, s, hs⟩ := (Unif.relAmple_iff_veryAmpleBy R A L hL).1 ha
  set_option backward.isDefEq.respectTransparency false in
  have isLB_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) : (AbLaw.pw H t).IsLB := by
    refine { cover := hH.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simpa only [AbLaw.pw, one_zpow, ← map_zpow] using h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simpa only [AbLaw.pw, mul_zpow, ← map_zpow] using h
  have hp : AbLaw.IsProjBy A.hom := ⟨_, isLB_pw hL _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := UU.TrivTwist.inK_iff_trivial_twist _ A L hL
  obtain ⟨Z, i, hi, hZ⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel globalFns_holds R A hA hp L _ hL hO
  exact ⟨Z, i, hi, AmpleStabFinite.isFinite_of_relAmple globalFns_holds R A hA L _ hL hO ha Z i hi hZ,
    fun T x => (hK _ rfl T x).trans (hZ T x)⟩

theorem exists_kTriv_of_isUnit : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] (x : R →+* K) (A₀ : Over (Sp K)) [GrpObj A₀] (φ₀ : A₀.left ⟶ A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsGrpPullback A₀ A (spMap x) φ₀ → Out.KTriv A₀ (L.pull φ₀) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (A' : Over (Sp R')) [GrpObj A'] (π : A'.left ⟶ A.left), IsUnit (φ f) → IsGrpPullback A' A (spMap φ) π → Out.KTriv A' (L.pull π) := by
  intro R _ _ A _ L K _ x A₀ _ φ₀ hA hL ha h₀ hk
  obtain ⟨Z, i, hi, hfin, hZ⟩ := exists_finite_rep R A L hA hL ha
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let ε := Z.left.isoSpec
  obtain ⟨e, he⟩ := (hZ (𝟙_ _) 1).1 (memKL_one hL _)
  obtain ⟨α, hα⟩ := Spec.map_surjective (ε.inv ≫ Z.hom)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (R := Γ(Z.left, ⊤)) (S := CommRingCat.of R) (e.left ≫ ε.hom)
  have hασ : α ≫ σ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hα, hσ, Category.assoc, Iso.hom_inv_id_assoc, Spec.map_id]
    exact Over.w e)
  have hαf : α.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hα]
    infer_instance
  have key : ∀ (C : Type) [CommRing C] (t : Sp C ⟶ Sp R) (z : Over.mk t ⟶ Z) (ψ : Γ(Z.left, ⊤) ⟶ CommRingCat.of C),
      Spec.map ψ = z.left ≫ ε.hom → (z ≫ i = 1 ↔ ψ = σ ≫ α ≫ ψ) := by
    intro C _ t z ψ hψ
    have e₁ : toUnit (Over.mk t) ≫ e ≫ i = 1 := by rw [he, MonObj.comp_one]
    have e₂ : Spec.map (σ ≫ α ≫ ψ) = (toUnit (Over.mk t) ≫ e).left ≫ ε.hom := by
      have e₃ : Spec.map (α ≫ ψ) = t := by
        rw [Spec.map_comp, hψ, hα, Category.assoc, Iso.hom_inv_id_assoc]
        exact Over.w z
      have e₄ : (toUnit (Over.mk t)).left = t := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk t)))
      rw [Spec.map_comp, e₃, hσ, Over.comp_left, e₄]
      exact (Category.assoc _ _ _).symm
    have : Mono i := Over.mono_of_mono_left i
    rw [← e₁, ← Category.assoc, cancel_mono, ← Spec.map_injective.eq_iff, e₂, hψ, cancel_mono]
    exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩
  obtain ⟨f, hf, H⟩ := exists_mul_sub_eq_zero α.hom hαf σ.hom
    (fun r => congrArg (fun q => q.hom r) hασ) x (by
      intro C _ ψ κ hψ b
      let d : Sp C ⟶ Z.left := Spec.map (CommRingCat.ofHom ψ) ≫ ε.inv
      let t : Sp C ⟶ Sp K := spMap κ
      have hd : d ≫ Z.hom = t ≫ spMap x := by
        simp only [d, t, spMap, Category.assoc, ← hα, ← Spec.map_comp]
        congr 1
        exact CommRingCat.hom_ext hψ
      have hdi : (d ≫ i.left) ≫ A.hom = t ≫ spMap x := by
        rw [Category.assoc, Over.w i, hd]
      let y : Over.mk t ⟶ A₀ := Over.homMk (h₀.1.lift _ _ hdi) (h₀.1.lift_snd _ _ _)
      let z : Over.mk (t ≫ spMap x) ⟶ Z := Over.homMk d hd
      have hz : z ≫ i = pushPt h₀.1.w y := Over.OverMorphism.ext (h₀.1.lift_fst _ _ hdi).symm
      have hL₀ : (L.pull φ₀).IsLB := DVR.linComb_isLB _ hL _ _
      have hy : y = 1 := hk _ t y (memKL_of_push h₀ hL hL₀ (lbIso_self hL₀) y ((hZ _ _).2 ⟨z, hz⟩))
      have hy' : pushPt h₀.1.w y = 1 := (congrArg (pushHom h₀ (Over.mk t)) hy).trans (map_one _)
      have := (key C _ z (CommRingCat.ofHom ψ) (by
        show _ = (_ ≫ ε.inv) ≫ ε.hom
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])).1 (hz.trans hy')
      exact congrArg (fun q => q.hom b) this)
  refine ⟨f, hf, fun R' _ φ A' _ π hu h C _ t y hy => ?_⟩
  have hL' : (L.pull π).IsLB := DVR.linComb_isLB _ hL _ _
  obtain ⟨z, hz⟩ := (hZ _ _).1 (memKL_push h hL hL' (lbIso_self hL') t y hy)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := Γ(Z.left, ⊤)) (S := CommRingCat.of C) (z.left ≫ ε.hom)
  obtain ⟨τ, rfl⟩ := Spec.map_surjective t
  have hc : α ≫ ψ = CommRingCat.ofHom φ ≫ τ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hα, hψ, Category.assoc, Iso.hom_inv_id_assoc]
    exact Over.w z)
  have hu' : IsUnit (ψ.hom (α.hom f)) := by
    have : ψ.hom (α.hom f) = τ.hom (φ f) := congrArg (fun q => q.hom f) hc
    rw [this]
    exact hu.map _
  have h₁ : z ≫ i = 1 := (key C _ z ψ hψ).2 (CommRingCat.hom_ext (RingHom.ext fun b => by
    have := congrArg ψ.hom (H b)
    rw [map_mul, map_zero, hu'.mul_right_eq_zero, map_sub, sub_eq_zero] at this
    exact this))
  have inj : ∀ {T : Over (Sp R')} {u v : T ⟶ A'}, pushPt h.1.w u = pushPt h.1.w v → u = v := fun {T u v} e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  exact inj ((hz.symm.trans h₁).trans (map_one (pushHom h (Over.mk (Spec.map τ)))).symm)

end GlobalTheory.KTrivSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_clopen_weilIs_iff : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), 0 < n → IsUnit (n : Γ(T.left, ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 → ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T), Out.WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U :=
  fun hL => PairingLocus.exists_clopen_of_lift hL.globalFns
    (kerPow_of_square (AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.AmpleStabTorsion

theorem finite_sections {k : Type} [Field k] [IsAlgClosed k] (H : Over (Sp k)) [IsFinite H.hom] :
    Finite (Out.baseOver (Sp k) ⟶ H) := by
  have hfin : (Set.univ : Set H.left).Finite :=
    (H.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  have : Finite H.left := Set.finite_univ_iff.1 hfin
  refine Finite.of_injective
    (fun y : Out.baseOver (Sp k) ⟶ H => (y.left : Sp k ⟶ H.left) (IsLocalRing.closedPoint k)) fun y y' h => ?_
  exact Over.OverMorphism.ext (ext_of_apply_closedPoint_eq H.hom (Over.w y) (Over.w y') h)


theorem exists_pow_eq_one : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ x : Out.baseOver (Sp k) ⟶ A, Triv (Out.translDiff A M x) → ∃ m : ℕ, 1 ≤ m ∧ x ^ m = 1 := by
  intro hL k _ _ A _ _ hA M hM hamp x hx
  set_option backward.isDefEq.respectTransparency false in
  have isLB_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) : (AbLaw.pw H t).IsLB := by
    refine { cover := hH.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simpa only [AbLaw.pw, one_zpow, ← map_zpow] using h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simpa only [AbLaw.pw, mul_zpow, ← map_zpow] using h
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy k A M hM).1 hamp
  obtain ⟨h0, -, htw⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns k A hA ⟨_, isLB_pw hM d, n, s, hs⟩ M _ hM h0
  have := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns k A hA M _ hM h0 hamp H j hj hH
  have := finite_sections H
  have hxK : x ∈ GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)) := by
    obtain ⟨c, hc⟩ := hx
    exact fun p => ⟨⊤, trivial, _, LB.isGen_genPull _ c hc _⟩
  have hfin : ((GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)) : Set (Out.baseOver (Sp k) ⟶ A))).Finite :=
    (Set.finite_range fun y : Out.baseOver (Sp k) ⟶ H => y ≫ j).subset fun z hz =>
      (hH _ z).1 ((htw _ rfl _ z).1 hz)
  have : Finite (GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k))) := hfin
  obtain ⟨m, hm, e⟩ := (isOfFinOrder_of_finite (⟨x, hxK⟩ : GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)))).exists_pow_eq_one
  exact ⟨m, hm, congrArg Subtype.val e⟩

end GlobalTheory.AmpleStabTorsion
end
end

