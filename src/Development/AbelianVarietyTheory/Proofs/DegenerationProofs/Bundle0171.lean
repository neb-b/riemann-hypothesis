module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsomorphismValuesCocycleEqBundleIsoValue
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.IsoValCocycle
open GlobalTheory.TorusExt GlobalTheory.IsoValConst

theorem exists_th_ne_zero (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type}
    [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) {n : ℕ} (hn : 2 ≤ n)
    (hF : (n : F) ≠ 0) (a : N.A) : ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0 := by
  let y : (TF (R := R) F).left := IsLocalRing.closedPoint F
  obtain ⟨th, ρ, hth, hv⟩ := ThetaInValues.exists_th ν y
  obtain ⟨x, hx, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P (jFK (R := R) F ≫ jK R) hn hF th
    (ThetaCoset.ne_zero_of_isGenSec hL₂.secBaseChangeAny D.P _ hth) (ν.eA a)
  obtain ⟨t, rfl⟩ := ν.eA.surjective x
  refine ⟨t, ν.eA.injective (by rw [map_pow, map_one]; exact hx), fun h => ?_⟩
  have q := hu y ν.J (ThetaInValues.good ν y)
  have e := hv (a * t)
  rw [h, MulZeroClass.zero_mul, map_zero, map_mul] at e
  exact not_isUnit_zero ((congrArg IsUnit e).mp q)

theorem cocycle_eq_val : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  intro hL hL₂ R O' _ _ _ _ _ _ f P D₀ C _ _ _ _ _ hf N' N ν' ν ψ w I gp hw he
  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) C).hom ≫ spMap f = (TF (R := O') C).hom := ArcTransport.base_comm fun r => (hf r).symm
  have hp : ∀ x : N.A, ArcTransport.pushF gp hT (ν'.eA (I.φ x)) = ν.eA x := fun x => Over.OverMorphism.ext (he x)
  have hW : ∀ x : N'.A, stalkConst z (wVal ν' ν w x) = (ArcTransport.wVal w z ν.J ν'.J (ν'.eA x)).val := fun x =>
    toStk_valF (ν'.eA x).left ((D₀.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA x).left ≫ ψ)) ⊓ P.P.L.U (ν'.J (ν'.eA x).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA x).left ≫ ψ)), hJ' _⟩ _
  refine ⟨fun x h => ?_, ?_⟩
  · have := hW x
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  let Ω : N.A → ((Sp C).presheaf.stalk z)ˣ := fun x => ArcTransport.wVal w z ν.J ν'.J (ν'.eA (I.φ x))
  have hΩ : ∀ x, stalkUnits z (I.h x) * Ω x = stalkUnits z (I.h 1) * Ω 1 := by
    refine const_of_cube (fun x => stalkUnits z (I.h x) * Ω x) (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ 2
      (fun x => ?_) (exists_th_ne_zero hL hL₂ ν le_rfl (Nat.cast_ne_zero.2 two_ne_zero))
    · have e := ArcTransport.thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ hJ' (ν'.eA (I.φ a)) (ν'.eA (I.φ b))
        (ν'.eA (I.φ c))
      rw [hp, hp, hp, ← map_one ν'.eA, ← map_one I.φ, ← stalk_θ, ← stalk_θ] at e
      simp only [← map_mul ν'.eA, ← map_mul I.φ] at e
      have e₁ : stalkUnits z (N.θ a b c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
        Ω c * (Ω 1)⁻¹ * stalkUnits z (N'.θ (I.φ a) (I.φ b) (I.φ c)) := e
      have e₂ := congrArg (stalkUnits z) (I.θ_eq a b c)
      rw [I.h_one, map_one]
      clear_value Ω
      apply Additive.ofMul.injective
      replace e₁ := congrArg Additive.ofMul e₁
      replace e₂ := congrArg Additive.ofMul e₂
      simp only [map_mul, ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ ⊢
      linear_combination (norm := abel) -e₁ - e₂
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 P.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D₀.P.A.left) (h := ψ) hw D₀.P.isLB P.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν.th
      obtain ⟨κ, hκ⟩ := sval_eq ν' z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 →
          ρ.val = (stalkUnits z (I.h a) * Ω a).val * (κ * stalkConst z I.lam * ρ'.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp C ⟶ _ from (ν'.eA (I.φ a)).left) hJ hJ'
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp C).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ.val = (Ω a).val * (κ * (stalkConst z (N'.th (I.φ a)) * ρ'.val)) :=
          (hρ a).trans ((congrArg (fun q => sval (Z := Sp C) ν.th q z ν.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ' _).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        rw [I.th_eq, Units.val_mul, Units.val_mul, stalkUnits_val, map_mul, map_mul]
        ring
      intro a b ha hb
      have hu : IsUnit (κ * stalkConst z I.lam * ρ'.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
    · obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D₀.P (jFK (R := O') C ≫ jK O') (ν.eA x) one_le_two
      exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  intro x
  apply (stalkConst z).injective
  have e := congrArg Units.val (hΩ x)
  rw [I.h_one, map_one, _root_.one_mul, Units.val_mul, stalkUnits_val] at e
  rw [map_mul, hW, hW, ← map_one I.φ]
  exact e

end GlobalTheory.IsoValCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionOfSurjectiveOfDimEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

namespace IsogenyOntoExtension

theorem exists_pow_eq_one_of_finite_kernel {k : Type} [Field k] {G B : Over (Sp k)} [GrpObj G]
    [GrpObj B] [IsCommMonObj G] (f : G ⟶ B) [IsMonHom f]
    (hf : IsFinite (pullback.snd f (η[B] : 𝟙_ _ ⟶ B)).left) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp k)) (x : T ⟶ G), x ≫ f = 1 → x ^ n = 1 := by
  have hp : IsPullback (pullback.fst f η[B]) (toUnit _) f η[B] := by
    have := IsPullback.of_hasPullback f η[B]
    rwa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at this
  rw [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at hf
  generalize pullback.fst f η[B] = i at hp
  generalize pullback f η[B] = Z at i hp hf
  have hm : Mono i := ⟨fun a b h => hp.hom_ext h (toUnit_unique _ _)⟩
  have hi : i ≫ f = 1 := hp.w
  obtain ⟨gZ, hZ⟩ := exists_grpObj_of_mono i (hp.lift η[G] (toUnit _) (by simp))
    (hp.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one,
        _root_.mul_one, Hom.one_def]))
    (hp.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))
    (hp.lift_fst _ _ _) (by rw [hp.lift_fst, Hom.mul_def]; congr 1)
    (by rw [hp.lift_fst, Hom.inv_def])
  have hZf : IsFinite Z.hom := by simpa using hf
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main k Z hZf inferInstance
  refine ⟨N, hN, fun T x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hp.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]


open RationalPoint in
theorem finite_kernel_points {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)}
    [GrpObj B] (f : G ⟶ B) (hf : IsFinite (pullback.snd f (η[B] : 𝟙_ _ ⟶ B)).left) :
    {x : 𝟙_ (Over (Sp k)) ⟶ G | x ≫ f = 1}.Finite := by
  have hp : IsPullback (pullback.fst f η[B]) (toUnit _) f η[B] := by
    have := IsPullback.of_hasPullback f η[B]
    rwa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at this
  rw [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at hf
  generalize pullback.fst f η[B] = i at hp
  generalize pullback f η[B] = Z at i hp hf
  have hZf : IsFinite Z.hom := by simpa using hf
  have h1 : Finite Z.left := by
    have := Z.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)
    rw [← Set.finite_univ_iff]
    exact this.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum k) _ _
  have h2 : Finite (𝟙_ (Over (Sp k)) ⟶ Z) := Finite.of_injective _ pt_injective
  refine (Set.finite_range fun z : 𝟙_ (Over (Sp k)) ⟶ Z => z ≫ i).subset fun x hx => ?_
  exact ⟨hp.lift x (toUnit _) hx, hp.lift_fst _ _ _⟩


open RationalPoint in
theorem eq_top_of_finite_cover {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G]
    [LocallyOfFiniteType G.hom] [IrreducibleSpace G.left]
    (H : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) {Z : Set G.left} (hZ : IsClosed Z)
    (hH : ∀ x, x ∈ H ↔ pt x ∈ Z) {F : Set (𝟙_ (Over (Sp k)) ⟶ G)} (hF : F.Finite)
    (hc : ∀ y, ∃ a ∈ F, a * y ∈ H) : H = ⊤ := by
  classical
  let t : (𝟙_ (Over (Sp k)) ⟶ G) → (G ⟶ G) := fun a => (toUnit G ≫ a) * 𝟙 G
  have ht : ∀ a y : 𝟙_ (Over (Sp k)) ⟶ G, y ≫ t a = a * y := fun a y => by
    simp only [t]
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (y ≫ toUnit G) (𝟙 _), Category.id_comp,
      Category.comp_id]
  let C : (𝟙_ (Over (Sp k)) ⟶ G) → Set G.left := fun a => (t a).left ⁻¹' Z
  have hC : ∀ a, IsClosed (C a) := fun a => hZ.preimage (t a).left.continuous
  have hCm : ∀ a y, pt y ∈ C a ↔ a * y ∈ H := fun a y => by
    rw [hH, ← ht, pt_comp]; rfl
  have hU : IsClosed (⋃ a ∈ F, C a) := hF.isClosed_biUnion fun a _ => hC a
  have hcov : (Set.univ : Set G.left) ⊆ ⋃ a ∈ F, C a := by
    by_contra hne
    have hne' : (⋃ a ∈ F, C a)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h => hne (h ▸ subset_rfl)
    have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
    obtain ⟨c, hcZ, hc'⟩ := nonempty_inter_closedPoints hne' hU.isOpen_compl.isLocallyClosed
    obtain ⟨x, hx⟩ := exists_pt_mem (X := G) (Z := {c}) hc' ⟨c, rfl⟩
    obtain ⟨a, ha, hax⟩ := hc x
    refine hcZ ?_
    rw [← show pt x = c from hx]
    exact Set.mem_biUnion ha ((hCm a x).2 hax)
  obtain ⟨D, hD, hDu⟩ := (isIrreducible_iff_sUnion_isClosed.1
    (IrreducibleSpace.isIrreducible_univ G.left)) (hF.image C).toFinset (by
      intro z hz
      obtain ⟨a, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hz
      exact hC a) (by rwa [Set.Finite.coe_toFinset, Set.sUnion_image])
  obtain ⟨a, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hD
  rw [eq_top_iff]
  intro y _
  have := (hCm a (a⁻¹ * y)).1 (hDu trivial)
  rwa [mul_inv_cancel_left] at this

end IsogenyOntoExtension


open IsogenyOntoExtension RationalPoint in
theorem torusExtension_of_surjective_of_dim_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), SmConn G → SmConn G' → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g G'.hom → Nonempty (TorusExtension G') → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → Nonempty (TorusExtension G) := by
  intro k _ _ G G' _ _ g hG hG' hg hg' hT i hi hs
  have hker := _root_.GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq k G G' g hG hG' hg hg' i hi hs
  obtain ⟨hfl, hsu⟩ := _root_.GlobalTheory.SS.flat_and_surjective_of_surjective_points k G G' hG hG' i hi hs
  obtain ⟨c, s, p, q, n⟩ := id hG
  obtain ⟨c', s', p', q', n'⟩ := id hG'
  obtain ⟨N, hN, hkill⟩ := exists_pow_eq_one_of_finite_kernel i hker
  have hqc : QuasiCompact i.left := by
    have : QuasiCompact (i.left ≫ G'.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp i.left G'.hom
  have hmul : IsMonHom (𝟙 G ^ N) := by
    clear hkill hN
    induction N with
    | zero => rw [pow_zero]; exact Serre.isMonHom_one
    | succ m ih => rw [pow_succ]; exact Serre.isMonHom_mul _ _
  obtain ⟨⟨r, hr, hir⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ G G' G i (𝟙 G ^ N) hi hmul
    hfl hsu hqc fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hkill T x hx]
  refine _root_.GlobalTheory.SS.nonempty_torusExtension_of_surjective_points k G' G hG hT r hr ?_
  obtain ⟨Z, hZ, hZm⟩ := exists_isClosed_image_of_isClosed_subgroup k G' G r hr inferInstance q'
    inferInstance q ⊤ Set.univ isClosed_univ (by simp)
  let φ : (𝟙_ (Over (Sp k)) ⟶ G') →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ r) fun x y => MonObj.mul_comp x y r
  have := grpObj_geometricallyIntegral_of_smooth _ G
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have htop : φ.range = ⊤ := by
    refine eq_top_of_finite_cover φ.range hZ (fun x => ?_) (finite_kernel_points i hker) fun y => ?_
    · rw [← range_left_subset_iff, ← hZm]
      exact ⟨fun ⟨a, ha⟩ => ⟨a, trivial, ha⟩, fun ⟨a, _, ha⟩ => ⟨a, ha⟩⟩
    · obtain ⟨z, hz⟩ := _root_.GlobalTheory.SS.torusExtension_points_divisible k G' hT N hN (y ≫ i)
      obtain ⟨x, rfl⟩ := hs z
      refine ⟨x ^ N * y⁻¹, ?_, x ≫ i, ?_⟩
      · show _ ≫ i = 1
        rw [MonObj.mul_comp, GrpObj.inv_comp, MonObj.pow_comp, hz, mul_inv_cancel]
      · show (x ≫ i) ≫ r = _
        rw [Category.assoc, hir, MonObj.comp_pow, Category.comp_id, inv_mul_cancel_right]
  intro y
  exact (htop ▸ Subgroup.mem_top y : y ∈ φ.range)

end GlobalTheory
end

