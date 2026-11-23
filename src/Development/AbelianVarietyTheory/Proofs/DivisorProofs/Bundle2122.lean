module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopIsoInvRestrictAppTop
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.EigenDescent
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EigenDescent

theorem topIso_inv_eq_appLE {X : Scheme.{0}} (W : X.Opens) (h : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W) :
    W.topIso.inv = W.ι.appLE W ⊤ h :=
  (Scheme.Opens.topIso_inv W).trans (Eq.trans rfl (Scheme.Opens.ι_appLE W W ⊤ h).symm)

theorem topIso_inv_appTop {X Z : Scheme.{0}} (W : X.Opens) (y : Z ⟶ W.toScheme)
    (h : (⊤ : Z.Opens) ≤ (y ≫ W.ι) ⁻¹ᵁ W) :
    W.topIso.inv ≫ y.appTop = (y ≫ W.ι).appLE W ⊤ h := by
  have h0 : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  rw [topIso_inv_eq_appLE W h0]
  refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE y W.ι W ⊤ ⊤ h0 le_rfl)
  congr 1
  exact (Scheme.Hom.appLE_eq_app _).symm

theorem topIso_inv_restrict_appTop {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) :
    U.topIso.inv ≫ (π ∣_ U).appTop = π.app U ≫ (π ⁻¹ᵁ U).topIso.inv := by
  have h0 : (⊤ : (π ⁻¹ᵁ U).toScheme.Opens) ≤ (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ U) := fun x _ => x.2
  have h1 : ∀ g : (π ⁻¹ᵁ U).toScheme ⟶ Y, g = (π ⁻¹ᵁ U).ι ≫ π → ∀ h : ⊤ ≤ g ⁻¹ᵁ U,
      g.appLE U ⊤ h = π.app U ≫ (π ⁻¹ᵁ U).topIso.inv := by
    rintro _ rfl h
    rw [topIso_inv_eq_appLE _ h0, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [topIso_inv_appTop U (π ∣_ U) (fun x _ => ((π ∣_ U) x).2)]
  exact h1 _ (morphismRestrict_ι π U) _

theorem evU_val_restrict {X Z : Scheme.{0}} (W : X.Opens) (y : Z ⟶ W.toScheme)
    (h : ∀ z, (y ≫ W.ι) z ∈ W) (r : Γ(X, W)ˣ) :
    (evU (y ≫ W.ι) h r).val = y.appTop.hom (W.topIso.inv.hom r.val) := by
  have e := congrArg (fun φ => φ.hom r.val) (topIso_inv_appTop W y (fun z _ => h z))
  exact e.symm

theorem appTop_injective_of_epi {X Y : Scheme.{0}} (Q : X ⟶ Y) [Epi Q] :
    Function.Injective Q.appTop.hom := by
  intro a b hab
  have e : Q ≫ Out.TLinPf.mOf a = Q ≫ Out.TLinPf.mOf b := by
    rw [Out.TLinPf.comp_mOf, Out.TLinPf.comp_mOf, hab]
  rw [cancel_epi] at e
  rw [← Out.TLinPf.fnOf_mOf a, e, Out.TLinPf.fnOf_mOf]

theorem unit_descends : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] [IsAffineHom π] (U : Y.Opens) (r : Γ(X, π ⁻¹ᵁ U)ˣ),
    (∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ∀ z, g₁ z ∈ π ⁻¹ᵁ U) (h₂ : ∀ z, g₂ z ∈ π ⁻¹ᵁ U),
      g₁ ≫ π = g₂ ≫ π → evU g₁ h₁ r = evU g₂ h₂ r) →
    ∃ u : Γ(Y, U)ˣ, pullU π U u = r := by
  intro X Y π _ _ _ U r hr
  have hS : Surjective (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict π U).flip inferInstance
  have hA : IsAffineHom (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict π U).flip inferInstance
  have hE : Epi (π ∣_ U) := Flat.epi_of_flat_of_surjective _
  have key : ∀ {Z : Scheme.{0}} (y₁ y₂ : Z ⟶ (π ⁻¹ᵁ U).toScheme), y₁ ≫ π ∣_ U = y₂ ≫ π ∣_ U →
      evU (y₁ ≫ (π ⁻¹ᵁ U).ι) (fun z => (y₁ z).2) r = evU (y₂ ≫ (π ⁻¹ᵁ U).ι) (fun z => (y₂ z).2) r := by
    intro Z y₁ y₂ e
    refine hr Z _ _ _ _ ?_
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]
  obtain ⟨v, hv⟩ := Out.TLinPf.descend_gen (π ∣_ U) ((π ⁻¹ᵁ U).topIso.inv.hom r.val) (by
    intro Z y₁ y₂ e
    rw [← evU_val_restrict _ y₁ (fun z => (y₁ z).2), ← evU_val_restrict _ y₂ (fun z => (y₂ z).2),
      key y₁ y₂ e])
  obtain ⟨v', hv'⟩ := Out.TLinPf.descend_gen (π ∣_ U) ((π ⁻¹ᵁ U).topIso.inv.hom (r⁻¹).val) (by
    intro Z y₁ y₂ e
    rw [← evU_val_restrict _ y₁ (fun z => (y₁ z).2), ← evU_val_restrict _ y₂ (fun z => (y₂ z).2)]
    have k := key y₁ y₂ e
    simp only [evU, map_inv] at k ⊢
    rw [k])
  have hvv : v * v' = 1 := by
    apply appTop_injective_of_epi (π ∣_ U)
    rw [map_mul, hv, hv', ← map_mul, Units.mul_inv, map_one, map_one]
  have h1 : U.topIso.hom.hom v * U.topIso.hom.hom v' = 1 := by
    rw [← map_mul, hvv, map_one]
  refine ⟨⟨U.topIso.hom.hom v, U.topIso.hom.hom v', h1, by rw [mul_comm, h1]⟩, Units.ext ?_⟩
  change (π.app U).hom (U.topIso.hom.hom v) = r.val
  have e := congrArg (fun φ => φ.hom (U.topIso.hom.hom v)) (topIso_inv_restrict_appTop π U)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [Iso.hom_inv_id_apply, hv] at e
  exact ((π ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv.injective e).symm

end GlobalTheory.EigenDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentGeneratorsHolomorphicFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetGen

theorem mul_dot_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f : X →+ ℂ) {c : ℂ}
    (hc : c ≠ 0) (χ : X) : c * (co bX χ ⬝ᵥ fun l => f (bX l) / c) = f χ := by
  conv_rhs => rw [← bX.sum_repr χ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  simp only [co]
  field_simp

theorem dual_alg (A : DualNumber ℂ) {c d c0 d0 l : ℂ} (hc : c ≠ 0) (hc0 : c0 ≠ 0) (hA : A.fst = 1)
    (hl : l = A.snd + d / c - d0 / c0) :
    A * (TrivSqZeroExt.inl c + TrivSqZeroExt.inr d) * TrivSqZeroExt.inl c0 =
      (1 + TrivSqZeroExt.inr l) * TrivSqZeroExt.inl c * (TrivSqZeroExt.inl c0 + TrivSqZeroExt.inr d0) := by
  ext
  · simp [hA]
  · simp [hA, hl]
    field_simp
    ring

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (χ χ' : X) :
    co bX (χ + χ') = co bX χ + co bX χ' := by
  ext l; simp [co]

theorem tangent_generators : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X)
    (d : CD N g r bX) (G : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g → ℂ),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b →
    ∃ T : Fin r → ℂ, ∀ (χ : N.X) (ct : Fin g → ℂ), ct = d.t12 *ᵥ co bX χ →
      vE (gm.s (ν.eX χ)) (𝟙 _) ν.J * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) +
        TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) =
      (1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ T))) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) *
        (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) +
          TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) := by
  intro R _ _ _ _ D _ _ _ N ν g r bX d G gm W h0 hD

  set cf : (Fin g → ℂ) → ℂ := fun w => G.frG (ν.J (ν.eA (d.ex w)).left) w with hcf
  set df : (Fin g → ℂ) → ℂ := fun w => fderiv ℂ (G.frG (ν.J (ν.eA (d.ex w)).left)) w W with hdf
  have hc : ∀ w, cf w ≠ 0 := fun w => by
    simp only [hcf, ← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  set Dl : (Fin g → ℂ) → ℂ := fun w => df w / cf w with hDl
  set A : N.X → DualNumber ℂ := fun χ => vE (gm.s (ν.eX χ)) (𝟙 _) ν.J with hA
  have hA1 : ∀ χ, (A χ).fst = 1 := fun χ => _root_.GlobalTheory.MBLow.Cl.fst_vE_eq_one ν gm h0 (ν.eX χ)
  set ct : N.X → (Fin g → ℂ) := fun χ => d.t12 *ᵥ co bX χ with hct
  have hct_add : ∀ χ χ', ct (χ + χ') = ct χ + ct χ' := fun χ χ' => by
    simp only [hct, co_add, Matrix.mulVec_add]
  have hx : ∀ χ, ν.eA (d.ex (ct χ)) = DegPre.cF D ℂ (ν.eX χ) := fun χ => by
    rw [← d.c_eq]; exact ν.c_eq χ
  have hprod := fun x y z j hj => _root_.GlobalTheory.MBLow.Cl.cube_val_frame ν d.toAB d.cub G x y z j hj

  have hsnd : ∀ χ χ', (A (χ + χ')).snd + (Dl (ct χ + ct χ') + Dl 0 - Dl (ct χ) - Dl (ct χ')) =
      (A χ).snd + (A χ').snd := fun χ χ' => by
    have hm := GlobalTheory.T.torusExtension_dualCharValues_mul_cube ν gm (ν.eX χ) (ν.eX χ')
    rw [_root_.GlobalTheory.MBLow.Cl.CubeJet.cube_jet ν d.toAB G hprod W gm h0 hD _ _ (ct χ) (ct χ') (hx χ) (hx χ'), ← map_add (f := _)] at hm
    have e := congrArg TrivSqZeroExt.snd hm
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at e
    have e1 := hA1 (χ + χ'); have e2 := hA1 χ; have e3 := hA1 χ'
    simp only [hA] at e1 e2 e3 ⊢
    rw [e1, e2, e3] at e
    linear_combination e
  clear hprod
  set ℓ : N.X → ℂ := fun χ => (A χ).snd + Dl (ct χ) - Dl 0 with hℓ
  have hℓ_add : ∀ χ χ', ℓ (χ + χ') = ℓ χ + ℓ χ' := fun χ χ' => by
    have := hsnd χ χ'
    simp only [hℓ, hct_add]
    linear_combination this
  let ℓh : N.X →+ ℂ := AddMonoidHom.mk' ℓ hℓ_add
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨fun l => ℓ (bX l) / (2 * Real.pi * Complex.I), fun χ ct' hct' => ?_⟩
  have hT : (2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ fun l => ℓ (bX l) / (2 * Real.pi * Complex.I)) = ℓ χ :=
    mul_dot_basis bX ℓh h2pi χ
  rw [hT, hct']
  exact dual_alg (A χ) (hc _) (hc 0) (hA1 χ) rfl

end GlobalTheory.MBLow.Cl.JetGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
namespace GlobalTheory.SqDecTransport

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem transport : ∀ (k K k₁ K' : Type) [Field k] [Field K] [Field k₁] [Field K'] (a : k →+* K) (b : k →+* k₁) (c : K →+* K') (d : k₁ →+* K'), c.comp a = d.comp b → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp K)) [GrpObj A] (π : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap a) π → ∀ (L₀ M₀ : LB A₀.left) (L M : LB A.left), L₀.IsLB → M₀.IsLB → L.IsLB → M.IsLB → LBIso L (L₀.pull π) → LBIso M (M₀.pull π) → SqDec ((Over.pullback (spMap b)).obj A₀) (L₀.pull (pullback.fst A₀.hom (spMap b))) (M₀.pull (pullback.fst A₀.hom (spMap b))) → SqDec ((Over.pullback (spMap c)).obj A) (L.pull (pullback.fst A.hom (spMap c))) (M.pull (pullback.fst A.hom (spMap c))) := by
  intro k K k₁ K' _ _ _ _ a b c d hcd A₀ _ A _ π hA L₀ M₀ L M hL₀ hM₀ hLL hML hL hM hD
  have hw : (pullback.fst A.hom (spMap c) ≫ π) ≫ A₀.hom = (pullback.snd A.hom (spMap c) ≫ spMap d) ≫ spMap b := by
    rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      spMap_comp_spMap, spMap_comp_spMap, hcd]
  let π' : pullback A.hom (spMap c) ⟶ pullback A₀.hom (spMap b) := pullback.lift _ _ hw
  have e₁ : π' ≫ pullback.fst A₀.hom (spMap b) = pullback.fst A.hom (spMap c) ≫ π := pullback.lift_fst _ _ _
  have e₂ : π' ≫ pullback.snd A₀.hom (spMap b) = pullback.snd A.hom (spMap c) ≫ spMap d := pullback.lift_snd _ _ _
  have hP : IsGrpPullback ((Over.pullback (spMap c)).obj A) ((Over.pullback (spMap b)).obj A₀) (spMap d) π' := by
    have n := (isGrpPullback_pullback A (spMap c)).comp hA
    rw [spMap_comp_spMap, hcd, ← spMap_comp_spMap, ← e₁] at n
    exact IsGrpPullback.cancel (isGrpPullback_pullback A₀ (spMap b)) n e₂
  obtain ⟨N, a₀, r, e, β, hN, ha₀, hβ, hI⟩ := hD
  have hβ' : ∀ i, ∃ f : (Over.pullback (spMap c)).obj A ⟶ (Over.pullback (spMap c)).obj A,
      IsMonHom f ∧ f.left ≫ π' = π' ≫ (β i).left := fun i => by
    haveI := hβ i
    exact GlobalTheory.HomDescent.exists_isMonHom_pull hP hP (β i)
  choose β' hβ'm hβ'c using hβ'
  have iL : LBIso (L.pull (pullback.fst A.hom (spMap c))) ((L₀.pull (pullback.fst A₀.hom (spMap b))).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull hL _ _ _ π' (fun _ => e₁.symm)
  have iM : LBIso (M.pull (pullback.fst A.hom (spMap c))) ((M₀.pull (pullback.fst A₀.hom (spMap b))).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull hM _ _ _ π' (fun _ => e₁.symm)
  refine ⟨N, a₀, r, e, β', hN, ha₀, hβ'm, ?_⟩
  have j₁ : LBIso (lbPow (L.pull (pullback.fst A.hom (spMap c))) N)
      ((lbPow (L₀.pull (pullback.fst A₀.hom (spMap b))) N).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iL _ _ _ π' (fun _ => by simp)
  have j₂ := GlobalTheory.RigidBundleGlue.LBIso.pull hI π'
  have j₃ : LBIso (LB.LinComb (M.pull (pullback.fst A.hom (spMap c))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β' i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ))
      ((LB.LinComb (M₀.pull (pullback.fst A₀.hom (spMap b))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ)).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iM _ _ _ π' (fun o => by
      cases o with
      | none => simp
      | some i => exact hβ'c i)
  exact LBIso.trans (isLB_lbPow (pull_isLB hLL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL₀ _) N) _)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hML _) _ _) j₁
    (LBIso.trans (pull_isLB (isLB_lbPow (pull_isLB hL₀ _) N) _)
      (pull_isLB (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hM₀ _) _ _) _)
      (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hML _) _ _) j₂ (LBIso.symm j₃))

end GlobalTheory.SqDecTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialEvaluationsOfMemKernelSymmetricPair
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KerAxes

theorem triv_of_local_evc {S : Scheme.{0}} {G T : Over S} [GrpObj G] (hG : IsAbelianScheme G)
    {P : LB (G ⊗ G).left} (hP : P.IsLB) (h2 : Triv (ev P (𝟙 G) (1 : G ⟶ G))) (x : T ⟶ G)
    (hloc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over S) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ x) g = 0) :
    Triv (ev P (snd G T ≫ x) (fst G T)) := by
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (snd G T ≫ x) (fst G T))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (G ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (snd G T ≫ x) (fst G T)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd G T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hG T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, lift_snd_assoc, Category.id_comp, lift_fst]
    exact evc_one_right hP h2 x
  · intro p
    obtain ⟨V, hV, hz⟩ := hloc p
    refine ⟨V, hV, ?_⟩
    let U := (snd G T).left ⁻¹ᵁ V
    let Y : Over S := Over.mk (U.ι ≫ (G ⊗ T).hom)
    let i : Y ⟶ G ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, ← Category.assoc]
    exact hz Y _ _ (fun z ↦ z.2)

theorem triv_of_memKL_pair : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a b : T ⟶ G), GlobalTheory.MemKL (G ⊗ G) P (lift a b) → (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (snd G T ≫ b) (fst G T)).left).Gen, t.IsGen) := by
  intro R _ _ G _ hG P hP h1 h2 hs T a b hx
  have hs' : (swap P).IsLB := pull_isLB hP _
  have h1' : Triv (ev P (1 : G ⟶ G) (𝟙 G)) := h1
  have h2' : Triv (ev P (𝟙 G) (1 : G ⟶ G)) := h2
  have add1 := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hG hG hP h1' h2')
  have add2 := (isAdditive_iff hs').1 (CubeNoeth.isAdditive_swap_of_triv_axes hG hG hP h1' h2')
  have symm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP v u = evc hP u v := by
    intro Y u v
    have e := congrArg (CechPic.pull (lift v u).left) ((cls_eq_iff hP hs').2 hs)
    exact e.trans (evc_swap hP hs' v u)
  have loc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over (Sp R)) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ a) g = 0 ∧ evc hP (t ≫ b) g = 0 := by
    intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    refine ⟨V, hV, fun Y t g ht ↦ ?_⟩
    have mk : ∀ u v : Y ⟶ G, evc hP ((t ≫ a) * u) ((t ≫ b) * v) = evc hP u v := by
      intro u v
      have e := pull_mul_eq hP hTV t ht (lift u v)
      have q : (t ≫ lift a b) * lift u v = lift ((t ≫ a) * u) ((t ≫ b) * v) := by
        ext <;> simp [MonObj.mul_comp]
      rw [q] at e
      exact e
    have e0 := mk 1 1
    rw [_root_.mul_one, _root_.mul_one, evc_one_left hP h1'] at e0
    constructor
    · have e1 := mk 1 g
      rw [_root_.mul_one, evc_one_left hP h1'] at e1
      have s := add2 Y (t ≫ b) g (t ≫ a)
      rw [evc_swap hP hs', evc_swap hP hs', evc_swap hP hs'] at s
      rw [s, e0, zero_add] at e1
      exact e1
    · have e3 := mk g 1
      rw [_root_.mul_one, evc_one_right hP h2'] at e3
      have s := add1 Y (t ≫ a) g (t ≫ b)
      rw [s, e0, zero_add] at e3
      rw [symm]
      exact e3
  refine ⟨triv_of_local_evc hG hP h2' a fun p ↦ ?_, triv_of_local_evc hG hP h2' b fun p ↦ ?_⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).1⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).2⟩

end GlobalTheory.KerAxes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqOfGermsPinchingSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem unit_eq_of_germs_glues : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (u v : Γ(X, V)ˣ), (∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) → (∀ z : Z, i z ∈ V → gm i z V u = gm i z V v) → u = v := by
  intro X X' Z Z' p i i' p' hc hG V u v hp hi
  have ep : (p.app V).hom u.val = (p.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext X'.sheaf (p ⁻¹ᵁ V)
    intro x hx
    have h := congrArg Units.val (hp x hx)
    rwa [gm_val _ x V hx, gm_val _ x V hx] at h
  have ei : (i.app V).hom u.val = (i.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext Z.sheaf (i ⁻¹ᵁ V)
    intro z hz
    have h := congrArg Units.val (hi z hz)
    rwa [gm_val _ z V hz, gm_val _ z V hz] at h
  have key : ∀ (f g : Z' ⟶ X) (_ : f = g) (O : Z'.Opens) (e : O ≤ f ⁻¹ᵁ V) (e' : O ≤ g ⁻¹ᵁ V),
      f.appLE V O e = g.appLE V O e' := by
    intro f g hfg O e e'; subst hfg; rfl
  have hag : (i'.appLE (p ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left).hom ((p.app V).hom u.val) =
      (p'.appLE (i ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right).hom ((i.app V).hom u.val) := by
    have e1 := Scheme.Hom.comp_appLE i' p V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left
    have e2 := Scheme.Hom.comp_appLE p' i V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right
    have e3 := key _ _ hc (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left inf_le_right
    rw [e1, e2] at e3
    have := congrArg (fun f => f.hom u.val) e3
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  exact Units.ext ((hG V _ _ hag).unique ⟨rfl, rfl⟩ ⟨ep.symm, ei.symm⟩)

end GlobalTheory.PinchLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroups
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_identity_unconditional :
    ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
      (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ :=
  _root_.GlobalTheory.UnitLemma.OrbitAll.identity_of_lie (GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis _root_.GlobalTheory.JR.unitMatch_all).1

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeImageComplPtsIn
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue

namespace GlobalTheory.Mean4O.CoverInt

theorem volume_image_compl_ptsIn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → (∀ W : X.Opens, Nonempty W → Function.Injective (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W)) → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (D : ℕ) (c : AlgChart p σ D), MeasureTheory.volume (c.e '' (c.e.source ∩ (ptsIn p σ U)ᶜ)) = 0 := by
  intro k _ X _ p σ hσ _ U hU D c
  have : IsDomain k := hσ.isDomain σ
  refine measure_mono_null ?_ (ae_iff.1 (SemiPosBir.ae_mem hσ c (U := U) ⟨_, hU⟩))
  rintro _ ⟨z, hz, rfl⟩ h
  have h₁ := h (c.e.map_source hz.1)
  rw [c.e.left_inv hz.1] at h₁
  exact hz.2 h₁

end GlobalTheory.Mean4O.CoverInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zariski_descent_dvr_trace_localisation : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  first | exact @GlobalTheory.zariski_descent_heart | exact GlobalTheory.zariski_descent_heart | (intros; apply GlobalTheory.zariski_descent_heart <;> assumption)
end

