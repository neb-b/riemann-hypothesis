module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.GlobalFields.WeilGroups.QuasiCharacterDecomposition
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValLogOfMulSelfEqZero
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.SqZero

theorem mvPolynomialEval_truncFinsupp_eq_sum_coeff_mul_prod {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] (w : σ → R)
    (n : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial.eval w (trunc' R n f) = ∑ β ∈ Finset.Iic n, coeff β f * ∏ i ∈ β.support, w i ^ β i := by
  have hsub : (trunc' R n f).support ⊆ Finset.Iic n := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, coeff_trunc'] at hm
    split_ifs at hm with h
    · exact Finset.mem_Iic.mpr h
    · exact absurd rfl hm
  rw [MvPolynomial.eval_eq, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [coeff_trunc', if_pos (Finset.mem_Iic.mp hm)]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

theorem hasVal_log_of_mul_self_eq_zero :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (p : ℕ) (x : B), x * x = 0 → HasVal p (fun _ : Unit => x) (PowerSeries.log Q : MvPowerSeries Unit Q) (algebraMap B Q x) := by
  intro B Q _ _ _ _ p x hx
  set y : Q := algebraMap B Q x with hy
  have hyy : y * y = 0 := by rw [hy, ← map_mul, hx, map_zero]
  have hcoeff : ∀ β : Unit →₀ ℕ, coeff β (PowerSeries.log Q : MvPowerSeries Unit Q) =
      PowerSeries.coeff (β ()) (PowerSeries.log Q) := by
    intro β
    rw [PowerSeries.coeff_def (by rfl)]
  intro m
  refine ⟨1, fun N' hN' => ⟨0, ?_⟩⟩
  rw [mul_zero, map_zero, sub_eq_zero, mvPolynomialEval_truncFinsupp_eq_sum_coeff_mul_prod]
  rw [Finset.sum_eq_single (Finsupp.single () 1)]
  · rw [hcoeff]
    simp [PowerSeries.coeff_log, hy]
  · intro β _ hβ
    rw [hcoeff, PowerSeries.coeff_log]
    by_cases h0 : β () = 0
    · simp [h0]
    · have h1 : β () ≠ 1 := by
        intro h1; apply hβ; ext u; simp [h1]
      have hsupp : β.support = {()} := by
        ext u; simp [h0]
      rw [hsupp, Finset.prod_singleton]
      obtain ⟨k, hk⟩ : ∃ k, β () = k + 2 := ⟨β () - 2, by omega⟩
      have hp : (algebraMap B Q) ((fun _ : Unit => x) ()) ^ (k + 2) = 0 := by
        show y ^ (k + 2) = 0
        rw [pow_add, pow_two, hyy, mul_zero]
      rw [hk, hp, mul_zero]
  · intro h
    exfalso; apply h
    rw [Finset.mem_Iic]
    intro u
    simpa using hN'

end GlobalTheory.QLog.SqZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterAbsoluteValuePower
section
open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HeckeNormPow

def toQC {K : Type} [Field K] [NumberField K] (χ : HChar K) : GroundTheory.Global.QuasiCharacter K where
  toMonoidHom := QuotientGroup.lift _ χ.1 (by
    rintro _ ⟨a, rfl⟩
    exact χ.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 χ.2.1

theorem norm_val_eq_rpow : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), ∃ s : ℝ,
    ∀ w : HeightOneSpectrum (𝓞 K), ‖((χ.val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ s := by
  intro K _ _ χ
  obtain ⟨s, hs⟩ := GroundTheory.Global.QuasiCharacter.exists_norm_eq_rpow (toQC χ)
  refine ⟨-s, fun w => ?_⟩
  have h1 := hs
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (unif_spec w)] at h1
  have h2 : ((χ.val w : ℂˣ) : ℂ) = (((toQC χ) (GroundTheory.Global.IdeleClassGroup.mk K
      (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w)))) : ℂˣ) : ℂ) := rfl
  rw [h2, h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

end GlobalTheory.HeckeNormPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal

theorem IsHeckeL.ne_zero_nat {E : Type} [Field E] [NumberField E] {χ : HChar E} {Λ : ℂ → ℂ} (hu : IsUnitary χ)
    (hΛ : IsHeckeL χ Λ) {s : ℕ} (hs : 1 ≤ s) : Λ s ≠ 0 := by
  rcases hs.eq_or_lt with rfl | h
  · obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire E
    rw [Nat.cast_one]
    exact GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (GlobalTheory.HeckeOne.cf χ) GlobalTheory.HeckeOne.two_le_N
      (GlobalTheory.HeckeOne.norm_cf hu) GlobalTheory.HeckeOne.sumN GlobalTheory.HeckeOne.nonemptyN Z Λ hZd hΛ.1 hZ
      fun s hs => (hΛ.2 s hs).unique (GlobalTheory.HeckeOne.hasProd_exp hu hs)
  · have hs' : 1 < (s : ℂ).re := by
      rw [Complex.natCast_re]; exact_mod_cast h
    rw [(hΛ.2 _ hs').unique (GlobalTheory.HeckeOne.hasProd_exp hu hs')]
    exact Complex.exp_ne_zero _

theorem heckeL_ne_zero_nat : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℤ) (χ : HChar E) (Λ : ℂ → ℂ) (s : ℕ), IsUnitary χ → HasInf χ φ m → (∀ i, 0 < m i) → IsHeckeL χ Λ → 1 ≤ s → Λ s ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hu _ _ hΛ hs => hΛ.ne_zero_nat hu hs

end GlobalTheory.CMVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationCompIsoLiftIff
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem schemeFil_comp_iso (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (σ : A₀ ⟶ B₀) [IsMonHom σ] [IsIso σ] (X : Over (Sp R)) (j : B₀.left ⟶ X.left)
    (wj : j ≫ X.hom = B₀.hom ≫ spMap π) (w : (σ.left ≫ j) ≫ X.hom = A₀.hom ≫ spMap π) (d : Crys κ (spMap π) A₀) :
    d ∈ schemeFil κ A₀ X (σ.left ≫ j) w ↔ push κ (spMap π) σ d ∈ schemeFil κ B₀ X j wj := by
  haveI : IsMonHom (inv σ) :=
    { one_hom := by rw [← cancel_mono σ]; simp
      mul_hom := by
        rw [← cancel_mono σ]
        simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, IsIso.inv_hom_id] }

  have mK : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (RingHom.id R) (σ.left ≫ j) :=
    IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := A₀.hom ≫ spMap π) (σ := RingHom.id R) (φ := σ.left ≫ j)
      (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, w])
  have mJ : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (B₀.hom ≫ spMap π) (RingHom.id R) j :=
    IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := B₀.hom ≫ spMap π) (σ := RingHom.id R) (φ := j)
      (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, wj])
  have key : ∀ a, (homMor κ (spMap π) σ).isMor.pull1 (mJ.pull1 a) = mK.pull1 a := fun a ↦
    IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) rfl a
  have key' : ∀ a, (homMor κ (spMap π) (inv σ)).isMor.pull1 (mK.pull1 a) = mJ.pull1 a := fun a ↦
    IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) (by rw [← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.id_comp]) a
  have back : ∀ c : prim κ (spMap π) A₀, primPull κ (spMap π) σ (primPull κ (spMap π) (inv σ) c) = c := fun c ↦ by
    refine Subtype.ext ?_
    change (homMor κ (spMap π) σ).isMor.pull1 ((homMor κ (spMap π) (inv σ)).isMor.pull1 c.1) = c.1
    rw [IsMor.pullback1_comp _ _ (IsMor.id κ (A₀.hom ≫ spMap π)) (fun _ ↦ rfl)
      (by rw [← Over.comp_left, IsIso.hom_inv_id, Over.id_left])]
    exact IsMor.pullCohomologyOne_id _ _
  simp only [schemeFil, primitiveCrystalHodgeLiftClasses, Submodule.mem_dualAnnihilator, Submodule.mem_comap, Submodule.mem_map,
    Submodule.subtype_apply, push_apply]
  constructor
  · rintro H c ⟨a, ha, e⟩
    refine H _ ⟨a, ha, ?_⟩
    change mK.pull1 a = _
    rw [← key, e]; rfl
  · rintro H c ⟨a, ha, e⟩
    have := H (primPull κ (spMap π) (inv σ) c) ⟨a, ha, ?_⟩
    · rwa [back] at this
    · change mJ.pull1 a = (homMor κ (spMap π) (inv σ)).isMor.pull1 c.1
      rw [← key', e]

end GlobalTheory.SqLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationMiddleEqReductionOfTop
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FilRed

theorem filtration_reduction : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _)) (F : Submodule R (HdR A)) (F₁ : Submodule R₁ (HdR A₁)),
      (∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y) →
      (∀ d₁, crysToDR κ₁ h₁ d₁ ∈ F₁ ↔ ∃ d, crysToDR κ h d ∈ F ∧ M.Corr d d₁) ∧
      ((∀ y : HdR A₁, y ∈ Fil A₁ ↔ ∃ x ∈ Fil A, (redMor h₂).Corr x y)) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hS g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg M F F₁ hF
  have hπ : Function.Surjective π := hS.comp ▸ hS.surj₁.comp hS.surj
  have H := canonical_of_abelianDeRham P hS.nil hπ hS.ker
  have hb := H.crysToDR_bijective h hA hg
  have hs := (H g A₀ A i h hA hg).1.2
  have e' : i₁ ≫ i₂ = 𝟙 _ ≫ i := by rw [e, Category.id_comp]
  have key : ∀ d d₁, (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
    intro d d₁
    refine ⟨fun H' c' ↦ ?_, fun H' ↦ crysToDR_corr κ h h₁ M (redMor h₂) e' H'⟩
    obtain ⟨c, rfl⟩ := hs c'
    have k : GrpMor (dp0 R) (𝟙 (Sp R)) A κ₁ (spMap π₁) A₀
        (ρ.comp (RingHom.id R)) (𝟙 _ ≫ spMap π) (𝟙 _ ≫ i) := by
      let m := liftMor κ h
      refine ⟨IsDPMorphism.comp _ M.dp m.dp, ?_, ?_, ?_⟩
      · rw [Category.assoc, m.base, ← Category.assoc, M.base, Category.assoc, Cris.spMap_comp]
      · rw [Category.assoc, m.w, ← Category.assoc, M.w, Category.assoc]
      · intro T x y x₀ y₀ hx hy
        let x₁ : Over.mk (T.hom ≫ 𝟙 _) ⟶ A₀ := Over.homMk (x.left ≫ 𝟙 _) (by
          simp only [Over.mk_hom, Category.assoc]; rw [M.w, reassoc_of% (Over.w x)])
        let y₁ : Over.mk (T.hom ≫ 𝟙 _) ⟶ A₀ := Over.homMk (y.left ≫ 𝟙 _) (by
          simp only [Over.mk_hom, Category.assoc]; rw [M.w, reassoc_of% (Over.w y)])
        let x₂ : Over.mk ((Over.mk (T.hom ≫ 𝟙 _)).hom ≫ spMap π) ⟶ A := Over.homMk x₀.left (by simpa using Over.w x₀)
        let y₂ : Over.mk ((Over.mk (T.hom ≫ 𝟙 _)).hom ≫ spMap π) ⟶ A := Over.homMk y₀.left (by simpa using Over.w y₀)
        have h₁ : (x₁ * y₁).left = (x * y).left ≫ 𝟙 _ := M.mul T x y x₁ y₁ rfl rfl
        have h₂ : (x₂ * y₂).left = (x₁ * y₁).left ≫ i :=
          m.mul _ x₁ y₁ x₂ y₂ (by simp [x₂, x₁, hx]) (by simp [y₂, y₁, hy])
        have h₃ : (x₀ * y₀).left = (x₂ * y₂).left := by
          simp only [Hom.mul_def, Over.comp_left, Over.lift_left, x₂, y₂, Over.homMk_left]
        rw [h₃, h₂, h₁, Category.assoc]
    rw [GrpMor.pull_pull (liftMor κ h) M k (fun _ ↦ rfl) rfl c,
      ← GrpMor.pull_pull (redMor h₂) (liftMor κ₁ h₁) k (fun _ ↦ rfl) e' c]
    exact H' c
  refine ⟨fun d₁ ↦ ?_, (canonical_of_abelianDeRham P (isDPNilpotent_squareZero hJ) hS.surj hS.kerJ g A₁ A i₂ h₂ hA hg).2.2⟩
  rw [hF]
  constructor
  · rintro ⟨x, hx, c⟩
    obtain ⟨d, rfl⟩ := hb.2 x
    exact ⟨d, hx, (key d d₁).1 c⟩
  · rintro ⟨d, hd, c⟩
    exact ⟨_, hd, (key d d₁).2 c⟩

end GlobalTheory.FilRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationTensorLiftsIffProjections
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.ProdFil

variable {R : Type} [CommRing R] {I : Ideal R}

theorem left_ext {B : Scheme.{0}} {X Y : Over B} {T : Scheme.{0}} (g h : T ⟶ (X ⊗ Y).left)
    (h1 : g ≫ (fst X Y).left = h ≫ (fst X Y).left) (h2 : g ≫ (snd X Y).left = h ≫ (snd X Y).left) :
    g = h := by
  have w : h ≫ (X ⊗ Y).hom = g ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, ← Category.assoc, h1]
  have := CartesianMonoidalCategory.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y)
    (Over.homMk h w) (Over.OverMorphism.ext (by simpa using h1)) (Over.OverMorphism.ext (by simpa using h2))
  exact congrArg (fun f => f.left) this

theorem primitive_pullback_mem_hodgeFiltration_of_monHom (κ : DividedPowers I) {S : Scheme.{0}} {t : S ⟶ Sp R} {A A' : Over S} [GrpObj A]
    [GrpObj A'] (f : A' ⟶ A) [IsMonHom f] {X X' : Over (Sp R)} {i : A.left ⟶ X.left} {i' : A'.left ⟶ X'.left}
    (w : i ≫ X.hom = A.hom ≫ t) (w' : i' ≫ X'.hom = A'.hom ≫ t) (m : X'.left ⟶ X.left) (hm : m ≫ X.hom = X'.hom)
    (e : f.left ≫ i = i' ≫ m) {c : prim κ t A} (hc : c ∈ primitiveCrystalHodgeLiftClasses κ A X i w) :
    primPull κ t f c ∈ primitiveCrystalHodgeLiftClasses κ A' X' i' w' := by
  obtain ⟨a, ha, hac⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hc)
  have hmor : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (X'.hom ≫ 𝟙 _) (RingHom.id R) m :=
    IsMor.of_over (dp0 R) (by rw [← Category.assoc, hm])
  refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨hmor.pull1 a, hmor.pullback1_mem_hodgeFiltration ha, ?_⟩)
  have hfi : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (A'.hom ≫ t) (RingHom.id R) (f.left ≫ i) :=
    IsMor.of_dividedPowersZeroIdeal κ (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, Category.assoc, w,
      ← Category.assoc, Over.w f])
  rw [IsMor.pullback1_comp _ _ hfi (fun _ ↦ rfl) e.symm]
  change _ = (homMor κ t f).isMor.pull1 c.1
  rw [show (c : Cris.H1 κ (A.hom ≫ t)) = _ from hac.symm]
  exact (IsMor.pullback1_comp _ _ hfi (fun _ ↦ rfl) rfl a).symm

theorem schemeFil_tensor_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left)
    (wi : i ≫ X.hom = A₀.hom ≫ spMap π) (wj : j ≫ Y.hom = B₀.hom ≫ spMap π)
    (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (wl : l ≫ (X ⊗ Y).hom = (A₀ ⊗ B₀).hom ≫ spMap π) (d : Crys κ (spMap π) (A₀ ⊗ B₀)),
    d ∈ schemeFil κ (A₀ ⊗ B₀) (X ⊗ Y) l wl ↔
      push κ (spMap π) (fst A₀ B₀) d ∈ schemeFil κ A₀ X i wi ∧ push κ (spMap π) (snd A₀ B₀) d ∈ schemeFil κ B₀ Y j wj := by
  intro R R₀ _ _ I κ π A₀ B₀ _ _ X Y i j wi wj e e' he he' h1 h1' l hl1 hl2 wl d
  have hAB : IsMonHom (1 : A₀ ⟶ B₀) := inferInstanceAs (IsMonHom (toUnit A₀ ≫ η[B₀]))
  have hBA : IsMonHom (1 : B₀ ⟶ A₀) := inferInstanceAs (IsMonHom (toUnit B₀ ≫ η[A₀]))
  have one_left : ∀ (C D : Over (Sp R₀)) [GrpObj C] [GrpObj D],
      (1 : C ⟶ D).left = C.hom ≫ (1 : Over.mk (𝟙 (Sp R₀)) ⟶ D).left := by
    intro C D _ _
    have : (1 : C ⟶ D) = (Over.homMk C.hom (by simp) : C ⟶ Over.mk (𝟙 (Sp R₀))) ≫ 1 := by simp
    rw [this]; rfl
  constructor
  · intro H
    constructor
    · refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
      rw [push_apply]
      exact (Submodule.mem_dualAnnihilator _).1 H _
        (primitive_pullback_mem_hodgeFiltration_of_monHom κ (fst A₀ B₀) wi wl (fst X Y).left (Over.w _) hl1.symm hc)
    · refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
      rw [push_apply]
      exact (Submodule.mem_dualAnnihilator _).1 H _
        (primitive_pullback_mem_hodgeFiltration_of_monHom κ (snd A₀ B₀) wj wl (snd X Y).left (Over.w _) hl2.symm hc)
  · rintro ⟨H1, H2⟩
    refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
    let ι₁ : A₀ ⟶ A₀ ⊗ B₀ := lift (𝟙 A₀) 1
    let ι₂ : B₀ ⟶ A₀ ⊗ B₀ := lift 1 (𝟙 B₀)
    have hmul : (fst A₀ B₀ ≫ ι₁) * (snd A₀ B₀ ≫ ι₂) = 𝟙 _ := by
      ext
      · rw [MonObj.mul_comp]; simp [ι₁, ι₂]
      · rw [MonObj.mul_comp]; simp [ι₁, ι₂]
    have hdec : c = primPull κ _ (fst A₀ B₀) (primPull κ _ ι₁ c) + primPull κ _ (snd A₀ B₀) (primPull κ _ ι₂ c) := by
      apply Subtype.ext
      have := c.2 (A₀ ⊗ B₀) (fst A₀ B₀ ≫ ι₁) (snd A₀ B₀ ≫ ι₂)
      rw [hmul, ← pullOver_pullOver, ← pullOver_pullOver] at this
      have hid : pullOver κ (spMap π) (𝟙 (A₀ ⊗ B₀)) (c : Cris.H1 κ ((A₀ ⊗ B₀).hom ≫ spMap π)) = c :=
        IsMor.pullCohomologyOne_id _ _
      rw [← hid, this]; rfl

    let mX : X ⟶ X ⊗ Y := lift (𝟙 X) (Over.homMk (X.hom ≫ e') (by simp [he']))
    let mY : Y ⟶ X ⊗ Y := lift (Over.homMk (Y.hom ≫ e) (by simp [he])) (𝟙 Y)
    have eX : ι₁.left ≫ l = i ≫ mX.left := by
      apply left_ext
      · rw [Category.assoc, hl1, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp [ι₁, mX]
      · rw [Category.assoc, hl2, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp only [ι₁, mX, lift_snd, Over.homMk_left]
        rw [one_left, Category.assoc, h1', ← Category.assoc, ← wi, Category.assoc]
    have eY : ι₂.left ≫ l = j ≫ mY.left := by
      apply left_ext
      · rw [Category.assoc, hl1, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp only [ι₂, mY, lift_fst, Over.homMk_left]
        rw [one_left, Category.assoc, h1, ← Category.assoc, ← wj, Category.assoc]
      · rw [Category.assoc, hl2, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp [ι₂, mY]
    have k1 := primitive_pullback_mem_hodgeFiltration_of_monHom κ ι₁ wl wi mX.left (Over.w _) eX hc
    have k2 := primitive_pullback_mem_hodgeFiltration_of_monHom κ ι₂ wl wj mY.left (Over.w _) eY hc
    rw [hdec, map_add (f := _), ← push_apply κ _ (fst A₀ B₀) d, ← push_apply κ _ (snd A₀ B₀) d, (Submodule.mem_dualAnnihilator _).1 H1 _ k1,
      (Submodule.mem_dualAnnihilator _).1 H2 _ k2, add_zero]

end GlobalTheory.SqLift.ProdFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfIsStd
section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.isDPMorphism_of_isStd :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)),
      Q.IsStd δ η → ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (F : Q.P →+* C) (c : C),
        c ∈ J'' → IsDPMorphism δ δ'' (F.comp (algebraMap B Q.P)) → (∀ n, F (Q.e n) = δ''.dpow n c) →
          IsDPMorphism η δ'' F := by
  intro B _ J δ Q η hQ C _ J'' δ'' F c hc hF he
  have hS : Q.ext J = Ideal.span (algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1)) := by
    rw [Ideal.span_union, ← Ideal.map_span, Ideal.span_eq]; rfl
  refine IsDPMorphism.on_span η δ'' hS ?_ ?_
  · rintro s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · exact hF.1 (Ideal.mem_map_of_mem _ ha)
    · rw [he]; exact δ''.dpow_mem k.succ_ne_zero hc
  · rintro n s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · rw [hQ.dp.2 a ha]
      exact (hF.2 a ha).symm
    · have h1 := Q.e_one_mem_ext J
      show F (η.dpow n (Q.e (k + 1))) = δ''.dpow n (F (Q.e (k + 1)))
      have h2 : η.dpow n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
        rw [← hQ.var (k + 1), η.dpow_comp k.succ_ne_zero h1, hQ.var]
      rw [h2, map_mul, map_natCast, he, he, δ''.dpow_comp k.succ_ne_zero hc]

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionMulPrimeWideIndicatorStatement
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNarrowRayClassLFunction_mul_prime_wideIndicator : ∀ {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → 𝔭 ≠ ⊥ → 𝔭 ⊔ 𝔪 = ⊤ →
    ∀ (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ), IsRayL 𝔪 (wideInd C) Z → IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z' →
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
  first | exact @GlobalTheory.isRayL_mul_prime_wideInd | exact GlobalTheory.isRayL_mul_prime_wideInd | (intros; apply GlobalTheory.isRayL_mul_prime_wideInd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomFibreDerivationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation :
    ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R]
      (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)),
      (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
      ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W),
        ρ (dw a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h) := by
  intro I _ _ g R _ _ N t W W₀ hW ρ hρ a h
  have expand := isTay_expand hW hρ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [expand (dw a h), expand h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [LinearMap.lTensor_tmul, ← dw_slTayHol hW a h k s]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatInPadicIntegersOfTwistedDifferenceStatement
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRatInPadicIntegers_of_twisted_difference : ∀ {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime] (g : G) (q : ℕ), l ∣ q →
    ∀ x : G → ℚ, (∀ C, InZl l (x C - (q : ℚ) * x (C * g))) → ∀ C, InZl l (x C) := by
  first | exact @GlobalTheory.inZl_of_twisted_difference | exact GlobalTheory.inZl_of_twisted_difference | (intros; apply GlobalTheory.inZl_of_twisted_difference <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyGenericOfKeyClosedPtsStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyGeneric_of_keyClosedPts' : GlobalTheory.LocAcyc.KeyClosedPts → GlobalTheory.LocAcyc.KeyGeneric := by
  first | (exact @GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts) | (exact GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts) | (intros; apply GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts  <;> assumption)
end

