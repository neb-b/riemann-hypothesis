module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SmoothCharNorm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_image_units (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (χ '' {x : kˣ | valuation k (x : k) = 1}).Finite := by
  have hS := GlobalTheory.SmGL.UnramFixed.isCompact_unitsO k
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun z : kˣ => (fun y => z⁻¹ * y) ⁻¹' (χ.ker : Set kˣ))
    (fun z => (continuous_const.mul continuous_id).isOpen_preimage _ hχ)
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine (t.finite_toSet.image χ).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨i, hi, ?_⟩
  have : χ (i⁻¹ * y) = 1 := hyi
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

theorem norm_eq_one_of_valuation_eq_one (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : kˣ)
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by
  by_contra hne
  have hpos : 0 < ‖(χ u : ℂ)‖ := norm_pos_iff.2 (χ u).ne_zero
  have hinj := pow_right_injective₀ hpos hne
  have hinf := Set.infinite_range_of_injective hinj
  apply hinf
  refine ((finite_image_units χ hχ).image (fun w : ℂˣ => ‖(w : ℂ)‖)).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨χ (u ^ n), ⟨u ^ n, ?_, rfl⟩, ?_⟩
  · simp [Units.val_pow_eq_pow_val, map_pow, hu]
  · simp [map_pow, Units.val_pow_eq_pow_val, norm_pow]

noncomputable def ordHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord k x)
  map_one' := by
    have : ord k (1 : kˣ) = 0 := ord_eq_zero_iff.2 (by simp)
    simp [this]
  map_mul' x y := by simp [ord_mul, ofAdd_add]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  have := congrArg Multiplicative.toAdd (map_zpow (ordHom k) x n)
  simpa [ordHom, toAdd_zpow, smul_eq_mul] using this

end GlobalTheory.SmoothCharNorm

theorem GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by
  intro k _ _ _ _ χ hχ
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hord : ord k ϖ = 1 := ord_eq_one hϖ
  have ha : 0 < ‖(χ ϖ : ℂ)‖ := norm_pos_iff.2 (χ ϖ).ne_zero
  have hq : (1 : ℝ) < (resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  have hlq : Real.log (resCard k : ℝ) ≠ 0 := (Real.log_pos hq).ne'
  refine ⟨-Real.log ‖(χ ϖ : ℂ)‖ / Real.log (resCard k : ℝ), fun z => ?_⟩
  have hz : ‖(χ z : ℂ)‖ = ‖(χ ϖ : ℂ)‖ ^ ord k z := by
    have hw : valuation k ((ϖ ^ (-ord k z) * z : kˣ) : k) = 1 := by
      rw [← ord_eq_zero_iff, ord_mul, GlobalTheory.SmoothCharNorm.ord_zpow, hord]; ring
    have hdec : z = ϖ ^ (ord k z) * (ϖ ^ (-ord k z) * z) := by group
    conv_lhs => rw [hdec]
    rw [map_mul, Units.val_mul, norm_mul,
      GlobalTheory.SmoothCharNorm.norm_eq_one_of_valuation_eq_one χ hχ _ hw, mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  have hϖabs : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
    refine (nabs_properties k).2.2.2.2.1 ⟨ϖ, hlt.le⟩ ϖ ?_ rfl
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one, Ideal.mem_span_singleton,
      (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
    rfl
  have hn : nabs k z = (resCard k : ℝ) ^ (-ord k z) := by
    have hw : valuation k ((ϖ ^ (-ord k z) * z : kˣ) : k) = 1 := by
      rw [← ord_eq_zero_iff, ord_mul, GlobalTheory.SmoothCharNorm.ord_zpow, hord]; ring
    have hdec : z = ϖ ^ (ord k z) * (ϖ ^ (-ord k z) * z) := by group
    conv_lhs => rw [hdec]
    rw [nabs_mul, (nabs_eq_one_iff _).2 hw, mul_one]
    have hp : nabs k (ϖ ^ ord k z) = nabs k ϖ ^ ord k z := by
      simp [nabs, map_zpow]
    rw [hp, hϖabs, _root_.inv_zpow, _root_.zpow_neg]
  rw [hz, hn, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (by positivity), Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos (by positivity)]
  congr 1
  push_cast
  field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealPlaceRecordTied
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_realPlace_record_tied :
    (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) →
    ∀ D : D7, ∃ A : ProvA, ProvisionCompatibility D A := by
  intro H D
  classical
  choose grp hgrp using fun p q : ℕ =>
    GlobalTheory.DetSqrtCover.exists_grpData_map_haar p q (D.cd.cd p q) (D.cd.haar p q)
  have key : ∀ (p q : ℕ) (lam : Ix p q → ℚ), ∃ R : DSRep (grp p q),
      IsParam lam → HasParam R lam := by
    intro p q lam
    by_cases h : IsParam lam
    · obtain ⟨R, hR⟩ := H p q (grp p q) lam h
      exact ⟨R, fun _ => hR⟩
    · obtain ⟨R, -⟩ := H p q (grp p q) _ (realPlaceStdParam_isParam p q)
      exact ⟨R, fun h' => absurd h' h⟩
  choose ds hds using key
  exact ⟨⟨grp, fun p q r s => Classical.choice (_root_.GlobalTheory.nonempty_fockData_pair p q r s _ _ _), ds⟩,
    ⟨hgrp, fun p q lam h => by first | exact hds p q lam h | exact fun _ => hds p q lam h⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedEffectiveCartierDivisorPullback
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.DivPull

variable {F : Type} [Field F] {B Y : GlobalTheory.ProjVar.Var F} {φ : B.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ B.X}

theorem regAt_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : RegAt (f y) g) :
    RegAt y (φ g) :=
  mem_O_ratOf.1 (h.map_mem_O (z := y) (mem_O_ratOf.2 hg))

theorem unitAt_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : UnitAt (f y) g) :
    UnitAt y (φ g) :=
  (unitAt_iff ((map_ne_zero φ).2 hg.ne_zero)).2
    ⟨regAt_map h hg.regAt, by rw [← map_inv₀]; exact regAt_map h hg.inv.regAt⟩

theorem unitAt_of_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : RegAt (f y) g)
    (hu : UnitAt y (φ g)) : UnitAt (f y) g := by
  have h0 : g ≠ 0 := (map_ne_zero φ).1 hu.ne_zero
  exact (unitAt_iff h0).2 ⟨hg, mem_O_ratOf.1
    (h.inv_mem_O (z := y) (mem_O_ratOf.2 hg) h0 (mem_O_ratOf.2 hu.inv.regAt))⟩

theorem exists_pullback (h : (ratOf B).IsHom (ratOf Y) φ f) (D : B.Dv) :
    ∃ D' : Y.Dv, ∀ (y : Y.X) (g : B.Fnˣ), D.IsEqn (f y) g →
      D'.IsEqn y (Units.map (φ : B.Fn →* Y.Fn) g) := by
  choose e he using fun y : Y.X => D.exists_isEqn (f y)
  have key : ∀ (y : Y.X) (g : B.Fnˣ), D.IsEqn (f y) g →
      germOf y (Units.map (φ : B.Fn →* Y.Fn) (e y)) = germOf y (Units.map (φ : B.Fn →* Y.Fn) g) := by
    intro y g hg
    rw [germOf_eq_iff]
    have := unitAt_map h ((he y).iff_unitAt.1 hg)
    rw [map_div₀] at this
    exact this
  refine ⟨show cartierGroup Y.X from ⟨fun y => germOf y (Units.map (φ : B.Fn →* Y.Fn) (e y)), fun y => ?_⟩, key⟩
  obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (f y)
  exact ⟨f ⁻¹ᵁ U, hU, Units.map (φ : B.Fn →* Y.Fn) g, fun z hz => key z g (hg _ hz)⟩

theorem exists_reduced_pullback : ∀ (F : Type) [Field F] (B Y : GlobalTheory.ProjVar.Var F) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X) (D : B.Dv), (ratOf B).IsHom (ratOf Y) φ f → KeepsRad (ratOf B) (ratOf Y) φ f → D.Eff → (∀ (y : B.X) (g : B.Fnˣ), D.IsEqn y g → ∀ (a : B.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g)) → ∃ D' : Y.Dv, D'.Eff ∧ (∀ y, y ∈ D'.supp ↔ f y ∈ D.supp) ∧ ∀ (y : Y.X) (g : Y.Fnˣ), D'.IsEqn y g → ∀ (a : Y.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g) := by
  intro F _ B Y φ f D h hk hD hr
  obtain ⟨D', hD'⟩ := exists_pullback h D
  refine ⟨D', CartierDiv.eff_iff.2 fun y g hg => ?_, fun y => ?_, fun y g hg a n ha hn => ?_⟩
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    have h1 := ((hD' y e he).iff_unitAt.1 hg).regAt.mul (regAt_map h (CartierDiv.eff_iff.1 hD _ e he))
    have h0 : φ e ≠ 0 := (map_ne_zero φ).2 e.ne_zero
    have e1 : (g : Y.Fn) / φ e * φ e = g := div_mul_cancel₀ _ h0
    exact e1 ▸ h1
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    change ¬ D'.IsEqn y 1 ↔ ¬ D.IsEqn (f y) 1
    rw [not_iff_not, (hD' y e he).iff_unitAt, he.iff_unitAt, Units.val_one, Units.val_one, one_div, one_div]
    constructor
    · intro hu
      have := hu.inv
      rw [inv_inv] at this
      exact (unitAt_of_map h (CartierDiv.eff_iff.1 hD _ e he) this).inv
    · intro hu
      have := hu.inv
      rw [inv_inv] at this
      exact (unitAt_map h this).inv
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    have hR := hk y e ⟨e.ne_zero, mem_O_ratOf.2 (CartierDiv.eff_iff.1 hD _ e he), fun x m hx hm =>
      mem_O_ratOf.2 (hr _ e he x m (mem_O_ratOf.1 hx) (mem_O_ratOf.1 hm))⟩
    have hu : UnitAt y ((g : Y.Fn) / φ e) := (hD' y e he).iff_unitAt.1 hg
    have h0 : φ e ≠ 0 := (map_ne_zero φ).2 e.ne_zero
    have hg0 : (g : Y.Fn) ≠ 0 := g.ne_zero
    have e1 : a ^ n / g * ((g : Y.Fn) / φ e) = a ^ n / φ e := by field_simp
    have e2 : a / φ e * ((g : Y.Fn) / φ e)⁻¹ = a / g := by field_simp
    have h2 : RegAt y (a / φ e) :=
      mem_O_ratOf.1 (hR.2.2 a n (mem_O_ratOf.2 ha) (mem_O_ratOf.2 (e1 ▸ hn.mul hu.regAt)))
    exact e2 ▸ h2.mul hu.inv.regAt

end GlobalTheory.FlagBundle.DivPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBounds
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

theorem valuation_chain_ratio_bounds (k : Type) [Field k] [ValuativeRel k] (m : ℕ) (r1 r2 : Fin m → kˣ) :
    ∃ R1 R2 : kˣ, 1 ≤ valuation k (R1 : k) ∧ valuation k (R2 : k) ≤ 1 ∧
      ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 →
        (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧
          valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) →
        ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  induction m with
  | zero =>
    refine ⟨1, 1, by simp, by simp, ?_⟩
    intro t ht _ i
    have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst hi
    rw [ht]; simp
  | succ m ih =>
    obtain ⟨R1', R2', h1', h2', hR⟩ := ih (fun j => r1 j.succ) (fun j => r2 j.succ)
    set a : kˣ := if valuation k (r1 0 : k) ≤ 1 then 1 else r1 0 with ha_def
    set b : kˣ := if 1 ≤ valuation k (r2 0 : k) then 1 else r2 0 with hb_def
    have ha1 : 1 ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have har : valuation k (r1 0 : k) ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    have hb1 : valuation k (b : k) ≤ 1 := by
      rw [hb_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have hbr : valuation k (b : k) ≤ valuation k (r2 0 : k) := by
      rw [hb_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    refine ⟨R1' * a, R2' * b, ?_, ?_, ?_⟩
    · simp only [Units.val_mul, map_mul]
      exact one_le_mul h1' ha1
    · simp only [Units.val_mul, map_mul]
      exact mul_le_one' h2' hb1
    intro t ht hrat
    have hT := hR (fun j => t j.succ) (by simp only [Fin.succ_last]; exact ht) (fun i => by
      have := hrat i.succ
      rw [← Fin.succ_castSucc] at this; exact this)
    have hR1le : valuation k (R1' : k) ≤ valuation k ((R1' * a : kˣ) : k) := by
      simp only [Units.val_mul, map_mul]; exact le_mul_of_one_le_right' ha1
    have hR2le : valuation k ((R2' * b : kˣ) : k) ≤ valuation k (R2' : k) := by
      simp only [Units.val_mul, map_mul]; exact mul_le_of_le_one_right' hb1
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 := hrat 0
      have ht1 := hT 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0 ht1
      have hne : ((t 1 : kˣ) : k) ≠ 0 := (t 1).ne_zero
      have hsplit : ((t 0 : kˣ) : k) = ((t 0 : k) / t 1) * t 1 := by field_simp
      rw [hsplit, map_mul]
      constructor
      · simp only [Units.val_mul, map_mul]
        calc valuation k (R2' : k) * valuation k (b : k)
            = valuation k (b : k) * valuation k (R2' : k) := mul_comm _ _
          _ ≤ valuation k (r2 0 : k) * valuation k (t 1 : k) := mul_le_mul' hbr ht1.1
          _ ≤ _ := mul_le_mul' h0.1 le_rfl
      · simp only [Units.val_mul, map_mul]
        calc valuation k ((t 0 : k) / t 1) * valuation k (t 1 : k)
            ≤ valuation k (r1 0 : k) * valuation k (R1' : k) := mul_le_mul' h0.2 ht1.2
          _ ≤ valuation k (a : k) * valuation k (R1' : k) := mul_le_mul' har le_rfl
          _ = _ := mul_comm _ _
    · have := hT j
      exact ⟨hR2le.trans this.1, this.2.trans hR1le⟩

theorem chain_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (r1 r2 : Fin m → kˣ), ∃ R1 R2 : kˣ, ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 → (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧ valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) → ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  intro k _ _ _ _ m r1 r2
  obtain ⟨R1, R2, -, -, h⟩ := valuation_chain_ratio_bounds k m r1 r2
  exact ⟨R1, R2, h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwExtend
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.Mem.SJ.Place

theorem exists_tw_extend {H K X : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (V : Submodule ℂ X) (φ : V →ₗ⋆[ℂ] K) (z : ℂ) (s : Bool) :
    ∃ sE : Tw s H →ₗ⋆[ℂ] Tw s K, ∀ (x : Tw s H) (hx : e (Tw.out x) ∈ V), sE x = Tw.mk s (z • φ ⟨e (Tw.out x), hx⟩) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V.comap e) (e.restrict (p := V.comap e) (q := V) fun _ h => h)
  refine ⟨{ toFun := fun x => Tw.mk s (z • φ (g (Tw.out x))), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    show z • φ (g (Tw.out x + Tw.out y)) = z • φ (g (Tw.out x)) + z • φ (g (Tw.out y))
    rw [map_add (f := _), map_add (f := _), smul_add]
  · intro a x
    show z • φ (g (cj s a • Tw.out x)) = cj s (starRingEnd ℂ a) • z • φ (g (Tw.out x))
    rw [map_smul, map_smulₛₗ, cj_conj, smul_comm]
  · intro x hx
    have := LinearMap.congr_fun hg ⟨Tw.out x, hx⟩
    show Tw.mk s (z • φ (g (Tw.out x))) = _
    rw [show g (Tw.out x) = ⟨e (Tw.out x), hx⟩ from this]

theorem scale_norm {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {c n a : ℝ} (hc : 0 < c) (hn : 0 < n) (y : K)
    (h : ‖y‖ ^ 2 = c * a) : n * ‖((1 : ℂ) * (((Real.sqrt (c * n))⁻¹ : ℝ) : ℂ)) • y‖ ^ 2 = a := by
  have hcn : 0 < c * n := mul_pos hc hn
  rw [one_mul, norm_smul, Complex.norm_real, mul_pow, h, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hcn.le]
  field_simp

theorem sEEofTT_spec {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0)))
    (𝓕 : Set (GA D (D.sp.Y 0))) (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) (h : EvalTieT M μ 𝓕 E X G ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E X G ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re ∧
      ((sEEofTT M μ 𝓕 E X G ι t c T : HHX X) : L2X X) ∈ goodSub X G := by
  have e : sEEofTT M μ 𝓕 E X G ι t c = (conjHH X G).toLinearMap.comp h.choose_spec.2.choose.toLinearMap := by
    unfold sEEofTT
    exact dif_pos h
  have e' : sEEofTT M μ 𝓕 E X G ι t c T = conjHH X G (h.choose_spec.2.choose T) := by
    rw [e]
    rfl
  rw [e']
  refine ⟨?_, (mem_EEC X G _).1 (h.choose_spec.2.choose T).2⟩
  rw [(conjHH X G).norm_map]
  exact (h.choose_spec.2.choose_spec T).2

theorem exists_placement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) (ι : GA D (Yc D 0) ≃* St.B.I.GA) (t : GA D (Yc D 0)) (c : ℝ) (s : Bool), R.models_HE → 0 < c → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c → ∃ (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX St)), 0 < κ ∧ ∀ (x : Tw s R.HE.H) (hx : R.HE.e (Tw.out x) ∈ R.EEat (R.levR F true)), sE x = Tw.mk s (((1 : ℂ) * (κ : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) ∧ RealDat.nP F true * ‖sE x‖ ^ 2 = ‖x‖ ^ 2 ∧ ((Tw.out (sE x) : HHX St) : L2X St) ∈ goodSub St Gd := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F St Gd ι t c s hE hc h
  have hn : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  obtain ⟨sE, hs⟩ := exists_tw_extend R.HE.e (R.EEat (R.levR F true))
    (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c)
    ((1 : ℂ) * (((Real.sqrt (c * RealDat.nP F true))⁻¹ : ℝ) : ℂ)) s
  refine ⟨(Real.sqrt (c * RealDat.nP F true))⁻¹, sE, inv_pos.2 (Real.sqrt_pos.2 (mul_pos hc hn)), fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := sEEofTT_spec (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c h ⟨R.HE.e (Tw.out x), hx⟩
  refine ⟨hs x hx, ?_, ?_⟩
  · rw [hs x hx]
    have hip : (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2 := by
      rw [← hE.2.2]
      exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (Tw.out x)).symm
    have key := scale_norm (K := HHX St) hc hn
      (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) (h1.trans (congrArg (c * ·) hip))
    exact key
  · rw [hs x hx]
    exact (goodSub St Gd).smul_mem _ h2

end GlobalTheory.Mem.SJ.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilSurj

open GlobalTheory.WeilRestrict Polynomial

theorem card_le_of_forall_pow_eq {F : Type*} [Field F] [Finite F] {m : ℕ} (hm : 1 < m)
    (h : ∀ x : F, x ^ m = x) : Nat.card F ≤ m := by
  classical
  haveI := Fintype.ofFinite F
  have hdeg : (X : F[X]).natDegree < (X ^ m : F[X]).natDegree := by
    rw [natDegree_X, natDegree_X_pow]; exact hm
  have hp : (X ^ m - X : F[X]) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_X_pow, natDegree_zero] at this
    omega
  have hsub : (Finset.univ : Finset F) ⊆ (X ^ m - X : F[X]).roots.toFinset := by
    intro x _
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    simp [h x]
  calc Nat.card F = (Finset.univ : Finset F).card := by rw [Nat.card_eq_fintype_card, Finset.card_univ]
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Multiset.toFinset_card_le _
    _ ≤ _ := card_roots' _
    _ = m := by rw [natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_X_pow]

theorem exists_weil_of_fixes : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (h' : IsPlaceOver A W) (σ : Weil h), (∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x) → ∃ τ : Weil h', ∀ z : Ω, (σ : G E Ω) z = (τ : G K Ω) z := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w W h h' σ hσ
  obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
  have hq1 : 1 < normV w := one_lt_normV w
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have := one_lt_normV W
      rw [hf, h0, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact h0
  have hφdeg : deg (resWeil h h' (frob h')) = f := by
    have h1 : ActsAs A (normV w ^ f) (frob h' : G K Ω) 1 0 := by
      rw [← hf]; exact actsAs_one_iff.mpr isFrob_frob
    have h2 := actsAs_resG (K := E) h1
    have := deg_eq (σ := resWeil h h' (frob h')) h2
    simpa using this
  obtain ⟨k, r, hr0, hrf, hdr⟩ : ∃ k r : ℤ, 0 ≤ r ∧ r < f ∧ r + f * k = deg σ :=
    ⟨deg σ / f, deg σ % f, Int.emod_nonneg _ (by exact_mod_cast hf0.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hf0), Int.emod_add_mul_ediv _ _⟩
  set σ' : Weil h := σ * (resWeil h h' (frob h' ^ k))⁻¹ with hσ'
  have hdeg' : deg σ' = r := by
    rw [hσ', deg_mul, deg_inv, map_zpow, deg_zpow, hφdeg]
    linear_combination -hdr
  have hfix' : ∀ x : K, (σ' : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x := by
    intro x
    rw [hσ', Subgroup.coe_mul, AlgEquiv.mul_apply, ← map_inv, resWeil_apply, AlgEquiv.commutes, hσ]
  have hr : r = 0 := by
    by_contra hne
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hne)
    set n := r.toNat with hn'
    have hn : (n : ℤ) = r := Int.toNat_of_nonneg hr0
    have hact := actsAs_of_deg (σ := σ') (a := n) (b := 0) (by rw [hdeg', hn]; simp)
    have hmem : ∀ x : 𝓞 K, x ^ (normV w ^ n) - x ∈ W.asIdeal := by
      intro x
      rw [← h' _]
      have hx : A.valuation (algebraMap K Ω x) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (map_isIntegral_int (algebraMap K Ω) x.isIntegral_coe))
      have := hact.2 _ hx
      rw [hfix', pow_zero, pow_one, Valuation.map_sub_swap] at this
      have e : algebraMap K Ω ((x ^ (normV w ^ n) - x : 𝓞 K) : K) =
          (algebraMap K Ω x) ^ (normV w ^ n) - algebraMap K Ω x := by simp
      rw [e]; exact this
    haveI : W.asIdeal.IsMaximal := W.isMaximal
    letI : Field (𝓞 K ⧸ W.asIdeal) := Ideal.Quotient.field _
    haveI : Finite (𝓞 K ⧸ W.asIdeal) := W.asIdeal.finiteQuotientOfFreeOfNeBot W.ne_bot
    have hall : ∀ y : 𝓞 K ⧸ W.asIdeal, y ^ (normV w ^ n) = y := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem x
    have hn0 : n ≠ 0 := by omega
    have hcard := card_le_of_forall_pow_eq (one_lt_pow₀ hq1 hn0) hall
    have hQ : Nat.card (𝓞 K ⧸ W.asIdeal) = normV w ^ f := hf
    rw [hQ] at hcard
    have : normV w ^ n < normV w ^ f := Nat.pow_lt_pow_right hq1 (by omega)
    omega
  have hine : (σ' : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp (by rw [hdeg', hr])
  let τ0 : G K Ω := { (σ' : G E Ω).toRingEquiv with commutes' := fun x => hfix' x }
  have hτ0 : τ0 ∈ Ine (F := K) A := hine
  refine ⟨ineIncl h' ⟨τ0, hτ0⟩ * frob h' ^ k, fun z => ?_⟩
  have key : (((resWeil h h' (frob h' ^ k))⁻¹ : Weil h) : G E Ω)
      (((frob h' ^ k : Weil h') : G K Ω) z) = z := by
    rw [← map_inv, resWeil_apply, ← AlgEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, AlgEquiv.one_apply]
  show (σ : G E Ω) z = (σ' : G E Ω) (((frob h' ^ k : Weil h') : G K Ω) z)
  rw [hσ', Subgroup.coe_mul, AlgEquiv.mul_apply, key]

end GlobalTheory.WeilSurj
end
end

