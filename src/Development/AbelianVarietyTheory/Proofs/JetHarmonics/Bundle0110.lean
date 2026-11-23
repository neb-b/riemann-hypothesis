module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupAdd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseChangeOfFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.LiesBaseChange

theorem isIntegral_of_scale (S : CDVR) {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L]
    [Algebra W L] [IsFractionRing W L] (φ : S.Fr →+* L) (hφ : φ.Finite) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (φ z) = (r : ℤ) * vV S.V z) (w : W) :
    (φ.comp (algebraMap S.V S.Fr)).IsIntegralElem (algebraMap W L w) := by
  have hint : ∀ a : S.V, ∃ v : W, algebraMap W L v = φ (algebraMap S.V S.Fr a) := fun a =>
    (IntegralFrameAllCompare.mem_range_iff _).2 (by
      rw [hi]; exact mul_nonneg (by positivity) ((IntegralFrameAllCompare.mem_range_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : S.V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = φ (algebraMap S.V S.Fr a) := hg0
  letI : Algebra S.V W := g.toAlgebra
  letI : Algebra S.Fr L := φ.toAlgebra
  letI : Algebra S.V L := (φ.comp (algebraMap S.V S.Fr)).toAlgebra
  have t1 : IsScalarTower S.V W L := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have t2 : IsScalarTower S.V S.Fr L := IsScalarTower.of_algebraMap_eq fun a => rfl
  have : FiniteDimensional S.Fr L := hφ
  obtain ⟨-, hloc, -, -, hfr⟩ := integralClosure_finite_local_of_isAdicComplete S.V S.cpl L
  have : CharZero S.Fr := IsFractionRing.charZero_of_isFractionRing S.V
  have hded : IsDedekindDomain (integralClosure S.V L) := integralClosure.isDedekindDomain S.V S.Fr L
  have hval : ValuationRing (integralClosure S.V L) := by
    have := ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (integralClosure S.V L)).out 3 2).1 hded
    exact this
  have hBW : ∀ b : integralClosure S.V L, ∃ v : W, algebraMap W L v = b := fun b =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.tower_top (A := W) b.2)
  choose k0 hk0 using hBW
  let k : integralClosure S.V L →+* W :=
    { toFun := k0
      map_one' := hinj (by simp [hk0])
      map_mul' := fun a b => hinj (by simp [hk0])
      map_zero' := hinj (by simp [hk0])
      map_add' := fun a b => hinj (by simp [hk0]) }
  have hk : ∀ b, algebraMap W L (k b) = b := hk0
  have hmax : ((maximalIdeal W).comap k).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap S.V (integralClosure S.V L))
      (fun x => Algebra.IsIntegral.isIntegral x) ((maximalIdeal W).comap k) ?_
    have hle : maximalIdeal S.V ≤ ((maximalIdeal W).comap k).comap (algebraMap S.V (integralClosure S.V L)) := by
      intro a ha
      by_cases h0 : a = 0
      · simp [h0]
      rw [Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal]
      intro hu
      have h1 := IntegralFrameAllCompare.vV_of_isUnit (K := L) hu
      have h3 : (0 : ℤ) < r * vV S.V (algebraMap S.V S.Fr a) :=
        mul_pos (by exact_mod_cast hr) (IntegralFrameAllCompare.vV_pos h0 ha)
      rw [← hi] at h3
      rw [hk] at h1
      exact h3.ne' h1
    have hp : (((maximalIdeal W).comap k).comap (algebraMap S.V (integralClosure S.V L))).IsPrime :=
      inferInstance
    rw [← (maximalIdeal.isMaximal S.V).eq_of_le hp.ne_top hle]
    infer_instance
  have hm := eq_maximalIdeal hmax
  change IsIntegral S.V (algebraMap W L w)
  by_cases hw : w = 0
  · subst hw; rw [map_zero]; exact isIntegral_zero
  have hw' : algebraMap W L w ≠ 0 := (map_ne_zero_iff _ hinj).2 hw
  rcases ValuationRing.isInteger_or_isInteger (integralClosure S.V L) (algebraMap W L w) with ⟨b, hb⟩ | ⟨b, hb⟩
  · rw [← hb]; exact b.2
  · have hb' : (b : L) = (algebraMap W L w)⁻¹ := hb
    have hu : IsUnit b := by
      by_contra hn
      have : b ∈ (maximalIdeal W).comap k := by rw [hm]; exact hn
      refine this (IsUnit.of_mul_eq_one w (hinj ?_))
      rw [map_mul, hk, hb', map_one, inv_mul_cancel₀ hw']
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have hc' : (b : L) * c = 1 := congrArg Subtype.val hc
    have : (c : L) = algebraMap W L w := by
      rw [hb', inv_mul_eq_one₀ hw'] at hc'
      exact hc'.symm
    rw [← this]; exact c.2

theorem exists_extension (S S' : CDVR) (φ : S.Fr →+* S'.Fr) (hφ : φ.Finite) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV S'.V (φ z) = (r : ℤ) * vV S.V z) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] (f : S.Fr →+* C) (h1 : ∀ a : S.V, ‖f (algebraMap S.V S.Fr a)‖ ≤ 1)
    (h2 : ∀ a ∈ maximalIdeal S.V, ‖f (algebraMap S.V S.Fr a)‖ < 1) :
    ∃ f' : S'.Fr →+* C, f'.comp φ = f ∧ (∀ a : S'.V, ‖f' (algebraMap S'.V S'.Fr a)‖ ≤ 1) ∧
      ∀ a ∈ maximalIdeal S'.V, ‖f' (algebraMap S'.V S'.Fr a)‖ < 1 := by
  obtain ⟨f', hf'⟩ : ∃ f' : S'.Fr →+* C, f'.comp φ = f := by
    letI : Algebra S.Fr S'.Fr := φ.toAlgebra
    letI : Algebra S.Fr C := f.toAlgebra
    have : FiniteDimensional S.Fr S'.Fr := hφ
    exact ⟨(IsAlgClosed.lift (R := S.Fr) (S := S'.Fr) (M := C)).toRingHom,
      RingHom.ext fun x => (IsAlgClosed.lift (R := S.Fr) (S := S'.Fr) (M := C)).commutes x⟩
  have hff : ∀ x, f' (φ x) = f x := fun x => congrArg (fun t : S.Fr →+* C => t x) hf'
  have hle : ∀ a : S'.V, ‖f' (algebraMap S'.V S'.Fr a)‖ ≤ 1 := fun a => by
    obtain ⟨p, hp, hpa⟩ := isIntegral_of_scale S φ hφ hr hi a
    let v : Valuation C NNReal := NormedField.valuation
    let g : S.V →+* v.integer := (f.comp (algebraMap S.V S.Fr)).codRestrict v.integer fun x => by
      change ‖f (algebraMap S.V S.Fr x)‖₊ ≤ 1
      exact_mod_cast h1 x
    have hI : IsIntegral v.integer (f' (algebraMap S'.V S'.Fr a)) := by
      refine ⟨p.map g, hp.map g, ?_⟩
      rw [Polynomial.eval₂_map]
      have := congrArg f' hpa
      rw [Polynomial.hom_eval₂, map_zero, ← RingHom.comp_assoc, hf'] at this
      exact this
    have : ‖f' (algebraMap S'.V S'.Fr a)‖₊ ≤ 1 := (Valuation.integer.integers v).mem_of_integral hI
    exact_mod_cast this
  refine ⟨f', hf', hle, fun a ha => ?_⟩
  by_cases h0 : a = 0
  · simp [h0]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  have hπm : π ∈ maximalIdeal S.V := hπ.not_isUnit
  have hπ0 : φ (algebraMap S.V S.Fr π) ≠ 0 :=
    (map_ne_zero φ).2 ((map_ne_zero_iff _ (IsFractionRing.injective S.V S.Fr)).2 hπ.ne_zero)
  have ha0 : algebraMap S'.V S'.Fr a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S'.V S'.Fr)).2 h0
  have hva := IntegralFrameAllCompare.vV_pos (K := S'.Fr) h0 ha
  have hn : 0 < vV S'.V (φ (algebraMap S.V S.Fr π)) := by
    rw [hi]; exact mul_pos (by exact_mod_cast hr) (IntegralFrameAllCompare.vV_pos hπ.ne_zero hπm)
  obtain ⟨n, hn'⟩ := Int.eq_ofNat_of_zero_le hn.le
  obtain ⟨b, hb⟩ := (IntegralFrameAllCompare.mem_range_iff (V := S'.V)
      ((algebraMap S'.V S'.Fr a) ^ (n : ℤ) * (φ (algebraMap S.V S.Fr π)) ^ (-1 : ℤ))).2 (by
    rw [vV_mul (zpow_ne_zero _ ha0) (zpow_ne_zero _ hπ0), IntegralFrameAllCompare.vV_zpow,
      IntegralFrameAllCompare.vV_zpow, hn']
    nlinarith)
  have he : (algebraMap S'.V S'.Fr a) ^ n = algebraMap S'.V S'.Fr b * φ (algebraMap S.V S.Fr π) := by
    rw [hb, zpow_neg_one, zpow_natCast, inv_mul_cancel_right₀ hπ0]
  have hlt : ‖f' (algebraMap S'.V S'.Fr a)‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, he, map_mul, norm_mul, hff]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hle b) (norm_nonneg _) (h2 π hπm)
  exact lt_of_pow_lt_pow_left₀ n zero_le_one (by rwa [one_pow])

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Formalism.L2.Pj.dualMap (g.comp f) = (Formalism.L2.Pj.dualMap g).comp (Formalism.L2.Pj.dualMap f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) {X : Scheme.{0}}
    {u : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber A) ⟶ X} {u' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber B) ⟶ X}
    (h : u' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap f) ≫ u) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap (g.comp f)) ≫ u =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap g) ≫ u' := by
  rw [h, ← Category.assoc, dualMap_comp]
  congr 1
  exact Spec.map_comp (CommRingCat.ofHom (Formalism.L2.Pj.dualMap f)) (CommRingCat.ofHom (Formalism.L2.Pj.dualMap g))

theorem baseChange_of_finite_extension {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c) (S S' : CDVR)
    (io : c.F →+* S.Fr) (φ : S.Fr →+* S'.Fr) (y : IntFr Xo c S io) (y' : IntFr Xo c S' (φ.comp io))
    (hφ : φ.Finite) {r : ℕ} (hr0 : 0 < r) (hr : ∀ z, vV S'.V (φ z) = (r : ℤ) * vV S.V z)
    (mx : letI := io.toAlgebra; letI := (φ.comp io).toAlgebra
      y'.1.x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ ≫ y.1.x)
    (mu : letI := io.toAlgebra; letI := (φ.comp io).toAlgebra
      ∀ τ i, y'.1.u τ i = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap φ) ≫ y.1.u τ i)
    (z : PointsOfFlagModel.Pt Tw .yy) (hl : LiesOverBaseChange la Tw S io y z) : LiesOverBaseChange la Tw S' (φ.comp io) y' z := by
  obtain ⟨h0, f, hf, h1, h2, hx, hu⟩ := hl
  obtain ⟨f', hf', h1', h2'⟩ := exists_extension S S' φ hφ hr0 hr f h1 h2
  subst hf'
  have e1 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (f'.comp φ) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ :=
    Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom f')
  refine ⟨h0, f', hf, h1', h2', ?_, fun τ i => (hu τ i).imp fun u' h => ⟨h.1, h.2.trans (dual_comp φ f' (mu τ i))⟩⟩
  exact hx.trans ((congrArg (· ≫ _) e1).trans ((Category.assoc _ _ _).trans
    (congrArg (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap f' ≫ ·) mx.symm)))

end GlobalTheory.LiesBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsConjLevelMapByLevelMoves
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ConjLevelMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_inv {S : Scheme.{0}} {t : SAB H S} (e : S ≅ S) (n : SABMap t t e.hom) :
    ∃ n' : SABMap t t e.inv, n.φ ≫ n'.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id t
  obtain ⟨i', hi'⟩ := LevelFibre.sab_cast e.inv_hom_id.symm i
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel n i'
  have h : n'.φ ≫ n.φ = 𝟙 _ := hn'.symm.trans (hi'.trans hi)
  have pn : IsPullback n.φ t.G.hom t.G.hom e.hom := n.cart.1
  have : IsIso n.φ := pn.isIso_fst_of_isIso
  refine ⟨n', ?_⟩
  rw [← cancel_mono n.φ, Category.assoc, h, Category.comp_id, Category.id_comp]

theorem conj_sec {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ≅ S₂}
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂.hom)
    (hr : ρ₂.hom ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {σ σ' : 𝟙_ (Over S₂) ⟶ t₂.G} {τ τ' : 𝟙_ (Over S) ⟶ t.G} (k : ℕ)
    (h₂ : σ'.left ≫ ν₂.φ = ρ₂.hom ≫ σ.left) (hm : (σ' ^ k).left ≫ m.φ = r ≫ τ'.left)
    (h : τ'.left ≫ ν.φ = ρ ≫ τ.left) : (σ ^ k).left ≫ m'.φ = r' ≫ τ.left := by
  have e := OverMove.pow_left_comp ν₂ h₂ k
  have a₁ : ρ₂.hom ≫ (σ ^ k).left ≫ m'.φ = ((σ' ^ k).left ≫ m.φ) ≫ ν.φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m'.φ) e.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((σ' ^ k).left ≫ ·) hφ).trans (Category.assoc _ _ _).symm)))
  have a₂ : (r ≫ τ'.left) ≫ ν.φ = ρ₂.hom ≫ r' ≫ τ.left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ τ.left) hr.symm).trans (Category.assoc _ _ _))))
  exact (cancel_epi ρ₂.hom).1 (a₁.trans ((congrArg (· ≫ ν.φ) hm).trans a₂))

end ConjLevelMap


open ConjLevelMap in
theorem exists_conj_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  intro E _ _ _ H Dw l Xo c n d hE ρ ν ρ₂ ν₂ gM gA gM₂ gA₂ h h₂ hM hA
  obtain ⟨i, hi⟩ := exists_inv ρ₂ ν₂
  obtain ⟨q, hq⟩ := ObjMaps.exists_sab_comp ν d.m
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_comp q i
  have hr : ρ₂.hom ≫ ρ₂.inv ≫ d.r ≫ ρ = d.r ≫ ρ := ρ₂.hom_inv_id_assoc _
  have hφ : ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ := by
    rw [hm', hq, ← Category.assoc, hi, Category.id_comp]
  have eM : ∀ a, Xo.univ.eta (gM₂ a) = Xo.univ.eta (gM a) := fun a => by
    rw [← sub_add_cancel (gM₂ a) (gM a), Xo.univ.eta_add, Xo.univ.eta_ker _ (hM a), _root_.one_mul]
  have eA : ∀ a, Xo.univ.etaA (gA₂ a) = Xo.univ.etaA (gA a) := fun a => by
    obtain ⟨x, hx⟩ := hA a
    rw [← sub_add_cancel (gA₂ a) (gA a), Xo.univ.etaA_add, hx, Xo.univ.etaA_ker, _root_.one_mul]
  refine ⟨_, m', hr, hφ, fun a => ?_, fun a => ?_⟩
  · exact conj_sec d.m m' ν ν₂ hr hφ d.pd (h₂.2.1 a) (hE.1 (gM₂ a)) (by rw [eM]; exact h.2.1 a)
  · exact conj_sec d.m m' ν ν₂ hr hφ (d.l₂.A / l.A) (h₂.2.2 a) (hE.2 (gA₂ a)) (by rw [eA]; exact h.2.2 a)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMultiplicativeChartAtSplitPrime
section
noncomputable section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.SplitChart

open ChordLaw

section Algebra

variable {k : Type} [CommRing k] {σ : Type}

theorem law_two {U : k⟦X⟧} (hU : constantCoeff U = 0) {F : MvPowerSeries (Fin 2) k}
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U] : Fin 2 → MvPowerSeries (Fin 2) k) F =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U)
    {a b : MvPowerSeries σ k} (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst (![PowerSeries.subst a U, PowerSeries.subst b U] : Fin 2 → MvPowerSeries σ k) F =
      PowerSeries.subst (a + b) U := by
  have hab := hasSubst_two ha hb
  have c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) U) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU
  have h := congrArg (MvPowerSeries.subst ![a, b]) H
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_two (c0 0) (c0 1)) hab, subst_psubst hab (by simp),
    MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at h
  refine Eq.trans ?_ h
  congr 1
  funext i
  fin_cases i
  · simp [subst_psubst hab (MvPowerSeries.constantCoeff_X 0), MvPowerSeries.subst_X hab]
  · simp [subst_psubst hab (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X hab]

theorem constantCoeff_mulN {R : Type} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    constantCoeff (JetMomFound.mulN F n) = 0 := by
  induction n with
  | zero => simp [JetMomFound.mulN]
  | succ n ih =>
    refine MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_two ih constantCoeff_X) ?_ F.zero_constantCoeff
    intro i
    fin_cases i
    · exact ih
    · exact constantCoeff_X

theorem map_mulN {R : Type} [CommRing R] (φ : R →+* k) (F : FormalGroup R) {U ℓ : k⟦X⟧}
    (hU : constantCoeff U = 0) (hℓ : constantCoeff ℓ = 0) (hUℓ : PowerSeries.subst ℓ U = (X : k⟦X⟧))
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U] : Fin 2 → MvPowerSeries (Fin 2) k)
      (MvPowerSeries.map φ F.toPowerSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U) (n : ℕ) :
    PowerSeries.map φ (JetMomFound.mulN F n) = PowerSeries.subst (C (n : k) * ℓ) U := by
  induction n with
  | zero =>
    simp only [JetMomFound.mulN, map_zero, Nat.cast_zero, zero_mul]
    exact (PowerSeries.subst_zero_of_constantCoeff_zero hU).symm
  | succ n ih =>
    have h := law_two hU H (a := (C (n : k) * ℓ : k⟦X⟧)) (b := ℓ)
      (show constantCoeff (C (n : k) * ℓ) = 0 by rw [map_mul, hℓ, mul_zero]) hℓ
    have e : (C ((n + 1 : ℕ) : k) * ℓ : k⟦X⟧) = C (n : k) * ℓ + ℓ := by
      rw [Nat.cast_succ, map_add (f := _), map_one]; ring
    rw [e]
    refine Eq.trans ?_ h
    rw [← ih, hUℓ]
    refine (MvPowerSeries.map_subst (hasSubst_two (constantCoeff_mulN F n) constantCoeff_X) _).trans ?_
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact PowerSeries.map_X φ

theorem deriv_of_mul {g : k⟦X⟧}
    (H : PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) g +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g +
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) g *
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g) :
    derivative g = C (coeff 1 g) * (1 + g) := by
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have HS : PowerSeries.HasSubst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h := congrArg (MvPowerSeries.pderiv (R := k) 1) H
  simp only [map_add (f := _), Derivation.leibniz, smul_eq_mul, GlobalTheory.FormalCalc.pderiv_powerSeries_subst (HX _),
    GlobalTheory.FormalCalc.pderiv_powerSeries_subst HS] at h
  have p0 : MvPowerSeries.pderiv (R := k) 1 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) = 0 := by
    simp [MvPowerSeries.pderiv_X_of_ne]
  have p1 : MvPowerSeries.pderiv (R := k) 1 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = 1 := by simp
  simp only [p0, p1, zero_add, mul_one, mul_zero, add_zero] at h
  have ha : MvPowerSeries.HasSubst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k) :=
    hasSubst_two constantCoeff_X (map_zero _)
  have h2 := congrArg (MvPowerSeries.subst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k)) h
  rw [subst_psubst ha (by simp), MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
    MvPowerSeries.subst_mul ha, subst_psubst ha (MvPowerSeries.constantCoeff_X 0),
    subst_psubst ha (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at h2
  have e : PowerSeries.subst (0 : MvPowerSeries Unit k) (derivative g) = (C (coeff 1 g) : k⟦X⟧) := by
    rw [PowerSeries.subst_zero_eq_C_constantCoeff, MvPowerSeries.map_C, ← coeff_zero_eq_constantCoeff_apply,
      coeff_derivative]
    simp [PowerSeries.C]
  rw [X_subst, X_subst, e] at h2
  rw [h2]
  ring

theorem subst_log_eq_X [IsAddTorsionFree k] {g L : k⟦X⟧} {γ ω : k} (hγ : γ * ω = 1) (hg : constantCoeff g = 0)
    (hd : derivative g = C γ * (1 + g)) (hL0 : constantCoeff L = 0) (hL : (1 + X) * derivative L = 1) :
    PowerSeries.subst (C ω * L) g = (X : k⟦X⟧) := by
  have h0 : constantCoeff (C ω * L) = 0 := by rw [map_mul, hL0, mul_zero]
  have Hs := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hh0 : constantCoeff (PowerSeries.subst (C ω * L) g : k⟦X⟧) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h0 _ hg
  have hD : derivative (PowerSeries.subst (C ω * L) g : k⟦X⟧) =
      C γ * (1 + PowerSeries.subst (C ω * L) g) * (C ω * derivative L) := by
    rw [PowerSeries.derivative_subst Hs, hd, PowerSeries.subst_mul Hs, PowerSeries.subst_add Hs,
      PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom Hs, map_one, Derivation.leibniz, derivative_C]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rfl
  generalize (PowerSeries.subst (C ω * L) g : k⟦X⟧) = h at hh0 hD
  have hC : (C γ : k⟦X⟧) * C ω = 1 := by rw [← map_mul, hγ, map_one]
  set r := derivative L with hr
  have hr' := congrArg (derivative (R := k)) hL
  rw [Derivation.leibniz, map_add (f := _), derivative_X, Derivation.map_one_eq_zero] at hr'
  simp only [smul_eq_mul] at hr'
  have hr0 : constantCoeff r = 1 := by simpa using congrArg constantCoeff hL
  have key : (1 + h) * r = 1 := by
    let _ : HasUniqueDiv k := IsAddTorsionFree.hasUniqueDiv
    apply derivative.ext
    · rw [Derivation.leibniz, map_add (f := _), Derivation.map_one_eq_zero, hD]
      simp only [smul_eq_mul]
      linear_combination (1 + h) * r * hr' - (1 + h) * derivative r * hL + (1 + h) * r ^ 2 * hC
    · simp [hh0, hr0]
  linear_combination (1 + X) * key - (1 + h) * hL

theorem exists_scale {R K : Type} [CommRing R] [Field K] [CharZero K] (φ : R →+* K) (F : FormalGroup R)
    {U ℓ L : K⟦X⟧} (hU : constantCoeff U = 0) (hℓ : constantCoeff ℓ = 0)
    (hUℓ : PowerSeries.subst ℓ U = (X : K⟦X⟧))
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)
      (MvPowerSeries.map φ F.toPowerSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U)
    {f : R⟦X⟧} (hf : JetMomFound.IsIsoGm F f) (hL0 : constantCoeff L = 0) (hL : (1 + X) * derivative L = 1) :
    ∃ (ω : K) (e : R⟦X⟧), IsUnit (coeff 1 e) ∧ PowerSeries.subst (C ω * L) U = PowerSeries.map φ e := by
  obtain ⟨f0, f1, hf⟩ := hf
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ f0
  have cU : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) U) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU
  have ha := hasSubst_two (c0 0) (c0 1)
  have hb := hasSubst_two (cU 0) (cU 1)
  rw [FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
    MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha] at hf
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf
  have h1 := congrArg (MvPowerSeries.map φ) hf
  rw [map_add (f := _), map_add (f := _), map_mul,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.map_subst (HX 0), PowerSeries.map_subst (HX 1), MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
  set f' := PowerSeries.map φ f with hf'
  have f0' : constantCoeff f' = 0 := by
    rw [hf', ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, f0, map_zero]
  have h2 := congrArg (MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)) h1
  rw [subst_psubst hb (by rw [MvPowerSeries.constantCoeff_map, F.zero_constantCoeff, map_zero]), H,
    MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_mul hb,
    subst_psubst hb (MvPowerSeries.constantCoeff_X 0), subst_psubst hb (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [← psubst_psubst (by simp) hU, ← psubst_psubst (MvPowerSeries.constantCoeff_X 0) hU,
    ← psubst_psubst (MvPowerSeries.constantCoeff_X 1) hU] at h2
  have hd := deriv_of_mul h2
  have g0 : constantCoeff (PowerSeries.subst U f' : K⟦X⟧) = 0 := PowerSeries.constantCoeff_subst_eq_zero hU _ f0'
  have hγ : coeff 1 (PowerSeries.subst U f' : K⟦X⟧) ≠ 0 := by
    intro hz
    have hg : (PowerSeries.subst U f' : K⟦X⟧) = 0 := by
      apply derivative.ext
      · rw [hd, hz]; simp
      · rw [g0, map_zero]
    have h3 := psubst_psubst (σ := Unit) hℓ hU f'
    rw [hg, hUℓ, X_subst, ← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hℓ),
      map_zero] at h3
    have h4 := f1.map φ
    rw [← coeff_map, ← hf', ← h3, map_zero] at h4
    exact not_isUnit_zero h4
  have h5 := subst_log_eq_X (mul_inv_cancel₀ hγ) g0 hd hL0 hL
  set ω := (coeff 1 (PowerSeries.subst U f' : K⟦X⟧))⁻¹
  have h0 : constantCoeff (C ω * L) = 0 := by rw [map_mul, hL0, mul_zero]
  rw [psubst_psubst (σ := Unit) h0 hU] at h5
  have u0 : constantCoeff (PowerSeries.subst (C ω * L) U : K⟦X⟧) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h0 _ hU
  refine ⟨ω, f.substInvOfIsUnit f1, by rw [coeff_one_substInvOfIsUnit]; exact Units.isUnit _, ?_⟩
  have h6 := congrArg (MvPowerSeries.map φ) (subst_substInvOfIsUnit_left f f0 f1)
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' f0)] at h6
  have h7 : PowerSeries.subst f' (PowerSeries.map φ (f.substInvOfIsUnit f1)) = (X : K⟦X⟧) :=
    h6.trans (PowerSeries.map_X φ)
  have h8 := psubst_psubst (σ := Unit) u0 f0' (PowerSeries.map φ (f.substInvOfIsUnit f1))
  rw [h7, h5, X_subst, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' u0)] at h8
  exact h8

end Algebra

theorem exists_mChart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ ω : ℂ_[q], M.MChart ω := by
  intro d q _ M hd hd16 hsp hL hOk b₁ b₂ b₃ b₄ b₆
  obtain ⟨F, hfin, H⟩ := exists_formalGroup_add q M hOk b₁ b₂ b₃ b₄ b₆
  obtain ⟨ℓ, hℓ, hUℓ, h1, h2⟩ := height_one_of_split d q M F hd hd16 hsp hL hOk H
  have hU : constantCoeff (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [Mdl.u]
  rw [← map_mulN (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H q] at h1 h2
  obtain ⟨f, hf⟩ := GlobalTheory.ConvSer.HeightOneInt.htOneIsGm q F hfin ⟨h1, h2⟩
  have hL0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by simp [logS]
  obtain ⟨ω, e, he1, he⟩ := exists_scale (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H hf hL0
    (MulSeries.mulS_laws q).2.2.2.2.1
  have hO : ∀ x : 𝓞_ℂ_[q], ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖ ≤ 1 := fun x => by
    have hx := (Valuation.mem_valuationSubring_iff _ _).1 x.2
    rw [PadicComplex.norm_eq_norm]
    exact Valued.toNormedField.norm_le_one_iff.2 hx
  refine ⟨ω, hOk, by rw [map_mul, hL0, mul_zero], fun n => ?_, ?_⟩
  · rw [hat, he, coeff_map]; exact hO _
  · rw [hat, he, coeff_map]
    obtain ⟨v, hv⟩ := he1.exists_right_inv
    have h3 := congrArg (fun x => ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖) hv
    simp only [map_mul, norm_mul, map_one, norm_one] at h3
    have h4 := hO (coeff 1 e)
    have h5 := hO v
    nlinarith [norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] (coeff 1 e)), norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] v)]

end GlobalTheory.MomOne.SplitChart
end
end

