module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAppellHumbertUniformisationOfKeyDatumIso
section
noncomputable section

section Push
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa GlobalTheory.KeyEq GlobalTheory.KeyIsoNormal

namespace GlobalTheory.KeyTransport

theorem eq_comp_of_isLieComb {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] (ψ : A' ⟶ A)
    (hm : ∀ a b : epsR ℂ ⟶ A', (a * b) ≫ ψ = (a ≫ ψ) * (b ≫ ψ)) {n : ℕ} {c : Fin n → ℂ}
    {v' : Fin n → (epsR ℂ ⟶ A')} {v : Fin n → (epsR ℂ ⟶ A)} (hv : ∀ i, (v i).left = (v' i).left ≫ ψ.left)
    {w' : epsR ℂ ⟶ A'} {w : epsR ℂ ⟶ A} (hw' : IsLieComb c v' w') (hw : IsLieComb c v w) : w = w' ≫ ψ := by
  obtain ⟨a', ha', rfl⟩ := hw'
  obtain ⟨a, ha, rfl⟩ := hw
  let m : (epsR ℂ ⟶ A') →* (epsR ℂ ⟶ A) := MonoidHom.mk' (fun p => p ≫ ψ) hm
  have e : a = m ∘ a' := by
    funext i
    ext
    change _ = (a' i).left ≫ ψ.left
    rw [ha, ha', hv, Category.assoc]
  rw [e, ← List.map_ofFn, ← map_list_prod]
  rfl

theorem eq_comp_of_isLieComb_cast {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] (ψ : A' ⟶ A)
    (hm : ∀ a b : epsR ℂ ⟶ A', (a * b) ≫ ψ = (a ≫ ψ) * (b ≫ ψ)) {n n' : ℕ} (h : n = n') {c : Fin n' → ℂ}
    {v' : Fin n' → (epsR ℂ ⟶ A')} {v : Fin n → (epsR ℂ ⟶ A)}
    (hv : ∀ i, (v i).left = (v' (i.cast h)).left ≫ ψ.left)
    {w' : epsR ℂ ⟶ A'} {w : epsR ℂ ⟶ A} (hw' : IsLieComb c v' w') (hw : IsLieComb (fun i => c (i.cast h)) v w) :
    w = w' ≫ ψ := by
  subst h
  exact eq_comp_of_isLieComb ψ hm hv hw' hw

theorem exists_push_key {x x' : KeyIn ℂ} (H : KeyPB x' x (RingHom.id ℂ)) {g : ℕ} (u' : HolUnif x'.P.A x'.P.L g) :
    ∃ u : HolUnif x.P.A x.P.L g, u.Λ = u'.Λ ∧ (∀ Hm χ', u'.IsAH Hm χ' → ∃ χ, u.IsAH Hm χ) ∧
      (u'.IsRig x'.rig → u.IsRig x.rig) ∧ (∀ θ, u'.IsFn x'.th θ → u.IsFn x.th θ) ∧
      ∀ (h : x.P.g = x'.P.g) (c : Fin x'.P.g → ℂ) (w' : epsR ℂ ⟶ x'.P.A) (w : epsR ℂ ⟶ x.P.A) (W : Fin g → ℂ),
        IsLieComb c x'.v w' → IsLieComb (fun i => c (i.cast h)) x.v w → u'.IsDiff W w' → u.IsDiff W w := by
  obtain ⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hFid : spMap F = 𝟙 _ := by
    rw [KeyCancel.dualNumber_ringHom_ext (F := F) (G := RingHom.id _) hF hFe]
    exact Spec.map_id _
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap (RingHom.id ℂ)) _
    (rigPull_le φ (spMap (RingHom.id ℂ)) he x.P.L) (fun _ => rfl)).1 hr
  rw [hid] at r he
  rw [Category.id_comp] at he
  have hc' := hc.congr hid rfl
  let ψ : x'.P.A ⟶ x.P.A := Over.homMk φ (hc'.1.w.trans (Category.comp_id _))
  obtain ⟨u, hex, hΛ, hfr⟩ := exists_push x.P.isLB x'.P.isLB ψ hc' w ((isGen_iff w).1 hw) u'
  replace hex : ∀ z, (u.ex z).left = (u'.ex z).left ≫ φ := hex
  replace hfr : ∀ j k z, φ ((u'.ex z).left pt) ∈ x.P.L.U j → (u'.ex z).left pt ∈ x'.P.L.U k →
    u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := hfr
  refine ⟨u, hΛ, fun Hm χ' hA => ⟨fun l => χ' ⟨l.1, hΛ ▸ l.2⟩, hA.1, hA.2.1, fun l => hA.2.2.1 _, fun l j z hz => ?_⟩,
    fun h₄ j hj => ?_, fun θ h₅ j z hz => ?_, fun h c q' q W hq' hq h₆ U hU f => ?_⟩
  · rw [hex] at hz
    have hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB ((u'.ex z).left pt)
    have hl : u'.ex (z + l.1) = u'.ex z := by
      rw [u'.ex_add, (u'.ker l.1).2 (hΛ ▸ l.2), _root_.mul_one]
    have e := hA.2.2.2 ⟨l.1, hΛ ▸ l.2⟩ k z ((top_le_preimage_iff_mem _ _).2 hk)
    rw [hfr j k z hj hk, hfr j k (z + l.1) (hl ▸ hj) (hl ▸ hk), hl, e]
    ring
  · have h0 : (u'.ex 0).left = eSec x'.P.A := by
      rw [(u'.ker 0).2 u'.Λ.zero_mem]
      change (toUnit _ ≫ η[x'.P.A]).left = η[x'.P.A].left
      rw [toUnit_unit, Category.id_comp]
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB (eSec x'.P.A pt)
    have hj' : φ (eSec x'.P.A pt) ∈ x.P.L.U (j PUnit.unit) := by
      have := mem_pull.1 (hj (Set.mem_univ pt))
      rw [← he] at this
      exact this
    have hk' : (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) pt ∈ (x'.P.L.pull (eSec x'.P.A)).U (fun _ => k) := mem_pull.2 hk
    have e := congrArg Units.val (r _ (𝟙 (Sp ℂ)) pt j (fun _ => k) (fun _ => hj') (fun _ => hk))
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, Units.val_mul] at e
    rw [hfr _ k 0 (h0 ▸ hj') (h0 ▸ hk), h0, h₄ (fun _ => k) ((top_le_preimage_iff_mem (𝟙 _) _).2 hk')]
    apply toStalk.injective
    rw [map_mul]
    exact (congrArg₂ (· * ·) (gw_eq_toStalk w _ hj' hk).symm (gm_eq_toStalk _ _ hk' _).symm).trans
      (e.symm.trans (gm_eq_toStalk _ _ (hj (Set.mem_univ pt)) _))
  · rw [hex] at hz ⊢
    have hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB ((u'.ex z).left pt)
    have e := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs _ (u'.ex z).left pt j k hj hk
    rw [gs_eq_toStalk _ _ hj, gs_eq_toStalk _ _ hk, gw_eq_toStalk w _ hj hk, ← map_mul] at e
    rw [toStalk.injective e, hfr j k z hj hk, h₅ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring
  · have e₀ : q = q' ≫ ψ := eq_comp_of_isLieComb_cast ψ (fun a b => comp_mul_of_isGrpPullback ψ hc' a b) h
      (fun i => by
        change _ = _ ≫ φ
        rw [hv, hFid, Category.id_comp]
        rfl) hq' hq
    have e : q.left = q'.left ≫ φ := by
      rw [e₀]
      rfl
    have := h₆ (φ ⁻¹ᵁ U) (by rw [e] at hU; exact hU) ((φ.app U).hom f)
    simp only [valAt'_comp, ← hex] at this
    rw [← this]
    congr 2
    generalize q.left = p at e hU
    subst e
    rw [Scheme.Hom.comp_appLE]
    rfl

end GlobalTheory.KeyTransport
end Push

section Main
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyTransport

theorem uniformisation_transport : ∀ (x x' : KeyIn ℂ), KeyPB x' x (RingHom.id ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (RingHom.id ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (RingHom.id ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (RingHom.id ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (RingHom.id ℂ) (W i)) w' := by
  intro x x' H hg g u Hm χ θ Fd ⟨h₁, h₂, h₃, h₄⟩
  have H' : KeyPB x x' (RingHom.id ℂ) :=
    KeyCancel.keyPB_cancel ℂ ℂ ℂ x x' x (RingHom.id ℂ) (RingHom.id ℂ) H (keyPB_id ℂ x)
  have hH : Hm.map (RingHom.id ℂ) = Hm := rfl
  obtain ⟨u', hΛ, hA, hR, hF, hD⟩ := exists_push_key H' u
  obtain ⟨χ', hχ⟩ := hA Hm χ h₁
  exact ⟨u', χ', θ, Fd, hχ, hR h₂, hF θ h₃, hΛ ▸ h₄, rfl, fun cf w w' W hw hw' hW => hD hg cf w w' W hw hw' hW⟩

end GlobalTheory.KeyTransport
end Main
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

private lemma mem_range_algebraMap_iff_valV_le_one (T : CDVR) (x : T.Fr) :
    x ∈ Set.range (algebraMap T.V T.Fr) ↔ valV T.V x ≤ 1 := by
  unfold valV
  constructor
  · rintro ⟨r, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one r
  · intro h
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
    exact ⟨a, ha⟩

private lemma withZero_le_one_iff_log_nonpos {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : x ≤ 1 ↔ WithZero.log x ≤ 0 := by
  conv_lhs => rw [← WithZero.exp_log hx, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp

theorem exists_cdvr_completion_integral_iff :
    ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)),
      ∃ (T : CDVR) (iK : K →+* T.Fr), T.FinRes ∧
        ∀ y : K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation K y ≤ 1 := by
  intro K _ _ p

  obtain ⟨T, k, e, hO, hfin⟩ := locFld K K (RingHom.id K) p
  unfold OverLa vV vLa at hO
  obtain ⟨he, hv⟩ := hO
  simp only [RingHom.comp_id] at hv
  refine ⟨T, k, hfin, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero]
    exact ⟨fun _ => zero_le, fun _ => ⟨0, map_zero _⟩⟩
  · have hky : k y ≠ 0 := (map_ne_zero k).2 hy
    have ha : valV T.V (k y) ≠ 0 := by
      unfold valV
      exact (Valuation.ne_zero_iff _).2 hky
    have hb : p.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy

    rw [mem_range_algebraMap_iff_valV_le_one, withZero_le_one_iff_log_nonpos ha, withZero_le_one_iff_log_nonpos hb]
    have h := hv y
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    constructor <;> intro h' <;> nlinarith

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoom
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory

theorem room_neg_log_epStar (f d L M k0 S : ℝ) (hf : 1 ≤ f) (hd : 1 ≤ d) (hL : 0 ≤ L)
    (hM : 0 < M) (hk : 0 < k0) (hS : 1 ≤ S)
    (h : Real.log (M * k0) ≤ 19 * L + 3 + Real.log d) :
    0 < epStar M f S k0 ∧ epStar M f S k0 ≤ 1 ∧
      -Real.log (epStar M f S k0) ≤ 19 * L + 6 + Real.log d + f + Real.log S := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hfS : 1 ≤ f * S := one_le_mul_of_one_le_of_one_le hf hS
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hlS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hpi := Real.pi_gt_three
  have hD : 0 < M * (f * S + 2) * k0 * Real.log 2 := by positivity
  unfold epStar
  refine ⟨lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  rcases min_choice 1 (Real.pi / (M * (f * S + 2) * k0 * Real.log 2)) with h1 | h1 <;> rw [h1]
  · rw [Real.log_one]; linarith
  · have hMk : 0 < M * k0 := by positivity
    have e : M * (f * S + 2) * k0 * Real.log 2 = (M * k0) * ((f * S + 2) * Real.log 2) := by ring
    rw [Real.log_div (by positivity) hD.ne', e, Real.log_mul hMk.ne' (by positivity)]
    have h2 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
    have h3 : Real.log ((f * S + 2) * Real.log 2) ≤ Real.log (3 * f * S) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h6 : Real.log (3 * f * S) = Real.log 3 + Real.log f + Real.log S := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    have h5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by positivity)
    linarith

theorem room_log_radius (f r : ℕ) (d e S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (he : 0 < e) (hS : 1 ≤ S) :
    0 < 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5)) =
      Real.log (1600 / 3) + Real.log r + (1 / 2) * Real.log f + (1 / 2) * Real.log S
        + 3 * Real.log ((f : ℝ) * r) + Real.log d - (1 / 2) * Real.log e := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hS' : (0 : ℝ) < S := by linarith
  have hd' : (0 : ℝ) < d := by linarith
  have h1 : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have h2 : 0 < Real.sqrt f := Real.sqrt_pos.2 hf'
  have h3 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr'
  have h4 : 0 < Real.sqrt (S * r) := Real.sqrt_pos.2 (by positivity)
  have E : 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) =
      1600 / 3 * Real.sqrt r * Real.sqrt f * Real.sqrt (S * r) * ((f : ℝ) * r) ^ 3 * d / Real.sqrt e := by
    unfold ReciprocityTheory.MultiplicativeHeights.approxR d5mu frameRadius
    field_simp
    norm_num
  rw [E]
  refine ⟨by positivity, ?_⟩
  rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by positivity) hd'.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) h4.ne',
    Real.log_mul (by positivity) h2.ne', Real.log_mul (by positivity) h3.ne',
    Real.log_pow, Real.log_sqrt he.le, Real.log_sqrt hf'.le, Real.log_sqrt hr'.le,
    Real.log_sqrt (by positivity), Real.log_mul hS'.ne' hr'.ne']
  push_cast
  ring

theorem room_of_constants : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (f r p0 : ℕ) (d L Om M k0 S : ℝ), 1 ≤ f → 1 ≤ r → p0 ≤ r → 1 ≤ d → 0 ≤ L → 0 < M → 0 < k0 → 1 ≤ S → Real.log (M * k0) ≤ 19 * L + 3 + Real.log d → 1 ≤ frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5) ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ S → ∀ C A : ℝ, C0 ≤ C → 2 ≤ A → (Formalism.L2.LamCM.pDeg Om + (1 / 2) * Real.log (frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5))) * (s + t) + s * Real.log ((r : ℝ) * frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5)) ≤ C * ((f : ℝ) * r + L + Real.log d + |Om|) ^ A * (1 + Real.log S) * S := by
  refine ⟨3000, by norm_num, ?_⟩
  intro f r p0 d L Om M k0 S hf hr hp hd hL hM hk hS h
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hp' : (p0 : ℝ) ≤ r := by exact_mod_cast hp
  obtain ⟨he0, he1, he2⟩ := room_neg_log_epStar f d L M k0 S hf' hd hL hM hk hS h
  obtain ⟨hX0, hX⟩ := room_log_radius f r d _ S hf hr hd he0 hS
  unfold frameBasisRadius
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt (epStar M f S k0) / Real.sqrt f))
    (3 * frameRadius S r / 5) with hXdef
  clear_value X
  have hle : Real.log (epStar M f S k0) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (f : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have hfn : (f : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_right (by linarith) hr'
  have hrn : (r : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_left (by linarith) hf'
  have a1 : 0 ≤ Real.log d := Real.log_nonneg hd
  have a2 : 0 ≤ Real.log S := Real.log_nonneg hS
  have a3 : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((f : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have b3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by linarith)
  have b4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < r by linarith)
  have b5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (f : ℝ) * r by linarith)
  have b6 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1600 / 3 by norm_num)
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  have hX1' : 1 ≤ X := by
    by_contra hc
    have := Real.log_neg hX0 (not_le.1 hc)
    linarith
  refine ⟨one_le_pow₀ hX1', ?_⟩
  intro s t hs ht hst C A hC hA
  have hOm := abs_nonneg Om
  set Z : ℝ := (f : ℝ) * r + L + Real.log d + |Om| with hZ
  have hZn : (f : ℝ) * r ≤ Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hXZ : Real.log X ≤ 600 * Z + Real.log S := by rw [hX]; linarith
  have hXZ' : Real.log X ≤ 600 * (Z * (1 + Real.log S)) := by
    have : Real.log S ≤ Z * Real.log S := le_mul_of_one_le_left a2 hZ1
    linarith
  have hpd : Formalism.L2.LamCM.pDeg Om ≤ Z := by unfold Formalism.L2.LamCM.pDeg; linarith
  have hlog : Real.log (X ^ (2 * p0 + 1)) ≤ 1800 * (Z ^ 2 * (1 + Real.log S)) := by
    rw [Real.log_pow]
    push_cast
    calc (2 * (p0 : ℝ) + 1) * Real.log X ≤ (3 * Z) * (600 * (Z * (1 + Real.log S))) :=
          mul_le_mul (by linarith) hXZ' hX1 (by linarith)
      _ = _ := by ring
  have hlog0 : 0 ≤ Real.log (X ^ (2 * p0 + 1)) := Real.log_nonneg (one_le_pow₀ hX1')
  rw [Real.log_mul (by positivity) (by positivity)]
  have hZW : Z ≤ Z ^ 2 * (1 + Real.log S) :=
    (le_self_pow₀ hZ1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hZA : Z ^ 2 ≤ Z ^ A := by
    have := Real.rpow_le_rpow_of_exponent_le hZ1 hA
    rwa [Real.rpow_two] at this
  set W := Z ^ 2 * (1 + Real.log S) with hW
  set Y := Real.log (X ^ (2 * p0 + 1)) with hY
  have hW0 : 0 ≤ W := by linarith
  have c1 : (Formalism.L2.LamCM.pDeg Om + 1 / 2 * Y) * (s + t) ≤ (901 * W) * S :=
    mul_le_mul (by linarith) hst (by linarith) (by linarith)
  have c2 : s * (Real.log r + Y) ≤ S * (1801 * W) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have c3 : 3000 * W ≤ C * Z ^ A * (1 + Real.log S) := by
    have : 3000 * Z ^ 2 ≤ C * Z ^ A := mul_le_mul hC hZA (by positivity) (by linarith)
    calc 3000 * W = (3000 * Z ^ 2) * (1 + Real.log S) := by rw [hW]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this (by linarith)
  have c4 : 3000 * W * S ≤ C * Z ^ A * (1 + Real.log S) * S :=
    mul_le_mul_of_nonneg_right c3 (by linarith)
  have c5 : 0 ≤ W * S := mul_nonneg hW0 (by linarith)
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDetIdealLocalGenFullLattice
section
open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

section

variable {K : Type} [Field K] [NumberField K]

theorem det_of_smul_rows {n : ℕ} (s : Fin n → 𝓞 K) (x : Fin n → Fin n → K) :
    (Matrix.of fun i => s i • x i).det = (∏ i, s i) • (Matrix.of x).det := by
  have h : (Matrix.of fun i => s i • x i) =
      Matrix.of fun i j => algebraMap (𝓞 K) K (s i) * (Matrix.of x) i j := by
    ext i j
    simp [Algebra.smul_def]
  rw [h, Matrix.det_mul_column, Algebra.smul_def, map_prod]


omit [NumberField K] in
theorem prod_notMem_asIdeal {n : ℕ} (p : HeightOneSpectrum (𝓞 K)) (s : Fin n → 𝓞 K)
    (hs : ∀ i, s i ∉ p.asIdeal) : ∏ i, s i ∉ p.asIdeal := by
  haveI := p.isPrime
  exact prod_mem (S := p.asIdeal.primeCompl) fun i _ => hs i

theorem valuation_smul_of_notMem (p : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ p.asIdeal) (c : K) :
    p.valuation K (s • c) = p.valuation K c := by
  have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
    refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
    exact (p.valuation_lt_one_iff_mem s).1 hlt
  rw [Algebra.smul_def, map_mul, h1, one_mul]

theorem valuation_smul_le (p : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (c : K) :
    p.valuation K (s • c) ≤ p.valuation K c := by
  rw [Algebra.smul_def, map_mul]
  exact mul_le_of_le_one_left' (p.valuation_le_one s)

end

theorem exists_detIdeal_isLocGen : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → Submodule.span K (Λ : Set (Fin n → K)) = ⊤ →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) K),
        (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ Λ) →
        (∀ c ∈ Λ, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i)) →
        IsLocGen p M.det I := by
  intro K _ _ n Λ hfg hspan
  let L : MLat K n := MLat.mk Λ (fun _ => 0)
  have hcoe : (L.detIdeal : Submodule (𝓞 K) K) = L.detSub :=
    A2.detIdeal_coe L (A2.detSub_isFractional L hfg)
  have hmem : ∀ y : K, y ∈ L.detIdeal ↔ y ∈ L.detSub := fun y => by
    rw [← hcoe]; rfl
  have hI : L.detIdeal ≠ 0 := by
    obtain ⟨x, hx, hd⟩ := A2.exists_det_ne Λ hspan
    intro h0
    have h := (hmem _).2 (A2.det_mem L x hx)
    rw [h0] at h
    exact hd ((FractionalIdeal.mem_zero_iff _).1 h)
  refine ⟨L.detIdeal, hI, fun p M h1 h2 => ?_⟩
  refine (isLocGen_iff_valuation_eq p _ _).2 (le_antisymm ?_ ?_)
  · choose s hs hsM using h1
    refine (valuation_le_iff_exists_smul_mem p hI _).2 ⟨∏ i, s i, prod_notMem_asIdeal p s hs, ?_⟩
    have h := A2.det_mem L (fun i => s i • M i) hsM
    rw [det_of_smul_rows s (fun i => M i)] at h
    exact (hmem _).2 h
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    rw [← hv]
    have hy' := (hmem y).1 hy
    clear hv hy
    induction hy' using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, hx, rfl⟩ := hd
      choose s hs hsx using fun i => h2 (x i) (hx i)
      let L' : MLat K n := MLat.mk (Submodule.span (𝓞 K) (Set.range fun i => M i)) (fun _ => 0)
      have h := A2.det_mem L' (fun i => s i • x i) hsx
      rw [A2.detSub_free L' (fun i => M i) rfl, det_of_smul_rows, Submodule.mem_span_singleton] at h
      obtain ⟨r, hr⟩ := h
      rw [← valuation_smul_of_notMem p (prod_notMem_asIdeal p s hs), ← hr]
      exact valuation_smul_le p r _
    | zero => simp
    | add a b _ _ ha hb => exact (Valuation.map_add _ a b).trans (max_le ha hb)
    | smul r a _ ha => exact (valuation_smul_le p r a).trans ha

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerLogOmCore
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.LamT

theorem exists_kronecker_logOm_core : ∀ (D : D7) (T : Core D) (h : LawsCore T) (large₂ : SizeData₂ D), ∃ (_ : NeZero T.Q.H.d) (χ : DirichletCharacter ℂ T.Q.H.d), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm :=
  fun D T h large₂ => GlobalTheory.LamF.exists_kronecker_logOm_eq D T.Q h.pins.1 large₂

end GlobalTheory.LamT
end

