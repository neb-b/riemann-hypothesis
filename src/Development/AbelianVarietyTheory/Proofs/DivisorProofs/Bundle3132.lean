module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstAlongOfKodairaSpencerZeroChart
section
set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSConst

theorem isConstAlong_of_ks_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hb D q hq Θ hKS hΘ ρ hρ
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m d
  haveI : IsNoetherianRing (ChartRing k m d) := hA.1
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) := hA.2.2.2
  letI := H.starRing
  obtain ⟨Y⟩ : Nonempty (Ray P.oD) := inferInstance
  obtain ⟨n', v', dd, hdd⟩ := _root_.GlobalTheory.RayBasis.exists_basis_isInv (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h0 => by
    have h4 := congrArg (fun f : ChartRing k m d => MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1) f) h0
    simp [bdParam, MvPowerSeries.coeff_X] at h4
  have f1 : ∀ x y, D (x + y) = D x + D y := D.map_add
  have f2 : ∀ (z : ℤ) (x : ChartRing k m d), D (z • x) = z • D x := fun z x => map_zsmul D z x
  have f3 : D 1 = 0 := D.map_one_eq_zero
  have f4 : ∀ x y, D (x * y) = x • D y + y • D x := D.leibniz
  obtain ⟨h, hB, hD⟩ : ∃ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
    generalize (⇑D : ChartRing k m d → ChartRing k m d) = f at f1 f2 f3 f4 hq ⊢
    letI : Algebra ℤ (ChartRing k m d) := Ring.toIntAlgebra _
    let D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d) :=
      { toFun := f, map_add' := f1, map_smul' := fun z x => f2 z x, map_one_eq_zero' := f3, leibniz' := f4 }
    exact _root_.GlobalTheory.heat_commuting_periods_exists (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd m (bdParam k m d) gam hmon hne D'
      (fun i => by
        show f (bdParam k m d i) ∈ _
        rw [hq i]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  exact GlobalTheory.T.degenerationData_constant_of_flat_heatOperators E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hB hD
    (GlobalTheory.T.heat_symbol_mem_maximalIdeal_of_kodairaSpencer_zero E H k m d t P gam hmon hli hab n v hv hb Y n' v' dd hdd D q hq h hB hD Θ hKS hΘ) ρ hρ
end GlobalTheory.KSConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRegularNearRigidBoundaryPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LocRegRig

theorem isKS_regular_at_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ Y.X.basicOpen f) ∧ x ∉ interior Y) → ∃ g ∉ m, ∀ a b, ∃ s : Γ(Y.X, U.1), (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * Θ a b := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hchart U W hW n v hv hbasis D DW Θ hDW hKS m hm hx0
  obtain ⟨x, hxU, hxm, hxint⟩ := hx0
  haveI := isIso_fst Y
  obtain ⟨x', rfl⟩ := (genι Y).surjective x
  have hbd : x' ∈ genBd Y := mem_genBd_iff.2 fun h => hxint (by
    rw [← SetLike.mem_coe, coe_interior]; exact h)
  have hcl : IsClosed ({x'} : Set (gen Y)) := _root_.GlobalTheory.LocReg.isClosed_singleton_gen E H Dw l Xo c Y U m hm x' hxU hxm
  obtain ⟨k, _, m', d, ξ, t, P, gam, h₀, h₁, h₂, h₃, ⟨φ⟩, h₅, h₆, -⟩ := hchart x' hbd hcl
  subst h₀
  have hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := hxU
  haveI : CharZero k := _root_.GlobalTheory.LocReg.charZero_of_chart E H Dw l Xo c Y k m' d ξ
  obtain ⟨D', hD', hDlog⟩ := _root_.GlobalTheory.ChartDer.logDer_extend_chartRing E H Dw l Xo c Y U D k m' d ξ hx h₁ h₂
  have hfac := GlobalTheory.T.toricChart_comp_genericFibreInclusion_eq_spec_chartMap E H Dw l Xo c Y U k m' d ξ hx
  obtain ⟨vR, hvR, hbR, hcomp⟩ := GlobalTheory.T.exists_tangentBasis_pullback_to_spec_of_affineOpen E H Y.X Y.t U _ (GlobalTheory.LocReg.chartHom Y U ξ hx) t _ hfac φ n v hv hbasis
  have hab := _root_.GlobalTheory.ChartAbLocus.mem_abLocus_iff E H Dw l Xo c Y k m' d ξ t φ h₃
  have hlin : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    h₆.linearIndependent.map' (Submodule.subtype _) (by simp)
  obtain ⟨ΘR, hΘR⟩ := _root_.GlobalTheory.LogKSChart.exists_isKS_of_logDer E H k m' d t P (fun i => gam i) h₅ hlin hab n vR hvR hbR D' hDlog
  obtain ⟨h, hhW, hh0⟩ := _root_.GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero E H Dw l Xo c Y U W hW k m' d ξ hx h₃
  obtain ⟨hflat, hcomap⟩ := _root_.GlobalTheory.LocRegFlat.chartHom_flat_comap E H Dw l Xo c Y U k m' d ξ hx h₁ m hm hxm
  have hWc := _root_.GlobalTheory.ModelQC.isCompact_of_le_affineOpen E H Dw l Xo c Y U W.1 (hW.le.trans inf_le_left)
  obtain ⟨g, hg, hs⟩ := _root_.GlobalTheory.LocRegDesc.descent Y.X U W.1 (hW.le.trans inf_le_left) hWc _ (GlobalTheory.LocReg.chartHom Y U ξ hx) hflat m hcomap
    h hhW hh0 (Fin n × Fin n) (fun p => Θ p.1 p.2) (fun p s N e => Dvd.intro _
      (_root_.GlobalTheory.LocRegCmp.ks_chart_eq E H Dw l Xo c Y hpq hsm U W hW n v hv hbasis D DW Θ hDW hKS k m' d ξ hx t φ h₁ h₃ vR hvR hcomp D' hD' ΘR hΘR
        h hhW hh0 p.1 p.2 s N e).symm)
  exact ⟨g, hg, fun a b => hs (a, b)⟩

end GlobalTheory.LocRegRig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBig
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.NefBigSep

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H N A B : LB X} {Z : Closeds X}

theorem deg_of_cls_eq (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H) (hN : N.IsLB) (hA : A.IsLB)
    (hB : B.IsLB) (a b : ℕ) (e : cls N hN = a • cls A hA + b • cls B hB) :
    interNumRed k Z ![N] = a * interNumRed k Z ![A] + b * interNumRed k Z ![B] := by
  rw [hZ.interNumRed_of_cls_eq_add hH hN (isLB_lbPow hA a) (isLB_lbPow hB b)
    (by rw [cls_lbPow hA, cls_lbPow hB, e]), hZ.interNumRed_lbPow hH hA,
    hZ.interNumRed_lbPow hH hB]

theorem exists_budget (ρ S c : ℚ) (a : ℕ) (hρ : 0 < ρ) (hS : S < ρ) (hS0 : 0 ≤ S) (hc : 0 < c) :
    ∃ q m' : ℕ, 0 < m' ∧ (q : ℚ) = ρ * m' ∧ a < q ∧ 1 / (m' : ℚ) ≤ c ∧ (m' : ℚ) * S < q - a := by
  have hd : (0 : ℚ) < ρ.den := by exact_mod_cast ρ.den_pos
  have hu : (0 : ℤ) ≤ ρ.num := (Rat.num_pos.2 hρ).le
  have hρ' : ((ρ.num.toNat : ℕ) : ℚ) = ρ * ρ.den := by
    rw [show ((ρ.num.toNat : ℕ) : ℚ) = ((ρ.num.toNat : ℤ) : ℚ) from rfl, Int.toNat_of_nonneg hu]
    exact (Rat.mul_den_eq_num ρ).symm
  have hgap : 0 < (ρ.den : ℚ) * (ρ - S) := mul_pos hd (sub_pos.2 hS)
  obtain ⟨t, ht⟩ := exists_nat_gt (max (1 / c) (a / ((ρ.den : ℚ) * (ρ - S))))
  have ht1 : 1 / c < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht2 : a / ((ρ.den : ℚ) * (ρ - S)) < t := lt_of_le_of_lt (le_max_right _ _) ht
  have htpos : (0 : ℚ) < t := lt_trans (by positivity) ht1
  have ht2' : (a : ℚ) < t * ((ρ.den : ℚ) * (ρ - S)) := by
    rw [div_lt_iff₀ hgap] at ht2; linarith
  refine ⟨ρ.num.toNat * t, ρ.den * t, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos ρ.den_pos (by exact_mod_cast htpos)
  · push_cast; rw [hρ']; ring
  · have : (a : ℚ) < ((ρ.num.toNat * t : ℕ) : ℚ) := by
      push_cast; rw [hρ']; nlinarith [mul_nonneg (mul_nonneg hd.le htpos.le) hS0]
    exact_mod_cast this
  · push_cast
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at ht1
    have : (1 : ℚ) ≤ ρ.den := by exact_mod_cast ρ.den_pos
    nlinarith
  · push_cast; rw [hρ']; nlinarith

end GlobalTheory.NefBigSep

namespace GlobalTheory.NefBigSep

theorem separate_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hPr hNad hNef X _ _ _ p n hp hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hG hNn hNb
    hcurve hx₁ hx₂ hne hh hz hsum hρ
  letI := algebraΓOfHom p
  obtain ⟨a, A, hA, E₀, ha, hAmp, hE₀, hcls⟩ :=
    GlobalTheory.T.exists_ample_add_effective_of_nef_big hNef X p hp N hNn.isLB hNn hNb
  obtain ⟨c, hc, hkltc⟩ := _root_.GlobalTheory.PairStep.exists_pos_kltAt_add_smul hPr X p n hp hdim Δ m G (qWeil E₀ 1) hm hG hklt
    ⟨1, E₀, one_pos, hE₀, rfl⟩
  have hS0 : 0 ≤ ∑ e ∈ Finset.Icc 1 n, h e := Finset.sum_nonneg fun e _ => (hh e).le
  obtain ⟨q, m', hm', hq, haq, hmc, hbud⟩ := exists_budget ρ _ c a hρ hsum hS0 hc
  have hNp := isLB_lbPow hNn.isLB (q - a)
  have hN'lb := isLB_tens hA hNp
  have hclsN' : cls _ hN'lb = cls A hA + (q - a) • cls N hNn.isLB := by
    rw [cls_tens hA hNp, cls_lbPow hNn.isLB]
  have hN'amp : IsAmpleLB (tens A (lbPow N (q - a))) :=
    IsAmpleLB.tens_of_isNef hNef ℂ X p hp A _ hAmp (hNn.pow hAmp _)
  have hqa : (0 : ℚ) < q - a := sub_pos.2 (by exact_mod_cast haq)
  have hqa' : (((q - a : ℕ) : ℚ)) = q - a := by rw [Nat.cast_sub haq.le]
  have hB : qWeil E₀ m' = (1 / (m' : ℚ)) • qWeil E₀ 1 := by
    funext z; simp [qWeil]; ring
  refine GlobalTheory.T.exists_section_separating_two_points_ample hPr hNad hNef X p n hp hdim M (Δ + qWeil E₀ m') (m * m') (m' • G + m • E₀)
    (tens A (lbPow N (q - a))) (1 / (m' : ℚ)) (fun e => h e / ((q : ℚ) - a)) x₁ x₂ hM
    (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', E₀, hm', hE₀, rfl⟩) ?_ (Nat.mul_pos hm hm')
    (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G E₀ hm hm' hG) hN'amp ?_ hx₁ hx₂ hne
    (fun e => div_pos (hh e) hqa) ?_ ?_
  · intro y
    rw [hB]
    exact (_root_.GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff X p n hp hdim Δ (qWeil E₀ 1) (1 / (m' : ℚ)) c y
      ⟨1, E₀, one_pos, hE₀, rfl⟩ hmc).1 (hkltc y)
  · intro C hC
    have h1 := hcurve C hC
    have dN' := deg_of_cls_eq hC hAmp hN'lb hA hNn.isLB 1 (q - a) (by rw [hclsN', one_nsmul])
    have dK := hC.interNumRed_of_cls_eq_add hAmp (isLB_lbPow hNn.isLB a) hA (isLB_toLB E₀)
      (by rw [cls_lbPow hNn.isLB, hcls])
    rw [hC.interNumRed_lbPow hAmp hNn.isLB] at dK
    have dG := deg_of_cls_eq hC hAmp (isLB_toLB (m' • G + m • E₀)) (isLB_toLB G) (isLB_toLB E₀)
      m' m (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add (f := _), map_nsmul, map_nsmul])
    rw [h1, dN', dG]
    have dK' : (a : ℚ) * interNumRed ℂ C ![N] = interNumRed ℂ C ![A] + interNumRed ℂ C ![toLB E₀] := by
      exact_mod_cast dK
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hm0' : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
    push_cast
    rw [hqa']
    field_simp
    linear_combination (m : ℚ) * dK' - (m : ℚ) * (interNumRed ℂ C ![N] : ℚ) * hq
  · intro z e hze he hdz
    have hmix := mixExp_interNumRed hNef ℂ X p hp N A (tens A (lbPow N (q - a))) hNn.isLB hA hN'lb
      (q - a) 1 (Closeds.closure {z}) e hNn hAmp.isNef (by rw [hclsN', one_nsmul, add_comm])
      (by rw [Closeds.coe_closure]; exact hdz)
    have key : ((q : ℚ) - a) ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)
        ≤ (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => tens A (lbPow N (q - a)) : ℤ) := by
      have := (Int.cast_le (R := ℚ)).2 hmix
      push_cast at this
      rwa [hqa'] at this
    have h0 := hz z e hze he hdz
    have e1 : h e ^ e * ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ) : ℚ) =
        (h e / ((q : ℚ) - a)) ^ e * (((q : ℚ) - a) ^ e *
          (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) := by
      rw [div_pow]; field_simp
    calc 2 * (e : ℚ) ^ e < _ := h0
      _ = _ := e1
      _ ≤ _ := mul_le_mul_of_nonneg_left key (pow_nonneg (div_pos (hh e) hqa).le _)
  · rw [← Finset.sum_div, div_lt_div_iff₀ hqa (by exact_mod_cast hm')]
    linarith

end GlobalTheory.NefBigSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDualNumberClassified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangent

theorem cycAway_dualNumber_factor {n : ℕ} (hn : n ≠ 0) (K : Type) [Field K] (β : cycAway n →+* DualNumber K) :
    ∃ β₀ : cycAway n →+* K, β = (algebraMap K (DualNumber K)).comp β₀ := by
  let π : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  have hnK : (n : K) ≠ 0 := by
    have := ((isUnit_natCast hn).map (π.comp β)).ne_zero
    simpa using this
  let S : Subring (cycAway n) :=
    { carrier := {x | TrivSqZeroExt.snd (β x) = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, TrivSqZeroExt.snd_mul] at *
        simp [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _), TrivSqZeroExt.snd_add] at *
        simp [ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_neg, TrivSqZeroExt.snd_neg] at *
        simp [ha] }
  have hζ : zetaAway n ∈ S := by
    have hz : zetaAway n ^ n = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    have h1 : β (zetaAway n) ^ n = 1 := by rw [← map_pow, hz, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    have h3 := congrArg TrivSqZeroExt.fst h1
    rw [TrivSqZeroExt.snd_pow] at h2
    rw [TrivSqZeroExt.fst_pow] at h3
    simp only [TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one] at h2 h3
    have ha : TrivSqZeroExt.fst (β (zetaAway n)) ≠ 0 := by
      intro h0; rw [h0, zero_pow hn] at h3; exact zero_ne_one h3
    show TrivSqZeroExt.snd (β (zetaAway n)) = 0
    rw [nsmul_eq_mul, smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' (pow_ne_zero _ ha)
      · exact h'
  have hinv : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) ∈ S := by
    set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
    have hu : (n : cycAway n) * u = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
    have h1 : (n : DualNumber K) * β u = 1 := by rw [← map_natCast β, ← map_mul, hu, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_natCast,
      TrivSqZeroExt.snd_natCast, smul_zero, add_zero, smul_eq_mul] at h2
    show TrivSqZeroExt.snd (β u) = 0
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · exact h
  have hall : ∀ x : cycAway n, x ∈ S := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hζ
      · exact hinv
    | zero => exact S.zero_mem
    | one => exact S.one_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | neg y _ hy => exact S.neg_mem hy
    | mul y z _ _ hy hz => exact S.mul_mem hy hz
  refine ⟨π.comp β, RingHom.ext fun x => ?_⟩
  ext
  · rfl
  · exact (hall x).trans (TrivSqZeroExt.snd_inl _ _).symm

theorem classified_dualNumber : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K]
    (β : cycAway n →+* DualNumber K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨β₀, rfl⟩ := cycAway_dualNumber_factor hn0 K β
  let L := AlgebraicClosure K
  obtain ⟨ψ, h1, -, hfl, hsurj⟩ := GlobalTheory.DualOpen.dualNumber_map_flat_surjective K L (algebraMap K L)
  have hff : ψ.FaithfullyFlat := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ψ)).1 ⟨hfl, hsurj⟩
  letI : Algebra (DualNumber K) (DualNumber L) := ψ.toAlgebra
  haveI : Module.FaithfullyFlat (DualNumber K) (DualNumber L) := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  refine _root_.GlobalTheory.SiegFpqcDesc.classified_of_faithfullyFlat g n hg hn hodd F (DualNumber K) (DualNumber L) _ c hc ?_
  intro c' hc'
  have hp : c'.Principal := by
    refine (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) _ _ (spMap ((algebraMap K (DualNumber K)).comp β₀))
      (spMap ((algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀)))
      (spMap (algebraMap (DualNumber K) (DualNumber L))) rfl ?_).2.1 c c' hc' hc
    rw [GlobalTheory.SiegelRingChange.spMap_comp']
    simp [spMap]
  have e : (algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀) =
      (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    exact congrArg (fun q => q.comp β₀) h1
  have key : ∀ b : cycAway n →+* DualNumber L, b = (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) →
      ∀ c' : SiegPre g n (zetaAway n) (spMap b), c'.Principal →
      ∃ f : Sp (DualNumber L) ⟶ F.X, f ≫ F.s = spMap b ∧ SiegPB c' F.univ f := by
    rintro b rfl c' hc'
    exact _root_.GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed g n hg hn hodd F L ((algebraMap K L).comp β₀) c' hc'
  exact key _ e c' hp

end GlobalTheory.SiegelTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSumsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_translate_eq_twisted_sums : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : X → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h)) := by
  first | exact @GlobalTheory.GSep.twistSum_translate | exact GlobalTheory.GSep.twistSum_translate | (intros; apply GlobalTheory.GSep.twistSum_translate <;> assumption)
end

