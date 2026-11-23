module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerPullbackSemiAbelianMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.LocRegCmp
open GlobalTheory.FlagMod (ev)

theorem leibniz_ext_of_res {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) {C : Type} [CommRing C]
    (ψ : Γ(X, W.1) →+* C) (d : C → C) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (D : Derivation ℤ Γ(X, W.1) Γ(X, W.1))
    (h : ∀ r, d (ψ ((X.presheaf.map (homOfLE hW).op).hom r)) = ψ (D ((X.presheaf.map (homOfLE hW).op).hom r)))
    (b : Γ(X, W.1)) : d (ψ b) = ψ (D b) := by
  have d0 : d 0 = 0 := by simpa using hadd 0 0
  have d1 : d 1 = 0 := by simpa using hd 1 1
  let g₁ : Γ(X, W.1) →+* DualNumber C :=
    { toFun := fun r => TrivSqZeroExt.inl (ψ r) + TrivSqZeroExt.inr (d (ψ r))
      map_one' := by ext <;> simp [d1]
      map_zero' := by ext <;> simp [d0]
      map_add' := fun a b => by ext <;> simp [hadd]
      map_mul' := fun a b => by ext <;> simp [hd, mul_comm] }
  let g₂ : Γ(X, W.1) →+* DualNumber C :=
    { toFun := fun r => TrivSqZeroExt.inl (ψ r) + TrivSqZeroExt.inr (ψ (D r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, mul_comm] }
  have e : g₁.comp (X.presheaf.map (homOfLE hW).op).hom = g₂.comp (X.presheaf.map (homOfLE hW).op).hom := by
    refine RingHom.ext fun r => ?_
    ext
    · simp [g₁, g₂]
    · simpa [g₁, g₂] using h r
  have : IsOpenImmersion (chart W) := W.2.isOpenImmersion_fromSpec
  have e2 : spMap g₁ ≫ chart W = spMap g₂ ≫ chart W := by
    rw [← GlobalTheory.LogKSLoc.spMap_res_chart U W hW, ← Category.assoc, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp',
      GlobalTheory.LogKSLoc.spMap_comp', e]
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 ((cancel_mono (chart W)).1 e2))
  have e4 : g₁ b = g₂ b := congrArg (fun k => k b) e3
  simpa [g₁, g₂] using congrArg TrivSqZeroExt.snd e4

theorem isKS_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1))
    (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1))
    (hD : ∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r))
    (hKS : IsKS t V U v D Θ) :
    IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW
      ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  obtain ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩ := hKS
  have hWU : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, fun i => Wc i ⊓ t.G.hom ⁻¹ᵁ W.1, j, d, ?_, fun i => inf_le_left.trans (hj i), fun i => ?_,
    fun i h b => ?_, fun i i' O hO g S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [← iSup_inf_eq, hsup, ← Scheme.Hom.preimage_inf, inf_right_comm, inf_eq_right.mpr hW]
  · exact ⟨fun O hO => (hfld i).1 O (hO.trans inf_le_left), fun O hO => (hfld i).2.1 O (hO.trans inf_le_left),
      fun O O' h hO => (hfld i).2.2 O O' h (hO.trans inf_le_left)⟩
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r) =
        resG t.G.left (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i) ((t.G.hom.appLE U.1 (Wc i) (hWU i)).hom r) := by
      intro r
      have e1 := congrArg (fun k => k.hom r) (t.G.hom.map_appLE h (homOfLE hW).op)
      have e2 := congrArg (fun k => k.hom r) (t.G.hom.appLE_map (hWU i)
        (homOfLE (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i)).op)
      exact e1.trans e2.symm
    refine leibniz_ext_of_res U W hW _ _ ((hfld i).1 _ inf_le_left) ((hfld i).2.1 _ inf_le_left) DW (fun r => ?_) b
    rw [hD, e, e, (hfld i).2.2 _ _ _ le_rfl, hcomp]
  · refine htest i i' O (hO.trans (inf_le_inf inf_le_left inf_le_left)) g S
      (φ.comp (X.presheaf.map (homOfLE hW).op).hom) g₀ w ?_ hO' fun a => ?_
    · rw [hg₀, ← GlobalTheory.LogKSLoc.spMap_res_chart U W hW, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
    · obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.dualMap_comp']

theorem ks_chart_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (k : Type) [Field k] [CharZero k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) (t : SAB H (Sp (ChartRing k m d))) (φ : SABMap t Y.t (ξ ≫ genι Y)), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ vR : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (vR i)) → (∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx))) ≫ v i) → ∀ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (GlobalTheory.LocReg.chartHom Y U ξ hx r) = GlobalTheory.LocReg.chartHom Y U ξ hx (D.1 r)) → ∀ ΘR : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) vR (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) ΘR → ∀ (h : Γ(Y.X, U.1)) (hh : Y.X.basicOpen h ≤ W.1), GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 → ∀ (a b : Fin n) (s : Γ(Y.X, U.1)) (N : ℕ), (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N) * (Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b) → GlobalTheory.LocReg.chartHom Y U ξ hx s = GlobalTheory.LocReg.chartHom Y U ξ hx h ^ N * (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm U W hW n v hv hb D DW Θ hDW hKS k _ _ m d ξ hx t φ hEt hbd vR hvR hvRφ D' hD' ΘR hKSR h hh hρh a b s N hs
  let ι0 : ChartRing k m d →+* FractionRing (ChartRing k m d) := algebraMap _ _
  let g : Sp (ChartRing k m d) ⟶ Y.X := ξ ≫ genι Y
  have hι0 : Function.Injective ι0 := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_ringHom (f := ι0.comp (algebraMap k (ChartRing k m d))) (hι0.comp (algebraMap k _).injective)
  obtain ⟨hg, hgρ⟩ := GlobalTheory.LocReg.chart_appLE_eq E H Dw l Xo c Y U k m d ξ hx
  have eR : ∀ x : ChartRing k m d, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom x) = x :=
    fun x => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv_hom_id_apply x
  have hgx : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom ((g.appLE U.1 ⊤ hg).hom r) =
      GlobalTheory.LocReg.chartHom Y U ξ hx r := by
    intro r; rw [hgρ]; exact eR _
  obtain ⟨hUW, D'', hDtop, hDW'⟩ := GlobalTheory.LocReg.deriv_ext_basicOpen Y.X U W (hW.le.trans inf_le_left) D.1 DW hDW h hh _ g hg D'
    (fun r => by rw [hgx, hgx]; exact hD' r)
  let U' : (Sp (ChartRing k m d)).affineOpens :=
    (Sp (ChartRing k m d)).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)
  have hU'U : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (g.preimage_mono (hW.le.trans inf_le_left))
  let v' : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), U'.1)) ⟶ t.G.left) := fun i =>
    spMap (dualMap ((Sp (ChartRing k m d)).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom) ≫ vR i
  have hv' : ∀ i, IsTanAtG t (chart U') (v' i) := fun i =>
    GlobalTheory.KSAgree.tan_res E H _ t ⟨⊤, isAffineOpen_top _⟩ U' le_top (vR i) (hvR i)
  have hcompU : ∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE U.1 U'.1 hU'U).hom) ≫ v i := by
    intro i
    show (spMap _ ≫ vR i) ≫ φ.φ = _
    rw [Category.assoc, hvRφ i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, GlobalTheory.CechKS.dualMap_comp_dualMap, ← hgρ,
      ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  have hcompW : ∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE W.1 U'.1 hUW).hom) ≫
      (spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) := by
    intro i
    rw [hcompU i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, GlobalTheory.CechKS.dualMap_comp_dualMap,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  let V' : (Sp (ChartRing k m d)).Opens := (Sp (ChartRing k m d)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))
  have hUV' : U'.1 ⊓ V' ≤ g ⁻¹ᵁ interior Y := by
    intro p hp
    have hp2 : p ∈ V' := hp.2
    have hnp : ∏ i, bdParam k m d i ∉ p.asIdeal := by
      have := hp2
      simp only [V'] at this
      rw [basicOpen_eq_of_affine] at this
      exact this
    have hnb : ξ p ∉ genBd Y := fun h' => hnp ((hbd p).1 h')
    obtain ⟨y, hy⟩ : ξ p ∈ Set.range Y.jQ := by
      by_contra h'
      exact hnb (mem_genBd.2 h')
    show g p ∈ (interior Y : Set Y.X)
    rw [GlobalTheory.LogKS.interior, Scheme.Hom.coe_opensRange]
    refine ⟨y, ?_⟩
    show (Y.jQ ≫ pullback.fst _ _) y = (ξ ≫ genι Y) p
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
  have hprod : ∏ i, bdParam k m d i ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
    simp [bdParam, MvPowerSeries.coeff_X] at this
  let x0 : Sp (FractionRing (ChartRing k m d)) ⟶ Y.X := spMap ι0 ≫ g
  have hevtop : ∀ (hK : ⊤ ≤ (spMap ι0) ⁻¹ᵁ (⊤ : (Sp (ChartRing k m d)).Opens)) r,
      ev (spMap ι0) ⊤ hK r = ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r) := by
    intro hK r
    unfold ev
    have : (spMap ι0).appLE ⊤ ⊤ hK = (spMap ι0).appTop := Scheme.Hom.appLE_eq_app _
    rw [this, Scheme.ΓSpecIso_naturality]
    rfl
  have hx0U : ⊤ ≤ x0 ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_comp (spMap ι0) hg
  have hevU : ∀ r, ev x0 U.1 hx0U r = ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx r) := by
    intro r
    rw [GlobalTheory.FlagMod.ev_spMap ι0 g U.1 hg hx0U]
    show ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = _
    rw [hgx]
  have htop : ⊤ ≤ (spMap ι0) ⁻¹ᵁ (⊤ : (Sp (ChartRing k m d)).Opens) := fun _ _ => trivial
  have hx0h : ⊤ ≤ x0 ⁻¹ᵁ Y.X.basicOpen h := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev x0 U.1 hx0U h
      (by rw [hevU]; exact ((map_ne_zero_iff ι0 hι0).2 hρh).isUnit) p
  have hx0W : ⊤ ≤ x0 ⁻¹ᵁ W.1 := fun p hp => hh (hx0h hp)
  have hKU' : ⊤ ≤ (spMap ι0) ⁻¹ᵁ U'.1 := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev (spMap ι0) ⊤ htop ((g.appLE U.1 ⊤ hg).hom h)
      (by rw [hevtop, hgx]; exact ((map_ne_zero_iff ι0 hι0).2 hρh).isUnit) p
  have hKV' : ⊤ ≤ (spMap ι0) ⁻¹ᵁ V' := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev (spMap ι0) ⊤ htop _
      (by rw [hevtop, eR]; exact ((map_ne_zero_iff ι0 hι0).2 hprod).isUnit) p
  have hint : ⊤ ≤ x0 ⁻¹ᵁ interior Y := fun p hp => hUV' ⟨hKU' hp, hKV' hp⟩
  obtain ⟨P₀, θ0, hpb, hiso⟩ := GlobalTheory.KSUniq.exists_polAV_interior Y x0 hint
  obtain ⟨mm, hmm, hiso'⟩ := GlobalTheory.PolAVPull.polAV_pull E H Y.X _ Y.t t g φ _ (spMap ι0) P₀ θ0 hpb hiso
  let φK := ev (spMap ι0) U'.1 hKU'
  have hpt : spMap φK ≫ chart U' = spMap ι0 := GlobalTheory.FlagMod.spMap_ev (spMap ι0) U'.2 hKU'
  have hvW : ∀ i, IsTanAtG Y.t (chart W) (spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) :=
    fun i => GlobalTheory.KSAgree.tan_res E H Y.X Y.t U W _ (v i) (hv i)
  have hks1 := GlobalTheory.KSBaseChange.isKS_pull E H Y.X _ Y.t t g φ (interior Y) V' W U' hUW hUV' n _ v' hvW hv' hcompW DW D'' hDW' Θ hKS
  have hks2 := isKS_restrict t V' ⟨⊤, isAffineOpen_top _⟩ U' le_top vR _ D'' ΘR hDtop hKSR
  have hb' := GlobalTheory.BasisPull.tanBasis_pull E H Y.X _ Y.t t g φ U U' hU'U n v v' hv hb hv' hcompU
  have huniq := GlobalTheory.KSPtUniq.isKS_unique_at_point E H _ t V' U' n v' hv' hb' _ φK P₀ mm
    (by rw [hpt]; exact hKV') (by rw [hpt]; exact hmm) hiso' _ _ _ hks1 hks2
  have hab := congrFun (congrFun huniq a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hab
  have e1 : φK ((g.appLE W.1 U'.1 hUW).hom (Θ a b)) = ev x0 W.1 hx0W (Θ a b) :=
    GlobalTheory.FlagMod.ev_appLE (spMap ι0) g hUW hKU' hx0W (Θ a b)
  have e2 : φK (((Sp (ChartRing k m d)).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom (ΘR a b)) =
      ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b)) :=
    (GlobalTheory.FlagMod.ev_res (spMap ι0) le_top hKU' htop (ΘR a b)).trans (hevtop _ _)
  have r1 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s) =
      ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx s) :=
    (GlobalTheory.FlagMod.ev_res x0 (Y.X.basicOpen_le h) hx0h hx0U s).trans (hevU s)
  have r2 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N)) =
      ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx h) ^ N := by
    rw [← map_pow, ← map_pow]
    exact (GlobalTheory.FlagMod.ev_res x0 (Y.X.basicOpen_le h) hx0h hx0U (h ^ N)).trans (hevU _)
  have r3 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b)) = ev x0 W.1 hx0W (Θ a b) :=
    GlobalTheory.FlagMod.ev_res x0 hh hx0h hx0W _
  have hsx := congrArg (ev x0 (Y.X.basicOpen h) hx0h) hs
  rw [map_mul, r1, r2, r3, ← e1, hab, e2] at hsx
  apply hι0
  rw [map_mul, map_pow]
  exact hsx

end GlobalTheory.LocRegCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerDescentOfTorusInvariantLifts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatDescend

open GlobalTheory.KS

theorem alg_sum {Γ₀ R : Type} [CommRing Γ₀] [CommRing R] {g n : ℕ} (κ : R →+* Γ₀) (P : Matrix (Fin g) (Fin n) R)
    (C : Matrix (Fin n) (Fin n) R) (X Z : Fin g → Γ₀) :
    ∑ a, ∑ b, κ (C a b) * (∑ c', κ (P c' b) * X c') * ∑ c, κ (P c a) * Z c =
      ∑ c, ∑ c', κ ((P * C * Pᵀ) c c') * X c' * Z c := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc ∑ a, ∑ b, ∑ c, ∑ c', κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c)
      = ∑ b, ∑ a, ∑ c, ∑ c', κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ c', ∑ a, κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm)
    _ = ∑ c, ∑ c', ∑ b, ∑ a, κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm)
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun a _ => ?_
        ring

theorem pbT_id' {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U)) {O : X.Opens} (h : O ≤ U) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT_of_le (𝟙 X) (show O ≤ (𝟙 X) ⁻¹ᵁ U from h), rsT_of_le h]
  rfl

theorem valR_pbT {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (q : Z ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ V)) (f : Γ(X, V)) :
    valR x (q ⁻¹ᵁ V) (pbT q f (q ⁻¹ᵁ V)) = valR (x ≫ q) V f := by
  rw [GlobalTheory.Heat.WtAlg.valR_eq' x _ h, GlobalTheory.KS.pbT_of_le q le_rfl, GlobalTheory.Heat.WtAlg.valR_eq' (x ≫ q) V h]
  rw [← Scheme.Hom.appLE_comp_appLE x q V (q ⁻¹ᵁ V) ⊤ le_rfl h]
  rfl

theorem isWt_pbT {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)) :
    IsWt Y 0 _ (pbT Y.q.left f (Y.q.left ⁻¹ᵁ V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.Heat.WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul, valR_pbT _ _ _ hV', valR_pbT _ _ _ hV]
  subst ha ha'
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq]
  rw [e]

section General

variable {R : Type} [CommRing R] {G B : Over (Sp R)} (q : G ⟶ B)

theorem exists_lift (hinj : ∀ (O : B.left.Opens) (f f' : Γ(B.left, O)),
      pbT q.left f (q.left ⁻¹ᵁ O) = pbT q.left f' (q.left ⁻¹ᵁ O) → f = f')
    (D : R → R) (V : B.left.Opens) (d : Fld G.left) (hd : IsLift G D (q.left ⁻¹ᵁ V) d)
    (hdesc : ∀ O, O ≤ V → ∀ f : Γ(B.left, O), ∃ f' : Γ(B.left, O),
      pbT q.left f' (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O))) :
    ∃ dB : Fld B.left, IsLift B D V dB ∧ ∀ O, O ≤ V → ∀ f : Γ(B.left, O),
      pbT q.left (dB O f) (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O)) := by
  classical
  have hq : q.left ≫ B.hom = G.hom := Over.w q
  let dB : Fld B.left := fun O f => if h : O ≤ V then (hdesc O h f).choose else 0
  have hB : ∀ O, O ≤ V → ∀ f : Γ(B.left, O),
      pbT q.left (dB O f) (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O)) := by
    intro O h f
    simp only [dB, dif_pos h]
    exact (hdesc O h f).choose_spec
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hd
  refine ⟨dB, ⟨⟨fun O h f f' => hinj O _ _ ?_, fun O h f f' => hinj O _ _ ?_, fun O O' h' h f => hinj O' _ _ ?_⟩,
    fun O h r => hinj O _ _ ?_⟩, hB⟩
  · rw [pbT_add, hB O h, hB O h, hB O h, pbT_add, h1 _ (q.left.preimage_mono h)]
  · rw [pbT_add, pbT_mul, pbT_mul, hB O h, hB O h, hB O h, pbT_mul, h2 _ (q.left.preimage_mono h)]
  · have hp : q.left ⁻¹ᵁ O' ≤ q.left ⁻¹ᵁ O := q.left.preimage_mono h'
    rw [hB O' (h'.trans h), ← rsT_of_le h', ← rsT_of_le h', pbT_rsT _ h' le_rfl, pbT_rsT _ h' le_rfl,
      ← rsT_pbT q.left le_rfl hp, ← rsT_pbT q.left le_rfl hp (dB O f), hB O h, rsT_of_le hp, rsT_of_le hp]
    exact h3 _ _ hp (q.left.preimage_mono h) _
  · rw [hB O h, pbT_constFn _ _ le_rfl, pbT_constFn _ _ le_rfl, hq, h4 _ (q.left.preimage_mono h)]

theorem dlg_pull {g : ℕ} (L : LB B.left) (δ : Fld G.left) (e : Fin g → Fld B.left) (he : ∀ c, IsField ⊤ (e c))
    (p : Fin g → R) (hδ : ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V),
      δ W (pbT q.left f W) = ∑ c, constFn G.hom W (p c) * pbT q.left (e c V f) W)
    (i i' : L.ι) (O : B.left.Opens) (h : O ≤ L.U i ⊓ L.U i') :
    dlg G q.left L δ i i' (q.left ⁻¹ᵁ O) =
      ∑ c, constFn G.hom _ (p c) * pbT q.left (dlg B (𝟙 _) L (e c) i i' O) (q.left ⁻¹ᵁ O) := by
  unfold dlg
  rw [← pbT_rsT q.left h le_rfl, hδ O _ le_rfl, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pbT_mul, pbT_id' _ h, pbT_id' _ h, pbT_rsT q.left h le_rfl, _root_.mul_assoc]

end General

theorem ksRel_of_invLifts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) → (∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → KSRel Dd.toPre.P.A (𝟙 Dd.toPre.P.A.left) Dd.toPre.P.L e ⇑D (P * C * Pᵀ) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd _ g w e P he hP D J V j d hcov hle hlift hwt C hC
  have hA := _root_.GlobalTheory.Heat.exists_unique_pbT_of_isWt_zero R Dd.toPre O oa Y
  have hinj : ∀ (U : Dd.toPre.P.A.left.Opens) (f f' : Γ(Dd.toPre.P.A.left, U)),
      pbT Y.q.left f (Y.q.left ⁻¹ᵁ U) = pbT Y.q.left f' (Y.q.left ⁻¹ᵁ U) → f = f' := fun U f f' h =>
    (hA U _ (isWt_pbT Y U f')).unique h rfl
  choose dB hB hB' using fun i => exists_lift Y.q hinj D (V i) (d i) (hlift i) fun U hU f =>
    (hA U _ (hwt i 0 U (Y.q.left.preimage_mono hU) _ (isWt_pbT Y U f))).exists
  refine ⟨J, V, j, dB, hcov, hle, hB, fun i i' U hU f => hinj U _ _ ?_⟩
  have hq : Y.q.left ≫ Dd.toPre.P.A.hom = Y.H.hom := Over.w Y.q
  have hL : U ≤ Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i') := hU.trans (inf_le_inf (hle i) (hle i'))
  rw [pbT_sub, hB' i U (hU.trans inf_le_left), hB' i' U (hU.trans inf_le_right),
    hC i i' _ (Y.q.left.preimage_mono hU)]
  simp only [fun b => dlg_pull Y.q Dd.toPre.P.L (dd b) e (fun c => (he c).1) (fun c => P c b) (hP b) _ _ U hL,
    fun a => hP a U _ le_rfl f, pbT_sum, pbT_mul, pbT_constFn _ Y.q.left (O₀ := U) le_rfl, hq]
  exact alg_sum ((Y.H.hom.appLE ⊤ _ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) P C _ _

end GlobalTheory.HeatDescend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationMatrixSymmetricLocalDomain
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSRelSymm

theorem fieldCompat : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left), IsGrpPullback A G (spMap x₀) m → ∀ (w : TanM (𝟙 (Sp R)) G) (e : Fld G.left), IsInv G w e → ∀ (v : epsR K ⟶ A), IsTangent v → v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left → ∀ (dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), GlobalTheory.KS.IsInvDer v dd → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), dd (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e O f) (m ⁻¹ᵁ O) := @GlobalTheory.Heat.FieldCompat.invField_baseChange

theorem cechData : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ P.A.left), m ≫ P.A.hom = A.hom ≫ spMap x₀ → ∀ {g : ℕ} (e : Fin g → Fld P.A.left) (dd : Fin g → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ a, IsField ⊤ (e a)) → (∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → ∃ L : LB P.A.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso P.L L ∧ ∃ d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(A.left, m ⁻¹ᵁ O), ∀ φ, GlobalTheory.KS.IsDlog m L dd φ → GlobalTheory.KS.KSCoc A.hom P.A.hom m (fun r => x₀ (D r)) L.U dd d (fun a => GlobalTheory.KS.lc A.hom (fun b => -x₀ (M a b)) φ) := @GlobalTheory.KSCechData.exists_ksCoc_of_ksRel

theorem ksRel_symm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (P : Out.PolAV (Sp R)) (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) P.A)) (e : Fin g → Fld P.A.left), (∀ c, IsInv P.A (w c) (e c)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → Mᵀ = M := by
  intro R _ _ _ _ _ _ P g w e he D M hKS
  let K := FractionRing R
  let x₀ : R →+* K := algebraMap R K
  let P₀ : Out.PolAV (Sp K) := GlobalTheory.StrictPull.polPull P (spMap x₀)
  let m : P₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap x₀)
  have hm : IsGrpPullback P₀.A P.A (spMap x₀) m := isGrpPullback_pullback P.A (spMap x₀)
  have := P.isAb.comm
  have := P₀.isAb.comm
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨u, hu, hul⟩ := GlobalTheory.Heat.CoeffWt.exists_isLieBasis w
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.exists_isLieBasis_baseChange R K x₀ P.A P₀.A m hm hs g u hu
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (v a) (hv.1 a)).1
  have hcomp : ∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O) :=
    fun a => fieldCompat x₀ m hm (w a) (e a) (he a) (v a) (hv.1 a) (by rw [hvl, hul]) (dd a) (hdd a)
  obtain ⟨L, hfin, hL, haff, hPL, d, hd⟩ := cechData x₀ P m hm.1.w e dd (fun a => (he a).1) hcomp D M hKS
  have hI : LBIso P₀.L (L.pull m) :=
    LBIso.trans P₀.isLB (pull_isLB P.isLB m) (pull_isLB hL m) (GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB)
      (hPL.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl))
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ g v dd hv hdd _ m L hL hI
  obtain ⟨Θ', hsy, hΘ'⟩ := GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1
    GlobalTheory.Moduli.cube_of_isLB K P₀ g v dd hv hdd R x₀ P m L _ d _ φ hm hL haff hI (hd φ hφ) hφ
  have e1 : Θ' = -M.map x₀ := by
    rw [eq_comm, ← sub_eq_zero]
    funext b
    refine (hφ' φ hφ).2 _ ?_
    rw [GlobalTheory.LogKSBal.lc_sub]
    exact hΘ' b
  have h1 : (M.map x₀)ᵀ = M.map x₀ := by
    have h : Θ'ᵀ = Θ' := hsy
    rwa [e1, Matrix.transpose_neg, neg_inj] at h
  ext a b
  have := congrFun (congrFun h1 a) b
  simp only [Matrix.transpose_apply, Matrix.map_apply] at this
  exact IsFractionRing.injective R K this

end GlobalTheory.KSRelSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationsCharacterIsoAssociatedCoord
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PelUnifUniqCoord

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → ∀ (t : SAB H (Sp W)) (P P' : PELUnif (maximalIdeal W) t),
      ∃ e : P.D.toPre.X ≃ₗ[𝓞 E] P'.D.toPre.X, ∀ y r r', PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (e y) r' →
        Associated (r ^ 2) (r' ^ 2) := by
  intro E _ _ _ H W _ _ _ hW t P P'
  haveI : CharZero W := hW.2
  obtain ⟨m, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨e, he⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H W t t m P P' hW.1.1 hW.1.2.2.1 hW.1.2.2.2
  refine ⟨e, fun y r r' hr hr' => ?_⟩
  obtain ⟨u, hu⟩ := he y r hr
  have h1 : Associated (u * r) r' := GlobalTheory.TorRef.psiCoord_associated hu hr'
  have h2 : Associated r r' := (associated_unit_mul_left r u u.isUnit).symm.trans h1
  exact h2.pow_pow

end GlobalTheory.PelUnifUniqCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFormalEndomorphismAlgebraic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem formalEnd_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ g : G ⟶ G, IsMonHom g ∧ ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, S, hS, hnd⟩ := _root_.GlobalTheory.MumSec.main R hR D A G hG U a a' h h' hE b hb
  obtain ⟨φ, hφ, hgen⟩ := _root_.GlobalTheory.Mum.GenericRatio.exists_generic_hom R hR D A G hG U a a' h h' hE b hb N S hN hS hnd
  have := hR.1.1
  have := hR.1.2.2.1
  obtain ⟨g, hg, hgφ⟩ := _root_.GlobalTheory.Mum.semiAbelian_end_generic_extends R G hG φ hφ
  exact ⟨g, hg, GlobalTheory.T.thickening_eq_of_generic_section_ratios R hR D A G hG U a a' h h' hE b hb N S hS hnd φ hgen g hg hgφ⟩

end GlobalTheory.Mum
end

