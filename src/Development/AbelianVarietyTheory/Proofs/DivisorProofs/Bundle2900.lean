module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDerivationsEqZeroKillingBothFactors
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

namespace GlobalTheory.KSBaseChangeLocal

theorem top_le_of_mem {S : Type} [CommRing S] [IsLocalRing S] {Y : Scheme.{0}} (g₀ : Sp S ⟶ Y) (V : Y.Opens)
    (hV : g₀.base (IsLocalRing.closedPoint S) ∈ V) : ⊤ ≤ g₀ ⁻¹ᵁ V := by
  intro x _
  have hs : x ⤳ IsLocalRing.closedPoint S :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
  exact (hs.map g₀.base.hom.continuous).mem_open V.isOpen hV

theorem valR_one_of_le {A : Type} [CommRing A] {Y : Scheme.{0}} (x : Sp A ⟶ Y) (O : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) : valR x O 1 = 1 := by
  simp only [valR, dif_pos h, map_one]

theorem eq_zero_of_kills_both : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (W₀ : Z.Opens), W₀ ≤ p ⁻¹ᵁ U.1 → ∀ (O : Z'.Opens), O ≤ φ ⁻¹ᵁ W₀ ⊓ p' ⁻¹ᵁ U'.1 → ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₀ : Sp S ⟶ Z'), ⊤ ≤ g₀ ⁻¹ᵁ O → ∀ (Δ : ∀ O' : Z'.Opens, Γ(Z', O') → S), (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f + f') = Δ O' f + Δ O' f') → (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f * f') = valR g₀ O' f * Δ O' f' + valR g₀ O' f' * Δ O' f) → (∀ (O₁ O₂ : Z'.Opens) (h : O₂ ≤ O₁), O₁ ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O₂ → ∀ f, Δ O₂ (resG Z' h f) = Δ O₁ f) → (∀ (O₀ : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O₀), O₀ ≤ W₀ → O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f₀, Δ O' ((φ.appLE O₀ O' h).hom f₀) = 0) → (∀ (O' : Z'.Opens) (h : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ r, Δ O' ((p'.appLE U'.1 O' h).hom r) = 0) → ∀ f, Δ O f = 0 := by
  intro Z Z' X X' p p' φ g hpb U U' hU'U W₀ hW₀ O hO S _ _ g₀ hg₀ Δ hadd hmul hres hφ hp' f
  set m := IsLocalRing.closedPoint S
  have hz : g₀.base m ∈ O := hg₀ (Set.mem_univ m)
  have hzW : φ.base (g₀.base m) ∈ W₀ := (hO hz).1
  obtain ⟨O₀, hO₀a, hzO₀, hO₀W⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) hzW
  obtain ⟨hA, hcl⟩ := _root_.GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top Z Z' X X' p p' φ g hpb U U' hU'U ⟨O₀, hO₀a⟩ (hO₀W.trans hW₀)
  set A := φ ⁻¹ᵁ O₀ ⊓ p' ⁻¹ᵁ U'.1 with hAdef
  have hzA : g₀.base m ∈ A := ⟨hzO₀, (hO hz).2⟩
  obtain ⟨h, hhle, hzD⟩ := hA.exists_basicOpen_le (V := A ⊓ O) ⟨g₀.base m, hzA, hz⟩ hzA
  set D := Z'.basicOpen h
  have hDA : D ≤ A := hhle.trans inf_le_left
  have hDO : D ≤ O := hhle.trans inf_le_right
  have htop : ⊤ ≤ g₀ ⁻¹ᵁ D := top_le_of_mem g₀ D hzD
  let δ : Γ(Z', D) →+ S := AddMonoidHom.mk' (Δ D) (hadd D hDO htop)
  have hδ : ∀ a, δ a = Δ D a := fun _ => rfl
  have h1 : Δ D 1 = 0 := by
    have e := hmul D hDO htop 1 1
    rw [_root_.mul_one, valR_one_of_le g₀ D htop, _root_.one_mul] at e
    have : Δ D 1 + Δ D 1 - Δ D 1 = Δ D 1 - Δ D 1 := by rw [← e]
    simpa using this
  have hgen : ∀ a : Γ(Z', A), Δ D (resG Z' hDA a) = 0 := by
    intro a
    have ha : a ∈ Subring.closure (Set.range (φ.appLE O₀ A inf_le_left).hom ∪
        Set.range (p'.appLE U'.1 A inf_le_right).hom) := by rw [hcl]; trivial
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨f₀, rfl⟩ | ⟨r, rfl⟩
      · rw [GlobalTheory.CechKSSmul.resG_appLE']
        exact hφ O₀ D _ hO₀W hDO htop f₀
      · rw [GlobalTheory.CechKSSmul.resG_appLE']
        exact hp' D _ hDO htop r
    | zero => rw [map_zero, ← hδ, map_zero]
    | one => rw [map_one, h1]
    | add x y _ _ hx hy => rw [map_add (f := _), hadd D hDO htop, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, ← hδ, map_neg, hδ, hx, neg_zero]
    | mul x y _ _ hx hy => rw [map_mul, hmul D hDO htop, hx, hy, mul_zero, mul_zero, add_zero]
  have hall : ∀ b : Γ(Z', D), Δ D b = 0 := by
    intro b
    obtain ⟨u, r, hu, hb⟩ := GlobalTheory.LogKSLoc.exists_frac ⟨A, hA⟩ ⟨D, hA.basicOpen h⟩ hDA h rfl b
    have e := hmul D hDO htop b (resG Z' hDA u)
    have e2 : Δ D (b * resG Z' hDA u) = 0 := by
      have : b * resG Z' hDA u = resG Z' hDA r := hb
      rw [this, hgen]
    rw [e2, hgen, mul_zero, zero_add] at e
    have hunit : IsUnit (valR g₀ D (resG Z' hDA u)) := by
      obtain ⟨w, hw⟩ := hu
      refine IsUnit.of_mul_eq_one (valR g₀ D (w⁻¹ : (Γ(Z', D))ˣ)) ?_
      rw [← hw, ← GlobalTheory.CechKSSmul.valR_mul_of_le g₀ D htop, Units.mul_inv, valR_one_of_le g₀ D htop]
    exact (hunit.mul_right_eq_zero).mp e.symm
  rw [← hres O D hDO le_rfl htop f]
  exact hall _

end GlobalTheory.KSBaseChangeLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueEqQuotientSectionByPowerAtField
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecQuot

open TopologicalSpace

variable {X : Scheme.{0}} {L : LB X}

abbrev ch1 (L : LB X) (j : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) j

theorem mem_finOnePowerChartOpen_iff {j : Fin 1 → L.ι} {x : X} : x ∈ ch1 L j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

theorem gm_secM_g {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z (ch1 L j ⊓ ch1 L j') ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) r z j j' hj hj').trans ?_
  rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast]

abbrev M1 (L : LB X) (k : ℕ) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))

theorem germ_finOnePowerLineBundle_transition_eq_pow {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z ((M1 L k).U j ⊓ (M1 L k).U j') ((M1 L k).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := gm_secM_g k r z j j' hj hj'

theorem lineBundlePowChartOpen_le_finOnePowerChartOpen (J : PUnit → L.ι) : powChart L J ≤ ch1 L (fun _ => J PUnit.unit) :=
  fun _ h => mem_finOnePowerChartOpen_iff.2 (mem_powChart.1 h)

def toPow {k : ℕ} (s : SecM (𝟙 X) L k) : (lbPow L k).Sec :=
  powSecOfGerm k (fun J => resG X (lineBundlePowChartOpen_le_finOnePowerChartOpen J) (s.f fun _ => J PUnit.unit)) fun y J J' hJ hJ' => by
    have e := gs_compat s (𝟙 X) y (j := fun _ => J PUnit.unit) (j' := fun _ => J' PUnit.unit)
      (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    have e2 := germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    refine (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _).trans (e.trans ?_)
    refine (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J') hJ' _).symm).trans ?_
    rw [Units.val_pow_eq_pow_val]

theorem gs_toPow {k : ℕ} (s : SecM (𝟙 X) L k) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (J : PUnit → L.ι)
    (hJ : r z ∈ powChart L J) : gs r z _ (powFn (toPow s) J) = gs r z _ (s.f fun _ => J PUnit.unit) :=
  gs_res r z (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _

theorem exists_secM_of_pow {n N : ℕ} (hn : n = N) (u : (lbPow L n).Sec) :
    ∃ c : SecM (𝟙 X) L N, ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ ch1 L j →
      gs r z _ (c.f j) = gs r z _ (powFn u (fun _ => j 0)) := by
  subst hn
  have le : ∀ j : Fin 1 → L.ι, ch1 L j ≤ powChart L (fun _ => j 0) := fun j _ h => mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 h)
  refine ⟨GlobalTheory.LBGerm.secOfGerm (M := M1 L n) (fun j => resG X (le j) (powFn u (fun _ => j 0)))
    fun y (j j' : Fin 1 → L.ι) hj hj' => ?_, fun r z j hj => gs_res r z (le j) hj _⟩
  have e := gs_powFn_compat u (𝟙 X) y _ _ (le j hj) (le j' hj')
  have e2 := germ_finOnePowerLineBundle_transition_eq_pow n (𝟙 X) y j j' hj hj'
  refine (gs_res (𝟙 X) y (le j) hj _).trans (e.trans ?_)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res (𝟙 X) y (le j') hj' _)).symm
  rw [Units.val_pow_eq_pow_val]

theorem gs_appLE₁ {Y Z : Scheme.{0}} (F : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ F ⁻¹ᵁ U) (r : Z ⟶ Y)
    (z : Z) (hz : r z ∈ V) (a : Γ(X, U)) : gs r z V ((F.appLE U V h).hom a) = gs (r ≫ F) z U a :=
  (gs_res r z h hz _).trans (gs_pull r F z U (h hz) a)

theorem valR_congr₁ {A : Type} [CommRing A] (x : Sp A ⟶ X) {U U' : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hU' : ⊤ ≤ x ⁻¹ᵁ U') (a : Γ(X, U)) (a' : Γ(X, U')) (h : ∀ z, gs x z U a = gs x z U' a') :
    valR x U a = valR x U' a' := by
  rw [valR, valR, dite_eq_left hU, dite_eq_left hU']
  refine congrArg _ (fn_ext fun z hz => ?_)
  rw [gs_appLE₁ _ _ _ _ _ _ hz, gs_appLE₁ _ _ _ _ _ _ hz]
  simp only [Category.id_comp]
  exact h z

theorem mem_of_top_le {A : Type} [CommRing A] {x : Sp A ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp A) :
    x z ∈ U := h (show z ∈ (⊤ : (Sp A).Opens) from trivial)

theorem valR_mul_pow_of_gs {A : Type} [CommRing A] (x : Sp A ⟶ X) {U V W : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (hW : ⊤ ≤ x ⁻¹ᵁ W) (c : Γ(X, U)) (f : Γ(X, V)) (s : Γ(X, W)) (m : ℕ)
    (h : ∀ z, gs x z U c = gs x z V f * gs x z W s ^ m) : valR x U c = valR x V f * valR x W s ^ m := by
  have hO : ⊤ ≤ x ⁻¹ᵁ (V ⊓ W) := fun z hz => ⟨hV hz, hW hz⟩
  have e1 : valR x V f = valR x (V ⊓ W) (resG X inf_le_left f) :=
    valR_congr₁ x hV hO _ _ fun z => (gs_res x z inf_le_left (mem_of_top_le hO z) f).symm
  have e2 : valR x W s = valR x (V ⊓ W) (resG X inf_le_right s) :=
    valR_congr₁ x hW hO _ _ fun z => (gs_res x z inf_le_right (mem_of_top_le hO z) s).symm
  have e3 : valR x U c = valR x (V ⊓ W) (resG X inf_le_left f * resG X inf_le_right s ^ m) :=
    valR_congr₁ x hU hO _ _ fun z => by
      rw [h z, gs_mul _ z _ (mem_of_top_le hO z), GlobalTheory.LBGerm.gs_pow _ z _ (mem_of_top_le hO z),
        gs_res x z inf_le_left (mem_of_top_le hO z), gs_res x z inf_le_right (mem_of_top_le hO z)]
  rw [e1, e2, e3, valR, valR, valR, dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_mul, map_mul, map_pow, map_pow]

theorem nonzeroLocus_toPow {k : ℕ} (s : SecM (𝟙 X) L k) : nonzeroLocus (toPow s) = nonzeroLocus s := by
  refine nonzeroLocus_eq_of (toPow s) _ (fun y hy => ?_) fun y J hJ => ?_
  · have ⟨j, hj⟩ : ∃ j : Fin 1 → L.ι, y ∈ ch1 L j := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j 0, mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 hj)⟩
  · have e : gs (𝟙 X) y _ ((toPow s).f J) = gs (𝟙 X) y _ (s.f fun _ => J PUnit.unit) := gs_toPow s (𝟙 X) y J hJ
    rw [e]
    exact (mem_nonzeroLocus_iff_isUnit s (k := fun _ => J PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ)).symm

theorem extend_part [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) {k : ℕ} (s : SecM (𝟙 X) L k)
    (f : Γ(X, nonzeroLocus s)) : ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N,
      ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i → r z ∈ nonzeroLocus s →
        gs r z _ (c.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  have hs' := nonzeroLocus_toPow s
  have le : ∀ J : PUnit → L.ι, nonzeroLocus (toPow s) ⊓ powChart L J ≤ nonzeroLocus s :=
    fun J => inf_le_left.trans hs'.le
  obtain ⟨N₀, hN₀⟩ := exists_sec_eq_pow_mul (m := 0) hL (toPow s) (fun J => resG X (le J) f)
    (GlobalTheory.LBGerm.mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' hy hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
      exact (gs_res (𝟙 X) y (le J) ⟨hy, hJ⟩ f).trans (gs_res (𝟙 X) y (le J') ⟨hy, hJ'⟩ f).symm)
  refine ⟨N₀, fun m N hm hN => ?_⟩
  obtain ⟨u, hu⟩ := hN₀ m hm
  obtain ⟨c, hc⟩ := exists_secM_of_pow (show 0 + k * m = N by omega) u
  refine ⟨c, fun r z i hi hz => ?_⟩
  have hJ : r z ∈ powChart L (fun _ => i) := mem_powChart.2 hi
  have hy : r z ∈ nonzeroLocus (toPow s) ⊓ powChart L (fun _ => i) := ⟨by rw [hs']; exact hz, hJ⟩
  have e := congrArg (gs r z _) (hu (fun _ => i))
  rw [gs_res r z _ hy, gs_mul r z _ hy, GlobalTheory.LBGerm.gs_pow r z _ hy, gs_res r z _ hy, gs_res r z _ hy] at e
  rw [hc r z (fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi), e, gs_toPow s r z _ hJ, _root_.mul_comm]

theorem quot_part {k : ℕ} (s : SecM (𝟙 X) L k) (m N : ℕ) (hN : N = k * m) (ρ : SecM (𝟙 X) L N) :
    ∃ f : Γ(X, nonzeroLocus s), ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i →
      r z ∈ nonzeroLocus s →
      gs r z _ (ρ.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  subst hN
  have loc : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X, X.basicOpen (s.f j)),
      resG X (X.basicOpen_le _) (ρ.f j) = a * resG X (X.basicOpen_le _) (s.f j) ^ m := fun j => by
    obtain ⟨b, hb⟩ := (show IsUnit (resG X (X.basicOpen_le (s.f j)) (s.f j)) from
      X.toRingedSpace.isUnit_res_basicOpen (s.f j)).exists_left_inv
    refine ⟨resG X (X.basicOpen_le _) (ρ.f j) * b ^ m, ?_⟩
    have key : ∀ {R : Type} [CommRing R] (x y c : R), c * y = 1 → x = x * c ^ m * y ^ m := fun x y c h => by
      rw [_root_.mul_assoc, ← _root_.mul_pow, h, _root_.one_pow, _root_.mul_one]
    exact key _ _ _ hb
  choose a ha using loc
  have hga : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ X.basicOpen (s.f j) →
      gs r z _ (ρ.f j) = gs r z _ (a j) * gs r z _ (s.f j) ^ m := fun r z j hz => by
    have e := congrArg (gs r z _) (ha j)
    have e1 := gs_res r z (X.basicOpen_le (s.f j)) hz (ρ.f j)
    have e2 := gs_res r z (X.basicOpen_le (s.f j)) hz (s.f j)
    have e3 := gs_mul r z _ hz (a j) (resG X (X.basicOpen_le (s.f j)) (s.f j) ^ m)
    have e4 := GlobalTheory.LBGerm.gs_pow r z _ hz (resG X (X.basicOpen_le (s.f j)) (s.f j)) m
    exact e1.symm.trans (e.trans (e3.trans (congrArg _ (e4.trans (congrArg (· ^ m) e2)))))
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (s.f j)) (nonzeroLocus s)
    (fun j => homOfLE (GlobalTheory.basicOpen_le_nonzeroLocus s j)) le_rfl a (fun i j => fn_ext fun y hy => by
      have hi : y ∈ ch1 L i := X.basicOpen_le _ hy.1
      have hj : y ∈ ch1 L j := X.basicOpen_le _ hy.2
      refine (gs_res (𝟙 X) y inf_le_left hy (a i)).trans
        (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy (a j)).symm)
      have u : IsUnit (gs (𝟙 X) y _ (s.f i) ^ m) :=
        ((GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y _ hi _).2 hy.1).pow m
      refine u.mul_right_cancel ?_
      rw [← hga (𝟙 X) y i hy.1, gs_compat ρ (𝟙 X) y hi hj, gs_compat s (𝟙 X) y hi hj, hga (𝟙 X) y j hy.2,
        germ_finOnePowerLineBundle_transition_eq_pow (k * m) (𝟙 X) y i j hi hj, germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y i j hi hj, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val]
      ring)
  refine ⟨f, fun r z i hi hz => ?_⟩
  have hz' : r z ∈ X.basicOpen (s.f fun _ => i) := (mem_nonzeroLocus_iff_basicOpen s (k := fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi)).1 hz
  rw [hga r z _ hz', ← hf (fun _ => i)]
  exact congrArg (· * _) (gs_res r z (GlobalTheory.basicOpen_le_nonzeroLocus s _) hz' f)

theorem valR_secM_eq_mul_pow : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j₀ → ∀ (k : ℕ) (s : SecM (𝟙 X) L k), ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus s → (∀ f : Γ(X, Out.nonzeroLocus s), ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N, valR ξ _ (c.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m) ∧ ∀ m N : ℕ, N = k * m → ∀ ρ : SecM (𝟙 X) L N, ∃ f : Γ(X, Out.nonzeroLocus s), valR ξ _ (ρ.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m := by
  intro X _ _ L hL F _ ξ j₀ hj₀ k s hs
  have hc : ⊤ ≤ ξ ⁻¹ᵁ ch1 L (fun _ => j₀) := fun z hz => mem_finOnePowerChartOpen_iff.2 (hj₀ hz)
  refine ⟨fun f => ?_, fun m N hN ρ => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := extend_part hL s f
    refine ⟨m₀, fun m N hm hN => ?_⟩
    obtain ⟨c, hc'⟩ := hm₀ m N hm hN
    exact ⟨c, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hc' ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩
  · obtain ⟨f, hf⟩ := quot_part s m N hN ρ
    exact ⟨f, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hf ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩

end GlobalTheory.SecQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldEqBasicOpenExtension
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem valR_cst_eq_iota : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R) (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* FractionRing Ω), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = algebraMap Ω (FractionRing Ω) (φ r)) → ∀ (O : G.left.Opens) (h : O ≤ G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ O → ∀ θ, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') O (GlobalTheory.HeatV.cst G.hom _ h θ) = iota θ := by
  intro R _ G Ω _ _ φ x' hx c iota hiota O h hO θ
  rw [GlobalTheory.CechKSSmul.valR_appLE_comp _ G.hom (GlobalTheory.HeatV.bo R c).1 O h hO θ]
  have hz : (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)) := by
    rw [Category.assoc, hx]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have h' : ⊤ ≤ ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom) ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 :=
    fun p hp => h (hO hp)
  set s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c with hs
  set z := (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom with hzdef
  let F : Γ(Sp R, (Sp R).basicOpen s) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
  have hF : ∀ θ, valR z (GlobalTheory.HeatV.bo R c).1 θ = F θ := fun θ => by
    simp only [valR, dif_pos h']; rfl
  suffices e : F = iota by rw [hF]; exact DFunLike.congr_fun e θ
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (S := Γ(Sp R, (Sp R).basicOpen s)) ?_
  ext y0
  obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = y0 :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y0, by simp⟩
  have e1 : algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      GlobalTheory.HeatV.resV R c r := rfl
  change F (GlobalTheory.HeatV.resV R c r) = iota (GlobalTheory.HeatV.resV R c r)
  rw [hiota]
  show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom
    ((z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom (GlobalTheory.HeatV.resV R c r)) = _
  have e2 : (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op ≫ z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h' =
      z.appTop := by
    exact (Scheme.Hom.map_appLE z h' _).trans (Scheme.Hom.appLE_eq_app z)
  have e3 : (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
      (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      z.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← e2]; rfl
  rw [show (GlobalTheory.HeatV.resV R c r) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) from rfl, e3]
  rw [hz]
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [n]
  simp

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueOfSectionPullbackScalarMultiple
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecScalVal

theorem val_of_secScal : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) (c : Γ(Y, ⊤)), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ c → ∀ (F : Type) [CommRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → valR (ξ ≫ f₂) _ (σ.f fun _ => i) = valR ξ ⊤ c * valR ξ _ (s.f fun _ => i) := by
  intro X₂ Y L₂ f₂ k σ s c hs F _ ξ i hi
  have hc := hs (fun _ => i) (fun _ => i) (fun a b _ => by rcases a <;> rcases b <;> rfl)
  have hW : ⊤ ≤ ξ ⁻¹ᵁ (LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) (fun _ => i)) := by
    intro y _
    have hy := hi (Set.mem_univ y)
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · simpa using hy
    · simpa using hy
  have hv := congrArg (valR ξ _) hc
  rw [GlobalTheory.ZH.CrdCalc.valR_mul ξ _ hW] at hv
  erw [GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW, GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW,
    GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW] at hv
  have hσ : ⊤ ≤ ξ ⁻¹ᵁ f₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) :=
    hW.trans (ξ.preimage_mono (inf_le_right.trans
      (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)))
  have hσ' : ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) := hσ
  rw [GlobalTheory.ZH.CrdCalc.valR_eq ξ _ hσ] at hv
  exact (GlobalTheory.ZH.CrdCalc.valR_eq (ξ ≫ f₂) _ hσ' _).trans hv

end GlobalTheory.SecScalVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueRelationSectionsThroughGeneratingIso
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
namespace GlobalTheory.GermVal

theorem valR_linComb_germ : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w k σ' s H F _ _ ξ i j h2 h1
  have m2 : f₂ (ξ (IsLocalRing.closedPoint F)) ∈ L₂.U i := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₂) _).1 h2
  have m1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ L₁.U j := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₁) _).1 h1
  have hy := H (ξ (IsLocalRing.closedPoint F)) i j m2 m1
  have a2 : ξ (IsLocalRing.closedPoint F) ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) :=
    Set.mem_iInter.2 fun _ => m2
  have aw : ξ (IsLocalRing.closedPoint F) ∈
      ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => m2, Set.mem_iInter.2 fun _ => m1⟩
  have a1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ (LB.LinComb L₁ (K := Fin 1) (fun _ => 𝟙 X₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    Set.mem_iInter.2 fun _ => m1
  rw [GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ a2, GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ aw,
    GlobalTheory.ZH.ThetaData.valR_eq_gs (ξ ≫ f₁) _ a1, gs_stalkMap ξ _ _ a2, gs_stalkMap ξ _ _ aw,
    gs_comp ξ f₁ _ _ a1, hy]
  simp only [map_mul, map_pow]

end GlobalTheory.GermVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueSectionInChartOfFrameValue
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

theorem valR_of_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 X) L x g k σ ω → ∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → valR x _ (σ.f fun _ => i) = ω * (valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val) ^ k := by
  intro X L hL Ω _ _ x g k σ ω hv i hi
  set z := IsLocalRing.closedPoint Ω
  have hxz : x z ∈ L.U i := hi (show z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  obtain ⟨J, hJ, hJi⟩ := exists_good L hL z (K := PUnit) (fun _ => x ≫ 𝟙 X) (fun _ => i) (fun _ _ _ => rfl)
    (fun _ => hxz)
  have h := hv (Sp Ω) (𝟙 _) z J hJ
  have e1 : J ((𝟙 (Sp Ω) ≫ x) ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  have e2 : J (𝟙 (Sp Ω) ≫ x ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  rw [sval_of σ (𝟙 _ ≫ x) z J (fun _ => i) (fun _ => e1), val_of g (𝟙 _) z J (fun _ => i) (fun _ => e2),
    Category.id_comp] at h
  have m1 : (𝟙 (Sp Ω)) z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have a1 : valR x _ (σ.f fun _ => i) =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs x z _ (σ.f fun _ => i)) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs x _ (Set.mem_iInter.2 fun _ => hxz) _
  have mG : (𝟙 (Sp Ω)) z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => i) := Set.mem_iInter.2 fun _ => hxz
  have a2 : valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) _ mG _
  have a3 : gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val = (gm (𝟙 (Sp Ω)) z _ (g.s fun _ => i)).val :=
    gs_unit _ _ _ mG _
  have hω : (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)) = ω := by
    rw [← GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) ⊤ m1, GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_rfl]
    simp [GlobalTheory.ZH.CrdCalc.valHom, Scheme.Hom.appLE]
  rw [a1, a2, a3]
  have h' := congrArg (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom h
  rw [map_mul, hω, Units.val_pow_eq_pow_val, map_pow] at h'
  exact h'

end GlobalTheory.HeatV
end
end

