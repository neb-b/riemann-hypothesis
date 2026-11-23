module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationDescendedClosedTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDegDataIsoOfGaloisDescendedGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltAtPointsNotContainingCentre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem qNum_principal_add_nsmul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) {N : LB X} (hN : IsAmpleLB N) {A : CartierDiv X} (e : toPic A = cls N hN.isLB)
    (l : ℕ) {g : X.functionFieldˣ} (hg : (g : X.functionField) ∈ (l • A).sections) :
    QNum p N l (qWeil (CartierDiv.principal g + l • A) 1) := by
  letI := algebraΓOfHom p
  refine ⟨1, CartierDiv.principal g + l • A, one_pos, CartierDiv.mem_sections_iff_eff.1 hg, rfl, ?_⟩
  intro C hC
  have e1 : toPic (CartierDiv.principal g + l • A) = l • cls N hN.isLB := by
    rw [map_add (f := _), map_nsmul, toPic_principal, e, zero_add]
  have e2 : cls (toLB (CartierDiv.principal g + l • A)) (isLB_toLB _) =
      cls (lbPow N l) (isLB_lbPow hN.isLB l) := by
    rw [← toPic_apply, e1, GlobalTheory.CechPic.cls_lbPow hN.isLB]
  rw [interNumRed_one_congr _ _ e2 C, hC.interNumRed_lbPow hN hN.isLB l]
  push_cast
  ring

theorem exists_step_divisor : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h → (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => N : ℤ) → ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p N h B ∧ Off B z ∧ (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧ (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  intro hPr _ _ X _ _ _ p n hproj hdim Δ m G N D P z k h hΔ hklt hm hG hN hD hP hk hZ hz hh hnum
  letI := algebraΓOfHom p
  obtain ⟨A, hA⟩ := toPic_surjective (X := X) (cls N hN.isLB)
  have hAN : cls (toLB A) (isLB_toLB A) = cls N hN.isLB := by rw [← toPic_apply, hA]
  have hAamp : IsAmpleLB (toLB A) :=
    (isAmpleLB_congr (isLB_toLB A) hN.isLB ((GlobalTheory.CechPic.cls_eq_iff _ _).1 hAN)).2 hN
  have hcongr : (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A) =
      interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => N := by
    rw [interNumRed_def, interNumRed_def, interNumSub_def, interNumSub_def, interNumOn_def,
      interNumOn_def]
    exact interNum_congr_cls (k := ℂ) (F := _) (fun _ => isLB_toLB A) (fun _ => hN.isLB)
      fun _ => hAN
  have hnumA : (P.card : ℚ) * (k : ℚ) ^ k <
      h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) := by
    rw [hcongr]; exact hnum
  obtain ⟨l₁, hl₁⟩ :=
    GlobalTheory.GeneralLift.exists_lift_klt hPr X p n hproj hdim Δ D m G A z hm hG hD hAamp
  obtain ⟨l, hll, hl, f₀, hf₀, hgen, δ₀, hδ0, hδ1, hmain⟩ :=
    GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step hPr X p n hproj hdim Δ m G A D P z k h hΔ hklt hm hG hAamp hD hP hk hZ hz hh
      hnumA l₁
  obtain ⟨u, hu, hvan, hoff⟩ := hl₁ l hll f₀ hf₀
  have hgen' : (l • A).GeneratesAt z (f₀ + u) :=
    GlobalTheory.Cartier.CommonEqn.generatesAt_add hgen hvan
  set g : X.functionFieldˣ := Units.mk0 (f₀ + u) hgen'.ne_zero with hg_def
  have hgval : (g : X.functionField) = f₀ + u := rfl
  have hgmem : (g : X.functionField) ∈ (l • A).sections := by
    rw [hgval]; exact add_mem hf₀ hu
  have hlpos : (0 : ℚ) < l := lt_trans hh hl
  have hEff : (CartierDiv.principal g + l • A).Eff := CartierDiv.mem_sections_iff_eff.1 hgmem
  have hzs : z ∉ (CartierDiv.principal g + l • A).supp := by
    rw [CartierDiv.notMem_supp_iff]
    have h1 : (CartierDiv.principal g).GeneratesAt z (g : X.functionField)⁻¹ :=
      CartierDiv.isEqn_iff_generatesAt_inv.1 (CartierDiv.isEqn_principal g z)
    have h2 : (l • A).GeneratesAt z (g : X.functionField) := by rw [hgval]; exact hgen'
    have h3 := h1.mul h2
    rwa [inv_mul_cancel₀ (Units.ne_zero g)] at h3
  refine ⟨(h / l) • qWeil (CartierDiv.principal g + l • A) 1, δ₀, hδ0, hδ1, ?_, ?_, ?_, ?_⟩
  · have h1 := qNum_principal_add_nsmul p hN hA l hgmem
    have h2 := qNum_smul X p hproj N (l : ℚ) (h / l) _ (div_nonneg hh.le hlpos.le) h1
    rwa [div_mul_cancel₀ h hlpos.ne'] at h2
  · intro w hw
    have h0 := (off_qWeil_iff_notMem_supp X (CartierDiv.principal g + l • A) 1 z hEff one_pos).2 hzs
    rw [Pi.smul_apply, h0 w hw, smul_zero]
  · intro δ h0 h1 x hx
    exact hmain u hu hvan g hgval δ h0 h1 x hx
  · intro y hy a ha hka
    exact hoff g hgval y hy a (h / l) ha ((div_lt_one hlpos).2 hl) hka

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltPointsNumericallyMultiple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AmpleStep

variable {X : Scheme.{0}} [IsIntegral X]

theorem generatesAt_add_vanishesAt {D : CartierDiv X} {x : X} {f u : X.functionField}
    (hf : D.GeneratesAt x f) (hu : D.VanishesAt x u) : D.GeneratesAt x (f + u) := by
  obtain ⟨e, he⟩ := D.exists_isEqn x
  rw [he.generatesAt_iff] at hf ⊢
  rw [he.vanishesAt_iff] at hu
  obtain ⟨a, ha, hae⟩ := hf
  obtain ⟨b, hb, hbe⟩ := hu
  refine ⟨a + b, ?_, by rw [map_add (f := _), hae, hbe, add_mul]⟩
  by_contra hn
  have h1 : a + b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hn
  have h2 : a ∈ IsLocalRing.maximalIdeal _ := by
    have := Ideal.sub_mem _ h1 hb
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 ha

theorem eff_nsmul {D : CartierDiv X} (hD : D.Eff) (r : ℕ) : (r • D).Eff := by
  induction r with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ r ih => rw [succ_nsmul]; exact ih.add hD

variable [IsLocallyNoetherian X]

theorem mult_nsmul (E : CartierDiv X) (r : ℕ) (z : X) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero =>
    have h₀ := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h₀
    rw [zero_nsmul]
    push_cast
    omega
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

end GlobalTheory.AmpleStep


open GlobalTheory.AmpleStep in
theorem GlobalTheory.AmpleStep.exists_divisor : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) →
      IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k →
      topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
      (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
      ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p (toLB A) h B ∧ Off B z ∧
        (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧
        (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  intro hP X _ _ _ p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.GeneralLift.exists_lift_klt hP X p n hp hn Δ D m G A z hm hG hD hA
  obtain ⟨l, hll, hhl, f₀, hf₀, hgen, δ₀, hδ0, hδ1, hnk⟩ :=
    GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step hP X p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum l₁
  obtain ⟨u, hu, huz, hukl⟩ := hl₁ l hll f₀ hf₀
  have hgz : (l • A).GeneratesAt z (f₀ + u) := generatesAt_add_vanishesAt hgen huz
  let g : X.functionFieldˣ := Units.mk0 (f₀ + u) hgz.ne_zero
  have hgv : (g : X.functionField) = f₀ + u := rfl
  have hEeff : (CartierDiv.principal g + l • A).Eff :=
    CartierDiv.mem_sections_iff_eff.1 (hgv ▸ Submodule.add_mem _ hf₀ hu)
  have hl0 : (0 : ℚ) < l := hh.trans hhl
  have hlpos : 0 < l := by exact_mod_cast hl0
  refine ⟨(h / l) • qWeil (CartierDiv.principal g + l • A) 1, δ₀, hδ0, hδ1, ?_, ?_,
    fun δ hδ hδ' x hx => hnk u hu huz g hgv δ hδ hδ' x hx, ?_⟩
  · obtain ⟨a, b, ha0, hb0, hab⟩ : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ h = a / b := by
      have hnum0 : 0 < h.num := Rat.num_pos.2 hh
      refine ⟨h.num.toNat, h.den, by omega, h.den_pos, ?_⟩
      have e1 : ((h.num.toNat : ℕ) : ℚ) = (h.num : ℚ) := by
        have : ((h.num.toNat : ℕ) : ℤ) = h.num := Int.toNat_of_nonneg hnum0.le
        exact_mod_cast this
      rw [e1, Rat.num_div_den]
    refine ⟨b * l, a • (CartierDiv.principal g + l • A), Nat.mul_pos hb0 hlpos, eff_nsmul hEeff a,
      ?_, fun C hC => ?_⟩
    · funext x
      simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul, hab]
      push_cast
      field_simp
    · have hcls : cls (toLB (a • (CartierDiv.principal g + l • A))) (isLB_toLB _) =
          (a * l) • cls (toLB A) (isLB_toLB A) + 0 • cls (toLB A) (isLB_toLB A) := by
        rw [← toPic_apply, ← toPic_apply]
        simp [map_nsmul, toPic_principal, smul_smul, mul_comm]
      have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB A)
        (isLB_toLB A) (a * l) 0 C hC hcls
      rw [e, hab]
      push_cast
      field_simp
      ring
  · have hoff : Off (qWeil (CartierDiv.principal g + l • A) 1) z :=
      (off_qWeil_iff_notMem_supp X _ 1 z hEeff one_pos).2 (by
        obtain ⟨e, he⟩ := (l • A).exists_isEqn z
        rw [CartierDiv.notMem_supp_iff, ((CartierDiv.isEqn_principal g z).add he).generatesAt_iff,
          one_mul, Units.val_mul, hgv]
        exact (he.generatesAt_iff).1 hgz)
    intro w hw
    simp [hoff w hw]
  · intro y hy a ha hk'
    exact hukl g hgv y hy a (h / l) ha ((div_lt_one hl0).2 hhl) hk'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

open GlobalTheory.EndLoc

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{0}}

def opBar (D : Datum p) (a : D.Oᵐᵒᵖ) : D.Oᵐᵒᵖ := MulOpposite.op ((D.star a.unop).unop)

theorem opBar_add (D : Datum p) (a b : D.Oᵐᵒᵖ) : opBar D (a + b) = opBar D a + opBar D b := by
  simp [opBar]

theorem isRAct_of_oActN (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) :
    IsRAct A (fun a : D.Oᵐᵒᵖ => act.act a.unop) :=
  ⟨fun _ => act.hom _, act.one, fun a b => act.mul b.unop a.unop, fun a b => act.add _ _⟩

theorem adj_of_rosatiFor (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left)
    (h : RosatiFor D act P) : Adj A P (opBar D) (fun a : D.Oᵐᵒᵖ => act.act a.unop) :=
  fun a => h a.unop

def oActNOfIsRAct (D : Datum p) {A : Over S} [GrpObj A] {act : D.Oᵐᵒᵖ → (A ⟶ A)} (h : IsRAct A act) :
    OActN D.O A where
  act c := act (MulOpposite.op c)
  hom c := h.1 _
  one := h.2.1
  mul b c := h.2.2.1 (MulOpposite.op c) (MulOpposite.op b)
  add b c := h.2.2.2 _ _

theorem rosatiFor_of_adj (D : Datum p) {A : Over S} [GrpObj A] {act : D.Oᵐᵒᵖ → (A ⟶ A)} (h : IsRAct A act)
    (P : LB (G2 A).left) (ha : Adj A P (opBar D) act) : RosatiFor D (oActNOfIsRAct D h) P :=
  fun c => ha (MulOpposite.op c)

theorem exists_finite_rep_oActN_rosati : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (c : SiegPre h M ζ s₁), Out.RelAmple c.A c.diag → ∃ (H : Scheme.{0}) (πH : H ⟶ S) (AH : Over H) (_ : GrpObj AH) (_ : IsCommMonObj AH) (φH : AH.left ⟶ c.A.left) (φ₂H : (G2 AH).left ⟶ (G2 c.A).left) (actH : OActN D.O AH), IsFinite πH ∧ IsAbelianScheme AH ∧ IsGrpPullback AH c.A πH φH ∧ IsSquare φH φ₂H ∧ RosatiFor D actH (c.P.pull φ₂H) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → ∃! z : T ⟶ H, z ≫ πH = g ∧ ∃ ψ : AT.left ⟶ AH.left, IsGrpPullback AT AH z ψ ∧ ψ ≫ φH = φ ∧ ∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actH.act a).left := by
  intro p _ D h M B _ ζ S _ s₁ c hample
  obtain ⟨r, e, W, d, hspan, hpos, hd, hsum⟩ := GlobalTheory.T.exists_spanning_posDef_relation_harrisTaylorOrder p D
  obtain ⟨R, hfin, -⟩ := GlobalTheory.T.adjointActions_order_finite_unramified_scheme S c.A c.P c.ab c.isLB c.rig₁ c.rig₂ c.symm hample D.Oᵐᵒᵖ (opBar D) r e W d
    (opBar_add D) hspan hpos hd hsum
  have hcomm : IsCommMonObj R.AH := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback R.pb
  refine ⟨R.H, R.π, R.AH, R.grp, hcomm, R.φ, R.φ₂, oActNOfIsRAct D R.isAct, hfin,
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab R.pb, R.pb, R.sq, rosatiFor_of_adj D R.isAct _ R.adj, ?_⟩
  intro T g AT _ φ φ₂ act hpb hsq hros
  obtain ⟨z, ⟨hz, ψ, hψ, hψφ, hψa⟩, huniq⟩ :=
    R.rep T g AT φ φ₂ _ hpb hsq (isRAct_of_oActN D act) (adj_of_rosatiFor D act _ hros)
  refine ⟨z, ⟨hz, ψ, hψ, hψφ, fun a => hψa (MulOpposite.op a)⟩, ?_⟩
  rintro z' ⟨hz', ψ', hψ', hψφ', hψa'⟩
  exact huniq z' ⟨hz', ψ', hψ', hψφ', fun a => hψa' a.unop⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAbelianLocusChartRing
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

namespace GlobalTheory.KSAbLocus

theorem tanBasis_of_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    (t : SAB H (Sp R)) {n : ℕ} (b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) {T : Type} [CommRing T]
    (φ : R →+* T) :
    (∀ i, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) (spMap (dualMap φ) ≫ (tv (b i)).left)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ 𝟙 (Sp R)) (fun i => spMap (dualMap φ) ≫ (tv (b i)).left) a w := by
  refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t φ (𝟙 (Sp R)) n _ (fun i => GlobalTheory.LieMet.isTan_tv (b i)) ?_
  intro w hw
  refine ⟨b.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
  · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
    rw [GlobalTheory.LieMet.isComb_iff]
    exact (b.sum_repr _).symm
  · have h := (GlobalTheory.LieMet.isComb_iff b a (GlobalTheory.LieMet.tanOf hw)).1 ha
    rw [h]
    ext i
    simp [Finsupp.single_apply]

theorem exists_isKS_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁, IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ htt hab n v' D DV
  let U : (Sp R).affineOpens := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  let ρ : R →+* Γ(Sp R, U.1) := ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hc : spMap ρ ≫ 𝟙 (Sp R) = chart U := by
    rw [Category.comp_id]
    show Spec.map _ = U.2.fromSpec
    rw [← (isAffineOpen_top (Sp R)).map_fromSpec U.2 (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op from rfl]
    erw [Spec.map_comp]
    rfl
  obtain ⟨hv, hb⟩ := GlobalTheory.KSAbLocus.tanBasis_of_basis t v' ρ
  rw [hc] at hv hb
  obtain ⟨PP', cub, sym, adj, prim, mm, -⟩ := sabPull proved_CubePullSt (chart U) t
  have h2 : (U.1 : (Sp R).Opens) = PrimeSpectrum.basicOpen (∏ i, tt i) :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) (∏ i, tt i)
  have h4 : ∀ q : Sp R, q ∈ ((U.1 : (Sp R).Opens) : Set (Sp R)) → ∏ i, tt i ∉ q.asIdeal := by
    intro q hq
    rw [h2] at hq
    exact hq
  have hx : ∀ s, ∏ i, tt i ∉ ((chart U) s).asIdeal := fun s =>
    h4 _ (by rw [← U.2.range_fromSpec]; exact ⟨s, rfl⟩)
  obtain ⟨hP, hA, hK⟩ := _root_.GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus E H R t P m tt htt hab _ (chart U) _ hx ⟨mm⟩
  exact _root_.GlobalTheory.KSOpen.exists_isKS_of_pull E H (Sp R) t _ U le_rfl _ ⟨mm⟩ hP hA hK n _ hv hb DV

end GlobalTheory.KSAbLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverUnitaryPELTypeFiniteExt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_odd_prime_isUnit_in_localRing (R : Type) [CommRing R] [IsLocalRing R] :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  have h : IsUnit ((2 : R) * (3 : ℕ) + (-1) * (5 : ℕ)) := by
    have : (2 : R) * (3 : ℕ) + (-1) * (5 : ℕ) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, Nat.prime_three, by decide, isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, Nat.prime_five, by decide, isUnit_of_mul_isUnit_right h⟩

theorem exists_labCover_of_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Nonempty (LabCover D') := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP
  have := hR.1.1
  have := hR.2
  obtain ⟨n, hn, ho, hu⟩ := exists_odd_prime_isUnit_in_localRing R
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have hloc : IsLocalHom φ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ (maximalIdeal V).comap φ := by rw [hc]; exact hna
    exact h1 ha⟩
  obtain ⟨DV, ⟨hDV⟩⟩ := GlobalTheory.MumPull.exists_pull R V φ hφ hloc D
  obtain ⟨_, oV, hPV⟩ := GlobalTheory.Mum.pelOK_of_isPullDeg R hR E H Dm D o hP V φ hφ DV ⟨hDV⟩
  have hXV : Nontrivial DV.toPre.X := hDV.xe.toEquiv.nontrivial
  obtain ⟨V', _, _, _, io, D', G', _, _, A', hV', hio, hfin, hD', hG', hU', hS'⟩ := GlobalTheory.T.exists_mumfordUniformisation_unitaryTypeTrait V hV E H Dm DV oV hXV hPV
  have hioloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  obtain ⟨R₁, _, _, _, ρ₁, D₁, A, lab, hf₁, hD₁, hS, h1, h2⟩ := GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension R hR D n hn ho hu V' hV' (io.comp φ)
    (hio.comp hφ) inferInstance D' G' A'
    (GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R V V' φ io _ _ _ hio ⟨hDV⟩ hD') hG' hU' hS'
  have hR₁ : Base R₁ := ⟨hf₁.1, charZero_of_injective_ringHom hf₁.2.1⟩
  have := hR₁.2
  obtain ⟨R₂, _, _, _, ρ₂, C, a, hf₂, hfib⟩ := GlobalTheory.T.exists_uniformised_cover_finite_ext_of_symmetric R₁ hR₁ A hS
  have hR₂ : Base R₂ := ⟨hf₂.1, charZero_of_injective_ringHom hf₂.2.1⟩
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ ρ₂ hf₂.2.1 (hf₂.2.2.to_isIntegral.isLocalHom hf₂.2.1) D₁
  obtain ⟨lab₂, k1, k2⟩ := _root_.GlobalTheory.Mum.exists_labels_finExt_galEqN R₁ hR₁ D₁ A lab n h1 h2 R₂ ρ₂ hf₂ D₂ hD₂ C.A a hfib hn.pos
  have hu₂ : IsUnit (n : R₂) := by simpa using hu.map (ρ₂.comp ρ₁)
  exact ⟨R₂, _, _, _, ρ₂.comp ρ₁, D₂, ⟨hf₂.1, hf₂.2.1.comp hf₁.2.1, hf₂.2.2.comp hf₁.2.2⟩,
    GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ₁ ρ₂ _ _ _ hf₂.2.1 hD₁ hD₂,
    _root_.GlobalTheory.Mum.UCover.labCover R₂ hR₂ D₂ C lab₂ n hn ho hu₂ k1 k2⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_theta_sum_common_sign_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  first | exact @GlobalTheory.GSep.twistAtEach_exists | exact GlobalTheory.GSep.twistAtEach_exists | (intros; apply GlobalTheory.GSep.twistAtEach_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOfGalAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_galAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → Has D := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ hS' U' a G _ _ β hS pb hinv
  obtain ⟨A, gen, κ, hgen, hκ, hLA⟩ := _root_.GlobalTheory.Mum.GenDesc.polarisedGeneric R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.GaloisPackageDescent.exists_cp R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv
  have hAP := _root_.GlobalTheory.Mum.lbIso_generic_descend R hR R' ρ hfin G' G β hS' hS pb A gen κ hgen hκ U'.LG.L U'.LG.isLB hLA P hP
  have hev := _root_.GlobalTheory.Mum.EvenDesc.evenOn_of_galAct R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv P hP
  obtain ⟨D₁, U₁, hLG, -⟩ := _root_.GlobalTheory.Mum.exists_unif_even R hR G P hS hev A gen hgen hAP
  have hP₁ : LBIso U'.LG.L (U₁.LG.L.pull β) := by rw [hLG]; exact hP
  have h₁ := _root_.GlobalTheory.Mum.nonempty_isPullDeg_of_galAct R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv A D₁ U₁ hP₁
  exact _root_.GlobalTheory.Mum.has_pull R R (RingHom.id R) hR.1 hR.1 Function.injective_id inferInstance D₁ D h₁
    ⟨G, inferInstance, inferInstance, A, hS, ⟨U₁⟩⟩

end GlobalTheory.Mum
end

