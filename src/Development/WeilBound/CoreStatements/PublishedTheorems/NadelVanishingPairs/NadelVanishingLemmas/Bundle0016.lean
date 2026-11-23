module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0015
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleMinusExceptional
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistBelow

theorem l1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData), FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧ ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0), J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := GlobalTheory.T.effective_cartier_local_equation

theorem l2 : ∀ (X : Scheme.{0}) (M : LB X), M.IsLB → ∀ (I : X.IdealSheafData), IsGloballyGenerated (twist (idealModule I) M) → ∃ (n : ℕ) (σ : Fin n → M.Sec), (∀ (k : Fin n) (i : M.ι) (W : X.affineOpens) (h : W.1 ≤ M.U i), resG X h ((σ k).f i) ∈ I.ideal W) ∧ ∀ (x : X) (i : M.ι) (hx : x ∈ M.U i) (W : X.affineOpens) (hxW : x ∈ W.1) (a : Γ(X, W.1)), a ∈ I.ideal W → X.presheaf.germ W.1 x hxW a ∈ Ideal.span (Set.range fun k => X.presheaf.germ (M.U i) x hx ((σ k).f i)) := GlobalTheory.T.ideal_sections_locally_generated

theorem l3 : ∀ (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData) (y : Y₁) (U : Y₀.Opens) (hx : t y ∈ U) (n : ℕ) (b : Fin n → Γ(Y₀, U)), (∀ (k : Fin n) (W : Y₀.affineOpens) (h : W.1 ≤ U), resG Y₀ h (b k) ∈ I.ideal W) → (∀ (W : Y₀.affineOpens) (hxW : t y ∈ W.1) (a : Γ(Y₀, W.1)), a ∈ I.ideal W → Y₀.presheaf.germ W.1 (t y) hxW a ∈ Ideal.span (Set.range fun k => Y₀.presheaf.germ U (t y) hx (b k))) → ∀ (U' : Y₁.affineOpens) (f : Γ(Y₁, U'.1)) (hyU' : y ∈ U'.1), fnOf U'.1 (gen_mem hyU') f ≠ 0 → (I.comap t).ideal U' = Ideal.span {f} → ∀ (V : Y₁.Opens) (hV : V ≤ t ⁻¹ᵁ U) (hyV : y ∈ V), (∀ k, RegAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f)) ∧ ∃ k, UnitAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f) := GlobalTheory.T.ideal_pullback_locally_generated

theorem isGenerated_of_sections {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {n : ℕ}
    (f : Fin n → Y.functionField) (hf : ∀ k, f k ∈ D.sections) (hg : ∀ y, ∃ k, D.GeneratesAt y (f k))
    (P : LB Y) (hP : P.IsLB) (e : cls P hP = toPic D) : IsGenerated P := by
  have h := presents_toLB D
  let s : Fin n → (toLB D).Sec := fun k => h.secEquiv.symm ⟨f k, hf k⟩
  have hs : ∀ k, h.rat (s k) = f k := by
    intro k
    rw [← h.coe_secEquiv]
    simp [s]
  have hgen : IsGenerated (toLB D) := by
    refine ⟨n, s, ?_⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := hg y
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨k, (h.generatesAt_rat_iff (s k)).1 (by rw [hs]; exact hk)⟩
  have hiso : LBIso P (toLB D) := (cls_eq_iff hP (isLB_toLB D)).1 (e.trans h.toPic_eq)
  exact hgen.of_lbIso hP hiso

private theorem fnOf_div_eq_fnOf_div_of_presents {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X}
    {r : L.ι → (X.functionField)ˣ} (h : Presents D L r) (s : L.Sec) (i j : L.ι)
    (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j) :
    fnOf (L.U i) hi (s.f i) / r i = fnOf (L.U j) hj (s.f j) / r j := by
  have hij : genericPoint X ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have hr := h.isRatSec i j hij
  have hc := congrArg (fnOf (L.U i ⊓ L.U j) hij) (s.compat i j)
  simp only [map_mul] at hc
  simp only [fnOf, TopCat.Presheaf.germ_res_apply] at hc hr ⊢
  rw [hc, hr]
  have hne : (X.presheaf.germ (L.U i ⊓ L.U j) (genericPoint X) hij).hom
      (L.g i j : Γ(X, L.U i ⊓ L.U j)) ≠ 0 := by
    intro h0
    have := congrArg (fun z => z * (X.presheaf.germ (L.U i ⊓ L.U j) (genericPoint X) hij).hom
      ((L.g i j)⁻¹ : (Γ(X, L.U i ⊓ L.U j))ˣ)) h0
    simp only [zero_mul, ← map_mul, Units.mul_inv, map_one] at this
    exact one_ne_zero this
  rw [mul_div_mul_left _ _ hne]

private theorem Presents_rat_eq_fnOf_div {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X}
    {r : L.ι → (X.functionField)ˣ} (h : Presents D L r) (s : L.Sec) (j : L.ι)
    (hj : genericPoint X ∈ L.U j) :
    h.rat s = fnOf (L.U j) hj (s.f j) / r j := by
  simp only [Presents.rat, LinearMap.coe_mk, AddHom.coe_mk]
  exact fnOf_div_eq_fnOf_div_of_presents h s _ j _ hj

theorem exists_eff_isGenerated : ∀ (Y₀ Y₁ : Scheme.{0}) [IsNoetherian Y₀] [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData), FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ E : CartierDiv Y₁, E.Eff ∧ E.supp = (I.comap t).support ∧ ∀ᶠ c : ℕ in atTop, ∀ (P : LB Y₁) (hP : P.IsLB), cls P hP = c • CechPic.pull t (cls A hA.isLB) - toPic E → IsGenerated P := by
  intro Y₀ Y₁ _ _ t I hEff A hA
  obtain ⟨E, hEeff, hEsupp, hEq⟩ := l1 Y₁ (I.comap t) hEff
  refine ⟨E, hEeff, hEsupp, ?_⟩
  filter_upwards [hA.eventually_isGloballyGenerated_twist (idealModule I)] with c hc
  intro P hP hcls
  have hM : (lbPow A c).IsLB := isLB_lbPow hA.isLB c
  obtain ⟨n, σ, hσ1, hσ2⟩ := l2 Y₀ (lbPow A c) hM I hc
  have hL : ((lbPow A c).pull t).IsLB := LB.isLB_pull hM t
  have hcov : ∀ y : Y₁, ∃ j, y ∈ ((lbPow A c).pull t).U j := by
    intro y
    have : y ∈ ⨆ i, ((lbPow A c).pull t).U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨i₀, hi₀⟩ := hcov (genericPoint Y₁)
  have h := presents_ofLB hL i₀ hi₀
  have hcls' : cls P hP = toPic (ofLB hL i₀ hi₀ - E) := by
    rw [map_sub, h.toPic_eq, cls_pull hM t, cls_lbPow hA.isLB c, hcls, map_nsmul]
  have key : ∀ y : Y₁, ∃ g : (Y₁.functionField)ˣ, (ofLB hL i₀ hi₀ - E).IsEqn y g ∧
      (∀ k, RegAt y (h.rat (secPull (σ k) t) * g)) ∧ ∃ k, UnitAt y (h.rat (secPull (σ k) t) * g) := by
    intro y
    obtain ⟨j, hj⟩ := hcov y
    have hx : t y ∈ (lbPow A c).U (j PUnit.unit) := Set.mem_iInter.1 hj PUnit.unit
    have hV : ((lbPow A c).pull t).U j ≤ t ⁻¹ᵁ (lbPow A c).U (j PUnit.unit) :=
      fun z hz => Set.mem_iInter.1 hz PUnit.unit
    obtain ⟨U', f, hyU', hfnzd, hspan⟩ := hEff y
    have hf : fnOf U'.1 (gen_mem hyU') f ≠ 0 := by
      haveI : Nonempty U'.1 := ⟨⟨y, hyU'⟩⟩
      intro h0
      rw [← map_zero (fnOf U'.1 (gen_mem hyU'))] at h0
      exact nonZeroDivisors.ne_zero hfnzd (fnOf_injective _ _ h0)
    have hEy := hEq y U' f hyU' hf hspan
    have hDy := (h.isEqn j y hj).sub hEy
    obtain ⟨hreg, hunit⟩ := l3 Y₀ Y₁ t I y ((lbPow A c).U (j PUnit.unit)) hx n
      (fun k => (σ k).f (j PUnit.unit)) (fun k W hW => hσ1 k _ W hW)
      (fun W hxW a ha => hσ2 (t y) _ hx W hxW a ha) U' f hyU' hf hspan _ hV hj
    have hrat : ∀ k, h.rat (secPull (σ k) t) * ↑(frameRat _ i₀ hi₀ j / Units.mk0 _ hf) =
        fnOf _ (gen_mem hj) (Scheme.Hom.appLE t ((lbPow A c).U (j PUnit.unit)) _ hV ((σ k).f (j PUnit.unit))) /
          fnOf U'.1 (gen_mem hyU') f := by
      intro k
      rw [Presents_rat_eq_fnOf_div h _ j (gen_mem hj)]
      have he : fnOf _ (gen_mem hj) ((secPull (σ k) t).f j) =
          fnOf _ (gen_mem hj) (Scheme.Hom.appLE t ((lbPow A c).U (j PUnit.unit)) _ hV ((σ k).f (j PUnit.unit))) := rfl
      rw [he]
      have hr0 : ((frameRat _ i₀ hi₀ j : (Y₁.functionField)ˣ) : Y₁.functionField) ≠ 0 := Units.ne_zero _
      simp only [Units.val_div_eq_div_val, Units.val_mk0]
      field_simp
    exact ⟨_, hDy, fun k => by rw [hrat]; exact hreg k,
      by obtain ⟨k, hk⟩ := hunit; exact ⟨k, by rw [hrat]; exact hk⟩⟩
  apply isGenerated_of_sections (ofLB hL i₀ hi₀ - E) (fun k => h.rat (secPull (σ k) t)) _ _ P hP hcls'
  · intro k
    rw [CartierDiv.mem_sections]
    intro y
    obtain ⟨g, hg, hreg, -⟩ := key y
    exact hg.regularAt_iff.2 (hreg k)
  · intro y
    obtain ⟨g, hg, -, k, hk⟩ := key y
    exact ⟨k, hg.generatesAt_iff.2 hk⟩

end GlobalTheory.TwistBelow
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.cartier_divisor_mult_characterize : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X), (D.Eff ↔ ∀ z, 0 ≤ D.mult z) ∧ (∀ x, x ∈ D.supp ↔ ∃ z, z ⤳ x ∧ D.mult z ≠ 0) ∧ (∀ E : CartierDiv X, (∀ z, D.mult z = E.mult z) → D = E) ∧ ∀ (x : X) (g : X.functionFieldˣ), (∀ z, z ⤳ x → Scheme.ord (g : X.functionField) z = D.mult z) → D.IsEqn x g := by
  first | exact @_root_.GlobalTheory.Cartier.MultEff.eff_supp_eq_of_mult | exact _root_.GlobalTheory.Cartier.MultEff.eff_supp_eq_of_mult | (intros; apply _root_.GlobalTheory.Cartier.MultEff.eff_supp_eq_of_mult <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DiscrepancyFormulaDivisor
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.discrepancy_formula_divisor : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ), 0 < m → IsDivOfForm K η → ∀ (E : DivOver q) (w : Y) (g : Y.functionFieldˣ), E.IsAt w → G.IsEqn w g → discrep E η m g = -((G - m • K).mult w : ℚ) / m := by
  first | exact @_root_.GlobalTheory.Discrepancy.discrep_isAt_eq_neg_mult | exact _root_.GlobalTheory.Discrepancy.discrep_isAt_eq_neg_mult | (intros; apply _root_.GlobalTheory.Discrepancy.discrep_isAt_eq_neg_mult <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLift
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.isAt_lift : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) →
    IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E →
    ∀ z : X, E.IsAt z → ∃ w : Y, s w = z ∧ E'.IsAt w := by
  intro k _ X Y _ _ p s _ hbij hprop E' E hOver z hz
  obtain ⟨w, hw, hwt⟩ := GlobalTheory.T.divisor_center_proper_lift k X Y p s hbij hprop E' E hOver z
    (hz.through specializes_rfl)
  subst hw
  refine ⟨w, rfl, fun f => ⟨fun hf => ?_, hwt f⟩⟩
  obtain ⟨g, rfl⟩ := hbij.2 f
  obtain ⟨a, rfl⟩ := (hz g).1 ((hOver g).2 hf)
  exact ⟨s.stalkMap w a, (GlobalTheory.functionFieldMap_algebraMap s w a).symm⟩

end GlobalTheory.Discrepancy
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChart
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem not_mem_basicOpen_prod {Y : Scheme.{0}} {U : Y.Opens} {v : Y} (hv : v ∈ U) {c : ℕ}
    (f : Fin c → Γ(Y, U)) (s : Finset (Fin c)) :
    v ∉ Y.basicOpen (∏ i ∈ s, f i) ↔ ∃ i ∈ s, v ∉ Y.basicOpen (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.notMem_empty, false_and, exists_false, iff_false, not_not]
    rw [Scheme.basicOpen_of_isUnit Y isUnit_one]
    exact hv
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    simp only [TopologicalSpace.Opens.mem_inf, not_and_or, ih, Finset.mem_insert,
      exists_eq_or_imp]

theorem exists_isSncChart (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) (y : Y) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
      (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u := by
  classical
  obtain ⟨hreg, U, hyU, c, f, J₀, hrsp, hid⟩ := hB y
  obtain ⟨V, hV, hyV, z, e, hz, hframe⟩ := GlobalTheory.T.regular_sequence_extend_coords k Y q n y U hyU c f hrsp
  obtain ⟨w₀, u₀, hinj, hw⟩ := GlobalTheory.T.regular_sequence_prime_divisors Y y U.1 hyU c f hreg hrsp
  have hwe : ∀ i, Function.extend e w₀ (fun _ => y) (e i) = w₀ i :=
    fun i => e.injective.extend_apply _ _ i
  have hue : ∀ i, Function.extend e u₀ (fun _ => 1) (e i) = u₀ i :=
    fun i => e.injective.extend_apply _ _ i

  have hB' : ∀ v, v ∈ U.1 → (v ∈ B ↔ ∃ i ∈ J₀, v ∉ Y.basicOpen (f i)) := by
    intro v hv
    have h1 : v ∈ B ↔ v ∈ (Scheme.IdealSheafData.vanishingIdeal B).support := Iff.rfl
    rw [h1, Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hv, hid, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    exact not_mem_basicOpen_prod hv f J₀
  refine ⟨V, hyV, z, J₀.map e, Function.extend e w₀ (fun _ => y),
    Function.extend e u₀ (fun _ => 1), ⟨hframe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hue, (hw i).1, hz, fnOf_resG]
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe]; exact (hw i).2.1
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe]; exact (hw i).2.2.1
  · intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 ha)
    obtain ⟨i', -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hb)
    rw [hwe, hwe] at hab
    rw [hinj hab]
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe, hue]; exact (hw i).2.2.2.2.1
  · intro j hj v hvy hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe] at hne
    rw [hue]
    by_cases hc : Order.coheight v = 1
    · have hvU : v ∈ U.1 := hvy.mem_open U.1.isOpen hyU
      have hb : v ∈ Y.basicOpen (f i) := (hw i).2.2.2.2.2 v hvy hc hne
      rw [(hw i).1]
      exact UnitAt.ord_eq_zero ((unitAt_fnOf_iff hvU _ _).2 hb)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hc _
  · intro v hvy hc
    have hvU : v ∈ U.1 := hvy.mem_open U.1.isOpen hyU
    rw [hB' v hvU]
    constructor
    · rintro ⟨i, hi, hnot⟩
      refine ⟨e i, Finset.mem_map_of_mem e hi, ?_⟩
      rw [hwe]
      by_contra hne
      exact hnot ((hw i).2.2.2.2.2 v hvy hc hne)
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
      rw [hwe]
      exact ⟨i, hi, (hw i).2.2.2.1⟩

end GlobalTheory.Discrepancy
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PushforwardCohomologyAffine
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.PassageDown

theorem exists_cover_of_isCompact {X : Scheme.{0}} {H : LB X} (h : IsAmpleLB H) {V : X.Opens}
    (hV : IsCompact (V : Set X)) : ∃ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec),
      (∀ a, 0 < e a) ∧ (∀ a, IsAffineOpen (nonzeroLocus (σ a))) ∧ ⨆ a, nonzeroLocus (σ a) = V := by
  classical
  have key : ∀ x : V, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (lbPow H n).Sec, (x : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ V ∧ IsAffineOpen (nonzeroLocus s) := fun x => h.exists_affine_le x.2
  choose n hn s hxs hsV hsA using key
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun x : V => (nonzeroLocus (s x) : Set X))
    (fun x => (nonzeroLocus (s x)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxs _⟩)
  refine ⟨t.card, fun a => n (t.equivFin.symm a), fun a => s (t.equivFin.symm a),
    fun a => hn _, fun a => hsA _, ?_⟩
  apply le_antisymm
  · exact iSup_le fun a => hsV _
  · intro y hy
    have hy' := ht hy
    simp only [Set.mem_iUnion] at hy'
    obtain ⟨i, hi, hyi⟩ := hy'
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨j, hj⟩ : ∃ j, t.equivFin.symm j = ⟨i, hi⟩ := ⟨_, Equiv.symm_apply_apply _ _⟩
    refine ⟨j, ?_⟩
    show y ∈ nonzeroLocus (s ↑(t.equivFin.symm j))
    rw [hj]
    exact hyi

end GlobalTheory.PassageDown

private theorem passage_cohOn_lemma {X Y : Scheme.{0}} (s : Y ⟶ X) (F : Y.Modules) (V : X.Opens)
    {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hV : V ≤ ⨆ i, U i)
    (hP : CechAcyclicMod V U ((Scheme.Modules.pushforward s).obj F))
    (hF : CechAcyclicMod (s ⁻¹ᵁ V) (fun i => s ⁻¹ᵁ U i) F) (n : ℕ) :
    Nonempty (cohOn ((Scheme.Modules.pushforward s).obj F) V n ≃+ cohOn F (s ⁻¹ᵁ V) n) := by
  have hV' : s ⁻¹ᵁ V ≤ ⨆ i, s ⁻¹ᵁ U i := by
    intro y hy
    have hy' := hV hy
    rw [TopologicalSpace.Opens.mem_iSup] at hy' ⊢
    exact hy'
  let φ := cechCubePushforwardIso V U (R := ℤ) F (g := s) (fun r => by simp)
  haveI : IsIso (cechComplexMap φ.hom) :=
    isIso_cechComplexMap _ (fun t _ => ConcreteCategory.bijective_of_isIso (φ.hom.app t))
  let e1 := cechAbHEquivH' hV (cechAcyclicMod_iff.1 hP) n
  let e2 := cechAbHEquivH' hV' (cechAcyclicMod_iff.1 hF) n
  let e3 := cechAbHEquiv ℤ ((Scheme.Modules.pushforward s).obj F) V U n
  let e4 := cechAbHEquiv ℤ F (s ⁻¹ᵁ V) (fun i => s ⁻¹ᵁ U i) n
  let e5 := (HomologicalComplex.homologyMapIso (asIso (cechComplexMap φ.hom)) n).toLinearEquiv.toAddEquiv
  exact ⟨e1.symm.trans (e3.trans (e5.trans (e4.symm.trans e2)))⟩

theorem GlobalTheory.passage_down_of_twist_vanishing : ∀ (X Y : Scheme.{0}) [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), IsAmpleLB H → (∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → (∀ i, Nonempty (coh ((Scheme.Modules.pushforward s).obj F) i ≃+ coh F i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn F (s ⁻¹ᵁ U) j) := by
  intro X Y _ _ _ _ s F _ H hH hvan
  haveI : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pushforward s).obj F) :=
    GlobalTheory.QCoh.isQuasicoherent_pushforward s F
  have key : ∀ V : X.Opens, IsCompact (V : Set X) → ∀ n,
      Nonempty (cohOn ((Scheme.Modules.pushforward s).obj F) V n ≃+ cohOn F (s ⁻¹ᵁ V) n) := by
    intro V hV n
    obtain ⟨r, e, σ, he, hA, hcov⟩ := GlobalTheory.PassageDown.exists_cover_of_isCompact hH hV
    have hle : ∀ a, nonzeroLocus (σ a) ≤ V := fun a => hcov ▸ le_iSup (fun a => nonzeroLocus (σ a)) a
    have hint : ∀ t : Finset (Fin r), t.Nonempty → IsAffineOpen (⨅ a ∈ t, nonzeroLocus (σ a)) :=
      fun t ht => GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated (R := Γ(X, ⊤)) X.toSpecΓ hA t ht
    apply passage_cohOn_lemma s F V (fun a => nonzeroLocus (σ a)) hcov.ge
    · exact cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le hle hint) _
    · intro t ht q
      rw [← preimage_cechOpen, cechOpen_of_nonempty hle ht]
      exact subsingleton_cohOn_preimage_iInf_nonzeroLocus X Y s F H hH.isLB (q + 1)
        (hvan _ (Nat.succ_pos q)) r e σ he t ht
  refine ⟨fun i => ?_, fun U hU j hj => ?_⟩
  · obtain ⟨f⟩ := key ⊤ (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ) i
    exact ⟨f⟩
  · obtain ⟨f⟩ := key U hU.isCompact j
    haveI : Subsingleton (cohOn ((Scheme.Modules.pushforward s).obj F) U j) := by
      refine subsingleton_cohOn_of_cechAcyclic (ι := Unit) (U := fun _ => U)
        (le_iSup (fun _ : Unit => U) ()) ?_ (by rw [Fintype.card_unit]; exact hj)
      refine cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le (fun _ => le_rfl) ?_) _
      intro t ht
      obtain ⟨i, hi⟩ := ht
      rwa [show (⨅ _ ∈ t, U) = U from le_antisymm (biInf_le _ hi) (le_iInf₂ fun _ _ => le_rfl)]
    exact f.symm.toEquiv.subsingleton
end

