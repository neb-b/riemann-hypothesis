module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumKernelBallMeasureLeIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitaryKernelLeExpPowEight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroAffineMilnorSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

open TopologicalSpace

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    (h : CechPic.pull f (cls L hL) = 0) : ∃ b : ∀ i, Γ(Y, f ⁻¹ᵁ L.U i)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : L.ι), f (r z) ∈ L.U i → f (r z) ∈ L.U j →
        gm r z _ (b i) = gm (r ≫ f) z _ (L.g i j) * gm r z _ (b j) := by
  rw [← cls_pull hL f (pull_isLB hL f)] at h
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 h
  have le : ∀ i, f ⁻¹ᵁ L.U i ≤ (L.pull f).U (fun _ ↦ i) := fun i y hy ↦ mem_pull.2 hy
  refine ⟨fun i ↦ res (le i) (t.s fun _ ↦ i), fun Z r z i j hi hj ↦ ?_⟩
  have mi : r z ∈ (L.pull f).U (fun _ ↦ i) := mem_pull.2 hi
  have mj : r z ∈ (L.pull f).U (fun _ ↦ j) := mem_pull.2 hj
  have hm : r z ∈ (L.pull f).U (fun _ ↦ i) ⊓ (L.pull f).U (fun _ ↦ j) := ⟨mi, mj⟩
  have e := congrArg (gm r z _) (ht (fun _ ↦ i) (fun _ ↦ j))
  rw [map_mul, gm_res r z _ hm, gm_res r z _ hm, gm_pull_g L f r z _ _ mi mj] at e
  rw [gm_res r z (le i) hi, gm_res r z (le j) hj]
  exact e

theorem eq_zero_of_square {X X₁ X₂ X₀ : Scheme.{0}} (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (g₁ : X₀ ⟶ X₁) (g₂ : X₀ ⟶ X₂)
    (w : g₁ ≫ f₁ = g₂ ≫ f₂)
    (inj : ∀ (W : X.Opens) (a b : Γ(X, W)), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b)
    (ex : ∀ (W : X.Opens) (h₂ : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W))
      (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)), g₁.appLE _ _ le_rfl a₁ = g₂.appLE _ _ h₂ a₂ →
        ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂)
    (lift : Function.Surjective (Units.map g₂.appTop.hom.toMonoidHom))
    (c : Pic X) (h₁ : CechPic.pull f₁ c = 0) (h₂ : CechPic.pull f₂ c = 0) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨b₁, hb₁⟩ := exists_units_of_pull_eq_zero hL f₁ h₁
  obtain ⟨b₂, hb₂⟩ := exists_units_of_pull_eq_zero hL f₂ h₂
  have le : ∀ W : X.Opens, g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := fun W ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  have injU : ∀ (W : X.Opens) (a b : Γ(X, W)ˣ), pullU f₁ W a = pullU f₁ W b → pullU f₂ W a = pullU f₂ W b → a = b :=
    fun W a b e₁ e₂ ↦ Units.ext (inj W _ _ (congrArg Units.val e₁) (congrArg Units.val e₂))
  have exU : ∀ (W : X.Opens) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)ˣ) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)ˣ),
      res le_rfl (pullU g₁ _ a₁) = res (le W) (pullU g₂ _ a₂) →
        ∃ a : Γ(X, W)ˣ, pullU f₁ W a = a₁ ∧ pullU f₂ W a = a₂ := fun W a₁ a₂ e ↦ by
    have e' : res le_rfl (pullU g₁ _ a₁⁻¹) = res (le W) (pullU g₂ _ a₂⁻¹) := by
      rw [map_inv, map_inv, map_inv, map_inv, e]
    obtain ⟨a, p₁, p₂⟩ := ex W (le W) a₁.val a₂.val (congrArg Units.val e)
    obtain ⟨a', q₁, q₂⟩ := ex W (le W) (a₁⁻¹).val (a₂⁻¹).val (congrArg Units.val e')
    have k : a * a' = 1 := inj W _ _ (by rw [map_mul, map_one, p₁, q₁, Units.mul_inv])
      (by rw [map_mul, map_one, p₂, q₂, Units.mul_inv])
    exact ⟨⟨a, a', k, (mul_comm _ _).trans k⟩, Units.ext p₁, Units.ext p₂⟩
  have key : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y ↦ by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  let V : L.ι → X₀.Opens := fun i ↦ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ L.U i)
  let q : ∀ i, Γ(X₀, V i)ˣ := fun i ↦ pullU g₁ _ (b₁ i) * (res (le _) (pullU g₂ _ (b₂ i)))⁻¹
  have gq : ∀ i x, x ∈ V i → gm (𝟙 X₀) x (V i) (q i) = gm g₁ x _ (b₁ i) * (gm g₂ x _ (b₂ i))⁻¹ := fun i x hx ↦ by
    have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
    have e₂ := (gm_res (𝟙 X₀) x (le (L.U i)) hx _).trans (gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i))
    rw [Category.id_comp] at e₁ e₂
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) e₁ ((map_inv _ _).trans (congrArg (·⁻¹) e₂)))
  obtain ⟨F, hF⟩ := glue_unit ⊤ V (fun _ ↦ le_top) (fun x _ ↦ by
      obtain ⟨i, hi⟩ := exists_chart hL (f₁ (g₁ x))
      exact Opens.mem_iSup.2 ⟨i, hi⟩) q (fun i j x hx ↦ by
      rw [gq i x hx.1, gq j x hx.2, hb₁ _ g₁ x i j hx.1 hx.2, hb₂ _ g₂ x i j (le _ hx.1) (le _ hx.2), w, key])
  obtain ⟨u, hu⟩ := lift F
  have hu' : pullU g₂ ⊤ u = F := hu
  have loc : ∀ i, ∃ s : Γ(X, L.U i)ˣ, pullU f₁ _ s = b₁ i ∧ pullU f₂ _ s = b₂ i * res le_top u := fun i ↦
    exU _ _ _ (unit_ext fun x hx ↦ by
      have e := congrArg (gm (𝟙 X₀) x (V i)) (hF i)
      rw [gm_res (𝟙 X₀) x _ hx, gq i x hx, ← hu'] at e
      have e₀ := gm_pull (𝟙 X₀) g₂ x ⊤ trivial u
      have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
      have e₂ := gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i * res le_top u)
      rw [Category.id_comp] at e₀ e₁ e₂
      rw [gm_res (𝟙 X₀) x _ hx, gm_res (𝟙 X₀) x _ hx, e₁, e₂, map_mul, gm_res g₂ x _ (le _ hx), ← e₀]
      exact (mul_inv_eq_iff_eq_mul.1 e.symm).trans (mul_comm _ _))
  choose s hs₁ hs₂ using loc
  have gp : ∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (W : X.Opens) (a : Γ(X, W)ˣ), f y ∈ W →
      gm (𝟙 Y) y (f ⁻¹ᵁ W) (pullU f W a) = gm f y W a := fun f y W a hy ↦
    (gm_pull (𝟙 _) f y W hy a).trans (by rw [Category.id_comp])
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, fun i j ↦ injU _ _ _ (unit_ext fun y hy ↦ ?_) (unit_ext fun y hy ↦ ?_)⟩
  · have e := hb₁ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp, ← hs₁, ← hs₁, gp f₁ y _ _ hy.1, gp f₁ y _ _ hy.2] at e
    rw [gp f₁ y _ _ hy, gp f₁ y _ _ hy, map_mul, gm_res f₁ y _ hy, gm_res f₁ y _ hy]
    exact e
  · have e := hb₂ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp] at e
    have k : ∀ i, f₂ y ∈ L.U i → gm f₂ y _ (s i) = gm (𝟙 _) y _ (b₂ i) * gm (𝟙 _) y ⊤ u := fun i hi ↦ by
      rw [← gp f₂ y _ _ hi, hs₂, map_mul, gm_res (𝟙 _) y _ hi]
    rw [gp f₂ y _ _ hy, gp f₂ y _ _ hy, map_mul, gm_res f₂ y _ hy, gm_res f₂ y _ hy]
    exact (k i hy.1).trans (by rw [e, k j hy.2, _root_.mul_assoc])

theorem pic_eq_zero_of_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left →
    Function.Surjective (Units.map (A ◁ k₂).left.appTop.hom.toMonoidHom) →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 → GlobalTheory.CechPic.pull (A ◁ j₂).left c = 0 → c = 0 := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ h hs
  have H := _root_.GlobalTheory.DualOpen.sections_milnor S A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ h
  have w : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext h.w
  refine eq_zero_of_square _ _ (A ◁ k₁).left (A ◁ k₂).left ?_ (fun W ↦ (H W).1)
    (fun W h₂ ↦ (H W).2 _ le_rfl h₂ le_rfl) hs
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, w]

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.PoincareL2

theorem nfac_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.mpr (div_ne_zero (PoinPf.dmin_ne X hy τ _) (PoinPf.dmin_ne X hy τ _))

theorem poincareNorm_sq_eq_weight_mul_norm_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    ENNReal.ofReal (X.pnorm la P y ^ 2) = ENNReal.ofReal (‖P y‖ ^ 2) * IW.Wpsi X la (fun _ => 0) y := by
  have h1 : X.pnorm la P y ^ 2 = ‖P y‖ ^ 2 * Real.exp (-phla X la y) := by
    rw [PoinPf.exp_neg_phla X la (nfac_pos' X la hy)]
    change (‖P y‖ * X.nfac la y) ^ 2 = _
    ring
  have h2 : IW.Wpsi X la (fun _ => 0) y = ENNReal.ofReal (Real.exp (-(phla X la y + 0))) := by
    simp [IW.Wpsi, hy]
  rw [h1, h2, add_zero, ENNReal.ofReal_mul (by positivity)]

theorem sum_le (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
      0 < X.p0 → X.p0 < r → IsOrth X x → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ y ∈ X.dom,
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) := by
  obtain ⟨C1, hC1, hS1⟩ := h1
  obtain ⟨C2, hC2, hS2⟩ := h2
  obtain ⟨C3, hC3, hS3⟩ := h3
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro E _ _ _ r X x hp0 hp0r hx hinj y hy
  have hb := FrameDegreeData.bOf_mem X hy
  have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
  set y' := rmul y (FrameDegreeData.bOf X y) with hy'
  have heq : ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) =
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y')) := by
    refine tsum_congr fun γ => ?_
    rw [hy', PoinPf.lact_rmul' γ.1 y (FrameDegreeData.bOf X y),
      PoinPf.kaY_rmul X hx ((PairUnfoldPf.lact_mem_dom_iff X γ.2 y).2 hy) hb]
  rw [heq]
  set S := ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y'))
  set N : ℝ := ((X.Ψ.card : ℝ) * r) ^ 8
  set M := muF X x (Metric.ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x)
  have e1 : M * S ≤ ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N)) :=
    (hS1 E r X x y' hp0 hp0r hx ho hinj).trans (mul_le_mul' le_rfl (hS2 E r X y' hp0 hp0r ho))
  have e3 : ENNReal.ofReal (Real.exp (-(C3 * N))) ≤ M := hS3 E r X x hp0 hp0r hx
  have hone : ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N))) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]; simp
  calc S = (ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N)))) * S := by
          rw [hone, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (C3 * N)) * M) * S := by gcongr
    _ = ENNReal.ofReal (Real.exp (C3 * N)) * (M * S) := by ring
    _ ≤ ENNReal.ofReal (Real.exp (C3 * N)) * (ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N))) := by
          gcongr
    _ = ENNReal.ofReal (Real.exp ((C1 + C2 + C3) * N)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add,
            ← Real.exp_add]
          congr 2; ring

end GlobalTheory.PoincareL2

theorem GlobalTheory.PoincareL2.poincare_l2_of_orthogonal (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ)
    * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF
    X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X
    y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp
    (-(C * ((X.Ψ.card : ℝ) * r) ^
    8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF
    : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X) → ℂ) (P0
    : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la
    (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0)
    (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^
    2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C *
    ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 /
    ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1)
    z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) := by
  obtain ⟨C, hC, hsum⟩ := GlobalTheory.PoincareL2.sum_le h1 h2 h3
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hPF
  classical
  set bb : ℝ := (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) with hbbdef
  have hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ)) := fun _ _ _ _ _ _ => rfl
  have hW := (IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds
    lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩).1
  set W := IW.Wpsi X la (fun _ => 0) with hWdef
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x0 hx0
  set C1 := ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) with hC1def
  have hsumY := hsum E r X x hp0 hp0r hx hinj
  set Pd := X.dom.indicator P0 with hPd
  have hPdm : Measurable Pd := PairUnfoldPf.meas_indC X hP0.1.continuousOn
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => ‖Pd y‖ₑ ^ 2 * W y / ENNReal.ofReal (PoinPf.kaY X x bb y) with hψ
  have hψm : Measurable ψ :=
    ((hPdm.enorm.pow_const 2).mul hW.1).div (PoinPf.meas_kaY X x bb).ennreal_ofReal
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    have hyb : rmul y b ∈ X.dom := PoinPf.rmulDom X hb hy
    simp only [hψ, hPd, Set.indicator_of_mem hyb, Set.indicator_of_mem hy, hP0.2 y hy b hb,
      hW.2.1 y hy b hb, PoinPf.kaY_rmul X hx hy hb]
    have hpos : 0 < ‖bchar la b‖ ^ 2 := pow_pos (norm_pos_iff.2 (PoinPf.bchar_ne X la hb)) 2
    have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    have ht : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc : ‖bchar la b‖ₑ ^ 2 = ENNReal.ofReal (‖bchar la b‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [enorm_mul, mul_pow, hc]
    congr 1
    rw [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ‖P0 y‖ₑ ^ 2 * ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W y)
        = (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) *
            (‖P0 y‖ₑ ^ 2 * W y) := by ring
      _ = ‖P0 y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
  have hpt : ∀ z ∈ FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ≤
      C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
    intro z hz
    have hy : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hFF.2.1 hz
    rw [GlobalTheory.PoincareL2.poincareNorm_sq_eq_weight_mul_norm_sq X la _ hy]
    have hk0 : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ 0 :=
      fun γ => (ENNReal.ofReal_pos.2 (PoinPf.kaY_pos _ _ _ _)).ne'
    have hkt : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ ⊤ :=
      fun _ => ENNReal.ofReal_ne_top
    have hcs := PoinPf.cs_sq (fun γ : X.Γ => ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ)
      (fun γ => ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) hk0 hkt
    have e1 : ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) ≤
        (∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
      exact pow_le_pow_left₀ zero_le (PoinPf.enorm_poin_le X la P0 _) 2
    have e2 : ∀ γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
        ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) =
          ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
      intro γ
      have hγy : lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hy
      simp only [hψ, hPd, Set.indicator_of_mem hγy, hW.2.2 γ.1 γ.2 _ hy]
      rw [ENNReal.mul_div_right_comm]
    calc ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)
        ≤ ((∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
            ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) * C1) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) :=
          mul_le_mul_of_nonneg_right
            (e1.trans (hcs.trans (mul_le_mul_of_nonneg_left (hsumY _ hy) zero_le))) zero_le
      _ = C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
          rw [← tsum_congr e2, ENNReal.tsum_mul_right]; ring
  have hmeasγ : ∀ γ : X.Γ, AEMeasurable (fun z => ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hψm.comp ((PairUnfoldPf.lact_cont X γ.1).comp (PairUnfoldPf.cpt_cont X x0)).measurable).aemeasurable
  have hunf := PairUnfoldPf.lunfold D FF measInv_holds hx0 hFF ψ hψm hψB
  have hmi := measInv_holds r X x0 x hx0 hx ψ hψm hψB
  have hrhs : ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF] with z hz
    have hyd : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := hz
    simp only [hψ, hPd, Set.indicator_of_mem hyd, hPF z hz, PoinPf.kaY_cpt X hx]
    rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.mul_div_right_comm]
  calc ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂muF X x0
      ≤ ∫⁻ z in FF, C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 hpt
    _ = C1 * ∑' γ : X.Γ, ∫⁻ z in FF, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeasγ]
    _ = C1 * ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂muF X x0 := by rw [hunf]
    _ = C1 * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
        rw [hmi, hrhs]

theorem GlobalTheory.PoincareL2.poincare_l2_inequality : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) :=
  GlobalTheory.PoincareL2.poincare_l2_of_orthogonal _root_.GlobalTheory.BallSum.ballSum_le _root_.GlobalTheory.KernelIntegral.lintegral_kaF_le _root_.GlobalTheory.BallVol.ballvol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryW
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

theorem ptVia_spOver (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E E' : Type} [CommRing E] [Algebra R' E]
    [CommRing E'] [Algebra R' E'] (φ : E →ₐ[R'] E') (y : Pt X' E) :
    ptVia w (spOver φ ≫ y) =
      @spOver R _ E E' _ (algVia σ E) _ (algVia σ E') (homVia σ φ) ≫ ptVia w y := by
  apply Over.OverMorphism.ext
  change (spMap (φ : E →+* E') ≫ y.left) ≫ q = spMap (φ : E →+* E') ≫ (y.left ≫ q)
  exact Category.assoc _ _ _

theorem bcPull_coc_cob (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) :
    (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧
      ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  constructor
  · intro h
    unfold IsCoc at h ⊢
    intro E _ _ E' _ _ E'' _ _ φ ψ y _
    let _ : Algebra R E := algVia σ E
    let _ : Algebra R E' := algVia σ E'
    let _ : Algebra R E'' := algVia σ E''
    have hc : (homVia σ ψ).comp (homVia σ φ) = homVia σ (ψ.comp φ) := AlgHom.ext fun _ ↦ rfl
    simp only [bcPull, ptVia_spOver, ← hc]
    exact h E E' E'' (homVia σ φ) (homVia σ ψ) (ptVia w y) (sm_whole _)
  · rintro ⟨k, hk⟩
    refine ⟨fun E _ _ y ↦ @k E _ (algVia σ E) (ptVia w y), ?_⟩
    unfold IsCob at hk ⊢
    intro E _ _ E' _ _ φ y _
    let _ : Algebra R E := algVia σ E
    let _ : Algebra R E' := algVia σ E'
    simp only [bcPull, ptVia_spOver]
    exact hk E E' (homVia σ φ) (ptVia w y) (sm_whole _)

theorem bcPull_keeps : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) :=
  fun _ _ _ _ _ _ _ _ w u ↦ bcPull_coc_cob w u

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDisjointUnionRepresentingFamilyUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem same_precomp {S : Scheme.{0}} {A T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : N.IsLB) (hM : M.IsLB) {y : Y ⟶ T} {u : Y ⟶ U} (z : Z ⟶ Y)
    (e : Same A N M y u) : Same A N M (z ≫ y) (z ≫ u) := by
  have e' := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM _ _).1 e)
  rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc, Category.assoc, Category.assoc] at e'
  exact (same_iff hN hM _ _).2 e'

theorem eq_of_same_of_disjoint_cover : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  intro S A _ κ _ X V hV hVd Bt B j _ hj hjd b bt hb P Pt hP hPt hPi T x y hxy e

  have mem : ∀ i (p : Bt.left), bt.left p ∈ V i → p ∈ Set.range (j i).left := by
    intro i p hp
    have hp' : p ∈ (⨆ i', (j i').left.opensRange) := by rw [hj]; trivial
    obtain ⟨i', q, rfl⟩ := (TopologicalSpace.Opens.mem_iSup.1 hp')
    have h1 : bt.left ((j i').left q) ∈ V i' := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb i', Over.comp_left, Scheme.Hom.comp_apply]
      change (V i').ι ((b i').left q) ∈ V i'
      exact (Scheme.Opens.range_ι (V i')).subset ⟨_, rfl⟩
    by_cases hii : i' = i
    · subst hii; exact ⟨q, rfl⟩
    · exact absurd (⟨h1, hp⟩ : bt.left ((j i').left q) ∈ (V i' ⊓ V i : X.left.Opens))
        (fun h ↦ (hVd hii).le_bot h)
  have loc : ∀ i, ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ x.left = ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ y.left := by
    intro i
    let Ti : Over S := Over.mk (((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ T.hom)
    let w : Ti ⟶ T := Over.homMk ((x ≫ bt).left ⁻¹ᵁ V i).ι rfl
    have lf : ∀ z : T ⟶ Bt, z ≫ bt = x ≫ bt → ∃ zi : Ti ⟶ B i, zi ≫ j i = w ≫ z := by
      intro z hz
      have r : Set.range (w ≫ z).left ⊆ Set.range (j i).left := by
        rintro _ ⟨p, rfl⟩
        apply mem i
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, hz, Over.comp_left,
          Scheme.Hom.comp_apply]
        exact (Scheme.Opens.range_ι ((x ≫ bt).left ⁻¹ᵁ V i)).subset ⟨p, rfl⟩
      exact ⟨Over.homMk (IsOpenImmersion.lift (j i).left _ r)
        (by rw [← Over.w (j i), IsOpenImmersion.lift_fac_assoc, Over.w]),
        Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    obtain ⟨xi, hx⟩ := lf x rfl
    obtain ⟨yi, hy⟩ := lf y hxy.symm
    have hQ := (hP i).fam.isLB
    have hb' : xi ≫ b i = yi ≫ b i := by
      have k : xi ≫ b i ≫ Over.homMk (V i).ι = yi ≫ b i ≫ Over.homMk (V i).ι := by
        rw [← hb, reassoc_of% hx, reassoc_of% hy, hxy]
      apply Over.OverMorphism.ext
      rw [← cancel_mono (V i).ι]
      exact congrArg (fun q ↦ q.left) k
    have hs : Same A (P i) (P i) xi yi := by
      have e2 := (same_iff hPt hPt _ _).1 (same_precomp hPt hPt w e)
      rw [same_iff hQ hQ, ← evc_comp_of_iso (j i) hPt hQ (hPi i), ← evc_comp_of_iso (j i) hPt hQ (hPi i),
        Category.assoc, Category.assoc, hx, hy]
      exact e2
    have h3 := Model.rep_ext (hP i) hb' hs
    exact congrArg (fun q ↦ q.left) (show w ≫ x = w ≫ y by rw [← hx, ← hy, h3])
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun z ↦ ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show (x ≫ bt).left z ∈ ⨆ i, V i by rw [hV]; trivial)
  exact ⟨_, hi, loc i⟩

end GlobalTheory.DualCon.ProdGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull2BijectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X), (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) → (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) → Function.Bijective (CoefMap.restrict (OAff s) G).pull2 := by
  first | exact @GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis | exact GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis | (intros; apply GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis <;> assumption)
end

