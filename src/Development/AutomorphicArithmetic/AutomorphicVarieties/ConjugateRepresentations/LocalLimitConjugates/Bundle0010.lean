module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CharOf
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (x : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ x) = T (cmp i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp

private theorem adj_rT {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (r : ℝ)
    (T : Module.End ℂ (Sm E a)) (hT : ∀ X φ, lie E a X (T φ) = T (lie E a X φ)) (X : GlobalTheory.CuspRep.Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) : smAdj Ξ r X (T.rTensor _ x) = T.rTensor _ (smAdj Ξ r X x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v =>
    simp only [smAdj, adj_apply, smA_apply, smB_apply, map_sub, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hT,
      LinearMap.map_smul_of_tower]

private theorem cocl_app {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (r : ℝ)
    {n : ℕ} (e : Fin n → Herm E a)
    (T : Module.End ℂ (Sm E a)) (hT : ∀ X φ, lie E a X (T φ) = T (lie E a X φ)) :
    ∀ {q : ℕ} (ω : Co Ξ q), Coclosed (smAdj Ξ r) e ω → Coclosed (smAdj Ξ r) e (app T ω)
  | 0, _, _ => trivial
  | _ + 1, ω, h => by
    have h' : del (smAdj Ξ r) e ω = 0 := h
    show del (smAdj Ξ r) e (app T ω) = 0
    refine AlternatingMap.ext fun X => ?_
    have h2 := congrArg (fun η => T.rTensor (Fin Ξ.d → ℂ) (η X)) h'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [del_apply, map_sum, AlternatingMap.zero_apply, map_zero] at h2
    simp only [del_apply, app_apply, adj_rT Ξ r T hT, AlternatingMap.zero_apply, h2]

theorem UpperTheory.V.Cj.H.charOf :
    UpperTheory.V.Cj.H.CharOf := by
  intro E _ _ _ a ha n e he Ξ r m hm q ω h1 h2 h3 h4 X i t u
  have hL := (sqLie E a r).2
  obtain ⟨-, -, c3, c4⟩ := capSm E a Ξ t u
  have hx := wigSm E a Ξ (sqSub E a r) hL t (m t) (hm t) u q ω h1 h2 h4
  have hv : Val (sqSub E a r) (app (cap t u - ((m t).map (u + ·)).prod • 1) ω) := fun Y j => by
    rw [app_apply, cmp_rT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ (c4 _ hL _ (h4 Y j)) (Submodule.smul_mem _ _ (h4 Y j))
  have hc := cocl_app Ξ r e (cap t u - ((m t).map (u + ·)).prod • 1) (fun Y φ => by
    have := LinearMap.congr_fun (c3 Y).eq φ
    simp only [Module.End.mul_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, this]) ω h3
  have h0 := (sqOrth E a ha n e he Ξ r q).1 _ hv hc hx
  have h5 := congrArg (fun η : Co Ξ q => cmp i (η X)) h0
  simp only [app_apply, cmp_rT, AlternatingMap.zero_apply, map_zero, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h5
  exact sub_eq_zero.1 h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem grow_lin {φ ψ : GA E a → ℂ} (hφ : Grow φ) (hψ : Grow ψ) : Grow (φ + ψ) := by
  intro g
  obtain ⟨C, N, h⟩ := hφ g
  obtain ⟨C', N', h'⟩ := hψ g
  refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
  have h1 := GlobalTheory.CuspRep.one_le_height y
  have h0 : 0 ≤ GlobalTheory.CuspRep.height y := zero_le_one.trans h1
  have e1 : C * GlobalTheory.CuspRep.height y ^ N ≤ |C| * GlobalTheory.CuspRep.height y ^ (N + N') :=
    mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right _ _)) (pow_nonneg h0 _) (abs_nonneg C)
  have e2 : C' * GlobalTheory.CuspRep.height y ^ N' ≤ |C'| * GlobalTheory.CuspRep.height y ^ (N + N') :=
    mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left _ _)) (pow_nonneg h0 _) (abs_nonneg C')
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add ((h y).trans e1) ((h' y).trans e2))

private theorem grow_smul (s : ℂ) {φ : GA E a → ℂ} (hφ : Grow φ) : Grow (s • φ) := by
  intro g
  obtain ⟨C, N, h⟩ := hφ g
  refine ⟨‖s‖ * C, N, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg s)

private theorem lev_of {φ : Sm E a} {S : Set (GL (Fin a) (Af E))} (hS : S ∈ 𝓝 1)
    (h : ∀ k ∈ S, act (.fin k) φ = φ) : HasLev φ :=
  isOpen_stab_of_mem_nhds (finRep E a) φ (Filter.mem_of_superset hS h)

private theorem lev_nhds {φ : Sm E a} (h : HasLev φ) : {k : GL (Fin a) (Af E) | act (.fin k) φ = φ} ∈ 𝓝 1 := by
  refine h.mem_nhds ?_
  change finRep E a 1 φ = φ
  rw [map_one]; rfl

private theorem rt_cv (μ : Measure (GA E a)) {φ ψ : Sm E a} {F : HL μ} (e : φ.1 = cv ψ.1 F) (g : GA E a) :
    (rt E a g φ).1 = cv (rt E a g ψ).1 F := by
  funext x
  change φ.1 (x * g) = ∫ y, GlobalTheory.AutomorphicL2Unitary.lift _ F y * ψ.1 (y⁻¹ * x * g) ∂μ
  rw [e]
  simp only [cv, mul_assoc]

end

theorem UpperTheory.V.Cj.H.gardFacts :
    UpperTheory.V.Cj.H.GardFacts := by
  intro E _ _ _ a ha μ _ _ φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, e⟩ := h
    obtain ⟨t1, t2⟩ := testOps E a ψ
    have hc : Continuous ψ.1 := (t1 hψ.2).1
    refine ⟨lev_of (lev_nhds hψ.2) fun k hk => ?_, ?_, ?_, fun X => ?_, fun g => ?_⟩
    · have hk' : rt E a (finGL E a k) ψ = ψ := hk
      apply Subtype.ext
      change (rt E a (finGL E a k) φ).1 = φ.1
      rw [rt_cv μ e, hk', e]
    · obtain ⟨h, -⟩ := convolution_L2_class (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1 F
      unfold InL
      rw [e]
      exact h
    · rw [e]
      exact cvGrow E a ha μ ψ.1 hc hψ.1 F
    · exact Submodule.subset_span ⟨_, F, (t2 hψ).1 X, cvLie E a μ ψ φ hψ F e X⟩
    · exact Submodule.subset_span ⟨_, F, (t2 hψ).2 g, rt_cv μ e g⟩
  | zero =>
    refine ⟨lev_of Filter.univ_mem fun k _ => map_zero _, ⟨fun _ _ _ => rfl, ?_⟩, fun g => ⟨0, 0, fun y => by simp⟩,
      fun X => by rw [map_zero]; exact zero_mem _, fun g => by rw [map_zero]; exact zero_mem _⟩
    exact MemLp.zero
  | add φ ψ _ _ h h' =>
    refine ⟨lev_of (Filter.inter_mem (lev_nhds h.1) (lev_nhds h'.1)) fun k hk => ?_, ?_, grow_lin h.2.2.1 h'.2.2.1,
      fun X => by rw [map_add]; exact add_mem (h.2.2.2.1 X) (h'.2.2.2.1 X),
      fun g => by rw [map_add]; exact add_mem (h.2.2.2.2 g) (h'.2.2.2.2 g)⟩
    · rw [map_add (f := _), hk.1, hk.2]
    · simpa only [one_smul] using ((clFacts E a μ).1 φ ψ 1 1 h.2.1 h'.2.1).1
  | smul s φ _ h =>
    refine ⟨lev_of (lev_nhds h.1) fun k hk => ?_, ?_, grow_smul s h.2.2.1,
      fun X => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.1 X),
      fun g => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.2 g)⟩
    · rw [map_smul, hk]
    · simpa only [zero_smul, add_zero] using ((clFacts E a μ).1 φ φ s 0 h.2.1 h.2.1).1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PerLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.perLim :
    UpperTheory.V.Cj.H.PerLim := by
  intro E _ _ _ a U Ξ q ω hω h0 hl
  have hc := (coneConvex E a).1
  have hn : (cone E a).Nonempty := ⟨_, hOne_mem_cone⟩
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have key : ∀ k, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (ω k) w.1 ∧ (∀ γ, (geo ho U Ξ).act q γ w = w) ∧
      (geo ho U Ξ).dOm q w = 0 := fun k => by
    have hv : ∀ X, LeftInv (ω k X) ∧ RightInv U (ω k X) := fun X => (levelVal E a U Ξ _).1 ((hω k).val X)
    obtain ⟨w, hw, hw0⟩ := corrFwd E a U Ξ q (ω k) (hω k).equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, hw0 s⟩⟩
    have hw' : Corr U Ξ (ω k) w'.1 := hw
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [h0 k] at h
    exact ⟨w', hw', fun γ => (corrInv E a ho U Ξ q _ _ hw').1 (fun X => (hv X).1) γ,
      (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)⟩
  choose w hw hi hd0 using key
  obtain ⟨c, hz, hlim⟩ := zigLim _ _ _ _ (geo ho U Ξ) hc hn q 0 (fun k _ => w k)
    (fun k => ⟨fun γ _ _ => (hi k γ).symm, fun x hx => by simp [hd, hx, Finset.sum_range_succ]⟩)
    (fun k _ _ => hd0 k) (fun _ _ => corrLim E a ho U Ξ q ω w hw hl)
  exact ⟨c, fun k => ⟨ho, w k, hw k, hz k⟩, fun x hx => hlim x (by omega)⟩
end

