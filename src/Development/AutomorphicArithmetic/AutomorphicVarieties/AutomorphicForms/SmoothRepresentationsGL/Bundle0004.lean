module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.FinKir
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem isY_map {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (f : R →+* S) {k : GL (Fin n) R}
    (h : IsY m k.val) : IsY m (GeneralLinearGroup.map f k).val := by
  intro i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (k.val i i) = 1
    rw [(h i hi).1, map_one]
  · change f (k.val i j) = 0
    rw [(h i hi).2 j hj, map_zero]

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := by
  intro i _
  exact ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_of_cmp {E : Type} [Field E] [NumberField E] {n m : ℕ} {k : GL (Fin n) (Af E)}
    (h : ∀ w, IsY m (cmp w k).val) : IsY m k.val := by
  intro i hi
  refine ⟨DFunLike.ext _ _ fun w => ?_, fun j hj => DFunLike.ext _ _ fun w => ?_⟩
  · exact (h w i hi).1
  · exact (h w i hi).2 j hj

private theorem loc_comm {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {k : GL (Fin n) (Af E)} (hk : cmp w k = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    k * locGL E n w y = locGL E n w y * k := by
  refine cmp_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [hk, one_mul, mul_one]
  · rw [show cmp v (locGL E n w y) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv y, one_mul, mul_one]

private theorem supp_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {a b : GL (Fin n) (Af E)} (ha : SuppIn S a) (hb : SuppIn S b) : SuppIn S (a * b) := fun w hw => by
  rw [map_mul, ha w hw, hb w hw, mul_one]

private theorem supp_loc {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) (y : GL (Fin n) (w.adicCompletion E)) :
    SuppIn S (locGL E n w y) := fun v hv =>
  GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : v = w => hv (e ▸ hw)) y

private theorem comb_mapDomain {G G' : Type} [Group G] [Group G'] (f : G →* G') (c : G →₀ ℂ) (W : G' → ℂ)
    (g : G') (p : G) : comb (c.mapDomain f) W (g * f p) = comb c (fun y => W (g * f y)) p := by
  unfold comb
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  simp only [map_mul, mul_assoc]

theorem UpperTheory.V.Af.Smo.finKir :
    UpperTheory.V.Af.Smo.LocKir → UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.EmbY → UpperTheory.V.Af.Smo.FinKir := by
  classical
  intro hK hP hE E _ _ _ n hn S U
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Finsupp.single 1 1, fun _ => 1, rfl, fun x hx => ?_, fun W _ _ p hp _ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact fun w _ => map_one _
    · obtain rfl : p = 1 := cmp_ext fun w => (hp w (Finset.notMem_empty w)).trans (map_one _).symm
      unfold comb
      rw [Finsupp.sum_single_index (by simp), mul_one]
  | insert w S hw ih =>
    obtain ⟨c₁, H₁, h1, hs₁, hc₁⟩ := ih
    obtain ⟨hE1, -, -, hEc⟩ := hE E n 0
    obtain ⟨c₀, H₀, h0, hc₀⟩ := hK E w (psiL w) ((hP E).1 w).1 ((hP E).1 w).2 n (n - 1) (by omega)
      (U.comap (locGL E n w) (hEc w))
    obtain ⟨c, hs, hc⟩ := exists_comb_comb c₁ (c₀.mapDomain (locGL E n w))
    have mono : ∀ {k : GL (Fin n) (Af E)}, SuppIn S k → SuppIn (insert w S) k :=
      fun hk v hv => hk v fun h => hv (Finset.mem_insert_of_mem h)
    have hl : ∀ y, SuppIn (insert w S) (locGL E n w y) := supp_loc (Finset.mem_insert_self w S)
    refine ⟨c, fun p => H₀ (cmp w p) * H₁ (p * (locGL E n w (cmp w p))⁻¹), ?_, fun x hx => ?_,
      fun W hW hU p hp hY => ?_⟩
    · simp only [map_one, inv_one, mul_one, h0, h1]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hs x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
      exact supp_mul (mono (hs₁ a ha)) (hl y)
    · have key : ∀ g, SuppIn S g → comb (c₀.mapDomain (locGL E n w)) W (g * locGL E n w (cmp w p))
          = H₀ (cmp w p) * W g := by
        intro g hg
        rw [comb_mapDomain, hc₀ (fun y => W (g * locGL E n w y)) ?_ ?_ _ (isY_map _ hY), map_one, mul_one]
        · intro ν hν y
          beta_reduce
          rw [map_mul, ← mul_assoc, loc_comm (hg w hw), mul_assoc,
            hW _ (hl ν) (hE1 w ν hν).1 _ (supp_mul (mono hg) (hl y)), (hE1 w ν hν).2]
          rfl
        · intro y u hu
          beta_reduce
          rw [map_mul, ← mul_assoc]
          exact hU _ (supp_mul (mono hg) (hl y)) _ hu (hl u)
      set p' := p * (locGL E n w (cmp w p))⁻¹ with hp'
      have e0 : cmp w p' = 1 := by
        rw [hp', map_mul, map_inv, show cmp w (locGL E n w (cmp w p)) = cmp w p from GlobalTheory.CuspRep.pLoc_locGL w _,
          mul_inv_cancel]
      have e1 : ∀ v, v ≠ w → cmp v p' = cmp v p := fun v hv => by
        rw [hp', map_mul, map_inv, show cmp v (locGL E n w (cmp w p)) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv _,
          inv_one, mul_one]
      have hS : SuppIn S p' := fun v hv => by
        by_cases h : v = w
        · subst h; exact e0
        · rw [e1 v h]
          exact hp v fun h' => (Finset.mem_insert.1 h').elim h hv
      have hY' : IsY (n - 1) p'.val := isY_of_cmp fun v => by
        by_cases h : v = w
        · subst h; rw [e0]; exact isY_one
        · rw [e1 v h]; exact isY_map _ hY
      have ep : p = p' * locGL E n w (cmp w p) := by rw [hp', inv_mul_cancel_right]
      have hI := hc₁ W (fun ν hν hy g hg => hW ν (mono hν) hy g (mono hg))
        (fun g hg u hu hu' => hU g (mono hg) u hu (mono hu')) p' hS hY'
      rw [hc, mul_assoc, ← hI]
      unfold comb at key ⊢
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun x hx => ?_
      have e2 : p * x = p' * x * locGL E n w (cmp w p) := by
        rw [mul_assoc, loc_comm (hs₁ x hx w hw), ← mul_assoc, ← ep]
      rw [e2, key _ (supp_mul hS (hs₁ x hx))]
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.HalfBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schTw :
    UpperTheory.V.Af.Smo.SchTensor → UpperTheory.V.Af.Smo.SchTw := by
  intro hT V M _ _ _ _ _ _ A e
  obtain ⟨δ, hδ, hAδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ‖A‖ * δ ≤ 1 / 2 := by
    refine ⟨1 / (2 * (‖A‖ + 1)), by positivity, ?_⟩
    have h0 : 0 ≤ ‖A‖ := norm_nonneg _
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hball : ∀ ξ ∈ Metric.ball e δ, ‖A (ξ - e)‖ ≤ 1 / 2 := by
    intro ξ hξ
    calc ‖A (ξ - e)‖ ≤ ‖A‖ * ‖ξ - e‖ := A.le_opNorm _
      _ ≤ ‖A‖ * δ := by
        gcongr
        rw [← dist_eq_norm]
        exact (Metric.mem_ball.mp hξ).le
      _ ≤ 1 / 2 := hAδ
  let φ : ContDiffBump e := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let χ : ContDiffBump e := ⟨δ / 2, δ, by positivity, by linarith⟩
  let g : V → (M →L[ℝ] M) := fun ξ => χ ξ • A (ξ - e)
  have hsmall : ∀ ξ : V, ‖g ξ‖ ≤ 1 / 2 := by
    intro ξ
    by_cases hξ : χ ξ = 0
    · simp [g, hξ]
    · have hmem : ξ ∈ Metric.ball e δ := by
        have h1 : ξ ∈ Function.support χ := hξ
        rwa [χ.support_eq] at h1
      simp only [g]
      rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
      calc χ ξ * ‖A (ξ - e)‖ ≤ 1 * (1 / 2) := by
            gcongr
            · exact χ.le_one
            · exact hball ξ hmem
        _ = 1 / 2 := by norm_num
  refine ⟨fun ξ => ((φ ξ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have h1 : φ e = 1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
    simp [h1]
  · intro ξ hξ y hy
    have hφ : φ ξ ≠ 0 := by
      intro h1
      apply hξ
      simp [h1]
    have hmem : ξ ∈ Metric.ball e δ := by
      have h1 : ξ ∈ Function.support φ := hφ
      rw [φ.support_eq] at h1
      exact Metric.ball_subset_ball (show δ / 2 ≤ δ by linarith) h1
    have h2 : y = -(A (ξ - e)) y := eq_neg_of_add_eq_zero_left hy
    have h3 : ‖y‖ ≤ 1 / 2 * ‖y‖ := by
      calc ‖y‖ = ‖(A (ξ - e)) y‖ := by
            conv_lhs => rw [h2]
            exact norm_neg _
        _ ≤ ‖A (ξ - e)‖ * ‖y‖ := (A (ξ - e)).le_opNorm y
        _ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hball ξ hmem) (norm_nonneg _)
    have h4 : ‖y‖ = 0 := le_antisymm (by linarith [norm_nonneg y]) (norm_nonneg y)
    exact norm_eq_zero.mp h4
  · intro α
    have hh : ContDiff ℝ ∞ (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp φ.contDiff
    have hhc : HasCompactSupport (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      φ.hasCompactSupport.comp_left Complex.ofReal_zero
    obtain ⟨G0, hG0⟩ := hT V M (fun ξ => ((φ ξ : ℝ) : ℂ)) hh hhc α
    have hg : Function.HasTemperateGrowth g := by
      apply HasCompactSupport.hasTemperateGrowth
      · exact χ.hasCompactSupport.smul_right (f' := fun ξ => A (ξ - e))
      · exact χ.contDiff.smul (A.contDiff.comp (contDiff_id.sub contDiff_const))
    let Φ : V × M → V × M := fun p => p + ContinuousLinearMap.inr ℝ V M (g p.1 p.2)
    have hΦ : Function.HasTemperateGrowth Φ := by
      have h1 : Function.HasTemperateGrowth (fun p : V × M => g p.1) :=
        hg.comp (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
      have h2 : Function.HasTemperateGrowth (fun p : V × M => g p.1 p.2) :=
        (ContinuousLinearMap.id ℝ (M →L[ℝ] M)).bilinear_hasTemperateGrowth h1
          (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
      exact Function.HasTemperateGrowth.add Function.HasTemperateGrowth.id
        ((ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth.comp h2)
    have hΦp : ∀ p : V × M, Φ p = (p.1, p.2 + g p.1 p.2) := by
      intro p
      ext <;> simp [Φ]
    have hup : ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C * (1 + ‖Φ p‖) ^ k := by
      refine ⟨1, 2, fun p => ?_⟩
      have e1 : ‖p.2‖ ≤ ‖p.2 + g p.1 p.2‖ + ‖g p.1 p.2‖ := by
        simpa using norm_sub_le (p.2 + g p.1 p.2) (g p.1 p.2)
      have e2 : ‖g p.1 p.2‖ ≤ 1 / 2 * ‖p.2‖ :=
        ((g p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall _) (norm_nonneg _))
      have e3 : ‖p.2 + g p.1 p.2‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_snd_le (p.1, p.2 + g p.1 p.2)
      have e4 : ‖p.1‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_fst_le (p.1, p.2 + g p.1 p.2)
      rw [pow_one]
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩ <;> nlinarith [norm_nonneg (Φ p), norm_nonneg p.2]
    refine ⟨SchwartzMap.compCLM ℂ hΦ hup G0, fun ξ y => ?_⟩
    rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦp, hG0]
    by_cases hφ : φ ξ = 0
    · simp [hφ]
    · have hmem : ξ ∈ Metric.closedBall e χ.rIn := by
        have h1 : ξ ∈ Function.support φ := hφ
        rw [φ.support_eq] at h1
        exact Metric.ball_subset_closedBall h1
      simp [g, χ.one_of_mem_closedBall hmem]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.InnerZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_equiv_mod {M : Type} [AddCommGroup M] [Module ℂ M] (U U' D : Submodule ℂ M)
    (h : U ⊓ D = ⊥) (h' : U' ⊓ D = ⊥) (e : U ⊔ D = U' ⊔ D) :
    ∃ T : U ≃ₗ[ℂ] U', ∀ u, (T u).1 - u.1 ∈ D := by
  have inj : ∀ W : Submodule ℂ M, W ⊓ D = ⊥ → Function.Injective (D.mkQ ∘ₗ W.subtype) := fun W hW => by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have hx' : x.1 ∈ W ⊓ D := ⟨x.2, (Submodule.Quotient.mk_eq_zero D).1 hx⟩
    rw [hW] at hx'
    exact Subtype.ext hx'
  have rg : ∀ W : Submodule ℂ M, LinearMap.range (D.mkQ ∘ₗ W.subtype) = (W ⊔ D).map D.mkQ := fun W => by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  have er : LinearMap.range (D.mkQ ∘ₗ U.subtype) = LinearMap.range (D.mkQ ∘ₗ U'.subtype) := by
    rw [rg, rg, e]
  refine ⟨(LinearEquiv.ofInjective _ (inj U h)).trans
    ((LinearEquiv.ofEq _ _ er).trans (LinearEquiv.ofInjective _ (inj U' h')).symm), fun u => ?_⟩
  refine (Submodule.Quotient.eq D).1 ?_
  exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (inj U' h')).apply_symm_apply
    (LinearEquiv.ofEq _ _ er (LinearEquiv.ofInjective _ (inj U h) u)))

private theorem iso_of_compl {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (π π' : CuspSub E n)
    (D : Submodule ℂ (TR.Sm E n)) (hD : TR.IsStable D) (h : π.V ⊓ D = ⊥) (h' : π'.V ⊓ D = ⊥)
    (hle : π'.V ≤ π.V ⊔ D) : π.Iso π' := by
  have hst : TR.IsStable (π.V ⊓ (π'.V ⊔ D)) := by
    rintro o φ ⟨h1, h2⟩
    refine ⟨π.stable o φ h1, ?_⟩
    obtain ⟨x, hx, d, hd, rfl⟩ := Submodule.mem_sup.1 h2
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (π'.stable o x hx) (hD o d hd)
  have hge : π.V ≤ π'.V ⊔ D := by
    rcases π.irred _ inf_le_left hst with h0 | h0
    · refine absurd (eq_bot_iff.2 fun x hx => ?_) π'.ne_bot
      obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hle hx)
      have hu' : u ∈ π.V ⊓ (π'.V ⊔ D) := ⟨hu, by
        have := Submodule.add_mem_sup hx (D.neg_mem hd)
        rwa [add_neg_cancel_right] at this⟩
      rw [h0, Submodule.mem_bot] at hu'
      rw [← h']
      refine ⟨hx, ?_⟩
      rw [hu', zero_add]
      exact hd
    · exact inf_eq_left.1 h0
  obtain ⟨T, hT⟩ := exists_equiv_mod π.V π'.V D h h'
    (le_antisymm (sup_le hge le_sup_right) (sup_le hle le_sup_right))
  refine ⟨T, fun o φ => Subtype.ext (sub_eq_zero.1 ?_)⟩
  rw [← Submodule.mem_bot ℂ, ← h']
  refine ⟨π'.V.sub_mem (T _).2 (π'.op o _).2, ?_⟩
  have h1 := D.sub_mem (hT (π.op o φ)) (hD o _ (hT φ))
  rw [map_sub, TR.CuspSub.op_val, sub_sub_sub_cancel_right] at h1
  exact h1

private theorem stab_orthRel {E : Type} [Field E] [NumberField E] {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : cuspForms E n →ₗ[ℂ] H)
    (hρ : ∀ X, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι ((gkModuleCusp E n).ρ X a)) (ι c) + inner ℂ (ι a) (ι ((gkModuleCusp E n).ρ X c)) = 0)
    (hσ : ∀ k, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι ((gkModuleCusp E n).σ k a)) (ι ((gkModuleCusp E n).σ k c)) = inner ℂ (ι a) (ι c))
    (hτ : ∀ g, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι (finRepCusp E n g a)) (ι (finRepCusp E n g c)) = inner ℂ (ι a) (ι c))
    {U : Submodule ℂ (cuspForms E n)} (hU : U ≤ centralCuspForms E n) (hs : Fb.Stab U) :
    Fb.Stab (orthRel ι (centralCuspForms E n) U) := by
  refine ⟨fun X φ hφ => ?_, fun k φ hφ => ?_, fun g φ hφ => ?_⟩
  · refine map_mem_orthRel (A' := fun y => -(gkModuleCusp E n).ρ X y) (Fb.stab_central.ρ X)
      (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hs.ρ X u hu)) hφ
    rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
    exact hρ X x (hU hx) y hy
  · refine map_mem_orthRel (A' := (gkModuleCusp E n).σ k⁻¹) (Fb.stab_central.σ k)
      (fun x hx y hy => ?_) (hs.σ k⁻¹) hφ
    rw [← hσ k _ (hU (hs.σ k⁻¹ x hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  · refine map_mem_orthRel (A' := finRepCusp E n g⁻¹) (Fb.stab_central.τ g)
      (fun x hx y hy => ?_) (hs.τ g⁻¹) hφ
    rw [← hτ g _ (hU (hs.τ g⁻¹ x hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]

private theorem carrier_le_of_not_iso {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ}
    (π π' : CuspSub E n) (hi : ¬ π.Iso π') (C : Submodule ℂ (cuspForms E n)) (hC : Fb.Stab C)
    (hinf : Fb.carrier π ⊓ C = ⊥) (hle : Fb.carrier π' ≤ Fb.carrier π ⊔ C) : Fb.carrier π' ≤ C := by
  have hst : TR.IsStable (π'.V ⊓ C.map (Fb.ofCusp E n)) := fun o x hx =>
    ⟨π'.stable o x hx.1, hC.map o x hx.2⟩
  rcases π'.irred _ inf_le_left hst with h0 | h0
  · refine absurd (iso_of_compl π π' _ hC.map ?_ h0 ?_) hi
    · rw [← Fb.map_carrier, ← Submodule.map_inf _ Fb.ofCusp_injective, hinf, Submodule.map_bot]
    · rw [← Fb.map_carrier, ← Fb.map_carrier, ← Submodule.map_sup]
      exact Submodule.map_mono hle
  · intro φ' hφ'
    obtain ⟨ψ, hψ, e⟩ := inf_eq_left.1 h0 (Fb.mem_carrier.1 hφ')
    obtain rfl := Fb.ofCusp_injective e
    exact hψ

theorem UpperTheory.V.Af.Smo.innerZero :
    UpperTheory.V.Af.Smo.InnerZero := by
  intro E _ _ _ n μ _ π π' hc hc' hi φ hφ φ' hφ'
  have l := Fb.carrier_le_central π hc
  have l' := Fb.carrier_le_central π' hc'
  have hs := Fb.stab_carrier π
  have hC := stab_orthRel (CuspidalSpectrum.cuspToL2 μ) (fun X a ha c hc => petersson_inner_lieAlgebra_skewAdjoint μ X ha hc)
    (fun k a ha c hc => petersson_inner_maximalCompact_invariant μ k ha hc) (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc) l hs
  have hsup := CuspidalSpectrum.sup_orthRel_centralCuspForms μ _ l hs.ρ hs.τ
  have hinf := inf_orthRel_eq_bot (ι := CuspidalSpectrum.cuspToL2 μ) l fun a ha h0 =>
    CuspidalSpectrum.eq_zero_of_cuspVecL_eq_zero (μ := μ) ha h0
  exact (carrier_le_of_not_iso π π' hi _ hC hinf (l'.trans hsup.ge) hφ').2 φ hφ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.IsYBlockGL
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology


open GroundTheory.Automorphic.FourierWhittaker in
private theorem isY_blockGL {K : Type} [Field K] {n k : ℕ} (hk : k < n) (γ : GL (Fin k) K) :
    IsY (n - 1) (blockGL hk.le γ : GL (Fin n) K).val := by
  intro i hi
  have hik : ¬ i.val < k := by omega
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coe_blockGL, blockMat_apply, dite_eq_right hik, if_pos rfl]
  · rw [coe_blockGL, blockMat_apply, dite_eq_right hik, if_neg hj.ne']


open GroundTheory.Automorphic.FourierWhittaker in
open scoped NumberField.AdeleRing in
private theorem step {K : Type} [Field K] [NumberField K] {n : ℕ} {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hc : Continuous ϕ) (hl : IsLeftInvariant ϕ) (hcusp : AutomorphicForm.IsCuspidal ϕ)
    {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (g : AdelicGLn.AdelicGL K n)
    (h0 : ∀ γ : GL (Fin k) K, partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le γ) * g) = 0) :
    partialCoeff ϕ (k + 1) g = 0 := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  set D := AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) with hD
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * D =
      D * colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    simp only [D]
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  set F : (Fin k → 𝔸[K]) → ℂ := fun x => partialCoeff ϕ (k + 1) (colGL k x * (D * g))
  have hip : IsIntegralPeriodic F := by
    refine ⟨(continuous_partialCoeff hc _).comp ((continuous_colGL k).mul continuous_const),
      fun ξ hξ x => ?_, fun x z hz => ?_⟩
    · obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      simp only [F]
      rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL hl hk]
    · have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
          fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
            (algebraMap (𝓞 K) K δ) * z i) := by
        funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
      change partialCoeff ϕ (k + 1)
          (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * (D * g)) =
        partialCoeff ϕ (k + 1) (colGL k x * (D * g))
      rw [colGL_add, mul_assoc (colGL k x),
        ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
        colGL_finiteAdeleInr, mul_assoc D, finEmb_mul_eq, ← mul_assoc,
        ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  have hcoeff : vecCoeff F = 0 := by
    funext ξ
    by_cases hξ : ξ = 0
    · rw [hξ]
      exact vecCoeff_zero_of_isCuspidal hc hl hcusp hk0 hk (D * g)
    · have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hl hk (rowCompletion ξ) (D * g)
      rw [vecMul_rowCompletion hξ] at h1
      refine h1.symm.trans ?_
      rw [hD, ← mul_assoc, ← map_mul, ← map_mul]
      exact h0 _
  have H := hip.hasSum_vecCoeff (hcoeff ▸ summable_zero) 0
  simp only [hcoeff, Pi.zero_apply, zero_mul] at H
  have hF0 : F 0 = 0 := (hasSum_zero.unique H).symm
  rw [← partialCoeff_succ_diagonal_blockGL hl hk (scalarGL k u⁻¹) g]
  change partialCoeff ϕ (k + 1) (D * g) = 0
  simpa [F, colGL_zero] using hF0

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.injP :
    UpperTheory.V.Af.Smo.InjP := by
  intro E _ _ n hn f hf X hX hW
  obtain ⟨V, hV⟩ := hf.level
  rw [← Fb.finEmb_eq] at hV
  have key : ∀ k, k < n → ∀ g ∈ X, partialCoeff f (k + 1) g = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ g hg
      exact (whittaker_eq_partialCoeff hf.cont hn g).symm.trans (hW g hg)
    | succ m ih =>
      intro hm g hg
      exact step hf.cont hf.left hf.cusp hV (Nat.succ_pos m) hm g fun γ =>
        ih (by omega) _ (hX _ (isY_blockGL hm γ) g hg)
  intro g hg
  have := key (n - 1) (by omega) g hg
  rwa [Nat.sub_add_cancel hn, partialCoeff_self] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PsiInf
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.psiInf :
    UpperTheory.V.Af.Smo.PsiInf := by
  intro E _ _ _ x
  have h : GroundTheory.Global.adelicChar E (sInf E x) = 𝐞 (-∑ v, x v) := by
    have e : sInf E x = GroundTheory.Global.infiniteAdeleInl (TR.infEq E x) := rfl
    rw [e, GroundTheory.Global.adelicChar_infiniteAdeleInl, ← Finset.sum_neg_distrib, GroundTheory.Global.addChar_map_finsetSum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [GroundTheory.Global.infiniteAdelicChar_apply_of_isReal (IsTotallyReal.isReal w)]
    have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (TR.infEq E x w) = x w :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (x w)
    rw [e2]
  exact congrArg (fun z : Circle => (z : ℂ)) h
end

