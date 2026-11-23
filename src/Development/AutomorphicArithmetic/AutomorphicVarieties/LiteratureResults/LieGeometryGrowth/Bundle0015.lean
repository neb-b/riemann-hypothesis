module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCorrSz
section
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

private theorem term_sz {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (k : ℕ) (τ : V → W) (Θ : V → F) (p : V)
    (hτ : ContDiffAt ℝ ∞ τ p) (hΘ : ContDiffAt ℝ ∞ Θ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : W → ℂ) (b : ℝ), ContDiffAt ℝ ∞ u (τ p) → Sz k u (τ p) b →
      Sz k (fun y => u (τ y) • Θ y) p (C * b) := by
  obtain ⟨c, hc⟩ := exists_sz k τ p
  obtain ⟨t, ht⟩ := exists_sz k Θ p
  obtain ⟨C, hC, H⟩ := compSz V W ℂ k c
  let L : ℂ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℂ
  refine ⟨2 ^ k * (‖L‖ * C) * t, by have := ht.nonneg; positivity, fun u b hu hb => ?_⟩
  have h1 := H u τ p b hτ hu (fun i _ hi => hc i hi) hb
  have s1 : ContDiffAt ℝ ∞ (fun y => u (τ y)) p := hu.comp p hτ
  have h2 := (appSz V ℂ (F →L[ℝ] F) k p).2.1 L _ _ s1 h1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (u (τ y))) p := L.contDiff.contDiffAt.comp p s1
  have h3 := (appSz V F F k p).1 _ Θ _ _ s2 hΘ h2 ht
  exact h3.mono (le_of_eq (by ring))

private theorem val_sz (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q) (hw : Corr U Ξ α w) (ρ : GA E a → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (hb : ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
      ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * ρ g) (k : ℕ) (v : Fin q → HV E a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g x, ContDiffAt ℝ ∞ (fun p => Tw U Ξ w g x p v) (hOne E a) ∧
      Sz k (fun p => Tw U Ξ w g x p v) (hOne E a) (M * ρ (pt g x)) := by
  obtain ⟨ι, _, X, j, Θ, τ, h1, hτ, hΘ, H⟩ := corrForm E a Ξ q v
  choose C hC HC using fun i => term_sz k τ (Θ i) (hOne E a) hτ (hΘ i)
  choose D hD HD using fun i => chartSz E a k ρ hρ (Bor.cmp (j i) (α (X i))) (hb (X i) (j i))
  refine ⟨∑ i, C i * D i, Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (hD i), fun g x => ?_⟩
  have e := H U α w hw g x
  have su : ∀ i, ContDiffAt ℝ ∞ (chart (Bor.cmp (j i) (α (X i))).1 (pt g x)) (τ (hOne E a)) := fun i => by
    rw [h1]; exact contDiffAt_chart (Bor.cmp (j i) (α (X i))).2 _ isUnit_one
  have st : ∀ i, ContDiffAt ℝ ∞ (fun p => chart (Bor.cmp (j i) (α (X i))).1 (pt g x) (τ p) • Θ i p) (hOne E a) :=
    fun i => ((su i).comp _ hτ).smul (hΘ i)
  refine ⟨(ContDiffAt.sum fun i _ => st i).congr_of_eventuallyEq e, ?_⟩
  have := (appSz (HV E a) ℝ (Fin Ξ.d → ℂ) k (hOne E a)).2.2 ι Finset.univ _ _ (fun i _ => st i)
    (fun i _ => HC i _ (D i * ρ (pt g x)) (su i) (by rw [h1]; exact HD i _))
  refine (this.congr e.symm).mono (le_of_eq ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.corrSz :
    UpperTheory.V.Lit.Geo.Cs.CorrSz := by
  intro E _ _ _ a U Ξ q α w hw ρ hρ hb k
  obtain ⟨T, C, hC, H⟩ := Cs.altEv (HV E a) (Fin Ξ.d → ℂ) q k
  choose M hM HM using Cs.val_sz E a U Ξ q α w hw ρ hρ hb k
  have h0 : 0 ≤ ∑ v ∈ T, M v := Finset.sum_nonneg fun v _ => hM v
  refine ⟨C * ∑ v ∈ T, M v, mul_nonneg hC h0, fun g x => ?_⟩
  rw [mul_assoc]
  exact H _ _ _ (mul_nonneg h0 (hρ _)) (fun v _ => (HM v g x).1) fun v hv => (HM v g x).2.mono
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun v _ => hM v) hv) (hρ _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsHomSz
section
open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.homSz :
    HomSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := hkSz V F q k c
  refine ⟨C, hC, fun Y W w b hY hW hw p hp hc hb => ?_⟩
  obtain ⟨ho, hs, -, -⟩ := UpperTheory.V.Lit.Geo.hkSmooth V F Y hY W hW q w hw
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  refine intSz V (V [⋀^Fin q]→L[ℝ] F) k p _ (fun z : V × ℝ => UpperTheory.V.Lit.Geo.hk W z.2 w z.1) (C * b) ho
    (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hs fun t ht => ?_
  exact h W t w p b (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) (hW.1.contDiffAt (hY.mem_nhds hp)) hc
    (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht))) (hb t ht)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsMove
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open scoped ContDiff

private theorem tp_smooth {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : V →L[ℝ] V) (B : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (hw : ContDiffAt ℝ ∞ w (A p)) :
    ContDiffAt ℝ ∞ (Cs.tp A B w) p := by
  have h1 : ContDiffAt ℝ ∞ (fun x => w (A x)) p := hw.comp p A.contDiff.contDiffAt
  have h2 := (ContinuousAlternatingMap.compContinuousLinearMapCLM A :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)).contDiff.contDiffAt.comp p h1
  exact (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V F F (Fin q) B).contDiff.contDiffAt.comp p h2

theorem UpperTheory.V.Lit.Geo.Cs.move :
    UpperTheory.V.Lit.Geo.Cs.Move := by
  intro E _ _ _ a ho U Ξ q k c
  obtain ⟨B, hB, hb⟩ := matBd E a Ξ c
  obtain ⟨D, hD, hd⟩ := Cs.tpSz (HV E a) (Fin Ξ.d → ℂ) q k B
  refine ⟨D, hD, fun w g x h b hh hs => ?_⟩
  obtain ⟨h1, -, h3⟩ := hb h hh.1 hh.2
  have e : sand h⁻¹ (sand h (hOne E a)) = hOne E a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  rw [Cs.Tw_eq U Ξ w.1 g h x]
  refine hd _ _ _ _ b (ContinuousLinearMap.opNorm_le_bound _ hB h3)
    (ContinuousLinearMap.opNorm_le_bound _ hB fun y => by rw [mulVecL_apply]; exact h1 y) ?_ (by rw [e]; exact hs)
  rw [e]
  exact tp_smooth _ _ _ _ ((w.2 _).1.contDiffAt (ho.mem_nhds (sand_mem_cone _ hOne_mem_cone)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsZwSz
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Geo
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem hv_coord (E : Type) [Field E] [NumberField E] (a : ℕ) :
    ∃ L : Fin a × Fin a × InfinitePlace E → ℂ →L[ℝ] HV E a,
      ∀ v : HV E a, v = ∑ n ∈ Finset.univ, L n (v.1 n.1 n.2.1 n.2.2) := by
  classical
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (HV E a).subtype (Submodule.ker_subtype _)
  refine ⟨fun n => LinearMap.toContinuousLinearMap (P ∘ₗ LinearMap.single ℝ (fun _ => Fin a → Cinf E) n.1 ∘ₗ
    LinearMap.single ℝ (fun _ => Cinf E) n.2.1 ∘ₗ LinearMap.single ℝ (fun _ => ℂ) n.2.2), fun v => ?_⟩
  have h1 : P v.1 = v := LinearMap.congr_fun hP v
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  refine h1.symm.trans (congrArg P ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fintype.sum_prod_type, ← map_sum]
  simp only [LinearMap.coe_single, Finset.univ_sum_single]

theorem UpperTheory.V.Lit.Geo.Cs.zwSz :
    ZwSz := by
  intro E _ _ _ a U Y C hY W hW k
  obtain ⟨B, -, hB⟩ := fieldDer E a U Y C hY
  obtain ⟨τ, h1, hτ, -, hs, -, he⟩ := secOne E a
  obtain ⟨L, hL⟩ := hv_coord E a
  choose φ hφ hb using hY.sm
  have e1 : toL (τ (hOne E a)).val = oneL E a := by rw [h1]; rfl
  have hc : ∀ i j w, ∃ c : ℝ, 0 ≤ c ∧ ∀ g, Sz k (chart (φ i j w).1 g) (oneL E a) (c * 1) := fun i j w => by
    refine chartSz E a k (fun _ => 1) (fun _ => zero_le_one) (φ i j w) fun l => ?_
    rcases l with _ | ⟨X, l⟩
    · refine ⟨B, fun g => ?_⟩
      rw [mul_one]
      change ‖(φ i j w).1 g‖ ≤ B
      rw [hφ]
      refine le_trans ?_ (hB g).1
      exact ((norm_le_pi_norm (toL (Y g).1 i j) w).trans (norm_le_pi_norm (toL (Y g).1 i) j)).trans
        (norm_le_pi_norm (toL (Y g).1) i)
    · obtain ⟨c, hc⟩ := hb i j w X l
      exact ⟨c, fun g => by rw [mul_one]; exact hc g⟩
  choose c _ hc using hc
  obtain ⟨b₁, hb₁⟩ := exists_sz k (fun p => toL (τ p).val) (hOne E a)
  obtain ⟨b₂, hb₂⟩ := exists_sz k (fun p => sand (τ p)) (hOne E a)
  obtain ⟨D, -, hD⟩ := compSz (HV E a) (Lie E a) ℂ k b₁
  refine ⟨2 ^ k * b₂ * ∑ n ∈ Finset.univ, ‖L n‖ * (D * (c n.1 n.2.1 n.2.2 * 1)), fun g x => ?_⟩
  have s0 : ∀ i j w, ContDiffAt ℝ ∞ (chart (φ i j w).1 (pt g x)) (toL (τ (hOne E a)).val) := fun i j w =>
    contDiffAt_chart (φ i j w).2 _ (val_mem_invSet _)
  have s1 : ∀ i j w, ContDiffAt ℝ ∞ (fun p => chart (φ i j w).1 (pt g x) (toL (τ p).val)) (hOne E a) := fun i j w =>
    ContDiffAt.comp (g := chart (φ i j w).1 (pt g x)) (f := fun p => toL (τ p).val) (hOne E a) (s0 i j w) hτ
  have z1 : ∀ i j w, Sz k (fun p => chart (φ i j w).1 (pt g x) (toL (τ p).val)) (hOne E a) (D * (c i j w * 1)) :=
    fun i j w => hD _ (fun p => toL (τ p).val) _ _ hτ (s0 i j w) (fun m _ hm => hb₁ m hm) (by rw [e1]; exact hc i j w _)
  have s2 : ∀ n : Fin a × Fin a × InfinitePlace E,
      ContDiffAt ℝ ∞ (fun p => L n (chart (φ n.1 n.2.1 n.2.2).1 (pt g x) (toL (τ p).val))) (hOne E a) := fun n =>
    (L n).contDiff.contDiffAt.comp (hOne E a) (s1 _ _ _)
  have z2 := (appSz (HV E a) (HV E a) (HV E a) k (hOne E a)).2.2 _ Finset.univ _ _ (fun n _ => s2 n)
    (fun n _ => (appSz (HV E a) ℂ (HV E a) k (hOne E a)).2.1 (L n) _ _ (s1 n.1 n.2.1 n.2.2) (z1 _ _ _))
  have z3 := (appSz (HV E a) (HV E a) (HV E a) k (hOne E a)).1 _ _ _ _ hs (ContDiffAt.sum fun n _ => s2 n) hb₂ z2
  refine z3.congr (he.mono fun p hp => ?_)
  have e2 := hW (g * τ p) x
  have e3 : sand (g * τ p) (hOne E a) = sand g p := by rw [map_mul, ContinuousLinearMap.mul_apply, hp]
  rw [e3] at e2
  simp only [chart_val, hφ, Zw, e2, ← pt_mul]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  exact congrArg _ (hL (hv (Y (pt (g * τ p) x)))).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmGood
section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.omGood :
    OmGood := by
  intro Γ V S _ _ _ _ d G W hW q
  have hsub : ∀ (q : ℕ) (w w' : G.Om q), (∀ s, RadBasic G.Y (w.1 s)) → (∀ s, RadBasic G.Y (w'.1 s)) →
      ∀ s, RadBasic G.Y ((w - w').1 s) := by
    intro q w w' h h' s p hp v i hi
    have e : (w - w').1 s p v = w.1 s p v - w'.1 s p v := rfl
    rw [e, h s p hp v i hi, h' s p hp v i hi, sub_self]
  have hpb : ∀ (q : ℕ) (w : G.Om q), (∀ s, RadBasic G.Y (w.1 s)) → ∀ s, RadBasic G.Y ((pbOm G W w).1 s) := by
    intro q w h s p hp v i hi
    rw [(omApply Γ V S d G W hW q).1 w s p hp]
    exact (pbBasic V _ G.Y G.isOpen (W s) (hW.field s) (hW.homog s) q).1 _ (h s) p hp v i hi
  have hhom : ∀ (q : ℕ) (w : G.Om (q + 1)), (∀ s, RadBasic G.Y (w.1 s)) →
      ∀ s, RadBasic G.Y ((homOm G W w).1 s) := by
    intro q w h s p hp v i hi
    rw [(omApply Γ V S d G W hW q).2 w s p hp]
    exact (pbBasic V _ G.Y G.isOpen (W s) (hW.field s) (hW.homog s) q).2 _ (w.2 s).1 (h s) p hp v i hi
  obtain ⟨h1, h2, -, h4⟩ := omHom Γ V S d G W hW
  refine ⟨fun w hw => ⟨⟨fun γ => ?_, hpb q w hw.basic, ?_⟩, ⟨fun γ => ?_, hw.dbasic, ?_⟩⟩,
    fun w w' hw hw' => ⟨fun γ => ?_, hsub q w w' hw.basic hw'.basic, ?_⟩,
    fun w hw => ⟨fun γ => ?_, hhom q w hw.basic, ?_⟩⟩
  · rw [(omEquiv Γ V S d G W hW q γ).1 w, hw.inv γ]
  · rw [h1]
    exact hpb _ _ hw.dbasic
  · rw [← dEquiv Γ V S d G q γ w, hw.inv γ]
  · rw [h2]
    intro s p _ v i _
    rfl
  · rw [map_sub, hw.inv γ, hw'.inv γ]
  · rw [map_sub]
    exact hsub _ _ _ hw.dbasic hw'.dbasic
  · rw [(omEquiv Γ V S d G W hW q γ).2 w, hw.inv γ]
  · rw [eq_sub_of_add_eq (h4 q w).symm]
    exact hsub _ _ _ (hsub _ _ _ (hpb _ _ hw.basic) hw.basic) (hhom _ _ hw.dbasic)
end

