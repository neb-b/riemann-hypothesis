module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGrassHeightE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights MvPolynomial Matrix

noncomputable section

namespace GrassHeightEAux

theorem log_block (j m : ℕ) (e : ℝ) (he : UnitDetBound m j e) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    -e ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by
  set S : ℝ := ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm : ‖WithLp.toLp 2 v‖ = ‖a‖ * Real.sqrt S := by
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2 = ‖a‖ ^ 2 * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp [hv, mul_pow]
    rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hdet : S = (1 + Z * Zᴴ).det.re := by
    rw [← PlueckerNormSq.full j m Z, Complex.ofReal_re]
  have hb := he Zᴴ fun a b => by rw [conjTranspose_apply, norm_star, hZ b a]
  rw [conjTranspose_conjTranspose, det_one_add_mul_comm, ← hdet] at hb
  rw [hnorm, div_mul_cancel_left₀ ha'.ne', Real.log_inv, Real.log_sqrt hS0]
  linarith

end GrassHeightEAux


open GrassHeightEAux in
theorem RootLogNormBoundE.full : RootLogNormBoundE.Statement := by
  intro f j m e ζ he hζ z hz
  have h₁ := RootAnchorNonzero.proof
  have hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ := fun τ =>
    (fsMetric (ι := PlIdx j m)).pos _ fun h0 => by
      obtain ⟨i, hi⟩ := hz.1 τ
      exact hi (congrFun h0 i)
  have key : ∀ τ : Fin f, -e ≤
      Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    intro τ
    obtain ⟨ζ', hζ', hz'⟩ := RootPointConj.full f j m ζ hζ z hz τ
    exact log_block j m e he ζ' (fun a b => by
        obtain ⟨k, hk, h⟩ := hζ' a b
        exact Complex.norm_eq_one_of_pow_eq_one h hk.ne')
      _ (h₁ f j m ζ hζ z hz τ) _ hz'
  have hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)),
      ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0 := fun τ _ =>
    div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'
  have e' : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z =
      ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    rw [← Real.log_prod hne]
    simp [logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]
  rw [e']
  calc -((f : ℝ) * e) = ∑ _τ : Fin f, -e := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun τ _ => key τ

theorem RootHeightE.full : RootHeightE.Statement := by
  intro f j m e ζ hf he hζ II hII
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have hV := RootArithVar.full f j m ζ hf hζ
  have hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ := by
    rw [rootPointIdeal, MultiHomogMemCoord.proof (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]
    simp [rootAnchorSection, rootCoord, anchor_minor]
  have hsm : IsSmoothHerm (fsMulti (plBlocks f j m)) := FsLineSmooth.proof _ _
  have hR := (hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0
    (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm
    (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem
  have e1 : (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) :
      Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)] := by
    funext i; fin_cases i; rfl
  rw [e1] at hR
  have hlow := PtsIntegralZeroLowerNE.proof (Fin f) (plBlocks f j m) (rootPointIdeal ζ)
    (fun i z => Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) i).h z))
    (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-((f : ℝ) * e))
    hV.2.1.2.1 (RootPointsFinite.full f j m ζ hζ) ?_ (RootLogNormBoundE.full f j m e ζ he hζ)
  · have : recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ)
        (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) =
        - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0 := by
      simp [recR, RootDivSuppEmpty.proof f j m ζ hζ]
    rw [this] at hR
    show II _ _ _ 1 _ ≤ _
    rw [hR]
    simp only [arInt]
    have := hlow
    nlinarith
  · intro u z hu hz
    have hh := (fsMulti (plBlocks f j m)).smul u z hu
    have hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1 := rfl
    simp only [logNorm, hh, hfa, zpow_one]
    have hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p)
        (map (Int.castRingHom ℂ) (rootAnchorSection f j m))
        = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) := by
      simp [rootAnchorSection, Finset.prod_mul_distrib]
    have hu0 : (∏ k, ‖u k‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)
    congr 1
    erw [hs]
    rw [norm_mul, norm_prod]
    field_simp

theorem GrassHeightE.full : GrassHeightE.Statement := by
  intro hZ2 f j m e hf he II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    ((f : ℝ) * e) (rootFamily f j m) II hII (GrassArithVar.full f j m hf) bot_le
    (FsLineSemipositive.full _ _ _) (NefOfNonneg.proof _ _ _ _ fun _ => ?_) (FsConjInvariant.proof _ _) ?_
    (RootDense.full f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨RootArithVar.full f j m ζ hf hζ, GrassLeRoot.proof f j m ζ, RootHeightE.full f j m e ζ hf he hζ II hII⟩

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeFibres
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace ModelFibreSumAlmostEverywhere

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem lift_mem (x : M.Xc) : modelLift M x x ∈ mcPts P :=
  ((modelLift_spec M x).1 x (mem_modelU M x)).1

theorem proj_lift (x : M.Xc) : M.proj (modelLift M x x) = x :=
  ((modelLift_spec M x).1 x (mem_modelU M x)).2

theorem lift_compat {x z : M.Xc} (hz : z ∈ modelU M x) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ modelLift M z z = fun p => c p.1 * modelLift M x z p := by
  have h1 := (modelLift_spec M x).1 z hz
  obtain ⟨c, hc, h⟩ := (M.fibre _ h1.1 _ (lift_mem M z)).mp (h1.2.trans (proj_lift M z).symm)
  exact ⟨c, hc, h⟩

theorem proj_eq_of_segre {x : M.Xc} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (μ : ℂ) (hμ : μ ≠ 0)
    (h : segre z = μ • segre (modelLift M x x)) : M.proj z = x := by
  obtain ⟨c, hc, hzc⟩ := sameOrbit_of_segre (lift_mem M x).1 μ hμ h
  have := (M.fibre _ (lift_mem M x) _ hz).mpr ⟨c, hc, hzc⟩
  rw [← this, proj_lift]

theorem modelQ_eq_local {x z : M.Xc} (hz : z ∈ modelU M x) :
    modelQ M Ψ z = fun i => Ψ (segre (modelLift M x z)) i.succ / Ψ (segre (modelLift M x z)) 0 := by
  obtain ⟨c, hc, hzc⟩ := lift_compat M hz
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext i
  simp only [modelQ, hzc, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_lift_chart (x : M.Xc) (j : Fin M.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x) :
    AnalyticAt ℂ (fun v => modelLift M x ((M.atlas.chart j).symm v)) u :=
  analyticAt_pi_iff.mpr fun p => (modelLift_spec M x).2 p j u hu

theorem analyticAt_segre_lift (x : M.Xc) (j : Fin M.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x) :
    AnalyticAt ℂ (fun v => Ψ (segre (modelLift M x ((M.atlas.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart M x j hu
  have hs : AnalyticAt ℂ (fun v => segre (modelLift M x ((M.atlas.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_modelQ (x : M.Xc) (j : Fin M.atlas.n) (hj : x ∈ (M.atlas.chart j).source)
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) :
    AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) := by
  set u := M.atlas.chart j x
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  have hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
    ⟨(M.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact mem_modelU M x⟩
  have hH := analyticAt_segre_lift M Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (modelLift M x ((M.atlas.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) i.succ /
        Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x)).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (modelQ_eq_local M Ψ hv.2).symm

theorem psi_zero_ne_of_not_mem_bad {E : Set M.Xc} {x : M.Xc} (hx : x ∉ modelBad M Ψ E) :
    Ψ (segre (modelLift M x x)) 0 ≠ 0 :=
  fun h => hx (Or.inr (Or.inl h))

theorem notMem_of_notMem_bad {E : Set M.Xc} {x : M.Xc} (hx : x ∉ modelBad M Ψ E) : x ∉ E :=
  fun h => hx (Or.inl h)

def modelW (x : M.Xc) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)

theorem modelW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : M.Xc}
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) : modelW M Ψ x ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ (modelQ M Ψ x) := by
  classical
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (modelLift M x x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * modelLift M x x p, mcPts_smul hPh c hc (lift_mem M x), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [modelW, h0]
    · simp only [modelW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, modelQ]
      rw [div_eq_inv_mul]

theorem modelW_injOn : Set.InjOn (modelW M Ψ) {x | Ψ (segre (modelLift M x x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  have h := congrArg (fun v => Ψ (segre (modelLift M x x)) 0 • v) hw
  simp only [modelW, smul_smul, mul_inv_cancel₀ (show Ψ (segre (modelLift M x x)) 0 ≠ 0 from hx),
    one_smul] at h
  have := proj_eq_of_segre M (lift_mem M x)
    (Ψ (segre (modelLift M x x)) 0 * (Ψ (segre (modelLift M x' x')) 0)⁻¹)
    (by simp [show Ψ (segre (modelLift M x x)) 0 ≠ 0 from hx,
      show Ψ (segre (modelLift M x' x')) 0 ≠ 0 from hx']) h
  rw [proj_lift] at this
  exact this

theorem mem_fibre_data {y : Fin e → ℂ} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hΨz : Ψ (segre z) = Fin.cons 1 y) :
    Ψ (segre (modelLift M (M.proj z) (M.proj z))) 0 ≠ 0 ∧ modelQ M Ψ (M.proj z) = y ∧
      modelW M Ψ (M.proj z) = segre z := by
  obtain ⟨c, hc, hxc⟩ := (M.fibre _ hz _ (lift_mem M (M.proj z))).mp (proj_lift M _).symm
  have hseg : segre (modelLift M (M.proj z) (M.proj z)) = (∏ k, c k) • segre z := by
    rw [hxc]; exact segre_smul c z
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (modelLift M (M.proj z) (M.proj z))) = (∏ k, c k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (modelLift M (M.proj z) (M.proj z))) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨by rw [h0]; exact hpc, ?_, ?_⟩
  · funext i
    simp only [modelQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [modelW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

theorem image_bad_null {E : Set M.Xc}
    (hE : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' E) = 0) :
    volume (modelQ M Ψ '' (modelBad M Ψ E ∩ {x | Ψ (segre (modelLift M x x)) 0 ≠ 0})) = 0 := by
  set A := M.atlas
  set G : Set M.Xc := {x | Ψ (segre (modelLift M x x)) 0 ≠ 0}
  set D : Fin A.n → Set (Fin e → ℂ) := fun j => {u | u ∈ (A.chart j).target ∧
    (A.chart j).symm u ∈ G ∧ ¬ (AnalyticAt ℂ (modelQ M Ψ ∘ (A.chart j).symm) u ∧
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}
  have han : ∀ j, ∀ u ∈ (A.chart j).target, (A.chart j).symm u ∈ G →
      AnalyticAt ℂ (modelQ M Ψ ∘ (A.chart j).symm) u := by
    intro j u hu hG
    have := analyticAt_modelQ M Ψ _ j ((A.chart j).map_target hu) hG
    rwa [(A.chart j).right_inv hu] at this
  have hsub : modelQ M Ψ '' (modelBad M Ψ E ∩ G) ⊆
      (⋃ j, (modelQ M Ψ ∘ (A.chart j).symm) ''
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (E ∩ G))) ∪
      ⋃ j, (modelQ M Ψ ∘ (A.chart j).symm) '' D j := by
    rintro _ ⟨x, ⟨hxb, hxG⟩, rfl⟩
    rcases hxb with hxE | hxc
    · obtain ⟨j, hj⟩ := A.cover x
      refine Or.inl (Set.mem_iUnion.mpr ⟨j, A.chart j x, ⟨(A.chart j).map_source hj, ?_⟩, ?_⟩)
      · rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact ⟨hxE, hxG⟩
      · simp [(A.chart j).left_inv hj]
    · rcases hxc with h0 | ⟨j, hj, hbad⟩
      · exact absurd h0 hxG
      · refine Or.inr (Set.mem_iUnion.mpr ⟨j, A.chart j x, ⟨(A.chart j).map_source hj, ?_, hbad⟩, ?_⟩)
        · show (A.chart j).symm (A.chart j x) ∈ G
          rw [(A.chart j).left_inv hj]; exact hxG
        · simp [(A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun j => ?_)
    (measure_iUnion_null fun j => ?_))
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
        (hE j))
    intro u hu
    exact ((han j u hu.1 hu.2.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u).restrictScalars ℝ) ?_ ?_
    · intro u hu
      exact ((han j u hu.1 hu.2.1).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro u hu
      have h0 : LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
        by_contra h
        exact hu.2.2 ⟨han j u hu.1 hu.2.1, h⟩
      have := abs_det_restrictScalars (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u)
      rw [h0, norm_zero, zero_pow two_ne_zero, abs_eq_zero] at this
      exact this

end ModelFibreSumAlmostEverywhere

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarChartSemipos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

theorem NbarChartSemipos.proof (hS : NbarSmooth.Statement) (hL : NbarLeviChart.Statement)
    (hA : APrimeChartMargin.Statement) : NbarChartSemipos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨c, hc, hAc⟩ := hA II Ψ K ι Ω E D O Lt X
  refine ⟨c, hc, fun B p q t δ hs hl hqp => ⟨hS II Ψ K ι Ω E D O Lt X B p q t hs, fun z hz w hw => ?_⟩⟩
  obtain ⟨k, hk⟩ := X.S.R.cover (X.M.proj z)
  have hk' : X.M.proj z ∈ X.S.R.mid k := X.S.R.inner_subset_mid k hk
  obtain ⟨v, hv, heq⟩ := hL II Ψ K ι Ω E D O Lt X B p q t hs z hz w hw k hk'
  have h1 := hl k _ hk' v
  have h2 := hAc z hz w k hk' v hv
  show 0 ≤ levi _ z w
  rw [heq]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 hq, mul_le_mul_of_nonneg_left h2 hp,
    mul_le_mul_of_nonneg_right hqp hv2]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjHoloLocal
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem holoOn_comp_compatChart_symm {d : ℕ} {X : Type} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas d X} {e : OpenPartialHomeomorph X (Fin d → ℂ)}
    (he : ReciprocityTheory.AnForm.M.IsCompatChart A e) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {u : Fin d → ℂ} (hu : u ∈ e.target) (huU : e.symm u ∈ U) :
    DifferentiableAt ℂ (g ∘ e.symm) u := by
  obtain ⟨j, hj⟩ := A.cover (e.symm u)
  have h1 : AnalyticAt ℂ (A.chart j ∘ e.symm) u := (he j).2 u ⟨hu, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart j).symm) ((A.chart j ∘ e.symm) u) := by
    refine hg j _ ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j (e.symm u)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact huU
  have h3 : g ∘ e.symm =ᶠ[𝓝 u] (g ∘ (A.chart j).symm) ∘ (A.chart j ∘ e.symm) := by
    have : ∀ᶠ u' in 𝓝 u, e.symm u' ∈ (A.chart j).source :=
      (e.continuousAt_symm hu).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
    filter_upwards [this] with u' hu'
    simp only [Function.comp, (A.chart j).left_inv hu']
  exact (h2.comp h1).differentiableAt.congr_of_eventuallyEq h3

theorem ProjHoloLocal.proof (hL : LocalOrbitChart.Statement)
    (hO : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement) : ProjHoloLocal.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D M e he z hz hze

  obtain ⟨N, hNo, hzN, κ, hκ, hκt, hκs⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z hz

  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections (M.proj z)
  obtain ⟨c, hc, hcz⟩ := (M.fibre z hz _ (hs _ hxU).1).1 (hs _ hxU).2.symm
  have hsxN : s (M.proj z) ∈ N := by rw [hcz]; exact (hκt z hzN c hc).1
  have hκsx : κ (s (M.proj z)) = κ z := by rw [hcz]; exact (hκt z hzN c hc).2
  have hsd : ∀ u ∈ e.target, e.symm u ∈ U → DifferentiableAt ℂ (s ∘ e.symm) u := fun u hu huU =>
    differentiableAt_pi.2 fun p => holoOn_comp_compatChart_symm he (hsh p) hu huU

  have hex : e (M.proj z) ∈ e.target := e.map_source hze
  have hexU : e.symm (e (M.proj z)) ∈ U := by rw [e.left_inv hze]; exact hxU
  have hTn : e.target ∩ e.symm ⁻¹' U ∩ (s ∘ e.symm) ⁻¹' N ∈ 𝓝 (e (M.proj z)) := by
    refine Filter.inter_mem (Filter.inter_mem (e.open_target.mem_nhds hex) ?_) ?_
    · exact (e.continuousAt_symm hex).preimage_mem_nhds (hUo.mem_nhds hexU)
    · refine (hsd _ hex hexU).continuousAt.preimage_mem_nhds (hNo.mem_nhds ?_)
      show s (e.symm (e (M.proj z))) ∈ N
      rw [e.left_inv hze]
      exact hsxN
  obtain ⟨T, hTsub, hTo, hxT⟩ := mem_nhds_iff.1 hTn
  have hψd : DifferentiableOn ℂ (κ ∘ s ∘ e.symm) T := fun u hu =>
    ((hκ _ (hTsub hu).2).differentiableAt.comp u
      (hsd u (hTsub hu).1.1 (hTsub hu).1.2)).differentiableWithinAt
  have hψi : Set.InjOn (κ ∘ s ∘ e.symm) T := by
    intro u hu u' hu' h
    have h1 := hs _ (hTsub hu).1.2
    have h2 := hs _ (hTsub hu').1.2
    obtain ⟨c', hc', hcc⟩ := hκs _ ⟨(hTsub hu).2, h1.1⟩ _ ⟨(hTsub hu').2, h2.1⟩ h
    have hp : M.proj (s (e.symm u)) = M.proj (s (e.symm u')) :=
      (M.fibre _ h1.1 _ h2.1).2 ⟨c', hc', hcc⟩
    rw [h1.2, h2.2] at hp
    exact e.symm.injOn (hTsub hu).1.1 (hTsub hu').1.1 hp

  obtain ⟨hψo, g, hg, hgψ⟩ := hO D.n T (κ ∘ s ∘ e.symm) hTo hψd hψi

  obtain ⟨O, hOo, hOeq⟩ :=
    continuousOn_iff'.1 M.cont (e.source ∩ e ⁻¹' T) (e.isOpen_inter_preimage hTo)
  refine ⟨O ∩ (N ∩ κ ⁻¹' ((κ ∘ s ∘ e.symm) '' T)),
    hOo.inter (hκ.continuousOn.isOpen_inter_preimage hNo hψo), ?_, g ∘ κ, ?_, ?_⟩
  · refine ⟨?_, hzN, e (M.proj z), hxT, ?_⟩
    · have hz' : z ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := ⟨⟨hze, hxT⟩, hz⟩
      rw [hOeq] at hz'
      exact hz'.1
    · show κ (s (e.symm (e (M.proj z)))) = κ z
      rw [e.left_inv hze]
      exact hκsx
  · intro w hw
    exact ((hg.differentiableAt (hψo.mem_nhds hw.2.2)).comp w
      (hκ w hw.2.1).differentiableAt).differentiableWithinAt
  · rintro z' ⟨⟨hz'O, hz'N, -⟩, hz'⟩
    have hp : z' ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := by
      rw [hOeq]
      exact ⟨hz'O, hz'⟩
    obtain ⟨⟨hpe, hpT⟩, -⟩ := hp
    refine ⟨hpe, ?_⟩
    have hpU : M.proj z' ∈ U := by
      have h := (hTsub hpT).1.2
      rwa [Set.mem_preimage, e.left_inv hpe] at h
    obtain ⟨c', hc', hcc⟩ := (M.fibre z' hz' _ (hs _ hpU).1).1 (hs _ hpU).2.symm
    have hκ' : κ (s (M.proj z')) = κ z' := by rw [hcc]; exact (hκt z' hz'N c' hc').2
    have hψz : (κ ∘ s ∘ e.symm) (e (M.proj z')) = κ z' := by
      show κ (s (e.symm (e (M.proj z')))) = κ z'
      rw [e.left_inv hpe]
      exact hκ'
    show e (M.proj z') = g (κ z')
    rw [← hψz, hgψ _ hpT]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelFibreFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ModelFibreFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ y, (modelQ M Ψ ⁻¹' {y} \ modelCrit M Ψ).Finite

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

