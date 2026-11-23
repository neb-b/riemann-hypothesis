module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnRightDerivativeFamilyModerateGrowth
section
noncomputable section

open Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped Topology

namespace GlobalTheory.TypeSum.DerFamCont

theorem exists_chart {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E)
    (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1) :
    ∃ (N : ℕ) (Y : Fin N → E) (Ψ : E → Fin N → ℝ), (∀ i, σ (Y i) = -Y i) ∧ Tendsto Ψ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ a in 𝓝 (1 : E), σ a * a = 1 → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let S : Submodule ℝ E := LinearMap.ker (σ + LinearMap.id)
  have hS : ∀ X, X ∈ S ↔ σ X = -X := fun X => by simp [S, add_eq_zero_iff_eq_neg]
  let b := Module.finBasis ℝ S
  let e : Fin (Module.finrank ℝ S) → E := fun i => b i
  have hli : LinearIndependent ℝ e := b.linearIndependent.map' S.subtype S.ker_subtype
  have he : ∀ i, σ (e i) = -e i := fun i => (hS _).1 (b i).2
  have hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e) := fun X hX => by
    have h := congrArg S.subtype (b.sum_repr ⟨X, (hS X).2 hX⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    rw [← h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ n : ℕ, σ (a ^ n) = σ a ^ n := fun n => by
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext n
    simp [hp]
  set Θ : (Fin _ → ℝ) → E := fun t => (List.ofFn fun i => NormedSpace.exp (t i • e i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, he, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  let T : (Fin _ → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod _ (fun i (t : Fin _ → ℝ) => NormedSpace.exp (t i • e i)) _ (fun i =>
      ⟨by simp, HasStrictFDerivAt.comp (0 : Fin _ → ℝ) (g := fun s : ℝ => NormedSpace.exp (s • e i))
        (by simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (e i) 0).hasStrictFDerivAt)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin _ => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ e hσ hli he hsp
  have hΦ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin (Module.finrank ℝ S) → ℝ) :
        (Fin (Module.finrank ℝ S) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ S) → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΦ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have p1 := hΦ.localInverse_tendsto
  have p3 := hΦ.eventually_right_inverse
  simp only [hΦ0] at p1 p3
  set Ψ := hΦ.localInverse _ _ _
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have ht : Tendsto (fun a => Θ (Ψ (P a))) (𝓝 1) (𝓝 1) := by
    have := hD.continuousAt.tendsto.comp p1
    rw [h0] at this
    exact this.comp hPt
  refine ⟨_, e, fun a => Ψ (P a), he, p1.comp hPt, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with a q1 q2 q3 ha
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 ha) (hP3 _ _ q1) q3 q2

variable {n : ℕ} {ε : Fin n → Bool}

theorem exists_chart_UJ (ε : Fin n → Bool) :
    ∃ (N : ℕ) (Y : Fin N → Mx n) (Ψ : Mx n → Fin N → ℝ), (∀ i, Y i ∈ lieSet ε) ∧ Tendsto Ψ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ a in 𝓝 (1 : Mx n), a ∈ UJset ε → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h2 := Jm_mul_self ε
  have hH : (Jm ε)ᴴ = Jm ε := by
    have h : (Jm ε)ᴴ * Jm ε = 1 := (maximal_compact_facts n ε).2.2.1.1.1
    rw [← Matrix.inv_eq_left_inv h, Matrix.inv_eq_left_inv h2]
  set J := Jm ε with hJdef
  let s : Mx n →ₗ[ℝ] Mx n :=
    { toFun := fun x => J * xᴴ * J
      map_add' := fun x y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, s x = J * xᴴ * J := fun _ => rfl
  have hJJ : ∀ x : Mx n, J * (J * x) = x := fun x => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  obtain ⟨N, Y, Ψ, hY, hΨ, hE⟩ := exists_chart s
    (fun a => by simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc, hJJ, h2,
      Matrix.mul_one])
    (fun a b => by simp only [hs, conjTranspose_mul, Matrix.mul_assoc, hJJ]) (by simp [hs, h2])
  refine ⟨N, Y, Ψ, fun i => ?_, hΨ, hE.mono fun g q hg => q ?_⟩
  · have := congrArg (J * ·) (hY i)
    simp only [hs, Matrix.mul_assoc, hJJ, Matrix.mul_neg] at this
    show (Y i)ᴴ * J + J * Y i = 0
    rw [this, neg_add_cancel]
  · have hg' : gᴴ * J * g = J := hg
    rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', h2]

theorem exists_step_bound {f f' : Mx n → ℂ} {X : Mx n} (hX : X ∈ lieSet ε) {C : ℝ} {N : ℕ}
    (hd : ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (f' g) 0)
    (hb : ∀ g ∈ UJset ε, ‖f' g‖ ≤ C * (1 + hs g) ^ N) :
    ∃ B : ℝ, ∀ a ∈ UJset ε, ∀ s ∈ Metric.closedBall (0 : ℝ) 1,
      ‖f (a * NormedSpace.exp (s • X)) - f a‖ ≤ |C| * ((1 + hs a) * B) ^ N * ‖s‖ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) 1).bddAbove_image
    (f := fun u : ℝ => 1 + hs (NormedSpace.exp (u • X)))
    (continuous_const.add (continuous_hs.comp (continuous_exp_smul X))).continuousOn
  refine ⟨B, fun a ha s hs1 => ?_⟩
  have := (convex_closedBall (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => f (a * NormedSpace.exp (t • X))) (f' := fun t => f' (a * NormedSpace.exp (t • X)))
    (C := |C| * ((1 + hs a) * B) ^ N) (x := 0) (y := s) (fun t _ => ?_) (fun t ht => ?_)
    (Metric.mem_closedBall_self zero_le_one) hs1
  · simpa using this
  · have k := hd _ (mul_mem_UJ ha (exp_mem_UJ hX t))
    have k2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact k)
    refine (k2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)).hasDerivWithinAt
    beta_reduce
    rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]
  · refine (hb _ (mul_mem_UJ ha (exp_mem_UJ hX t))).trans ?_
    have h0 := hs_nonneg (a * NormedSpace.exp (t • X))
    have h1 := hs_nonneg a
    refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity) (abs_nonneg C)
    exact (one_add_hs_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hB ⟨t, ht, rfl⟩) (by positivity))

theorem tendsto_prod {f : Mx n → ℂ} {α : Type} {L : Filter α} {g₀ : Mx n} {c : ℂ} {N : ℕ}
    (hf : ∀ X ∈ lieSet ε, ∃ (f' : Mx n → ℂ) (C : ℝ),
      (∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (f' g) 0) ∧
      ∀ g ∈ UJset ε, ‖f' g‖ ≤ C * (1 + hs g) ^ N) :
    ∀ (d : ℕ) (Y : Fin d → Mx n) (t : α → Fin d → ℝ) (a : α → Mx n), (∀ i, Y i ∈ lieSet ε) →
      (∀ i, Tendsto (fun p => t p i) L (𝓝 0)) → (∀ p, a p ∈ UJset ε) → Tendsto a L (𝓝 g₀) →
      Tendsto (fun p => f (a p)) L (𝓝 c) →
      Tendsto (fun p => f (a p * (List.ofFn fun i => NormedSpace.exp (t p i • Y i)).prod)) L (𝓝 c) := by
  intro d
  induction d with
  | zero => intro Y t a _ _ _ _ h; simpa using h
  | succ d ih =>
    intro Y t a hY ht ha hag hc
    simp only [List.ofFn_succ, List.prod_cons, ← Matrix.mul_assoc]
    refine ih (fun i => Y i.succ) (fun p i => t p i.succ) (fun p => a p * NormedSpace.exp (t p 0 • Y 0))
      (fun i => hY _) (fun i => ht _) (fun p => mul_mem_UJ (ha p) (exp_mem_UJ (hY 0) _)) ?_ ?_
    · have := hag.mul (((continuous_exp_smul (Y 0)).tendsto 0).comp (ht 0))
      simpa using this
    · obtain ⟨f', C, h1, h2⟩ := hf _ (hY 0)
      obtain ⟨B, hB⟩ := exists_step_bound (hY 0) h1 h2
      have h3 : Tendsto (fun p => f (a p * NormedSpace.exp (t p 0 • Y 0)) - f (a p)) L (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun p => |C| * ((1 + hs (a p)) * B) ^ N * ‖t p 0‖) ?_ ?_
        · filter_upwards [(ht 0).eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with p hp
          exact hB _ (ha p) _ hp
        · have := (((((continuous_hs.tendsto g₀).comp hag).const_add 1).mul_const B).pow N |>.const_mul |C|).mul
            (ht 0).norm
          simpa using this
      simpa using h3.add hc

theorem continuousOn_of_isDerFam : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ),
    IsDerFam ε F → FamGrowth ε N F →
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε) := by
  intro n ε N F hF hG l hl g₀ hg₀
  obtain ⟨d, Y, Ψ, hY, hΨ, hE⟩ := exists_chart_UJ ε
  have ht : Tendsto (fun g => g₀⁻¹ * g) (𝓝[UJset ε] g₀) (𝓝 1) := by
    have := ((continuous_const (y := g₀⁻¹)).matrix_mul continuous_id).tendsto g₀
    rw [id, inv_mul_UJ hg₀] at this
    exact this.mono_left nhdsWithin_le_nhds
  have key := tendsto_prod (ε := ε) (f := F l) (L := 𝓝[UJset ε] g₀) (g₀ := g₀) (c := F l g₀) (N := N)
    (fun X hX => by
      obtain ⟨C, hC⟩ := hG (X :: l) (List.forall_mem_cons.2 ⟨hX, hl⟩)
      exact ⟨F (X :: l), C, hF l hl X hX, hC⟩)
    d Y (fun g => Ψ (g₀⁻¹ * g)) (fun _ => g₀) hY (fun i => tendsto_pi_nhds.1 (hΨ.comp ht) i) (fun _ => hg₀)
    tendsto_const_nhds tendsto_const_nhds
  refine key.congr' ?_
  filter_upwards [ht.eventually hE, self_mem_nhdsWithin] with g q hg
  rw [q (mul_mem_UJ (inv_mem_UJ hg₀) hg), ← Matrix.mul_assoc, mul_inv_UJ hg₀, Matrix.one_mul]

end GlobalTheory.TypeSum.DerFamCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section
namespace GlobalTheory.KFinApprox

theorem approx_identity : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [TopologicalSpace X] (F : X → KG ε → ℂ),
    (Continuous fun p : X × KG ε => F p.1 p.2) → ∀ C : Set X, IsCompact C → ∀ δ : ℝ, 0 < δ →
    ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ x ∈ C, ‖F x 1 - ∫ k, e k * F x k ∂(muK ε)‖ < δ := by
  intro n ε X _ F hF C hC δ hδ

  have hFx : ∀ x, Continuous (F x) := fun x =>
    hF.comp (Continuous.prodMk continuous_const continuous_id)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact
  have hintR : ∀ g : KG ε → ℝ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

  have hG : Continuous fun z : KG ε × X => ‖F z.2 z.1 - F z.2 1‖ :=
    ((hF.comp (Continuous.prodMk continuous_snd continuous_fst)).sub
      (hF.comp (Continuous.prodMk continuous_snd continuous_const))).norm
  have hev : ∀ᶠ k in 𝓝 (1 : KG ε), ∀ x ∈ C, ‖F x k - F x 1‖ < δ / 3 := by
    refine hC.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have ht := hG.tendsto ((1 : KG ε), y)
    simp only [sub_self, norm_zero] at ht
    exact ht.eventually_lt_const (by positivity)
  obtain ⟨U, hUP, hUo, hU1⟩ := eventually_nhds_iff.1 hev

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hUo.isClosed_compl
    (isClosed_singleton (x := (1 : KG ε))) (Set.disjoint_singleton_right.2 (fun h => h hU1))
  have hf1' : f 1 = 1 := by simpa using hf1 (Set.mem_singleton (1 : KG ε))
  have hfnn : ∀ k, 0 ≤ f k := fun k => (hf01 k).1
  have hfU : ∀ k, k ∉ U → f k = 0 := fun k hk => by simpa using hf0 hk
  have hIpos : 0 < ∫ k, f k ∂(muK ε) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous
      (isClosed_tsupport _).isCompact (fun k => hfnn k) (x := 1) (by rw [hf1']; norm_num)
  obtain ⟨I, hIdef⟩ : ∃ I, ∫ k, f k ∂(muK ε) = I := ⟨_, rfl⟩
  rw [hIdef] at hIpos

  let ψ : C(KG ε, ℂ) := ⟨fun k => ((f k / I : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (f.continuous.div_const I)⟩
  have hψ : ∀ k, ψ k = ((f k / I : ℝ) : ℂ) := fun k => rfl
  have hψint : ∫ k, ψ k ∂(muK ε) = 1 := by
    simp only [hψ]
    rw [integral_complex_ofReal, integral_div, hIdef, div_self hIpos.ne']
    simp
  have hψnorm : ∀ k, ‖ψ k‖ = f k / I := fun k => by
    rw [hψ, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hfnn k) hIpos.le)]
  have h7 := GlobalTheory.KFinSep.finAlg_dense ε

  obtain ⟨M, hM⟩ := (hC.prod isCompact_univ).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨A, hA, hMA⟩ : ∃ A : ℝ, 0 < A ∧ M * (muK ε).real Set.univ ≤ A := by
    have hm : 0 ≤ (muK ε).real Set.univ := measureReal_nonneg
    refine ⟨(|M| + 1) * ((muK ε).real Set.univ + 1), by positivity, ?_⟩
    nlinarith [le_abs_self M, abs_nonneg M]
  have hη : 0 < δ / (3 * A) := div_pos hδ (by linarith)

  have hmem : ψ ∈ (GlobalTheory.KFinSep.finAlg ε).topologicalClosure := by
    rw [h7]; exact StarSubalgebra.mem_top
  have hmem' : ψ ∈ closure ((GlobalTheory.KFinSep.finAlg ε : Set C(KG ε, ℂ))) := hmem
  obtain ⟨p, hp, hpd⟩ := Metric.mem_closure_iff.1 hmem' (δ / (3 * A)) hη
  have hpK : KFinFun ε p := hp.1
  have hpk : ∀ k, ‖ψ k - p k‖ ≤ δ / (3 * A) := fun k => by
    have h := ContinuousMap.norm_coe_le_norm (ψ - p) k
    rw [← dist_eq_norm] at h
    simpa using h.trans hpd.le
  refine ⟨p, hpK, fun x hx => ?_⟩
  have i1 : Integrable (fun k => ψ k * F x 1) (muK ε) := hintC _ (ψ.continuous.mul continuous_const)
  have i2 : Integrable (fun k => ψ k * F x k) (muK ε) := hintC _ (ψ.continuous.mul (hFx x))
  have i3 : Integrable (fun k => p k * F x k) (muK ε) := hintC _ (p.continuous.mul (hFx x))
  have e1 : ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) = F x 1 - ∫ k, ψ k * F x k ∂(muK ε) := by
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hψint, one_mul]
  have e2 : ∫ k, (ψ k - p k) * F x k ∂(muK ε) =
      ∫ k, ψ k * F x k ∂(muK ε) - ∫ k, p k * F x k ∂(muK ε) := by
    simp_rw [sub_mul]
    exact integral_sub i2 i3
  have e3 : F x 1 - ∫ k, p k * F x k ∂(muK ε) =
      ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε) := by
    rw [e1, e2]; ring
  have b1 : ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε)‖ ≤ δ / 3 := by
    have hg : Integrable (fun k => f k / I * (δ / 3)) (muK ε) :=
      hintR _ ((f.continuous.div_const I).mul continuous_const)
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun k => ?_)).trans_eq ?_
    · rw [norm_mul, hψnorm]
      by_cases hk : k ∈ U
      · have := hUP k hk x hx
        rw [norm_sub_rev] at this
        exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hfnn k) hIpos.le)
      · rw [hfU k hk]; simp
    · rw [integral_mul_const, integral_div, hIdef, div_self hIpos.ne', one_mul]
  have b2 : ‖∫ k, (ψ k - p k) * F x k ∂(muK ε)‖ ≤ δ / 3 := by
    refine (norm_integral_le_of_norm_le_const (C := δ / (3 * A) * M)
      (Filter.Eventually.of_forall fun k => ?_)).trans ?_
    · rw [norm_mul]
      exact mul_le_mul (hpk k) (hM (x, k) ⟨hx, Set.mem_univ _⟩) (norm_nonneg _) hη.le
    · calc δ / (3 * A) * M * (muK ε).real Set.univ
          = δ / (3 * A) * (M * (muK ε).real Set.univ) := by ring
        _ ≤ δ / (3 * A) * A := mul_le_mul_of_nonneg_left hMA hη.le
        _ = δ / 3 := by field_simp
  rw [e3]
  calc ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε)‖
      ≤ δ / 3 + δ / 3 := (norm_add_le _ _).trans (add_le_add b1 b2)
    _ < δ := by linarith

end GlobalTheory.KFinApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsOrthonormalEigen
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.EigenSpan

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem inK_smul {X : Mx n} (hX : X ∈ lieSet ε) (hXs : Xᴴ = -X) (t : ℝ) : Formalism.REAL.inK ε ((t : ℂ) • X) := by
  have h0 : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hc : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
    rw [hXs, Matrix.neg_mul] at h0
    exact neg_add_eq_zero.1 h0
  refine ⟨?_, ?_⟩
  · show ((t : ℂ) • X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ((t : ℂ) • X) = 0
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc, mul_smul_comm, ← smul_add, h0,
      smul_zero]
  · rw [smul_mul_assoc, mul_smul_comm, hc]

theorem exp_mem_K {X : Mx n} (hX : X ∈ lieSet ε) (hXs : Xᴴ = -X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  have := (maximal_compact_facts n ε).2.2.2.1 _ (inK_smul hX hXs t)
  rwa [Complex.coe_smul] at this

theorem dRep_mem_of_kStable {X : Mx n} (hX : X ∈ lieSet ε) (hXs : Xᴴ = -X) {F : Submodule ℂ H}
    [FiniteDimensional ℂ F] (hF : IsKStableOn ε σ F) {v : H} (hv : v ∈ F) : dRep σ X v ∈ F := by
  have hc : IsClosed (F : Set H) := F.closed_of_finiteDimensional
  have hm : ∀ t : ℝ, σ (NormedSpace.exp (t • X)) v ∈ F := fun t => hF _ (exp_mem_K hX hXs t) v hv
  unfold dRep
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) 0
  · refine hc.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (F.restrictScalars ℝ).smul_mem _ (F.sub_mem (hm t) (hm 0))
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact F.zero_mem

theorem exists_kStable {p : ℕ} {x : Fin p → H} (hx : ∀ j, IsKFin ε σ (x j)) :
    ∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧ IsKStableOn ε σ F ∧ ∀ j, x j ∈ F := by
  unfold IsKFin at hx
  choose S hSfin hxS hSst using hx
  haveI : ∀ j, FiniteDimensional ℂ (S j) := hSfin
  refine ⟨⨆ j, S j, inferInstance, fun g hg v hv => ?_, fun j => Submodule.mem_iSup_of_mem j (hxS j)⟩
  refine Submodule.iSup_induction S (motive := fun v => σ g v ∈ ⨆ j, S j) hv
    (fun j v hv => Submodule.mem_iSup_of_mem j (hSst j g hg v hv)) ?_ ?_
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem inner_onePlusCas_self (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) :
    ⟪v, onePlusCas σ X v⟫_ℂ = ((‖v‖ ^ 2 + ∑ i, ‖dRep σ (X i) v‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ i, ⟪v, dRep σ (X i) (dRep σ (X i) v)⟫_ℂ = -⟪dRep σ (X i) v, dRep σ (X i) v⟫_ℂ := fun i =>
    inner_dRep (isUnit_Jm ε) hσ hv (dRep_mem (isUnit_Jm ε) hσ hv (hX i)) (hX i)
  simp only [onePlusCas, inner_sub_right, inner_sum, h, Finset.sum_neg_distrib, sub_neg_eq_add,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem exists_orthonormal_eigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (X : Fin d → Mx n),
    (∀ i, X i ∈ lieSet ε ∧ (X i)ᴴ = -X i) → ∀ (p : ℕ) (x : Fin p → H), (∀ j, IsKFin ε σ (x j)) →
    ∃ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e ∧ (∀ i, IsKFin ε σ (e i)) ∧ (∀ i, 1 ≤ μ i) ∧
      (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) ∧ ∀ j, x j = ∑ i, ⟪e i, x j⟫_ℂ • e i := by
  intro n ε H _ _ _ σ hS d X hX p x hx
  obtain ⟨F, hFfin, hFst, hxF⟩ := exists_kStable hx
  have hσ : IsURepOn (UJset ε) σ := hS.1
  have hXl : ∀ i, X i ∈ lieSet ε := fun i => (hX i).1
  have hKF : ∀ v ∈ F, IsKFin ε σ v := fun v hv => ⟨F, hFfin, hv, hFst⟩
  have hSm : ∀ v ∈ F, Sm ε σ v := fun v hv => hS.2.2.1 v (hKF v hv)
  have hD : ∀ i, ∀ v ∈ F, dRep σ (X i) v ∈ F := fun i v hv => dRep_mem_of_kStable (hX i).1 (hX i).2 hFst hv
  have hT : ∀ v ∈ F, onePlusCas σ X v ∈ F := fun v hv =>
    F.sub_mem hv (F.sum_mem fun i _ => hD i _ (hD i v hv))
  let T : F →ₗ[ℂ] F :=
    { toFun := fun v => ⟨onePlusCas σ X v, hT v v.2⟩
      map_add' := fun a b => Subtype.ext (by
        have h : ∀ i, dRep σ (X i) (dRep σ (X i) ((a : H) + b)) =
            dRep σ (X i) (dRep σ (X i) a) + dRep σ (X i) (dRep σ (X i) b) := fun i =>
          Dw_add hσ (l := [X i, X i]) (by simp [hXl i]) (hSm a a.2) (hSm b b.2)
        show onePlusCas σ X ((a : H) + b) = onePlusCas σ X a + onePlusCas σ X b
        simp only [onePlusCas, h, Finset.sum_add_distrib]
        abel)
      map_smul' := fun c a => Subtype.ext (onePlusCas_smul hσ hXl c (hSm a a.2)) }
  have hTv : ∀ v : F, (T v : H) = onePlusCas σ X v := fun v => rfl
  have hTs : T.IsSymmetric := fun a b => by
    rw [Submodule.coe_inner, Submodule.coe_inner, hTv, hTv]
    exact (inner_onePlusCas hσ hXl (hSm a a.2) (hSm b b.2)).symm
  let E := hTs.eigenvectorBasis (rfl : Module.finrank ℂ F = Module.finrank ℂ F)
  have hE : ∀ i, onePlusCas σ X (E i : H) = (hTs.eigenvalues rfl i : ℂ) • (E i : H) := fun i => by
    rw [← hTv]
    exact congrArg Subtype.val (hTs.apply_eigenvectorBasis rfl i)
  refine ⟨Module.finrank ℂ F, fun i => (E i : H), hTs.eigenvalues rfl, ?_, fun i => hKF _ (E i).2, fun i => ?_, hE,
    fun j => ?_⟩
  · exact E.orthonormal.comp_linearIsometry F.subtypeₗᵢ
  · have h1 := inner_onePlusCas_self hσ hXl (hSm _ (E i).2)
    have hn : ‖(E i : H)‖ = 1 := E.orthonormal.1 i
    rw [hE i, inner_smul_right, inner_self_eq_norm_sq_to_K, hn] at h1
    have h2 : hTs.eigenvalues rfl i = 1 + ∑ k, ‖dRep σ (X k) (E i : H)‖ ^ 2 := by
      simp only [RCLike.ofReal_one, Complex.ofReal_one, one_pow, mul_one] at h1
      exact_mod_cast h1
    rw [h2]
    have : 0 ≤ ∑ k, ‖dRep σ (X k) (E i : H)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  · have h := congrArg Subtype.val (E.sum_repr' ⟨x j, hxF j⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm

end GlobalTheory.TypeSum.EigenSpan
end
end

