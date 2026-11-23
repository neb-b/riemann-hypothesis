module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CauchyRiemannFacts
section
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_matrix_mul {A B : ℂ → Matrix (Fin n) (Fin n) ℂ} {A' B' : Matrix (Fin n) (Fin n) ℂ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  have hA' : HasDerivAt (fun τ => (A τ : Fin n → Fin n → ℂ)) (A' : Fin n → Fin n → ℂ) 0 := hA
  have hB' : HasDerivAt (fun τ => (B τ : Fin n → Fin n → ℂ)) (B' : Fin n → Fin n → ℂ) 0 := hB
  have h : HasDerivAt (fun τ => ((A τ * B τ : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ))
      ((A' * B 0 + A 0 * B' : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.mul_apply, Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun k _ => ?_
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA' i) k).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB' k) j)
  exact h

theorem fderiv_zOfE_raise (x : M2 n) (h : (u1 x).det ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * raiseR S) = WM x * S * (u1 x)⁻¹ := by
  let v := x * raiseR S
  have hl := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hg := (da_zOfE x h).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  simp only [id_eq, one_smul, Function.comp_def] at hg
  have hu : ∀ τ : ℂ, u1 (x + τ • v) = u1 x + τ • (u2 x * S) := fun τ => by
    rw [line_raise, first_cayley_block_mul_block, Matrix.mul_one, Matrix.mul_smul]
  have hN : ∀ τ : ℂ, Nm (x + τ • v) = Nm x + τ • (Nm' x * S) := fun τ => by
    rw [line_raise, Nm_mX, Matrix.mul_one, Matrix.mul_smul]
  have hc : Continuous fun τ : ℂ => (u1 x + τ • (u2 x * S)).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), (u1 x + τ • (u2 x * S)).det ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using h)
  have hB := ((hasDerivAt_id (0 : ℂ)).smul_const (u2 x * S)).const_add (u1 x)
  simp only [id_eq, one_smul] at hB
  have hL := hasDerivAt_matrix_mul hg hB
  have hR := ((hasDerivAt_id (0 : ℂ)).smul_const (Nm' x * S)).const_add (Nm x)
  simp only [id_eq, one_smul] at hR
  have heq : (fun τ : ℂ => zOfE (x + τ • v) * (u1 x + τ • (u2 x * S))) =ᶠ[𝓝 0]
      fun τ => Nm x + τ • (Nm' x * S) := by
    filter_upwards [hev] with τ hτ
    rw [← hu, zOfE_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (by rwa [hu])), Matrix.mul_one, hN]
  have hfin := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero] at hfin
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have key : fderiv ℂ zOfE x v * u1 x = WM x * S := by
    refine (eq_sub_of_add_eq hfin).trans ?_
    rw [WM, show (-(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂) = Nm' x from rfl, Matrix.sub_mul, Matrix.mul_assoc (zOfE x)]
  calc fderiv ℂ zOfE x v = fderiv ℂ zOfE x v * u1 x * (u1 x)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]
    _ = WM x * S * (u1 x)⁻¹ := congrArg (fun M => M * (u1 x)⁻¹) key

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₁₂_mul' (A B : M2 n) :
    (A * B).toBlocks₁₂ = A.toBlocks₁₁ * B.toBlocks₁₂ + A.toBlocks₁₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Nm x := by
  simp [toBlocks₁₁_mul', Cm, Nm, Matrix.mul_smul]

theorem mul_cm₁₂ (x : M2 n) : (x * Cm n).toBlocks₁₂ = Nm' x := by
  simp [toBlocks₁₂_mul', Cm, Nm', Matrix.mul_smul, Matrix.mul_neg]

theorem det_ne_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    intro h3
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, h3, zero_mul, Matrix.det_neg] at this
    simp at this
  exact h2 h1.symm

theorem det_cm_ne : (Cm n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (cm_mul_cmi (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem wm_det (x : M2 n) (hx : InG x) (h : (u1 x).det ≠ 0) : (WM x).det ≠ 0 := by
  intro hW
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hW
  set w := -(((u1 x)⁻¹ * u2 x) *ᵥ v)
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have hM : (x * Cm n) *ᵥ Sum.elim w v = 0 := by
    rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_mulVec, mul_cm₁₁, mul_cm₁₂, mul_cm₂₁, mul_cm₂₂]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have e1 : Nm x *ᵥ w + Nm' x *ᵥ v = WM x *ᵥ v := by
      simp only [w, WM, Matrix.mulVec_neg, Matrix.mulVec_mulVec, zOfE_eq, Matrix.sub_mulVec, Matrix.mul_assoc]
      rw [show -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂ = Nm' x from rfl]; abel
    have e2 : u1 x *ᵥ w + u2 x *ᵥ v = 0 := by
      simp only [w, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1,
        Matrix.one_mul, neg_add_cancel]
    rw [e1, e2, hv]
    funext i; cases i <;> simp
  have hdet : (x * Cm n).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero (det_ne_of_inG hx) det_cm_ne
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
  exact hv0 (funext fun i => by simpa using congrFun h0 (Sum.inr i))

theorem cra2 : CauchyRiemannFacts := by
  refine ⟨fun n m e y => orbital_function_eq_weighted m e y, fun n x h0 h => ⟨da_zOfE x h, fun m e => da_F0E m e x h0 h, fun Q =>
    ⟨fderiv_zOfE_low x h Q, fun m e => fderiv_F0E_low m e x h0 h Q⟩, fun R => ?_, fun hx => wm_det x hx h⟩⟩
  rw [sig_low]
  exact fderiv_zOfE_raise x h Rᴴ

end PositivityTheory.Rg.Sw.HSt.CR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FzDer
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.FL
open PositivityTheory.Rg.Sw.LVs.II (cE)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fzDer : FzDer := by
  intro n m e w Z b
  have hX : IsLie (if b = true then dir1 Z else dir2 Z) := lie_dir Z b
  haveI := kRCpt n
  have hc1 : Continuous fun k : KR n => rD (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rD _).comp continuous_subtype_val
  have hc2 : Continuous fun k : KR n => rA (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rA _).comp continuous_subtype_val
  obtain ⟨C1, hC1⟩ := (isCompact_range hc1).isBounded.exists_norm_le
  obtain ⟨C2, hC2⟩ := (isCompact_range hc2).isBounded.exists_norm_le
  refine ⟨|(e : ℝ)| * max C1 0 + ((m : ℝ) + 2 * ‖w‖) * max C2 0, by positivity, fun y => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  obtain ⟨R, hR, hRb⟩ := fz_deriv (x := mR (p * k)) hX (p * k).2 m e w
  refine ⟨R, ?_, ?_⟩
  · simp only [cE_eq_exp]
    exact hR
  · refine hRb.trans ?_
    have e1 : rD (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rD (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rD_up]
    have e2 : rA (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rA (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rA_up _ _ _ hp]
    have b1 : ‖rD (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C1 0 :=
      (hC1 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    have b2 : ‖rA (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C2 0 :=
      (hC2 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    rw [e1, e2, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    gcongr

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TopSeries
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

private theorem isCompact_KR' (n : ℕ) : IsCompact ((KR n : Set (GR n))) := by
  classical
  let S : Set (M2 n) := {x | InG x ∧ xᴴ * x = 1}
  have hSc : IsClosed S := by
    change IsClosed ({x : M2 n | InG x} ∩ {x : M2 n | xᴴ * x = 1})
    refine IsClosed.inter ?_ ?_
    · exact isClosed_eq
        ((((continuous_id : Continuous (fun x : M2 n => x)).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    · exact isClosed_eq (((continuous_id : Continuous (fun x : M2 n => x)).matrix_conjTranspose).matrix_mul continuous_id) continuous_const
  have hBox : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hSsub : S ⊆ (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) := by
    intro x hx i _ j _
    have hu : x ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hx.2
    simpa using entry_norm_bound_of_unitary hu i j
  have hS : IsCompact S := hBox.of_isClosed_subset hSc hSsub
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let φ : S → GR n := fun x =>
    ⟨⟨x.1, x.1ᴴ, mul_eq_one_comm.mp x.2.2, x.2.2⟩, x.2.1⟩
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
    exact continuous_subtype_val.matrix_conjTranspose
  have hR : (KR n : Set (GR n)) = Set.range φ := by
    ext Y
    constructor
    · intro hY
      refine ⟨⟨mR Y, hY⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
    · rintro ⟨x, rfl⟩
      exact x.2
  rw [hR]
  exact isCompact_range hφ

theorem topSeries (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) [MeasurableSpace (KR n)] [BorelSpace (KR n)]
    (μ : Measure (KR n)) [IsFiniteMeasure μ] {z : ℂ} (hz : t < z.re) (ρ : KR n → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (hρ : Continuous ρ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (ha : InG a) (hb : InG b) (g : G) (y : GR n) (y₀ : GlobalTheory.Eis.Cosets Pp Γ → GR n) (C : GlobalTheory.Eis.Cosets Pp Γ → ℂ)
    (hyC : ∀ q y', trm Ht f s₀ z (((q.out : Γ) : G) * g * ι y') = C q * fz m e (z - s₀) (mR (y₀ q * y'))) :
    Summable (fun q => C q * tOp μ (ιK n) ρ ψ a b (fz m e (z - s₀)) (mR (y₀ q * y))) ∧
    tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y) =
      d.eval z * ∑' q, C q * tOp μ (ιK n) ρ ψ a b (fz m e (z - s₀)) (mR (y₀ q * y)) := by
  classical
  haveI : CompactSpace (KR n) := isCompact_iff_compactSpace.mp (isCompact_KR' n)
  set A : GR n := grOf a ha with hA
  set B : GR n := grOf b hb with hB
  have hmul : ∀ Y₁ Y₂ : GR n, mR (Y₁ * Y₂) = mR Y₁ * mR Y₂ := fun _ _ => by simp [mR]
  have hY : ∀ (w : GR n) (k : KR n) (s : Fin n → Fin n → ℝ),
      mR w * ιK n k * a * nU (herm s) * b = mR (w * ((k : GR n) * A * nG s * B)) := by
    intro w k s
    simp only [hmul, ιK_apply, mR_nG, hA, hB, mR_grOf, mul_assoc]
  obtain ⟨hbd, hE⟩ := h.far z hz
  let P : KR n × (Fin n → Fin n → ℝ) → G := fun p => g * ι (y * ((p.1 : GR n) * A * nG p.2 * B))
  have hWc : Continuous fun p : KR n × (Fin n → Fin n → ℝ) => (p.1 : GR n) * A * nG p.2 * B :=
    (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_nG.comp continuous_snd)).mul continuous_const
  have hP : Continuous P := continuous_const.mul (h.ιc.comp (continuous_const.mul hWc))
  have hKc : IsCompact (P '' (Set.univ ×ˢ tsupport ψ)) := (isCompact_univ.prod hψc).image hP
  obtain ⟨u, hu, hub⟩ := hbd _ hKc
  have hterm : ∀ q (Y : GR n), GlobalTheory.Eis.term Pp Γ (fun x : G => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) (g * ι Y) q =
      C q * fz m e (z - s₀) (mR (y₀ q * Y)) := by
    intro q Y
    rw [← hyC q Y]
    simp only [GlobalTheory.Eis.term, trm, mul_assoc]
  have hBd : ∀ q (k : KR n) s, s ∈ tsupport ψ →
      ‖C q * fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B))))‖ ≤ |u q| := by
    intro q k s hs
    have h1 := hub (P (k, s)) ⟨(k, s), ⟨Set.mem_univ _, hs⟩, rfl⟩ q
    rw [hterm] at h1
    exact h1.trans (le_abs_self _)
  have hG : ∀ q, Continuous fun p : KR n × (Fin n → Fin n → ℝ) =>
      fz m e (z - s₀) (mR (y₀ q * (y * ((p.1 : GR n) * A * nG p.2 * B)))) := fun q =>
    (continuous_fzG (m := m) (e := e) hS (z - s₀)).comp (continuous_const.mul (continuous_const.mul hWc))
  have hfun : ∀ q (k : KR n) s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) =
      fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B)))) := by
    intro q k s
    rw [hY, mul_assoc]
  have hM : ∀ q, ∃ M : ℝ, ∀ (k : KR n) s, s ∈ tsupport ψ →
      ‖fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B))))‖ ≤ M := by
    intro q
    obtain ⟨M, hM⟩ := (isCompact_univ.prod hψc).exists_bound_of_continuousOn (hG q).continuousOn
    exact ⟨M, fun k s hs => hM (k, s) ⟨Set.mem_univ _, hs⟩⟩
  have hψi : Integrable (fun s => ‖ψ s‖) := (hψ.integrable_of_hasCompactSupport hψc).norm
  have hzero : ∀ s, s ∉ tsupport ψ → ψ s = 0 := fun s hs => image_eq_zero_of_notMem_tsupport hs
  have hIc : ∀ q, Continuous fun k : KR n =>
      ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s := by
    intro q
    obtain ⟨M, hMb⟩ := hM q
    simp_rw [hfun]
    refine continuous_of_dominated (bound := fun s => M * ‖ψ s‖) ?_ ?_ (hψi.const_mul M) ?_
    · intro k
      exact (((hG q).comp (continuous_const.prodMk continuous_id)).mul hψ).aestronglyMeasurable
    · intro k
      refine Filter.Eventually.of_forall fun s => ?_
      by_cases hs : s ∈ tsupport ψ
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hMb k s hs) (norm_nonneg _)
      · simp [hzero s hs]
    · refine Filter.Eventually.of_forall fun s => ?_
      exact ((hG q).comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hv : Summable fun q => |u q| := hu.abs
  have hv0 : ∀ q, 0 ≤ |u q| := fun q => abs_nonneg _
  have hFb : ∀ q (k : KR n) s,
      ‖C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤ |u q| * ‖ψ s‖ := by
    intro q k s
    rw [hfun, ← mul_assoc, norm_mul]
    by_cases hs : s ∈ tsupport ψ
    · exact mul_le_mul_of_nonneg_right (hBd q k s hs) (norm_nonneg _)
    · simp [hzero s hs]
  have hin : ∀ k : KR n,
      (Summable fun q => ∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)) ∧
      ∫ s, ∑' q, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) =
        ∑' q, ∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
    intro k
    refine integral_tsum_supp _ (fun q => |u q|) hv hv0 (fun s => ‖ψ s‖) hψi (fun q s => hFb q k s) ?_
    intro q
    simp_rw [hfun]
    exact (continuous_const.mul
      (((hG q).comp (continuous_const.prodMk continuous_id)).mul hψ)).aestronglyMeasurable
  have hIb : ∀ q (k : KR n),
      ‖C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤
        |u q| * (‖ρ k‖ * ∫ s, ‖ψ s‖) := by
    intro q k
    have h2 : ‖∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤
        ∫ s, |u q| * ‖ψ s‖ :=
      norm_integral_le_of_norm_le (hψi.const_mul _) (Filter.Eventually.of_forall fun s => hFb q k s)
    rw [integral_const_mul] at h2
    rw [integral_const_mul] at h2
    rw [mul_left_comm, norm_mul, norm_mul]
    rw [norm_mul] at h2
    calc ‖ρ k‖ * (‖C q‖ * ‖∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s‖)
        ≤ ‖ρ k‖ * (|u q| * ∫ s, ‖ψ s‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = |u q| * (‖ρ k‖ * ∫ s, ‖ψ s‖) := by ring
  have hbdρ : Integrable (fun k : KR n => ‖ρ k‖ * ∫ s, ‖ψ s‖) μ :=
    (hρ.norm.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hout := integral_tsum_supp (ν := μ)
    (fun q k => C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s))
    (fun q => |u q|) hv hv0 _ hbdρ hIb
    (fun q => (continuous_const.mul (hρ.mul (hIc q))).aestronglyMeasurable)
  have hpt : ∀ (k : KR n) s, resG ι (Ê z) g (mR y * ιK n k * a * nU (herm s) * b) * ψ s =
      d.eval z * ∑' q, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
    intro k s
    rw [hY, resG_mR, hE, cosetSum_apply, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hfun, ← mul_assoc (C q), ← hyC q]
    simp only [trm, mul_assoc]
  refine ⟨?_, ?_⟩
  · refine hout.1.congr fun q => ?_
    simp only [tOp, integral_const_mul]
  · have hL : ∀ k : KR n, ρ k * ∫ s, resG ι (Ê z) g (mR y * ιK n k * a * nU (herm s) * b) * ψ s =
        d.eval z * ∑' q, C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
      intro k
      simp_rw [hpt k]
      rw [integral_const_mul, (hin k).2]
      simp_rw [integral_const_mul]
      rw [mul_left_comm, ← tsum_mul_left]
      congr 1
      refine tsum_congr fun q => ?_
      ring
    simp only [tOp]
    simp_rw [hL]
    rw [integral_const_mul, hout.2]
    congr 1
    refine tsum_congr fun q => ?_
    rw [integral_const_mul]

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

