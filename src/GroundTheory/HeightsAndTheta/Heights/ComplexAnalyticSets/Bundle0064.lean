module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology Filter Matrix ComplexSets

noncomputable section

namespace IsolatedFibreOpenPoly

variable {n d : ℕ}

def graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + d)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.append X p)

def graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + d)) ℂ) :=
  P.comap (graphSubst p)

def graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + d) → ℂ :=
  Fin.append x fun i => eval x (p i)

def firstPart (z : Fin (n + d) → ℂ) : Fin n → ℂ :=
  fun j => z (Fin.castAdd d j)

def lastRows (n d : ℕ) : Matrix (Fin d) (Fin (n + d)) ℂ :=
  fun i j => if j = Fin.natAdd n i then 1 else 0

theorem lastRows_mulVec (z : Fin (n + d) → ℂ) : lastRows n d *ᵥ z = fun i => z (Fin.natAdd n i) := by
  funext i
  simp [lastRows, Matrix.mulVec, dotProduct, ite_mul]

theorem firstPart_graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    firstPart (graphPt p x) = x := by
  funext j
  simp [firstPart, graphPt, Fin.append_left]

theorem graphPt_natAdd (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (i : Fin d) :
    graphPt p x (Fin.natAdd n i) = eval x (p i) := by
  simp [graphPt, Fin.append_right]

theorem continuous_firstPart : Continuous (firstPart : (Fin (n + d) → ℂ) → Fin n → ℂ) :=
  continuous_pi fun _ => continuous_apply _

theorem eval_graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (q : MvPolynomial (Fin (n + d)) ℂ) : eval x (graphSubst p q) = eval (graphPt p x) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [graphSubst]
  | add q r hq hr => simp only [map_add (f := _), hq, hr]
  | mul_X q i hq =>
    simp only [map_mul, graphSubst, aeval_X, eval_X]
    congr 1
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [graphPt, Fin.append_left]
    · simp [graphPt, Fin.append_right]

theorem graphSubst_rename (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    graphSubst p (rename (Fin.castAdd d) q) = q := by
  rw [graphSubst, aeval_rename]
  have h : (Fin.append X p ∘ Fin.castAdd d : Fin n → MvPolynomial (Fin n) ℂ) = X := by
    funext j
    simp [Fin.append_left]
  rw [h, aeval_X_left_apply]

theorem graphSubst_surjective (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Function.Surjective (graphSubst p) :=
  fun q => ⟨rename (Fin.castAdd d) q, graphSubst_rename p q⟩

theorem isPrime_graphIdeal {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.IsPrime)
    (p : Fin d → MvPolynomial (Fin n) ℂ) : (graphIdeal P p).IsPrime := by
  have := hP
  unfold graphIdeal
  infer_instance

theorem ringKrullDim_graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + d)) ℂ ⧸ graphIdeal P p) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set f : MvPolynomial (Fin (n + d)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mk P).comp (graphSubst p).toRingHom with hf
  have hsurj : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp (graphSubst_surjective p)
  have hker : graphIdeal P p = RingHom.ker f := by
    rw [hf, ← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj))

theorem graphPt_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin d → MvPolynomial (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ zeroSet P) : graphPt p x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) := by
  intro q hq
  rw [← eval_graphSubst]
  exact hx _ hq

theorem firstPart_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    firstPart z ∈ zeroSet P := by
  intro q hq
  have h := hz (rename (Fin.castAdd d) q) (by
    show graphSubst p (rename (Fin.castAdd d) q) ∈ P
    rw [graphSubst_rename]
    exact hq)
  rw [eval_rename] at h
  exact h

theorem natAdd_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) (i : Fin d) :
    z (Fin.natAdd n i) = eval (firstPart z) (p i) := by
  have h := hz (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) (by
    show graphSubst p (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) ∈ P
    rw [map_sub, graphSubst_rename, graphSubst, aeval_X, Fin.append_right, sub_self]
    exact P.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  exact h

theorem eq_graphPt_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    z = graphPt p (firstPart z) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun i => ?_) k
  · simp [graphPt, firstPart, Fin.append_left]
  · rw [natAdd_of_mem hz i, graphPt_natAdd]

theorem proof (hOpen : IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpen.Statement) : IsolatedFibreOpenPoly.Statement := by
  intro n d P p x hP hdim hx ⟨W, hW, hiso⟩ W' hW'
  have hV : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety (graphIdeal P p) d :=
    ⟨isPrime_graphIdeal hP p, by rw [ringKrullDim_graphIdeal]; exact hdim⟩
  have hAx : lastRows n d *ᵥ graphPt p x = fun i => eval x (p i) := by
    rw [lastRows_mulVec]
    funext i
    exact graphPt_natAdd p x i
  have hN : ∀ U ∈ 𝓝 x, firstPart ⁻¹' U ∈ 𝓝 (graphPt p x) := fun U hU =>
    continuous_firstPart.continuousAt.preimage_mem_nhds (by rw [firstPart_graphPt]; exact hU)
  have hisoG : ∀ z ∈ firstPart ⁻¹' W, z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) →
      lastRows n d *ᵥ z = lastRows n d *ᵥ graphPt p x → z = graphPt p x := by
    intro z hzW hz hAz
    have hfz : firstPart z = x := by
      refine hiso _ ⟨firstPart_mem hz, hzW⟩ fun i => ?_
      have h := congrFun hAz i
      rw [lastRows_mulVec, lastRows_mulVec] at h
      simp only at h
      rw [natAdd_of_mem hz, graphPt_natAdd] at h
      exact h
    rw [eq_graphPt_of_mem hz, hfz]
  have h := hOpen (n + d) d (graphIdeal P p) (lastRows n d) (graphPt p x) hV (graphPt_mem p hx)
    ⟨firstPart ⁻¹' W, hN W hW, hisoG⟩ (firstPart ⁻¹' W') (hN W' hW')
  rw [hAx] at h
  refine Filter.mem_of_superset h ?_
  rintro _ ⟨z, ⟨hz, hzW'⟩, rfl⟩
  refine ⟨firstPart z, ⟨firstPart_mem hz, hzW'⟩, ?_⟩
  show (fun i => eval (firstPart z) (p i)) = lastRows n d *ᵥ z
  rw [lastRows_mulVec]
  funext i
  exact (natAdd_of_mem hz i).symm

end IsolatedFibreOpenPoly

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem isClosed_zeroSetIn_of_ideal {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (zeroSetIn I) := by
  have h : zeroSetIn I = ⋂ q ∈ I, {z : σ → ℂ | eval z q = 0} := by
    ext z; simp [zeroSetIn]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem HolomorphicOnSubset.continuousWithinAt_trace {σ : Type*} [Fintype σ] {g : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S) {z : σ → ℂ} (hz : z ∈ S) :
    ContinuousWithinAt g S z := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg z hz
  have hFc : ContinuousAt F z := (hF.differentiableAt (hV.mem_nhds hzV)).continuousAt
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hgF ⟨hz, hzV⟩)
  filter_upwards [inter_mem_nhdsWithin S (hV.mem_nhds hzV)] with x hx using hgF hx

theorem HolomorphicOnSubset.differentiableAt_comp {σ : Type*} [Fintype σ] {k : ℕ}
    {g : (σ → ℂ) → ℂ} {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S)
    {s : (Fin k → ℂ) → σ → ℂ} {y : Fin k → ℂ} (hs : DifferentiableAt ℂ s y)
    (hS : ∀ᶠ y' in 𝓝 y, s y' ∈ S) : DifferentiableAt ℂ (fun y' => g (s y')) y := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg (s y) hS.self_of_nhds
  have hFd : DifferentiableAt ℂ F (s y) := hF.differentiableAt (hV.mem_nhds hzV)
  have hev : ∀ᶠ y' in 𝓝 y, s y' ∈ V := hs.continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)
  refine (hFd.comp y hs).congr_of_eventuallyEq ?_
  filter_upwards [hS, hev] with y' h1 h2 using hgF ⟨h1, h2⟩

theorem LocalTrace.proof (hbc : LocalBranchedCovering.Statement) : LocalTrace.Statement := by
  intro σ _ I w U g hI hw hU hg
  obtain ⟨k, A, W, D, m, δ, hWo, hwW, hWc, hWU, hDo, hAwD, hwonly, hprop, hδd, hδne, hsheets,
    hopen⟩ := hbc σ I w U hI hw hU
  have hZc : IsClosed (zeroSetIn I) := isClosed_zeroSetIn_of_ideal I
  have hKc : IsCompact (zeroSetIn I ∩ closure W) := hWc.inter_left hZc
  have hgc : ContinuousOn g (zeroSetIn I ∩ U) := fun z hz => hg.continuousWithinAt_trace hz
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ zeroSetIn I ∩ closure W, ‖g z‖ ≤ M :=
    hKc.exists_bound_of_continuousOn (hgc.mono (Set.inter_subset_inter_right _ hWU))

  obtain ⟨f, hf⟩ : ∃ f : (Fin k → ℂ) → ℂ,
      ∀ y, f y = ∑ᶠ z ∈ {z | z ∈ zeroSetIn I ∩ W ∧ A z = y}, g z := ⟨_, fun _ => rfl⟩
  have hfsum : ∀ (s : Fin m → σ → ℂ) (y : Fin k → ℂ),
      (∀ j, s j ∈ zeroSetIn I ∩ W ∧ A (s j) = y) → Function.Injective s →
      (∀ z ∈ zeroSetIn I ∩ W, A z = y → z ∈ Set.range s) → f y = ∑ j, g (s j) := by
    intro s y hs hinj hcov
    have hset : {z | z ∈ zeroSetIn I ∩ W ∧ A z = y} = Set.range s := by
      ext z
      constructor
      · rintro ⟨hz, hAz⟩
        exact hcov z hz hAz
      · rintro ⟨j, rfl⟩
        exact hs j
    rw [hf, hset, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  have hmemU : ∀ z ∈ zeroSetIn I ∩ W, z ∈ zeroSetIn I ∩ U := fun z hz =>
    ⟨hz.1, hWU (subset_closure hz.2)⟩
  have hfd : DifferentiableOn ℂ f (D ∩ {t | δ t ≠ 0}) := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    have hev : f =ᶠ[𝓝 y] fun y' => ∑ j, g (s j y') := by
      filter_upwards [hOo.mem_nhds hyO] with y' hy'
      exact hfsum (fun j => s j y') y' (hsO y' hy').1 (hsO y' hy').2.1 (hsO y' hy').2.2
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun j _ => ?_
    refine hg.differentiableAt_comp ((hsd j).differentiableAt (hOo.mem_nhds hyO)) ?_
    filter_upwards [hOo.mem_nhds hyO] with y' hy' using hmemU _ ((hsO y' hy').1 j).1
  have hfb : ∀ y ∈ D ∩ {t | δ t ≠ 0}, ‖f y‖ ≤ m * M := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    rw [hfsum (fun j => s j y) y (hsO y hyO).1 (hsO y hyO).2.1 (hsO y hyO).2.2]
    calc ‖∑ j, g (s j y)‖ ≤ ∑ j : Fin m, ‖g (s j y)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum fun j _ =>
          hM _ ⟨((hsO y hyO).1 j).1.1, subset_closure ((hsO y hyO).1 j).1.2⟩
      _ = m * M := by simp
  obtain ⟨T, hTd, hTf⟩ := RiemannExtensionAnalytic.proof k D δ f hDo hδd hδne hfd (fun τ _ =>
    ⟨Set.univ, Filter.univ_mem, isBounded_iff_forall_norm_le.2 ⟨m * M, by
      rintro _ ⟨y, ⟨⟨_, hyD⟩, hyδ⟩, rfl⟩
      exact hfb y ⟨hyD, hyδ⟩⟩⟩)
  refine ⟨k, A, W ∩ A ⁻¹' D, D, m, T, hWo.inter (hDo.preimage A.continuous), ⟨hwW, hAwD⟩,
    fun z hz => hWU (subset_closure hz.1), hDo, hAwD,
    fun z hz hAz => hwonly z ⟨hz.1, hz.2.1⟩ hAz, hTd, ?_⟩
  intro y hyD

  have hseq : ∀ n : ℕ, ∃ t ∈ D ∩ Metric.ball y (1 / ((n : ℝ) + 1)), δ t ≠ 0 := fun n =>
    hδne _ (hDo.inter Metric.isOpen_ball) Set.inter_subset_left
      ⟨y, hyD, Metric.mem_ball_self (by positivity)⟩
  choose t ht htδ using hseq
  have htD : ∀ n, t n ∈ D := fun n => (ht n).1
  have httend : Tendsto t atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (ht n).2)
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hX : ∀ n, ∃ X : Fin m → σ → ℂ, (∀ j, X j ∈ zeroSetIn I ∩ W ∧ A (X j) = t n) ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = t n → z ∈ Set.range X) ∧ T (t n) = ∑ j, g (X j) := by
    intro n
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets (t n) (htD n) (htδ n)
    obtain ⟨h1, h2, h3⟩ := hsO (t n) hyO
    exact ⟨fun j => s j (t n), h1, h3, by rw [hTf ⟨htD n, htδ n⟩, hfsum _ (t n) h1 h2 h3]⟩
  choose X hXmem hXcov hXT using hX

  have hKm : IsCompact (Set.univ.pi fun _ : Fin m => zeroSetIn I ∩ closure W) :=
    isCompact_univ_pi fun _ => hKc
  obtain ⟨x, hxK, φ, hφ, hXφ⟩ := hKm.tendsto_subseq (x := X) (fun n => Set.mem_univ_pi.2 fun j =>
    ⟨(hXmem n j).1.1, subset_closure (hXmem n j).1.2⟩)
  have hxK' : ∀ j, x j ∈ zeroSetIn I ∩ closure W := fun j => Set.mem_univ_pi.1 hxK j
  have hxj : ∀ j, Tendsto (fun n => X (φ n) j) atTop (𝓝 (x j)) := fun j => tendsto_pi_nhds.1 hXφ j
  have htφ : Tendsto (fun n => t (φ n)) atTop (𝓝 y) := httend.comp hφ.tendsto_atTop
  have hAx : ∀ j, A (x j) = y := fun j =>
    tendsto_nhds_unique ((A.continuous.tendsto _).comp (hxj j))
      (Tendsto.congr (fun n => ((hXmem (φ n) j).2).symm) htφ)
  have hxW : ∀ j, x j ∈ W := fun j => hprop (x j) (hxK' j) (by rw [hAx j]; exact hyD)
  have hT1 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (T y)) :=
    (hTd.differentiableAt (hDo.mem_nhds hyD)).continuousAt.tendsto.comp htφ
  have hT2 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (∑ j, g (x j))) := by
    have hs : Tendsto (fun n => ∑ j, g (X (φ n) j)) atTop (𝓝 (∑ j, g (x j))) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      exact (hgc (x j) ⟨(hxK' j).1, hWU (hxK' j).2⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hxj j, Filter.Eventually.of_forall fun n =>
          hmemU _ (hXmem (φ n) j).1⟩)
    exact Tendsto.congr (fun n => (hXT (φ n)).symm) hs
  refine ⟨x, fun j => ⟨⟨(hxK' j).1, hxW j, by show A (x j) ∈ D; rw [hAx j]; exact hyD⟩, hAx j⟩,
    ?_, tendsto_nhds_unique hT1 hT2⟩

  rintro z ⟨hzZ, hzW, -⟩ hAz
  by_contra hz
  have hne : ∀ j, 0 < dist z (x j) := fun j => dist_pos.2 fun h => hz ⟨j, h.symm⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo z hzW
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ r ∧ ∀ j, 2 * ε < dist z (x j) := by
    refine Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε) (Filter.Eventually.and (nhdsWithin_le_nhds (Iic_mem_nhds hr) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ r)
      (Filter.eventually_all.2 fun j => nhdsWithin_le_nhds ?_))
    have h2 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
    exact h2.eventually (gt_mem_nhds (hne j))
  obtain ⟨ε, hε0, hεr, hεd⟩ := hε.exists
  have hnbhd := hopen z ⟨hzZ, hzW⟩ ε hε0
  rw [hAz] at hnbhd
  have hev1 : ∀ᶠ n in atTop, t (φ n) ∈ A '' (zeroSetIn I ∩ Metric.ball z ε) := htφ hnbhd
  have hev2 : ∀ᶠ n in atTop, ∀ j, dist (X (φ n) j) (x j) < ε :=
    Filter.eventually_all.2 fun j => Metric.tendsto_nhds.1 (hxj j) ε hε0
  obtain ⟨n, ⟨z', ⟨hz'Z, hz'b⟩, hAz'⟩, hd⟩ := (hev1.and hev2).exists
  have hz'W : z' ∈ W := hrW (Metric.ball_subset_ball hεr hz'b)
  obtain ⟨j, hj⟩ := hXcov (φ n) z' ⟨hz'Z, hz'W⟩ hAz'
  have h1 := hd j
  rw [hj] at h1
  rw [Metric.mem_ball] at hz'b
  have h3 := dist_triangle z z' (x j)
  have h4 := hεd j
  rw [dist_comm] at hz'b
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Filter ComplexSets

open scoped ENNReal

noncomputable section

namespace LogIntegrableProof

variable {n : ℕ}

theorem lintegral_lt_top (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) {d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (u : Fin n → ℂ) (R : ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hu : linForm u ∉ J) :
    ∫⁻ z in zeroSetEuc J ∩ {z | ‖z‖ ≤ R}, ‖Real.log ‖∑ j, u j * z j‖‖ₑ
      ∂(μH[((2 * d : ℕ) : ℝ)]) < ⊤ := by
  obtain ⟨C, α, hα, hC⟩ := hS n d J u R hJ hdim hu
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} with hSdef
  set μ := (μH[((2 * d : ℕ) : ℝ)]).restrict S
  have hsub : S ⊆ zeroSetEuc J ∩ Metric.ball 0 (R + 1) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff]
    linarith [(show ‖z‖ ≤ R from hz.2)]
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ :=
    (measure_mono hsub).trans_lt (hF n d J hJ hdim (R + 1))
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin n) => ∑ j, u j * z j := by fun_prop
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => Real.log ‖∑ j, u j * z j‖
  have hFm : Measurable F := Real.measurable_log.comp hcont.norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun z => max (-F z) 0
  have hGm : Measurable G := hFm.neg.max measurable_const
  set M : ℝ := max (∑ j, ‖u j‖ * R) 0

  have hFle : ∀ z ∈ S, F z ≤ M := by
    intro z hz
    refine (Real.log_le_self (norm_nonneg _)).trans ((norm_sum_le _ _).trans ?_)
    refine le_trans ?_ (le_max_left _ _)
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le z j).trans hz.2) (norm_nonneg _)

  have hG : ∫⁻ z, ENNReal.ofReal (G z) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Eventually.of_forall fun z => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro z ⟨hz, hzS⟩
      refine ⟨hzS, ?_⟩
      have htF : F z ≤ -t := by
        rcases le_max_iff.mp (show t ≤ G z from hz) with h1 | h1
        · linarith
        · linarith
      change ‖∑ j, u j * z j‖ ≤ Real.exp (-t)
      rcases (norm_nonneg (∑ j, u j * z j)).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · exact (Real.log_le_iff_le_exp h0).mp htF
    · rw [← Real.exp_mul]; ring_nf
  have hle : ∀ z ∈ S, ‖F z‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G z) := by
    intro z hz
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hFle z hz
    rcases le_or_gt 0 (F z) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F z) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F z) 0; have := le_max_right (∑ j, ‖u j‖ * R) 0
      linarith
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun z => ENNReal.ofReal M + ENNReal.ofReal (G z))
    (measurable_const.add hGm.ennreal_ofReal) hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin, hG⟩

end LogIntegrableProof


open LogIntegrableProof in
theorem LogIntegrable.proof (hM : SheetSumMeasurable.Statement) (hD : ChartMassCompare.Statement)
    (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) : LogIntegrable.Statement := by
  intro n d J A u φ R hJ hdim hA hu hφ
  have hcont : Continuous fun x : Fin n → ℂ => linEval u x := by unfold linEval; fun_prop
  have hwm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (continuous_norm.comp hcont).measurable
  refine ⟨(hM n d J A _ φ hJ hdim hA (hwm.indicator measurableSet_closedBall) hφ).2.aestronglyMeasurable,
    ?_⟩
  obtain ⟨K, hK, hDK⟩ := hD n d J A φ R hJ hdim hA hφ

  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ L * ‖WithLp.ofLp z‖ :=
    ⟨(n : ℝ) ^ (2⁻¹ : ℝ), by positivity, fun z => by
      simpa [dist_zero_right] using
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (WithLp.ofLp z) 0⟩
  unfold HasFiniteIntegral
  refine (hDK _ hwm).trans_lt (ENNReal.mul_lt_top hK ?_)
  refine lt_of_le_of_lt (lintegral_mono_set ?_) (lintegral_lt_top hS hF u (L * R) hJ hdim hu)
  rintro z ⟨hz, hzB⟩
  refine ⟨hz, ?_⟩
  have : ‖WithLp.ofLp z‖ ≤ R := mem_closedBall_zero_iff.mp hzB
  exact (hL z).trans (mul_le_mul_of_nonneg_left this hL0)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormSheetedOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedOffDiscriminant.proof (hcut : PrimitiveFormSheetedLocusCutOut.Statement)
    (hnear : PrimitiveFormSheetedPointsNear.Statement) : PrimitiveFormSheetedOffDiscriminant.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨c, e, hc, he, hce, hsh⟩ := hcut σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  rcases hirr.2 c e hc he hce with hc0 | he0
  · exact ⟨_, hc0.and hsh, fun y hy hyδ => ((hy.2.2 hy.1 hyδ).1).2 (hy.2.1 hy.1)⟩
  · exfalso
    obtain ⟨z, hz, hzδ, hzs⟩ :=
      hnear σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ _ (he0.and hsh)
    exact (hz.2.2 hz.1 hzδ).2 hzs (hz.2.1 hz.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

