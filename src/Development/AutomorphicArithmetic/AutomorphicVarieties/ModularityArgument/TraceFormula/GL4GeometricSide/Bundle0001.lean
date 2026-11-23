module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.HeckeMem
section
noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private def cos (U : Subgroup G) (a : G) : Set G := {y | a⁻¹ * y ∈ U}

private theorem cos_self (U : Subgroup G) (a : G) : a ∈ cos U a := by
  simp [cos, U.one_mem]

private theorem isOpen_cos {U : Subgroup G} (hU : IsOpen (U : Set G)) (a : G) : IsOpen (cos U a) :=
  hU.preimage (continuous_const.mul continuous_id)

private theorem exists_reps {U : Subgroup G} (hU : IsOpen (U : Set G)) {C : Set G} (hC : IsCompact C) :
    ∃ s : Finset G, (∀ a ∈ s, ∀ b ∈ s, ∀ y, y ∈ cos U a → y ∈ cos U b → a = b) ∧
      C ⊆ ⋃ a ∈ s, cos U a := by
  classical
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun g => cos U g)
    (fun g _ => (isOpen_cos hU g).mem_nhds (cos_self U g))
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ U))).image Quotient.out, ?_, ?_⟩
  · intro a ha b hb y hya hyb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb
    have hab : (Quotient.out q)⁻¹ * Quotient.out q' ∈ U := by
      have := U.mul_mem hya (U.inv_mem hyb)
      simpa [mul_assoc] using this
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ U) = QuotientGroup.mk (Quotient.out q') :=
      QuotientGroup.eq.2 hab
    have e : q = q' := by
      simpa [QuotientGroup.out_eq'] using this
    rw [e]
  · intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hr : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk g : G ⧸ U)) : G ⧸ U) = QuotientGroup.mk g :=
      QuotientGroup.out_eq' _
    have hgr : (Quotient.out (QuotientGroup.mk g : G ⧸ U))⁻¹ * g ∈ U := QuotientGroup.eq.1 hr
    refine Set.mem_iUnion₂.2 ⟨Quotient.out (QuotientGroup.mk g : G ⧸ U),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hg), ?_⟩
    have := U.mul_mem hgr hyg
    simpa [cos, mul_assoc] using this

private theorem integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] {U : Subgroup G} (hU : IsOpen (U : Set G))
    (hfin : μ (U : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ U, h (g * k) = h g) :
    ∃ s : Finset G, ∀ f : G → ℂ, (∀ g, ∀ k ∈ U, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ a ∈ s, (h a * (μ.real (U : Set G) : ℂ)) * f a := by
  classical
  obtain ⟨s, hdis, hcov⟩ := exists_reps hU hc.isCompact
  refine ⟨s, fun f hf => ?_⟩
  have hmeas : ∀ a, μ (cos U a) = μ (U : Set G) := fun a => measure_preimage_mul μ a⁻¹ (U : Set G)
  have hval : ∀ a y, y ∈ cos U a → h y * f y = h a * f a := by
    intro a y hy
    have e : y = a * (a⁻¹ * y) := by group
    rw [e, hinv a _ hy, hf a _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ a ∈ s, (cos U a).indicator (fun _ => h a * f a) y := by
    funext y
    by_cases hy : ∃ a ∈ s, y ∈ cos U a
    · obtain ⟨a, ha, hya⟩ := hy
      rw [Finset.sum_eq_single a, Set.indicator_of_mem hya, hval a y hya]
      · intro b hb hba
        exact Set.indicator_of_notMem (fun hyb => hba (hdis b hb a ha y hyb hya)) _
      · exact fun h' => (h' ha).elim
    · have hy0 : h y = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
        obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.1 (hcov hmem)
        exact ⟨a, ha, hya⟩
      rw [hy0, zero_mul]
      exact (Finset.sum_eq_zero fun a ha => Set.indicator_of_notMem (fun hya => hy ⟨a, ha, hya⟩) _).symm
  rw [hsum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_indicator_const _ (isOpen_cos hU a).measurableSet]
    simp only [Measure.real, hmeas a, Complex.real_smul]
    ring
  · intro a _
    refine (integrable_indicator_iff (isOpen_cos hU a).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas a]; exact hfin)

end Abs

theorem heckeMem : HeckeMem := by
  intro E _ _ _ n π K hKo hKc _ _ μf _ h hh ψ
  let St : Subgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | finRep E n k ψ.1 = ψ.1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSt : IsOpen (St : Set (GL (Fin n) (Af E))) := (π.cusp ψ.1 ψ.2).1.level
  have hU : IsOpen ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) := hKo.inter hSt
  have hfin : μf ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt hKc.measure_lt_top).ne
  obtain ⟨s, hs⟩ := integral_eq_sum μf hU hfin hh.1 (fun g k hk => by
    simpa using hh.2 1 K.one_mem k hk.1 g)
  let c : GL (Fin n) (Af E) → ℂ := fun a => h a * (μf.real ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) : ℂ)
  have hmem : ∑ g ∈ s, c g • finRep E n g ψ.1 ∈ π.V :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.stable (.fin g) ψ.1 ψ.2)
  have hop : (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 = heckeOp μf h ψ.1.1 := by
    funext x
    have hinv := hs (fun g => ψ.1.1 (x * finGL E n g)) (fun g k hk => by
      have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (show finRep E n k ψ.1 = ψ.1 from hk.2)
      have e' : ψ.1.1 (x * finGL E n g * finGL E n k) = ψ.1.1 (x * finGL E n g) := e
      simpa [mul_assoc] using e')
    rw [heckeOp, hinv]
    simp [c, Submodule.coe_sum, Finset.sum_apply]
    rfl
  refine ⟨s, c, ⟨_, hmem⟩, rfl, hop, fun k hk => ?_⟩
  refine Subtype.ext (funext fun x => ?_)
  change (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 (x * finGL E n k) = (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 x
  rw [hop]
  have e := integral_mul_left_eq_self (μ := μf) (fun g => h g * ψ.1.1 (x * finGL E n g)) k
  simp only [heckeOp]
  rw [← e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have e2 : h (k * g) = h g := by simpa using hh.2 k hk 1 K.one_mem g
  simp [e2, map_mul, mul_assoc]

end UpperTheory.V.Z.GSp4Splitting
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.IntegrableCoef
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

variable {n : ℕ}

private theorem cont_tr (E : PositivityTheory.RgBcC.KMod n) (T : E.V →L[ℂ] E.V) :
    Continuous fun κ : Un n =>
      LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) := by
  let L : (E.V →L[ℂ] E.V) →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ E.V).comp (ContinuousLinearMap.coeLM ℂ)
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact hL.comp (E.cont.mul continuous_const)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private theorem integrable_coef [CompactSpace (Un n)] [MeasurableSpace (Un n)] [BorelSpace (Un n)]
    (ν : Measure (Un n)) [IsFiniteMeasure ν] (σ : Un n →* (V →ₗ[ℂ] V)) (hσ : IsK σ)
    {f : Un n → ℂ} (hf : Continuous f) (v w : V) :
    Integrable (fun κ => f κ * ⟪w, σ κ v⟫_ℂ) ν :=
  (hf.mul (hσ.cont v w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem exists_avg [CompactSpace (Un n)] [MeasurableSpace (Un n)] [BorelSpace (Un n)]
    (ν : Measure (Un n)) [IsFiniteMeasure ν] (σ : Un n →* (V →ₗ[ℂ] V)) (hσ : IsK σ)
    {f : Un n → ℂ} (hf : Continuous f) (v : V) :
    ∃ p : V, ∀ w : V, ⟪w, p⟫_ℂ = ∫ κ, f κ * ⟪w, σ κ v⟫_ℂ ∂ν := by
  obtain ⟨S, hfd, hv, hS⟩ := hσ.fin v
  have hmem : ∀ κ, σ κ v ∈ S := fun κ => hS κ v hv
  let b := stdOrthonormalBasis ℂ S
  have hexp : ∀ κ, σ κ v = ∑ i, ⟪((b i : S) : V), σ κ v⟫_ℂ • ((b i : S) : V) := by
    intro κ
    have h := b.sum_repr' (⟨σ κ v, hmem κ⟩ : S)
    have h' := congrArg (Subtype.val) h
    simpa [Submodule.coe_sum, Submodule.coe_inner] using h'.symm
  refine ⟨∑ i, (∫ κ, f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ ∂ν) • ((b i : S) : V), fun w => ?_⟩
  have hint : ∀ κ, f κ * ⟪w, σ κ v⟫_ℂ =
      ∑ i, (f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ) * ⟪w, ((b i : S) : V)⟫_ℂ := by
    intro κ
    conv_lhs => rw [hexp κ]
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
    ring
  simp_rw [hint]
  rw [integral_finsetSum _ fun i _ => (integrable_coef ν σ hσ hf v _).mul_const _, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, integral_mul_const]

theorem avgEx : AvgEx := by
  intro n _ _ ν _ V _ _ σ hσ E T
  haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  have hf := cont_tr E T
  choose p hp using fun v : V => exists_avg ν σ hσ hf v
  have hI := fun v w : V => integrable_coef ν σ hσ hf v w
  refine ⟨{ toFun := p, map_add' := ?_, map_smul' := ?_ }, fun v w => hp v w⟩
  · intro x y
    refine ext_inner_left ℂ fun w => ?_
    rw [inner_add_right, hp, hp, hp, ← integral_add (hI x w) (hI y w)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_add (f := _), inner_add_right, mul_add]
  · intro c x
    refine ext_inner_left ℂ fun w => ?_
    rw [RingHom.id_apply, inner_smul_right, hp, hp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_smul, inner_smul_right]
    ring

end UpperTheory.V.Z.GSp4Splitting
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LieStab
section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open Matrix

private theorem flow {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (c : ℝ → S) (hc : ∀ t, HasDerivAt c (D (c t)) t) :
    c 1 = NormedSpace.exp D (c 0) := by
  have hψ : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • D) (c u)) 0 t := by
    intro t
    have he := (hasDerivAt_exp_smul_const (𝕂 := ℝ) D (1 - t)).comp_const_sub 1 t
    have h := he.clm_apply (hc t)
    convert h using 1
    simp [ContinuousLinearMap.mul_apply]
  have hconst := is_const_of_deriv_eq_zero
    (fun u => (hψ u).differentiableAt) (fun u => (hψ u).deriv) 1 0
  simpa using hconst

private theorem exp_mem {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (M : Submodule ℝ S) (hM : IsClosed (M : Set S)) (hD : ∀ y ∈ M, D y ∈ M)
    {x : S} (hx : x ∈ M) : NormedSpace.exp D x ∈ M := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) D
  have hs2 := (ContinuousLinearMap.apply ℝ S x).hasSum hs
  have hpow : ∀ m : ℕ, (D ^ m) x ∈ M := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact hD _ ih
  refine hM.mem_of_tendsto hs2 (Filter.Eventually.of_forall fun s => ?_)
  refine M.sum_mem fun m _ => ?_
  simpa using M.smul_mem _ (hpow m)

private theorem lift {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {S : Submodule ℂ V}
    {c : ℝ → S} {d : S} {t : ℝ} (h : HasDerivAt (fun s => (c s : V)) (d : V) t) : HasDerivAt c d t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  exact (Asymptotics.isLittleO_norm_left).1 h.norm_left

variable {n : ℕ}

private def curve (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (t : ℝ) : Un n :=
  ⟨NormedSpace.exp ((t : ℂ) • X), (UpperTheory.RealTr.skewExp n).1 _ (by
    rw [conjTranspose_smul, hX]; simp)⟩

private theorem curve_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    curve X hX (s + t) = curve X hX s * curve X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

private theorem curve_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : curve X hX 0 = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
  simp

end UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open UpperTheory.V.Z.GSp4Splitting.LieStabilizer in
theorem UpperTheory.V.Z.GSp4Splitting.lieStab :
    LieStab := by
  intro n V _ _ σ Kf hder N hN k x hx
  obtain ⟨X, hX, hXk⟩ := (UpperTheory.RealTr.skewExp n).2 k
  obtain ⟨S, hfd, hxS, hσS, hKS, hd⟩ := hder.2 x
  haveI : FiniteDimensional ℂ S := hfd
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : Module.End ℂ V := ∑ a, ∑ b, X a b • Kf a b
  have hLapp : ∀ w, L w = ∑ a, ∑ b, X a b • Kf a b w := by
    intro w
    simp [L, LinearMap.sum_apply]
  have hLS : ∀ w ∈ S, L w ∈ S := by
    intro w hw
    rw [hLapp]
    exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hKS a b w hw)
  have hLN : ∀ w ∈ N, L w ∈ N := by
    intro w hw
    rw [hLapp]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (hN a b w hw)
  let Dc : S →L[ℂ] S := LinearMap.toContinuousLinearMap (L.restrict hLS)
  let D : S →L[ℝ] S := Dc.restrictScalars ℝ
  have hDapp : ∀ w : S, ((D w : S) : V) = L w := fun w => rfl
  let γ := curve X hX
  let c : ℝ → S := fun t => ⟨σ (γ t) x, hσS _ _ hxS⟩
  have hc : ∀ t, HasDerivAt c (D (c t)) t := by
    intro t
    apply lift
    have h0 : HasDerivAt (fun s : ℝ => σ (γ s) (c t : V)) (L (c t : V)) (t - t) := by
      rw [sub_self, hLapp]
      exact hd X γ (fun _ => rfl) _ (c t).2
    have h1 := h0.comp_sub_const t t
    convert h1 using 1
    funext s
    have : γ s = γ (s - t) * γ t := by
      rw [← curve_add, sub_add_cancel]
    show σ (γ s) x = σ (γ (s - t)) (σ (γ t) x)
    rw [this, map_mul, Module.End.mul_apply]
    exact hDapp _
  have h1 := flow D c hc
  let M : Submodule ℂ S := N.comap S.subtype
  have hMc : IsClosed (M : Set S) := Submodule.closed_of_finiteDimensional M
  have hc0 : c 0 ∈ M.restrictScalars ℝ := by
    show σ (γ 0) x ∈ N
    have : γ 0 = 1 := curve_zero X hX
    rw [this, map_one]
    exact hx
  have h2 := exp_mem D (M.restrictScalars ℝ) hMc (fun y hy => hLN _ hy) hc0
  rw [← h1] at h2
  have hk : γ 1 = k := by
    apply Subtype.ext
    show NormedSpace.exp (((1 : ℝ) : ℂ) • X) = k.1
    simpa using hXk
  have h3 : σ (γ 1) x ∈ N := h2
  rwa [hk] at h3
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ProjEx
section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Un n →* (V →ₗ[ℂ] V)} {E : KMod n}

private theorem sig_inv (k : Un n) (y : V) : σ k (σ k⁻¹ y) = y := by
  have h : σ k * σ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact LinearMap.congr_fun h y

private theorem inner_sig (hσ : IsK σ) (k : Un n) (c y : V) : ⟪c, σ k y⟫_ℂ = ⟪σ k⁻¹ c, y⟫_ℂ := by
  have h := hσ.iso k (σ k⁻¹ c) y
  rw [sig_inv] at h
  exact h

private theorem range_mem (t : invA σ E) (ξ : E.V →L[ℂ] ℂ) : t.1 ξ ∈ isoSp σ E :=
  (le_iSup (fun t : invA σ E => LinearMap.range t.1) t) ⟨ξ, rfl⟩

private theorem iso_le {W : Submodule ℂ V} (h : ∀ (t : invA σ E) ξ, t.1 ξ ∈ W) : isoSp σ E ≤ W := by
  refine iSup_le fun t => ?_
  rintro _ ⟨ξ, rfl⟩
  exact h t ξ

private theorem map_iso (B : V →ₗ[ℂ] V) (hB : ∀ k x, B (σ k x) = σ k (B x)) {x : V}
    (hx : x ∈ isoSp σ E) : B x ∈ isoSp σ E := by
  have h : isoSp σ E ≤ (isoSp σ E).comap B := by
    refine iso_le fun t ξ => ?_
    have ht : B.comp t.1 ∈ invA σ E := fun k ξ => by
      simp only [LinearMap.comp_apply]
      rw [t.2 k ξ, hB]
    exact range_mem ⟨_, ht⟩ ξ
  exact h hx

private theorem iso_stable (k : Un n) {x : V} (hx : x ∈ isoSp σ E) : σ k x ∈ isoSp σ E := by
  have h : isoSp σ E ≤ (isoSp σ E).comap (σ k) := by
    refine iso_le fun t ξ => ?_
    show σ k (t.1 ξ) ∈ isoSp σ E
    rw [← t.2 k ξ]
    exact range_mem t _
  exact h hx

private theorem orth_stable (hσ : IsK σ) {K : Submodule ℂ V} (hK : ∀ k, ∀ x ∈ K, σ k x ∈ K)
    (k : Un n) {y : V} (hy : y ∈ Kᗮ) : σ k y ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro c hc
  rw [inner_sig hσ]
  exact hy _ (hK _ _ hc)

private theorem proj_comm (hσ : IsK σ) (K : Submodule ℂ V) [K.HasOrthogonalProjection]
    (hK : ∀ k, ∀ x ∈ K, σ k x ∈ K) (k : Un n) (x : V) :
    K.starProjection (σ k x) = σ k (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal (hK _ _ (K.starProjection_apply_mem x)) ?_
  rw [← map_sub]
  exact orth_stable hσ hK k (K.sub_starProjection_mem_orthogonal x)

private theorem core (hσ : IsK σ) (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (hS : ∀ k, ∀ x ∈ S, σ k x ∈ S) {x : V} (hx : x ∈ S) :
    ∃ u ∈ S ⊓ isoSp σ E, x - u ∈ (isoSp σ E)ᗮ := by
  let D : Submodule ℂ V := S ⊓ isoSp σ E
  haveI : FiniteDimensional ℂ D := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace D := FiniteDimensional.complete ℂ D
  let C : Submodule ℂ V := S ⊓ Dᗮ
  haveI : FiniteDimensional ℂ C := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace C := FiniteDimensional.complete ℂ C
  have hD : ∀ k, ∀ x ∈ D, σ k x ∈ D := fun k x hx => ⟨hS k x hx.1, iso_stable k hx.2⟩
  have hC : ∀ k, ∀ x ∈ C, σ k x ∈ C := fun k x hx => ⟨hS k x hx.1, orth_stable hσ hD k hx.2⟩
  have hu : D.starProjection x ∈ D := D.starProjection_apply_mem x
  refine ⟨D.starProjection x, hu, ?_⟩
  have hc : x - D.starProjection x ∈ C := ⟨S.sub_mem hx hu.1, D.sub_starProjection_mem_orthogonal x⟩
  have hIC : isoSp σ E ≤ Cᗮ := by
    intro y hy
    have h1 : C.starProjection y ∈ isoSp σ E :=
      map_iso (C.starProjection : V →ₗ[ℂ] V) (fun k z => proj_comm hσ C hC k z) hy
    have h2 : C.starProjection y ∈ C := C.starProjection_apply_mem y
    have h3 : C.starProjection y ∈ D := ⟨h2.1, h1⟩
    have h0 : C.starProjection y = 0 := by
      have h4 : C.starProjection y ∈ D ⊓ Dᗮ := ⟨h3, h2.2⟩
      rw [D.inf_orthogonal_eq_bot] at h4
      exact (Submodule.mem_bot ℂ).1 h4
    exact (Submodule.starProjection_apply_eq_zero_iff C).1 h0
  rw [Submodule.mem_orthogonal]
  intro y hy
  have h := (Submodule.mem_orthogonal _ _).1 (hIC hy) _ hc
  rw [← inner_conj_symm, h, map_zero]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.projEx :
    ProjEx := by
  intro n V _ _ σ hσ E
  haveI : (isoSp σ E).HasOrthogonalProjection := ⟨fun v => by
    obtain ⟨S, hfd, hx, hS⟩ := hσ.fin v
    haveI := hfd
    obtain ⟨u, hu, hv⟩ := core (E := E) hσ S hS hx
    exact ⟨u, hu.2, hv⟩⟩
  have hIs : ∀ k, ∀ x ∈ isoSp σ E, σ k x ∈ isoSp σ E := fun k x hx => iso_stable k hx
  refine ⟨((isoSp σ E).starProjection : V →ₗ[ℂ] V), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact Submodule.inner_starProjection_left_eq_right _ x y
  · intro x
    exact (isoSp σ E).starProjection_apply_mem x
  · intro x hx
    exact (Submodule.starProjection_eq_self_iff).2 hx
  · intro k
    ext x
    exact proj_comm hσ _ hIs k x
  · rintro B ⟨B', hadj, hcomm⟩
    have hB : ∀ x ∈ isoSp σ E, B x ∈ isoSp σ E := fun x hx =>
      map_iso B (fun k z => LinearMap.congr_fun (hcomm k).1 z) hx
    have hB' : ∀ x ∈ isoSp σ E, B' x ∈ isoSp σ E := fun x hx =>
      map_iso B' (fun k z => LinearMap.congr_fun (hcomm k).2 z) hx
    ext x
    show (isoSp σ E).starProjection (B x) = B ((isoSp σ E).starProjection x)
    refine Submodule.eq_starProjection_of_mem_orthogonal (hB _ ((isoSp σ E).starProjection_apply_mem x)) ?_
    rw [← map_sub, Submodule.mem_orthogonal]
    intro c hc
    have h := (Submodule.mem_orthogonal _ _).1 ((isoSp σ E).sub_starProjection_mem_orthogonal x) (B' c) (hB' c hc)
    rw [← inner_conj_symm, hadj, ← inner_conj_symm, h, map_zero, map_zero]
  · intro N hN x hx
    obtain ⟨S, hfd, hxS, hS⟩ := hσ.fin x
    haveI := hfd
    haveI : FiniteDimensional ℂ (S ⊓ N : Submodule ℂ V) := Submodule.finiteDimensional_inf_left S N
    obtain ⟨u, hu, hv⟩ := core (E := E) hσ (S ⊓ N) (fun k y hy => ⟨hS k y hy.1, hN k y hy.2⟩) ⟨hxS, hx⟩
    have he : (isoSp σ E).starProjection x = u := Submodule.eq_starProjection_of_mem_orthogonal hu.2 hv
    show (isoSp σ E).starProjection x ∈ N
    rw [he]
    exact hu.1.2
end

