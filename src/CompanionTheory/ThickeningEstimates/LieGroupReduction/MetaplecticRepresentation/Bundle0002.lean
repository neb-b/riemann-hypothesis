module

public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousOm

@[expose] public section

-- bundled from CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticGroupT2Space
section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace MpE

omit [Fintype l] in
theorem toBlocks₁₁_one' : (1 : Mat l).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem sec_one : sec (1 : Mat l) = 1 := by
  rw [sec, block_inl_inl_one, block_inl_inr_one, block_inr_inl_one, toBlocks₁₁_one', Matrix.det_one, abs_one, Real.sqrt_one, inv_one,
    Ring.inverse_one, big_one]

theorem eventually_det_pos : ∀ᶠ s in 𝓝 (1 : Sp l), 0 < s.1.toBlocks₁₁.det := by
  have hc : Continuous fun s : Sp l => s.1.toBlocks₁₁.det :=
    Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
      continuous_subtype_val.matrix_elem (Sum.inl i) (Sum.inl j))
  have h1 : (1 : Sp l).1.toBlocks₁₁.det = 1 := by
    rw [show (1 : Sp l).1 = 1 from rfl, toBlocks₁₁_one', Matrix.det_one]
  have h2 : ∀ᶠ y in 𝓝 ((1 : Sp l).1.toBlocks₁₁.det), (0 : ℝ) < y := lt_mem_nhds (by rw [h1]; exact one_pos)
  exact (hc.tendsto 1).eventually h2

theorem eventually_det_pos_G : ∀ᶠ g in 𝓝 (1 : G l), 0 < (pr g).1.toBlocks₁₁.det := by
  have h := continuous_pr.tendsto (1 : G l)
  rw [map_one] at h
  exact h.eventually eventually_det_pos

theorem tendsto_sec (hD : SecDer l) (f : Sch l) :
    Tendsto (fun s : Sp l => schwartzToL2 l (sec s.1 f)) (𝓝 1) (𝓝 (schwartzToL2 l f)) := by
  let m' : (l ⊕ l) → (l ⊕ l) → (((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] ℝ) := fun a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => ℝ) b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => (l ⊕ l) → ℝ) a)
  have h := hD ((l ⊕ l) → (l ⊕ l) → ℝ) (fun x => Matrix.of x) m' (fun a b => (1 : Mat l) a b) rfl
    (fun a b => (m' a b).hasFDerivAt.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)) f
  have h2 : schwartzToL2 l (sec (Matrix.of fun a b => (1 : Mat l) a b) f) = schwartzToL2 l f := by
    rw [show (Matrix.of fun a b => (1 : Mat l) a b) = 1 from rfl, sec_one, ContinuousLinearMap.one_apply]
  have h3 : Tendsto (fun x : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (sec (Matrix.of x) f))
      (𝓝 (fun a b => (1 : Mat l) a b)) (𝓝 (schwartzToL2 l f)) := by
    convert h.continuousAt.tendsto using 2
    exact h2.symm
  have hc : Continuous fun s : Sp l => (fun a b => (s.1 : Mat l) a b : (l ⊕ l) → (l ⊕ l) → ℝ) :=
    continuous_pi fun a => continuous_pi fun b => continuous_subtype_val.matrix_elem a b
  have h4 : Tendsto (fun s : Sp l => (fun a b => (s.1 : Mat l) a b : (l ⊕ l) → (l ⊕ l) → ℝ)) (𝓝 1)
      (𝓝 (fun a b => (1 : Mat l) a b)) := hc.tendsto 1
  exact h3.comp h4

theorem exists_sch_ne : ∃ f : Sch l, schwartzToL2 l f ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_ne_zero (l := l) 0
  refine ⟨φ, fun h => hφ ?_⟩
  have : φ = 0 := injective_toLp 2 volume
    (show φ.toLp 2 volume = (0 : Sch l).toLp 2 volume by
      rw [← schwartzToL2_apply, ← schwartzToL2_apply, h, map_zero])
  simp [this]

end MpE

open MpE

theorem nearOne_of (hS : SecEx l) (hK : Ker l) (hD : SecDer l) : NearOne l := by
  obtain ⟨ε, -, hker, hεom⟩ := hK
  obtain ⟨f, hf⟩ := exists_sch_ne (l := l)
  have hv : 0 < ‖schwartzToL2 l f‖ := norm_pos_iff.2 hf
  have hom : ∀ᶠ g in 𝓝 (1 : G l), ‖om g (schwartzToL2 l f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := (continuous_om (schwartzToL2 l f)).tendsto (1 : G l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 h).eventually (gt_mem_nhds hv)
  have hsec : ∀ᶠ g in 𝓝 (1 : G l), ‖schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := continuous_pr.tendsto (1 : G l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 ((tendsto_sec hD f).comp h)).eventually (gt_mem_nhds hv)
  filter_upwards [eventually_det_pos_G, hom, hsec] with g h1 h2 h3
  obtain ⟨g', c, hg', hU, hc⟩ := hS (pr g) h1.ne'
  rw [hc h1, one_smul] at hU
  have hk : pr (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, hg', mul_inv_cancel]
  rcases (hker _).1 hk with h | h
  · rw [mul_inv_eq_one.1 h, hU, hg']
  · exfalso
    have hg : g = ε * g' := mul_inv_eq_iff_eq_mul.1 h
    have e1 : om g = om ε * om g' := by rw [hg, map_mul]
    have e : om g (schwartzToL2 l f) = -schwartzToL2 l (sec (pr g).1 f) := by
      rw [e1]
      show om ε (om g' (schwartzToL2 l f)) = _
      rw [hεom, om_sch, hU]
    rw [e] at h2
    have h4 : ‖schwartzToL2 l f + schwartzToL2 l f‖ ≤
        ‖schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ + ‖-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ := by
      have := norm_add_le (schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f) (-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f)
      have e2 : schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f + (-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f) =
          -(schwartzToL2 l f + schwartzToL2 l f) := by abel
      rwa [e2, norm_neg] at this
    have h5 : ‖schwartzToL2 l f + schwartzToL2 l f‖ = 2 * ‖schwartzToL2 l f‖ := by
      rw [← two_smul ℂ (schwartzToL2 l f), norm_smul]
      norm_num
    linarith

namespace MpE

theorem isInducing_F :
    IsInducing (fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l))) := ⟨rfl⟩

theorem metaplectic_group_t2Space : T2Space (G l) := by
  refine T2Space.of_injective_continuous (f := fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l)))
    ?_ isInducing_F.continuous
  intro g h hgh
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨h1, h2⟩ := hgh
  have hu : om g = om h := LinearIsometryEquiv.ext fun f => congrFun h2 f
  have hU : omS g = omS h := ContinuousLinearMap.ext fun f => by
    apply injective_toLp 2 volume
    show schwartzToL2 l (omS g f) = schwartzToL2 l (omS h f)
    rw [← om_sch, ← om_sch, hu]
  exact Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext hu (Units.ext hU)))

end MpE

theorem cover_of (hT : TopG l) (hO : Surj l) (hK : Ker l) (hS : SecEx l) (hD : SecDer l) : Cover l := by
  have : IsTopologicalGroup (G l) := hT
  have : T2Space (G l) := metaplectic_group_t2Space
  obtain ⟨ε, -, hker, -⟩ := hK
  have hσ : ∀ s : Sp l, ∃ g : G l, 0 < s.1.toBlocks₁₁.det → pr g = s ∧ omS g = sec s.1 := fun s => by
    by_cases h : 0 < s.1.toBlocks₁₁.det
    · obtain ⟨g, c, h1, h2, h3⟩ := hS s h.ne'
      exact ⟨g, fun _ => ⟨h1, by rw [h2, h3 h, one_smul]⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose σ hσ using hσ
  have hd : DenseRange (schwartzToL2 l) := by
    have h := SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ l) (F := ℂ)
      (μ := (volume : Measure (EuclideanSpace ℝ l))) (p := 2) ENNReal.ofNat_ne_top
    convert h using 1
    funext g
    rfl
  have hv : ∀ v : L2 l, Tendsto (fun s => om (σ s) v) (𝓝 1) (𝓝 v) := fun v => by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨φ, hφ⟩ := hd.exists_dist_lt v (show 0 < δ / 3 by positivity)
    have h1 := (Metric.tendsto_nhds.1 (tendsto_sec hD φ)) (δ / 3) (by positivity)
    filter_upwards [h1, eventually_det_pos] with s hs1 hs2
    have e : om (σ s) (schwartzToL2 l φ) = schwartzToL2 l (sec s.1 φ) := by rw [om_sch, (hσ s hs2).2]
    calc dist (om (σ s) v) v ≤ dist (om (σ s) v) (om (σ s) (schwartzToL2 l φ)) +
          dist (om (σ s) (schwartzToL2 l φ)) (schwartzToL2 l φ) + dist (schwartzToL2 l φ) v := dist_triangle4 _ _ _ _
      _ < δ := by
        rw [(om (σ s)).isometry.dist_eq, e, dist_comm (schwartzToL2 l φ) v]
        linarith
  have key : Tendsto σ (𝓝 1) (𝓝 1) := by
    have hpr : Tendsto (fun s => pr (σ s)) (𝓝 (1 : Sp l)) (𝓝 1) :=
      tendsto_id.congr' (eventually_det_pos.mono fun s hs => (hσ s hs).1.symm)
    have h2 : Tendsto (fun s => ((pr (σ s), fun f => om (σ s) f) : Sp l × (L2 l → L2 l))) (𝓝 1)
        (𝓝 ((pr (1 : G l), fun f => om (1 : G l) f))) := by
      rw [map_one, map_one]
      refine hpr.prodMk_nhds (tendsto_pi_nhds.2 fun v => ?_)
      simpa using hv v
    exact isInducing_F.tendsto_nhds_iff.2 h2
  have hopen : IsOpenMap (pr : G l → Sp l) := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨g, hg, rfl⟩
    have hc : Tendsto (fun t : Sp l => (pr g)⁻¹ * t) (𝓝 (pr g)) (𝓝 1) := by
      have : Continuous fun t : Sp l => (pr g)⁻¹ * t :=
        Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) fun t => ((pr g)⁻¹ * t).2
      simpa using this.tendsto (pr g)
    have h1 : Tendsto (fun t => g * σ ((pr g)⁻¹ * t)) (𝓝 (pr g)) (𝓝 g) := by
      have := ((continuous_const_mul g).tendsto 1).comp (key.comp hc)
      rwa [mul_one] at this
    filter_upwards [h1 (hU.mem_nhds hg), hc.eventually eventually_det_pos] with t ht ht'
    exact ⟨_, ht, by rw [map_mul, (hσ _ ht').1, mul_inv_cancel_left]⟩
  have hker' : ((pr : G l →* Sp l).ker : Set (G l)) = {1, ε} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hker g
  have hdisc : IsDiscrete ((pr : G l →* Sp l).ker : Set (G l)) := by
    rw [hker']
    exact ((Set.finite_singleton ε).insert 1).isDiscrete
  have hq : IsQuotientMap (pr : G l → Sp l) := hopen.isQuotientMap continuous_pr hO
  exact (hq.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom hdisc).isCoveringMap

end CompanionTheory.ThKR.Mp
end
end

-- bundled from CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MpFOne
section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff RealInnerProductSpace

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

theorem mq_add' (S T : Eu l →L[ℝ] Eu l) (g : Sch l) : mq (S + T) g = mq S g + mq T g := by
  ext x
  simp only [mq_apply, SchwartzMap.add_apply, ContinuousLinearMap.add_apply, inner_add_right]
  push_cast
  ring

theorem mq_smul' (c : ℝ) (S : Eu l →L[ℝ] Eu l) (g : Sch l) : mq (c • S) g = c • mq S g := by
  ext x
  simp only [mq_apply, SchwartzMap.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_right, Complex.real_smul]
  push_cast
  ring

theorem vf_add' (H K : Eu l →L[ℝ] Eu l) (g : Sch l) : vf (H + K) g = vf H g + vf K g := by
  ext x
  simp only [vf_apply, SchwartzMap.add_apply, ContinuousLinearMap.add_apply, map_add (f := _)]

theorem vf_smul' (c : ℝ) (H : Eu l →L[ℝ] Eu l) (g : Sch l) : vf (c • H) g = c • vf H g := by
  ext x
  simp only [vf_apply, SchwartzMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]

def qdLin (f : Sch l) : Mat l →ₗ[ℝ] Sch l where
  toFun X := Qd X f
  map_add' X Y := by
    have ht : (X + Y).toBlocks₁₁ = X.toBlocks₁₁ + Y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
    simp only [Qd, map_add (f := _), neg_add, mq_add', vf_add', ht, trace_add, add_div, ofReal_add, add_smul]
    abel
  map_smul' c X := by
    have ht : (c • X).toBlocks₁₁ = c • X.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
    have hc : ((c • X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f = c • (((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f) := by
      rw [smul_eq_mul, mul_div_assoc, ofReal_mul, mul_smul, Complex.coe_smul]
    simp only [Qd, map_smul, ← smul_neg, mq_smul', vf_smul', ht, trace_smul, RingHom.id_apply]
    rw [hc, (fou l).map_smul_of_tower, smul_sub, smul_add, smul_add]

theorem qd_sum (X : Mat l) (f : Sch l) : ∑ a, ∑ b, X a b • Qd (Matrix.single a b 1) f = Qd X f := by
  show _ = qdLin f X
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℝ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  rfl

theorem exp_mem_sp {X : Mat l} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    NormedSpace.exp X ∈ Matrix.symplecticGroup l ℝ := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have hu : IsUnit (Matrix.J l ℝ) :=
    ⟨⟨Matrix.J l ℝ, -Matrix.J l ℝ, by rw [mul_neg, J_squared, neg_neg], by rw [neg_mul, J_squared, neg_neg]⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : Xᵀ = Matrix.J l ℝ * -X * (Matrix.J l ℝ)⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᵀ * (Matrix.J l ℝ * NormedSpace.exp X) = Matrix.J l ℝ := by
    have := exp_mul_exp_neg (-X)
    rw [neg_neg] at this
    rw [← Matrix.exp_transpose, h1, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.J l ℝ),
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc, this, Matrix.mul_one]
  rw [SymplecticGroup.mem_iff', Matrix.mul_assoc]
  exact h2

theorem onePar_of (h1 : TopG l) (h2 : Cover l) (h3 : NearOne l) (h4 : SecDer l) : OnePar l := by
  have : IsTopologicalGroup (G l) := h1
  intro X hX
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ := fun t =>
    exp_mem_sp (SMulMemClass.smul_mem t hX)
  have hcont : Continuous fun t : ℝ => (NormedSpace.exp (t • X) : Mat l) :=
    continuous_pi fun a => continuous_pi fun b => continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ a b) X t).continuousAt
  let p : C(ℝ, Sp l) := ⟨fun t => ⟨NormedSpace.exp (t • X), hmem t⟩, hcont.subtype_mk _⟩
  have hp : ∀ t, (p t).1 = NormedSpace.exp (t • X) := fun t => rfl
  have hpadd : ∀ s t, p (s + t) = p s * p t := fun s t => Subtype.ext (by
    show NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X)
    rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
  have he : pr (1 : G l) = p 0 := by
    rw [map_one]
    exact Subtype.ext (by simp [hp])
  obtain ⟨Γ, ⟨hΓ0, hΓp⟩, -⟩ := h2.existsUnique_continuousMap_lifts p 0 1 he
  have hpr : ∀ t, pr (Γ t) = p t := fun t => congrFun hΓp t
  refine ⟨Γ, Γ.continuous, hΓ0, fun s t => ?_, fun t => by rw [hpr]; rfl, fun f => ?_⟩
  · have := h2.eq_of_comp_eq (g₁ := fun t => Γ (s + t)) (g₂ := fun t => Γ s * Γ t)
      (Γ.continuous.comp (continuous_const.add continuous_id)) (continuous_const.mul Γ.continuous)
      (funext fun t => by simp only [Function.comp, map_mul, hpr, hpadd]) 0 (by simp [hΓ0])
    exact congrFun this t
  · have h3' : ∀ᶠ g in 𝓝 (Γ 0), omS g = sec (pr g).1 := by rw [hΓ0]; exact h3
    have hev := (Γ.continuous.tendsto 0).eventually h3'
    have hd : ∀ a b, HasFDerivAt (fun x : ℝ => NormedSpace.exp (x • X) a b)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X a b)) 0 := fun a b => by
      have := hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ a b) X 0
      simp only [zero_smul, NormedSpace.exp_zero, one_mul, Matrix.entryLinearMap_apply] at this
      exact this.hasFDerivAt
    have hS := (h4 ℝ (fun x => NormedSpace.exp (x • X)) (fun a b => (1 : ℝ →L[ℝ] ℝ).smulRight (X a b)) 0
      (by simp) hd f).hasDerivAt
    have hval : (∑ a, ∑ b, ((1 : ℝ →L[ℝ] ℝ).smulRight (X a b)).smulRight
        (schwartzToL2 l (Qd (Matrix.single a b 1) f))) 1 = (quad X f).toLp 2 := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, one_smul]
      rw [show quad X f = Qd X f from quad_eq hX f, ← qd_sum X f]
      show _ = schwartzToL2 l _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, ContinuousLinearMap.map_smul_of_tower]
    rw [hval] at hS
    refine hS.congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    show om (Γ t) (schwartzToL2 l f) = _
    rw [om_sch, ht, hpr t]
    rfl

end CompanionTheory.ThKR.Mp
end
end

