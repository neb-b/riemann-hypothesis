module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
public import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

@[expose] public section

section PartG1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open scoped InnerProductSpace

section SchurLemma

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def tent (x δ : ℝ) (t : ℝ) : ℝ := max 0 (1 - |t - x| / δ)

theorem tent_cont (x δ : ℝ) : Continuous (tent x δ) := by
  unfold tent
  fun_prop

theorem tent_self (x δ : ℝ) : tent x δ x = 1 := by simp [tent]

theorem tent_mul {x y : ℝ} (h : x ≠ y) (t : ℝ) : tent x (|x - y| / 2) t * tent y (|x - y| / 2) t = 0 := by
  have hd : 0 < |x - y| / 2 := by have := abs_pos.2 (sub_ne_zero.2 h); linarith
  by_cases h1 : |x - y| / 2 ≤ |t - x|
  · have : tent x (|x - y| / 2) t = 0 := by
      unfold tent
      apply max_eq_left
      have := (one_le_div hd).2 h1
      linarith
    rw [this, zero_mul]
  · have h2 : |x - y| / 2 ≤ |t - y| := by
      by_contra h2
      have h1 := not_le.1 h1
      have h2 := not_le.1 h2
      have : |x - y| ≤ |t - x| + |t - y| := by
        have e : x - y = (t - y) - (t - x) := by ring
        rw [e]
        have := abs_sub (t - y) (t - x)
        linarith
      linarith
    have : tent y (|x - y| / 2) t = 0 := by
      unfold tent
      apply max_eq_left
      have := (one_le_div hd).2 h2
      linarith
    rw [this, mul_zero]

theorem schur_selfAdjoint [Nontrivial H] (𝒮 : Set (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ U ∈ 𝒮, ∀ v ∈ S, U v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ U ∈ 𝒮, Commute A U) :
    ∃ a : ℝ, A = algebraMap ℝ (H →L[ℂ] H) a := by
  obtain ⟨a, ha⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have hsub : ∀ y ∈ spectrum ℝ A, y = a := by
    intro y hy
    by_contra hne
    set δ := |y - a| / 2 with hδ
    set F := cfc (tent y δ) A with hF
    set G := cfc (tent a δ) A with hG
    have hFG : F * G = 0 := by
      rw [hF, hG, ← cfc_mul (tent y δ) (tent a δ) A (tent_cont _ _).continuousOn (tent_cont _ _).continuousOn]
      have : (fun t => tent y δ t * tent a δ t) = fun _ => (0 : ℝ) := by
        funext t; exact tent_mul hne t
      rw [this, cfc_const_zero]
    have hne0 : ∀ x ∈ spectrum ℝ A, cfc (tent x δ) A ≠ 0 := by
      intro x hx h0
      have h1 : tent x δ x ∈ spectrum ℝ (cfc (tent x δ) A) := by
        rw [cfc_map_spectrum (tent x δ) A hA (tent_cont _ _).continuousOn]
        exact ⟨x, hx, rfl⟩
      rw [h0, spectrum.zero_eq, tent_self] at h1
      exact one_ne_zero h1
    have hGc : ∀ U ∈ 𝒮, Commute G U := fun U hU => (hc U hU).cfc_real _
    set S : Submodule ℂ H := (LinearMap.range (G : H →ₗ[ℂ] H)).topologicalClosure with hS
    have hSinv : ∀ U ∈ 𝒮, ∀ v ∈ S, U v ∈ S := by
      intro U hU v hv
      have hv' : v ∈ closure ((LinearMap.range (G : H →ₗ[ℂ] H)) : Set H) := hv
      refine map_mem_closure U.continuous hv' ?_
      rintro _ ⟨w, rfl⟩
      refine ⟨U w, ?_⟩
      have := congrArg (fun T : H →L[ℂ] H => T w) (hGc U hU).eq
      exact this
    have hSk : S ≤ LinearMap.ker (F : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ F.isClosed_ker
      rintro _ ⟨w, rfl⟩
      have := congrArg (fun T : H →L[ℂ] H => T w) hFG
      exact this
    rcases hirr S (Submodule.isClosed_topologicalClosure _) hSinv with h | h
    · apply hne0 a ha
      ext w
      have : G w ∈ S := Submodule.le_topologicalClosure _ ⟨w, rfl⟩
      rw [h] at this
      simpa using this
    · apply hne0 y hy
      ext w
      have : w ∈ S := by rw [h]; trivial
      exact hSk this
  refine ⟨a, ?_⟩
  calc A = cfc (id : ℝ → ℝ) A := (cfc_id ℝ A hA).symm
    _ = cfc (fun _ : ℝ => a) A := cfc_congr fun y hy => hsub y hy
    _ = algebraMap ℝ (H →L[ℂ] H) a := cfc_const a A hA

theorem schur_general [Nontrivial H] (𝒮 : Set (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ U ∈ 𝒮, ∀ v ∈ S, U v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hc : ∀ U ∈ 𝒮, Commute A U) (hc' : ∀ U ∈ 𝒮, Commute A (star U)) :
    ∃ z : ℂ, ∀ v, A v = z • v := by
  have hs : ∀ U ∈ 𝒮, Commute (star A) U := fun U hU => by
    have := (hc' U hU).star_star
    rwa [star_star] at this
  obtain ⟨a, ha⟩ := schur_selfAdjoint 𝒮 hirr (A + star A) (IsSelfAdjoint.add_star_self A)
    (fun U hU => (hc U hU).add_left (hs U hU))
  have hsa : IsSelfAdjoint (Complex.I • (A - star A)) := by
    rw [isSelfAdjoint_iff, star_smul, star_sub, star_star]
    simp only [RCLike.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
  obtain ⟨b, hb⟩ := schur_selfAdjoint 𝒮 hirr (Complex.I • (A - star A)) hsa
    (fun U hU => ((hc U hU).sub_left (hs U hU)).smul_left _)
  refine ⟨((a : ℂ) - Complex.I * b) / 2, fun v => ?_⟩
  have h1 : A v + star A v = (a : ℂ) • v := by
    have := congrArg (fun T : H →L[ℂ] H => T v) ha
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have h2 : Complex.I • (A v - star A v) = (b : ℂ) • v := by
    have := congrArg (fun T : H →L[ℂ] H => T v) hb
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have h3 : A v - star A v = -(Complex.I * b) • v := by
    have : A v - star A v = (-Complex.I) • (Complex.I • (A v - star A v)) := by
      rw [smul_smul]; simp
    rw [this, h2, smul_smul]; ring_nf
  have h4 : (2 : ℂ) • A v = ((a : ℂ) - Complex.I * b) • v := by
    have : (2 : ℂ) • A v = (A v + star A v) + (A v - star A v) := by rw [two_smul]; abel
    rw [this, h1, h3, ← add_smul]; ring_nf
  have h5 : A v = (2 : ℂ)⁻¹ • ((2 : ℂ) • A v) := by rw [smul_smul]; simp
  rw [h5, h4, smul_smul]
  congr 1
  ring

end SchurLemma

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartG1

section PartG2

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

section Ortho

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure SqRep (μ : Measure G) (σ : G → (H →L[ℂ] H)) : Prop where
  one : σ 1 = 1
  mul : ∀ a b, σ (a * b) = (σ a).comp (σ b)
  iso : ∀ g v, ‖σ g v‖ = ‖v‖
  cont : ∀ v, Continuous fun g => σ g v
  irr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤
  l2 : ∀ v w : H, MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 μ

variable {μ : Measure G} {σ : G → (H →L[ℂ] H)}

namespace SqRep

theorem inner_map (h : SqRep μ σ) (g : G) (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (h.iso g)).inner_map_map x y

theorem mul_inv_apply (h : SqRep μ σ) (g : G) (x : H) : σ g (σ g⁻¹ x) = x := by
  have := congrArg (fun T : H →L[ℂ] H => T x) (h.mul g g⁻¹)
  simp only [mul_inv_cancel, h.one] at this
  exact this.symm

theorem inner_inv (h : SqRep μ σ) (g : G) (x y : H) : ⟪σ g⁻¹ x, y⟫_ℂ = ⟪x, σ g y⟫_ℂ := by
  rw [← h.inner_map g (σ g⁻¹ x) y, h.mul_inv_apply]

def T (h : SqRep μ σ) (w : H) : H →ₗ[ℂ] Lp ℂ 2 μ where
  toFun v := (h.l2 v w).toLp _
  map_add' v v' := by
    apply Lp.ext
    filter_upwards [(h.l2 (v + v') w).coeFn_toLp, (h.l2 v w).coeFn_toLp, (h.l2 v' w).coeFn_toLp,
      Lp.coeFn_add ((h.l2 v w).toLp _) ((h.l2 v' w).toLp _)] with g h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3, map_add (f := _), inner_add_right]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(h.l2 (c • v) w).coeFn_toLp, (h.l2 v w).coeFn_toLp,
      Lp.coeFn_smul c ((h.l2 v w).toLp _)] with g h1 h2 h4
    rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, map_smul, inner_smul_right, smul_eq_mul]

theorem T_ae (h : SqRep μ σ) (w v : H) : (h.T w v : G → ℂ) =ᵐ[μ] fun g => ⟪w, σ g v⟫_ℂ :=
  (h.l2 v w).coeFn_toLp

theorem T_cont (h : SqRep μ σ) (w : H) : Continuous (h.T w) := by
  refine LinearMap.continuous_of_seq_closed_graph (h.T w) fun u x y hu hy => ?_
  have hm : TendstoInMeasure μ (fun n => ((h.T w (u n) : Lp ℂ 2 μ) : G → ℂ)) atTop (y : G → ℂ) :=
    tendstoInMeasure_of_tendsto_Lp hy
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  apply Lp.ext
  have hall : ∀ᵐ g ∂μ, ∀ n, (h.T w (u n) : G → ℂ) g = ⟪w, σ g (u n)⟫_ℂ :=
    ae_all_iff.2 fun n => h.T_ae w (u n)
  filter_upwards [hae, hall, h.T_ae w x] with g h1 h2 h3
  rw [h3]
  have h4 : Tendsto (fun i => ⟪w, σ g (u (ns i))⟫_ℂ) atTop (𝓝 ⟪w, σ g x⟫_ℂ) := by
    have hc : Continuous fun v : H => ⟪w, σ g v⟫_ℂ := continuous_const.inner (σ g).continuous
    exact (hc.tendsto x).comp (hu.comp hns.tendsto_atTop)
  have h5 : Tendsto (fun i => ⟪w, σ g (u (ns i))⟫_ℂ) atTop (𝓝 (y g)) := by
    refine h1.congr fun i => ?_
    exact h2 (ns i)
  exact tendsto_nhds_unique h5 h4

def Tc (h : SqRep μ σ) (w : H) : H →L[ℂ] Lp ℂ 2 μ := ⟨h.T w, h.T_cont w⟩

def II (μ : Measure G) (σ : G → (H →L[ℂ] H)) (v w v' w' : H) : ℂ :=
  ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ

theorem integrable (h : SqRep μ σ) (v w v' w' : H) :
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (h.Tc w' v') (h.Tc w v)).congr ?_
  filter_upwards [h.T_ae w v, h.T_ae w' v'] with g h1 h2
  have e1 : (h.Tc w v : G → ℂ) g = ⟪w, σ g v⟫_ℂ := h1
  have e2 : (h.Tc w' v' : G → ℂ) g = ⟪w', σ g v'⟫_ℂ := h2
  rw [e1, e2, RCLike.inner_apply]
  rfl

theorem inner_Tc (h : SqRep μ σ) (v w v' w' : H) : ⟪h.Tc w' v', h.Tc w v⟫_ℂ = II μ σ v w v' w' := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h.T_ae w v, h.T_ae w' v'] with g h1 h2
  have e1 : (h.Tc w v : G → ℂ) g = ⟪w, σ g v⟫_ℂ := h1
  have e2 : (h.Tc w' v' : G → ℂ) g = ⟪w', σ g v'⟫_ℂ := h2
  rw [e1, e2, RCLike.inner_apply]
  rfl

end SqRep

end Ortho

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartG2

section PartG3

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

section Ortho2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {μ : Measure G} {σ : G → (H →L[ℂ] H)}

namespace SqRep

theorem II_right [μ.IsMulRightInvariant] (h : SqRep μ σ) (a : G) (v w v' w' : H) :
    II μ σ (σ a v) w (σ a v') w' = II μ σ v w v' w' := by
  unfold II
  have e : ∀ g, ⟪w, σ g (σ a v)⟫_ℂ * star ⟪w', σ g (σ a v')⟫_ℂ =
      (fun x => ⟪w, σ x v⟫_ℂ * star ⟪w', σ x v'⟫_ℂ) (g * a) := by
    intro g
    simp only [h.mul g a, ContinuousLinearMap.comp_apply]
  simp_rw [e]
  exact integral_mul_right_eq_self (fun x => ⟪w, σ x v⟫_ℂ * star ⟪w', σ x v'⟫_ℂ) a

theorem II_inv [μ.IsInvInvariant] (h : SqRep μ σ) (v w v' w' : H) : II μ σ v w v' w' = II μ σ w' v' w v := by
  unfold II
  rw [← integral_inv_eq_self (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show ⟪w, σ g⁻¹ v⟫_ℂ * star ⟪w', σ g⁻¹ v'⟫_ℂ = ⟪v', σ g w'⟫_ℂ * star ⟪v, σ g w⟫_ℂ
  have e1 : ⟪w, σ g⁻¹ v⟫_ℂ = star ⟪v, σ g w⟫_ℂ := by
    rw [← inner_conj_symm, h.inner_inv]; rfl
  have e2 : star ⟪w', σ g⁻¹ v'⟫_ℂ = ⟪v', σ g w'⟫_ℂ := by
    have : star ⟪w', σ g⁻¹ v'⟫_ℂ = ⟪σ g⁻¹ v', w'⟫_ℂ := inner_conj_symm _ _
    rw [this, h.inner_inv]
  rw [e1, e2, mul_comm]

def AA (h : SqRep μ σ) (w w' : H) : H →L[ℂ] H := (ContinuousLinearMap.adjoint (h.Tc w')).comp (h.Tc w)

theorem inner_AA (h : SqRep μ σ) (v w v' w' : H) : ⟪v', h.AA w w' v⟫_ℂ = II μ σ v w v' w' := by
  unfold AA
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, h.inner_Tc]

theorem AA_comm [μ.IsMulRightInvariant] (h : SqRep μ σ) (w w' : H) (a : G) : Commute (h.AA w w') (σ a) := by
  show h.AA w w' * σ a = σ a * h.AA w w'
  ext v
  show h.AA w w' (σ a v) = σ a (h.AA w w' v)
  refine ext_inner_left ℂ fun v' => ?_
  rw [h.inner_AA, ← h.inner_inv, h.inner_AA]
  conv_lhs => rw [← h.mul_inv_apply a v']
  exact h.II_right a v w (σ a⁻¹ v') w'

theorem star_eq (h : SqRep μ σ) (a : G) : star (σ a) = σ a⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact fun x y => h.inner_inv a x y

theorem exists_scalar [Nontrivial H] [μ.IsMulRightInvariant] (h : SqRep μ σ) (w w' : H) :
    ∃ z : ℂ, ∀ v v', II μ σ v w v' w' = z * ⟪v', v⟫_ℂ := by
  obtain ⟨z, hz⟩ := schur_general (Set.range σ)
    (fun S hS hinv => h.irr S hS fun g v hv => hinv _ ⟨g, rfl⟩ v hv) (h.AA w w')
    (by rintro _ ⟨a, rfl⟩; exact h.AA_comm w w' a)
    (by rintro _ ⟨a, rfl⟩; rw [h.star_eq]; exact h.AA_comm w w' a⁻¹)
  refine ⟨z, fun v v' => ?_⟩
  rw [← h.inner_AA, hz, inner_smul_right]

theorem ortho [Nontrivial H] [μ.IsMulRightInvariant] [μ.IsInvInvariant] [μ.IsOpenPosMeasure] (h : SqRep μ σ) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  obtain ⟨e, he⟩ := exists_ne (0 : H)
  have hN : (0 : ℝ) < ‖e‖ ^ 2 := by positivity
  have hee : ⟪e, e⟫_ℂ = ((‖e‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  choose z hz using h.exists_scalar

  set J : ℝ := ∫ g, ‖⟪e, σ g e⟫_ℂ‖ ^ 2 ∂μ with hJ
  have hIJ : II μ σ e e e e = (J : ℂ) := by
    unfold II
    rw [hJ, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show ⟪e, σ g e⟫_ℂ * star ⟪e, σ g e⟫_ℂ = ((‖⟪e, σ g e⟫_ℂ‖ ^ 2 : ℝ) : ℂ)
    have := RCLike.mul_conj (⟪e, σ g e⟫_ℂ)
    rw [show star ⟪e, σ g e⟫_ℂ = (starRingEnd ℂ) ⟪e, σ g e⟫_ℂ from rfl, this]
    norm_cast
  have hcontc : Continuous fun g => ‖⟪e, σ g e⟫_ℂ‖ ^ 2 :=
    ((continuous_const.inner (h.cont e)).norm).pow 2
  have hint : Integrable (fun g => ‖⟪e, σ g e⟫_ℂ‖ ^ 2) μ := by
    have := (h.integrable e e e e).norm
    refine this.congr (Eventually.of_forall fun g => ?_)
    show ‖⟪e, σ g e⟫_ℂ * star ⟪e, σ g e⟫_ℂ‖ = ‖⟪e, σ g e⟫_ℂ‖ ^ 2
    rw [norm_mul, norm_star, sq]
  have hJpos : 0 < J := by
    have h0 : 0 ≤ J := integral_nonneg fun g => by positivity
    rcases h0.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have h2 := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hint).1 h1.symm
      have h3 : (fun g => ‖⟪e, σ g e⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) :=
        (hcontc.ae_eq_iff_eq μ (continuous_const (y := (0 : ℝ)))).1 h2
      have h4 : ‖⟪e, σ 1 e⟫_ℂ‖ ^ 2 = (0 : ℝ) := congrFun h3 1
      rw [h.one, one_apply_eq_self, hee] at h4
      have h5 : ‖((‖e‖ ^ 2 : ℝ) : ℂ)‖ = ‖e‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hN.le]
      rw [h5] at h4
      have : 0 < (‖e‖ ^ 2) ^ 2 := by positivity
      linarith
  have hNc : ((‖e‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'

  have hzw : ∀ w w', z w w' * ((‖e‖ ^ 2 : ℝ) : ℂ) = z e e * ⟪w, w'⟫_ℂ := by
    intro w w'
    rw [← hee, ← hz w w' e e, h.II_inv, hz e e w' w]
  have hzee : z e e * ((‖e‖ ^ 2 : ℝ) : ℂ) = (J : ℂ) := by rw [← hee, ← hz e e e e, hIJ]
  refine ⟨(‖e‖ ^ 2) ^ 2 / J, by positivity, fun v w v' w' => ⟨h.integrable v w v' w', ?_⟩⟩
  have hJc : (J : ℂ) ≠ 0 := by exact_mod_cast hJpos.ne'
  have key : II μ σ v w v' w' = z w w' * ⟪v', v⟫_ℂ := hz w w' v v'
  show II μ σ v w v' w' = _
  rw [key]
  have e1 : z w w' = z e e * ⟪w, w'⟫_ℂ / ((‖e‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hzw]; field_simp
  have e2 : z e e = (J : ℂ) / ((‖e‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hzee]; field_simp
  rw [e1, e2]
  push_cast
  have hne : ((‖e‖ : ℝ) : ℂ) ≠ 0 := by
    have : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    exact_mod_cast this
  field_simp

end SqRep

end Ortho2

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartG3

section PartA1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MultOne

end MultOne

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartA1

section PartA2

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

section Tr

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem conj_mem {P a : MatKR k r} (hP : IsCayleyU k r ε P) (ha : a ∈ UH (Hpk k r)) :
    P * a * P⁻¹ ∈ UJset ε ∧ P⁻¹ * (P * a * P⁻¹) * P = a := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r := hP.1.2
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  constructor
  · show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
    calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hH, ha']
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2]; simp
  · calc P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1]; simp

def cjH (P : MatKR k r) (hu : IsUnit P.det) : MatKR k r ≃ₜ MatKR k r where
  toFun x := P⁻¹ * x * P
  invFun y := P * y * P⁻¹
  left_inv x := by
    have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    calc P * (P⁻¹ * x * P) * P⁻¹ = (P * P⁻¹) * x * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [h2]; simp
  right_inv y := by
    have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
    calc P⁻¹ * (P * y * P⁻¹) * P = (P⁻¹ * P) * y * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [h1]; simp
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def ioP (P : MatKR k r) (g : Formalism.REAL.UJ ε) : Mt k r := P⁻¹ * umat g * P

theorem measurableEmbedding_conjCayley {P : MatKR k r} (hP : IsCayleyU k r ε P) : MeasurableEmbedding (ioP (ε := ε) P) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => (cjH P hu) (umat g)) :=
    (cjH P hu).isClosedEmbedding.comp (Formalism.REAL.isClosedEmbeddingMatrix _ ε).1
  have h2 : Topology.IsClosedEmbedding (ioP (ε := ε) P) := h1
  exact h2.measurableEmbedding

theorem conj_mem_unitaryGroup {P : MatKR k r} (hP : IsCayleyU k r ε P) (g : Formalism.REAL.UJ ε) :
    Matrix.of (ioP P g) ∈ UH (Hpk k r) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r := hP.1.2
  have hg : (umat g)ᴴ * Formalism.REAL.Jm ε * umat g = Formalism.REAL.Jm ε := g.2
  show (P⁻¹ * umat g * P)ᴴ * Hpk k r * (P⁻¹ * umat g * P) = Hpk k r
  rw [← hH]
  calc (P⁻¹ * umat g * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * umat g * P)
      = Pᴴ * ((umat g)ᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * umat g) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * ((umat g)ᴴ * Formalism.REAL.Jm ε * umat g) * P := by rw [h2]; simp
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by rw [hg]

theorem isHaarOn_map_conjCayley {P : MatKR k r} (hP : IsCayleyU k r ε P) :
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ((Formalism.REAL.muG ε).map (ioP P)) := by
  have hemb := measurableEmbedding_conjCayley hP
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨hemb.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h0
    exact (NeZero.ne (Formalism.REAL.muG ε)) h0
  · rw [hemb.map_apply]
    have : ioP P ⁻¹' {x | Matrix.of x ∉ UH (Hpk k r)} = (∅ : Set (Formalism.REAL.UJ ε)) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact conj_mem_unitaryGroup hP g
    rw [this, measure_empty]
  · intro s hs
    have hm : Measurable (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply]
      refine Finset.measurable_sum _ fun l _ => ?_
      have h0 : Measurable fun x : Mt k r => x l j := by fun_prop
      exact h0.const_mul _
    rw [Measure.map_map hm hemb.measurable]
    set s' : Formalism.REAL.UJ ε := Formalism.REAL.indefiniteUnitaryMk ε (P * s * P⁻¹) (conj_mem hP hs).1 with hs'
    have hcomp : lmulM s ∘ ioP (ε := ε) P = ioP P ∘ fun g => s' * g := by
      funext g
      show s * (P⁻¹ * umat g * P) = P⁻¹ * (P * s * P⁻¹ * umat g) * P
      calc s * (P⁻¹ * umat g * P) = (P⁻¹ * P) * s * (P⁻¹ * umat g * P) := by rw [h1]; simp
        _ = P⁻¹ * (P * s * P⁻¹ * umat g) * P := by simp only [Matrix.mul_assoc]
    rw [hcomp, ← Measure.map_map hemb.measurable (measurable_const_mul s'), map_mul_left_eq_self]

theorem transport {P : MatKR k r} (hP : IsCayleyU k r ε P) {μ : Measure (Mt k r)}
    (hμ : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • (Formalism.REAL.muG ε).map (ioP P) := by
  obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨c1, a1, a2, e1⟩ := BridgeLemma₃.hu_eq_smul (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν hμ
  obtain ⟨c2, b1, b2, e2⟩ := BridgeLemma₃.hu_eq_smul (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν (isHaarOn_map_conjCayley hP)
  refine ⟨c1 / c2, ENNReal.div_ne_zero.2 ⟨a1, b2⟩, ENNReal.div_ne_top a2 b1, ?_⟩
  rw [e1, e2, smul_smul, ENNReal.div_mul_cancel b1 b2]

theorem schur_hpk {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : MatKR k r → (H →L[ℂ] H)}
    {P : MatKR k r} (hP : IsCayleyU k r ε P) {d : ℝ} (hd : IsFdeg (Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d)
    {μG : Measure (Mt k r)} (hμ : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG) :
    ∃ d' : ℝ, 0 < d' ∧ ∀ v w v' w' : H,
      Integrable (fun x => inner ℂ w (σ (Matrix.of x) v) * star (inner ℂ w' (σ (Matrix.of x) v'))) μG ∧
      ∫ x, inner ℂ w (σ (Matrix.of x) v) * star (inner ℂ w' (σ (Matrix.of x) v')) ∂μG =
        inner ℂ v' v * inner ℂ w w' / (d' : ℂ) := by
  obtain ⟨c, c0, ctop, hc⟩ := transport hP hμ
  have hc' : 0 < c.toReal := ENNReal.toReal_pos c0 ctop
  obtain ⟨hd0, hS⟩ := hd
  refine ⟨d / c.toReal, div_pos hd0 hc', fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := hS v w v' w'
  have hemb := measurableEmbedding_conjCayley (ε := ε) hP
  constructor
  · rw [hc]
    refine Integrable.smul_measure ?_ ctop
    rw [hemb.integrable_map_iff]
    exact hi
  · rw [hc, integral_smul_measure, hemb.integral_map]
    have : (∫ g, inner ℂ w (σ (Matrix.of (ioP P g)) v) * star (inner ℂ w' (σ (Matrix.of (ioP P g)) v'))
        ∂(Formalism.REAL.muG ε)) = inner ℂ v' v * inner ℂ w w' / (d : ℂ) := he
    rw [this, Complex.real_smul]
    push_cast
    have h1 : (c.toReal : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
    have h2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    field_simp

end Tr

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartA2

section PartG4

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

section Fdeg

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance muG_right : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩

instance muG_inv : (Formalism.REAL.muG ε).IsInvInvariant :=
  ⟨Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular n ε⟩

instance muG_open : (Formalism.REAL.muG ε).IsOpenPosMeasure := by unfold Formalism.REAL.muG; infer_instance

theorem sqRep_of_isDS [CompleteSpace H] {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (h : IsDS ε lam σ) : SqRep (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (umat g)) := by
  obtain ⟨-, -, ⟨⟨h1, hm⟩, hiso, hcont⟩, hirr, hl2, -⟩ := h
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  refine ⟨h1, fun a b => hm _ (hmem a) _ (hmem b), fun g v => hiso _ (hmem g) v, fun v => ?_, fun S hS hinv => ?_, hl2⟩
  · exact (hcont v).comp_continuous (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous hmem
  · refine hirr S hS fun g hg v hv => ?_
    exact hinv (Formalism.REAL.indefiniteUnitaryMk ε g hg) v hv

theorem fdeg_exists {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsDS ε lam σ) :
    ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d := by
  have : CompleteSpace H := h.1
  have : Nontrivial H := h.2.1
  obtain ⟨d, hd, ho⟩ := (sqRep_of_isDS h).ortho
  exact ⟨d, hd, ho⟩

end Fdeg

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartG4

section PartR1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open Formalism.MainNotions.S.Loc Formalism.MainNotions.BridgeLemma ValuativeRel IsDedekindDomain NumberField Topology

section Resid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

end Resid

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartR1

section PartR2

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.BridgeLemma ValuativeRel IsDedekindDomain NumberField Ideal

section PrimeSum

end PrimeSum

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartR2

section PartS1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.LocalBesselAndTopKernel Formalism.MainNotions.BridgeLemma

section S27

end S27

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartS1

section PartM1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

section Homog

variable {k r : ℕ}

end Homog

section Scale

variable (D : D7)

end Scale

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartM1

section PartM2

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.MainNotions.UniformConstantsAndStatements ValuativeRel IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable (D : D7)

variable {D}

theorem hypTT_all (u u' : D.what₂.Word) : HypTT D u u' := by
  have hg0 := (D.host.g_prime 0).two_le
  have hg1 := (D.host.g_prime 1).two_le
  set G := D.host.g 0 * D.host.g 1 with hG
  have hG4 : 4 ≤ G := by nlinarith
  have hGG : 1 < G ^ 2 := by nlinarith
  have t1 := T_mod D u
  have t2 := T_mod D u'
  rw [Nat.mod_eq_of_lt hGG] at t1 t2
  have p1 := (D.mem u).A.T_prime
  have p2 := (D.mem u').A.T_prime
  have three : ∀ T : ℕ, T.Prime → T % G ^ 2 = 1 → 3 ≤ T := by
    intro T hT hm
    by_contra h3
    have : T < 3 := by omega
    interval_cases T
    · exact Nat.not_prime_zero hT
    · exact Nat.not_prime_one hT
    · rw [Nat.mod_eq_of_lt (by nlinarith)] at hm; omega
  refine ⟨p1, p2, three _ p1 t1, three _ p2 t2, ?_⟩
  have hm : (D.mem u).A.T ≡ (D.mem u').A.T [MOD G ^ 2] := by
    unfold Nat.ModEq; rw [t1, t2]
  have hm' : (D.mem u).A.T ≡ (D.mem u').A.T [MOD G] := Nat.ModEq.of_dvd (Dvd.intro_left _ (sq G).symm) hm
  exact Int.natCast_modEq_iff.2 hm'

end Main

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartM2

section PartM3

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.MainNotions.UniformConstantsAndStatements ValuativeRel IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main2

variable {D : D7}

variable {eps : ℝ} (Fm : FamP eps)

end Main2

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartM3
