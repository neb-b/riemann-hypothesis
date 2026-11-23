module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyBallSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevInequalityAtOneIndefiniteUnitary
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.SobolevHaar

theorem cube_step {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ)
    (c : Fin (N + 1) → ℝ → G) (s : ℝ) (hs : 0 < s)
    (hc : ∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b)
    (f f' : G → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt (fun t => f (x * c (Fin.last N) t)) (f' x) 0) :
    ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖f (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod‖ ^ 2 ≤
      2 / s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖f (List.ofFn fun i => c i (t i)).prod‖ ^ 2) +
      2 * s * ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖f' (List.ofFn fun i => c i (t i)).prod‖ ^ 2 := by
  set l := Fin.last N with hl
  have hΘ := continuous_prod_ofFn_curves (N + 1) c (fun i => (hc i).1)
  have hΘ' := continuous_prod_ofFn_curves N (fun i => c i.castSucc) (fun i => (hc _).1)
  have hsn : ∀ (t : Fin N → ℝ) (r : ℝ),
      (List.ofFn fun i => c i (Fin.snoc (α := fun _ => ℝ) t r i)).prod
        = (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r := by
    intro t r
    rw [List.ofFn_succ']
    simp [hl]
  have fub : ∀ w : G → ℂ, Continuous w →
      IntegrableOn (fun t : Fin N → ℝ => ∫ r in (0 : ℝ)..s,
        ‖w ((List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r)‖ ^ 2)
        (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) ∧
      ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖w (List.ofFn fun i => c i (t i)).prod‖ ^ 2 =
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∫ r in (0 : ℝ)..s,
        ‖w ((List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r)‖ ^ 2 := by
    intro w hw
    have h := integral_cube_succ_last N s
      (fun t => ‖w (List.ofFn fun i => c i (t i)).prod‖ ^ 2) ((hw.comp hΘ).norm.pow 2)
    simp only [hsn] at h
    simp only [intervalIntegral.integral_of_le hs.le, ← integral_Icc_eq_integral_Ioc]
    exact h
  obtain ⟨i1, b1⟩ := fub f hf
  obtain ⟨i2, b2⟩ := fub f' hf'
  have pt : ∀ x : G, ‖f x‖ ^ 2 ≤ 2 / s * (∫ r in (0 : ℝ)..s, ‖f (x * c l r)‖ ^ 2)
      + 2 * s * ∫ r in (0 : ℝ)..s, ‖f' (x * c l r)‖ ^ 2 := by
    intro x
    have h := sobolev_endpoint_one_variable ℂ (fun r => f (x * c l r))
      (fun r => f' (x * c l r)) s hs ?_ ?_
    · simpa only [(hc l).2.1, mul_one] using h
    · intro r _
      have h1 : HasDerivAt (fun t => f (x * c l r * c l t)) (f' (x * c l r)) (r - r) := by
        rw [sub_self]; exact hd _
      have h2 := h1.comp_sub_const r r
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [mul_assoc, ← (hc l).2.2, add_sub_cancel]
    · exact (hf'.comp (continuous_const.mul (hc l).1)).continuousOn
  have i0 : IntegrableOn (fun t : Fin N → ℝ =>
      ‖f (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod‖ ^ 2)
      (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) :=
    ((hf.comp hΘ').norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have key := integral_mono i0 ((i1.const_mul (2 / s)).add (i2.const_mul (2 * s)))
    (fun t => pt _)
  simp only [Pi.add_apply] at key
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul] at key
  rw [b1, b2]
  exact key

theorem cube_sum {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Set V) (u : V)
    (hu : u ∈ A) (s : ℝ) (hs : 0 < s) : ∀ (N : ℕ) (c : Fin N → ℝ → G) (D : Fin N → V → V),
    (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) →
    (∀ i, ∀ v ∈ A, D i v ∈ A) →
    ∃ (S : List V) (C : ℝ), (∀ v ∈ S, v ∈ A) ∧ 0 ≤ C ∧ ∀ Fr : V → G → ℂ, (∀ v ∈ A, Continuous (Fr v)) →
      (∀ v ∈ A, ∀ i x, HasDerivAt (fun t => Fr v (x * c i t)) (Fr (D i v) x) 0) →
      ‖Fr u 1‖ ^ 2 ≤ C * (S.map fun v => ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖Fr v (List.ofFn fun i => c i (t i)).prod‖ ^ 2).sum := by
  intro N
  induction N with
  | zero =>
    intro c D _ _
    refine ⟨[u], 1, by simpa using hu, zero_le_one, fun Fr _ _ => ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Measure.real]
  | succ N ih =>
    intro c D hc hD
    obtain ⟨S, C, hS, hC, h⟩ := ih (fun i => c i.castSucc) (fun i => D i.castSucc) (fun i => hc _)
      (fun i => hD _)
    refine ⟨S ++ S.map (D (Fin.last N)), C * (2 / s + 2 * s), ?_, by positivity, fun Fr h1 h2 => ?_⟩
    · intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hS v hv
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
        exact hD _ w (hS w hw)
    refine (h Fr h1 fun v hv i => h2 v hv _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [List.map_append, List.sum_append, List.map_map, ← List.sum_map_add, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun v hv => ?_
    refine (cube_step N c s hs hc (Fr v) (Fr (D (Fin.last N) v)) (h1 v (hS v hv))
      (h1 _ (hD _ v (hS v hv))) (h2 v (hS v hv) _)).trans ?_
    simp only [Function.comp_apply]
    have p : ∀ w, 0 ≤ ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖Fr w (List.ofFn fun i => c i (t i)).prod‖ ^ 2 := fun w => integral_nonneg fun t => by positivity
    have a1 := mul_nonneg (show 0 ≤ 2 * s by positivity) (p v)
    have a2 := mul_nonneg (show 0 ≤ 2 / s by positivity) (p (D (Fin.last N) v))
    nlinarith

theorem exists_small (n : ℕ) : ∃ s : ℝ, 0 < s ∧ n * (Real.exp (3 * n ^ 2 * s) - 1) ≤ 1 / 2 := by
  have h : ContinuousAt (fun s : ℝ => n * (Real.exp (3 * n ^ 2 * s) - 1)) 0 := by fun_prop
  have h2 : ∀ᶠ s : ℝ in 𝓝 0, n * (Real.exp (3 * n ^ 2 * s) - 1) < 1 / 2 :=
    h.eventually_lt continuousAt_const (by simp)
  obtain ⟨s, h3, h4⟩ := ((h2.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and self_mem_nhdsWithin).exists
  exact ⟨s, h4, h3.le⟩

theorem sobolev_at_one : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ F : List (Mx n) → Mx n → ℂ, (∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)) → IsDerFam ε F → (∀ l ∈ S, Integrable (fun g : UJ ε => ‖F l (umat g)‖ ^ 2) (muG ε)) → ‖F [] 1‖ ^ 2 ≤ C * (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum := by
  intro n ε
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  obtain ⟨κ, hκ, hg, -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge n ε
  obtain ⟨s, hs, hsn⟩ := exists_small n
  let c : Fin (n ^ 2) → ℝ → UJ ε := fun i t =>
    GlobalTheory.GaugeConst.expJ ε (t • (⟨E i, (hE1 i).1⟩ : GlobalTheory.GaugeConst.lieJ ε))
  have hc : ∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b := fun i =>
    ⟨(GlobalTheory.GaugeConst.continuous_expJ ε).comp (continuous_id.smul continuous_const),
      GlobalTheory.GaugeConst.uMat_injective ε (by
        change NormedSpace.exp ((0 : ℝ) • E i) = 1
        simp),
      fun a b => GlobalTheory.GaugeConst.uMat_injective ε (exp_add_smul (E i) a b)⟩
  obtain ⟨S, C, hS, hC, h⟩ := cube_sum {l : List (Mx n) | ∀ Y ∈ l, Y ∈ lieSet ε} [] (by simp) s hs (n ^ 2) c
    (fun i l => E i :: l) hc (fun i l hl Y hY => by
      rcases List.mem_cons.1 hY with rfl | hY
      exacts [(hE1 i).1, hl Y hY])
  set K := Real.exp (2 * n ^ 3 * (Real.exp (2 * n ^ 2 * s) - 1)) * κ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨S, C * K, hS, by positivity, fun F hF hD hI => ?_⟩
  have hcont : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → Continuous fun g : UJ ε => F l (umat g) :=
    fun l hl => (hF l hl).comp_continuous (GlobalTheory.GaugeConst.continuous_uMat ε) fun g => g.2
  refine (h (fun l g => F l (umat g)) hcont fun l hl i x => hD l hl (E i) (hE1 i).1 _ x.2).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun l hl => ?_
  have hl' := hcont l (hS l hl)
  have hΘ := continuous_prod_ofFn_curves (n ^ 2) c (fun i => (hc i).1)
  have hch := GlobalTheory.ProductChart.lintegral_chart_le n ε κ s E (fun t => (List.ofFn fun i => c i (t i)).prod) hg
    (fun i => (hE1 i).1) hE2 hs hsn (fun t => by
      have := map_list_prod ((Units.coeHom (Mx n)).comp (UJ ε).subtype) (List.ofFn fun i => c i (t i))
      refine this.trans ?_
      rw [List.map_ofFn]
      simp only [Complex.coe_smul]
      rfl)
    (fun g => ENNReal.ofReal (‖F l (umat g)‖ ^ 2)) (hl'.norm.pow 2).measurable.ennreal_ofReal
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t : Fin (n ^ 2) → ℝ => ‖F l (umat (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
    (Filter.Eventually.of_forall fun t => by positivity)
    ((hl'.comp hΘ).norm.pow 2).aestronglyMeasurable]
  have hp : 0 ≤ ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε) := integral_nonneg fun g => by positivity
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0 hp) (hch.trans ?_)
  rw [ENNReal.ofReal_mul hK0, ofReal_integral_eq_lintegral_ofReal (hI l hl)
    (Filter.Eventually.of_forall fun g => by positivity)]
  exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end GlobalTheory.SobolevHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEqBasis
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingSpan

section Gen

variable {K C H Y : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ}

theorem span_range_eq_basis {n : ℕ} (b : Module.Basis (Fin n) K C) (j : C →ₛₗ[σ] H) :
    Submodule.span ℂ (Set.range j) = Submodule.span ℂ (Set.range fun k => j (b k)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨f, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

theorem span_eq_top_of_ev (j : C → H) (ev : H →ₗ[ℂ] (Y → ℂ)) (hinj : Function.Injective ev)
    (h : ∀ x, ev x ∈ Submodule.span ℂ (Set.range fun f => ev (j f))) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have e : (Set.range fun f => ev (j f)) = ev '' Set.range j := Set.range_comp ev j
  have h1 := h x
  rw [e, Submodule.span_image] at h1
  obtain ⟨y, hy, hxy⟩ := h1
  exact hinj hxy ▸ hy

theorem indep_conj {m : ℕ} {φ : Fin m → Y → ℂ} (h : LinearIndependent ℂ φ) :
    LinearIndependent ℂ fun k g => starRingEnd ℂ (φ k g) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc k
  have h2 : ∑ i, star (c i) • φ i = 0 := by
    funext g
    have := congrArg (starRingEnd ℂ) (congrFun hc g)
    simpa [Finset.sum_apply] using this
  simpa using h _ h2 k

end Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def evL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' a b := by simp [evAt]
  map_smul' c a := by simp [evAt]


set_option maxHeartbeats 1000000 in
theorem jUnif_of (hl : LawsJ T) (hJ : JEvExists T R κ v₀) (hB : JEvBar T R κ) (hI : EvInj T R v₀)
    (h1 : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i),
      LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)))
    (h2 : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) → ∀ (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (x : (R.HW i σ).H),
      evAt R i σ (v₀ i σ) x ∈
        Submodule.span ℂ (Set.range fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))))
    (h3 : ∀ (i : Fin D.R.m) σ, ¬ GoodEmb T.Q.c (res T σ) →
      Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank ℂ (R.HW i ((starRingEnd ℂ).comp σ)).H) :
    JUnif T R κ v₀ := by
  have good : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) →
      (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
        LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧
      Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
    intro i σ hσ
    have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hl.spaceW _ (inR i) _ hσ
    have he : ∀ f, evL T R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) :=
      jTop_good T R κ v₀ hσ hV (hJ i σ hσ hV)
    refine ⟨fun m b hb => LinearIndependent.of_comp (evL T R i σ (v₀ i σ)) ?_,
      span_eq_top_of_ev _ (evL T R i σ (v₀ i σ)) (hI i σ hσ) fun x => ?_⟩
    · have e : (evL T R i σ (v₀ i σ)) ∘ (fun k => jTop T R κ v₀ i σ (b k)) =
          fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := funext fun k => he (b k)
      rw [e]
      exact h1 i _ hσ hV m b hb
    · rw [funext he]
      exact h2 i σ hσ hV x
  intro i σ
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · exact good i σ hσ
  have hσ' : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := hl.spaceW _ (inR i) _ hσ'
  obtain ⟨v, -, he⟩ := jTop_bar T R κ v₀ hσ hV (hB i σ hσ hV)
  have hind : ∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k) := fun m b hb => by
    refine LinearIndependent.of_comp (evL T R i σ v) ?_
    have e : (evL T R i σ v) ∘ (fun k => jTop T R κ v₀ i σ (b k)) =
        fun k g => starRingEnd ℂ (phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) g) := funext fun k => he (b k)
    rw [e]
    exact indep_conj (h1 i _ hσ' hV m b hb)
  refine ⟨hind, ?_⟩
  obtain ⟨b⟩ := hasB_nTop T hl κ i
  have hs := (good i ((starRingEnd ℂ).comp σ) hσ').2
  rw [span_range_eq_basis b] at hs ⊢
  have d1 : Module.finrank ℂ (R.HW i ((starRingEnd ℂ).comp σ)).H ≤ nTop T κ i := by
    rw [← finrank_top, ← hs]
    exact (finrank_range_le_card _).trans (Fintype.card_fin _).le
  have hi := hind _ b b.linearIndependent
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
  rw [finrank_span_eq_card hi, Fintype.card_fin]
  exact (h3 i σ hσ).trans d1

end GlobalTheory.ReadingSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymplecticBasesMatched
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g g' : ℕ} {X' X : Data E r}

theorem perFr_castFr (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (castFr h.psi x) v τ i = perFr X' x v τ i := by
  cases X; cases X'
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3
  rfl

noncomputable def renum (q : Fin g' ≃ Fin g) : (Fin g → ℂ) ≃L[ℂ] (Fin g' → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ q).toContinuousLinearEquiv

theorem renum_apply (q : Fin g' ≃ Fin g) (z : Fin g → ℂ) (j : Fin g') : renum q z j = z (q j) := rfl

theorem hx_renum (h : SameSp X' X) {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} (hs' : IsSympl X' bas') (hs : IsSympl X bas)
    {x : Frame X'.Ψ r} (hxd : x ∈ X'.dom) (q : Fin g' ≃ Fin g)
    (hpv : ∀ v, renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v) (z w : Fin g → ℂ) :
    hx X bas idx (castFr h.psi x) z w = hx X' bas' idx' x (renum q z) (renum q w) := by
  have hx1 := h.castFr_mem_dom hxd
  have him' := (hx_laws E r X' g' bas' idx' 0 hs' Even.zero x hxd).2.2.1
  have him := (hx_laws E r X g bas idx 0 hs Even.zero _ hx1).2.2.1
  refine sub_eq_zero.1 (form_eq_zero_of_im
    (fun z w => hx X bas idx (castFr h.psi x) z w - hx X' bas' idx' x (renum q z) (renum q w))
    (fun w => ⟨fun u v => ?_, fun c u => ?_⟩) (fun z => ⟨fun u v => ?_, fun c u => ?_⟩) _
    (span_range_pv idx hs hx1) ?_ z w)
  · simp only [hx, map_add (f := _), mulVec_add, add_dotProduct]; ring
  · simp only [hx, map_smul, mulVec_smul, smul_dotProduct, smul_eq_mul]; ring
  · simp only [hx, map_add (f := _), star_add, mulVec_add, dotProduct_add]; ring
  · have : renum q (c • u) = c • renum q u := rfl
    simp only [hx, this, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_sub]
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [Complex.sub_im, hpv, hpv, him, him', h.EF_eq, sub_self]

theorem denseRange_embR {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (n : ℕ) : DenseRange (Ker.embR X (n := n)) := by
  obtain ⟨L, hL⟩ := Ker.exists_equiv_zR X idx (n := n) hs hx
  have h := L.symm.surjective.denseRange.comp (Ker.denseRange_zR_embR X idx hs hx) L.symm.continuous
  convert h using 1
  funext y
  simp [← hL]

theorem zR_lact (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) {n : ℕ} (γ : GL (Fin r) E) (hγ : IsUn X γ)
    (v : Ker.WR X n) :
    Ker.zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = Ker.zR X idx x v := by
  funext k i
  have hm : mat (lact γ x) (idx i).1 =
      (γ : Matrix (Fin r) (Fin r) E).map (idx i).1.1 * mat x (idx i).1 := rfl
  rw [Ker.zR, Ker.zR, hm]
  split_ifs
  · rw [PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map (idx i).1.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map (idx i).1.1.mapMatrix)
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

theorem zR_renum (h : SameSp X' X) {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {idx : Fin g ≃ X.Ψ × Fin r} (hs' : IsSympl X' bas')
    {x : Frame X'.Ψ r} (hxd : x ∈ X'.dom) (q : Fin g' ≃ Fin g)
    (hpv : ∀ v, renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v) {n : ℕ} (v : Ker.WR X' n) (k : Fin n) :
    renum q (Ker.zR X idx (castFr h.psi x) (fun τ => v ⟨τ.1, h.psi.ge τ.2⟩) k) = Ker.zR X' idx' x v k := by
  refine (denseRange_embR idx' hs' hxd n).induction_on (p := fun v : Ker.WR X' n =>
    renum q (Ker.zR X idx (castFr h.psi x) (fun τ => v ⟨τ.1, h.psi.ge τ.2⟩) k) = Ker.zR X' idx' x v k) v
    (isClosed_eq ?_ ?_) (fun y => hpv (y k))
  · have := (Ker.zRLin X idx (castFr h.psi x) (n := n)).continuous_of_finiteDimensional
    have h2 : Continuous fun (v : Ker.WR X' n) (τ : X.Ψ) => v ⟨τ.1, h.psi.ge τ.2⟩ :=
      continuous_pi fun τ => continuous_apply _
    have h3 := (continuous_apply k).comp (this.comp h2)
    exact (renum q).continuous.comp h3
  · exact (continuous_apply k).comp (Ker.zRLin X' idx' x (n := n)).continuous_of_finiteDimensional

end SlopeTestRemainingChoices

theorem anFib_move_renum : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r g g' : ℕ) (X' X : Data D.host.E r) (hX : SameSp X' X) (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g' ≃ X'.Ψ × Fin r) (e' : Fin g' ≃ Lt1 Dw) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl X' bas' → IsSympl X bas → Matched c σ X' idx' e' → Matched c σ X idx e → ∀ x ∈ X'.dom, ∀ L : Lt D.host.E r, SelfD X' L → ∀ ga : GL (Fin r) D.host.E, IsUn X ga → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (y : FrPt Xo c ℂ) (A' : AnFib X' bas' idx' e' x L y) (th' : (Fin g' → ℂ) → ℂ), A'.Reads 1 y.s th' → ∃ (A : AnFib X bas idx e (lact ga (castFr hX.psi x)) (mapL ga L) y) (th : (Fin g → ℂ) → ℂ), A.Reads 1 y.s th ∧ (∀ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), A'.Marked mk → A.Marked (mvMap ga mk)) ∧ ∀ (n : ℕ) (v' : GlobalTheory.Ker.WR X' n) (v : GlobalTheory.Ker.WR X n), (∀ (τ : X'.Ψ) (k : Fin n), v ⟨τ.1, hX.psi ▸ τ.2⟩ k = ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ v' τ k) → GlobalTheory.Ker.gaussR X bas idx (lact ga (castFr hX.psi x)) (GlobalTheory.Ker.zR X idx (lact ga (castFr hX.psi x)) v) * ∏ b, th (GlobalTheory.Ker.zR X idx (lact ga (castFr hX.psi x)) v b) = GlobalTheory.Ker.gaussR X' bas' idx' x (GlobalTheory.Ker.zR X' idx' x v') * ∏ b, th' (GlobalTheory.Ker.zR X' idx' x v' b) := by
  intro D H Dw l Xo c σ r g g' X' X h bas' idx' e' bas idx e hs' hs hm' hm x hxd L hL ga hga
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y A th' hth
  let q : Fin g' ≃ Fin g := e'.trans e.symm
  have hq (j) : e (q j) = e' j := e.apply_symm_apply _
  have hpv (v) : renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v := by
    funext j
    rw [renum_apply, hm.1, hm'.1, hq, perFr_castFr h]
  have hty (j) : rowType X (idx (q j)) = rowType X' (idx' j) := by rw [hm.2, hm'.2, hq]
  have hx1 := h.castFr_mem_dom hxd
  obtain ⟨-, -, -, -, -, -, -, hinv⟩ := hx_laws _ r X g bas idx 0 hs Even.zero _ hx1
  obtain ⟨hdom, hpv2, -, hhx2⟩ := hinv ga hga
  have hhx (z w) : hx X bas idx (lact ga (castFr h.psi x)) z w = hx X' bas' idx' x (renum q z) (renum q w) := by
    rw [hhx2, hx_renum h hs' hs hxd q hpv]
  have hp (v) : renum q (pv X idx (lact ga (castFr h.psi x)) (Lev.lin ga v)) = pv X' idx' x v :=
    (congrArg (renum q) (hpv2 v)).trans (hpv v)
  have hp' (v) : renum q (pv X idx (lact ga (castFr h.psi x)) v) = pv X' idx' x (Lev.lin ga⁻¹ v) := by
    rw [← hp, Lev.lin_inv']
  have hlat (z) : (∃ v ∈ L, renum q z = pv X' idx' x v) ↔
      ∃ v ∈ mapL ga L, z = pv X idx (lact ga (castFr h.psi x)) v :=
    ⟨fun ⟨v, hv, hz⟩ => ⟨Lev.lin ga v, ⟨v, hv, rfl⟩, (renum q).injective (hz.trans (hp v).symm)⟩,
      fun ⟨v, hv, hz⟩ => ⟨_, Lev.mem_mapL.1 hv, (congrArg (renum q) hz).trans (hp' v)⟩⟩
  refine ⟨
    { ex := fun z => A.ex (renum q z)
      ex_add := fun z w => by rw [map_add (f := _), A.ex_add]
      ex_onto := A.ex_onto.comp (renum q).surjective
      ex_ker := fun z => (A.ex_ker _).trans (hlat z)
      ex_lin := fun a z => by
        rw [← A.ex_lin]
        congr 1
        funext j
        simp only [renum_apply, hty]
      hol := fun U f => ?_
      der := fun ℓ => ⟨?_, fun U hU f => ?_⟩
      fr := fun j z => A.fr j (renum q z)
      fr_hol := fun j => (A.fr_hol j).comp (renum q).differentiableOn fun z hz => hz
      fr_ne := fun j z => A.fr_ne j _
      fr_g := fun j j' z => A.fr_g j j' _
      fr_0 := fun j => by rw [map_zero]; exact A.fr_0 j
      χ := fun v => A.χ (Lev.lin ga⁻¹ v)
      χ_norm := fun v hv => A.χ_norm _ (Lev.mem_mapL.1 hv)
      fr_per := fun v hv j z hz => by
        rw [hhx, hhx, map_add (f := _), hp']; exact A.fr_per _ (Lev.mem_mapL.1 hv) j _ hz },
    fun z => th' (renum q z), fun j z => hth j (renum q z), fun mk hk a ha => ?_, fun n v' v hv => ?_⟩
  · exact ⟨(A.hol U f).1.preimage (renum q).continuous,
      (A.hol U f).2.comp (renum q).differentiableOn fun z hz => hz⟩
  · simpa only [map_zero] using (A.der ℓ).1
  · rw [(A.der ℓ).2 U hU f]
    have h1 := (renum q).comp_right_fderiv (f := fun z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (A.ex z).left U f) (x := 0)
    have h2 : renum q (Pi.single (e.symm ℓ) 1) = Pi.single (e'.symm ℓ) 1 := by
      funext j
      rw [renum_apply]
      have h3 : q j = e.symm ℓ ↔ j = e'.symm ℓ := by
        rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply, hq]
      simp only [Pi.single_apply, h3]
    rw [← h2]
    rw [map_zero] at h1
    exact (congrArg (fun F => F (Pi.single (e.symm ℓ) 1)) h1).symm
  · rw [hk a ha, ← hp]
    change A.ex _ = A.ex _
    congr 3
    rw [Lev.lin_apply, mulVec_smul]
    rfl
  · have hv2 : v = fun τ k => ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ v' ⟨τ.1, h.psi.ge τ.2⟩ k := by
      funext τ k
      exact hv ⟨τ.1, h.psi.ge τ.2⟩ k
    have hz (k) : renum q (Ker.zR X idx (lact ga (castFr h.psi x)) v k) = Ker.zR X' idx' x v' k := by
      rw [hv2, zR_lact idx _ ga hga (fun τ => v' ⟨τ.1, h.psi.ge τ.2⟩), zR_renum h hs' hxd q hpv]
    simp only [Ker.gaussR, hhx, hz]

end GlobalTheory.OneMapRef
end

