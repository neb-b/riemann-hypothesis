module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivatives
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AvgFam

section Compact

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsFiniteMeasure μ]

theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

def intCLM : C(K, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ k, f k ∂μ
      map_add' := fun f g => integral_add (integrable_of_continuous μ f.continuous)
        (integrable_of_continuous μ g.continuous)
      map_smul' := fun c f => integral_smul c _ }
    (μ.real Set.univ) fun f => by
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => f.norm_coe_le_norm k)

theorem continuous_avg {Y : Type} [TopologicalSpace Y] {F : K → Y → ℂ}
    (hF : Continuous fun p : K × Y => F p.1 p.2) : Continuous fun x => ∫ k, F k x ∂μ := by
  let Φ : C(Y × K, ℂ) := ⟨fun p => F p.2 p.1, hF.comp continuous_swap⟩
  exact (intCLM μ).continuous.comp Φ.curry.continuous

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem hasDerivAt_avg (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {F : K → GA D V → ℂ} (hF : ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (hFc : ∀ x, Continuous fun k => F k x)
    (hGc : Continuous fun p : K × GA D V => Rder θ V τ X (F p.1) p.2) (g : GA D V) :
    HasDerivAt (fun t : ℝ => ∫ k, F k (g * oneP θ V τ X t) ∂μ) (∫ k, Rder θ V τ X (F k) g ∂μ) 0 := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hc1 : Continuous fun p : K × ℝ => Rder θ V τ X (F p.1) (g * oneP θ V τ X p.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_const.mul ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).comp continuous_snd)))
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc1.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t k => F k (g * oneP θ V τ X t))
    (F' := fun t k => Rder θ V τ X (F k) (g * oneP θ V τ X t)) (x₀ := 0) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one)
    (Filter.Eventually.of_forall fun t => (hFc _).aestronglyMeasurable)
    (integrable_of_continuous μ (hFc _))
    ((hc1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun k t ht => hC (k, t) ⟨Set.mem_univ _, ht⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ =>
      GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder (hF k) hX) g t)
  have e := key.2
  simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at e
  exact e

end Compact

theorem avg_closed : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  intro D θ hθ V K _ _ _ _ μ _ 𝒢 hc hsm hder
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : ∀ F ∈ 𝒢, ∀ x, Continuous fun k => F k x := fun F hF x =>
    (hc F hF).comp (continuous_id.prodMk continuous_const)
  have hint : ∀ F ∈ 𝒢, ∀ x, Integrable (fun k => F k x) μ := fun F hF x =>
    integrable_of_continuous μ (hk F hF x)
  have hd : ∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, ∀ g, HasDerivAt (fun t : ℝ => ∫ k, F k (g * oneP θ V τ X t) ∂μ)
      (∫ k, Rder θ V τ X (F k) g ∂μ) 0 := fun F hF τ X hX g =>
    hasDerivAt_avg μ hθ hX (hsm F hF) (hk F hF) (hc _ (hder F hF τ X hX)) g
  have hR : ∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ,
      Rder θ V τ X (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, Rder θ V τ X (F k) x ∂μ :=
    fun F hF τ X hX => funext fun g => (hd F hF τ X hX g).deriv
  have hSm : ∀ F ∈ 𝒢, (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := by
    intro F hF
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V {φ | ∃ F ∈ 𝒢, φ = fun x => ∫ k, F k x ∂μ} ?_ ?_ _
      ⟨F, hF, rfl⟩
    · rintro _ ⟨F, hF, rfl⟩
      exact continuous_avg μ (hc F hF)
    · rintro _ ⟨F, hF, rfl⟩ τ X hX
      exact ⟨_, ⟨_, hder F hF τ X hX, rfl⟩, hd F hF τ X hX⟩
  have hW : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ F ∈ 𝒢, (fun k => l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) ∈ 𝒢 ∧
        l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) =
          fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ := by
    intro l hl F hF
    induction l with
    | nil => exact ⟨hF, rfl⟩
    | cons p l ih =>
      obtain ⟨h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      have hp := hl p List.mem_cons_self
      refine ⟨hder _ h1 p.1 p.2 hp, ?_⟩
      simp only [List.foldr_cons]
      rw [h2]
      exact hR _ h1 p.1 p.2 hp
  have hC : ∀ F ∈ 𝒢, ∀ τ Z, (fun k => RderC θ V τ Z (F k)) ∈ 𝒢 ∧
      RderC θ V τ Z (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, RderC θ V τ Z (F k) x ∂μ := by
    intro F hF τ Z
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have m1 := hder F hF τ _ h1
    have m2 := hder F hF τ _ h2
    have e : (fun k => RderC θ V τ Z (F k)) = (fun k => Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) (F k)) +
        Complex.I • (fun k => Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) (F k)) := rfl
    refine ⟨e ▸ add_mem m1 (Submodule.smul_mem _ _ m2), ?_⟩
    have i1 := hint _ m1
    have i2 := hint _ m2
    simp only [RderC]
    rw [hR F hF τ _ h1, hR F hF τ _ h2]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i1 x) ((i2 x).const_mul _), integral_const_mul]
  have hL : ∀ τ (L : List ((GA D V → ℂ) → GA D V → ℂ)), (∀ f ∈ L, ∃ Z, f = RderC θ V τ Z) → ∀ F ∈ 𝒢,
      (fun k => L.foldr (fun f acc => f acc) (F k)) ∈ 𝒢 ∧
        L.foldr (fun f acc => f acc) (fun x => ∫ k, F k x ∂μ) =
          fun x => ∫ k, (L.foldr (fun f acc => f acc) (F k)) x ∂μ := by
    intro τ L hLZ F hF
    induction L with
    | nil => exact ⟨hF, rfl⟩
    | cons f L ih =>
      obtain ⟨h1, h2⟩ := ih fun q hq => hLZ q (List.mem_cons_of_mem _ hq)
      obtain ⟨Z, rfl⟩ := hLZ f List.mem_cons_self
      refine ⟨(hC _ h1 τ Z).1, ?_⟩
      simp only [List.foldr_cons]
      rw [h2]
      exact (hC _ h1 τ Z).2
  intro F hF
  refine ⟨continuous_avg μ (hc F hF), hSm F hF, fun l hl => (hW l hl F hF).2, fun τ j => ?_⟩
  have hmem : ∀ idx : Fin (j + 1) → Fin V.rank, ∀ f ∈ List.ofFn (fun a : Fin (j + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), ∃ Z, f = RderC θ V τ Z := by
    intro idx f hf
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
    exact ⟨_, rfl⟩
  simp only [gelf]
  rw [Finset.sum_congr rfl fun idx _ => (hL τ _ (hmem idx) F hF).2]
  funext x
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ fun idx _ => hint _ (hL τ _ (hmem idx) F hF).1 x]

end GlobalTheory.AvgFam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSmoothEigenvectorCasimirDifferenceOperator
section
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis
  GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

theorem exists_eigen_casOp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)) (d e : ℕ) (X : Fin d → Mx n) (Y : Fin e → Mx n), Std ε σ →
    (∀ i, X i ∈ lieSet ε) → (∀ b, Y b ∈ lieSet ε) →
    (∀ k ∈ Kset ε, ∀ v, Sm ε σ v → casOp σ X Y (σ k v) = σ k (casOp σ X Y v)) →
    ∃ (u : H) (χ : ℂ), Sm ε σ u ∧ u ≠ 0 ∧ casOp σ X Y u = χ • u := by
  intro n ε H _ _ _ σ d e X Y h hX hY hK
  have hσ := h.1
  obtain ⟨v₀, hv₀K, hv₀⟩ := h.2.2.2.2
  let f : KG ε → ℂ := fun k => star ⟪v₀, σ (toMK k) v₀⟫_ℂ
  have hfc : Continuous f := (continuous_const.inner (KCoef.continuous_orbit hσ v₀)).star
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ hfc
  obtain ⟨m, a, c, -, haK, -, hsum⟩ := kAvg_finite_rank n ε H σ h f (KCoef.kFinFun_coef hσ hv₀K)
  let Ss : Submodule ℂ H := smooth (Jm ε) σ
  let V : Submodule ℂ H := Ss.map (Q : H →ₗ[ℂ] H)
  have hVspan : V ≤ Submodule.span ℂ (Set.range a) := by
    rintro _ ⟨w, -, rfl⟩
    change Q w ∈ _
    rw [hQ, hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hVsm : ∀ u ∈ V, Sm ε σ u := by
    intro u hu
    have hspan : Submodule.span ℂ (Set.range a) ≤ Ss :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h.2.2.1 _ (haK j))
    exact hspan (hVspan hu)
  haveI : FiniteDimensional ℂ V :=
    by
      haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range a)
      exact Submodule.finiteDimensional_of_le hVspan

  have hcomm : ∀ v, Sm ε σ v → casOp σ X Y (Q v) = Q (casOp σ X Y v) := by
    intro v hv
    have hQv : Sm ε σ (Q v) := hVsm _ ⟨v, hv, rfl⟩
    refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
    have hy' : Sm ε σ y := hy
    rw [inner_casOp hσ hX hY hy' hQv, hQ, hQ, KCoef.inner_kAvg hσ hfc, KCoef.inner_kAvg hσ hfc]
    congr 1
    funext k
    congr 1
    rw [← inner_casOp hσ hX hY hy' (Sm.translate hσ hv (KCoef.toMK_mem_UJ k)), hK _ (toMK_mem_K k) v hv]
  have hVmap : ∀ u ∈ V, casOp σ X Y u ∈ V := by
    rintro _ ⟨v, hv, rfl⟩
    change casOp σ X Y (Q v) ∈ V
    rw [hcomm v hv]
    exact ⟨_, sm_casOp hσ hX hY hv, rfl⟩
  let F : Module.End ℂ V :=
    { toFun := fun u => ⟨casOp σ X Y u, hVmap u u.2⟩
      map_add' := fun x y => Subtype.ext (casOp_add hσ hX hY (hVsm _ x.2) (hVsm _ y.2))
      map_smul' := fun r x => Subtype.ext (casOp_smul hσ hX hY r (hVsm _ x.2)) }
  have hQv₀ : Q v₀ ≠ 0 := by
    intro h0
    apply KCoef.inner_kAvg_ne_zero hσ hv₀
    rw [← hQ, h0, inner_zero_right]
  haveI : Nontrivial V := ⟨⟨⟨Q v₀, v₀, h.2.2.1 _ hv₀K, rfl⟩, 0, fun h0 => hQv₀ (congrArg Subtype.val h0)⟩⟩
  obtain ⟨χ, hχ⟩ := Module.End.exists_eigenvalue F
  obtain ⟨u, hu⟩ := hχ.exists_hasEigenvector
  refine ⟨u, χ, hVsm _ u.2, fun h0 => hu.2 (Subtype.ext h0), ?_⟩
  exact congrArg Subtype.val (hu.apply_eq_smul)

end GlobalTheory.TypeSum.CasBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SignatureLieSetExpandOrthonormalBases
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section
namespace GlobalTheory.TypeSum.CasBasis.Expand
variable {n : ℕ}

theorem sum_get {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [Fin.sum_univ_def]
  conv_rhs => rw [← List.map_get_finRange l]
  rw [List.map_map]
  rfl

theorem trace_mul_unitE (U : Mx n) (a b : Fin n) : trace (U * unitE a b) = U b a := by
  simpa [unitE] using (Matrix.trace_mul_single U a b 1)

theorem sum_flatMap {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem filter_split {α M : Type*} [AddCommMonoid M] (l : List α) (c d : α → Bool) (F : α → M) :
    ((l.filter fun p => c p && (d p == true)).map F).sum + ((l.filter fun p => c p && (d p == false)).map F).sum =
      (l.map fun p => if c p then F p else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases hc : c a <;> cases hd : d a <;> simp [← ih] <;> abel

theorem sum_map_neg' {α M : Type*} [AddCommGroup M] (l : List α) (f : α → M) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, neg_add]

theorem sum_product_list {M : Type*} [AddCommMonoid M] (G : Fin n × Fin n → M) :
    ((List.product (List.finRange n) (List.finRange n)).map G).sum = ∑ a, ∑ b, G (a, b) := by
  simp [List.product, List.map_flatMap, sum_flatMap, List.map_map, Fin.sum_univ_def, Function.comp_def]

variable {ε : Fin n → Bool}

theorem diag_re {U : Mx n} (hU : U ∈ lieSet ε) (a : Fin n) : (U a a).re = 0 := by
  have h := (mem_lieSet_iff_entry.mp hU) a a
  rcases ha : ε a <;> simp [ha] at h <;> have h2 := congrArg Complex.re h <;> simp at h2 <;> linarith

theorem entry_same {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a = ε b) : U b a = -star (U a b) := by
  have h1 := (mem_lieSet_iff_entry.mp hU) a b
  rw [h] at h1
  have : (starRingEnd ℂ) (U b a) = -U a b := by
    rcases hb : ε b <;> simp [hb] at h1 <;> first | linear_combination h1 | linear_combination -h1
  have h3 := congrArg (starRingEnd ℂ) this
  simp at h3
  simpa [Complex.star_def] using h3

theorem entry_opp {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a ≠ ε b) : U b a = star (U a b) := by
  have h1 := (mem_lieSet_iff_entry.mp hU) a b
  have : star (U b a) = U a b := by
    rcases ha : ε a <;> rcases hb : ε b <;> simp_all <;> first | linear_combination h1 | linear_combination -h1
  have h3 := congrArg star this
  simpa using h3

abbrev tm (U X : Mx n) : Mx n := (trace (U * X)).re • X

theorem tm_diag {U : Mx n} (hU : U ∈ lieSet ε) (a : Fin n) :
    tm U (Complex.I • unitE a a) = -(U a a • unitE a a) := by
  have h := diag_re hU a
  simp only [tm, Matrix.mul_smul, trace_smul, trace_mul_unitE, ← Complex.coe_smul, smul_smul, ← neg_smul]
  congr 1
  apply Complex.ext <;> simp [h]

theorem tm_same {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a = ε b) :
    tm U (invSqrtTwo • (unitE a b - unitE b a)) + tm U ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) =
      -(U a b • unitE a b + U b a • unitE b a) := by
  have hba := entry_same hU h
  simp only [tm, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, trace_smul, trace_sub, trace_add, trace_mul_unitE,
    ← Complex.coe_smul, hba]
  match_scalars <;> simp only [smul_eq_mul] <;> apply Complex.ext <;>
    simp [invSqrtTwo, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im] <;> field_simp
  all_goals (try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]) <;> ring

theorem tm_opp {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a ≠ ε b) :
    tm U (invSqrtTwo • (unitE a b + unitE b a)) + tm U ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a)) =
      U a b • unitE a b + U b a • unitE b a := by
  have hba := entry_opp hU h
  simp only [tm, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, trace_smul, trace_sub, trace_add, trace_mul_unitE,
    ← Complex.coe_smul, hba]
  match_scalars <;> simp only [smul_eq_mul] <;> apply Complex.ext <;>
    simp [invSqrtTwo, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im] <;> field_simp
  all_goals (try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]) <;> ring

abbrev pairTerm (U : Mx n) (p : Fin n × Fin n) : Mx n := U p.1 p.2 • unitE p.1 p.2 + U p.2 p.1 • unitE p.2 p.1

theorem decomp (U : Mx n) :
    U = ∑ a, U a a • unitE a a + ∑ a, ∑ b, if a < b then pairTerm U (a, b) else 0 := by
  ext r t
  simp only [Matrix.add_apply, Matrix.sum_apply, apply_ite (fun M : Mx n => M r t), pairTerm, Matrix.smul_apply,
    single_apply, smul_eq_mul, Matrix.zero_apply]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rcases lt_trichotomy r t with h | rfl | h
  · rw [Finset.sum_eq_single r (fun x _ hx => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind) (by simp),
      Finset.sum_eq_single t (fun y _ hy => by split_ifs <;> grind) (by simp)]
    simp [h, h.ne, not_lt.mpr h.le]
  · simp only [lt_self_iff_false, if_true]
    rw [Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind]
    simp
  · rw [Finset.sum_eq_single t (fun x _ hx => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind) (by simp),
      Finset.sum_eq_single r (fun y _ hy => by split_ifs <;> grind) (by simp)]
    simp [h, h.ne, h.ne', not_lt.mpr h.le]

theorem pairs_split (U : Mx n) :
    ((pairs ε true).map (pairTerm U)).sum + ((pairs ε false).map (pairTerm U)).sum =
      ∑ a, ∑ b, if a < b then pairTerm U (a, b) else 0 :=
  (filter_split _ (fun p : Fin n × Fin n => decide (p.1 < p.2)) (fun p : Fin n × Fin n => ε p.1 == ε p.2)
    (pairTerm U)).trans (by rw [sum_product_list]; simp)

theorem sum_k {U : Mx n} (hU : U ∈ lieSet ε) :
    ∑ i, tm U (kB ε i) = -(∑ a, U a a • unitE a a + ((pairs ε true).map (pairTerm U)).sum) := by
  rw [show (∑ i, tm U (kB ε i)) = ((kList ε).map (tm U)).sum from sum_get _ _]
  simp only [kList, List.map_append, List.sum_append, List.map_map, List.map_flatMap, sum_flatMap, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_def, tm_diag hU]
  rw [List.map_congr_left (g := fun p => -pairTerm U p) (fun p hp => by
    have hs : ε p.1 = ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    exact tm_same hU hs), Fin.sum_univ_def, sum_map_neg', sum_map_neg', neg_add]

theorem sum_p {U : Mx n} (hU : U ∈ lieSet ε) :
    ∑ b, tm U (pB ε b) = ((pairs ε false).map (pairTerm U)).sum := by
  rw [show (∑ b, tm U (pB ε b)) = ((pList ε).map (tm U)).sum from sum_get _ _]
  simp only [pList, List.map_flatMap, sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [List.map_congr_left (g := pairTerm U) (fun p hp => by
    have hs : ε p.1 ≠ ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    exact tm_opp hU hs)]

end GlobalTheory.TypeSum.CasBasis.Expand

namespace GlobalTheory.TypeSum.CasBasis


open Expand in
theorem lieSet_expand_bases : ∀ (n : ℕ) (ε : Fin n → Bool), ∀ U ∈ lieSet ε,
    U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := by
  intro n ε U hU
  have h1 := sum_p hU
  have h2 := sum_k hU
  simp only [tm] at h1 h2
  rw [h1, h2, sub_neg_eq_add]
  conv_lhs => rw [decomp U]
  rw [← pairs_split (ε := ε)]
  abel

end GlobalTheory.TypeSum.CasBasis
end
end

