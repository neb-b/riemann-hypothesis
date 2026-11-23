module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivatives
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparatelyFiniteDimFunctionsFinite
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.ProdTrick

theorem exists_finset_separating {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    ∃ T : Finset X, ∀ v ∈ V, (∀ x ∈ T, v x = 0) → v = 0 :=
  _root_.UpperTheory.Reformulated.B.Qp2.exists_finset_separating V

theorem exists_finiteDimensional_of_slices :
    ∀ (X Y : Type) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)),
      FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ →
      ∃ 𝓥 : Submodule ℂ (X × Y → ℂ), FiniteDimensional ℂ 𝓥 ∧
        ∀ f : X × Y → ℂ, (∀ y, (fun x => f (x, y)) ∈ V₁) → (∀ x, (fun y => f (x, y)) ∈ V₂) →
          f ∈ 𝓥 := by
  intro X Y V₁ V₂ h₁ h₂
  obtain ⟨T, hT⟩ := exists_finset_separating V₁
  let S : Submodule ℂ (X × Y → ℂ) :=
    { carrier := {f | (∀ y, (fun x => f (x, y)) ∈ V₁) ∧ (∀ x, (fun y => f (x, y)) ∈ V₂)}
      add_mem' := fun {a b} ha hb =>
        ⟨fun y => V₁.add_mem (ha.1 y) (hb.1 y), fun x => V₂.add_mem (ha.2 x) (hb.2 x)⟩
      zero_mem' := ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩
      smul_mem' := fun c a ha =>
        ⟨fun y => V₁.smul_mem c (ha.1 y), fun x => V₂.smul_mem c (ha.2 x)⟩ }
  let L : S →ₗ[ℂ] (T → V₂) :=
    { toFun := fun f t => ⟨fun y => (f : X × Y → ℂ) ((t : X), y), f.2.2 t⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    funext ⟨x, y⟩
    have hy := hT _ (f.2.1 y) (fun t ht => by
      have := congrArg Subtype.val (congrFun hf ⟨t, ht⟩)
      exact congrFun this y)
    exact congrFun hy x
  have : FiniteDimensional ℂ S := FiniteDimensional.of_injective L hL
  exact ⟨S, this, fun f h1 h2 => ⟨h1, h2⟩⟩

end GlobalTheory.CompanionTheory.CTFin.ProdTrick
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntEl

open MeasureTheory

theorem finite_range {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

theorem measure_level_ne_top {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [AddCommGroup W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ : X → W} (hc : HasCompactSupport φ) {v : W}
    (hv : v ≠ 0) : μ (φ ⁻¹' {v}) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (IsCompact.measure_lt_top hc))
  intro x hx
  apply subset_tsupport
  rw [Function.mem_support, show φ x = v from hx]
  exact hv

theorem smInt_comp {X Y W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X)
    (ψ : X → Y) (g : Y → W) (S : Finset Y) (hS : ∀ x, ψ x ∈ S)
    (hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y})) (hf : ∀ y ∈ S, g y ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤) :
    smInt μ (g ∘ ψ) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • g y := by
  classical
  have hsupp : (Function.support fun v : W => (((μ ((g ∘ ψ) ⁻¹' {v})).toReal : ℝ) : ℂ) • v)
      ⊆ ↑(S.image g) := by
    intro v hv
    by_contra hvS
    apply hv
    have : (g ∘ ψ) ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hvS (Finset.mem_coe.2 (Finset.mem_image.2 ⟨ψ x, hS x, hx⟩))
    simp [this]
  unfold smInt
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
      (fun y hy => Finset.mem_image_of_mem g hy)]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv0 : v = 0
  · subst hv0
    rw [smul_zero]
    symm
    exact Finset.sum_eq_zero fun y hy => by rw [(Finset.mem_filter.1 hy).2, smul_zero]
  · have hset : (g ∘ ψ) ⁻¹' {v} = ⋃ y ∈ S.filter (fun y => g y = v), ψ ⁻¹' {y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp, Set.mem_iUnion,
        Finset.mem_filter, exists_prop]
      constructor
      · intro hx
        exact ⟨ψ x, ⟨hS x, hx⟩, rfl⟩
      · rintro ⟨y, ⟨_, hy⟩, rfl⟩
        exact hy
    have hmeas : μ ((g ∘ ψ) ⁻¹' {v}) = ∑ y ∈ S.filter (fun y => g y = v), μ (ψ ⁻¹' {y}) := by
      rw [hset]
      refine measure_biUnion_finset ?_ fun y hy => hm y (Finset.mem_filter.1 hy).1
      intro a _ b _ hab
      exact Disjoint.preimage ψ (Set.disjoint_singleton.2 hab)
    rw [hmeas, ENNReal.toReal_sum (fun y hy => hf y (Finset.mem_filter.1 hy).1
      (by rw [(Finset.mem_filter.1 hy).2]; exact hv0)), Complex.ofReal_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.1 hy).2]

theorem smInt_add {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ₁ φ₂ : X → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂ := by
  classical
  let ψ : X → W × W := fun x => (φ₁ x, φ₂ x)
  let S : Finset (W × W) := (finite_range l₁ c₁).toFinset ×ˢ (finite_range l₂ c₂).toFinset
  have hS : ∀ x, ψ x ∈ S := fun x =>
    Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩,
      (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩⟩
  have hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y}) := fun y _ =>
    ((l₁.prodMk l₂).isOpen_fiber y).measurableSet
  have f₁ : ∀ y : W × W, y.1 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₁ hy) (measure_mono fun x hx => by
      show φ₁ x = y.1
      rw [← show ψ x = y from hx])
  have f₂ : ∀ y : W × W, y.2 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₂ hy) (measure_mono fun x hx => by
      show φ₂ x = y.2
      rw [← show ψ x = y from hx])
  have e₀ : smInt μ (φ₁ + φ₂) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • (y.1 + y.2) :=
    smInt_comp μ ψ (fun y => y.1 + y.2) S hS hm fun y _ hy => by
      by_cases h : y.1 = 0
      · refine f₂ y fun h' => hy ?_
        show y.1 + y.2 = 0
        rw [h, h', add_zero]
      · exact f₁ y h
  have e₁ : smInt μ φ₁ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.1 :=
    smInt_comp μ ψ (fun y => y.1) S hS hm fun y _ hy => f₁ y hy
  have e₂ : smInt μ φ₂ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.2 :=
    smInt_comp μ ψ (fun y => y.2) S hS hm fun y _ hy => f₂ y hy
  rw [e₀, e₁, e₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => smul_add _ _ _

theorem smInt_linear {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (T : W →ₗ[ℂ] W') {φ : X → W}
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    smInt μ (T ∘ φ) = T (smInt μ φ) := by
  classical
  let S : Finset W := (finite_range l c).toFinset
  have hS : ∀ x, φ x ∈ S := fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩
  have hm : ∀ y ∈ S, MeasurableSet (φ ⁻¹' {y}) := fun y _ => (l.isOpen_fiber y).measurableSet
  have e₀ : smInt μ (T ∘ φ) = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • T y :=
    smInt_comp μ φ T S hS hm fun y _ hy =>
      measure_level_ne_top μ c fun h => hy (by rw [h, map_zero])
  have e₁ : smInt μ φ = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • y :=
    smInt_comp μ φ id S hS hm fun y _ hy => measure_level_ne_top μ c hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e₀, e₁, map_sum]
  exact Finset.sum_congr rfl fun y _ => (map_smul T _ y).symm

theorem smInt_comp_measurePreserving {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X) {c : X → X} {φ : X → W}
    (hc : MeasurePreserving c μ μ) (l : IsLocallyConstant φ) :
    smInt μ (φ ∘ c) = smInt μ φ := by
  unfold smInt
  refine finsum_congr fun v => ?_
  have h : μ (c ⁻¹' (φ ⁻¹' {v})) = μ (φ ⁻¹' {v}) :=
    hc.measure_preimage (l.isOpen_fiber v).measurableSet.nullMeasurableSet
  rw [Set.preimage_comp, h]

theorem smInt_indicator {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W]
    (μ : Measure X) (A : Set X) (v : W) :
    smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  classical
  unfold smInt
  by_cases hv : v = 0
  · subst hv
    rw [smul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have : (A.indicator fun _ => (0 : W)) ⁻¹' {w} = ∅ := by
        ext x
        simp [Set.indicator_zero', Ne.symm hw]
      rw [this, measure_empty]
      simp
  · rw [finsum_eq_single _ v]
    · have : (A.indicator fun _ => v) ⁻¹' {v} = A := by
        ext x
        by_cases hx : x ∈ A
        · simp [hx]
        · simp [hx, Ne.symm hv]
      rw [this]
    · intro w hw
      by_cases hw0 : w = 0
      · rw [hw0, smul_zero]
      · have : (A.indicator fun _ => v) ⁻¹' {w} = ∅ := by
          ext x
          by_cases hx : x ∈ A
          · simp [hx, Ne.symm hw]
          · simp [hx, Ne.symm hw0]
        simp [this]

theorem smInt_properties : ∀ {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasureOnCompacts μ], (∀ φ₁ φ₂ : X → W, IsLocallyConstant φ₁ → HasCompactSupport φ₁ → IsLocallyConstant φ₂ → HasCompactSupport φ₂ → smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂) ∧ (∀ (T : W →ₗ[ℂ] W') (φ : X → W), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (T ∘ φ) = T (smInt μ φ)) ∧ (∀ (c : X → X) (φ : X → W), MeasureTheory.MeasurePreserving c μ μ → IsLocallyConstant φ → smInt μ (φ ∘ c) = smInt μ φ) ∧ ∀ (A : Set X) (v : W), IsCompact A → IsOpen A → IsClosed A → smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  intro X W W' _ _ _ _ _ _ _ μ _
  exact ⟨fun φ₁ φ₂ l₁ c₁ l₂ c₂ => smInt_add μ l₁ c₁ l₂ c₂,
    fun T φ l c => smInt_linear μ T l c,
    fun c φ hc l => smInt_comp_measurePreserving μ hc l,
    fun A v _ _ _ => smInt_indicator μ A v⟩

end GlobalTheory.CompanionTheory.Rodier.SmIntEl

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpaceComplete
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobComplete

section Limit

variable {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem ae_eq_of_tendsto {K : ℕ → Mat n → V} {L : Mat n → V} {y : Lp V 2 μ}
    (hK : ∀ k, MemLp (fun g : G n => K k g.val) 2 μ)
    (hy : Tendsto (fun k => cls μ (K k)) atTop (𝓝 y))
    (hp : ∀ g : G n, Tendsto (fun k => K k g.val) atTop (𝓝 (L g.val))) :
    y =ᵐ[μ] fun g : G n => L g.val := by
  have hm : TendstoInMeasure μ (fun k => (cls μ (K k) : G n → V)) atTop y :=
    tendstoInMeasure_of_tendsto_Lp hy
  obtain ⟨ns, hns0, hns⟩ := hm.exists_seq_tendsto_ae
  have hc : ∀ᵐ g ∂μ, ∀ k, (cls μ (K k) : G n → V) g = K k (g : G n).val :=
    ae_all_iff.2 fun k => by
      have e : cls μ (K k) = (hK k).toLp _ := dif_pos (hK k)
      rw [e]
      exact (hK k).coeFn_toLp
  filter_upwards [hns, hc] with g h1 h2
  simp only [h2] at h1
  exact tendsto_nhds_unique h1 ((hp g).comp (StrictMono.tendsto_atTop hns0))

end Limit

theorem sob_complete : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], SobG →
    ∀ a : ℕ → Mat n → V, (∀ k, Sob μ (a k)) → (∀ w, CauchySeq fun k => cls μ (Rw w (a k))) →
    ∃ b : Mat n → V, Sob μ b ∧ (∀ w, Tendsto (fun k => cls μ (Rw w (a k))) atTop (𝓝 (cls μ (Rw w b)))) ∧
      ∀ g ∈ GLs n, Tendsto (fun k => a k g) atTop (𝓝 (b g)) := by
  intro n _ _ μ _ V _ _ _ hS a ha hC
  obtain ⟨S, C, hb'⟩ := GlobalTheory.CompanionTheory.CurveJ.sup_bound hS n μ
  have hb := hb' V
  have hs : ∀ k w, Sob μ (Rw w (a k)) := fun k w => GlobalTheory.CompanionTheory.SobOpsPf.sob_Rw w (ha k)
  have hU : ∀ w, UniformCauchySeqOn (fun k => Rw w (a k)) atTop (GLs n) := by
    intro w
    have hT : Tendsto (fun p : ℕ × ℕ => C * ∑ w' ∈ S,
        dist (cls μ (Rw w' (Rw w (a p.1)))) (cls μ (Rw w' (Rw w (a p.2))))) (atTop ×ˢ atTop) (𝓝 0) := by
      have e0 : (C * ∑ w' ∈ S, (0 : ℝ)) = 0 := by simp
      rw [← e0]
      refine Tendsto.const_mul C (tendsto_finsetSum _ fun w' _ => ?_)
      have h1 := hC (w' ++ w)
      simp only [← GlobalTheory.CompanionTheory.CurveJ.Rw_append] at h1
      rw [prod_atTop_atTop_eq]
      exact cauchySeq_iff_tendsto_dist_atTop_0.1 h1
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
    filter_upwards [hT.eventually (gt_mem_nhds hε)] with p hp x hx
    refine hεu ?_
    have b := GlobalTheory.CompanionTheory.CurveJ.bound3 hb (hs p.1 w) (hs p.2 w) (hs p.2 w) 0 hx
    simp only [zero_smul, sub_zero, ← dist_eq_norm] at b
    exact lt_of_le_of_lt b hp
  obtain ⟨Gf, hG, hsm, hR⟩ := _root_.GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth n V a (fun k => (ha k).1) hU
  have hy : ∀ w, ∃ y : Lp V 2 μ, Tendsto (fun k => cls μ (Rw w (a k))) atTop (𝓝 y) := fun w =>
    cauchySeq_tendsto_of_complete (hC w)
  choose y hy using hy
  have hae : ∀ w, y w =ᵐ[μ] fun g : G n => Rw w (Gf []) g.val := by
    intro w
    have h := ae_eq_of_tendsto (fun k => (hs k w).2 []) (K := fun k => Rw w (a k)) (L := Gf w) (hy w)
      (fun g => (hG w).tendsto_at (GlobalTheory.CompanionTheory.SobOpsPf.val_mem g))
    filter_upwards [h] with g hg
    rw [hg, hR w _ (GlobalTheory.CompanionTheory.SobOpsPf.val_mem g)]
  have hM : ∀ w, MemLp (fun g : G n => Rw w (Gf []) g.val) 2 μ := fun w =>
    (Lp.memLp (y w)).ae_eq (hae w)
  have hcl : ∀ w, cls μ (Rw w (Gf [])) = y w := by
    intro w
    rw [GlobalTheory.CompanionTheory.CurveJ.cls_of (hM w)]
    exact Lp.ext ((hM w).coeFn_toLp.trans (hae w).symm)
  refine ⟨Gf [], ⟨hsm, hM⟩, fun w => ?_, fun g hg => (hG []).tendsto_at hg⟩
  rw [hcl w]
  exact hy w

end GlobalTheory.CompanionTheory.SobComplete
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksExponent
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.StandardBlocks

theorem stdBlocks_one {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) (a : Fin n) (i : Fin 1) :
    stdBlocks (fun _ : Fin n => 1) hd ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [hi]

theorem blk_stdBlocks {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) (i : Fin n) :
    blk (stdBlocks (fun _ : Fin n => 1) hd) i = i := by
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective i
  rw [blk_apply]
  exact (stdBlocks_one hd a p).symm

theorem unipRad_stdBlocks (k : Type) [Field k] {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) :
    unipRad k (stdBlocks (fun _ : Fin n => 1) hd) = unipB k (Fin n) := by
  have hb2 : ∀ i : Fin n, blk (points (Fin n)) i = i := fun i => by
    have h := blk_apply (points (Fin n)) i ()
    rwa [points_apply] at h
  ext g
  rw [unipB, mem_unipRad, mem_unipRad, mem_parab, mem_parab]
  simp only [blk_stdBlocks, hb2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a i j => ?_⟩
    have h := h2 a (0 : Fin 1) (0 : Fin 1)
    simp only [stdBlocks_one] at h
    simp only [points_apply]
    rw [h]
    simp [Matrix.one_apply]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a i j => ?_⟩
    have h := h2 a () ()
    simp only [points_apply] at h
    simp only [stdBlocks_one]
    obtain rfl : i = j := Subsingleton.elim i j
    rw [h]
    simp [Matrix.one_apply]

theorem leviEmb_stdBlocks (k : Type) [Field k] {n : ℕ} (hd : ∑ _a : Fin n, 1 = n)
    (t : Levi k fun _ : Fin n => Fin 1) :
    leviEmb k (stdBlocks (fun _ : Fin n => 1) hd) t =
      diagT k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective j
  rw [val_diagT]
  by_cases hab : a = b
  · subst hab
    have hpq : p = q := Subsingleton.elim _ _
    subst hpq
    rw [leviEmb_apply_same, stdBlocks_one]
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, Subsingleton.elim p 0]
  · rw [leviEmb_apply_ne k _ t hab, stdBlocks_one, stdBlocks_one, Matrix.diagonal_apply_ne _ hab]

theorem deltaHalf_stdBlocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Levi k fun _ : Fin n => Fin 1) :
    deltaHalf k (fun _ : Fin n => Fin 1) t =
      deltaHalf k (fun _ : Fin n => Unit)
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp_fin (fun _ : Fin n => Fin 1) (fun _ => Fintype.card_fin 1) a,
    modExp_fin (fun _ : Fin n => Unit) (fun _ => Fintype.card_unit) a]
  congr 1
  exact (congrFun ((leviTorus k (Fin n)).symm_apply_apply
    fun a => Matrix.GeneralLinearGroup.det (t a)) a).symm

theorem twKer_one_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (h : N = N') : twKer π N 1 = twKer π N' 1 := by
  subst h
  rfl

theorem torusChar_stdBlocks {k : Type} [Field k] {n : ℕ} (χ : Fin n → kˣ →* ℂˣ)
    (t : ∀ _ : Fin n, GL (Fin 1) k) :
    PositivityTheory.Lbc.torusChar χ t =
      (torusChar χ (fun a => Matrix.GeneralLinearGroup.det (t a)) : ℂ) := by
  rw [PositivityTheory.Lbc.torusChar, GlobalTheory.SmGL.torusChar, MonoidHom.finsetProd_apply, Units.coe_prod]
  rfl

private theorem smul_mk_eq_smul_mk_of_submodule_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    {p q : Submodule ℂ V} (h : p = q) (a b : ℂ) (u w : V)
    (hk : a • (Submodule.Quotient.mk u : V ⧸ p) = b • Submodule.Quotient.mk w) :
    a • (Submodule.Quotient.mk u : V ⧸ q) = b • Submodule.Quotient.mk w := by
  subst h
  exact hk

theorem stdBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.StdBridge := by
  intro k _ _ _ _ n hd V _ _ π χ y hy heig
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 =
      twKer π (unipRad k (points (Fin n))) 1 :=
    twKer_one_congr π (unipRad_stdBlocks k hd)
  obtain ⟨w, rfl⟩ :=
    Submodule.Quotient.mk_surjective (twKer π (unipRad k (points (Fin n))) 1) y
  refine ⟨(Submodule.Quotient.mk w :
    V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1), ?_, ?_⟩
  · intro h
    apply hy
    have h' : w ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    rw [hK] at h'
    exact (Submodule.Quotient.mk_eq_zero _).mpr h'
  · intro t
    have key : (jac (points (Fin n)) π
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)))
          (Submodule.Quotient.mk w) =
        ((torusChar χ fun a => Matrix.GeneralLinearGroup.det (t a) : ℂˣ) : ℂ) •
          Submodule.Quotient.mk w :=
      heig (fun a => Matrix.GeneralLinearGroup.det (t a))
    have hD : leviEmb k (points (Fin n))
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) =
        diagT k (Fin n) (fun a => Matrix.GeneralLinearGroup.det (t a)) := rfl
    rw [jac_mk, hD] at key
    have heq : (jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (Submodule.Quotient.mk w) =
        PositivityTheory.Lbc.torusChar χ t • (Submodule.Quotient.mk w :
          V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1) := by
      rw [jac_mk, leviEmb_stdBlocks, deltaHalf_stdBlocks, torusChar_stdBlocks]
      exact smul_mk_eq_smul_mk_of_submodule_eq hK.symm _ _ _ _ key
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact heq

end GlobalTheory.CompanionTheory.StandardBlocks

end
end

