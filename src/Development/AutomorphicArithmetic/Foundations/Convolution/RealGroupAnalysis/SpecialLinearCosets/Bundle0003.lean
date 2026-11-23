module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
public import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ClosedEmbeddingVal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem trace_compactOpen {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsClosedEmbedding i)
    (hb : ∀ x, ∀ N ∈ 𝓝 x, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N)
    {C : Set Y} (hCo : IsOpen C) (hCc : IsCompact C) :
    ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i ⁻¹' O = C := by
  have hcl : IsClosed (i '' Cᶜ) := hi.isClosedMap _ hCo.isClosed_compl
  have hloc : ∀ y ∈ C, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i y ∈ O ∧ O ⊆ (i '' Cᶜ)ᶜ := by
    intro y hy
    refine hb (i y) _ (hcl.isOpen_compl.mem_nhds ?_)
    rintro ⟨y', hy', e⟩
    exact hy' (hi.injective e ▸ hy)
  choose! O hOo hOc hOy hON using hloc
  obtain ⟨t, ht, hcov⟩ := hCc.elim_nhds_subcover (fun y => i ⁻¹' O y)
    (fun y hy => ((hOo y hy).preimage hi.continuous).mem_nhds (hOy y hy))
  refine ⟨⋃ y ∈ t, O y, isOpen_biUnion fun y hy => hOo y (ht y hy),
    t.isCompact_biUnion fun y hy => hOc y (ht y hy), ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨z, hz, hy⟩
    by_contra hc
    exact hON z (ht z hz) hy ⟨y, hc, rfl⟩
  · intro hy
    simpa using hcov hy

private theorem indicator_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {O : Set X}
    (hO : IsOpen O) (hc : IsCompact O) : O.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ O
  · exact ⟨O, hO, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Oᶜ, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private theorem extend_SB {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsClosedEmbedding i)
    (hb : ∀ x, ∀ N ∈ 𝓝 x, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N)
    (a : Y → ℂ) (ha : a ∈ SB Y) : ∃ b ∈ SB X, ∀ y, b (i y) = a y := by
  obtain ⟨hlc, hcs⟩ := ha
  have hK : IsCompact (tsupport a) := hcs
  haveI : CompactSpace (tsupport a) := isCompact_iff_compactSpace.mp hK
  have hfin : (Set.range ((tsupport a).restrict a)).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  have hfib : ∀ c : ℂ, c ≠ 0 → ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i ⁻¹' O = a ⁻¹' {c} := by
    intro c hc
    refine trace_compactOpen hi hb (hlc.isOpen_fiber c) (hK.of_isClosed_subset (hlc.isClosed_fiber c) ?_)
    intro y hy
    refine subset_tsupport _ ?_
    rw [Function.mem_support, show a y = c from hy]
    exact hc
  choose! O hOo hOc hOt using hfib
  let S : Finset ℂ := hfin.toFinset.erase 0
  refine ⟨fun x => ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) x, ?_, ?_⟩
  · have : (fun x => ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) x) =
        ∑ c ∈ S, c • (O c).indicator (fun _ => (1 : ℂ)) := by
      ext x
      simp [Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    exact indicator_mem_SB (hOo c hc0) (hOc c hc0)
  · intro y
    have hterm : ∀ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) (i y) = if c = a y then c else 0 := by
      intro c hc
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      have hm : i y ∈ O c ↔ a y = c := by
        have := Set.ext_iff.mp (hOt c hc0) y
        simpa using this
      by_cases h : c = a y
      · rw [Set.indicator_of_mem (hm.mpr h.symm), if_pos h, mul_one]
      · have : i y ∉ O c := fun h' => h (hm.mp h').symm
        rw [Set.indicator_of_notMem this, if_neg h, mul_zero]
    change ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) (i y) = a y
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S (a y) (fun c => c)]
    split_ifs with h
    · rfl
    · have h0 : a y = 0 := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr ⟨⟨y, subset_tsupport _ hne⟩, rfl⟩⟩)
      exact h0.symm

private theorem closedEmbedding_val (F : Type) [Field F] [NumberField F] (v : P F) :
    IsClosedEmbedding (Subtype.val : SL v → M2 v) := by
  have h : IsClosed {m : M2 v | m.det = 1} :=
    isClosed_singleton.preimage (show Continuous (fun m : M2 v => m.det) from continuous_id.matrix_det)
  exact h.isClosedEmbedding_subtypeVal

private theorem compactOpen_basis (F : Type) [Field F] [NumberField F] (v : P F) (x : M2 v) (N : Set (M2 v))
    (hN : N ∈ 𝓝 x) : ∃ O : Set (M2 v), IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N := by
  have h0 : (fun y : M2 v => x + y) ⁻¹' N ∈ 𝓝 (0 : M2 v) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨U, hUo, hUc, hUN⟩ := (UpperTheory.ConvolutionTheory.R2.I.lgrp F v).2
    ((fun y : Multiplicative (M2 v) => Multiplicative.toAdd y) ⁻¹' ((fun y : M2 v => x + y) ⁻¹' N))
    (by
      have : Tendsto (fun y : Multiplicative (M2 v) => Multiplicative.toAdd y) (𝓝 1) (𝓝 (0 : M2 v)) :=
        continuous_toAdd.tendsto _
      exact this h0)
  let e : Multiplicative (M2 v) → M2 v := fun y => x + Multiplicative.toAdd y
  have he : IsOpenEmbedding e := (Homeomorph.addLeft x).isOpenEmbedding
  refine ⟨e '' U, he.isOpenMap _ hUo, hUc.image he.continuous, ⟨1, U.one_mem, by simp [e]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hUN hy

theorem UpperTheory.ConvolutionTheory.R2.I.ext :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : SB (SL v)), ∃ b : SB (M2 v), ∀ m : SL v, b.1 m.1 = a.1 m := by
  intro F _ _ v a
  obtain ⟨b, hb, h⟩ := extend_SB (closedEmbedding_val F v) (compactOpen_basis F v) a.1 a.2
  exact ⟨⟨b, hb⟩, h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Cols
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.ptN :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) (X : M2 v),
      (∀ b, ψl v (-(b * X.det)) * Pt a X = Pt (fun m => a (m * !![1, b; 0, 1])) X) ∧
      ∀ s, Pt a (X * !![1, 0; -s, 1]) = Pt (fun m => ψl v (-(s * m.det)) * a m) X := by
  intro F _ _ v a X
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hadd := (UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.2.1
  refine ⟨fun b => ?_, fun s => ?_⟩
  · unfold Pt
    rw [← integral_const_mul,
      ← integral_add_right_eq_self (μ := μ2 v) (fun c' => ψl v (-(b * X.det)) *
        (a (cols (fun i => X i 1) c') * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0)))
        (b • fun i => X i 1)]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    have hm : cols (fun i => X i 1) c' * !![1, b; 0, 1]
        = cols (fun i => X i 1) (c' + b • fun i => X i 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cols, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hp : ψl v (-(b * X.det)) * ψl v (X 0 0 * (c' + b • fun i => X i 1) 1
          - X 1 0 * (c' + b • fun i => X i 1) 0) = ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) := by
      rw [← hadd]
      congr 1
      simp [Matrix.det_fin_two]
      ring
    simp only [hm]
    rw [mul_left_comm, hp]
  · unfold Pt
    rw [show (fun i => (X * !![1, 0; -s, 1]) i 1) = (fun i => X i 1) by
      funext i
      simp [Matrix.mul_apply, Fin.sum_univ_two]]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    have hp : ψl v ((X * !![1, 0; -s, 1]) 0 0 * c' 1 - (X * !![1, 0; -s, 1]) 1 0 * c' 0)
        = ψl v (-(s * (cols (fun i => X i 1) c').det)) * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) := by
      rw [← hadd]
      congr 1
      simp [cols, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    simp only []
    rw [hp]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ColsHApply
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem tr_mem {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] {a : G → ℂ}
    (ha : a ∈ SB G) (y : G) : (fun x => a (x * y)) ∈ SB G := by
  obtain ⟨h1, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.1 ha
  exact GroundTheory.LocalField.mem_schwartzBruhat.2
    ⟨h1.comp_continuous (continuous_id.mul continuous_const), h2.comp_homeomorph (Homeomorph.mulRight y)⟩

private theorem ind_mem {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) : ind U ∈ SB G := by
  refine GroundTheory.LocalField.mem_schwartzBruhat.2 ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [hUo.mem_nhds hx] with y hy
      have hy' : y ∈ U := hy
      simp [ind, hx, hy']
    · filter_upwards [(U.isClosed_of_isOpen hUo).isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ U := hy
      simp [ind, hx, hy']
  · exact HasCompactSupport.intro hUc fun x hx => by simp [ind, hx]

private theorem ifnSum {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (L : SB G →ₗ[ℂ] ℂ) (hL : ∀ (y : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * y)) → L a' = L a)
    (a a' : SB G) (s : Finset G) (cf : G → ℂ) (h : ∀ x, a.1 x = ∑ g ∈ s, cf g * a'.1 (x * g⁻¹)) :
    L a = (∑ g ∈ s, cf g) * L a' := by
  have e : a = ∑ g ∈ s, cf g • (⟨_, tr_mem a'.2 g⁻¹⟩ : SB G) := by
    apply Subtype.ext
    funext x
    rw [h x, Submodule.coe_sum, Finset.sum_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, smul_eq_mul, hL g⁻¹ a' _ fun _ => rfl]

private theorem ifnAbs {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (hG : Lgrp G) (l I : SB G →ₗ[ℂ] ℂ)
    (hl : ∀ (y : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * y)) → l a' = l a)
    (hI : ∀ (y : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * y)) → I a' = I a)
    (hne : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → IsCompact (U : Set G) → a.1 = ind U → I a ≠ 0) :
    ∃ c : ℂ, ∀ a : SB G, l a = c * I a := by
  have ratio : ∀ (U U' : Subgroup G) (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G))
      (hUo' : IsOpen (U' : Set G)) (hUc' : IsCompact (U' : Set G)), U' ≤ U →
      l ⟨_, ind_mem U hUo hUc⟩ * I ⟨_, ind_mem U' hUo' hUc'⟩ =
        l ⟨_, ind_mem U' hUo' hUc'⟩ * I ⟨_, ind_mem U hUo hUc⟩ := by
    intro U U' hUo hUc hUo' hUc' hle
    obtain ⟨s, -, -, hs⟩ := cosetSum G U U' hle hUc hUo'
    have h : ∀ x, (⟨_, ind_mem U hUo hUc⟩ : SB G).1 x =
        ∑ g ∈ s, (fun _ => (1 : ℂ)) g * (⟨_, ind_mem U' hUo' hUc'⟩ : SB G).1 (x * g⁻¹) := by
      intro x
      simpa using hs x
    rw [ifnSum l hl _ _ s _ h, ifnSum I hI _ _ s _ h]
    ring
  obtain ⟨U₀, hU₀o, hU₀c, -⟩ := hG Set.univ Filter.univ_mem
  refine ⟨l ⟨_, ind_mem U₀ hU₀o hU₀c⟩ / I ⟨_, ind_mem U₀ hU₀o hU₀c⟩, ?_⟩
  have h0 : I ⟨_, ind_mem U₀ hU₀o hU₀c⟩ ≠ 0 := hne U₀ _ hU₀o hU₀c rfl
  intro a
  obtain ⟨U, s, cf, hUo, hUc, -, hs⟩ := cosetSpan G hG a.1 a.2 Set.univ Filter.univ_mem
  have hWo : IsOpen ((U ⊓ U₀ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hUo.inter hU₀o
  have hWc : IsCompact ((U ⊓ U₀ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hUc.inter_right (U₀.isClosed_of_isOpen hU₀o)
  have hW : I ⟨_, ind_mem _ hWo hWc⟩ ≠ 0 := hne _ _ hWo hWc rfl
  have e1 := ratio U _ hUo hUc hWo hWc inf_le_left
  have e2 := ratio U₀ _ hU₀o hU₀c hWo hWc inf_le_right
  have h : ∀ x, a.1 x = ∑ g ∈ s, cf g * (⟨_, ind_mem U hUo hUc⟩ : SB G).1 (x * g⁻¹) := by
    intro x
    rw [hs x]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm g⁻¹ x]
  rw [ifnSum l hl _ _ s _ h, ifnSum I hI _ _ s _ h]
  have key : l ⟨_, ind_mem U hUo hUc⟩ = l ⟨_, ind_mem U₀ hU₀o hU₀c⟩ / I ⟨_, ind_mem U₀ hU₀o hU₀c⟩ * I ⟨_, ind_mem U hUo hUc⟩ := by
    rw [div_mul_eq_mul_div, eq_div_iff h0]
    apply mul_right_cancel₀ hW
    linear_combination (I ⟨_, ind_mem U₀ hU₀o hU₀c⟩) * e1 - (I ⟨_, ind_mem U hUo hUc⟩) * e2
  rw [key]
  ring

section Meas
variable {F : Type} [Field F] [NumberField F] {v : P F}

private def colsH : ((Fin 2 → Kv v) × (Fin 2 → Kv v)) ≃ₜ M2 v where
  toFun p := cols p.1 p.2
  invFun X := (fun i => X i 0, fun i => X i 1)
  left_inv p := by
    ext i <;> fin_cases i <;> simp [cols]
  right_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cols]
  continuous_toFun := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [cols] <;> simp <;> fun_prop
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_ <;> refine continuous_pi fun i => ?_ <;> fun_prop

private theorem cols_add (p q : (Fin 2 → Kv v) × (Fin 2 → Kv v)) :
    cols (p + q).1 (p + q).2 = cols p.1 p.2 + cols q.1 q.2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cols]

private theorem int_sb {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) :
    Integrable (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a (cols p.1 p.2)) ((μ2 v).prod (μ2 v)) := by
  obtain ⟨h1, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.1 ha
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  exact (h1.continuous.comp colsH.continuous).integrable_of_hasCompactSupport (h2.comp_homeomorph colsH)

private noncomputable def IMl : SB (M2 v) →ₗ[ℂ] ℂ where
  toFun a := IM a.1
  map_add' a b := by
    simp only [IM]
    exact integral_add (int_sb a.2) (int_sb b.2)
  map_smul' c a := by
    simp only [IM, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c _

end Meas

theorem UpperTheory.ConvolutionTheory.R2.I.invFn :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (ℓ : SB (M2 v) →ₗ[ℂ] ℂ), (∀ (y : M2 v) (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m + y)) → ℓ a' = ℓ a) →
      ∃ c : ℂ, ∀ a : SB (M2 v), ℓ a = c * IM a.1 := by
  intro F _ _ v ℓ hℓ
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hI : ∀ (y : M2 v) (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m + y)) → IM a'.1 = IM a.1 := by
    intro y a a' h
    have e : (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a'.1 (cols p.1 p.2)) =
        fun p => (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) (p + colsH.symm y) := by
      funext p
      have hy : cols (colsH.symm y).1 (colsH.symm y).2 = y := colsH.apply_symm_apply y
      simp only [cols_add, hy]
      exact h _
    simp only [IM]
    rw [e]
    exact integral_add_right_eq_self (μ := (μ2 v).prod (μ2 v)) (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) (colsH.symm y)
  have hne : ∀ (U : Subgroup (Multiplicative (M2 v))) (a : SB (M2 v)), IsOpen (U : Set (Multiplicative (M2 v))) →
      IsCompact (U : Set (Multiplicative (M2 v))) → a.1 = ind U → IM a.1 ≠ 0 := by
    intro U a hUo hUc ha
    let S : Set ((Fin 2 → Kv v) × (Fin 2 → Kv v)) := colsH ⁻¹' {X : M2 v | Multiplicative.ofAdd X ∈ U}
    have hSo : IsOpen S := IsOpen.preimage colsH.continuous hUo
    have hSc : IsCompact S := colsH.isCompact_preimage.2 hUc
    have hSn : S.Nonempty := ⟨colsH.symm (0 : M2 v), by
      show colsH (colsH.symm (0 : M2 v)) ∈ {X : M2 v | Multiplicative.ofAdd X ∈ U}
      rw [colsH.apply_symm_apply]
      exact U.one_mem⟩
    have e : (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) = S.indicator fun _ => (1 : ℂ) := by
      funext p
      rw [ha]
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        exact Set.indicator_of_mem (s := (U : Set (Multiplicative (M2 v)))) hp _
      · rw [Set.indicator_of_notMem hp]
        exact Set.indicator_of_notMem (s := (U : Set (Multiplicative (M2 v)))) hp _
    simp only [IM]
    rw [e, integral_indicator_const _ hSo.measurableSet]
    have hpos : ((μ2 v).prod (μ2 v)) S ≠ 0 := (hSo.measure_pos _ hSn).ne'
    have hfin : ((μ2 v).prod (μ2 v)) S ≠ ⊤ := hSc.measure_lt_top.ne
    have : ((μ2 v).prod (μ2 v)).real S ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩
    simpa using this
  haveI : T2Space (Multiplicative (M2 v)) := inferInstanceAs (T2Space (M2 v))
  obtain ⟨c, hc⟩ := ifnAbs (G := Multiplicative (M2 v)) (lgrp F v).2 ℓ IMl
    (fun y a a' h => hℓ (Multiplicative.toAdd y) a a' h)
    (fun y a a' h => hI (Multiplicative.toAdd y) a a' h)
    (fun U a hUo hUc ha => hne U a hUo hUc ha)
  exact ⟨c, hc⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.EqOfBelowSelf
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I.PlaceCoordinates

open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem cont_symm (v : P F) (w : P E) (i : Kv v ≃+* Kv w) (hi : Continuous i) :
    Continuous i.symm := by
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  exact i.toEquiv.continuous_symm_iff.2
    (AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi)

private theorem eq_completionMap (v : P F) (w : P E) [w.asIdeal.LiesOver v.asIdeal] (i : Kv v →+* Kv w)
    (hi : Continuous i) (hc : ∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) (k : Kv v) :
    i k = completionMap v w k := by
  have h := (HeightOneSpectrum.denseRange_algebraMap F v).equalizer hi (continuous_completionMap v w)
    (funext fun x => by
      simp only [Function.comp]
      rw [hc, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w)])
  exact congrFun h k

private theorem eq_of_below_self {w w' : P E} (h : Below w w') : w' = w := by
  refine HeightOneSpectrum.ext ?_
  rw [show w.asIdeal = _ from h]
  ext x
  exact Iff.rfl

private theorem coord (D : Dat F E) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * D.θ := by
  refine ⟨D.b.repr x 0, D.b.repr x 1, ?_⟩
  conv_lhs => rw [← D.b.sum_repr x]
  simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]

private theorem place_eq (D : Dat F E) (v : P F) (w w' : P E) [w'.asIdeal.LiesOver v.asIdeal]
    (i : Kv v ≃+* Kv w) (hi : Continuous i)
    (hc : ∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x))
    (h : completionMap v w' (i.symm (algebraMap E (Kv w) D.θ)) = algebraMap E (Kv w') D.θ) : w' = w := by
  have hF : ∀ a : F, i.symm (algebraMap E (Kv w) (algebraMap F E a)) = algebraMap F (Kv v) a := fun a => by
    rw [← hc, RingEquiv.symm_apply_apply]
  refine eq_of_below_self (I.below E E w w' ((completionMap v w').comp i.symm.toRingHom)
    ((continuous_completionMap v w').comp (cont_symm v w i hi)) fun x => ?_)
  obtain ⟨a, b, rfl⟩ := coord D x
  change completionMap v w' (i.symm (algebraMap E (Kv w) _)) = algebraMap E (Kv w') _
  simp only [map_add (f := _), map_mul, hF, h, completionMap_algebraMap, Algebra.algebraMap_self, RingHom.id_apply,
    IsScalarTower.algebraMap_apply F E (Kv w')]

private theorem sE_snd_above (D : Dat F E) (v : P F) (θ k : Kv v) (w' : P E)
    [hl : w'.asIdeal.LiesOver v.asIdeal] :
    (sE D v θ k).2 w' = completionMap v w' (k / 2) +
      completionMap v w' (k / (2 * θ)) * algebraMap E (Kv w') D.θ := by
  have hb : AdeleBaseChange.below F w' = v := (below_eq_iff _ _).2 hl
  subst hb
  obtain ⟨-, -, hs, -⟩ := sgLaws F (AdeleBaseChange.below F w')
  change completionMap (AdeleBaseChange.below F w') w' ((sg (AdeleBaseChange.below F w') (k / 2)).2 (AdeleBaseChange.below F w')) +
    completionMap (AdeleBaseChange.below F w') w' ((sg (AdeleBaseChange.below F w') (k / (2 * θ))).2 (AdeleBaseChange.below F w')) * algebraMap E (Kv w') D.θ = _
  rw [show (sg (AdeleBaseChange.below F w') (k / 2)).2 (AdeleBaseChange.below F w') = k / 2 from hs _,
    show (sg (AdeleBaseChange.below F w') (k / (2 * θ))).2 (AdeleBaseChange.below F w') = k / (2 * θ) from hs _]

private theorem sE_snd_not_above (D : Dat F E) (v : P F) (θ k : Kv v) (w' : P E) (hb : AdeleBaseChange.below F w' ≠ v) :
    (sE D v θ k).2 w' = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hs, -⟩ := sgLaws F v
  change completionMap (AdeleBaseChange.below F w') w' ((sg v (k / 2)).2 (AdeleBaseChange.below F w')) +
    completionMap (AdeleBaseChange.below F w') w' ((sg v (k / (2 * θ))).2 (AdeleBaseChange.below F w')) * algebraMap E (Kv w') D.θ = _
  rw [(hs _).2 _ hb, (hs _).2 _ hb, map_zero, zero_mul, add_zero]

private theorem sE_fst (D : Dat F E) (v : P F) (θ k : Kv v) : (sE D v θ k).1 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hs, -⟩ := sgLaws F v
  change InfinitePlace.infiniteAdeleRingMap (sg v (k / 2)).1 +
    InfinitePlace.infiniteAdeleRingMap (sg v (k / (2 * θ))).1 * (rt D.θ).1 = 0
  rw [(hs _).1, (hs _).1, map_zero, zero_mul, add_zero]

end UpperTheory.ConvolutionTheory.R2.I.PlaceCoordinates

open UpperTheory.ConvolutionTheory.R2.I.PlaceCoordinates GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.ConvolutionTheory.R2.I.place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (w : P E) (i : Kv v ≃+* Kv w), Continuous i →
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
      ∃ θ : Kv v, θ ^ 2 = algebraMap F (Kv v) D.δ ∧ θ ≠ 0 ∧ ∀ k, sg w (i k) = sE D v θ k := by
  intro F E _ _ _ _ _ D v w i hi hc
  have hb : Below v w := I.below F E v w i.toRingHom hi hc
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨hb⟩
  have hθE : D.θ ≠ 0 := D.b1 ▸ D.b.ne_zero 1
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = i.symm (algebraMap E (Kv w) D.θ) := ⟨_, rfl⟩
  have hiθ : i θ = algebraMap E (Kv w) D.θ := by rw [hθ, RingEquiv.apply_symm_apply]
  have hsq : θ ^ 2 = algebraMap F (Kv v) D.δ := by
    apply i.injective
    rw [map_pow, hiθ, hc, ← map_pow, D.sq]
  have hne : θ ≠ 0 := fun h => hθE ((map_eq_zero _).1 (by rw [← hiθ, h, map_zero]))
  have h2 : (2 : Kv v) ≠ 0 := by
    have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
    exact two_ne_zero
  refine ⟨θ, hsq, hne, fun k => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hs, -⟩ := sgLaws E w
  obtain ⟨-, -, hs0, -⟩ := sgLaws E w
  refine Prod.ext ((hs _).1.trans (sE_fst D v θ k).symm) (FiniteAdeleRing.ext E fun w' => ?_)
  by_cases hv : AdeleBaseChange.below F w' = v
  · haveI hl' : w'.asIdeal.LiesOver v.asIdeal := (below_eq_iff _ _).1 hv
    change (sg w (i k)).2 w' = (sE D v θ k).2 w'
    rw [sE_snd_above]
    by_cases hw : w' = w
    · subst hw
      have e := eq_completionMap v w' i.toRingHom hi hc
      have e' : ∀ x, completionMap v w' x = i x := fun x => (e x).symm
      rw [show (sg w' (i k)).2 w' = i k from hs0 _, e', e', ← hiθ, ← map_mul, ← map_add (f := _)]
      congr 1
      field_simp
      ring
    · have hj : completionMap v w' θ ≠ algebraMap E (Kv w') D.θ := fun h =>
        hw (place_eq D v w w' i hi hc (hθ ▸ h))
      have hj2 : completionMap v w' θ ^ 2 = algebraMap E (Kv w') D.θ ^ 2 := by
        rw [← map_pow, hsq, completionMap_algebraMap, ← map_pow, D.sq,
          IsScalarTower.algebraMap_apply F E (Kv w')]
      have hneg : algebraMap E (Kv w') D.θ = -completionMap v w' θ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hj2 with h | h
        · exact absurd h hj
        · rw [h, neg_neg]
      rw [(hs _).2 _ hw, hneg, mul_neg, ← map_mul, ← map_neg, ← map_add (f := _)]
      rw [show k / 2 + -(k / (2 * θ) * θ) = 0 by field_simp; ring, map_zero]
  · have hw : w' ≠ w := fun h => hv (h ▸ (below_eq_iff _ _).2 hl)
    exact ((hs _).2 _ hw).trans (sE_snd_not_above D v θ k w' hv).symm
end

