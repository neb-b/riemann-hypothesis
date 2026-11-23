module

public import Formalism.HarderNarasimhan.DegSupermodZ
public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0004
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0002
public import Lemmata.GeneralBFactSecondTail.Imports

@[expose] public section

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
section
open Module Submodule

noncomputable section

namespace Formalism.HN

section Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem duality_mem_dualZ (L : Submodule ℤ E) (y : E) :
    y ∈ dualZ L ↔ y ∈ span ℝ (L : Set E) ∧ ∀ x ∈ L, ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
  have key : ∀ x : E, y ∈ ((Int.castAddHom ℝ).range.toIntSubmodule).comap
      ((innerSL ℝ x : E →L[ℝ] ℝ).toLinearMap.restrictScalars ℤ) ↔
        ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
    intro x
    rw [Submodule.mem_comap]
    change (innerSL ℝ x) y ∈ (Int.castAddHom ℝ).range ↔ _
    rw [AddMonoidHom.mem_range]
    simp
  simp only [dualZ, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_iInf, key]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem duality_inner_sum_dual (v w : ι → E)
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) (c : ι → ℝ) (k : ι) :
    inner ℝ (v k) (∑ i, c i • w i) = c k := by
  simp [inner_sum, real_inner_smul_right, hvw]

theorem duality_eq_zero_of_inner (v : ι → E) {z : E} (hz : z ∈ span ℝ (Set.range v))
    (h : ∀ k, inner ℝ (v k) z = 0) : z = 0 := by
  have hall : ∀ u ∈ span ℝ (Set.range v), inner ℝ u z = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact h k
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  have hzz := hall z hz
  exact inner_self_eq_zero.mp hzz

theorem duality_expand (v w : ι → E) (hw : ∀ i, w i ∈ span ℝ (Set.range v))
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) {y : E}
    (hy : y ∈ span ℝ (Set.range v)) : y = ∑ k, inner ℝ (v k) y • w k := by
  have hs : (∑ k, inner ℝ (v k) y • w k) ∈ span ℝ (Set.range v) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hw k)
  have h0 := duality_eq_zero_of_inner v (Submodule.sub_mem _ hy hs) fun j => by
    have h2 := duality_inner_sum_dual v w hvw (fun k => inner ℝ (v k) y) j
    rw [inner_sub_right, sub_eq_zero]
    exact h2.symm
  exact sub_eq_zero.mp h0

private theorem exists_int_inner_of_mem_span_int (v : ι → E) (y : E)
    (hy : ∀ k, ∃ n : ℤ, (n : ℝ) = inner ℝ (v k) y) {x : E} (hx : x ∈ span ℤ (Set.range v)) :
    ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hy k
  | zero => exact ⟨0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [inner_add_left, ← ha, ← hb, Int.cast_add]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a * b, ?_⟩
    have hsm : a • x = (a : ℝ) • x := by
      exact (Int.cast_smul_eq_zsmul (R := ℝ) a x).symm
    rw [hsm, real_inner_smul_left, ← hb, Int.cast_mul]

theorem duality_dualZ_span (v w : ι → E) (hw : ∀ i, w i ∈ span ℝ (Set.range v))
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) :
    dualZ (span ℤ (Set.range v)) = span ℤ (Set.range w) := by
  have hspan : span ℝ ((span ℤ (Set.range v) : Submodule ℤ E) : Set E) = span ℝ (Set.range v) := by
    exact Submodule.span_span_of_tower ℤ ℝ (Set.range v)
  apply le_antisymm
  · intro y hy
    rw [duality_mem_dualZ, hspan] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [duality_expand v w hw hvw hy1]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨n, hn⟩ := hy2 (v k) (Submodule.subset_span (Set.mem_range_self k))
    have hsm : inner ℝ (v k) y • w k = n • w k := by
      rw [← hn]
      exact Int.cast_smul_eq_zsmul (R := ℝ) n (w k)
    rw [hsm]
    exact Submodule.smul_mem _ n (Submodule.subset_span (Set.mem_range_self k))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, duality_mem_dualZ, hspan]
    refine ⟨hw i, fun x hx => exists_int_inner_of_mem_span_int v (w i) (fun k => ?_) hx⟩
    refine ⟨if k = i then 1 else 0, ?_⟩
    rw [hvw]
    split_ifs <;> simp

theorem duality_linIndep (v w : ι → E)
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) : LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  rw [← duality_inner_sum_dual v w hvw g k, hg, inner_zero_right]

theorem duality_exists_dual (v : ι → E) (hv : LinearIndependent ℝ v) :
    ∃ w : ι → E, (∀ i, w i ∈ span ℝ (Set.range v)) ∧
      (∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) ∧
      (Matrix.gram ℝ w).det = ((Matrix.gram ℝ v).det)⁻¹ := by
  have hGdet : (Matrix.gram ℝ v).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc0
    have hz : ∑ i, c i • v i = 0 := by
      refine duality_eq_zero_of_inner v
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_range_self i))) fun k => ?_
      have hk : ∑ i, Matrix.gram ℝ v k i * c i = 0 := congrFun hc k
      rw [inner_sum, ← hk]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, Matrix.gram_apply, mul_comm]
    funext i
    exact Fintype.linearIndependent_iff.mp hv c hz i
  have hunit : IsUnit (Matrix.gram ℝ v).det := isUnit_iff_ne_zero.mpr hGdet
  have hmul : Matrix.gram ℝ v * (Matrix.gram ℝ v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hmul' : (Matrix.gram ℝ v)⁻¹ * Matrix.gram ℝ v = 1 := Matrix.nonsing_inv_mul _ hunit
  refine ⟨fun i => ∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j,
    fun i => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)), fun k i => ?_, ?_⟩
  · show inner ℝ (v k) (∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j) = if k = i then 1 else 0
    have h := congrFun (congrFun hmul k) i
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [inner_sum, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, Matrix.gram_apply, mul_comm]
  · show (Matrix.gram ℝ (fun i => ∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j)).det = _
    rw [Formalism.F.gram_sum_smul_eq_transpose_mul v (Matrix.gram ℝ v)⁻¹, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose]
    have h1 : ((Matrix.gram ℝ v)⁻¹).det * (Matrix.gram ℝ v).det = 1 := by
      rw [← Matrix.det_mul, hmul', Matrix.det_one]
    rw [h1, one_mul]
    exact eq_inv_of_mul_eq_one_left h1

variable [FiniteDimensional ℝ E]

private theorem rk_span_range_eq_card_of_linearIndependent (u : ι → E) (hu : LinearIndependent ℝ u) :
    Formalism.F.rk (span ℤ (Set.range u)) = Fintype.card ι := by
  have := (Formalism.F.discreteTopology_span_range_and_covol u hu).1
  rw [Formalism.F.rank_eq_finrank_span (span ℤ (Set.range u)), Submodule.span_span_of_tower,
    finrank_span_eq_card hu]

theorem duality_basic (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (dualZ L) ∧ Formalism.F.rk (dualZ L) = Formalism.F.rk L ∧
    Formalism.F.deg (dualZ L) = - Formalism.F.deg L ∧ dualZ (dualZ L) = L := by
  obtain ⟨v, hv, hL⟩ : ∃ v : Fin (Module.finrank ℤ L) → E,
      LinearIndependent ℝ v ∧ span ℤ (Set.range v) = L :=
    ⟨fun i => ((Module.finBasis ℤ L i : L) : E),
      Formalism.F.linearIndependent_coe_basis L (Module.finBasis ℤ L),
      Formalism.F.span_range_coe_basis' L (Module.finBasis ℤ L)⟩
  obtain ⟨w, hw, hvw, hdet⟩ := duality_exists_dual v hv
  have hwli := duality_linIndep v w hvw
  have hdual : dualZ L = span ℤ (Set.range w) := by
    rw [← duality_dualZ_span v w hw hvw, hL]
  have hwv : ∀ k i, inner ℝ (w k) (v i) = if k = i then 1 else 0 := by
    intro k i
    rw [real_inner_comm, hvw]
    by_cases h : k = i
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hv' : ∀ i, v i ∈ span ℝ (Set.range w) := by
    intro i
    rw [duality_expand v w hw hvw (Submodule.subset_span (Set.mem_range_self i))]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self k))
  have hrkL := rk_span_range_eq_card_of_linearIndependent v hv
  rw [hL] at hrkL
  have hcv := (Formalism.F.discreteTopology_span_range_and_covol v hv).2
  rw [hL] at hcv
  have hcw := Formalism.F.discreteTopology_span_range_and_covol w hwli
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdual]
    exact hcw.1
  · rw [hdual, rk_span_range_eq_card_of_linearIndependent w hwli, hrkL]
  · rw [hdual]
    unfold Formalism.F.deg
    rw [hcw.2, hcv, hdet, Real.sqrt_inv, Real.log_inv]
  · rw [hdual, duality_dualZ_span w v hv' hwv, hL]

private theorem starProjection_mem_and_sub_mem_orthogonal (K : Submodule ℝ E)
    [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x ∈ K ∧ x - K.starProjection x ∈ Kᗮ := by
  constructor
  · exact K.starProjection_apply_mem x
  · exact K.sub_starProjection_mem_orthogonal x

theorem duality_dualZ_quot_le (L T : Submodule ℤ E) (hT : T ≤ L) :
    dualZ (Formalism.F.quot L T) ≤ dualZ L := by
  intro y hy
  rw [duality_mem_dualZ] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  have hWL : span ℝ (T : Set E) ≤ span ℝ (L : Set E) := Submodule.span_mono hT
  have hQ : ∀ x ∈ L, (span ℝ (T : Set E))ᗮ.starProjection x ∈ Formalism.F.quot L T ∧
      (span ℝ (T : Set E))ᗮ.starProjection x ∈ (span ℝ (T : Set E))ᗮ ∧
      x - (span ℝ (T : Set E))ᗮ.starProjection x ∈ span ℝ (T : Set E) := by
    intro x hx
    obtain ⟨h1, h2⟩ := starProjection_mem_and_sub_mem_orthogonal (span ℝ (T : Set E))ᗮ x
    refine ⟨Submodule.mem_map_of_mem
      (f := ((span ℝ (T : Set E))ᗮ.starProjection : E →L[ℝ] E).toLinearMap.restrictScalars ℤ) hx,
      h1, ?_⟩
    rwa [Submodule.orthogonal_orthogonal] at h2
  have hspan : span ℝ (Formalism.F.quot L T : Set E) ≤
      (span ℝ (T : Set E))ᗮ ⊓ span ℝ (L : Set E) := by
    refine Submodule.span_le.mpr fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hq
    change (span ℝ (T : Set E))ᗮ.starProjection x ∈ (span ℝ (T : Set E))ᗮ ⊓ span ℝ (L : Set E)
    obtain ⟨-, h1, h2⟩ := hQ x hx
    rw [Submodule.mem_inf]
    refine ⟨h1, ?_⟩
    have h4 := Submodule.sub_mem _ (Submodule.subset_span hx : x ∈ span ℝ (L : Set E)) (hWL h2)
    rwa [sub_sub_cancel] at h4
  obtain ⟨hyW, hyL⟩ := Submodule.mem_inf.mp (hspan hy1)
  refine ⟨hyL, fun x hx => ?_⟩
  obtain ⟨hq, -, h2⟩ := hQ x hx
  obtain ⟨n, hn⟩ := hy2 _ hq
  refine ⟨n, ?_⟩
  have h0 : inner ℝ (x - (span ℝ (T : Set E))ᗮ.starProjection x) y = 0 := by
    exact Submodule.inner_right_of_mem_orthogonal h2 hyW
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [hn, h0]

end Dual

universe u

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeIneq
section
open Module NumberField

noncomputable section

namespace Formalism.HN

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem sizeIneq_exists_mul_mem (A : Submodule (𝓞 K) V) (x : V)
    (hx : x ∈ Submodule.span K (A : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first | exact Bl.general_b_fact_second''''''.goal1 .. | (apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> first | assumption | infer_instance)

theorem sizeIneq_span_inf_ker (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    Submodule.span K ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (A : Set V) ⊓ LinearMap.ker φ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨hxA, hxk⟩
    exact ⟨Submodule.subset_span hxA, hxk⟩
  · rintro x ⟨hxS, hxk⟩
    obtain ⟨d, hd, hdx⟩ := sizeIneq_exists_mul_mem A x hxS
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := by
      intro h0
      exact hd (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
    have hmem : d • x ∈ (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine ⟨hdx, ?_⟩
      show φ (d • x) = 0
      rw [← algebraMap_smul K d x, map_smul, LinearMap.mem_ker.mp hxk, smul_zero]
    have hx : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem sizeIneq_rk [FiniteDimensional K V] (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) + rkK (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) =
      rkK A := by
  unfold rkK
  set S := Submodule.span K (A : Set V) with hS
  have h1 : Submodule.span K ((A.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) =
      S.map φ := by
    rw [Submodule.map_coe, hS, Submodule.map_span]
    rfl
  rw [h1, sizeIneq_span_inf_ker]
  have := (φ.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at this
  rw [← this, ← Submodule.map_comap_subtype S (LinearMap.ker φ)]
  congr 1
  exact (Submodule.equivMapOfInjective _ S.injective_subtype _).finrank_eq.symm

end SlopeTestRemainingChoices

theorem sizeIneq_of (h1 : SizeMu) (h2 : HtImage) (h3 : PlLat) : SizeIneq := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hIB hI0
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hrkeq := sizeIneq_rk φ A
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set A₀ := A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) with hA₀def
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hA0 : A ≠ ⊥ := by
    intro h
    apply hI0
    rw [hIdef, h, Submodule.map_bot]
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIB))
  obtain ⟨hAlat, -, -⟩ := h3 K V ι b X hX A hAfg
  obtain ⟨hBlat, -, -⟩ := h3 K W κ b' X' hX' B hBfg
  obtain ⟨-, hrkI, hhtI⟩ := h3 K W κ b' X' hX' I hIfg
  obtain ⟨hsat, hht⟩ := h2 K V ι W κ b X b' X' hX hX' φ A hAfg
  have hSA := h1 K V ι b X hX A hAfg hA0
  have hSB := h1 K W κ b' X' hX' B hBfg hB0
  obtain ⟨-, -, hsQ, -, hlarge, -⟩ := hSA
  obtain ⟨-, -, -, hleast, -, -⟩ := hSB
  have hSI := (h1 K W κ b' X' hX' I hIfg hI0).1

  have hA₀ne : A₀ ≠ A := by
    intro h
    apply hI0
    rw [eq_bot_iff]
    rintro y ⟨x, hx, rfl⟩
    have hx0 : x ∈ A₀ := h ▸ hx
    exact (Submodule.mem_bot _).2 (LinearMap.mem_ker.1 hx0.2)

  have hSBB := saturation_basic_properties (𝓞 K) W _ ρ' B hBlat
  have hrkIpos : 0 < rk ρ' I := by
    rcases Nat.eq_zero_or_pos (rk ρ' I) with h | h
    · exact absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0
    · exact h
  have hMB := slope_characterization (𝓞 K) W _ ρ' B hBlat hB0
  have hdegI := (hMB.1 (muMax ρ' B)).1 le_rfl I hIB
  have hslI : slope ρ' I ≤ muMax ρ' B := by
    show Formalism.F.deg (zl ρ' I) / (Formalism.F.rk (zl ρ' I) : ℝ) ≤ _
    rw [div_le_iff₀ (by exact_mod_cast hrkIpos)]
    exact hdegI
  have hleI : leastSize b' X' B ≤ size b' X' I := by
    rw [hleast, hSI]
    exact Real.exp_le_exp.2 (by linarith)

  have hSBA := saturation_basic_properties (𝓞 K) V _ ρ A hAlat
  have hq := hSBA.2.2.2.2.2.2.2 A₀ hsat
  have hlt : rk ρ A₀ < rk ρ A := by
    refine lt_of_le_of_ne hq.2.1 (fun h => hA₀ne ?_)
    exact (hSBA.2.2.1 A₀ A hsat hsat.1 le_rfl h.symm).symm
  have hMA := slope_characterization (𝓞 K) V _ ρ A hAlat hA0
  have hmin := (hMA.2.1 (muMin ρ A)).1 le_rfl A₀ hsat.1
  have hslQ : muMin ρ A ≤ Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ A₀)) := by
    have hr : (Formalism.F.rk (Formalism.F.quot (zl ρ A) (zl ρ A₀)) : ℝ) = (rk ρ A : ℝ) - rk ρ A₀ := by
      rw [hq.1, Nat.cast_sub hq.2.1]
    have hrpos : (0 : ℝ) < (rk ρ A : ℝ) - rk ρ A₀ := by
      have : (rk ρ A₀ : ℝ) < rk ρ A := by exact_mod_cast hlt
      linarith
    unfold Formalism.F.slope
    rw [hr, le_div_iff₀ hrpos, hq.2.2]
    exact hmin
  have hQle : sizeQ b X A A₀ ≤ largestSize b X A := by
    rw [hlarge, hsQ A₀ hsat hA₀ne]
    exact Real.exp_le_exp.2 (by linarith)
  have hlargepos : 0 < largestSize b X A := by rw [hlarge]; exact Real.exp_pos _

  set P := ∏ v, opNormAt b X b' X' v φ with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg (fun v _ => norm_nonneg _)
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hs : (0 : ℝ) < rkK I := by
    have : rkK I ≠ 0 := by
      intro h
      rw [hrkI, h, mul_zero] at hrkIpos
      exact lt_irrefl _ hrkIpos
    exact_mod_cast Nat.pos_of_ne_zero this
  have hrkR : ((rkK A : ℝ) - rkK A₀) = rkK I := by
    rw [← hrkeq]; push_cast; ring
  rw [Finset.prod_pow] at hht
  have hX0 : 0 ≤ P ^ (2 * rkK I) := pow_nonneg hP _
  have hQpos : 0 < htQ b X A A₀ := pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0
  have he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ)) := by positivity
  have hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀ := by
    unfold size sizeQ
    rw [hrkR]
    calc ht b' X' I ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ)))
        ≤ (P ^ (2 * rkK I) * htQ b X A A₀) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.rpow_le_rpow hhtI.le hht he
      _ = (P ^ (2 * rkK I)) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) *
            htQ b X A A₀ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.mul_rpow hX0 hQpos.le
      _ = P ^ ((1 : ℝ) / (nPl K : ℝ)) *
            htQ b X A A₀ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP]
          congr 1
          push_cast
          field_simp
  rw [div_le_iff₀ hlargepos]
  calc leastSize b' X' B ≤ size b' X' I := hleI
    _ ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀ := hcore
    _ ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * largestSize b X A :=
        mul_le_mul_of_nonneg_left hQle (Real.rpow_nonneg hP _)

end Formalism.HN
end
end

