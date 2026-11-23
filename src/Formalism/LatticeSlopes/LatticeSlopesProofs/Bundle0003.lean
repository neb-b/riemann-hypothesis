module

public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle0001
public import Formalism.LatticeSlopes.CovolAntiSameRank

@[expose] public section

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality
section
open Module Submodule

noncomputable section

namespace Formalism.F

universe u v

private theorem finrank_int_eq_finrank_real_span {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L₀ ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      invFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e) ?_ e.injective
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub x hx⟩, hx, rfl⟩
  haveI : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype
    rw [Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]
  rw [← e.finrank_eq, ZLattice.rank ℝ L₀]

theorem linearIndependent_coe_basis'' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical
  have h1 : Submodule.span ℤ (Set.range (fun i => (b i : E))) = L := by
    have := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range (fun i => (b i : E))) =
      Submodule.span ℝ (L : Set E) := by
    have h2 := Submodule.span_span_of_tower ℤ ℝ (Set.range (fun i => (b i : E)))
    rw [h1] at h2
    exact h2.symm
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, ← finrank_int_eq_finrank_real_span L,
    Module.finrank_eq_card_basis b]

theorem det_gram_basis_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    0 < (Matrix.gram ℝ (fun i => (b i : E))).det :=
  (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis'' L b)).det_pos

theorem covol_pos_of_discrete {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    0 < covol L := by
  classical
  rw [covol, dite_eq_left (inferInstance : DiscreteTopology L)]
  exact Real.sqrt_pos.mpr (det_gram_basis_pos L _)

theorem norm_sum_smul_le_of_int {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (v : ι → E) (w : ι → F)
    (C : ℝ) (h : ∀ n : ι → ℤ, ‖∑ i, (n i : ℝ) • w i‖ ≤ C * ‖∑ i, (n i : ℝ) • v i‖) :
    ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖ := by

  have hq : ∀ q : ι → ℚ, ‖∑ i, (q i : ℝ) • w i‖ ≤ C * ‖∑ i, (q i : ℝ) • v i‖ := by
    intro q
    classical
    obtain ⟨m, hm, hz⟩ : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ z : ℤ, (q i : ℝ) * m = z := by
      refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), fun i => ?_⟩
      obtain ⟨k, hk⟩ : (q i).den ∣ ∏ j, (q j).den :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(q i).num * k, ?_⟩
      rw [hk]
      push_cast
      rw [← mul_assoc]
      congr 1
      exact_mod_cast Rat.mul_den_eq_num (q i)
    choose n hn using hz
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hw : ∑ i, (n i : ℝ) • w i = (m : ℝ) • ∑ i, (q i : ℝ) • w i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hn i, smul_smul, mul_comm]
    have hv : ∑ i, (n i : ℝ) • v i = (m : ℝ) • ∑ i, (q i : ℝ) • v i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hn i, smul_smul, mul_comm]
    have key := h n
    rw [hw, hv, norm_smul, norm_smul, Real.norm_of_nonneg hm'.le, mul_left_comm] at key
    exact le_of_mul_le_mul_left key hm'

  intro c
  have hd : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  refine hd.induction_on (p := fun c : ι → ℝ => ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖) c ?_ hq
  exact isClosed_le (by fun_prop) (by fun_prop)

theorem slopeInequality_of (h : SlopeLeMuMax.{v}) : SlopeInequality.{u, v} := by
  intro E F _ _ _ _ _ _ L M hL hM hne φ C hφ hC
  classical
  let g : L →ₗ[ℤ] F := M.subtype.comp φ
  have ginj : Function.Injective g := M.injective_subtype.comp hφ
  let N : Submodule ℤ F := LinearMap.range g
  have hNM : N ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact (φ x).2
  haveI : DiscreteTopology L := hL
  haveI : DiscreteTopology M := hM
  haveI : DiscreteTopology N :=
    DiscreteTopology.of_continuous_injective (continuous_inclusion hNM)
      (Submodule.inclusion_injective hNM)
  let e : L ≃ₗ[ℤ] N := LinearEquiv.ofInjective g ginj

  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hφx : ((φ ⟨x, hxL⟩ : M) : F) ≠ 0 := by
    intro h0
    apply hx0
    have h1 : φ ⟨x, hxL⟩ = φ 0 := by
      rw [map_zero]
      exact Subtype.ext h0
    exact congrArg Subtype.val (hφ h1)
  have hNne : N ≠ ⊥ := by
    intro h0
    apply hφx
    have hmem : g ⟨x, hxL⟩ ∈ N := LinearMap.mem_range_self g _
    rw [h0, Submodule.mem_bot] at hmem
    exact hmem
  have hCpos : 0 < C := by
    have h1 : ‖((φ ⟨x, hxL⟩ : M) : F)‖ ≤ C * ‖x‖ := hC ⟨x, hxL⟩
    have h2 : 0 < ‖((φ ⟨x, hxL⟩ : M) : F)‖ := norm_pos_iff.mpr hφx
    have h3 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h3.le]
  have h1 : slope N ≤ muMax M := h F M N hM hNM hNne

  set r := Module.finrank ℤ L with hr_def
  have hrkL : rk L = r := rfl
  have hrkN : rk N = r := by
    show Module.finrank ℤ N = Module.finrank ℤ L
    exact e.finrank_eq.symm
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hrpos : 0 < r := Module.finrank_pos

  let b := Module.finBasis ℤ L
  have hcL : covol L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det :=
    covol_eq_gram E L (Fin r) b
  have hcN : covol N = Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det :=
    covol_eq_gram F N (Fin r) (b.map e)
  have hint : ∀ n : Fin r → ℤ,
      ‖∑ i, (n i : ℝ) • ((φ (b i) : M) : F)‖ ≤ C * ‖∑ i, (n i : ℝ) • (b i : E)‖ := by
    intro n
    have h2 := hC (∑ i, n i • b i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h2
    simpa only [Int.cast_smul_eq_zsmul] using h2
  have hreal := norm_sum_smul_le_of_int (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hint
  have hdet := gram_det_le E F (Fin r) (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hreal
  have hle : covol N ≤ C ^ r * covol L := by
    rw [hcN, hcL]
    calc Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin r)) *
            (Matrix.gram ℝ (fun i => (b i : E))).det) := Real.sqrt_le_sqrt hdet
      _ = C ^ r * Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
        rw [Fintype.card_fin, show C ^ (2 * r) = (C ^ r) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hcLpos := covol_pos_of_discrete L
  have hcNpos := covol_pos_of_discrete N
  have hlog : Real.log (covol N) ≤ r * Real.log C + Real.log (covol L) := by
    have h2 := Real.log_le_log hcNpos hle
    rwa [Real.log_mul (by positivity) hcLpos.ne', Real.log_pow] at h2
  have hr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hs : slope L ≤ slope N + Real.log C := by
    unfold slope deg
    rw [hrkL, hrkN, div_add' _ _ _ hr.ne', div_le_div_iff_of_pos_right hr]
    nlinarith
  linarith

end Formalism.F
end
end

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
section
open Module Submodule

noncomputable section

namespace Formalism.F

universe u

private theorem finrank_int_eq_finrank_span_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (span ℝ (L : Set E)) := by

  let V := span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L' ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : L' => (⟨((x : V) : E), x.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨Submodule.span_span_coe_preimage⟩
  exact φ.finrank_eq.symm.trans (ZLattice.rank ℝ L')

theorem linearIndependent_coe_basis' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (e i : E)) := by
  have hspanZ : span ℤ (Set.range fun i => (e i : E)) = L := by
    have : (Set.range fun i => (e i : E)) = L.subtype '' Set.range e := Set.range_comp _ _
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  have hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR, ← finrank_int_eq_finrank_span_real L,
    Module.finrank_eq_card_basis e]

theorem gram_intMatrix_eq_map {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem slopesBdd_of (hG : GramDetLe.{u, 0, 0}) : SlopesBdd.{u} := by
  intro E _ _ _ L hL
  haveI := hL
  let e := Module.finBasis ℤ L
  have he : LinearIndependent ℝ (fun i => (e i : E)) := linearIndependent_coe_basis' L e

  let S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, WithLp.ofLp x i • (e i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h0 := Fintype.linearIndependent_iff.mp he (fun i => WithLp.ofLp x i) hx
    have h1 : WithLp.ofLp x = 0 := funext h0
    simpa using congrArg (WithLp.toLp 2) h1
  obtain ⟨K, hK0, hK⟩ := S.exists_antilipschitzWith hSinj
  have hKpos : (0 : ℝ) < K := hK0
  refine ⟨Real.log K, ?_⟩
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL
  let f := Module.finBasis ℤ N
  let M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ :=
    fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M i j : ℝ) • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm
  let w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) :=
    fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))
  have hSw : ∀ j, S (w j) = (f j : E) := by
    intro j
    rw [hfj j]
    simp [S, w]
  have hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ,
      ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖ := by
    intro c
    have h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hSw]
    rw [← h1]
    simpa [dist_eq_norm] using hK.le_mul_dist (∑ j, c j • w j) 0
  have hdet := hG E (EuclideanSpace ℝ (Fin (Module.finrank ℤ L))) (Fin (Module.finrank ℤ N))
    (fun j => (f j : E)) w K hcomp
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det, Fintype.card_fin] at hdet

  have hwli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h2 : ∑ j, c j • (f j : E) = 0 := by
      rw [← map_zero S, ← hc]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hSw]
    exact Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis' N f) c h2
  have hwpos : 0 < (Matrix.gram ℝ w).det := (Matrix.posDef_gram_of_linearIndependent hwli).det_pos
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det] at hwpos
  have hd1 : (1 : ℝ) ≤ (Int.castRingHom ℝ) (M.transpose * M).det := by
    simp only [eq_intCast] at hwpos ⊢
    have : (0 : ℤ) < (M.transpose * M).det := by exact_mod_cast hwpos
    exact_mod_cast this
  have hk : (0 : ℝ) < (Module.finrank ℤ N : ℝ) := by
    haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
    exact_mod_cast Module.finrank_pos
  set g := (Matrix.gram ℝ (fun j => (f j : E))).det with hg
  have hgK : 1 ≤ (K : ℝ) ^ (2 * Module.finrank ℤ N) * g := hd1.trans hdet
  have hgpos : 0 < g := by
    by_contra hneg
    push_neg at hneg
    have : (K : ℝ) ^ (2 * Module.finrank ℤ N) * g ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hlog : -(2 * (Module.finrank ℤ N : ℝ)) * Real.log K ≤ Real.log g := by
    have h1 : Real.log 1 ≤ Real.log ((K : ℝ) ^ (2 * Module.finrank ℤ N) * g) :=
      Real.log_le_log one_pos hgK
    rw [Real.log_one, Real.log_mul (by positivity) hgpos.ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  have hcov : covol N = Real.sqrt g := by rw [covol, dite_eq_left hN]
  show -Real.log (covol N) / (Module.finrank ℤ N : ℝ) ≤ Real.log K
  rw [hcov, Real.log_sqrt hgpos.le, div_le_iff₀ hk]
  nlinarith

end Formalism.F
end
end

