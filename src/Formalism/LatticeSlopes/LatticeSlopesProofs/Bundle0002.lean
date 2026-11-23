module

public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle0001
public import Formalism.LatticeSlopes.CovolAntiSameRank

@[expose] public section

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
section
open Module Submodule MeasureTheory

noncomputable section

namespace Formalism.F

theorem covol_eq_covolume' : CovolEqCovolume := by
  intro E _ _ _ _ _ L _ _
  classical
  rw [covol, dite_eq_left (inferInstance : DiscreteTopology L)]
  set b := Module.finBasis ℤ L with hb
  set bR : Basis (Fin (Module.finrank ℤ L)) ℝ E := b.ofZLatticeBasis ℝ L with hbR
  have hrank : Module.finrank ℝ E = Module.finrank ℤ L := (ZLattice.rank ℝ L).symm
  set o : OrthonormalBasis (Fin (Module.finrank ℤ L)) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hrank)
  set A := o.toBasis.toMatrix bR with hA

  have hgo : Matrix.gram ℝ (fun i => o.toBasis i) = 1 := by
    ext i j
    simp [Matrix.gram, Matrix.one_apply, orthonormal_iff_ite.mp o.orthonormal]
  have hv : (fun i => ((b i : L) : E)) = fun j => ∑ i, A i j • o.toBasis i := by
    funext j
    rw [hA, o.toBasis.sum_toMatrix_smul_self]
    exact (Basis.ofZLatticeBasis_apply ℝ L b j).symm
  have hg : Matrix.gram ℝ (fun i => ((b i : L) : E)) = A.transpose * A := by
    rw [hv, gram_sum_smul_eq_transpose_mul, hgo, Matrix.mul_one]
  have hdet : (Matrix.gram ℝ (fun i => ((b i : L) : E))).det = (o.toBasis.det bR) ^ 2 := by
    rw [hg, Matrix.det_mul, Matrix.det_transpose, Basis.det_apply, sq]

  have h1 : ZLattice.covolume L = (MeasureTheory.volume (ZSpan.fundamentalDomain bR)).toReal := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L MeasureTheory.volume
      (ZLattice.isAddFundamentalDomain b MeasureTheory.volume)]
    rfl
  have h2 := ZSpan.measure_fundamentalDomain bR MeasureTheory.volume o.toBasis
  have h3 : MeasureTheory.volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [MeasureTheory.measure_congr
      (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.volume),
      OrthonormalBasis.coe_toBasis, o.volume_parallelepiped]
  rw [hdet, Real.sqrt_sq_eq_abs, h1, h2, h3, mul_one, ENNReal.toReal_ofReal (abs_nonneg _)]

end Formalism.F
end
end

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
section
open Module Submodule

noncomputable section

namespace Formalism.F

theorem linearIndependent_coe_basis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical

  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L ≃ₗ[ℤ] L' :=
    { toFun := fun x => ⟨⟨x, Submodule.subset_span x.2⟩, x.2⟩
      invFun := fun y => ⟨((y : V) : E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective (f := fun y : L' => (⟨((y : V) : E), y.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (by
        intro a c h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show Submodule.span ℝ _ = Submodule.span ℝ (L : Set E)
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩⟩
  have hrank := ZLattice.rank ℝ L'
  have hLspan : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have h1 := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
    exact h1
  have key : Fintype.card ι = Module.finrank ℝ V := by
    rw [← hrank, ← φ.finrank_eq, Module.finrank_eq_card_basis b]
  rw [linearIndependent_iff_card_eq_finrank_span]
  show Fintype.card ι = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => (b i : E)))
  rw [← Submodule.span_span_of_tower ℤ ℝ, hLspan]
  exact key

theorem covol_pos' : CovolPos := by
  intro E _ _ _ L hL
  haveI := hL
  rw [covol_eq_gram E L (Fin (Module.finrank ℤ L)) (Module.finBasis ℤ L)]
  apply Real.sqrt_pos.2
  exact (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L _)).det_pos

theorem discreteTopology_span_singleton {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : v ≠ 0) :
    DiscreteTopology (span ℤ ({v} : Set E)) := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hs : ({0} : Set (span ℤ ({v} : Set E))) = Metric.ball 0 ‖v‖ := by
    ext ⟨x, hx⟩
    rw [Set.mem_singleton_iff, mem_ball_zero_iff]
    constructor
    · intro h
      rw [h, norm_zero]
      exact hv'
    · intro h
      obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have hn : ‖n • v‖ < ‖v‖ := h
      rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs] at hn
      have h1 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left hv').1 hn
      have hn0 : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h1)
      subst hn0
      exact Subtype.ext (zero_smul ℤ v)
  rw [hs]
  exact Metric.isOpen_ball

theorem covol_basic_properties : CovolBasic := by
  intro E _ _ _
  refine ⟨?_, ?_⟩
  · haveI : DiscreteTopology (⊥ : Submodule ℤ E) := inferInstance
    rw [covol_eq_gram E ⊥ (Fin 0) (Module.Basis.empty _)]
    simp [Matrix.det_isEmpty]
  · intro v hv
    haveI := discreteTopology_span_singleton hv
    have hli : LinearIndependent ℤ (fun _ : Unit => v) := by
      have hR : LinearIndependent ℝ (fun _ : Unit => v) := by
        rw [linearIndependent_unique_iff]
        first
          | exact hv
          | (intro r hr; exact (smul_eq_zero.1 hr).resolve_right hv)
      first
        | exact hR.restrict_scalars' ℤ
        | exact hR.restrict_scalars (by intro a c h; simpa using h)
    have hr : span ℤ (Set.range fun _ : Unit => v) = span ℤ ({v} : Set E) := by
      rw [Set.range_const]
    let b : Basis Unit ℤ (span ℤ ({v} : Set E)) := (Basis.span hli).map (LinearEquiv.ofEq _ _ hr)
    have hb : (fun i => (b i : E)) = fun _ => v := by
      funext i
      simp [b, Basis.span_apply]
    rw [covol_eq_gram E _ Unit b, hb, Matrix.det_unique, Matrix.gram_apply,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end Formalism.F
end
end

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained
section
open Module

namespace Formalism.F

universe u

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem att_rk_pos {N : Submodule ℤ E} [DiscreteTopology N] (hN : N ≠ ⊥) : 0 < rk N := by
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  exact Module.finrank_pos

theorem att_rk_le {L N : Submodule ℤ E} [DiscreteTopology L] (h : N ≤ L) : rk N ≤ rk L :=
  LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion h) (Submodule.inclusion_injective h)

end

end Formalism.F
end

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
section
open Module Submodule MeasureTheory

noncomputable section

namespace Formalism.F

universe u

theorem covol_eq_of_linearEquiv_inner {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [DiscreteTopology M]
    (f : L ≃ₗ[ℤ] M)
    (hf : ∀ x y : L, inner ℝ ((f x : M) : F) ((f y : M) : F) = inner ℝ (x : E) (y : E)) :
    covol M = covol L := by
  classical
  let b := Module.finBasis ℤ L
  rw [covol_eq_gram F M (Fin (Module.finrank ℤ L)) (b.map f), covol_eq_gram E L _ b]
  congr 2
  ext i j
  simp only [Matrix.gram, Matrix.of_apply, Basis.map_apply]
  exact hf (b i) (b j)

theorem exists_short_vector_of_isZLattice (hC : CovolEqCovolume.{u}) {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ W) :
    ∃ x ∈ L, x ≠ 0 ∧
      ‖x‖ ≤ Real.sqrt (finrank ℝ W : ℝ) * covol L ^ ((1 : ℝ) / (finrank ℝ W : ℝ)) := by
  classical
  set n := finrank ℝ W with hn_def
  let b := Module.finBasis ℤ L
  have hfund := ZLattice.isAddFundamentalDomain b MeasureTheory.volume
  have hcov : ZLattice.covolume L = MeasureTheory.volume.real
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L _ hfund
  have hFfin : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hc : 0 < covol L := by
    rw [hC W L]
    exact ZLattice.covolume_pos L _
  have hF : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
      ENNReal.ofReal (covol L) := by
    rw [hC W L, hcov, MeasureTheory.measureReal_def, ENNReal.ofReal_toReal hFfin]

  set t := covol L ^ ((1 : ℝ) / (n : ℝ)) with ht_def
  have ht : 0 ≤ t := Real.rpow_nonneg hc.le _
  have htn : t ^ n = covol L := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  let o := stdOrthonormalBasis ℝ W
  set S : Set W := {x | ∀ i, |o.repr x i| ≤ t} with hS
  have hnorm : ∀ x ∈ S, ‖x‖ ≤ Real.sqrt (n : ℝ) * t := by
    intro x hx
    rw [← o.repr.norm_map x, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖o.repr x i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin n, t ^ 2) := by
          apply Real.sqrt_le_sqrt
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
      _ = Real.sqrt (n : ℝ) * t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ht]
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx i
    simpa [map_neg] using hx i
  have hconv : Convex ℝ S := by
    intro x hx y hy a c ha hc hac i
    simp only [map_add (f := _), map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc |a * o.repr x i + c * o.repr y i| ≤ |a * o.repr x i| + |c * o.repr y i| := abs_add_le _ _
      _ = a * |o.repr x i| + c * |o.repr y i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]
      _ ≤ a * t + c * t := by
          gcongr
          · exact hx i
          · exact hy i
      _ = t := by rw [← add_mul, hac, one_mul]
  have hclosed : IsClosed S := by
    rw [hS, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hcpt : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
    refine (Metric.isBounded_closedBall (x := (0 : W)) (r := Real.sqrt (n : ℝ) * t)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm x hx
  have hSeq : S = (WithLp.ofLp ∘ o.measurableEquiv) ⁻¹'
      Set.Icc (fun _ => -t) (fun _ => t) := by
    ext x
    simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, Set.mem_Icc,
      Pi.le_def, abs_le, forall_and]
    rfl
  have hvolS : MeasureTheory.volume S = ENNReal.ofReal (t - -t) ^ n := by
    rw [hSeq, ((PiLp.volume_preserving_ofLp (Fin n)).comp
      o.measurePreserving_measurableEquiv).measure_preimage measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmeas : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) *
      2 ^ n ≤ MeasureTheory.volume S := by
    rw [hF, hvolS, ← ENNReal.ofReal_pow (by linarith),
      show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by simp,
      ← ENNReal.ofReal_mul hc.le]
    apply le_of_eq
    congr 1
    rw [show t - -t = 2 * t by ring, mul_pow, htn, mul_comm]
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos hn
  haveI hLc : Countable L := b.equivFun.injective.countable
  haveI : Countable L.toAddSubgroup := hLc
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (L := L.toAddSubgroup) hfund hsymm hconv hcpt hmeas
  refine ⟨(x : W), x.2, ?_, hnorm _ hxS⟩
  intro h0
  exact hx0 (Subtype.ext h0)

theorem shortVector_of (hC : CovolEqCovolume.{u}) : ShortVector.{u} := by
  intro E _ _ _ L hL hne
  classical
  haveI : DiscreteTopology L := hL

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L ≃ₗ[ℤ] L₀ :=
    { toFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      invFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e.symm) ?_ e.symm.injective
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
  letI : MeasurableSpace (Submodule.span ℝ (L : Set E)) := borel _
  haveI : BorelSpace (Submodule.span ℝ (L : Set E)) := ⟨rfl⟩
  have hcov : covol L₀ = covol L :=
    covol_eq_of_linearEquiv_inner L L₀ e (fun _ _ => rfl)
  have hrk : finrank ℝ (Submodule.span ℝ (L : Set E)) = rk L := by
    rw [← ZLattice.rank ℝ L₀]
    exact e.finrank_eq.symm
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set E)) := by
    rw [hrk]
    exact Module.finrank_pos
  obtain ⟨x, hx, hx0, hxn⟩ := exists_short_vector_of_isZLattice hC L₀ hpos
  refine ⟨(x : E), hx, ?_, ?_⟩
  · intro h0
    exact hx0 (Subtype.ext h0)
  · rw [hrk, hcov] at hxn
    exact hxn

end Formalism.F
end
end

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
section
namespace Formalism.F

universe u

theorem slopeLeMuMax_of (h : SlopesBdd.{u}) : SlopeLeMuMax.{u} := by
  intro E _ _ _ L N hL hNL hN
  exact le_csSup (h E L hL) (show slope N ∈ slopes L from ⟨N, hNL, hN, rfl⟩)

theorem muMaxMono_of (h : SlopesBdd.{u}) : MuMaxMono.{u} := by
  intro E _ _ _ L N hL hNL hN
  apply csSup_le_csSup (h E L hL) (show (slopes N).Nonempty from ⟨slope N, N, le_rfl, hN, rfl⟩)
  rintro t ⟨M, hMN, hM, rfl⟩
  exact ⟨M, hMN.trans hNL, hM, rfl⟩

end Formalism.F
end

