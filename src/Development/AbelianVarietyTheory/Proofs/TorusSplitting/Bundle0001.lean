module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBasisSpanEqOfDiscrete
section
open Module Submodule

namespace GlobalTheory

theorem exists_basis_span_eq_of_discrete {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology M] (hM : span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤) :
    ∃ b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), span ℤ (Set.range b) = M := by
  have : IsZLattice ℝ M := ⟨hM⟩
  have := ZLattice.module_free ℝ M
  have := ZLattice.module_finite ℝ M
  let b1 := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = N := by
    rw [← finrank_eq_card_basis b1]
    simp
  refine ⟨b1.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Basis.range_reindex]
  exact Basis.ofZLatticeBasis_span ℝ M _

theorem exists_inner_dual_basis {N : ℕ} (b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    ∃ d : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), ∀ j y, inner ℝ (d j) y = b.repr y j := by
  let w : Fin N → EuclideanSpace ℝ (Fin N) := fun j =>
    (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap (b.coord j))
  have hw : ∀ j y, inner ℝ (w j) y = b.repr y j := fun j y => by
    simp [w, InnerProductSpace.toDual_symm_apply]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun x => inner ℝ x (b i)) hg
    simpa [sum_inner, real_inner_smul_left, hw, Finsupp.single_apply] using this
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp), fun j y => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', hw]

theorem transference_discrete_lattice :
    ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))), DiscreteTopology M →
      Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ → ∀ lam : ℝ, 0 < lam →
      (∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → z ≠ 0 →
        lam ≤ ‖z‖) →
      ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧
        ∀ j, ‖v j‖ ≤ (N : ℝ) ^ 2 / lam := by
  intro N M _ hM lam hlam hmin
  obtain ⟨b, rfl⟩ := exists_basis_span_eq_of_discrete M hM
  obtain ⟨d, hd⟩ := exists_inner_dual_basis b
  obtain ⟨y, hli, hint, hy⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual d lam hlam (by
    intro x hx hx0
    refine hmin x (fun y hy => ?_) hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    obtain ⟨e, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hy
    refine ⟨∑ j, c j * e j, ?_⟩
    simp [sum_inner, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hd,
      Finsupp.single_apply])
  refine ⟨y, fun i => ?_, hli, hy⟩
  rw [b.mem_span_iff_repr_mem ℤ]
  intro j
  obtain ⟨m, hm⟩ := hint i j
  exact ⟨m, by rw [← hd, real_inner_comm, hm]; simp⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsShortIntegralRationalBasis
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem exists_short_integral_rational_basis :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
      (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
      ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) →
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
      ∃ ω : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun j => (ω j : E)) ∧
        ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ omStar (E := E)) := by
  intro hex E _ _ _
  classical
  obtain ⟨n, ω, hωB, hsp⟩ := hex E
  have htop : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ := by
    rw [eq_top_iff, ← (NumberField.integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [NumberField.integralBasis_apply]
    exact hsp _
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range fun j => (ω j : E))
  have hbfin : b.Finite := hbli.setFinite
  have := hbfin.fintype
  have hcard : Fintype.card b = Module.finrank ℚ E := by
    have h := finrank_span_eq_card hbli
    rw [Subtype.range_coe, hbspan, htop, finrank_top] at h
    rw [h]
  let e : Fin (Module.finrank ℚ E) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ x : b, ∃ j, (ω j : E) = x := fun x => hbS x.2
  choose idx hidx using hmem
  refine ⟨fun i => ω (idx (e i)), ?_, fun i τ => hωB _ τ⟩
  have : (fun i => ((ω (idx (e i)) : 𝓞 E) : E)) = (fun x : b => (x : E)) ∘ e := by
    funext i; simp [hidx]
  rw [this]
  exact (linearIndependent_equiv e).mpr hbli

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.GaussTailOfCardLe
section
open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem gaussTail_of_card_le : Ext.GaussianTailBound := by
  intro ι h g R0 hR0 hg hh hcard
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = R0 ^ 2 / 16 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; positivity
  have ht' : 2 * (g : ℝ) + 1 ≤ t := by rw [ht_def]; linarith

  have key := GlobalTheory.summable_exp_neg_of_card_le (fun i => h i ^ 2 / 16) (t := t) (C := 9 ^ g)
    (fun i => by
      have h1 := hh i
      have h2 : R0 ^ 2 ≤ h i ^ 2 := by nlinarith
      rw [ht_def]
      linarith)
    (fun s u htu hs => by
      have hu0 : 0 < u := lt_of_lt_of_le ht htu
      obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 4 * Real.sqrt u := ⟨_, rfl⟩
      have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
      have hR2 : R ^ 2 = 16 * u := by rw [hR, mul_pow, hsq]; norm_num
      have hRnn : 0 ≤ R := by rw [hR]; positivity

      have hle : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 16 * u → x ≤ R := fun x hx hx2 => by
        nlinarith
      have hR0R : R0 ≤ R := hle R0 hR0.le (by rw [ht_def] at htu; linarith)
      have hsS : ∀ i ∈ s, h i ≤ R := fun i hi => by
        have h3 := hs i hi
        exact hle (h i) (hR0.le.trans (hh i)) (by linarith)
      refine (hcard R hR0R s hsS).trans ?_
      have hpow : (3 * R / R0) ^ (2 * g) = 9 ^ g * (u / t) ^ g := by
        rw [pow_mul, ← mul_pow]
        congr 1
        rw [div_pow, mul_pow, hR2, ht_def]
        field_simp
        ring
      rw [hpow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)

      have hx : u / t ≤ Real.exp (u / t - 1) := by
        have := Real.add_one_le_exp (u / t - 1)
        linarith
      have hy : u - t = t * (u / t - 1) := by field_simp
      have hy0 : 0 ≤ u / t - 1 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith
      calc (u / t) ^ g ≤ Real.exp (u / t - 1) ^ g := by gcongr
        _ = Real.exp (g * (u / t - 1)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((u - t) / 2) := by
          apply Real.exp_le_exp.mpr
          rw [hy]
          nlinarith [mul_le_mul_of_nonneg_right ht' hy0])
  have e : ∀ i, -(h i) ^ 2 / 16 = -(h i ^ 2 / 16) := fun i => by ring
  simp only [e]
  refine ⟨key.1, key.2.trans_eq ?_⟩
  rw [ht_def, neg_div]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NearestPlaneRounding
section
open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem nearestPlane_rounding : Ext.NearestPlane := by
  intro V _ _ n v _ x hx
  obtain ⟨w, hw, hle⟩ := exists_int_comb_norm_sub_sq_le n v hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hw
  refine ⟨c, ?_⟩
  have hsum : ∑ i, ((c i : ℤ) : ℝ) • v i = ∑ i, c i • v i := by
    simp only [Int.cast_smul_eq_zsmul]
  rw [hsum]
  linarith

end GlobalTheory
end

