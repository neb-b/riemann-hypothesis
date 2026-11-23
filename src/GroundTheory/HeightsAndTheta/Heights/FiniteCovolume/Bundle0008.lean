module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantExists
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

theorem exists_posDef_mul_inv_mul_eq {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    ∃ P : Matrix n n ℂ, P.PosDef ∧ P * H⁻¹ * P = H := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set d : n → ℝ := hH.eigenvalues with hddef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    have h0 := hdet.ne_zero
    rw [hH.det_eq_prod_eigenvalues] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← hddef, hi]))
  have hinv : H⁻¹ = U * diagonal (fun i => (((d i)⁻¹ : ℝ) : ℂ)) * star U := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    have : (fun i => ((d i : ℝ) : ℂ) * (((d i)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hd i), Complex.ofReal_one]
    rw [this, diagonal_one, Matrix.one_mul, hUU']
  refine ⟨U * diagonal (fun i => ((|d i| : ℝ) : ℂ)) * star U, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|d i| : ℝ) : ℂ))).PosDef :=
      Matrix.posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (abs_pos.mpr (hd i))
    have hinj : Function.Injective U.vecMul := by
      intro x y hxy
      have := congrArg (fun z => z ᵥ* star U) hxy
      simpa only [vecMul_vecMul, hUU', vecMul_one] using this
    simpa only [star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same hinj
  · rw [hinv]
    conv_rhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
      Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc |d i| * (d i)⁻¹ * |d i| = |d i| * |d i| * (d i)⁻¹ := by ring
      _ = d i * d i * (d i)⁻¹ := by rw [abs_mul_abs_self]
      _ = d i := mul_inv_cancel_right₀ (hd i) _

section Spaces

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem MajorantExists.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : GramAtData.Statement h v) : MajorantExists.Statement h v := by
  choose P hP hPH using fun w => exists_posDef_mul_inv_mul_eq (h₁ w).1 (h₁ w).2
  exact ⟨⟨P, hP, hPH⟩⟩

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMinkowskiVolumeForm
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory Submodule

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem MinkowskiVolumeForm.proof : MinkowskiVolumeForm.Statement V d := by
  classical
  intro o b lam hlam hmin
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have hd : finrank ℝ V = d := Fact.out

  have hcomb : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨z, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hz : z ≠ 0 := by
      rintro rfl
      simp at hx0
    simpa [← Int.cast_smul_eq_zsmul ℝ] using hmin z hz
  have hdisc : DiscreteTopology (span ℤ (Set.range b)) :=
    DiscreteTopology.of_forall_le_norm hlam fun x hx => hcomb x x.2 (by simpa using hx)
  have hZ : LinearIndependent ℤ b := by
    rw [Fintype.linearIndependent_iff]
    intro z hz
    by_contra hne
    have hz' : z ≠ 0 := fun h => hne (fun i => by simp [h])
    have h1 := hmin z hz'
    have h2 : ∑ i, (z i : ℝ) • b i = 0 := by simpa [Int.cast_smul_eq_zsmul] using hz
    rw [h2, norm_zero] at h1
    linarith
  have hR : LinearIndependent ℝ b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc,
      Set.finrank, finrank_span_eq_card hZ]
  have hcard : Fintype.card (Fin d) = finrank ℝ V := by simp [hd]
  let B : Basis (Fin d) ℝ V := Basis.mk hR (hR.span_eq_top_of_card_eq_finrank' hcard).ge
  have hB : ⇑B = b := Basis.coe_mk _ _

  have hF : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |o.volumeForm b| := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B volume), ← o.measure_eq_volume,
      AlternatingMap.measure_parallelepiped, hB]

  let e : OrthonormalBasis (Fin d) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hd)
  set σ : ℝ := lam / Real.sqrt d with hσ
  have hσ0 : 0 ≤ σ := div_nonneg hlam.le (Real.sqrt_nonneg _)
  let φ : V →ₗ[ℝ] (Fin d → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap ∘ₗ e.repr.toLinearEquiv.toLinearMap
  let P : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ioo (-σ) σ
  let s : Set V := φ ⁻¹' P
  have hs_mem : ∀ v, v ∈ s ↔ ∀ i, |e.repr v i| < σ := by
    intro v
    simp only [s, P, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo, abs_lt]
    rfl
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [hs_mem] at hx ⊢
    intro i
    simpa using hx i
  have hconv : Convex ℝ s := (convex_pi fun _ _ => convex_Ioo _ _).linear_preimage φ
  have hvol : volume s = ENNReal.ofReal (2 * σ) ^ d := by
    have hmp : MeasurePreserving (fun v : V => WithLp.ofLp (e.repr v)) volume volume :=
      (PiLp.volume_preserving_ofLp (Fin d)).comp e.measurePreserving_repr
    rw [show s = (fun v : V => WithLp.ofLp (e.repr v)) ⁻¹' P from rfl,
      hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  by_contra hlt
  push Not at hlt
  have hlt' : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ V < volume s := by
    rw [hd]
    have h : ENNReal.ofReal (|o.volumeForm b| * 2 ^ d) < ENNReal.ofReal ((2 * σ) ^ d) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), mul_pow, mul_comm]
      exact mul_lt_mul_of_pos_left hlt (by positivity)
    rwa [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (mul_nonneg zero_le_two hσ0),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← hF, ← hvol] at h
  have hcount : Countable (span ℤ (Set.range B)).toAddSubgroup := by
    change Countable (span ℤ (Set.range B))
    infer_instance
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' B volume) hsymm hconv hlt'
  have hx0' : x ≠ 0 := by
    rintro rfl
    exact hx0 rfl
  have h1 : lam ≤ ‖x‖ := hcomb x (by rw [← hB]; exact hxL) hx0'
  have h2 : ‖x‖ < lam := by
    rw [hs_mem] at hxs
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exact absurd (@Subsingleton.elim _ (finrank_zero_iff.1 (hd.trans hd0)) x 0) hx0'
    · have hσpos : 0 < σ := div_pos hlam (Real.sqrt_pos.2 (by exact_mod_cast hdpos))
      have hsq : (d : ℝ) * σ ^ 2 = lam ^ 2 := by
        rw [hσ, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        field_simp
      rw [← e.repr.norm_map, EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ i, ‖e.repr x i‖ ^ 2) < Real.sqrt (∑ _i : Fin d, σ ^ 2) := by
            apply Real.sqrt_lt_sqrt (by positivity)
            apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hdpos⟩⟩)
            intro i _
            rw [Real.norm_eq_abs, sq_lt_sq, abs_of_pos hσpos, abs_abs]
            exact hxs i
        _ = lam := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq,
              Real.sqrt_sq hlam.le]
  linarith

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PParabolicDecomposition
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ParabolicDecomposition.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : KTransitive.Statement ι) (h₂ : HermAtPlace.Statement h v)
    (h₃ : GramAtData.Statement h v) (h₄ : ArchInvariant.Statement h v)
    (h₅ : VecAtNeZero.Statement v) : ParabolicDecomposition.Statement h v := by
  intro M x₀ hx₀ hiso g
  have hz : ∀ w, vecAt v x₀ w ≠ 0 := h₅ x₀ hx₀
  have hzi : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← h₂, hiso, map_zero]
  have hzi' : ∀ w, star (invApply g (vecAt v x₀) w) ⬝ᵥ
      (gramAt h v w *ᵥ invApply g (vecAt v x₀) w) = 0 := fun w => by
    rw [h₄, hzi]

  have hginv : ∀ w, (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := fun w => rfl
  have hz' : ∀ w, invApply g (vecAt v x₀) w ≠ 0 := by
    intro w hw
    apply hz w
    have e : ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ invApply g (vecAt v x₀) w =
        vecAt v x₀ w := by
      rw [invApply, hginv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← e, hw, Matrix.mulVec_zero]
  have hmaj : ∀ w, IsMajorantOf (gramAt h v w) (M.P w) := fun w =>
    ⟨M.posDef w, (h₃ w).1, (h₃ w).2, M.siegel w⟩
  choose k hkH hkP c hc using fun w =>
    h₁ _ _ (hmaj w) _ _ (hz w) (hz' w) (hzi w) (hzi' w)
  have hkA : k ∈ archUnitary h v := (Subgroup.mem_pi _).2 fun w _ => hkH w
  set kk : archUnitary h v := ⟨k, hkA⟩ with hkk
  have hkS : kk ∈ M.stab := by
    rw [Majorant.stab, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_pi _).2 fun w _ => hkP w
  refine ⟨g * kk⁻¹, kk, hkS, by group, fun w => ⟨(c w)⁻¹, ?_⟩⟩
  have hcw : c w ≠ 0 := by
    intro h0
    apply hz' w
    have e := congrArg (fun y => (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at e
    exact e

  have hk : (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      (c w)⁻¹ • invApply g (vecAt v x₀) w := by
    have e := congrArg (fun y => (c w)⁻¹ • ((((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y)) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hcw, one_smul] at e
    exact e.symm
  have hp : (((g * kk⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) * (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := rfl
  rw [hp, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, invApply, hginv, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PPhaseOnMinus
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

noncomputable section

theorem PhaseOnMinus.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PhaseOnMinus.Statement ι := by
  intro H P hM c hc
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hHi : H⁻¹ * H = 1 := nonsing_inv_mul H hdet

  have hA2 : A * A = 1 := by
    simp only [hAdef, majInvolution]
    calc H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPHP, hHi]

  have hPA : P * A = H := by
    simp only [hAdef, majInvolution]; rw [← Matrix.mul_assoc, hPHP]

  have hAh : Aᴴ = P * H⁻¹ := by
    simp only [hAdef, majInvolution, conjTranspose_mul, conjTranspose_nonsing_inv,
      hH.eq, hP.isHermitian.eq]

  let Dm : ℂ → Matrix ι ι ℂ := fun a => ((1 + a) / 2) • (1 : Matrix ι ι ℂ) + ((1 - a) / 2) • A
  have hD : phaseOnMinus H P c = Dm c := by
    simp only [Dm, phaseOnMinus, ← hAdef]
    module
  have hDD : ∀ a b : ℂ, a * b = 1 → Dm a * Dm b = 1 := by
    intro a b hab
    simp only [Dm, add_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hA2]
    have e1 : (1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2) = 1 := by
      linear_combination (1 / 2 : ℂ) * hab
    have e2 : (1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2) = 0 := by
      linear_combination (-1 / 2 : ℂ) * hab
    calc _ = ((1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2)) • (1 : Matrix ι ι ℂ)
          + ((1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2)) • A := by module
      _ = 1 := by rw [e1, e2]; simp
  have hDA : ∀ a : ℂ, Dm a * A = A * Dm a := by
    intro a
    simp only [Dm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
      Matrix.mul_one]

  have hDP : (Dm c)ᴴ * P = P * Dm (star c) := by
    simp only [Dm, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hAh, add_mul,
      mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hPA]
    simp only [hPHP, star_div₀, star_add, star_sub, star_one]
    norm_num
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD, hDP, Matrix.mul_assoc, hDD _ _ hcc, Matrix.mul_one]
  · rw [hD, ← hPA, ← Matrix.mul_assoc, hDP, Matrix.mul_assoc, ← hDA c, ← Matrix.mul_assoc,
      Matrix.mul_assoc P, hDD _ _ hcc, Matrix.mul_one]
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PShortestVectorIndex
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [IsTotallyReal F] in
theorem ShortestVectorIndex.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LineIndexCoeffs.Statement (E := E) W) (h₂ : LineCoeffsFG.Statement (E := E) W)
    (h₃ : WeightedLenSmul.Statement h v) (h₄ : WeightPos.Statement h v)
    (h₅ : WeightedIndexBound.Statement E) : ShortestVectorIndex.Statement h v := by
  intro M r ha D La g x hD hx hx0 hmin
  set c : InfinitePlace E → ℝ := fun w =>
    (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re with hc
  have hcpos : ∀ w, 0 < c w := h₄ M g x hx0
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]

  have hlen : ∀ a : E, M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a
    rw [h₃ M g x a]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hlen1 : M.len (invApply g (vecAt v x)) ^ 2 = ∑ w, c w := by
    have := hlen 1
    simpa using this
  have hsub : intSubgroup E ≤ lineCoeffs La x := by
    rintro _ ⟨a, rfl⟩
    exact hD.isLattice.smul_mem a x hx
  have hfg : (lineCoeffs La x).FG := h₂ La x hD.isLattice.fg hx0
  have hmin' : ∀ a ∈ lineCoeffs La x, a ≠ 0 →
      ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a haA ha0
    have hax : a • x ∈ La := haA
    have hax0 : a • x ≠ 0 := smul_ne_zero ha0 hx0
    have hle := hmin (a • x) hax hax0
    rw [← hlen1, ← hlen a]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  obtain ⟨a, hali, habs⟩ := ha
  have ha' : ∃ b : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg, hali.comp _ (Fin.cast_injective hdeg), fun i σ => habs _ σ⟩
  have key := h₅ c hcpos (lineCoeffs La x) hsub hfg hmin' r ha'
  rw [h₁ La x hx0]
  rw [hdeg] at key
  push_cast at key
  exact key

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldOrbit
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal Pointwise

variable (G : Type*) [Group G]

theorem UnfoldOrbit.bijective_mul_out_inv {Γ Γ₀ : Subgroup G} (hle : Γ₀ ≤ Γ) :
    Function.Bijective (fun p : (Γ ⧸ Γ₀.subgroupOf Γ) × Γ₀ =>
      (⟨(p.2 : G) * ((Quotient.out p.1 : Γ) : G)⁻¹,
        Γ.mul_mem (hle p.2.2) (Γ.inv_mem (Quotient.out p.1).2)⟩ : Γ)) := by
  constructor
  · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have hmem : (Quotient.out q' : Γ)⁻¹ * Quotient.out q ∈ Γ₀.subgroupOf Γ := by
      rw [Subgroup.mem_subgroupOf]
      have key : (((Quotient.out q' : Γ)⁻¹ * Quotient.out q : Γ) : G) = (h' : G)⁻¹ * h := by
        rw [show (h' : G)⁻¹ * h = (h' : G)⁻¹ * ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) *
          ((Quotient.out q : Γ) : G) by group, heq]
        push_cast
        group
      rw [key]
      exact Γ₀.mul_mem (Γ₀.inv_mem h'.2) h.2
    have hq : q' = q := by
      rw [← QuotientGroup.out_eq' q', ← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hmem
    subst hq
    have hh : h = h' := Subtype.ext (mul_right_cancel heq)
    rw [hh]
  · intro γ
    have hmem := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk γ⁻¹ :
      Γ ⧸ Γ₀.subgroupOf Γ)).symm
    rw [Subgroup.mem_subgroupOf] at hmem
    refine ⟨⟨QuotientGroup.mk γ⁻¹, ⟨_, hmem⟩⟩, ?_⟩
    apply Subtype.ext
    simp

theorem UnfoldOrbit.proof [MeasurableSpace G] [MeasurableMul G] : UnfoldOrbit.Statement G := by
  intro μ _ Γ Γ₀ _ hle FD FD₀ hFD hFD₀ φ hφ hinv
  have : Countable Γ₀ := (Subgroup.inclusion_injective hle).countable
  have : Countable (Γ ⧸ Γ₀.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  rw [lintegral_tsum (f := fun (q : Γ ⧸ Γ₀.subgroupOf Γ) g => φ (((Quotient.out q : Γ) : G)⁻¹ * g))
      fun q => (hφ.comp (measurable_const_mul _)).aemeasurable,
    hFD.setLIntegral_eq_tsum φ FD₀,
    ← (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle)).tsum_eq,
    ENNReal.tsum_prod']
  refine tsum_congr fun q => ?_
  have h1 : ∫⁻ g in FD, φ (((Quotient.out q : Γ) : G)⁻¹ * g) ∂μ =
      ∫⁻ x in ((Quotient.out q : Γ) : G)⁻¹ • FD, φ x ∂μ := by
    rw [← Set.image_smul]
    exact (measurePreserving_mul_left μ _).setLIntegral_comp_emb (measurableEmbedding_mulLeft _) φ FD
  rw [h1, hFD₀.setLIntegral_eq_tsum' φ]
  refine tsum_congr fun h => ?_
  have hset : h • ((Quotient.out q : Γ) : G)⁻¹ • FD ∩ FD₀ =
      FD₀ ∩ (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle) (q, h)) • FD := by
    rw [Set.inter_comm]
    congr 1
    show (h : G) • ((Quotient.out q : Γ) : G)⁻¹ • FD = ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) • FD
    rw [smul_smul]
  rw [hset]
  exact lintegral_congr fun x => hinv _ (h⁻¹).2 x

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedSpaceDim
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField NumberField.InfinitePlace Module

theorem WeightedSpaceDim.proof (E : Type*) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    WeightedSpaceDim.Statement E := by
  unfold WeightedSpaceDim.Statement
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin,
    card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    IsTotallyComplex.finrank]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

