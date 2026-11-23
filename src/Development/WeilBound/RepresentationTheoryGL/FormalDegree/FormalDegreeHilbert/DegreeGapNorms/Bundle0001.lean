module

public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.DegreeGapNorms.DegPsi
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS

theorem degPsi : DegPsi := by
  intro n ε V _ _ _ Ψ H _ _ σ j C d m hC hj hΨ hd
  set b := stdOrthonormalBasis ℂ V with hb
  obtain ⟨hd0, hS⟩ := hd
  have hb1 : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
  have key : ∀ i l, Integrable (fun g : Formalism.REAL.UJ ε => ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2) m ∧
      ∫ g, ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 ∂m = 1 / d := by
    intro i l
    obtain ⟨hi, he⟩ := hS (j (b i)) (j (b l)) (j (b i)) (j (b l))
    have hpt : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.coefOn σ (j (b i)) (j (b l)) g * star (Formalism.MainNotions.S.coefOn σ (j (b i)) (j (b l)) g) =
        ((C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [Formalism.MainNotions.S.coefOn]
      rw [hΨ g (b i) (b l), norm_mul, Complex.norm_real, Real.norm_of_nonneg hC.le]
      push_cast; ring
    simp_rw [hpt] at hi he
    rw [integral_complex_ofReal, hj, hj, hb1, hb1] at he
    have he' : ∫ g, C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 ∂m = C * C / d := by
      apply Complex.ofReal_injective
      rw [he]; push_cast; ring
    have hi' : Integrable (fun g : Formalism.REAL.UJ ε => C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2) m := by
      refine hi.re.congr (ae_of_all _ fun g => ?_)
      simp only
      exact RCLike.ofReal_re _
    have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hC.ne'
    refine ⟨?_, ?_⟩
    · refine (hi'.const_mul (C ^ 2)⁻¹).congr (ae_of_all _ fun g => ?_)
      simp only
      field_simp
    · rw [integral_const_mul] at he'
      have hd' : d ≠ 0 := hd0.ne'
      field_simp at he' ⊢
      nlinarith [he']
  have hexp : ∀ g : Formalism.REAL.UJ ε, hsOp (Ψ (Formalism.MainNotions.S.umat g)) =
      ∑ i, ∑ l, ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 := by
    intro g
    unfold hsOp
    exact sum_congr rfl fun i _ => (b.sum_sq_norm_inner_right _).symm
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => hsOp (Ψ (Formalism.MainNotions.S.umat g))) m := by
    simp_rw [hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (key i l).1
  have hval : ∫ g, hsOp (Ψ (Formalism.MainNotions.S.umat g)) ∂m = (Module.finrank ℂ V : ℝ) ^ 2 / d := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun l _ => (key i l).1)]
    rw [sum_congr rfl fun i _ => integral_finsetSum _ fun l _ => (key i l).1]
    rw [sum_congr rfl fun i _ => sum_congr rfl fun l _ => (key i l).2]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun g => by unfold hsOp; positivity), hval]

end PositivityTheory.RgFd
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.DegreeGapNorms.FdAllOf
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem fdAll_of (hM : ModelDS) (hF : FdModel) : FdAll := by
  intro n ε lam hl H _ _ σ hσ
  obtain ⟨T⟩ := HW.kType_exists ε lam hl
  obtain ⟨μ, hμ⟩ := S7.exists_mu hl
  have hDS := (hM n ε lam T μ hl hμ).2
  have hd := hF n ε lam T μ hl hμ
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.DSUniq.ds_unique
    CompanionTheory.D.LK.hMultAlg CompanionTheory.D.LK.hKModExists CompanionTheory.D.LK.hOrthCyc
    n ε lam H _ σ (sigLam ε (PsiM T μ) T.w) hl hσ hDS
  have hc : ∀ (v w : H) (g : Formalism.REAL.UJ ε), Formalism.MainNotions.S.coefOn σ v w g =
      Formalism.MainNotions.S.coefOn (sigLam ε (PsiM T μ) T.w) (U v) (U w) g := by
    intro v w g
    simp only [Formalism.MainNotions.S.coefOn]
    rw [← hU _ g.2 v, LinearIsometryEquiv.inner_map_map]
  refine ⟨hd.1, fun v w v' w' => ?_⟩
  obtain ⟨h1, h2⟩ := hd.2 (U v) (U w) (U v') (U w')
  simp only [hc]
  refine ⟨h1, ?_⟩
  rw [h2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

end PositivityTheory.RgFd
end
end

