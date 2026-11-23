module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModelWeightSizeSpreadBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

noncomputable section

namespace GlobalTheory.RunIn.WtSize

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_cm {M : Type} [AddCommMonoid M] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (g : (E →+* ℂ) → M) :
    ∑ τ : X.Ψ, (g τ.1 + g (ComplexEmbedding.conjugate τ.1)) = ∑ τ, g τ := by
  classical
  have hs : ∑ τ : X.Ψ, (g τ.1 + g (ComplexEmbedding.conjugate τ.1)) =
      ∑ τ ∈ X.Ψ, (g τ + g (ComplexEmbedding.conjugate τ)) :=
    Finset.sum_coe_sort X.Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ))
  rw [hs, Finset.sum_add_distrib, ← Finset.sum_add_sum_compl X.Ψ g]
  congr 1
  refine Finset.sum_nbij' (fun τ => ComplexEmbedding.conjugate τ) (fun τ => ComplexEmbedding.conjugate τ)
    ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    simpa [Finset.mem_compl] using (X.cmType τ).1 hτ
  · intro τ hτ
    have h1 : τ ∉ X.Ψ := by simpa [Finset.mem_compl] using hτ
    by_contra h2
    exact h1 ((X.cmType τ).2 (by simpa using h2))
  · intro τ _
    simp
  · intro τ _
    simp
  · intro τ _
    rfl

theorem two_mul_card_cm {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    2 * Fintype.card X.Ψ = Module.finrank ℚ E := by
  have h := sum_cm X (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [← NumberField.Embeddings.card E ℂ, ← h]
  ring

theorem sum_row_le (r p0 : ℕ) (hp : p0 ≤ r) (u v : ℕ → ℕ) :
    ∑ j : Fin r, (if p0 ≤ (j : ℕ) then u ((j : ℕ) - p0) else v (p0 - 1 - (j : ℕ))) ≤
      ∑ i ∈ Finset.range r, u i + ∑ i ∈ Finset.range r, v i := by
  classical
  rw [Finset.sum_ite]
  gcongr
  · calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => p0 ≤ (j : ℕ)), u ((j : ℕ) - p0)
          = ∑ i ∈ Finset.image (fun j : Fin r => (j : ℕ) - p0) (Finset.univ.filter (fun j : Fin r => p0 ≤ (j : ℕ))), u i := by
            refine (Finset.sum_image ?_).symm
            intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            dsimp only at hab
            exact Fin.ext (by omega)
      _ ≤ ∑ i ∈ Finset.range r, u i := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            obtain ⟨j, _, rfl⟩ := hi
            simp only [Finset.mem_range]
            have := j.isLt
            omega
  · calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => ¬ p0 ≤ (j : ℕ)), v (p0 - 1 - (j : ℕ))
          = ∑ i ∈ Finset.image (fun j : Fin r => p0 - 1 - (j : ℕ)) (Finset.univ.filter (fun j : Fin r => ¬ p0 ≤ (j : ℕ))), v i := by
            refine (Finset.sum_image ?_).symm
            intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            dsimp only at hab
            exact Fin.ext (by omega)
      _ ≤ ∑ i ∈ Finset.range r, v i := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            obtain ⟨j, hj, rfl⟩ := hi
            simp only [Finset.mem_range]
            have := j.isLt
            omega

theorem spread_le {r : ℕ} (x b : Fin r → ℝ) (m : ℝ) (hm : 0 ≤ m) (hb : ∀ i, 0 ≤ b i)
    (hx : ∀ i, |x i| = b i + m) : (⨆ i, x i) - ⨅ i, x i ≤ ∑ i, b i + 2 * m := by
  classical
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · rw [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
    have : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => hb i)
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := x)
    rw [← hi, ← hj]
    have hxi : x i ≤ b i + m := (le_abs_self _).trans (hx i).le
    have hxj : -(b j + m) ≤ x j := by
      have := neg_abs_le (x j)
      rw [hx j] at this
      exact this
    by_cases hij : i = j
    · subst hij
      have : 0 ≤ ∑ k, b k := Finset.sum_nonneg (fun k _ => hb k)
      linarith
    · have hpair : b i + b j ≤ ∑ k, b k := by
        rw [← Finset.sum_pair hij]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hb k)
      linarith

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_bijective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Bijective (relab (E := E) c σ) := by
  have hinj : Function.Injective (relab (E := E) c σ) := by
    intro τ τ' hττ'
    unfold relab embF at hττ'
    ext x
    have h1 := congrArg (fun f : E →+* ℂ => f x) hττ'
    simp only [RingHom.comp_apply] at h1
    exact congrArg Subtype.val (σ.injective h1)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

private lemma entry_abs (p0 j s t h : ℕ) :
    |(((if p0 ≤ j then (s : ℤ) + (h : ℤ) else -(t : ℤ) - (h : ℤ) : ℤ)) : ℝ)| =
      (((if p0 ≤ j then s else t : ℕ)) : ℝ) + (h : ℝ) := by
  split_ifs with hj
  · push_cast
    exact abs_of_nonneg (by positivity)
  · push_cast
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) h])]
    ring

theorem laU_bounds (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) (B : ℕ)
    (hB : ∑ τ, ∑ i ∈ Finset.range r, a (τ, i) ≤ B) :
    (∑ τ, (U.X k).spread (laU U a n k) τ) ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * n ∧
      (∑ τ, ∑ i, |((laU U a n k τ i : ℤ) : ℝ)|) ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * r * n / 2 := by
  unfold laU
  have hp : (U.X k).p0 ≤ r := (U.X k).p0_le
  have hbij := relab_bijective (E := E) c σ
  have hm2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    exact_mod_cast this
  have htot : ∑ τ : (U.X k).Ψ, (∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ.1, i) + ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) (conjEmb τ.1), i)) ≤ B := by
    have hinvb : Function.Bijective (Function.invFun (relab (E := E) c σ)) :=
      ⟨(Function.rightInverse_invFun hbij.2).injective, (Function.leftInverse_invFun hbij.1).surjective⟩
    calc _ = ∑ τ : (U.X k).Ψ, ((fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) τ.1 +
            (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) (ComplexEmbedding.conjugate τ.1)) := rfl
      _ = ∑ τ, (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) τ :=
          sum_cm (U.X k) (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i))
      _ = ∑ τ, ∑ i ∈ Finset.range r, a (τ, i) := Fintype.sum_bijective _ hinvb _ _ (fun _ => rfl)
      _ ≤ B := hB
  have hsum : ∑ τ : (U.X k).Ψ, ∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) ≤ (B : ℝ) := by
    calc _ ≤ ∑ τ : (U.X k).Ψ, (((∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ.1, i) + ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) (conjEmb τ.1), i)) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro τ _
          rw [← Nat.cast_sum]
          exact_mod_cast sum_row_le r (U.X k).p0 hp (fun i => a (Function.invFun (relab c σ) τ.1, i))
            (fun i => a (Function.invFun (relab c σ) (conjEmb τ.1), i))
      _ ≤ (B : ℝ) := by
          rw [← Nat.cast_sum]
          exact_mod_cast htot
  have h0 : (0 : ℝ) ≤ Fintype.card (U.X k).Ψ := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  constructor
  · calc _ ≤ ∑ τ : (U.X k).Ψ, (∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + 2 * ((n / 2 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro τ _
          unfold ReciprocityTheory.ChartRestriction.G.FD.Data.spread
          exact spread_le _ _ _ (by positivity) (fun j => by positivity) (fun j => entry_abs _ _ _ _ _)
      _ ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          nlinarith [hsum, mul_le_mul_of_nonneg_left hm2 h0]
  · calc _ = ∑ τ : (U.X k).Ψ, ∑ j : Fin r, ((((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro τ _
          apply Finset.sum_congr rfl
          intro j _
          exact entry_abs _ _ _ _ _
      _ ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * r * n / 2 := by
          have e : ∀ τ : (U.X k).Ψ, ∑ j : Fin r, ((((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)) = ∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + r * ((n / 2 : ℕ) : ℝ) := by
            intro τ
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_congr rfl (fun τ _ => e τ), Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          nlinarith [hsum, mul_le_mul_of_nonneg_left hm2 (mul_nonneg h0 hr0)]

theorem sum_wtA_le {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (m : ℕ) :
    ∑ τ, ∑ i ∈ Finset.range m, wtA w (τ, i) ≤ WeightAlgebra.DF w := by
  classical
  unfold wtA WeightAlgebra.DF WeightAlgebra.degP ext0
  have key : ∀ (q : ℕ) (g : Fin q → ℕ),
      ∑ i ∈ Finset.range m, (if h : i < q then g ⟨i, h⟩ else 0) ≤ ∑ i, g i := by
    intro q g
    calc _ ≤ ∑ i ∈ Finset.range q, (if h : i < q then g ⟨i, h⟩ else 0) := by
          apply Finset.sum_le_sum_of_ne_zero
          intro i _ hi
          rw [Finset.mem_range]
          by_contra hc
          exact hi (dif_neg hc)
      _ = ∑ i, g i := by
          rw [Finset.sum_range]
          simp
  rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_le_sum (fun t _ => ?_)
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact add_le_add (key _ _) (key _ _)

theorem laU_wtA_size : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * w.n ∧ (∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * D.R.r * w.n / 2 := by
  intro D T h j hj w σ hσ k
  have h2 := two_mul_card_cm ((T.U j σ).X k)
  have h3 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have h4 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.der.finrank_E
    rw [h4]
    simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  have hc : (Fintype.card ((T.U j σ).X k).Ψ : ℝ) = D.R.f := by
    have : Fintype.card ((T.U j σ).X k).Ψ = D.R.f := by omega
    exact_mod_cast this
  have hb := laU_bounds (T.U j σ) (wtA w) w.n k (WeightAlgebra.DF w) (sum_wtA_le w _)
  rw [hc] at hb
  exact hb

end GlobalTheory.RunIn.WtSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValue

theorem finite_levelQuotient {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem map_weighted_finsum {F S₁ S₂ T Q : Type} [Field F] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra F S₁] [Algebra F S₂] [Algebra F T] [Finite Q] (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T)
    (k : F) (w : Q → F) (A₁ : Q → S₁) (A₂ : Q → S₂) (h : ∀ q, ψ₁ (A₁ q) = ψ₂ (A₂ q)) :
    ψ₁ (algebraMap F S₁ k * ∑ᶠ q, algebraMap F S₁ (w q) * A₁ q) =
      ψ₂ (algebraMap F S₂ k * ∑ᶠ q, algebraMap F S₂ (w q) * A₂ q) := by
  haveI := Fintype.ofFinite Q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [finsum_eq_sum_of_fintype, map_mul, map_sum, AlgHom.commutes, h]

end GlobalTheory.ShortValue

namespace GlobalTheory

theorem shortThetaValue_existsUnique_natural : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, ShortValAt Xo c nab w Λ β N P y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 → ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hN a P hP w β
  haveI := ShortValue.finite_levelQuotient Dw l
  have cmp := _root_.GlobalTheory.ShortCompare.shortSum_eq_of_witnesses hL hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hP
  have nat : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 →
      ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
    intro S T _ _ _ _ φ y0 y hφ v0 v h0 h1
    obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := h0
    obtain ⟨S2, _, _, φ2, y2, z2, tp2, F2, hf2, hm2, hz2, hg2, ht2, hu2, e2⟩ := h1
    obtain ⟨U, _, _, ψ2, ψ1, hc, -, hinj⟩ :=
      exists_faithfullyFlat_pushout c.F S S2 S1 (φ2.comp φ) φ1 hf1
    have key := cmp S y0 S1 φ1 y1 z1 tp1 F1 S2 (φ2.comp φ) y2 z2 tp2 F2 hm1
      (FramedBaseChange.trans φ φ2 hφ hm2) hz1 hg1 ht1 hu1 hz2 hg2 ht2 hu2 U ψ1 ψ2 hc.symm
    have hinj2 : Function.Injective φ2 := hf2.injective
    apply hinj2
    apply hinj
    have e0 : ψ2 (φ2 (φ v0)) = ψ1 (φ1 v0) := AlgHom.congr_fun hc v0
    rw [e0, e1, e2]
    exact ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _ key
  refine ⟨fun S _ _ y => ?_, nat⟩
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1⟩ :=
    _root_.GlobalTheory.exists_cover_shortVal_data hL E H Dw l Xo c n Λ N hU hT hN S y
  obtain ⟨v, hv, -⟩ := existsUnique_preimage_of_faithfullyFlat c.F S S1 φ1 hf1
    (algebraMap c.F S1 (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S1 (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) *
          ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b))
    (fun T _ _ ψ1 ψ2 hc => ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _
      (cmp S y S1 φ1 y1 z1 tp1 F1 S1 φ1 y1 z1 tp1 F1 hm1 hm1 hz1 hg1 ht1 hu1 hz1 hg1 ht1 hu1 T ψ1 ψ2 hc))
  have hv' : ShortValAt Xo c nab w Λ β N P y v :=
    ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, hv⟩
  exact ⟨v, hv', fun v' h' => nat S S (AlgHom.id c.F S) y y (FramedBaseChange.refl y) v' v h' hv'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SingularMetricFreeDivisorInvariantLowerBound
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FreeDivMetric

open GlobalTheory.Up GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}


open Classical in
noncomputable def Wfree (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) *
    ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
    ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ)

theorem Wfree_of_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X G x)) *
      ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  unfold Wfree
  rw [if_pos hx]

theorem Wfree_of_notMem {x : Frame X.Ψ r} (hx : x ∉ X.dom) : Wfree Xa Fl G n x = 0 := by
  unfold Wfree
  rw [if_neg hx]

private lemma sum_norm_sq_pos_of_exists_ne_zero {N : ℕ} {a : Fin N → ℂ} (h : ∃ k, a k ≠ 0) : 0 < ∑ k, ‖a k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := h
  exact Finset.sum_pos' (fun i _ => by positivity) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hk) 2⟩

theorem Wfree_eq_exp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hs : ∃ k, Fl.s k x ≠ 0) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-(phla X G x +
      (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)))) := by
  have hA : 0 < ∑ k, ‖Xa.w k x‖ ^ 2 := sum_norm_sq_pos_of_exists_ne_zero (Xa.w_nz x hx)
  have hB : 0 < ∑ k, ‖Fl.s k x‖ ^ 2 := sum_norm_sq_pos_of_exists_ne_zero hs
  have key : Real.exp (-(phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))) =
      Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Wfree_of_mem Xa Fl G n hx, key,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hA.le _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hB]

theorem Wfree_eq_pnorm {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  have hc : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _
  have key : Real.exp (-phla X G x) = Real.exp (-phla X (G + n • Xa.L) x) *
      Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ)) * Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2)) := by
    rw [GlobalTheory.Up.phla_add_nsmul hx, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Wfree_of_mem Xa Fl G n hx, hw, hs, ENNReal.ofReal_mul hc.le, ENNReal.ofReal_mul hc.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_rpow_of_pos hc, ENNReal.ofReal_rpow_of_pos hc, key,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hc.le _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

private lemma isBddSec_of_mem_SSgt {la : Wt X.Ψ r} {c : ℝ} {P : Frame X.Ψ r → ℂ} (h : P ∈ X.SSgt la c) :
    X.IsBddSec la P := h.1.1

theorem measurable_Wfree : Measurable (Wfree Xa Fl G n) := by
  have hw : ∀ k, ContinuousOn (Xa.w k) X.dom := fun k => (isBddSec_of_mem_SSgt (Xa.w_van k)).1.1.continuousOn
  have hs : ∀ k, ContinuousOn (Fl.s k) X.dom := fun k => (isBddSec_of_mem_SSgt (Fl.s_van k)).1.1.continuousOn
  have ha : ContinuousOn (fun x => Real.exp (-phla X G x)) X.dom :=
    Real.continuous_exp.comp_continuousOn (IW.phla_contOn X G).neg
  have hA : ContinuousOn (fun x => ∑ k, ‖Xa.w k x‖ ^ 2) X.dom :=
    continuousOn_finsetSum _ fun k _ => ((hw k).norm).pow 2
  have hB : ContinuousOn (fun x => ∑ k, ‖Fl.s k x‖ ^ 2) X.dom :=
    continuousOn_finsetSum _ fun k _ => ((hs k).norm).pow 2
  have e : Wfree Xa Fl G n = fun x =>
      X.dom.indicator (fun x => ENNReal.ofReal (Real.exp (-phla X G x))) x *
        X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2)) x ^ (-(1 / 2 : ℝ)) *
        X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2)) x ^ (-((n : ℝ) - 1 / 2)) := by
    funext x
    by_cases hx : x ∈ X.dom
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact Wfree_of_mem Xa Fl G n hx
    · rw [Set.indicator_of_notMem hx, zero_mul, zero_mul]
      exact Wfree_of_notMem Xa Fl G n hx
  rw [e]
  exact ((GlobalTheory.Up.DivMetricPf.measurable_cut ha).mul
    ((GlobalTheory.Up.DivMetricPf.measurable_cut hA).pow_const _)).mul
    ((GlobalTheory.Up.DivMetricPf.measurable_cut hB).pow_const _)

theorem Wfree_rmul (hN : NfacRmulStatement (E := E)) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    Wfree Xa Fl G n (rmul x b) =
      Wfree Xa Fl G n x / ENNReal.ofReal (‖bchar (G + n • Xa.L) b‖ ^ 2) := by
  have hxb : rmul x b ∈ X.dom := OntoS.dom_rmul X hx hb
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hx hb
  have hs : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hx hb
  have h1 := GlobalTheory.Up.DivMetricPf.exp_neg_phla hxb (G + n • Xa.L)
  have h2 := GlobalTheory.Up.DivMetricPf.exp_neg_phla hx (G + n • Xa.L)
  have h3 := hN r X (G + n • Xa.L) x hx b hb
  have hn0 : X.nfac (G + n • Xa.L) (rmul x b) ≠ 0 := by
    intro h
    have hp := Real.exp_pos (-phla X (G + n • Xa.L) (rmul x b))
    rw [h1, h] at hp
    norm_num at hp
  have hc : ‖bchar (G + n • Xa.L) b‖ ≠ 0 := by
    intro h
    rw [h, inv_zero, zero_mul] at h3
    exact hn0 h3
  have hc2 : 0 < ‖bchar (G + n • Xa.L) b‖ ^ 2 := by positivity
  have hph : Real.exp (-phla X (G + n • Xa.L) (rmul x b)) =
      Real.exp (-phla X (G + n • Xa.L) x) / ‖bchar (G + n • Xa.L) b‖ ^ 2 := by
    rw [h1, h2, h3]
    field_simp
  rw [Wfree_eq_pnorm Xa Fl G n hxb, Wfree_eq_pnorm Xa Fl G n hx]
  simp only [hw, hs]
  rw [hph, ENNReal.ofReal_div_of_pos hc2]
  simp only [div_eq_mul_inv]
  ring

theorem Wfree_lact (hN : NfacLactStatement (E := E)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Wfree Xa Fl G n (lact γ x) = Wfree Xa Fl G n x := by
  have hxg : lact γ x ∈ X.dom := OntoS.dom_lact X hγ hx
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hγ hx
  have hs : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hγ hx
  have hph : Real.exp (-phla X (G + n • Xa.L) (lact γ x)) = Real.exp (-phla X (G + n • Xa.L) x) := by
    rw [GlobalTheory.Up.DivMetricPf.exp_neg_phla hxg, GlobalTheory.Up.DivMetricPf.exp_neg_phla hx, hN r X _ γ hγ x hx]
  rw [Wfree_eq_pnorm Xa Fl G n hxg, Wfree_eq_pnorm Xa Fl G n hx]
  simp only [hw, hs, hph]

theorem Wfree_lower (hn : 1 ≤ n) : WLower X (G + n • Xa.L) (Wfree Xa Fl G n) := by
  obtain ⟨C, hC, hCw⟩ := GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Xa.w_van k)
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Fl.s_van k)
  have ht : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)),
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hD _), fun x hx => ?_⟩
  have e1 := GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hC (hCw x hx) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e2 := GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hD (hDs x hx) ht
  rw [Wfree_eq_pnorm Xa Fl G n hx]
  calc ENNReal.ofReal (C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)) * Real.exp (-phla X (G + n • Xa.L) x))
      = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) * ENNReal.ofReal (C ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (D ^ (-((n : ℝ) - 1 / 2))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hC.le _))]
        congr 1
        ring
    _ ≤ _ := by gcongr

theorem freeDivMetric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → IsMetricW X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ WLower X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ ∀ x ∈ X.dom, (∃ k, Fl.s k x ≠ 0) → (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) x = ENNReal.ofReal (Real.exp (-(fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) x)) := by
  intro E _ _ _ r X Xa Fl G n hn
  have hR := GlobalTheory.NormFactor.nfacRmul_holds (E := E)
  have hL := GlobalTheory.NormFactor.nfacLact_holds (E := E)
  exact ⟨⟨measurable_Wfree Xa Fl G n, fun x hx b hb => Wfree_rmul Xa Fl G n hR hx hb,
    fun γ hγ x hx => Wfree_lact Xa Fl G n hL hγ hx⟩, Wfree_lower Xa Fl G n hn,
    fun x hx hs => Wfree_eq_exp Xa Fl G n hx hs⟩

end GlobalTheory.FreeDivMetric
end

