module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.HaarUp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.HaarRightStatement
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def capIdx (k r : ℕ) (i : Fin (k + 2 * r + 1)) : Fin (2 * r + k + 1) := Fin.cast (by omega) i

def coefL {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w : H) (ξ : Vp) (g : Mat k r) (m : H) : Vp :=
  per P μW μN ψ π (coefX σ x₀ w m) ξ g

def PerEquivStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), IsBData z c u π μW μN →
    ∀ (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r), ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r,
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ (h * m * x) =
        Formalism.MainNotions.S.psiGen k r z c m • π h (per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x)

theorem perEquiv : PerEquivStatement := by
  intro k r u z c Vp _ _ _ π μW μN P hB F ξ x h hh m hm
  exact EvaluationEquivalence.sInt_equiv hB (fun g => F (P * g * P⁻¹)) ξ x hh hm

def FrameLawStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h →
    ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ (x₀ : Mat k r) (w : V) (ξ : Vp) (g : Mat k r), x₀ ∈ UJset ε → g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      ∃ (g₀ : Mat k r) (Dk : Fin k → Fin k → Module.End ℂ Vp)
        (ψ' : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ),
        Formalism.MainNotions.S.IsFrameW k r z g₀ ∧
        (∀ a b, Capelli.blk k r a < Capelli.blk k r b → ∀ m ∈ genSub E V,
          coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g
              ((frameE (g₀⁻¹ * g * P⁻¹) E (capIdx k r a) (capIdx k r b) m : D) : H) =
            ψ' a b • coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g ((m : D) : H)) ∧
        (∀ a b, Capelli.blk k r a < Capelli.blk k r b → ¬ Capelli.IsSimplePair k r a b → ψ' a b = 0) ∧
        (0 < r → Capelli.kappa k r ψ' ≠ 0) ∧
        (∀ i j, ∀ m ∈ genSub E V,
          coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g
              ((frameE (g₀⁻¹ * g * P⁻¹) E (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) m :
                D) : H) =
            Dk i j (coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g ((m : D) : H))) ∧
        ∀ (x : ℂ) (ζ : Vp), Capelli.capelliC Dk x ζ =
          (∏ j : Fin k, (x + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) • ζ

theorem frameLaw : FrameLawStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD _ _ _ hμ hcoef hp hq hgap hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ g hx₀ hg
  obtain ⟨hq0, hneed⟩ := gapNeed k r ε h hp hq hgap
  have hdd := S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hneed hq0 hμ
  have hb := CurveContinuity.per_gap hgap
  have hh0 : 0 ≤ h := by
    have h1 := hgap.1
    have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2)
      (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith
  have ha0 : 0 ≤ aExp ε h := div_nonneg hh0 (by positivity)
  have hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ ((w : D) : H) (aExp ε h) (m : H) :=
    fun m hm => tmC_good_genSub hσ hD hμ hcoef ha0 (fun wd v₁ v₂ => hdd wd v₁ v₂) hx₀ w hm
  have hT := hB.2.1
  obtain ⟨g₀, hg₀, hρ⟩ := hB.2.2.2.1
  obtain ⟨dρ, hdρ, hcap⟩ := EvaluationEquivalence.exists_derived _ hρ
  set l : D → Vp := fun m => coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g (m : H)
    with hl
  have hact : ∀ X : Mat k r, ∀ m ∈ genSub E V, actM E X m ∈ genSub E V := fun X m hm => by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
      (Submodule.mem_sInf.mpr fun S hS => hS.2 a b _ (Submodule.mem_sInf.mp hm S hS))
  let Λ : Mat k r → Module.End ℂ D := fun Z => actM E ((g * P⁻¹)⁻¹ * (g₀ * Z * g₀⁻¹) * (g * P⁻¹))
  have hΛ : ∀ Y1 Y2 : Mat k r, ∀ m ∈ genSub E V,
      l (Λ (Y1 + Complex.I • Y2) m) = l (Λ Y1 m) + Complex.I • l (Λ Y2 m) := fun Y1 Y2 m hm => by
    have e : Λ (Y1 + Complex.I • Y2) m = Λ Y1 m + Complex.I • Λ Y2 m := by
      simp only [Λ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, actM,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
        LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [e]
    exact EvaluationEquivalence.per_lin hP hB hg hb ξ (hgood _ (hact _ m hm)) (hgood _ (hact _ m hm)) _
  have hfr : ∀ i j, frameE (g₀⁻¹ * g * P⁻¹) E i j = Λ (Matrix.single i j 1) := fun i j => by
    have e : (g * P⁻¹)⁻¹ * (g₀ * Matrix.single i j 1 * g₀⁻¹) * (g * P⁻¹) =
        (g₀⁻¹ * g * P⁻¹)⁻¹ * Matrix.single i j 1 * (g₀⁻¹ * g * P⁻¹) := by
      rw [Matrix.mul_assoc g₀⁻¹, Matrix.mul_inv_rev g₀⁻¹,
        Matrix.nonsing_inv_nonsing_inv _ (TransportGeo.uh_det hg₀.1)]
      simp only [Matrix.mul_assoc]
    simp only [Λ, e, frameE, actM]
    generalize g₀⁻¹ * g * P⁻¹ = Q
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  have hder : ∀ Y : Mat k r, Yᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * Y = 0 → ∀ m ∈ genSub E V,
      HasDerivAt (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ ((w : D) : H) (m : H)) ξ
        (g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹ * g)) (l (Λ Y m)) 0 := fun Y hY m hm => by
    have := EvaluationEquivalence.per_deriv hσ hD hx₀ hP hB hg hb ξ (EvaluationEquivalence.conj_lie hg₀.1 hY) m (hgood m hm)
      (hgood _ (hact _ m hm))
    simp only [EvaluationEquivalence.exp_conj_frame hg₀.1] at this
    exact this
  have h1W : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UWset k r z := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z).one_mem
  have h1N : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).one_mem
  have hπ := hcTypeW_uRep k r z u Vp π hB.1 hT hB.2.2.2.1
  have hN : ∀ Y : Mat k r, Y ∈ Base.N.levF (Base.levB k r) 0 →
      Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r = -Y → ∀ m ∈ genSub E V,
      l (Λ Y m) = (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) • l m := fun Y h1 h2 m hm => by
    obtain ⟨hY, hf⟩ := EvaluationEquivalence.lieN_facts c hg₀ hT h1 h2
    refine (hder Y hY m hm).unique ?_
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ))))
        (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const
        (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) (x := (0 : ℝ))).cexp
    refine (h3.smul_const (l m)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have h4 := perEquiv k r u z c Vp π μW μN P hB (coefX σ x₀ ((w : D) : H) (m : H)) ξ g 1 h1W _ (hf t).1
    rw [Matrix.one_mul, (hf t).2, hπ.1.1] at h4
    exact h4
  have hW : ∀ A : Matrix (Fin k) (Fin k) ℂ, Aᴴ = -A → ∀ m ∈ genSub E V,
      l (Λ (EvaluationEquivalence.emb0 k r A) m) = dρ A (l m) := fun A hA m hm => by
    refine (hder _ (EvaluationEquivalence.block_embedding_skew_hermitian hA) m hm).unique ?_
    refine (hdρ A hA (l m)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have hu : NormedSpace.exp ((t : ℂ) • A) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
        conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal, smul_neg,
        ← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • A)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have h4 := perEquiv k r u z c Vp π μW μN P hB (coefX σ x₀ ((w : D) : H) (m : H)) ξ g _
      (EvaluationEquivalence.frame_mem_UW hg₀ hT hu) 1 h1N
    have h5 : Formalism.MainNotions.S.psiGen k r z c (1 : Mat k r) = 1 := by
      have h6 := Mult1.S0.A.psiGen_mul hB.1 c h1N h1N
      have h7 : Formalism.MainNotions.S.psiGen k r z c (1 : Mat k r) ≠ 0 := Complex.exp_ne_zero _
      rw [Matrix.one_mul] at h6
      exact (mul_right_eq_self₀.mp h6.symm).resolve_right h7
    rw [Matrix.mul_one, h5, one_smul] at h4
    simp only []
    rw [← map_smul, EvaluationEquivalence.exp_embed]
    exact h4
  refine ⟨g₀, fun i j => dρ (Matrix.single i j 1),
    fun a b => EvaluationEquivalence.psiC z c (Matrix.single (capIdx k r a) (capIdx k r b) 1), hg₀,
    fun a b hab m hm => ?_, fun a b _ hs => EvaluationEquivalence.psiC_zero z c hs, fun _ => ?_, fun i j m hm => ?_, hcap⟩
  · set Z : Mat k r := Matrix.single (capIdx k r a) (capIdx k r b) 1 with hZ
    have hZ1 : Z ∈ Base.N.levF (Base.levB k r) 0 := fun i j hij => by
      rw [hZ, Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      have h8 : Base.levB k r (capIdx k r a) < Base.levB k r (capIdx k r b) := hab
      omega
    have hZ2 : Formalism.QuantumDeterminants.Hpk k r * Zᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Base.N.levF (Base.levB k r) 0 :=
      EvaluationEquivalence.st_mem hZ1
    obtain ⟨p1, p2, p3⟩ := EvaluationEquivalence.parts Z
    have m1 : ∀ s t : ℂ, s • (Z + t • (Formalism.QuantumDeterminants.Hpk k r * Zᴴ * Formalism.QuantumDeterminants.Hpk k r)) ∈
        Base.N.levF (Base.levB k r) 0 := fun s t i j hij => by
      simp only [Matrix.smul_apply, Matrix.add_apply, hZ1 i j hij, hZ2 i j hij, smul_zero, add_zero]
    show l (frameE _ E _ _ m) = _ • l m
    rw [hfr, ← hZ]
    conv_lhs => rw [p3]
    rw [hΛ _ _ m hm, hN _ (m1 _ _) p1 m hm, hN _ (m1 _ _) p2 m hm, smul_smul, ← add_smul,
      EvaluationEquivalence.psiC_parts]
    rfl
  · refine Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b _ => ?_
    split_ifs with hs
    · exact EvaluationEquivalence.psiC_ne hB.2.2.1 hT hs
    · exact one_ne_zero
  · set A : Matrix (Fin k) (Fin k) ℂ := Matrix.single i j 1 with hA
    have e1 : A = (1 / 2 : ℂ) • (A - Aᴴ) + Complex.I • ((-Complex.I / 2) • (A + Aᴴ)) := by
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      linear_combination (A a b + Aᴴ a b) / 2 * Complex.I_mul_I
    have s1 : ((1 / 2 : ℂ) • (A - Aᴴ))ᴴ = -((1 / 2 : ℂ) • (A - Aᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← smul_neg, neg_sub]; simp
    have s2 : ((-Complex.I / 2) • (A + Aᴴ))ᴴ = -((-Complex.I / 2) • (A + Aᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm, ← neg_smul]
      congr 1; simp; ring
    show l (frameE _ E _ _ m) = dρ A (l m)
    have e2 : (Matrix.single (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) 1 : Mat k r) =
        EvaluationEquivalence.emb0 k r A := (EvaluationEquivalence.block_embedding_single i j).symm
    rw [hfr, e2]
    conv_lhs => rw [e1, map_add (f := _), map_smul _ Complex.I]
    rw [hΛ _ _ m hm, hW _ s1 m hm, hW _ s2 m hm]
    conv_rhs => rw [e1, map_add (f := _), map_smul _ Complex.I]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ProductBoundThreeFactors
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

def finKer {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T' : S7.KType ε Λ)
    (μ' : Fin (2 * r + k + 1) → ℤ) (v₁ v₂ : T'.V) (P : Mat k r) (x : Mat k r) (y : Mat k r)
    (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : ℂ :=
  ⟪v₂, S7.PsiM T' μ' (y⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) v₁⟫_ℂ

theorem finB_frob_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ frob g := Real.sqrt_nonneg _

theorem product_bound_three_factors (A B X p1 p2 Φ C0 C1 V : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hV : 0 ≤ V) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (h1 : A ≤ C0 * p1) (h2 : B ≤ C1 * V * p2) (h3 : p1 * p2 ≤ Φ) :
    A * (B * X) ≤ C0 * C1 * V * X * Φ := by
  have e1 : A * (B * X) ≤ (C0 * p1) * ((C1 * V * p2) * X) :=
    mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hX) (mul_nonneg hB hX) (by positivity)
  have e2 : (C0 * p1) * ((C1 * V * p2) * X) = C0 * C1 * V * X * (p1 * p2) := by ring
  have e3 : C0 * C1 * V * X * (p1 * p2) ≤ C0 * C1 * V * X * Φ :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

theorem finFub_int' (hIS : S0.IntSStatement) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ)
    (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r) (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN)
    (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ)
    (hμ : S7.IsMu lam' μ') (v₁ v₂ : T'.V) (ξ : Vp) (F : Mat k r → ℂ) (C : ℝ)
    (hFc : ContinuousOn F (UJset ε)) (hFb : ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      F (Formalism.MainNotions.S.umat q.1) • (finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2 •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
  obtain ⟨hz, hT, -, hπW, hHW, hHN⟩ := hB
  haveI : SigmaFinite μW := hHW.1
  haveI : SigmaFinite μN := hHN.1
  obtain ⟨hq0, hh, hmax⟩ := finB_gap hgap
  set a := aExp ε h with ha
  set β := a - 1 with hβ
  have hm1 := le_max_left (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
  have hm2 := le_max_right (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
  have hpos1 : (0 : ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
  have hβ0 : 0 ≤ β := by linarith
  have hIJ := finB_intJ ε hq0 (β / 2) (by linarith)
  have hIS' := finB_intS hIS hP z μW μN hz hT hHW hHN x hx (β / 4) (by unfold S0.bS S0.nS; linarith)
  obtain ⟨C', hC'⟩ := S0.DecDeriv.psiM_frob_dec ε lam' h T' μ' hlam hgl hh hq0 hμ
  have hπU := hcTypeW_uRep k r z u Vp π hz hT hπW
  have hPae := ae_mem_unitary_nilpotent_product z μW μN hHW hHN
  have hQae : ∀ᵐ q ∂((Formalism.REAL.muG ε).prod (μW.prod μN)),
      Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of q.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae hPae
  have hgpJ : ∀ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r →
        P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ ∈ UJset ε := fun p hp =>
    cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem (unitary_hermitian_form_mul_mem hp.1.1 hp.2.1) hx)

  have hof := S0.Dec.of_cont k r
  have hfc : Continuous (fun M : Mat k r => frob M) := by
    have : (fun M : Mat k r => frob M) = fun M => Formalism.FourierDecayAlt.B.gN M := funext finB_frob_eq
    rw [this]; exact S0.Dec.gN_cont k r
  have hgpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
    (continuous_const.matrix_mul (((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  have humc := continuous_unitary_matrix ε
  have hinvc : Continuous (fun y : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat y)⁻¹) := by
    have : (fun y : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat y)⁻¹) = fun y => Formalism.MainNotions.S.umat y⁻¹ :=
      funext fun y => (finB_umat_inv y).symm
    rw [this]; exact humc.comp continuous_inv
  have hmc : Continuous (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) :=
    (hinvc.comp continuous_fst).matrix_mul (hgpc.comp continuous_snd)

  have hT2m : Measurable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2))) :=
    ((hfc.comp (hgpc.comp continuous_snd)).measurable.pow_const _).mul ((hfc.comp hmc).measurable.pow_const _)
  have hT1 : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (Formalism.MainNotions.S.umat q.1) ^ (-(β / 2)) * frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := hIJ.mul_prod hIS'
  have hT2 : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2)))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
    rw [integrable_prod_iff' hT2m.aestronglyMeasurable]
    constructor
    · filter_upwards [hPae] with p hp
      obtain ⟨γ, hγ⟩ := exists_unitary_preimage ε (hgpJ p hp)
      have h1 := (finB_intJ_shift ε (β / 2) hIJ γ).1
      rw [hγ] at h1
      exact h1.const_mul _
    · refine (hIS'.mul_const (∫ y, frob (Formalism.MainNotions.S.umat y) ^ (-(β / 2)) ∂(Formalism.REAL.muG ε))).congr ?_
      filter_upwards [hPae] with p hp
      obtain ⟨γ, hγ⟩ := exists_unitary_preimage ε (hgpJ p hp)
      have h2 := (finB_intJ_shift ε (β / 2) hIJ γ).2
      rw [hγ] at h2
      have hnn : ∀ y : Formalism.REAL.UJ ε,
          ‖frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-(β / 4)) *
            frob ((Formalism.MainNotions.S.umat y)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) ^ (-(β / 2))‖ =
          frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-(β / 4)) *
            frob ((Formalism.MainNotions.S.umat y)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) ^ (-(β / 2)) := by
        intro y
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (finB_frob_nonneg _) _)
          (Real.rpow_nonneg (finB_frob_nonneg _) _))]
      simp only [hnn]
      rw [integral_const_mul, h2]
  have hΦ : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        (frob (Formalism.MainNotions.S.umat q.1) ^ (-(β / 2)) +
          frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2))))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
    refine (hT1.add hT2).congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]; ring
  set S3 : Set (Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) :=
    {q | Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹ ∈ UJset ε}
    with hS3
  have hScl : IsClosed S3 :=
    ((S0.Dec.UW_closed k r z).preimage (hof.comp (continuous_fst.comp continuous_snd))).inter
      ((finB_UJ_closed ε).preimage (hgpc.comp continuous_snd))
  have hSae : ∀ᵐ q ∂((Formalism.REAL.muG ε).prod (μW.prod μN)), q ∈ S3 := by
    filter_upwards [hQae] with q hq
    exact ⟨hq.1, hgpJ q.2 hq⟩
  have hE1 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      F (Formalism.MainNotions.S.umat q.1)) S3 :=
    (hFc.comp_continuous (humc.comp continuous_fst) (fun q => unitary_matrix_mem_set ε _)).continuousOn
  have hE2 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2) S3 := by
    unfold finKer
    have hmaps : Set.MapsTo (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) S3 {g | inUJ ε g} := by
      intro q hq
      show (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ∈ UJset ε
      rw [← finB_umat_inv]
      exact finB_UJ_mul (unitary_matrix_mem_set ε _) hq.2
    have h := (S7.psiM_continuousOn T' μ' hμ).comp hmc.continuousOn hmaps
    exact continuousOn_const.inner (h.clm_apply continuousOn_const)
  have hE3 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ) S3 := by
    show ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of q.2.2)) • π (Matrix.of q.2.1)⁻¹ ξ) S3
    have hq21 : Continuous (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => Matrix.of q.2.1) :=
      hof.comp (continuous_fst.comp continuous_snd)
    have hinvc' : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.1)⁻¹) S3 :=
      (((continuous_const.matrix_mul hq21.matrix_conjTranspose).matrix_mul continuous_const).continuousOn).congr
        (fun q hq => S0.DecA.inv_eq hq.1.1)
    have h := (hπU.2.2 ξ).comp hinvc' (fun q hq => S0.Dec.UW_inv_mem hq.1)
    exact (continuous_star.comp ((S0.Dec.psiGen_cont k r z c).comp
      (hof.comp (continuous_snd.comp continuous_snd)))).continuousOn.smul h
  refine Integrable.mono' (hΦ.const_mul (max C 0 * max C' 0 * (‖v₁‖ * ‖v₂‖) * ‖ξ‖)) ?_ ?_
  · rw [← Measure.restrict_eq_self_of_ae_mem hSae]
    exact (hE1.smul (hE2.smul hE3)).aestronglyMeasurable hScl.measurableSet
  filter_upwards [hQae] with q hq
  have hY := unitary_matrix_mem_set ε q.1
  have hg := hgpJ q.2 hq
  have hYg : (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ∈ UJset ε := by
    rw [← finB_umat_inv]; exact finB_UJ_mul (unitary_matrix_mem_set ε _) hg
  have hψ : ‖Formalism.MainNotions.S.psiGen k r z c (Matrix.of q.2.2)‖ = 1 := by
    unfold Formalism.MainNotions.S.psiGen; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hπ' : ‖π (Matrix.of q.2.1)⁻¹ ξ‖ = ‖ξ‖ := hπU.2.1 _ (S0.Dec.UW_inv_mem hq.1) ξ
  have hchi : ‖chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ‖ = ‖ξ‖ := by
    simp only [chiInv, norm_smul, norm_star, hψ, hπ', one_mul]
  have hF1 : ‖F (Formalism.MainNotions.S.umat q.1)‖ ≤ max C 0 * frob (Formalism.MainNotions.S.umat q.1) ^ (-β) := by
    have h1 := hFb _ hY
    rw [show 1 - a = -β by rw [hβ]; ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (finB_frob_nonneg _) _))
  have hK1 : ‖finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2‖ ≤ max C' 0 * (‖v₁‖ * ‖v₂‖) *
      frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) := by
    unfold finKer
    have h1 := hC' _ hYg
    have ea : h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) = a := rfl
    rw [ea] at h1
    have hle : frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-a) ≤
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le (finB_one_le hYg) (by rw [hβ]; linarith)
    have h2 : ‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹))‖ ≤
        max C' 0 * frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) :=
      h1.trans (mul_le_mul (le_max_left _ _) hle (Real.rpow_nonneg (finB_frob_nonneg _) _) (le_max_right _ _))
    calc _ ≤ ‖v₂‖ * ‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) v₁‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖v₂‖ * (‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹))‖ * ‖v₁‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖v₂‖ * ((max C' 0 * frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β)) * ‖v₁‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hpair := finB_pair β hβ0 hY hg hYg
  rw [norm_smul, norm_smul, hchi]
  exact product_bound_three_factors _ _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (le_max_right _ _)
    (le_max_right _ _) (by positivity) (Real.rpow_nonneg (finB_frob_nonneg _) _)
    (Real.rpow_nonneg (finB_frob_nonneg _) _) hF1 hK1 hpair

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

