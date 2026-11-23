module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0013
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefEmbed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaD
section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem coe_toL2_ae_eq_of_memLp {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ((toL2 ε F : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun g => F (Formalism.MainNotions.S.umat g) := by
  unfold toL2
  rw [dite_eq_left h]
  exact h.coeFn_toLp

theorem tfd_coef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool) (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) (ζ : Fin n → H) (c : Fin n)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ g =
      tfSgn ε c * ∑ d, tfCoef dual g c d * inner ℂ y (σ g (ζ d)) := by
  unfold coefMap
  rw [sum_eq_single c (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same, inner_smul_left,
    tf_tensGrp_apply, inner_sum]
  simp only [inner_smul_right]
  congr 1
  exact tf_star_sgn ε c

theorem tensor_functor_separation (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {y : H} (hy : y ∈ closGen E V) {ζ ζ' : Fin n → H} (hζ : ∀ c, ζ c ∈ closGen E V)
    (hζ' : ∀ c, ζ' c ∈ closGen E V)
    (hm : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hm' : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ' (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    inner ℂ (tfPh dual ε σ y ζ) (tfJ ε (tfPh dual ε σ y ζ')) = tfFormBH ε ζ ζ' * inner ℂ y y / (d : ℂ) := by
  set F : (Fin n → H) → Fin n → Formalism.REAL.UJ ε → ℂ := fun ζ c g =>
    coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ (Formalism.MainNotions.S.umat g) with hF
  have h1 : ∀ c, inner ℂ (tfPh dual ε σ y ζ c) (tfJ ε (tfPh dual ε σ y ζ') c) =
      ∫ g, tfSgn ε c * (star (F ζ c g) * F ζ' c g) ∂(Formalism.REAL.muG ε) := fun c => by
    rw [tfJ_apply, inner_smul_right, integral_const_mul, tfPh_apply, tfPh_apply, L2.inner_def]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [coe_toL2_ae_eq_of_memLp (hm c), coe_toL2_ae_eq_of_memLp (hm' c)] with g e1 e2
    rw [e1, e2, RCLike.inner_apply, mul_comm]
    rfl
  have hi : ∀ c, Integrable (fun g => tfSgn ε c * (star (F ζ c g) * F ζ' c g)) (Formalism.REAL.muG ε) :=
    fun c => ((hm c).star.integrable_mul (hm' c)).const_mul _
  have hs := fun c => tfClRep_schur hgap hσ hD hV hc hVK hd hy (hζ' c) hy (hζ c)
  rw [PiLp.inner_apply, sum_congr rfl fun c _ => h1 c, ← integral_finsetSum _ fun c _ => hi c]
  have h2 : ∀ g : Formalism.REAL.UJ ε, ∑ c, tfSgn ε c * (star (F ζ c g) * F ζ' c g) =
      ∑ c, tfSgn ε c * (inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' c)) *
        star (inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ c)))) := fun g => by
    have h3 := tf_jquad (tfCoef dual (Formalism.MainNotions.S.umat g)) (tfSgn ε) (tfCoef_orth dual (umat_mem_UJset ε g))
      (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ c))) (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' c)))
    refine Eq.trans (sum_congr rfl fun c _ => ?_) (h3.trans (sum_congr rfl fun c _ => by ring))
    simp only [hF, tfd_coef, star_mul', tf_star_sgn]
    linear_combination (tfSgn ε c * star (∑ d, tfCoef dual (Formalism.MainNotions.S.umat g) c d *
      inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ d))) * ∑ d, tfCoef dual (Formalism.MainNotions.S.umat g) c d *
        inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' d))) * tfSgn_mul_self ε c
  simp only [h2]
  rw [integral_finsetSum _ fun c _ => (hs c).1.const_mul _, tfFormBH, sum_mul, sum_div]
  refine sum_congr rfl fun c _ => ?_
  rw [integral_const_mul, (hs c).2]
  ring

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaE
section
noncomputable section

open Finset MeasureTheory
open Formalism.MainNotions.S (umat)

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

private theorem memLp_of_weighted_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (y : H)
    (hW : MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε)) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε) := by
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) :=
    continuous_const.inner ((hσ.2.2 y).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : Subsingleton (Formalism.REAL.UJ ε) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 (Fin.cast hn i)))⟩
    have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
    refine MemLp.of_bound hcont.aestronglyMeasurable (‖y‖ * ‖y‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖inner ℂ y (σ (umat g) y)‖ ≤ ‖y‖ * ‖σ (umat g) y‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
  · refine hW.of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have hs : 1 ≤ Real.sqrt (S7.hs (umat g)) :=
      Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact le_mul_of_one_le_left (norm_nonneg _) hs

private theorem memLp_coefficients {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : G → (H →L[ℂ] H)} (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)
    (hInv : MeasurePreserving (Inv.inv : G → G) μ μ)
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (y : H) (hy : y ≠ 0) (h0 : MemLp (fun g => inner ℂ y (ρ g y)) 2 μ) (v w : H) :
    MemLp (fun g => inner ℂ w (ρ g v)) 2 μ := by
  have hall (x : H) : MemLp (fun g => inner ℂ y (ρ g x)) 2 μ :=
    GraphTrick.memLp_of_ne hR hone hmul hiso hirr y y hy h0 x
  have hinv := ((hall w).comp_measurePreserving hInv).star
  have e : star ((fun g => inner ℂ y (ρ g w)) ∘ Inv.inv) = fun g => inner ℂ w (ρ g y) := by
    funext g
    have hs := GraphTrick.star_eq (ρ := ρ) hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e] at hinv
  exact GraphTrick.memLp_of_ne hR hone hmul hiso hirr w y hy hinv v

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ (w : H) (σ (umat g) (v : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  let ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (umat g)
  have hone : ρ 1 = 1 := by
    change tfClRep σ (closGen E V) 1 = 1
    exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    exact hU.1.2 (umat a) (umat_mem_UJset ε a) (umat b) (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 (umat g) (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  have hcoe : (fun g => inner ℂ y0 (ρ g y0)) = fun g => inner ℂ (y : H) (σ (umat g) (y : H)) := by
    funext g
    change inner ℂ (y : H) (↑(tfClRep σ (closGen E V) (umat g) y0) : H) = _
    rw [tfClRep_coe σ _ (hst (umat g) (umat_mem_UJset ε g))]
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    rw [hcoe]
    exact memLp_of_weighted_diagonal hσ (y : H) (hW y hyG y hyG)
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  exact memLp_coefficients (ρ := ρ) (MeasureTheory.measurePreserving_mul_right (Formalism.REAL.muG ε))
    (Measure.measurePreserving_inv (Formalism.REAL.muG ε)) hone hmul hiso hirr y0 hy0 h0

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaG
section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem tfg_gen {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (S : Submodule ℂ (Fin n → M))
    (hV : tensSub V ≤ S) (hS : ∀ a b, ∀ f ∈ S, tensF dual E a b f ∈ S) : tensSub (genSub E V) ≤ S := by
  let T : Submodule ℂ M := ⨅ c, S.comap (LinearMap.single ℂ (fun _ : Fin n => M) c)
  have hT : ∀ m, m ∈ T ↔ ∀ c, (Pi.single c m : Fin n → M) ∈ S := fun m => by simp [T, Submodule.mem_iInf]
  have hle : genSub E V ≤ T := sInf_le ⟨fun v hv => (hT v).2 fun c => hV (tset_mem.mpr fun d => by
      by_cases h : d = c
      · subst h; simpa using hv
      · simp [h]),
    fun a b m hm => (hT _).2 fun c => by
      have hm' := (hT m).1 hm
      cases dual
      · have e : (Pi.single c (E a b m) : Fin n → M) =
            tensF false E a b (Pi.single c m) - if b = c then Pi.single a m else 0 := by
          funext d
          simp only [tensF, cond_false, Pi.sub_apply, tensV_coord]
          by_cases h1 : d = c <;> by_cases h2 : d = a <;> by_cases h3 : b = c <;>
            simp_all
        rw [e]
        refine S.sub_mem (hS a b _ (hm' c)) ?_
        split_ifs
        · exact hm' a
        · exact S.zero_mem
      · have e : (Pi.single c (E a b m) : Fin n → M) =
            tensF true E a b (Pi.single c m) + if a = c then Pi.single b m else 0 := by
          funext d
          simp only [tensF, cond_true, Pi.add_apply, tensVd_coord]
          by_cases h1 : d = c <;> by_cases h2 : d = b <;> by_cases h3 : a = c <;>
            simp_all
        rw [e]
        refine S.add_mem (hS a b _ (hm' c)) ?_
        split_ifs
        · exact hm' b
        · exact S.zero_mem⟩
  intro f hf
  rw [← Finset.univ_sum_single f]
  exact S.sum_mem fun c _ => (hT _).1 (hle (tset_mem.mp hf c)) c

theorem tfg_real {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ X} (hU : IsInfUnitary ε E) {c : ℂ} {v : X}
    (h : casimir E v = c • v) : casimir E v = ((c.re : ℝ) : ℂ) • v := by
  by_cases hv : v = 0
  · simp [hv]
  have h1 : inner ℂ (casimir E v) v = inner ℂ v (casimir E v) := by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    have e1 := hU b a v (E b a v)
    have e2 := hU a b (E b a v) v
    have e3 : inner ℂ v (E a b (E b a v)) = starRingEnd ℂ (inner ℂ (E a b (E b a v)) v) :=
      (inner_conj_symm _ _).symm
    rw [e3, e2, map_mul, inner_conj_symm]
    congr 1
    unfold adjSign; split_ifs <;> simp
  rw [h, inner_smul_left, inner_smul_right] at h1
  have h2 := mul_right_cancel₀ (inner_self_ne_zero.mpr hv) h1
  rw [h, Complex.conj_eq_iff_re.mp h2]

theorem tf_closure_stable (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {y : D} (hy : y ∈ genSub E V) :
    ∀ g ∈ UJset ε, ∀ v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure,
      tfRdiag ε g v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure := by
  have hη : ∀ c, (Pi.single c (tfSgn ε c • y) : Fin n → D) ∈ tensSub (genSub E V) := fun c =>
    tset_mem.mpr fun d => by
      by_cases h : d = c
      · subst h; simpa using Submodule.smul_mem _ _ hy
      · simp [h]
  have hco : ∀ c, (fun d => (((Pi.single c (tfSgn ε c • y) : Fin n → D) d : D) : H)) =
      Pi.single c (tfSgn ε c • (y : H)) := fun c => funext fun d => by
    by_cases h : d = c
    · subst h; simp
    · simp [h]
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _ (hη c) f hf
  simp only [hco] at hce
  have hR := tfRdiag_isURepOn ε
  have hDR := isDerivedOn_smE hR
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        cases dual <;> simp [coefMap, tensGrp, inner_sum, inner_smul_right, mul_sum,
          mul_assoc, mul_left_comm, mul_comm]) }
  have hΦE : ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
      Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := fun a b f =>
    Subtype.ext (vectorL2_ext fun c => by
      refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
      refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
      exact (hce c f.1 f.2).2.1 a b g hg)
  let P' : Module.End ℂ (tensSub (n := n) (genSub E V)) := P.restrict hP.1
  let Ξ := Φ ∘ₗ P'
  have hΞE : ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Ξ f) =
      Ξ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := fun a b f => by
    refine (hΦE a b (P' f)).trans (congrArg Φ (Subtype.ext ?_))
    exact (hP.2.1 a b f.1 f.2).symm
  let W : Submodule ℂ (tensSub (n := n) (genSub E V)) := (tensSub V).comap (tensSub (genSub E V)).subtype
  have := hV.1
  have hVle : tensSub (n := n) V ≤ tensSub (genSub E V) := fun f hf =>
    tset_mem.mpr fun c => Submodule.mem_sInf.mpr fun _ hT => hT.1 (tset_mem.mp hf c)
  have hfd : FiniteDimensional ℂ (tensSub (n := n) V) :=
    Module.Finite.of_injective (LinearMap.pi fun c => LinearMap.codRestrict V
      ((LinearMap.proj c : (Fin n → D) →ₗ[ℂ] D) ∘ₗ (tensSub V).subtype) fun f => tset_mem.mp f.2 c)
      (fun f f' h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  have hW' : FiniteDimensional ℂ W := Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hVle).symm
  have hkst : IsKStableSub ε (smE ε (tfRdiag ε)) (W.map Ξ) := by
    rintro a b hab _ ⟨f, hf, rfl⟩
    refine ⟨_, ?_, (hΞE a b f).symm⟩
    have hf' := tset_mem.mp (show f.1 ∈ tensSub V from hf)
    refine tset_mem.mpr fun c => ?_
    show tensF dual E a b f.1 c ∈ V
    cases dual
    · simp only [tensF, cond_false, tensV_coord]
      exact V.add_mem (hV.2.1 a b hab _ (hf' c)) (by split_ifs; exacts [hf' b, V.zero_mem])
    · simp only [tensF, cond_true, tensVd_coord]
      exact V.sub_mem (hV.2.1 a b hab _ (hf' c)) (by split_ifs; exacts [hf' a, V.zero_mem])
  have hcas : ∀ v ∈ W.map Ξ, casimir (smE ε (tfRdiag ε)) v =
      (((((casVal lam : ℝ) : ℂ) + n + 2 * z).re : ℝ) : ℂ) • v := by
    rintro _ ⟨f, -, rfl⟩
    refine tfg_real (isInfUnitary_of_isDerivedOn hR hDR) ?_
    have h3 : diagOp (casimir E) (P f.1) = ((casVal lam : ℝ) : ℂ) • P f.1 := funext fun c => by
      rw [diagOp_coord, casimir_genSub hD.glRep hc _ (tset_mem.mp (hP.1 _ f.2) c)]; rfl
    have h2 : casimir (tensF dual E) (P f.1) = (((casVal lam : ℝ) : ℂ) + n + 2 * z) • P f.1 := by
      rw [add_smul, add_smul, mul_smul, ← hEP f.1 f.2, ← h3]
      cases dual
      · exact LinearMap.congr_fun (casimir_tensV hD.glRep) _
      · exact LinearMap.congr_fun (casimir_tensVd hD.glRep) _
    show casimir _ (Φ (P' f)) = _ • Φ (P' f)
    rw [← map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hΦE, ← map_sum]
    refine congrArg Φ (Subtype.ext ?_)
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [show ((P' f : tensSub (n := n) (genSub E V)) : Fin n → D) = P f.1 from rfl, ← h2]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply]
  have hgen : genSub (smE ε (tfRdiag ε)) (W.map Ξ) = LinearMap.range Ξ := by
    refine le_antisymm (sInf_le ⟨LinearMap.map_le_range, ?_⟩) ?_
    · rintro a b _ ⟨f, rfl⟩
      exact ⟨_, (hΞE a b f).symm⟩
    · rintro _ ⟨f, rfl⟩
      have h1 := tfg_gen dual E V (((genSub (smE ε (tfRdiag ε)) (W.map Ξ)).comap Ξ).map
        (tensSub (genSub E V)).subtype)
        (fun f hf => ⟨⟨f, hVle hf⟩, Submodule.mem_sInf.mpr fun _ hT => hT.1 ⟨_, hf, rfl⟩, rfl⟩)
        (by
          rintro a b _ ⟨f, hf, rfl⟩
          refine ⟨⟨_, tensSub_stable dual a b f.1 f.2⟩, ?_, rfl⟩
          show Ξ _ ∈ genSub _ _
          rw [← hΞE]
          exact tset_genSub_E _ _ a b hf) f.2
      obtain ⟨f', hf', e⟩ := h1
      rwa [← Subtype.ext e]
  have hspan : Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
      v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))} =
      (genSub (smE ε (tfRdiag ε)) (W.map Ξ)).map (smD ε (tfRdiag ε)).subtype := by
    rw [hgen, ← Submodule.span_eq (Submodule.map _ _)]
    congr 1
    ext v
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨⟨f, hf⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨f.1, f.2, rfl⟩
  rw [hspan]
  exact closure_genSub_stable hR hDR inferInstance hkst hcas

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaJ
section
noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

theorem tf_ge_abstract {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (HP H' : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) (hH'c : IsClosed (H' : Set (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))))
    (hH'P : H' ≤ HP) (hH'st : ∀ g, ∀ v ∈ H', ρ g v ∈ H') (hH'0 : H' ≠ ⊥)
    (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    {d' : ℝ} (hd' : 0 < d')
    (hschur : ∀ x ∈ H', ∀ v ∈ H', ∫ g, ‖inner ℂ x (ρ g v)‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖v‖ ^ 2 / d') :
    d' ≤ ∑ c, ‖w c‖ ^ 2 ∧ (∑ c, ‖w c‖ ^ 2 = d' → HP ≤ H') := by
  have : CompleteSpace H' := hH'c.completeSpace_coe
  set Pw : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) := fun c => H'.starProjection (w c) with hPw
  have hPwm : ∀ c, Pw c ∈ H' := fun c => H'.starProjection_apply_mem (w c)
  have horth : ∀ c, ∀ y ∈ H', inner ℂ (w c - Pw c) y = 0 := fun c y hy =>
    H'.starProjection_inner_eq_zero (w c) y hy
  have hinnerP : ∀ c, ∀ y ∈ H', inner ℂ (w c) y = inner ℂ (Pw c) y := fun c y hy => by
    have := horth c y hy
    rwa [inner_sub_left, sub_eq_zero] at this
  have hpyth : ∀ c, ‖w c‖ ^ 2 = ‖Pw c‖ ^ 2 + ‖w c - Pw c‖ ^ 2 := fun c => by
    have h0 : inner ℂ (Pw c) (w c - Pw c) = 0 := by
      rw [← inner_conj_symm, horth c _ (hPwm c), map_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Pw c) (w c - Pw c) h0
    rw [add_sub_cancel] at this
    simp only [sq]; linarith
  have hL2 : ∀ f : Lp ℂ 2 μ, ‖f‖ ^ 2 = ∫ g, ‖(f : G → ℂ) g‖ ^ 2 ∂μ := fun f => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
      ← integral_re (MeasureTheory.L2.integrable_inner f f)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ((f : G → ℂ) g)
  have hcomp : ∀ v ∈ H', ∀ c, ‖v c‖ ^ 2 = ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := fun v hv c => by
    rw [hL2, ← hschur (Pw c) (hPwm c) v hv]
    refine integral_congr_ae ?_
    filter_upwards [hrep v (hH'P hv) c] with g hg
    rw [hg, hinnerP c _ (hH'st g v hv)]
  have hkey : ∀ v ∈ H', ‖v‖ ^ 2 = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := fun v hv => by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Lp ℂ 2 μ) v
    calc ‖v‖ ^ 2 = ∑ c, ‖v c‖ ^ 2 := h
      _ = ∑ c, ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := Finset.sum_congr rfl fun c _ => hcomp v hv c
      _ = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := by rw [Finset.sum_mul, Finset.sum_div]
  obtain ⟨v0, hv0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH'0
  have hsum : ∑ c, ‖Pw c‖ ^ 2 = d' := by
    have h := hkey v0 hv0
    have hn : ‖v0‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
    field_simp at h
    nlinarith [h, hn, sq_nonneg ‖v0‖]
  refine ⟨hsum ▸ Finset.sum_le_sum fun c _ => by rw [hpyth c]; nlinarith [sq_nonneg ‖w c - Pw c‖], fun heq => ?_⟩
  have hwc : ∀ c, w c ∈ H' := by
    have h0 : ∑ c, ‖w c - Pw c‖ ^ 2 = 0 := by
      have := congrArg (fun t => t - d') heq
      simp only [sub_self] at this
      rw [← this, ← hsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [hpyth c]; ring
    intro c
    have := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => sq_nonneg ‖w c - Pw c‖).mp h0 c (Finset.mem_univ c)
    have h1 : w c - Pw c = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    rw [sub_eq_zero.mp h1]; exact hPwm c
  have hadj : ∀ g (a b : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), inner ℂ a (ρ g b) = inner ℂ (ρ g⁻¹ a) b := fun g a b => by
    let L : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗᵢ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) :=
      ⟨(ρ g : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), hiso g⟩
    have e : ρ g (ρ g⁻¹ a) = a := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
    conv_lhs => rw [← e]
    exact L.inner_map_map _ _
  intro v hv
  set u := v - H'.starProjection v with hu
  have huP : u ∈ HP := HP.sub_mem hv (hH'P (H'.starProjection_apply_mem v))
  have hu0 : ∀ c, ((u c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] 0 := fun c => by
    filter_upwards [hrep u huP c] with g hg
    rw [hg, hadj, Pi.zero_apply]
    have := H'.starProjection_inner_eq_zero v _ (hH'st g⁻¹ _ (hwc c))
    rw [← inner_conj_symm, this, map_zero]
  have hu' : u = 0 := by
    refine (WithLp.ofLp_injective 2).eq_iff.mp ?_
    funext c
    exact Lp.eq_zero_iff_ae_eq_zero.mpr (hu0 c)
  have : v = H'.starProjection v := sub_eq_zero.mp hu'
  rw [this]; exact H'.starProjection_apply_mem v

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

