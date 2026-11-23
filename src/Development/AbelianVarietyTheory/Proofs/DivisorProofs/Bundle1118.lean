module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TotalDegreeBindLeOfLinear
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyAveragesFiniteWeightStableSubspace
section
noncomputable section

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF

theorem polyAverages_finiteWeightStableSubspace : PolyAvg := by
  classical
  intro n ε d
  set Wm : Set (Fin n → ℝ) := wtM '' {m : EntIdx n →₀ ℕ | (m.sum fun _ e => e) ≤ d}
  refine ⟨Wm, (finite_monomials_of_degree_le d).image _, fun H _ _ _ σ hσ u => ?_⟩
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  set φ : Formalism.REAL.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => Formalism.REAL.toMK k with hφdef
  have hφc : Continuous φ := hemb.continuous
  have hφK : ∀ g, φ g ∈ Kset ε := fun g => g.2
  have hφ1 : φ 1 = 1 := rfl
  have hφm : ∀ a b, φ (a * b) = φ a * φ b := fun a b => rfl
  have hφs : ∀ m ∈ Kset ε, ∃ g, φ g = m := by
    intro m hm
    have : m ∈ Set.range (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) := by
      rw [Formalism.REAL.range_toMK]
      exact hm
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩
  have hinUJ : ∀ g, φ g ∈ UJset ε := fun g => smd_inUJ_of_Kset (hφK g)
  have horb : ∀ u : H, Continuous fun k => σ (φ k) u := fun u => (hσ.2.2 u).comp_continuous hφc hinUJ
  have hentc : Continuous fun k => entVar (φ k) := by
    refine continuous_pi fun i => ?_
    rcases i with x | x
    · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hφc))
  have hpolyc : ∀ Q : MvPolynomial (EntIdx n) ℂ, Continuous fun k => eval (entVar (φ k)) Q :=
    fun Q => (MvPolynomial.continuous_eval Q).comp hentc
  have hint : ∀ (Q : MvPolynomial (EntIdx n) ℂ) (u : H),
      Integrable (fun k => eval (entVar (φ k)) Q • σ (φ k) u) (muK ε) := fun Q u =>
    ((hpolyc Q).smul (horb u)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Xu : H → MvPolynomial (EntIdx n) ℂ →ₗ[ℂ] H := fun u =>
    { toFun := fun Q => ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂(muK ε)
      map_add' := fun Q R => by
        simp only [map_add (f := _), add_smul]
        exact integral_add (hint Q u) (hint R u)
      map_smul' := fun c Q => by
        simp only [smul_eval, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have hXu : ∀ u Q, Xu u Q = ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂(muK ε) := fun _ _ => rfl
  have htr : ∀ u Q g, σ (φ g) (Xu u Q) = Xu u (bind₁ (trF (φ g⁻¹)) Q) := by
    intro u Q g
    rw [hXu, hXu, ← (σ (φ g)).integral_comp_comm (hint Q u)]
    have e2 : ∫ k, σ (φ g) (eval (entVar (φ k)) Q • σ (φ k) u) ∂(muK ε) =
        ∫ k, eval (entVar (φ (g⁻¹ * (g * k)))) Q • σ (φ (g * k)) u ∂(muK ε) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_smul, inv_mul_cancel_left]
      rw [hφm g k, hσ.1.2 _ (hinUJ g) _ (hinUJ k)]
      rfl
    rw [e2, integral_mul_left_eq_self (fun k => eval (entVar (φ (g⁻¹ * k))) Q • σ (φ k) u) g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hφm, eval_mul_eq_bind₁]
  have hmono : ∀ (u : H) (m : EntIdx n →₀ ℕ),
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (wtM m) (Xu u (monomial m 1)) := by
    intro u m θ hθ
    rw [mir_Kset_eq] at hθ
    obtain ⟨g, hg⟩ := hφs _ hθ
    have hginv : φ g⁻¹ = star (φ g) := by
      have h1 : φ g * star (φ g) = 1 := Unitary.mul_star_self_of_mem (hφK g).1
      calc φ g⁻¹ = φ g⁻¹ * (φ g * star (φ g)) := by rw [h1, Matrix.mul_one]
        _ = star (φ g) := by rw [← Matrix.mul_assoc, ← hφm, inv_mul_cancel, hφ1, Matrix.one_mul]
    rw [← hg, htr, hXu, hXu, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [← eval_mul_eq_bind₁, hginv, hg, show Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) =
      dTor θ from rfl, eval_monomial_tor, mul_smul]
  let Sd : Submodule ℂ H := (restrictTotalDegree (EntIdx n) ℂ d).map (Xu u)
  refine ⟨Sd, Module.Finite.map _ _, ?_, ?_, ?_⟩
  · intro k hk x hx
    rw [mir_Kset_eq] at hk
    obtain ⟨g, rfl⟩ := hφs k hk
    obtain ⟨Q, hQ, rfl⟩ := hx
    rw [htr]
    refine Submodule.mem_map_of_mem ?_
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    rw [mem_restrictTotalDegree]
    exact (totalDegree_bind_le_of_linear _ (trF_totalDegree _) Q).trans hQ
  · intro P hP
    exact Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ P).2 hP)
  · rintro μ s ⟨Q, hQ, rfl⟩ hs0 hsw
    by_contra hμ
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    have hsum : Xu u Q = ∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m • Xu u (monomial m 1) := by
      conv_lhs => rw [Q.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    have horth : ∀ m ∈ Q.support, inner ℂ (Xu u Q) (Xu u (monomial m 1)) = 0 := by
      intro m hm
      refine kfin_wt_orth hσ hsw (hmono u m) fun h => hμ ?_
      exact ⟨m, (le_totalDegree hm).trans hQ, h.symm⟩
    apply hs0
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    calc inner ℂ (Xu u Q) (Xu u Q) = inner ℂ (Xu u Q) (∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m • Xu u (monomial m 1)) := by
          rw [← hsum]
      _ = 0 := by
          rw [inner_sum]
          exact Finset.sum_eq_zero fun m hm => by rw [inner_smul_right, horth m hm, mul_zero]

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoefIrrepHasDerivedAction
section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.PcEF.PolynomialCoefficientDerivedAction

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

lemma not_cdom {Λ : Fin n → ℝ} {a b : Fin n} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom ε (Λ + Pi.single a 1 - Pi.single b 1) Λ := by
  rintro ⟨c, hc, he⟩
  let ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑ j : Fin n, ((j : ℕ) : ℝ) * f j
      map_add' := by
        intro f g
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r f
        simp [Finset.mul_sum, mul_left_comm] }
  have hψ : ∀ x : Fin n, ψ (Pi.single x 1) = ((x : ℕ) : ℝ) := by
    intro x
    simp [ψ, Pi.single_apply]
  have hl : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by
    abel
  rw [hl] at he
  have h := congrArg ψ he
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Formalism.REAL.root, map_sub, hψ, smul_eq_mul] at h
  have hr : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy := (hc x y h0).1
      have : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

section Der

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : KG ε →* unitary (H →L[ℂ] H))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (H →L[ℂ] H))
  (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
    (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0)
  (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
  (hσ : ∀ g : KG ε, σ (toMK g) = ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H))


include hder in
lemma conj (g : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ Y * star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Y * star (toMK g)) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have hY' := inK_conj' g hY
  set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((g : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK g) :=
    toMK_inv' g
  have hγ' : ∀ t : ℝ, toMK (g * γ t * g⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK g * Y * star (toMK g))) := by
    intro t
    have e1 : toMK (g * γ t * g⁻¹) = toMK g * toMK (γ t) * toMK g⁻¹ := rfl
    rw [e1, toMK_inv', hγ t, ← hU]
    have e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.exp_units_conj]
  have h1 := hder _ hY' _ hγ'
  set A : H →L[ℂ] H := ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  have h2 := (((ContinuousLinearMap.mul ℂ (H →L[ℂ] H) A).comp
      ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip (star A))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (hder _ hY γ hγ)
  have hf : (fun t => ((τ (g * γ t * g⁻¹) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) =
      fun t => A * ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * star A := by
    funext t
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [hf] at h1
  have h3 := h2.unique (by simpa [Function.comp_def, mul_assoc] using h1)
  simpa [mul_assoc] using h3


include hder in
lemma conj_single (g : KG ε) {a b : Fin n} (hab : ε a = ε b) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ (Matrix.single a b 1) *
      star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Matrix.single a b 1 * star (toMK g)) := by
  rw [single_eq_kp a b]
  have e : toMK g * (kp1 a b + Complex.I • kp2 a b) * star (toMK g) =
      toMK g * kp1 a b * star (toMK g) + Complex.I • (toMK g * kp2 a b * star (toMK g)) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, map_add (f := _), map_smul, map_add (f := _), map_smul, ← conj τ dτ hder g (inK_hermitian_unit hab),
    ← conj τ dτ hder g (inK_skew_hermitian_unit hab), mul_add, add_mul, mul_smul_comm, smul_mul_assoc]


include hder hσ in
lemma dτ_of_wt {μ : Fin n → ℝ} {v : H}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a : Fin n) :
    dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
  set d : Fin n → ℂ := fun b => if b = a then Complex.I else 0 with hddef
  have hd : ∀ b, star (d b) = -d b := fun b => by
    simp only [d]; split_ifs <;> simp
  have hX := torep_inK_diag ε d hd
  set γ := onepCurve ε hX with hγdef
  have hD : ∀ t : ℝ, toMK (γ t) =
      Matrix.diagonal (fun b => Complex.exp (((if b = a then t else 0 : ℝ) : ℂ) * Complex.I)) := by
    intro t
    rw [toMK_onepCurve, ← Matrix.diagonal_smul, torep_exp_diag]
    congr 1
    funext b
    by_cases h : b = a <;> simp [d, h]
  have hval : ∀ t : ℝ, ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v =
      Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v := by
    intro t
    rw [← hσ, hD t, hv _ (by rw [← hD t]; exact (γ t).2)]
    have hs : (∑ b, μ b * (if b = a then t else 0)) = μ a * t := by
      simp [Finset.sum_ite_eq']
    rw [hs]
  have h1 : HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v)
      (dτ (Matrix.diagonal d) v) 0 := by
    have := ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hder _ hX γ (toMK_onepCurve _ hX))
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v)
      (((μ a : ℂ) * Complex.I) • v) 0 := by
    rw [show (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) =
      fun t : ℝ => Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v from funext hval]
    have h3 : HasDerivAt (fun t : ℝ => (((μ a * t : ℝ) : ℂ) * Complex.I)) ((μ a : ℂ) * Complex.I) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (μ a)).ofReal_comp).mul_const Complex.I
      simpa using this
    have := (h3.cexp).smul_const v
    simpa using this
  have heq := h1.unique h2
  have hdX : dτ (Matrix.diagonal d) = Complex.I • dτ (Matrix.single a a 1) := by
    rw [torep_diag_sum, Finset.sum_eq_single a (fun b _ hb => by simp [d, hb]) (by simp), map_smul]
    simp [d]
  rw [hdX, _root_.smul_apply, mul_comm, mul_smul] at heq
  exact smul_right_injective _ Complex.I_ne_zero heq


include hder hσ in
lemma hw {Λ : Fin n → ℝ}
    (hK5 : ∀ (μ : Fin n → ℝ) (v : H), v ∈ (⊤ : Submodule ℂ H) → v ≠ 0 →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ v → Formalism.MainNotions.S.CDom ε μ Λ)
    {w : H} (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ Λ w) (a b : Fin n) (hab : a < b)
    (hε : ε a = ε b) : dτ (Matrix.single a b 1) w = 0 := by
  by_contra hx
  refine not_cdom hab (hK5 _ _ Submodule.mem_top hx ?_)
  intro θ hθ
  set g := torepK ε hθ
  set A : H →L[ℂ] H := ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  have hk : σ (Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I))) = A := hσ g
  have hAA : star A * A = 1 := Unitary.coe_star_mul_self _
  have hwA : A w = Complex.exp (((∑ c, Λ c * θ c : ℝ) : ℂ) * Complex.I) • w := by
    rw [← hk]
    exact hw θ hθ
  have key : A * dτ (Matrix.single a b 1) = (A * dτ (Matrix.single a b 1) * star A) * A := by
    rw [mul_assoc (A * dτ (Matrix.single a b 1)), hAA, mul_one]
  rw [hk, show A (dτ (Matrix.single a b 1) w) = (A * dτ (Matrix.single a b 1)) w from rfl, key,
    show (A * dτ (Matrix.single a b 1) * star A * A) w = (A * dτ (Matrix.single a b 1) * star A) (A w) from rfl,
    conj_single τ dτ hder g hε, hwA,
    show toMK g = Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I)) from rfl, fh_diag_conj,
    map_smul, map_smul, _root_.smul_apply, smul_smul]
  congr 1
  have hs : (∑ c, (Λ + Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) c * θ c) = (∑ c, Λ c * θ c) + θ a - θ b := by
    simp [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, ite_mul]
  have hst : star (Complex.exp ((θ b : ℂ) * Complex.I)) = Complex.exp (-((θ b : ℂ) * Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [hs, hst, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Der

end GlobalTheory.PsCo.PcEF.PolynomialCoefficientDerivedAction

namespace GlobalTheory.PsCo.PcEF

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

theorem polyCoefIrrep_hasDerivedAction :
    ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type)
      [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : GlobalTheory.PsCo.Pc1.Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
      (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) →
      ∃ T₀ : KType ε γ, ∀ k : KG ε,
        ReciprocityTheory.ChartRestriction.TR.Weyl.kChar T₀ k = trK T (toMK k) := by
  intro n ε γ W _ _ _ T hT _
  obtain ⟨-, hU, hK⟩ := hT
  have : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
  obtain ⟨τ, hτc, hτ⟩ := uRepHom n ε W T hU
  obtain ⟨dτ, hder⟩ := derivExists n ε W τ hτc
  have hσ : ∀ g : KG ε, T (toMK g) = ((τ g : unitary (W →L[ℂ] W)) : W →L[ℂ] W) := fun g => (hτ g).symm
  obtain ⟨v0, -, hv0, hwt0⟩ := hK.2.2.2.1
  have hn : ‖v0‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  set w : W := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0 with hwdef
  have hwn : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  have hwt : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T γ w := by
    intro θ hθ
    rw [hwdef, map_smul, hwt0 θ hθ, smul_comm]
  refine ⟨KType.mk (V := W) τ hτc ?_ dτ hder w hwn
    (fun a => PolynomialCoefficientDerivedAction.dτ_of_wt τ dτ hder T hσ hwt a)
    (fun a b hab he => PolynomialCoefficientDerivedAction.hw τ dτ hder T hσ hK.2.2.2.2 hwt a b hab he), fun k => ?_⟩
  · intro S hS
    refine hK.2.2.1 S le_top (fun g hg v hv => ?_)
    have h := hS (torepK ε hg) v hv
    rw [← hσ] at h
    exact h
  · show LinearMap.trace ℂ W ((((τ k : unitary (W →L[ℂ] W)) : W →L[ℂ] W)) : W →ₗ[ℂ] W) = trK T (toMK k)
    rw [← hσ]
    rfl

end GlobalTheory.PsCo.PcEF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyOnKConj
section
noncomputable section

open MvPolynomial
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

def conjPoly (n : ℕ) : Poly n →+* Poly n :=
  (rename (Sum.swap : (Fin n × Fin n) ⊕ (Fin n × Fin n) → _)).toRingHom.comp (map (starRingEnd ℂ))

theorem ev_conjPoly {n : ℕ} (g : Mat n) (P : Poly n) : ev g (conjPoly n P) = conj (ev g P) := by
  have h : (ev g).comp (conjPoly n) = (starRingEnd ℂ).comp (ev g) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [conjPoly, ev]
    · intro i
      rcases i with x | x
      · simp [conjPoly, ev]
      · simp [conjPoly, ev]
  exact congrArg (fun φ : Poly n →+* ℂ => φ P) h

theorem polyOnK_conj {n : ℕ} {ε : Fin n → Bool} {f : Mat n → ℂ} (hf : PolyOnK ε f) :
    PolyOnK ε fun k => conj (f k) := by
  obtain ⟨P, hP⟩ := hf
  exact ⟨conjPoly n P, fun k hk => by dsimp only; rw [ev_conjPoly, hP k hk]⟩

theorem polyOnK_sum {n : ℕ} {ε : Fin n → Bool} {ι : Type} (s : Finset ι) (f : ι → Mat n → ℂ)
    (hf : ∀ i ∈ s, PolyOnK ε (f i)) : PolyOnK ε fun k => ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun k _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨P, hP⟩ := hf a (Finset.mem_insert_self a s)
    obtain ⟨Q, hQ⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact ⟨P + Q, fun k hk => by dsimp only at hQ ⊢; rw [Finset.sum_insert ha, map_add (f := _), hP k hk, hQ k hk]⟩

theorem trPoly : TrPoly := by
  intro n ε W _ _ _ T hT
  apply polyOnK_conj
  have e : trK T = fun k => ∑ i, ⟪(stdOrthonormalBasis ℂ W) i, T k ((stdOrthonormalBasis ℂ W) i)⟫_ℂ := by
    funext k
    simp only [trK, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ W)]
    rfl
  rw [e]
  exact polyOnK_sum _ _ fun i _ => hT _ _

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceGLConjMaxCompactIffStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruenceGL_conj_maxCompact_iff : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (m k : ℕ) (c N : GLw m w), c ∈ GlobalTheory.LFun.KGL w (n := m) → ((c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ (N ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)))) := by
  first | exact @GlobalTheory.congConj_iff | exact GlobalTheory.congConj_iff | (intros; apply GlobalTheory.congConj_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStableStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruenceLevel_iff_lattice_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  first | exact @GlobalTheory.TwLat.Lv.level_iff | exact GlobalTheory.TwLat.Lv.level_iff | (intros; apply GlobalTheory.TwLat.Lv.level_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpenLeIsCompact
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem relIndex_ne_zero_of_isOpen_le_isCompact {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (K U : Subgroup H) (hK : IsCompact (K : Set H))
    (hU : IsOpen (U : Set H)) (_hUK : U ≤ K) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hO : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) :=
    hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hO
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory
end

