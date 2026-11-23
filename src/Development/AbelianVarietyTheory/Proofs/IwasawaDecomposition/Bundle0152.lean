module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseSpanCoherentVectorsFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CoherentDense

open MvPolynomial

theorem eq_zero_of_hasSum_pow (a : ℕ → ℂ) (h : ∀ t : ℂ, HasSum (fun n => t ^ n * a n) 0) : a = 0 := by
  have h1 : HasFPowerSeriesAt (0 : ℂ → ℂ) (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    rw [hasFPowerSeriesAt_iff]
    exact Filter.Eventually.of_forall fun t => by
      simpa [FormalMultilinearSeries.coeff_ofScalars] using h t
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).1 h1.eq_zero

theorem eq_zero_of_hasSum_monomial {σ : Type} [Fintype σ] (c : (σ →₀ ℕ) → ℂ)
    (h : ∀ x : σ → ℂ, HasSum (fun α : σ →₀ ℕ => c α * α.prod fun l k => x l ^ k) 0) : c = 0 := by
  classical
  let S : ℕ → Finset (σ →₀ ℕ) := fun n => (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset
  have hS : ∀ n α, α ∈ S n ↔ α.degree = n := fun n α => by simp [S]
  have key : ∀ n, (∑ α ∈ S n, monomial α (c α) : MvPolynomial σ ℂ) = 0 := by
    intro n
    refine MvPolynomial.funext fun x => ?_
    have h1 : (fun m => eval x (∑ α ∈ S m, monomial α (c α) : MvPolynomial σ ℂ)) = 0 := by
      refine eq_zero_of_hasSum_pow _ fun t => ?_
      have h2 := (h (t • x)).tsum_fiberwise (fun α => α.degree)
      refine h2.congr_fun fun m => ?_
      have e : ((fun α : σ →₀ ℕ => α.degree) ⁻¹' {m}) = (S m : Set (σ →₀ ℕ)) := by
        ext α; simp [hS]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, Finset.tsum_subtype' (S m) (fun α : σ →₀ ℕ => c α * α.prod fun l k => (t • x) l ^ k), map_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [eval_monomial, ← (hS m α).1 hα, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
      ring
    simpa using congrFun h1 n
  funext α
  have h3 := congrArg (AddMonoidAlgebra.coeff · α) (key α.degree)
  rw [coeff_sum, Finset.sum_eq_single α (fun β _ hβ => by simp [coeff_monomial, hβ])
    (fun hα => absurd ((hS _ α).2 rfl) hα)] at h3
  simpa using h3

theorem factorial_mul_coeff_expPS {σ : Type} [Fintype σ] (x : σ → ℂ) (α : σ →₀ ℕ) :
    α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (expPS (∑ l, x l • X l)) =
      α.prod fun l k => x l ^ k := by
  classical
  have hdeg : (α.sum fun _ e => e) = α.degree := by
    rw [Finsupp.degree_apply]; rfl
  rw [MvPowerSeries.coeff_apply, expPS, Finset.sum_eq_single α.degree]
  · rw [coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
    have hs : (α.prod fun _ k => k.factorial) * α.multinomial = α.degree.factorial := by
      rw [Finsupp.multinomial_eq, Finsupp.degree_apply, ← Nat.multinomial_spec]; rfl
    have hs' : α.prod (fun _ k => (k.factorial : ℂ)) * (α.multinomial : ℂ) = (α.degree.factorial : ℂ) := by
      rw [← hs]; simp [Finsupp.prod]
    have h0 : (α.degree.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← mul_div_assoc, ← mul_assoc, hs', mul_div_cancel_left₀ _ h0]
  · intro k _ hk
    rw [coeff_linearCombination_X_pow_of_fintype, if_neg (by rw [hdeg]; exact Ne.symm hk), zero_div]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

theorem eq_zero_of_inner_monomial {σ : Type} [DecidableEq σ] (F : Fock σ) (u : F.H)
    (h : ∀ α, inner ℂ u (F.ι (monomial α 1)) = 0) : u = 0 := by
  refine F.dense.eq_zero_of_inner_left ℂ ?_
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _), inner_add_right, hf, hg, add_zero]
  | monomial β c =>
    have e : (monomial β c : MvPolynomial σ ℂ) = c • monomial β 1 := by simp [smul_monomial]
    rw [e, map_smul, inner_smul_right, h, mul_zero]

theorem hasSum_inner {σ : Type} [DecidableEq σ] (F : Fock σ) (u v : F.H) :
    HasSum (fun α : σ →₀ ℕ => inner ℂ u (F.ι (monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ)) *
      inner ℂ (F.ι (monomial α 1)) v) (inner ℂ u v) := by
  let m : (σ →₀ ℕ) → ℝ := fun α => α.prod fun _ k => (k.factorial : ℝ)
  have hm : ∀ α, 0 < m α := fun α => Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _)
  have hm' : ∀ α : σ →₀ ℕ, α.prod (fun _ k => (k.factorial : ℂ)) = (m α : ℂ) := fun α => by
    simp [m, Finsupp.prod]
  let r : (σ →₀ ℕ) → ℂ := fun α => (((√(m α))⁻¹ : ℝ) : ℂ)
  have hr : ∀ α, (starRingEnd ℂ) (r α) = r α := fun α => Complex.conj_ofReal _
  have hr2 : ∀ α, r α * r α = (m α : ℂ)⁻¹ := fun α => by
    simp only [r]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (hm α).le, Complex.ofReal_inv]
  have hm0 : ∀ α, (m α : ℂ) ≠ 0 := fun α => by exact_mod_cast (hm α).ne'
  have hr0 : ∀ α, r α ≠ 0 := fun α h => inv_ne_zero (hm0 α) (by rw [← hr2, h, mul_zero])
  let b : (σ →₀ ℕ) → F.H := fun α => r α • F.ι (monomial α 1)
  have hb : Orthonormal ℂ b := by
    rw [orthonormal_iff_ite]
    intro α β
    simp only [b, inner_smul_left, inner_smul_right, F.fockIP, hr]
    split_ifs with h
    · subst h
      rw [← mul_assoc, hr2, hm', inv_mul_cancel₀ (hm0 α)]
    · simp
  have hsp : (Submodule.span ℂ (Set.range b))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    refine eq_zero_of_inner_monomial F w fun α => ?_
    have := Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self α)) hw
    simpa [b, inner_smul_right, hr0] using this
  have h := (HilbertBasis.mkOfOrthogonalEqBot hb hsp).hasSum_inner_mul_inner u v
  refine h.congr_fun fun α => ?_
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  simp only [b, inner_smul_left, inner_smul_right, hr, hm', div_eq_mul_inv, ← hr2]
  ring

end GlobalTheory.CoherentDense


open GlobalTheory.CoherentDense in
theorem GlobalTheory.dense_span_coherent : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (e : (Ix P Q → ℂ) → F.H), (∀ x, HasCoeff F (e x) (expPS (gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x))) → Dense (Submodule.span ℂ (Set.range e) : Set F.H) := by
  intro P Q F e he
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have hg : ∀ x : Ix P Q → ℂ, gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x = ∑ l, x l • MvPolynomial.X l := fun x => by
    simp [gaussPoly, MvPolynomial.smul_eq_C_mul]
  have h := eq_zero_of_hasSum_monomial
    (fun α => inner ℂ u (F.ι (MvPolynomial.monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ))) fun x => by
      have h1 := hasSum_inner F u (e x)
      rw [Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self x)) hu] at h1
      simpa only [he x _, hg, factorial_mul_coeff_expPS] using h1
  refine eq_zero_of_inner_monomial F u fun α => ?_
  have h2 := congrFun h α
  have h0 : α.prod (fun _ k => (k.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simpa [h0] using h2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetConsColNeZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.Subst

theorem consCol_mulVec_map {E S : Type} [Field E] [CommRing S] (φ : E →+* S) {M : ℕ}
    (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (t : S) (w : Fin M → S) :
    ((Matrix.of fun i => Fin.cons (α := fun _ => E) (x 0 i) (B i) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) E).map φ).mulVec (Fin.cons t w) =
      t • (fun i => φ (x 0 i)) + (B.map φ).mulVec w := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

theorem det_consCol_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (h : StepData σ J x a B J') : (consCol x B).det ≠ 0 := by
  obtain ⟨-, ha, hx, hB, hJ', -, hd⟩ := h
  intro h0
  obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have e := consCol_mulVec_map (RingHom.id E) x B (v 0) (Fin.tail v)
  rw [Fin.cons_self_tail] at e
  have e' : v 0 • x 0 + B.mulVec (Fin.tail v) = 0 := by
    rw [← hPv]
    exact e.symm
  let r : Fin (M + 1) → E := Matrix.vecMul (fun i => σ (x 0 i)) J
  have hr : ∀ y, hE σ J (x 0) y = r ⬝ᵥ y := by
    intro y
    simp only [hE, Formalism.UG.hform, r, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have h1 : r ⬝ᵥ B.mulVec (Fin.tail v) = 0 := by
    rw [Matrix.dotProduct_mulVec]
    have : Matrix.vecMul r B = 0 := by
      funext j
      exact (hr _).symm.trans (hB j)
    rw [this, zero_dotProduct]
  have h2 : v 0 = 0 := by
    have := congrArg (fun y => r ⬝ᵥ y) e'
    simp only [dotProduct_add, h1, dotProduct_smul, ← hr (x 0), hx, add_zero, dotProduct_zero,
      smul_eq_mul, mul_eq_zero] at this
    rcases this with h | h
    · exact h
    · exact absurd ((map_eq_zero _).1 h) ha
  rw [h2, zero_smul, zero_add] at e'
  have h3 : J'.mulVec (Fin.tail v) = 0 := by
    rw [hJ', ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero]
  have h4 : Fin.tail v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd h3
  apply hv
  rw [← Fin.cons_self_tail v, h2, h4]
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem lintegral_subst (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (h1 : IsArtinianRing S) (h2 : IsReduced S) (lam : Measure S) (hl : lam.IsAddHaarMeasure) (M : ℕ)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) S) (hG : IsUnit G.det)
    (f : (Fin (M + 1) → S) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(Measure.pi fun _ => lam) =
      (modu S G.det : ℝ≥0∞) * ∫⁻ t, ∫⁻ y', f (G.mulVec (Fin.cons t (y' 0))) ∂(tupMeas lam 1 M) ∂lam := by
  have key := GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct S h1 h2 lam hl 1 (M + 1) G 1 hG (by simp)
  have hm1 : modu S 1 = 1 := (GlobalTheory.GaugeEx.modu_basic S).2.2.1
  rw [Matrix.det_one, hm1, pow_one, one_pow, mul_one] at key
  have hU : ∀ K : ℕ, MeasurePreserving (fun X : Fin 1 → Fin K → S => X 0) (tupMeas lam 1 K)
      (Measure.pi fun _ => lam) := fun K =>
    measurePreserving_funUnique (Measure.pi fun _ : Fin K => lam) (Fin 1)
  have hGc : Continuous fun z : Fin (M + 1) → S => G.mulVec z :=
    continuous_const.matrix_mulVec continuous_id
  have hlr : lrAct G (1 : Matrix (Fin 1) (Fin 1) S) = fun X _ => G.mulVec (X 0) := by
    funext X a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp [lrAct]
  have hlrm : Measurable (lrAct G (1 : Matrix (Fin 1) (Fin 1) S)) := by
    rw [hlr]
    exact Measurable.of_eval fun _ => hGc.measurable.comp (measurable_pi_apply 0)
  have hfG : Measurable fun z : Fin (M + 1) → S => f (G.mulVec z) := hf.comp hGc.measurable
  have hP := (measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => lam) 0).symm
  have hc : ∀ p : S × (Fin M → S),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => S) 0).symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  calc ∫⁻ z, f z ∂(Measure.pi fun _ => lam)
      = ∫⁻ X, f (X 0) ∂(tupMeas lam 1 (M + 1)) := ((hU _).lintegral_comp hf).symm
    _ = (modu S G.det : ℝ≥0∞) * ∫⁻ X, f (G.mulVec (X 0)) ∂(tupMeas lam 1 (M + 1)) := by
        conv_lhs => rw [key]
        rw [lintegral_smul_measure, lintegral_map (f := fun X : Fin 1 → Fin (M + 1) → S => f (X 0))
          (hf.comp (measurable_pi_apply 0)) hlrm, hlr]
        rfl
    _ = (modu S G.det : ℝ≥0∞) * ∫⁻ z, f (G.mulVec z) ∂(Measure.pi fun _ => lam) := by
        rw [(hU _).lintegral_comp hfG]
    _ = _ := by
        congr 1
        rw [← hP.lintegral_comp hfG]
        refine (lintegral_prod _ (hfG.comp hP.measurable).aemeasurable).trans ?_
        refine lintegral_congr fun t => ?_
        have hm : Measurable fun w : Fin M → S => f (G.mulVec (Fin.cons t w)) := by
          have := (hfG.comp hP.measurable).comp (measurable_prodMk_left (x := t))
          convert this using 2 with w
          simp only [Function.comp, hc]
        rw [(hU M).lintegral_comp hm]
        simp only [Function.comp, hc]

theorem subst : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ (lam : Measure (R ⊗[F] E)), lam.IsAddHaarMeasure → ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E), g • ratTup (F := F) R x = y → ∀ f : (Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ z, f z ∂(Measure.pi fun _ => lam) = (modu (R ⊗[F] E) (inclR R (consCol x B).det) : ℝ≥0∞) * ∫⁻ t, ∫⁻ y', f (t • y 0 + pairOf R σ J B y g y' 1) ∂(tupMeas lam 1 M) ∂lam := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hR M J x a B J' hS lam hl g y hy f hf
  obtain ⟨n1, n2, -⟩ := GlobalTheory.GaugeEx.nice_tensor F E R hR
  have hP : IsUnit (inclR (F := F) R (consCol x B).det) :=
    (IsUnit.mk0 _ (det_consCol_ne_zero σ J x a B J' hS)).map _
  have hJ : IsUnit (JR (F := F) R J).det := by
    have : IsUnit (inclR (F := F) R J.det) := (IsUnit.mk0 _ hS.1.2).map _
    rwa [RingHom.map_det] at this
  set A : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) :=
    (HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)).val with hA
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have hU : Formalism.UG.cT (sigR R σ) A * JR R J * A = JR R J := (show HR R σ J from g).2
  have hN : A.det * sigR R σ A.det = 1 := by
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    apply hJ.mul_left_cancel
    rw [mul_one]
    conv_rhs => rw [← this]
    ring
  have hmA : modu (R ⊗[F] E) A.det = 1 := by
    rw [(GlobalTheory.GaugeEx.modu_eq_modu_norm F E σ hCM R A.det 1 hAu (by rw [map_one, hN])).2]
    exact (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  have hdet : (A * (consCol x B).map (inclR (F := F) R)).det =
      A.det * inclR (F := F) R (consCol x B).det := by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [lintegral_subst (R ⊗[F] E) n1 n2 lam hl M (A * (consCol x B).map (inclR (F := F) R))
    (by rw [hdet]; exact hAu.mul hP) f hf, hdet,
    (GlobalTheory.GaugeEx.modu_basic (R ⊗[F] E)).2.1 _ _ hAu hP, hmA, one_mul]
  congr 1
  refine lintegral_congr fun t => lintegral_congr fun y' => congrArg f ?_
  rw [← Matrix.mulVec_mulVec, consCol, consCol_mulVec_map, Matrix.mulVec_add, Matrix.mulVec_smul]
  subst hy
  rfl

end GlobalTheory.GaugeEx.Subst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeBidual
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelHecke.DualConj

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J L ↔ ∀ x ∈ L, hform σ J x y ∈ (algebraMap (𝓞 E) E).range := by
  have := bwG_span_dualSet σ J L
  change y ∈ ((Submodule.span (𝓞 E) (dualSet σ J L) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ _
  rw [this]; rfl

omit [NumberField E] in
theorem hform_eq (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_unitary (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E)
    (hg : cT σ g * J * g = J) (x y : Fin n → E) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have e : (fun i => σ ((g *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* cT σ g := by
    funext i
    simp [cT, mulVec, vecMul, dotProduct, mul_comm]
  rw [hform_eq, hform_eq, e, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

omit [NumberField E] in
theorem hform_smul_left (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

@[reducible] def starOf (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add σ

theorem dual_lattice_bidual (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit J.det) (hH : cT σ J = J) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice E (dualL σ J L) ∧ dualL σ J (dualL σ J L) = L := by
  letI : StarRing E := starOf σ hσ
  let h : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (hform σ J)
      (fun x x' y => by simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
      (fun a x y => hform_smul_left σ J a x y)
      (fun x y y' => by simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (fun a x y => hform_smul_right σ J a x y)
  have hh : ∀ x y, h x y = hform σ J x y := fun _ _ => rfl
  have hsym' : ∀ x y, σ (hform σ J x y) = hform σ J y x := by
    intro x y
    have e : ∀ i j, σ (J i j) = J j i := fun i j => congrFun (congrFun hH j) i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hform, map_sum, map_mul, hσ, e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsym : h.IsSymm := ⟨fun x y => hsym' x y⟩
  have hr : ∀ y, (∀ x, hform σ J x y = 0) → y = 0 := by
    intro y hy
    have h1 : J *ᵥ y = 0 := by
      funext i
      have := hy (Pi.single i 1)
      rw [hform_eq, dotProduct, Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hb
        simp [hb]
      · simp
    have ey : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [ey, h1, mulVec_zero]
  have hnd : h.Nondegenerate := by
    refine ⟨fun x hx => hr x fun y => ?_, fun y hy => hr y hy⟩
    rw [← hsym', ← hh, hx y, map_zero]
  have hd : ∀ M : Submodule (𝓞 E) (Fin n → E), Formalism.HermitianLatticesTheory.dual h M = dualL σ J M := by
    intro M
    ext y
    rw [mem_dualL]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
    rfl
  have := Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E (Fin n → E) h hsym hnd (fun r => LocB.sig_int σ r) L hL
  rw [hd, hd] at this
  exact ⟨this.1, this.2.1⟩

theorem localization_dualL_le (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hPQ : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P) (M N : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N) :
    Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N) ≤ Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) := by
  have h1P : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  have key : ∃ s : 𝓞 E, s ∉ P ∧ ∀ x ∈ M, s • x ∈ N := by
    have h0 : M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := fun x hx =>
      h ((rlv_mem_locP P M x).2 ⟨1, h1P, by rwa [one_smul]⟩)
    clear h
    induction M, hM using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨s, hs, hx⟩ := (rlv_mem_locP P N x).1 (h0 (Submodule.mem_span_singleton_self x))
      refine ⟨s, hs, fun y hy => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_comm]; exact N.smul_mem a hx
    | sup A B _ _ hA hB =>
      obtain ⟨s, hs, h1⟩ := hA (le_sup_left.trans h0)
      obtain ⟨t, ht, h2⟩ := hB (le_sup_right.trans h0)
      refine ⟨s * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs ht, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine N.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (h1 a ha)
      · rw [mul_smul]; exact N.smul_mem _ (h2 b hb)
  obtain ⟨s, hs, hsM⟩ := key
  obtain ⟨s', hs'⟩ := LocB.sig_int σ s
  have hs'Q : s' ∉ Q := fun hq => hs (hPQ s' s hs' hq)
  intro y hy
  obtain ⟨t, ht, hty⟩ := (rlv_mem_locP Q _ y).1 hy
  refine (rlv_mem_locP Q _ y).2 ⟨s' * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs'Q ht, ?_⟩
  rw [mem_dualL] at hty ⊢
  intro x hx
  have := hty _ (hsM x hx)
  rw [← algebraMap_smul E s x, hform_smul_left] at this
  rw [mul_smul, ← algebraMap_smul E s' (t • y), hform_smul_right, hs']
  exact this

theorem mem_mulLat (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ mulLat γ.1 L ↔ (γ⁻¹).1 *ᵥ y ∈ L := by
  rw [← map_glE, Submodule.mem_map_equiv, glE_symm_apply]

theorem mulLat_lattice (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice E (mulLat γ.1 L) := by
  letI : Submodule.IsLattice E (mulLat γ.1 L) := Submodule.IsLattice.of_fg E (hL.fg.map _)
  constructor
  change Submodule.span E ((L.map ((Matrix.mulVecLin γ.1).restrictScalars (𝓞 E)) :
    Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤
  rw [show Submodule.span E ((L.map ((Matrix.mulVecLin γ.1).restrictScalars (𝓞 E)) :
      Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      (Submodule.span E (L : Set (Fin n → E))).map (Matrix.mulVecLin γ.1) by
        rw [Submodule.map_span]; rfl,
    hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (glE γ).surjective

theorem dualL_mulLat (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E) (hγ : γ ∈ UJ σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) : dualL σ J (mulLat γ.1 L) = mulLat γ.1 (dualL σ J L) := by
  ext y
  have ey : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ y) = y := (glE γ).apply_symm_apply y
  rw [mem_mulLat, mem_dualL, mem_dualL]
  constructor
  · intro h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey] at this
    exact this

theorem dual_conj_primes : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime], (∀ x, σ (σ x) = x) → IsUnit J.det → cT σ J = J → (∀ a b : 𝓞 E, (b : E) = σ (a : E) → (a ∈ Q ↔ b ∈ P)) → ∀ M N : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E M → Submodule.IsFullLattice E N → (Formalism.HermitianLatticesTheory.localization₂ P M = Formalism.HermitianLatticesTheory.localization₂ P N → Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N)) ∧ (Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J N) → Formalism.HermitianLatticesTheory.localization₂ Q M = Formalism.HermitianLatticesTheory.localization₂ Q N) ∧ ∀ γ : GL (Fin n) E, γ ∈ UJ σ J → Submodule.IsFullLattice E (mulLat γ.1 M) ∧ dualL σ J (mulLat γ.1 M) = mulLat γ.1 (dualL σ J M) := by
  intro E _ _ σ n J P Q _ _ hσ hJ hH hPQ M N hM hN
  have hPQ' : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P := fun a b hab =>
    (hPQ a b (by rw [hab, hσ])).1
  have one : ∀ A B : Submodule (𝓞 E) (Fin n → E), A.FG → B.FG → Formalism.HermitianLatticesTheory.localization₂ P A = Formalism.HermitianLatticesTheory.localization₂ P B →
      Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J A) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J B) := fun A B hA hB h =>
    le_antisymm (localization_dualL_le σ J P Q hPQ' B A hB h.ge) (localization_dualL_le σ J P Q hPQ' A B hA h.le)
  obtain ⟨hM1, hM2⟩ := dual_lattice_bidual σ hσ J hJ hH M hM
  obtain ⟨hN1, hN2⟩ := dual_lattice_bidual σ hσ J hJ hH N hN
  refine ⟨one M N hM.fg hN.fg, fun h => ?_, fun γ hγ => ⟨mulLat_lattice γ M hM, dualL_mulLat σ J γ hγ M⟩⟩
  have := one _ _ hM1.fg hN1.fg h
  rwa [hM2, hN2] at this

end GlobalTheory.LevelHecke.DualConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_generate_ideal_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ J : X.IdealSheafData, ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
  first | exact @GlobalTheory.ProjBlowup.exists_generates | exact GlobalTheory.ProjBlowup.exists_generates | (intros; apply GlobalTheory.ProjBlowup.exists_generates <;> assumption)
end

