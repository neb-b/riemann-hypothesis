module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormThetaFunctionPeriodicRealVariables
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare.ThetaPeriod

variable {D : D7}

def mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) : AF D.host.F →+ WA V W where
  toFun a := Matrix.of fun i j => a ⊗ₜ[D.host.F] γ i j
  map_zero' := by ext i j; exact TensorProduct.zero_tmul _ _
  map_add' x y := by ext i j; exact TensorProduct.add_tmul _ _ _

theorem continuous_mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    Continuous (mulRat V W γ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun a : AF D.host.F => mulRat V W γ a i j) =
      fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] γ i j : AE D) := by
    funext a
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
  rw [e]
  have : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  exact Continuous.smul (M := AF D.host.F) (X := AE D) (f := fun a : AF D.host.F => a) continuous_id continuous_const

theorem mulRat_one (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    mulRat V W γ 1 = ratW V W γ := by
  ext i j; rfl

theorem ratW_nsmul (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (N : ℕ) :
    ratW V W (N • γ) = N • ratW V W γ := by
  ext i j
  exact (incA D).toAddMonoidHom.map_nsmul N (γ i j)

theorem norm_periodic (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (hU : ∀ U : AddSubgroup (AF D.host.F), IsOpen (U : Set (AF D.host.F)) →
      ∃ N : ℕ, 0 < N ∧ pairA D.host.F 0 (N : Af D.host.F) ∈ U)
    (V W : HSp D) (f : WA V W → ℂ) (hf : IsThetaFun ψ V W f) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ w, ‖f (w + iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)))‖ = ‖f w‖ := by
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨N, hN, hmem⟩ := hU (U.comap (mulRat V W γ)) (hUo.preimage (continuous_mulRat V W γ))
  refine ⟨N, hN, fun w => ?_⟩
  set u : WA V W := mulRat V W γ (pairA D.host.F 0 (N : Af D.host.F)) with hu
  set r : WA V W := mulRat V W γ (pairA D.host.F (N : Ainf D.host.F) 0) with hr
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hr0 : IsRealW V W r := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hsum : r + u = N • ratW V W γ := by
    rw [hr, hu, ← AddMonoidHom.map_add (f := _), ← mulRat_one, ← AddMonoidHom.map_nsmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (N : Ainf D.host.F) + 0 = N • (1 : Ainf D.host.F)
      rw [add_zero, nsmul_one]
    · show 0 + (N : Af D.host.F) = N • (1 : Af D.host.F)
      rw [zero_add, nsmul_one]
  have hpu : piW θ V W u = 0 := by
    funext τ i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu0 i) j
    show θ τ (infPart D (u i j)) = 0
    rw [this, RingHom.map_zero]
  have hi : iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)) = r := by
    rw [Nat.cast_smul_eq_nsmul, ← AddMonoidHom.map_nsmul, ← hsum, AddMonoidHom.map_add (f := _), hpu, add_zero,
      h.iota_pi hr0]
  have h1 : ∀ x, ‖f (x + u)‖ = ‖f x‖ := fun x => by
    have := congrFun (hUf u hmem hu0) x
    rw [← this, Heisenberg₂, norm_mul, hψ, one_mul]
  have h2 := congrArg norm (hf.quasi (N • γ) w)
  rw [norm_mul, hψ, one_mul, ratW_nsmul, ← hsum] at h2
  rw [hi, ← h1, ← h2, add_assoc, add_comm]

end GlobalTheory.FockCompare.ThetaPeriod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem pair_fst_of_snd {F : Type} [Field F] [NumberField F] (a : AF F) (h : sndA F a = 0) :
    pairA F (fstA F a) 0 = a := Prod.ext rfl h.symm

theorem half_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (θ : Ainf F ⊗[F] E →+* ℂ)
    (a : AF F) :
    θ (fstA F (algebraMap F (AF F) (1 / 2) * a) ⊗ₜ[F] (1 : E)) = θ (fstA F a ⊗ₜ[F] (1 : E)) / 2 := by
  have h2 : algebraMap F (AF F) (1 / 2) * a + algebraMap F (AF F) (1 / 2) * a = a := by
    rw [← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]
  conv_rhs => rw [← h2, map_add (f := _), TensorProduct.add_tmul, RingHom.map_add (f := _)]
  ring

theorem valTau_coe {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AF D.host.F) :
    ((valTau θ τ a : ℝ) : ℂ) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
  have h := conj_tmul_one hθ τ (fstA D.host.F a)
  exact Complex.conj_eq_iff_re.1 h

theorem real_adele_ext_and_char : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ a : AF D.host.F, sndA D.host.F a = 0 → ((∀ τ, valTau θ τ a = 0) → a = 0) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) = Complex.exp (-(Real.pi * Complex.I) * ((∑ τ, valTau θ τ a : ℝ) : ℂ)) := by
  intro D θ σ h a ha
  refine ⟨fun h0 => ?_, fun ψ hψ => ?_⟩
  · have h1 : (a ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = 0 := by
      refine h.ext _ ?_ fun τ => ?_
      · have e : finPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ha, TensorProduct.zero_tmul]
      · have e : infPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ← valTau_coe h.inf, h0, Complex.ofReal_zero]
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := AF D.host.F)
      (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [map_zero]
    exact h1
  · have hc := hψ.2.2 θ h.inf (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a))
    rw [psiInf, pair_fst_of_snd _ (by rw [map_mul, ha, mul_zero])] at hc
    rw [hc]
    congr 1
    have e : ∀ ρ, θ ρ (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) ⊗ₜ[D.host.F] (1 : D.host.E))
        = ((valTau θ ρ a : ℝ) : ℂ) / 2 := fun ρ => by
      rw [valTau_coe h.inf]
      exact half_tmul (θ ρ) a
    rw [Finset.sum_congr rfl fun ρ _ => e ρ, ← Finset.sum_div, Complex.ofReal_sum]
    push_cast
    ring

end GlobalTheory.FockCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem smooth_iff_sm_and_real_lines : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), (∀ f : WA V W → ℂ, (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔ Sm (iotaW σ V W) f) ∧ (∀ L : ℝ →+ WA V W, IsRealDir V W L → ∀ t : ℝ, L t = iotaW σ V W (t • piW θ V W (L 1))) ∧ ∀ u : RW V W, ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ ∀ t : ℝ, L t = iotaW σ V W (t • u) := by
  intro D θ σ h V W
  refine ⟨fun f => ⟨fun H w => ?_, fun H k L hL hL0 w => ?_⟩, fun L hL t => ?_, fun u => ?_⟩
  · let e : RW V W ≃L[ℝ] (Fin (Module.finrank ℝ (RW V W)) → ℝ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
    have h1 := H _ ((iotaW σ V W).comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom)
      ((h.continuous_iota V W).comp e.symm.continuous) (fun t => h.real_iota V W _) w
    have h2 := h1.comp e.contDiff
    have h3 : (fun x : RW V W => f (w + iotaW σ V W x)) = fun x => f (w + iotaW σ V W (e.symm (e x))) := by
      funext x; rw [e.symm_apply_apply]
    rw [h3]
    exact h2
  · let M : (Fin k → ℝ) →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL)
    have h2 := (H w).comp M.contDiff
    have h3 : (fun t => f (w + L t)) = fun t => f (w + iotaW σ V W (piW θ V W (L t))) := by
      funext t; rw [h.iota_pi (hL0 t)]
    rw [h3]
    exact h2
  · let M : ℝ →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL.1)
    have h2 : M (t • (1 : ℝ)) = t • M 1 := M.map_smul t 1
    rw [smul_eq_mul, mul_one] at h2
    have h3 : piW θ V W (L t) = t • piW θ V W (L 1) := h2
    rw [← h3, h.iota_pi (hL.2 t)]
  · let M : ℝ →L[ℝ] RW V W := ContinuousLinearMap.toSpanSingleton ℝ u
    exact ⟨(iotaW σ V W).comp M.toLinearMap.toAddMonoidHom,
      ⟨(h.continuous_iota V W).comp M.continuous, fun t => h.real_iota V W _⟩, fun t => rfl⟩

end GlobalTheory.FockCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare

variable {D : D7}

theorem span_tauE_eq_top {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) :
    Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) = ⊤ := by
  set S := Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) with hS
  have hθ := h.inf
  have hcl : IsClosed (S : Set (D.what₂.Tau → ℂ)) := S.closed_of_finiteDimensional
  have key : ∀ y : Ainf D.host.F ⊗[D.host.F] D.host.E, (fun τ => θ τ y) ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have : (fun τ => θ τ 0) = 0 := by funext τ; exact RingHom.map_zero _
      rw [this]; exact S.zero_mem
    | add a b ha hb =>
      have : (fun τ => θ τ (a + b)) = (fun τ => θ τ a) + fun τ => θ τ b := by
        funext τ; exact RingHom.map_add _ _ _
      rw [this]; exact S.add_mem ha hb
    | tmul a x =>
      have e : ∀ (a : Ainf D.host.F) τ, θ τ (a ⊗ₜ[D.host.F] x) =
          θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
        intro a τ
        rw [← (hθ τ).1, ← RingHom.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hc : Continuous fun a : Ainf D.host.F => fun τ => θ τ (a ⊗ₜ[D.host.F] x) := by
        refine continuous_pi fun τ => ?_
        simp only [e]
        exact (hθ τ).2.mul continuous_const
      refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
        (hcl.preimage hc) fun f => ?_
      have e1 : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
        exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
          (B := D.host.E)).commutes f |>.trans
          ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
      refine Submodule.subset_span ⟨algebraMap D.host.F D.host.E f * x, ?_⟩
      funext τ
      show tauE D τ _ = θ τ ((algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] x)
      rw [e, e1, (hθ τ).1, RingHom.map_mul]
  rw [eq_top_iff]
  intro z _
  have := key (infPart D (σ z))
  rwa [show (fun τ => θ τ (infPart D (σ z))) = z from funext fun τ => h.comp z τ] at this

theorem span_piW_ratW_eq_top (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V W : HSp D) :
    Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) = ⊤ := by
  classical
  set T := Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) with hT
  let L : Fin V.rank → Fin W.rank → (D.what₂.Tau → ℂ) →ₗ[ℝ] RW V W := fun i j =>
    { toFun := fun z τ k l => if i = k ∧ j = l then z τ else 0
      map_add' := fun x y => by funext τ k l; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by funext τ k l; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hL : ∀ i j z, L i j z ∈ T := by
    intro i j z
    have hz : z ∈ Submodule.comap (L i j) T := by
      refine (Submodule.span_le.2 ?_ : _ ≤ Submodule.comap (L i j) T) ((span_tauE_eq_top h).ge Submodule.mem_top)
      rintro _ ⟨e, rfl⟩
      refine Submodule.subset_span ⟨Matrix.single i j e, ?_⟩
      funext τ k l
      show θ τ (infPart D (incA D (Matrix.single i j e k l))) = if i = k ∧ j = l then tauE D τ e else 0
      rw [comp_incA h.inf, Matrix.single_apply]
      split_ifs
      · rfl
      · exact RingHom.map_zero _
    exact hz
  rw [eq_top_iff]
  intro z _
  have : z = ∑ i, ∑ j, L i j fun τ => z τ i j := by
    funext τ k l
    simp only [Finset.sum_apply]
    show z τ k l = ∑ i, ∑ j, if i = k ∧ j = l then z τ i j else 0
    simp [ite_and]
  rw [this]
  exact T.sum_mem fun i _ => T.sum_mem fun j _ => hL i j _

end GlobalTheory.FockCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem map_trace_tensor {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    p (Algebra.trace A (A ⊗[F] E) z) =
      Algebra.trace B (B ⊗[F] E) (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by
  have key : ∀ (C : Type) [CommRing C] [Algebra F C] (c : C) (e : E),
      Algebra.trace C (C ⊗[F] E) (c ⊗ₜ[F] e) = c * algebraMap F C (Algebra.trace F E e) := by
    intro C _ _ c e
    have h1 : (c ⊗ₜ[F] e : C ⊗[F] E) = c • ((1 : C) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul]
    congr 1
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext x
    simp
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rw [Algebra.TensorProduct.map_tmul, key, key, map_mul, AlgHom.commutes]; rfl

theorem map_sesq_sum_eq_zero {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (q : A →+* B) (σ : A →+* A)
    (hσ : ∀ z, q z = 0 → q (σ z) = 0) (a : Fin m → Fin m → A) (b : Fin n → Fin n → A)
    (x y : Matrix (Fin m) (Fin n) A) (h : x.map q = 0 ∨ y.map q = 0) :
    q (∑ i, ∑ j, ∑ k, ∑ l, σ (y i j) * a k i * b j l * x k l) = 0 := by
  have hk : ∀ i j k l (a b : A), q (σ (y i j) * a * b * x k l) = 0 := by
    intro i j k l a b
    rw [map_mul, map_mul, map_mul]
    rcases h with h | h
    · have h1 : q (x k l) = 0 := congrFun (congrFun h k) l
      rw [h1, mul_zero]
    · have h1 : q (y i j) = 0 := congrFun (congrFun h i) j
      rw [hσ _ h1, zero_mul, zero_mul, zero_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hk, Finset.sum_const_zero]

theorem map_trace_sesq_eq_zero {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (s : E →ₐ[F] E) {m n : ℕ}
    (c : A ⊗[F] E) (a : Fin m → Fin m → A ⊗[F] E) (b : Fin n → Fin n → A ⊗[F] E)
    (x y : Matrix (Fin m) (Fin n) (A ⊗[F] E))
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (Algebra.trace A (A ⊗[F] E) (c * ∑ i, ∑ j, ∑ k, ∑ l, sigR A s (y i j) * a k i * b j l * x k l)) = 0 := by
  have hc : ∀ z : A ⊗[F] E, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s z) =
      sigR B s ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero]
    | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
    | tmul a e => rfl
  have hh := map_sesq_sum_eq_zero (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s)
    (fun z hz => by rw [hc, hz, map_zero]) a b x y h
  rw [map_trace_tensor, map_mul]
  erw [hh]
  rw [mul_zero, map_zero]

variable {D : D7}

theorem map_sympl_eq_zero {B : Type} [CommRing B] [Algebra D.host.F B] (p : AF D.host.F →ₐ[D.host.F] B)
    (V W : HSp D) (x y : WA V W)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0) :
    p (sympl V W x y) = 0 := by
  unfold sympl hHom
  split_ifs
  · exact map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (V.gram k i))
      (fun j l => incA D (W.gram j l)) x y h
  · exact map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (V.gram i k))
      (fun j l => incA D (W.gram l j)) x y h

theorem sympl_parts (D : D7) (V W : HSp D) (x y : WA V W) :
    ((IsRealW V W x ∨ IsRealW V W y) → sndA D.host.F (sympl V W x y) = 0) ∧
      ((x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) → fstA D.host.F (sympl V W x y) = 0) :=
  ⟨fun h => map_sympl_eq_zero (sndA D.host.F) V W x y h, fun h => map_sympl_eq_zero (fstA D.host.F) V W x y h⟩

end GlobalTheory.FockCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare.SymplVal

theorem trace_field {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  obtain ⟨a, ha⟩ := hf (e + σ e) (by rw [map_add (f := _), hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h2, map_add (f := _), h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

theorem trace_tensor {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e)
    (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h2 σ hσ hf, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

theorem trace_AE (D : D7) (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) z) = z + cA D z :=
  trace_tensor D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e) (fun e he => (D.sp.cm.fixed e).1 he) _ z

theorem map_sum4 {A : Type} [CommRing A] (φ : A →+* ℂ) (c : A →+* A) (hc : ∀ a, φ (c a) = starRingEnd ℂ (φ a))
    {m n : ℕ} (x y : Fin m → Fin n → A) (P Q : Fin m → Fin n → Fin m → Fin n → A) :
    φ (∑ i, ∑ j, ∑ k, ∑ l, c (x i j) * P i j k l * Q i j k l * y k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (φ (x i j)) * φ (P i j k l) * φ (Q i j k l) * φ (y k l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc]

theorem comp_hHom {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W) :
    θ τ (infPart D (hHom V W x y)) = hC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  unfold hHom hC
  split_ifs
  · refine (map_sum4 ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
      (fun i j k l => incA D (V.gram k i)) (fun i j k l => incA D (W.gram j l))).trans ?_
    simp only [hi]
    rfl
  · refine (map_sum4 ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
      (fun i j k l => incA D (V.gram i k)) (fun i j k l => incA D (W.gram l j))).trans ?_
    simp only [hi]
    rfl

theorem valTau_sympl : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W),
    valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  intro D θ hθ V W τ x y
  unfold valTau sympl symplC
  rw [trace_AE, RingHom.map_add (f := _), RingHom.map_add (f := _), comp_cA hθ, RingHom.map_mul, RingHom.map_mul, comp_incA hθ,
    comp_hHom hθ, Complex.add_re, Complex.conj_re, two_mul]

end GlobalTheory.FockCompare.SymplVal
end

