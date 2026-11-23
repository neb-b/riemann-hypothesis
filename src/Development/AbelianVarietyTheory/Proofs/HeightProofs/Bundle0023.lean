module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.LiftUnitary

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {A B T : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem lift_abstract (φ : A →+* B) (p : T → A →+* ℂ) (s : (T → ℂ) → A) (c : A →+* A) (cB : B →+* B)
    (hfin : ∀ z, φ (s z) = 0) (hcomp : ∀ z τ, p τ (s z) = z τ)
    (hext : ∀ a, φ a = 0 → (∀ τ, p τ a = 0) → a = 0)
    (hc : ∀ a, φ (c a) = cB (φ a)) (hp : ∀ τ a, p τ (c a) = starRingEnd ℂ (p τ a))
    (J : Matrix n n A) (hJ : ∀ τ, (J.map (p τ)).det ≠ 0) (g : T → Matrix n n ℂ)
    (hg : ∀ τ, (g τ)ᴴ * J.map (p τ) * g τ = J.map (p τ)) :
    ∃ k : GL n A, k ∈ Formalism.UG.UJ c J ∧ Formalism.UG.bc φ k = 1 ∧ ∀ τ, (k : Matrix n n A).map (p τ) = g τ := by
  let m : (T → Matrix n n ℂ) → Matrix n n A := fun g => 1 + Matrix.of fun i j => s fun τ => (g τ - 1) i j
  have m1 : ∀ g, (m g).map φ = 1 := by
    intro g; ext i j
    simp only [m, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), hfin, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  have m2 : ∀ g τ, (m g).map (p τ) = g τ := by
    intro g τ; ext i j
    simp only [m, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), hcomp, Matrix.sub_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have mext : ∀ x y : Matrix n n A, x.map φ = y.map φ → (∀ τ, x.map (p τ) = y.map (p τ)) → x = y := by
    intro x y h1 h2
    ext i j
    rw [← sub_eq_zero]
    refine hext _ ?_ fun τ => ?_
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun (h2 τ) i) j
  have hdet : ∀ τ, IsUnit (g τ).det := by
    intro τ
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det (hg τ)
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ τ this.symm
  have o1 : (1 : Matrix n n A).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have o2 : ∀ τ, (1 : Matrix n n A).map (p τ) = 1 := fun τ => Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨m g, m fun τ => (g τ)⁻¹, ?_, ?_⟩, ?_, ?_, m2 g⟩
  · refine mext _ _ ?_ fun τ => ?_
    · rw [Matrix.map_mul, m1, m1, o1, Matrix.one_mul]
    · rw [Matrix.map_mul, m2, m2, o2, Matrix.mul_nonsing_inv _ (hdet τ)]
  · refine mext _ _ ?_ fun τ => ?_
    · rw [Matrix.map_mul, m1, m1, o1, Matrix.one_mul]
    · rw [Matrix.map_mul, m2, m2, o2, Matrix.nonsing_inv_mul _ (hdet τ)]
  · show Formalism.UG.cT c (m g) * J * m g = J
    refine mext _ _ ?_ fun τ => ?_
    · have e : (Formalism.UG.cT c (m g)).map φ = Formalism.UG.cT cB ((m g).map φ) := by
        ext i j; exact hc _
      rw [Matrix.map_mul, Matrix.map_mul, e, m1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
    · have e : (Formalism.UG.cT c (m g)).map (p τ) = ((m g).map (p τ))ᴴ := by
        ext i j; exact hp τ _
      rw [Matrix.map_mul, Matrix.map_mul, e, m2, hg]
  · apply Units.ext
    exact m1 g

end Abstract

theorem snd_sigR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (sigR (AF F) σ z) =
      sigR (Af F) σ ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul a x => rfl

theorem lift_unitary (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V : HSp D)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ∃ k ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = g τ := by
  have hJ : ∀ τ, (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    intro τ; ext i j; exact comp_incA h.inf τ _
  obtain ⟨k, hk, hf, hi⟩ := lift_abstract (finPart D) (fun τ => (θ τ).comp (infPart D)) σ (cA D)
    (sigR (Af D.host.F) D.sp.cm.sig) h.fin h.comp h.ext (snd_sigR D.sp.cm.sig) (comp_cA h.inf)
    (V.gram.map (incA D))
    (fun τ => by
      rw [hJ]
      have e : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
      rw [e]
      exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
    g (fun τ => by rw [hJ]; exact hg τ)
  exact ⟨⟨k, hk⟩, hf, hi⟩

end GlobalTheory.FockCompare.LiftUnitary

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}

theorem isThetaFun_zero : IsThetaFun ψ V W 0 := {
  quasi γ w := by simp
  level := ⟨⊤, by change IsOpen (Set.univ : Set (WA V W)); exact isOpen_univ, fun u _ _ => by funext w; simp [Heisenberg₂]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const }

theorem isThetaFun_add {f g : WA V W → ℂ} (hf : IsThetaFun ψ V W f) (hg : IsThetaFun ψ V W g) :
    IsThetaFun ψ V W (f + g) := {
  quasi γ w := by simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hU'o, hU'⟩ := hg.level
    refine ⟨U ⊓ U', by change IsOpen ((U : Set (WA V W)) ∩ (U' : Set (WA V W))); exact hUo.inter hU'o, fun u hu hinf => ?_⟩
    have e1 := hU u (AddSubgroup.mem_inf.1 hu).1 hinf
    have e2 := hU' u (AddSubgroup.mem_inf.1 hu).2 hinf
    funext w
    have h1 := congrFun e1 w
    have h2 := congrFun e2 w
    simp only [Heisenberg₂, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem isThetaFun_smul (c : ℂ) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f) :
    IsThetaFun ψ V W (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w, mul_left_comm]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hinf => ?_⟩
    funext w
    have h1 := congrFun (hU u hu hinf) w
    simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, h1]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem exists_thetaSubmodule : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D),
    ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  intro D ψ V W
  refine ⟨{ carrier := {f | IsThetaFun ψ V W f}
            add_mem' := fun hf hg => isThetaFun_add hf hg
            zero_mem' := isThetaFun_zero
            smul_mem' := fun c _ hf => isThetaFun_smul c hf }, fun f => Iff.rfl⟩

end GlobalTheory.FockCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

namespace GlobalTheory.FieldSize

theorem natAbs_discr_le_of_map_different_le (F F' L : Type) [Field F] [Field F'] [Field L]
    [NumberField F] [NumberField F'] [NumberField L] [Algebra F L] [Algebra F' L]
    (h : (differentIdeal ℤ (𝓞 F')).map (algebraMap (𝓞 F') (𝓞 L)) ≤ differentIdeal (𝓞 F) (𝓞 L)) :
    (discr L).natAbs ≤ (discr F').natAbs ^ Module.finrank F' L * (discr F).natAbs ^ Module.finrank F L := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) L (𝓞 L)]
  refine Nat.mul_le_mul_right _ ?_
  have h1 := Ideal.absNorm_dvd_absNorm_of_le h
  rw [Ideal.absNorm_algebraMap (𝓞 F') (𝓞 L), absNorm_differentIdeal F' (𝓞 F')] at h1
  have h2 : Module.finrank (𝓞 F') (𝓞 L) = Module.finrank F' L :=
    (IsFractionRing.finrank_eq (𝓞 F') F' (𝓞 L) L).symm
  rw [h2] at h1
  exact Nat.le_of_dvd (pow_pos (Int.natAbs_pos.2 (discr_ne_zero F')) _) h1

theorem log_discr_div_le (F F' L : Type) [Field F] [Field F'] [Field L]
    [NumberField F] [NumberField F'] [NumberField L] [Algebra F L] [Algebra F' L]
    (h : (differentIdeal ℤ (𝓞 F')).map (algebraMap (𝓞 F') (𝓞 L)) ≤ differentIdeal (𝓞 F) (𝓞 L)) :
    Real.log |((discr L : ℤ) : ℝ)| / Module.finrank ℚ L ≤
      Real.log |((discr F : ℤ) : ℝ)| / Module.finrank ℚ F + Real.log |((discr F' : ℤ) : ℝ)| / Module.finrank ℚ F' := by
  have h1 := natAbs_discr_le_of_map_different_le F F' L h
  have h2 : |((discr L : ℤ) : ℝ)| ≤ |((discr F' : ℤ) : ℝ)| ^ Module.finrank F' L * |((discr F : ℤ) : ℝ)| ^ Module.finrank F L := by
    have := (Nat.cast_le (α := ℝ)).2 h1
    simpa [Nat.cast_natAbs] using this
  have p : ∀ (K : Type) [Field K] [NumberField K], (0 : ℝ) < |((discr K : ℤ) : ℝ)| := fun K _ _ =>
    abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have h3 := Real.log_le_log (p L) h2
  rw [Real.log_mul (pow_pos (p F') _).ne' (pow_pos (p F) _).ne', Real.log_pow, Real.log_pow] at h3
  have e1 : (Module.finrank ℚ L : ℝ) = Module.finrank ℚ F * Module.finrank F L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F L).symm
  have e2 : (Module.finrank ℚ L : ℝ) = Module.finrank ℚ F' * Module.finrank F' L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F' L).symm
  have q : ∀ (K : Type) [Field K] [NumberField K], (0 : ℝ) < Module.finrank ℚ K := fun K _ _ => by
    exact_mod_cast Module.finrank_pos
  have qL := q L
  have qF := q F
  have qF' := q F'
  rw [div_le_iff₀ qL, add_mul]
  have a1 : Real.log |((discr F : ℤ) : ℝ)| / Module.finrank ℚ F * Module.finrank ℚ L =
      Module.finrank F L * Real.log |((discr F : ℤ) : ℝ)| := by
    rw [e1]; field_simp
  have a2 : Real.log |((discr F' : ℤ) : ℝ)| / Module.finrank ℚ F' * Module.finrank ℚ L =
      Module.finrank F' L * Real.log |((discr F' : ℤ) : ℝ)| := by
    rw [e2]; field_simp
  rw [a1, a2]; linarith

theorem sz_sup : ∀ (F F' : IntermediateField ℚ ℂ) (a b a' b' : ℝ), Sz F a b → Sz F' a' b' → Sz (F ⊔ F') (a + a') (b + b') := by
  rintro F F' a b a' b' ⟨i1, ha, hb⟩ ⟨i2, ha', hb'⟩
  haveI i3 : FiniteDimensional ℚ ↥(F ⊔ F') := IntermediateField.finiteDimensional_sup F F'
  letI : NumberField F := NumberField.mk
  letI : NumberField F' := NumberField.mk
  letI : NumberField ↥(F ⊔ F') := NumberField.mk
  refine ⟨i3, ?_, ?_⟩
  · have h1 : (Module.finrank ℚ ↥(F ⊔ F') : ℝ) ≤ Module.finrank ℚ F * Module.finrank ℚ F' := by
      exact_mod_cast IntermediateField.finrank_sup_le F F'
    have q : ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], (0 : ℝ) < Module.finrank ℚ K := fun K _ => by
      exact_mod_cast Module.finrank_pos
    have h2 := Real.log_le_log (q _) h1
    rw [Real.log_mul (q F).ne' (q F').ne'] at h2
    linarith
  · letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    letI : Algebra F' ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    have h := log_discr_div_le F F' ↥(F ⊔ F') (GlobalTheory.T.map_different_le_different_sup_intermediateField F F')
    exact h.trans (add_le_add hb hb')

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockBasisMatrix

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_basis (S : HSpace E) (Q : Matrix (Fin S.rank) (Fin S.rank) E) (hQ : IsUnit Q.det) :
    ∃ b : Module.Basis (Fin S.rank) E S.V, Q = S.frame.toMatrix b := by
  refine ⟨S.frame.map (Matrix.toLinearEquiv S.frame Q hQ), ?_⟩
  ext i j
  simp [Module.Basis.toMatrix_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Finsupp.single_apply]

theorem isUnit_det (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) : IsUnit (S.frame.toMatrix b).det := by
  letI := Module.Basis.invertibleToMatrix S.frame b
  exact Matrix.isUnit_det_of_invertible _

theorem gram_change (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (i j : Fin S.rank) :
    (((S.frame.toMatrix b).map star)ᵀ * S.gram * S.frame.toMatrix b) i j = S.hT (b i) (b j) := by
  conv_rhs => rw [← S.frame.sum_repr (b i), ← S.frame.sum_repr (b j)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, HSpace.gram,
    map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem diag_ne_zero (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V)
    (ho : ∀ i j, i ≠ j → S.hT (b i) (b j) = 0) (i : Fin S.rank) : S.hT (b i) (b i) ≠ 0 := by
  intro h0
  refine b.ne_zero i (S.nondeg.2 _ fun x => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
  by_cases hk : k = i
  · rw [hk, h0, smul_zero]
  · rw [ho k i hk, smul_zero]

theorem diag_real (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) (x : S.V) :
    (((τ (S.hT x x)).re : ℝ) : ℂ) = τ (S.hT x x) := by
  rw [← Complex.conj_eq_iff_re, ← hτ]
  exact congrArg τ (S.herm.eq x x)

theorem toMatrix_mul_diag (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (s : Module.End E S.V)
    (c : Fin S.rank → E) (hs : ∀ i, s (b i) = c i • b i) :
    LinearMap.toMatrix S.frame S.frame s * S.frame.toMatrix b = S.frame.toMatrix b * Matrix.diagonal c := by
  rw [linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  rw [Matrix.mul_diagonal, LinearMap.toMatrix_apply, hs, Module.Basis.toMatrix_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_comm]

theorem orthogonal_basis (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V)
    (ho : ∀ i j, i ≠ j → S.hT (b i) (b j) = 0) (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) :
    (∀ i, (τ (S.hT (b i) (b i))).re ≠ 0) ∧
    ((S.frame.toMatrix b).map τ)ᴴ * S.gram.map τ * (S.frame.toMatrix b).map τ =
      Matrix.diagonal (fun i => (((τ (S.hT (b i) (b i))).re : ℝ) : ℂ)) ∧
    ∀ s : Module.End E S.V, (∀ i, s (b i) = if 0 < (τ (S.hT (b i) (b i))).re then b i else -b i) →
      (LinearMap.toMatrix S.frame S.frame s).map τ * (S.frame.toMatrix b).map τ =
        (S.frame.toMatrix b).map τ * Matrix.diagonal (fun i => if 0 < (τ (S.hT (b i) (b i))).re then (1 : ℂ) else -1) := by
  refine ⟨fun i h => ?_, ?_, fun s hs => ?_⟩
  · have := diag_real S τ hτ (b i)
    rw [h, Complex.ofReal_zero] at this
    exact diag_ne_zero S b ho i ((map_eq_zero τ).1 this.symm)
  · have e : ((S.frame.toMatrix b).map τ)ᴴ = (((S.frame.toMatrix b).map star)ᵀ).map τ := by
      ext i j
      simp [Matrix.conjTranspose_apply, hτ]
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    rw [Matrix.map_apply, gram_change]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, diag_real S τ hτ]
    · rw [Matrix.diagonal_apply_ne _ hij, ho i j hij, map_zero]
  · have h := toMatrix_mul_diag S b s (fun i => if 0 < (τ (S.hT (b i) (b i))).re then (1 : E) else -1)
      (fun i => by rw [hs i]; split_ifs <;> simp)
    rw [← Matrix.map_mul, h, Matrix.map_mul, Matrix.diagonal_map (map_zero τ)]
    congr 2
    funext i
    split_ifs <;> simp

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem basis_matrix : ∀ (D : D7) (V : HSp D), (∀ Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E, IsUnit Q.det → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Q = V.frame.toMatrix b) ∧ ∀ b : Module.Basis (Fin V.rank) D.host.E V.V, IsUnit (V.frame.toMatrix b).det ∧ (∀ i j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b) i j = V.hT (b i) (b j)) ∧ ((∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ τ : D.what₂.Tau, (∀ i, (tauE D τ (V.hT (b i) (b i))).re ≠ 0) ∧ ((V.frame.toMatrix b).map (tauE D τ))ᴴ * gramAt D V τ * (V.frame.toMatrix b).map (tauE D τ) = Matrix.diagonal (fun i => (((tauE D τ (V.hT (b i) (b i))).re : ℝ) : ℂ)) ∧ ∀ s : Module.End D.host.E V.V, (∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i) → thAt V τ s * (V.frame.toMatrix b).map (tauE D τ) = (V.frame.toMatrix b).map (tauE D τ) * Matrix.diagonal (fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then (1 : ℂ) else -1)) := by
  intro D V
  exact ⟨exists_basis V, fun b => ⟨isUnit_det V b, gram_change V b,
    fun ho τ => orthogonal_basis V b ho (tauE D τ) (tauE_star τ)⟩⟩

end GlobalTheory.FockBasisMatrix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelation
section
noncomputable section

open scoped ContDiff

namespace GlobalTheory.FockCompare

section

variable {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
  {ι : R →+ G} {π : G →+ R} {om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ}


omit [FiniteDimensional ℝ R] in
theorem heisComm_coset (hπ : ∀ x, π (ι x) = x)
    (hf : ∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u)
    (f : G → ℂ) (h : Sm ι f) (v : R) (w : G) :
    (fun x : R => hD ι π om v f (w + ι x)) = fun x : R =>
      -(Real.pi * Complex.I) * (om (π w + x) v : ℝ) * f (w + ι x) + fderiv ℝ (fun y : R => f (w + ι y)) x v := by
  funext x
  rw [hf f h, map_add (f := _), hπ]
  congr 2
  have e : (fun y : R => f (w + ι x + ι y)) = fun y : R => (fun z : R => f (w + ι z)) (x + y) := by
    funext y; simp only [map_add (f := _), add_assoc]
  rw [e, fderiv_comp_add_left (f := fun z : R => f (w + ι z)), add_zero]

theorem heisComm_hasFDerivAt_om (a v x : R) :
    HasFDerivAt (fun x : R => ((om (a + x) v : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))) x := by
  have h := (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))).hasFDerivAt (x := a + x)
  have h2 := h.comp x ((hasFDerivAt_id x).const_add a)
  rw [ContinuousLinearMap.comp_id] at h2
  exact h2

theorem heisComm_contDiff_om (a v : R) : ContDiff ℝ ∞ (fun x : R => ((om (a + x) v : ℝ) : ℂ)) :=
  (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))).contDiff.comp
    (contDiff_const.add contDiff_id)

theorem heisComm_second (hπ : ∀ x, π (ι x) = x)
    (hf : ∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u)
    (f : G → ℂ) (h : Sm ι f) (u v : R) (w : G) :
    hD ι π om u (hD ι π om v f) w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) *
        (-(Real.pi * Complex.I) * (om (π w) v : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 v) +
      (-(Real.pi * Complex.I) * (om u v : ℝ) * f w +
        -(Real.pi * Complex.I) * (om (π w) v : ℝ) * fderiv ℝ (fun x : R => f (w + ι x)) 0 u +
        fderiv ℝ (fderiv ℝ (fun x : R => f (w + ι x))) 0 u v) := by
  have hfd : ∀ w', ContDiff ℝ ∞ (fderiv ℝ (fun x : R => f (w' + ι x))) := fun w' =>
    (h w').fderiv_right (m := ∞) (by simp)
  have hs : Sm ι (hD ι π om v f) := by
    intro w'
    rw [heisComm_coset hπ hf f h v w']
    exact ((contDiff_const.mul (heisComm_contDiff_om _ _)).mul (h w')).add
      ((hfd w').clm_apply contDiff_const)
  rw [hf _ hs, hf f h v w, heisComm_coset hπ hf f h v w]
  congr 1
  have h1 : HasFDerivAt (fun x : R => f (w + ι x)) (fderiv ℝ (fun x : R => f (w + ι x)) 0) 0 :=
    ((h w).differentiable (by simp) 0).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ (fun x : R => f (w + ι x))) (fderiv ℝ (fderiv ℝ (fun x : R => f (w + ι x))) 0) 0 :=
    ((hfd w).differentiable (by simp) 0).hasFDerivAt
  have h3 := ((((heisComm_hasFDerivAt_om (om := om) (π w) v 0).const_mul (-(Real.pi * Complex.I))).mul h1).add
    (h2.clm_apply (hasFDerivAt_const v 0))).fderiv
  have h4 := congrArg (fun L => L u) h3
  refine Eq.trans h4 ?_
  simp
  ring

end

theorem heisenberg_derivative_commutator :
    ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
      (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) →
      (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
        -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) →
      (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → ∀ u v : R,
      hD ι π om u (hD ι π om v f) - hD ι π om v (hD ι π om u f) =
        (-(2 * Real.pi * Complex.I) * (om u v : ℝ)) • f := by
  intro G R _ _ _ _ ι π om hπ hf ha f h u v
  funext w
  have hsym : IsSymmSndFDerivAt ℝ (fun x : R => f (w + ι x)) 0 :=
    (h w).contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [Pi.sub_apply, heisComm_second hπ hf f h u v, heisComm_second hπ hf f h v u, hsym u v, ha u v]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end GlobalTheory.FockCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeQuasiInvariantAndLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem dRho_quasi_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  intro D ψ V W L f
  refine ⟨fun hf γ w => ?_, fun u hu hf => ?_⟩
  · unfold dRho
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    exact GlobalTheory.DualPairCheck.heis_quasi ψ V W (L t) f hf γ w
  · funext w
    have key : ∀ t, Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) = Heisenberg₂ ψ V W (L t) f := by
      intro t
      conv_rhs => rw [← hf]
      rw [GlobalTheory.DualPairCheck.heis_heis, GlobalTheory.DualPairCheck.heis_heis, (hu t).1, (hu t).2, add_comm]
    have : (fun t => Heisenberg₂ ψ V W (L t) f w) = fun t => Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) w := by
      funext t; rw [key]
    conv_rhs => unfold dRho; rw [this]
    unfold dRho
    rw [Heisenberg₂, ← deriv_const_mul_field]
    rfl

end GlobalTheory.FockCompare
end

