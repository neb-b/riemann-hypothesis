module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0054
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0028
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0062
public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0036
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAdaptedAt
section
namespace UpperTheory.Reformulated.B.Gwb8

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict GroundTheory.Automorphic
  GroundTheory.Heights₂.Heights.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ}

omit [IsCMField E] in
private theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

omit [IsCMField E] in
private theorem embOf_comp (s : 𝓞 E →+* ℂ) : (embOf s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext fun a => embOf_coe s a

omit [IsCMField E] in
private theorem embOf_eq_iff (s : 𝓞 E →+* ℂ) (t : E →+* ℂ) :
    embOf s = t ↔ s = t.comp (algebraMap (𝓞 E) E) := by
  constructor
  · rintro rfl
    exact (embOf_comp s).symm
  · rintro rfl
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (embOf_comp _)

private theorem trace_sum (F : UnivFam E Ψ j j' n g Λ) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ, 2 * (embOf (F.σ τ) x).re := by
  refine UpperTheory.trace_eq_sum_re_cm_type (fun τ => embOf (F.σ τ)) ?_ ?_ x
  · intro a b hab
    apply F.cm.1
    rw [← embOf_comp (F.σ a), ← embOf_comp (F.σ b)]
    exact congrArg (fun t : E →+* ℂ => t.comp (algebraMap (𝓞 E) E)) hab
  · intro s
    simp only [embOf_eq_iff, RingHom.comp_assoc]
    exact F.cm.2 _

private theorem vec_bas (C : LatEmb F) (k : Fin (2 * g)) : C.bas k = C.vec (C.lam k) := by
  funext τ i
  exact C.bas_eq k τ i

private theorem per_vec (C : LatEmb F) (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  let v : Λ →+ (Ψ → Fin (j + j') → ℂ) :=
    { toFun := C.vec
      map_zero' := by funext τ i; simp [LatEmb.vec]
      map_add' := fun a b => by funext τ i; simp [LatEmb.vec] }
  have key : ((C.perExt R).toAddMonoidHom.comp v).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    change C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [← vec_bas, LatEmb.perExt, Module.Basis.constr_basis]
  exact LinearMap.congr_fun key x

private theorem per_act (C : LatEmb F) (R : RiemLat E g Λ) (a : 𝓞 E) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R (fun τ => F.σ τ a • y τ) = R.B a (C.perExt R y) := by
  let D : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) :=
    { toFun := fun y τ => F.σ τ a • y τ
      map_add' := fun y y' => by funext τ; simp
      map_smul' := fun r y => by funext τ; simp [smul_comm r] }
  have key : (C.perExt R).comp D = ((R.B a).restrictScalars ℝ).comp (C.perExt R) := by
    refine C.bas.ext fun k => ?_
    change C.perExt R (fun τ => F.σ τ a • C.bas k τ) = R.B a (C.perExt R (C.bas k))
    rw [vec_bas, per_vec, ← R.act, ← per_vec C]
    congr 1
    funext τ i
    simp [LatEmb.vec, C.e_smul, embOf_coe]
  exact LinearMap.congr_fun key y

private theorem sesq_emb (C : LatEmb F) (τ : Ψ) (x y : Λ) :
    embOf (F.σ τ) (C.h.toSesq (C.e y) (C.e x)) = star (C.vec y τ) ⬝ᵥ (C.gr τ *ᵥ C.vec x τ) := by
  rw [sesq_eq_sum C.h.toSesq (Pi.basisFun E (Fin (j + j')))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, embedding_conj, Pi.basisFun_repr, dotProduct, mulVec, Finset.mul_sum,
    LatEmb.gr, LatEmb.vec, Matrix.map_apply, Pi.star_apply, mul_assoc]
  rfl

private theorem per_im (C : LatEmb F) (R : RiemLat E g Λ) (hR : R.form = F.form)
    (y y' : Ψ → Fin (j + j') → ℂ) :
    (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y' := by
  let b₁ : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y y' => (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im)
      (fun a b c => by simp [add_dotProduct])
      (fun r a c => by simp [smul_dotProduct])
      (fun a b c => by simp [mulVec_add, dotProduct_add])
      (fun r a c => by simp [star_smul, mulVec_smul, dotProduct_smul])
  let b₂ : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y y' => C.Fm y y')
      (fun a b c => by
        simp only [LatEmb.Fm, Pi.add_apply, mulVec_add, dotProduct_add, mul_add, Complex.add_re,
          Finset.sum_add_distrib])
      (fun r a c => by
        simp only [LatEmb.Fm, Pi.smul_apply, mulVec_smul, dotProduct_smul, mul_smul_comm, Complex.smul_re,
          Finset.smul_sum])
      (fun a b c => by
        simp only [LatEmb.Fm, Pi.add_apply, star_add, add_dotProduct, mul_add, Complex.add_re,
          Finset.sum_add_distrib])
      (fun r a c => by
        simp only [LatEmb.Fm, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct, mul_smul_comm,
          Complex.smul_re, Finset.smul_sum])
  have key : b₁ = b₂ := by
    refine LinearMap.ext_basis C.bas C.bas fun k l => ?_
    change (C.perExt R (C.bas k) ⬝ᵥ R.Hm *ᵥ star (C.perExt R (C.bas l))).im = C.Fm (C.bas k) (C.bas l)
    rw [vec_bas, vec_bas, per_vec, per_vec, R.im, hR]
    have h1 := congrArg (fun q : ℚ => (q : ℝ)) (C.form_eq (C.lam k) (C.lam l))
    simp only [Rat.cast_intCast] at h1
    rw [h1, trace_sum F]
    simp only [LatEmb.Fm, map_mul, sesq_emb]
  exact LinearMap.congr_fun₂ key y y'

private theorem gr_herm (C : LatEmb F) (τ : Ψ) : (C.gr τ).IsHermitian := by
  have h := isHermitianFor_gram C.h (Pi.basisFun E (Fin (j + j')))
  ext a b
  have h1 := congrArg (embOf (F.σ τ)) (congrFun (congrFun h a) b)
  simp only [transpose_apply, Matrix.map_apply] at h1
  simp only [conjTranspose_apply, LatEmb.gr, Matrix.map_apply]
  rw [← h1]
  exact (embedding_conj (embOf (F.σ τ)) _).symm

private theorem sgr_herm (C : LatEmb F) (τ : Ψ) : (C.sgr τ).IsHermitian := by
  unfold LatEmb.sgr Matrix.IsHermitian
  rw [conjTranspose_smul, (gr_herm C τ).eq]
  simp

private theorem sgr_unit (C : LatEmb F) (τ : Ψ) : IsUnit (C.sgr τ).det := by
  have h := (isUnit_det_gram C.h (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))
  rw [RingHom.map_det] at h
  have he : C.eps τ ≠ 0 := by
    intro h0
    have := C.eps_sq τ
    rw [h0] at this
    norm_num at this
  rw [LatEmb.sgr, det_smul]
  exact (IsUnit.mk0 _ (pow_ne_zero _ (Complex.ofReal_ne_zero.2 he))).mul h

open Classical in
private theorem per_single (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ) (a : 𝓞 E) (y : Fin (j + j') → ℂ) :
    R.B a (C.perExt R (Pi.single τ y)) =
      (F.σ τ a).re • C.perExt R (Pi.single τ y) +
        (F.σ τ a).im • C.perExt R (Pi.single τ (Complex.I • y)) := by
  rw [← per_act, ← map_smul, ← map_smul, ← map_add (f := _)]
  congr 1
  funext τ'
  by_cases h : τ' = τ
  · subst h
    funext i
    simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im (F.σ τ' a)]
    ring
  · simp [Pi.single_eq_of_ne h]

end UpperTheory.Reformulated.B.Gwb8

open UpperTheory.Reformulated.B.Gwb8 Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict in
theorem UpperTheory.Reformulated.B.Gwb8.exists_adapted_at :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {Ψ : Type}
      [inst_3 : Fintype Ψ] {j j' n g : ℕ} {Λ : Type} [inst_4 : AddCommGroup Λ]
      [inst_5 : _root_.Module (NumberField.RingOfIntegers E) Λ] {F : GlobalTheory.CompanionTheory.Ar.Cusp.UnivFam E Ψ j j' n g Λ}
      (C : GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmb F) (R : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ),
      R.form = F.form →
        R.HasSig F.σ j j' →
          ∀ (τ : Ψ),
            ∃ (A : Matrix (Fin (j + j')) (GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Sg j j') ℂ),
              A.conjTranspose * C.sgr τ * A = GlobalTheory.CompanionTheory.Ar.Cusp.Dict.sgI j j' ∧
                (∀ (v : Fin j → ℂ), C.pPart R τ (A.mulVec (Sum.elim v (0 : Fin j' → ℂ))) = (0 : Fin g → ℂ)) ∧
                  ∀ (v : Fin j' → ℂ), C.pBar R τ (A.mulVec (Sum.elim (0 : Fin j → ℂ) v)) = (0 : Fin g → ℂ) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R hR hs τ
  classical
  let p : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (C.perExt R).comp (LinearMap.single ℝ (fun _ : Ψ => Fin (j + j') → ℂ) τ)
  have hp : ∀ y, p y = C.perExt R (Pi.single τ y) := fun _ => rfl
  have hB : ∀ a y, R.B a (p y) = ((F.σ τ a).re : ℂ) • p y + ((F.σ τ a).im : ℂ) • p (Complex.I • y) :=
    fun a y => per_single C R τ a y
  have hI : ∀ y : Fin (j + j') → ℂ, p (Complex.I • Complex.I • y) = -p y := fun y => by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  obtain ⟨K, K', h1, h2, h3, h4, h5, h6, h7⟩ := UpperTheory.hermitian_positive_symplectic p R.Hm (C.sgr τ) C.c
    (eigSp R.B (F.σ τ)) (eigSp R.B ((starRingEnd ℂ).comp (F.σ τ))) R.pos (sgr_unit C τ) C.c_pos
    (fun y y' => by
      rw [hp, hp, per_im C R hR, LatEmb.Fm, Finset.sum_eq_single τ]
      · simp only [Pi.single_eq_same, C.xi_eq, LatEmb.sgr, smul_mulVec, dotProduct_smul, smul_eq_mul,
          Complex.ofReal_mul, mul_assoc]
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp)
    (hs τ).1 (hs τ).2
    (fun y => by
      simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_sub, map_smul, hB, hI]
      intro a
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul]
      have e := Complex.re_add_im (F.σ τ a)
      linear_combination (p y i - Complex.I * p (Complex.I • y) i) * e +
        (((F.σ τ a).im : ℂ) * p (Complex.I • y) i) * Complex.I_mul_I)
    (fun y => by
      simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_add, map_smul, hB, hI]
      intro a
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul,
        RingHom.comp_apply]
      have e : ((F.σ τ a).re : ℂ) - ((F.σ τ a).im : ℂ) * Complex.I = starRingEnd ℂ (F.σ τ a) := by
        apply Complex.ext <;> simp
      linear_combination (p y i + Complex.I * p (Complex.I • y) i) * e +
        (((F.σ τ a).im : ℂ) * p (Complex.I • y) i) * Complex.I_mul_I)
  obtain ⟨A, hA, hK, hK'⟩ := UpperTheory.signature_block_diagonal (C.sgr τ) K K' (sgr_herm C τ) h1 h2 h5 h6 h7
  refine ⟨A, hA, fun v => ?_, fun v => ?_⟩
  · have := h3 _ (hK v)
    rw [hp, hp] at this
    rw [LatEmb.pPart]
    convert smul_zero (1 / 2 : ℂ)
  · have := h4 _ (hK' v)
    rw [hp, hp] at this
    rw [LatEmb.pBar]
    convert smul_zero (1 / 2 : ℂ)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExportFamilies
section
theorem UpperTheory.Reformulated.B.ExportFamilies.K_repr :
    ∀ (D : Formalism.L2.Ker.Car),
    ∀ x ∈ D.host.K,
      ∃ (p : ℚ) (q : ℚ),
        x =
          (↑p : D.host.E) +
            (↑q : D.host.E) *
              D.host.sqd := by
  intro D x hx
  have hs := D.host.sqd_sq
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqd} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) D.host.sqd)]
    exact hx
  refine Algebra.adjoin_induction (p := fun x _ => ∃ p q : ℚ, x = (p : D.host.E) + q * D.host.sqd)
    (fun y hy => ⟨0, 1, by simpa using hy⟩) (fun r => ⟨r, 0, by simp⟩) ?_ ?_ hx'
  · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by push_cast; ring⟩
  · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a * c - D.host.d * (b * e), a * e + b * c, by
      push_cast; linear_combination ((b : D.host.E) * e) * hs⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterion
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterion.be :
    Formalism.L2.Ker.Car → ℂ :=
    fun (D : Formalism.L2.Ker.Car) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterion.OKc :
    Formalism.L2.Ker.Car → ℂ → Prop :=
    fun (D : Formalism.L2.Ker.Car) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterion.be D) / (2 : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of :
    ∀ (D : Formalism.L2.Ker.Car) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterion.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hφ : D.host.φ₀ D.host.sqd = Complex.I * ((Real.sqrt (D.host.d : ℝ) : ℝ) : ℂ) := D.host.φ₀_mem
  obtain ⟨a, b, hab⟩ := UpperTheory.adjoin_sqrt_eq_rat_span D.host.E D.host.d D.host.sqd D.host.sqd_sq
    ((u : D.host.K) : D.host.E) (u : D.host.K).2
  have hval : D.host.φ₀ ((u : D.host.K) : D.host.E)
      = (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (D.host.d : ℝ) : ℝ) : ℂ)) := by
    rw [hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hφ]
  have hint : IsIntegral ℤ (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
    (u.isIntegral_coe).map
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  rw [hval] at hint
  obtain ⟨x, y, hxy, h⟩ := UpperTheory.integral_quadratic_half_int D.host.d D.host.hyp.2.1 a b hint
  exact ⟨x, y, hxy, hval.trans h⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StarSqrtNeg
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma conj_eq_neg_of_sq {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ 2 = -(n : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exfalso; rw [h1] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hz]

theorem UpperTheory.Reformulated.B.StarSqrtNeg.star_sqrt_neg :
    ∀ {D : Formalism.L2.Ker.Car} (x : D.host.E) (n : ℕ),
    (0 : ℕ) < n →
      x ^ (2 : ℕ) = -(↑n : D.host.E) →
        Star.star x =
          -x := by
  intro D x n hn h
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  apply φ.injective
  have key : φ (Star.star x) = (starRingEnd ℂ) (φ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x
  have hsq : (φ x) ^ 2 = -(n : ℂ) := by
    have := congrArg φ h
    simpa using this
  rw [key, map_neg]
  exact conj_eq_neg_of_sq hn hsq
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VanishKfLow
section
noncomputable def UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.KfLow :
    {D : Formalism.BasicNotions.D7} →
      {V : Formalism.BasicNotions.TH.HSp D} →
        {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} → (M : Formalism.IndefR.Mult.DSModel V S) → (τ : D.what₂.Tau) → Submodule ℂ ↥(M.sm τ) :=
    fun {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : Formalism.IndefR.Mult.DSModel V S)
        (τ : D.what₂.Tau) ↦
      Submodule.span ℂ
        {w : ↥(M.sm τ) |
          ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
            ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)), (↑w : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical in
private theorem UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.equiv_of_mem
    {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ)
    (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (Formalism.L2.Theta.GA D V)) (χ : Formalism.L2.Theta.GA D V → ℂ)
    {T : Formalism.IndefR.Mult.MMap M} (hT : T ∈ Formalism.IndefR.Mult.Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ))
    (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    ∃ k : Formalism.L2.Theta.GA D V, ∀ x : Formalism.L2.Theta.GA D V, T (Function.update v τ w) x = T v (x * k) := by
  refine ⟨Formalism.L2.Theta.atTau θ V τ g, ?_⟩
  unfold Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem U hU => intro x; exact congrFun (hU.equiv τ g hg v w hw) x
  | zero => intro x; rfl
  | add U U' _ _ h h' =>
    intro x
    show U (Function.update v τ w) x + U' (Function.update v τ w) x = U v _ + U' v _
    rw [h x, h' x]
  | smul a U _ h =>
    intro x
    show a • U (Function.update v τ w) x = a • U v _
    rw [h x]

theorem UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.vanish_KfLow :
    ∀ {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
      (θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ)
      (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (Formalism.L2.Theta.GA D V)) (χ : Formalism.L2.Theta.GA D V → ℂ)
      {T : Formalism.IndefR.Mult.MMap M},
      T ∈ Formalism.IndefR.Mult.Mult θ M J χ →
        (∀ (v : (ρ : D.what₂.Tau) → ↥(Formalism.IndefR.Links.lowT M ρ)),
            ((T : ((i : D.what₂.Tau) → ↥(M.sm i)) → Formalism.L2.Theta.GA D V → ℂ) fun (ρ : D.what₂.Tau) ↦ (↑(v ρ) : ↥(M.sm ρ))) =
              (0 : Formalism.L2.Theta.GA D V → ℂ)) →
          ∀ (s : Finset D.what₂.Tau) (v : M.Vec),
            (∀ τ ∈ s, v τ ∈ UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.KfLow M τ) →
              (∀ τ ∉ s,
                  ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
                    ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)),
                      (↑(v τ) : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)) →
                (T : ((i : D.what₂.Tau) → ↥(M.sm i)) → Formalism.L2.Theta.GA D V → ℂ) v = (0 : Formalism.L2.Theta.GA D V → ℂ) := by
  intro D V S θ M J χ T hT h0 s v hs hns
  classical
  refine UpperTheory.multilinear_vanish_lattice T (fun τ => (Formalism.IndefR.Links.lowT M τ : Set (M.sm τ)))
    (fun τ => {w : ↥(M.sm τ) |
          ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
            ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)), (↑w : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)})
    (fun u hu => h0 (fun ρ => ⟨u ρ, hu ρ⟩)) ?_ v ?_
  · rintro τ w ⟨g, hg, w0, hw⟩
    refine ⟨w0.1, w0.2, fun u hu => ?_⟩
    obtain ⟨k, hk⟩ := UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.equiv_of_mem θ M J χ hT τ g hg (Function.update u τ w0.1) w
      (by rw [Function.update_self]; exact hw)
    funext x
    have h1 := hk x
    rw [Function.update_idem] at h1
    have h2 : T (Function.update u τ w) x = T (Function.update u τ w0.1) (x * k) := by convert h1
    rw [h2, hu]
    rfl
  · intro τ
    by_cases h : τ ∈ s
    · exact hs τ h
    · exact Submodule.subset_span (hns τ h)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightThresholdDefs
section
private theorem UpperTheory.Reformulated.B.WeightThresholdDefs.core {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} (h : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ n : NumberField.RingOfIntegers K, n ≠ 0 ∧ (n : K) • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := h ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K (L : Set V) x hx
  refine ⟨t, nonZeroDivisors.coe_ne_zero t, ?_⟩
  rw [Submodule.span_eq, Submonoid.smul_def] at ht
  have : ((t : NumberField.RingOfIntegers K) : K) • x = (t : NumberField.RingOfIntegers K) • x :=
    algebraMap_smul K (t : NumberField.RingOfIntegers K) x
  rw [this]
  exact ht

theorem UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem :
    ∀ {D : Formalism.L2.Ker.Car} {N : ℕ}
    {L₁ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E)},
    Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) = ⊤ →
      ∀ (x : Fin N → D.host.E),
        ∃ (n : NumberField.RingOfIntegers D.host.E),
          n ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑n : D.host.E) • x ∈
              L₁ := by
  intro D N L₁ h x
  exact UpperTheory.Reformulated.B.WeightThresholdDefs.core h x
end

