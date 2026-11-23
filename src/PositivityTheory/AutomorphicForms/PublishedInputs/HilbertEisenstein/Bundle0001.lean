module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Qminor
public import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
public import GroundTheory.GlobalFields.TateThesis.Bundle0009
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import GroundTheory.GlobalFields.TateThesis.Bundle0008
public import GroundTheory.GlobalFields.TateThesis.TraceLatticePoisson
public import GroundTheory.GlobalFields.TateThesis.AdelePoisson

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CenterFinitenessHolds
section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : ∀ (z : Ideles F) (g : GA F 2), φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

theorem UpperTheory.HilbertEisensteinWeightOne.center_finiteness_holds : SPois → SInt → SSmooth → SZfin := by
  intro _ _ _ F _ _ _ ω c hω φ hc hw hl
  have hcap : ∀ v u, ∃ c : ℂ, TR.cap v u φ = c • φ := fun v u => by
    have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
      classical
      rw [← lie_scalar hω hc (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have := casimir _ (TR.glRel_Eop v) ((1 : ℕ) : ℂ) φ h0 (hw v) (hl v) u
    refine ⟨_, Eq.trans ?_ this⟩
    rw [TR.cap]
    norm_num
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, u, rfl⟩ := hx
    obtain ⟨c, e⟩ := hcap v u
    exact Submodule.mem_span_singleton.2 ⟨c, e.symm⟩
  | algebraMap c => exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 hy
    have e' : c • φ = y φ := e
    change x (y φ) ∈ Submodule.span ℂ {φ}
    rw [← e', map_smul]
    exact Submodule.smul_mem _ _ hx
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CentralCharacterHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

namespace EisensteinCentralCharacter

variable {F : Type} [Field F] [NumberField F]

theorem thetaS_scalar_diagonal (Ψ : (Fin 2 → Ad F) → ℂ) (k : Fˣ) (h : GA F 2) :
    thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k : Ideles F) * h) = thetaS Ψ h := by
  unfold thetaS
  let e : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} :=
    { toFun := fun ξ => ⟨(k : F) • ξ.1, smul_ne_zero k.ne_zero ξ.2⟩
      invFun := fun ξ => ⟨((k⁻¹ : Fˣ) : F) • ξ.1, smul_ne_zero (k⁻¹).ne_zero ξ.2⟩
      left_inv := fun ξ => Subtype.ext (by simp [smul_smul])
      right_inv := fun ξ => Subtype.ext (by simp [smul_smul]) }
  have key : ∀ ξ : Fin 2 → F,
      rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k : Ideles F) * h : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) = rowA ((k : F) • ξ) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)) := by
    intro ξ
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    congr 1
    funext i
    rw [Matrix.vecMul_diagonal]
    simp [rowA, coe_diagonal, mul_comm]
  refine Eq.trans ?_ (e.tsum_eq fun ξ => Ψ (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))))
  exact tsum_congr fun ξ => by rw [key]; rfl

theorem hchar_diagonal (ω : HChar F) (k : Fˣ) : ω.1 (diagonal F k) = 1 := ω.2.2 k

theorem absD_nonneg (g : GA F 2) : 0 ≤ absD g := (IdeleGroup.ideleModule F _).2.le

theorem absD_scalar_mul (z : Ideles F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
      ((IdeleGroup.ideleModule F z : ℝ)) ^ 2 * absD g := by
  unfold absD
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_pow]
  rfl

theorem eisInt_mul_diag [IsTotallyReal F] (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) (k : Fˣ) :
    eisInt ω Ψ g t (u * diagonalToNormOne F k) = eisInt ω Ψ g t u := by
  unfold eisInt
  have h : moduleSection (w0 F) t * ((u * diagonalToNormOne F k : normOneSubgroup F) : Ideles F) =
      diagonal F k * (moduleSection (w0 F) t * (u : Ideles F)) := by
    rw [Subgroup.coe_mul, coe_diagonalToNormOne]
    ac_rfl
  rw [h, map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)),
    mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k)), thetaS_scalar_diagonal,
    map_mul ω.1, hchar_diagonal, one_mul]

theorem eisInt_scalar [IsTotallyReal F] (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (z : Ideles F) (g : GA F 2)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt ω Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) t u =
      ((ω.1 z : ℂˣ) : ℂ) * eisInt ω Ψ g (t * (normOneSplitting (w0 F) z).2)
        (u * (normOneSplitting (w0 F) z).1) := by
  set p := normOneSplitting (w0 F) z with hp
  have hz : z = (p.1 : Ideles F) * moduleSection (w0 F) p.2 := by
    rw [← normOneSplitting_symm_apply, hp, ContinuousMulEquiv.symm_apply_apply]
  have ht0 : (p.2 : ℝ) = (IdeleGroup.ideleModule F z : ℝ) := rfl
  have hmul : moduleSection (w0 F) (t * p.2) * ((u * p.1 : normOneSubgroup F) : Ideles F) =
      (moduleSection (w0 F) t * (u : Ideles F)) * z := by
    rw [hz, map_mul, Subgroup.coe_mul]
    ac_rfl
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) ((moduleSection (w0 F) t * (u : Ideles F)) * z) * g =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) := by
    rw [map_mul, mul_assoc]
  have hω : ((ω.1 ((moduleSection (w0 F) t * (u : Ideles F)) * z) : ℂˣ) : ℂ) =
      ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) * ((ω.1 z : ℂˣ) : ℂ) := by
    rw [map_mul ω.1, Units.val_mul]
  have habs : ((IdeleGroup.ideleModule F z : ℝ) ^ 2 * absD g) ^ ((1 : ℝ) / 2) =
      (IdeleGroup.ideleModule F z : ℝ) * absD g ^ ((1 : ℝ) / 2) := by
    have h0 : 0 ≤ (IdeleGroup.ideleModule F z : ℝ) := (IdeleGroup.ideleModule F z).2.le
    rw [Real.mul_rpow (by positivity) (absD_nonneg g), ← Real.rpow_natCast,
      ← Real.rpow_mul h0]
    norm_num
  have hc : (((t * p.2 : {r : ℝ // 0 < r}) : ℝ) : ℂ) =
      ((t : ℝ) : ℂ) * ((IdeleGroup.ideleModule F z : ℝ) : ℂ) := by
    rw [← ht0, ← Complex.ofReal_mul]
    rfl
  unfold eisInt
  rw [hmul, hsc, absD_scalar_mul, habs, hω, hc]
  have hωz : ((ω.1 z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hωA : ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  generalize thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)) = T
  generalize ((ω.1 z : ℂˣ) : ℂ) = a at hωz ⊢
  generalize ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) = b at hωA ⊢
  push_cast
  field_simp

theorem setIntegral_fd_mul (f : normOneSubgroup F → ℂ)
    (hf : ∀ (k : Fˣ) (u : normOneSubgroup F), f (u * diagonalToNormOne F k) = f u) (u0 : normOneSubgroup F) :
    ∫ u in normOneFundamentalDomain F, f (u * u0) ∂normOneMeasure F =
      ∫ u in normOneFundamentalDomain F, f u ∂normOneMeasure F := by
  have hE := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
  have hE' : IsFundamentalDomain (diagonalNormOne F).op
      ((fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F) (normOneMeasure F) := by
    refine hE.preimage_of_equiv (e := id)
      (measurePreserving_mul_right (normOneMeasure F) u0⁻¹).quasiMeasurePreserving Function.bijective_id ?_
    intro γ x
    show (γ • x) * u0⁻¹ = γ • (x * u0⁻¹)
    simp only [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
    exact mul_right_comm _ _ _
  have h1 : ∫ u in normOneFundamentalDomain F, f (u * u0) ∂normOneMeasure F =
      ∫ v in (fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F, f v ∂normOneMeasure F := by
    have := (measurePreserving_mul_right (normOneMeasure F) u0).setIntegral_preimage_emb
      (measurableEmbedding_mulRight u0) f ((fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F)
    rw [← this]
    congr 2
    ext x
    simp
  rw [h1]
  refine hE'.setIntegral_eq hE ?_
  intro γ x
  rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
  have hm : ((γ : (normOneSubgroup F)ᵐᵒᵖ)).unop ∈ diagonalNormOne F := Subgroup.mem_op.1 γ.2
  obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.1 hm
  have he : ((γ : (normOneSubgroup F)ᵐᵒᵖ)).unop = diagonalToNormOne F k := Subtype.ext hk.symm
  rw [he, hf]

end EisensteinCentralCharacter

open EisensteinCentralCharacter in
theorem central_character_holds : SPois → SInt → SSmooth → SCent := by
  intro _ _ _ F _ _ _ ω c _ z g
  have h1 : ∀ t : {r : ℝ // 0 < r},
      ∫ u in normOneFundamentalDomain F, eisInt ω (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) t u
        ∂normOneMeasure F =
      ((ω.1 z : ℂˣ) : ℂ) * ∫ u in normOneFundamentalDomain F,
        eisInt ω (Phi c) g (t * (normOneSplitting (w0 F) z).2) u ∂normOneMeasure F := by
    intro t
    simp only [eisInt_scalar ω (Phi c) z g t]
    rw [integral_const_mul, setIntegral_fd_mul _ (fun k u => eisInt_mul_diag ω (Phi c) g _ u k)]
  unfold Eis
  simp only [h1]
  rw [integral_const_mul]
  exact congrArg (((ω.1 z : ℂˣ) : ℂ) * ·) (integral_mul_right_eq_self
    (fun t => ∫ u in normOneFundamentalDomain F, eisInt ω (Phi c) g t u ∂normOneMeasure F)
    (normOneSplitting (w0 F) z).2)

end UpperTheory.HilbertEisensteinWeightOne
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ContinuousPInfApply
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap nonZeroDivisors Classical
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published NumberField.mixedEmbedding

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]


variable (F) in
def gauss : 𝓢(NumberField.mixedEmbedding.mixedSpace F, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
    (gaussianSchwartz (NumberField.mixedEmbedding.euclidean.mixedSpace F))

def gJ (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Ad F → ℂ := schwartzBruhatTensor (gauss F) (cosetIndicator J 0)

theorem gJ_mem (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : gJ J ∈ schwartzBruhat F :=
  schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat J 0)


variable (F) in
def invN (N : ℕ) : IdeleGroup F :=
  diagonal F (Units.mk0 ((N : F) + 1)⁻¹ (inv_ne_zero (Nat.cast_add_one_ne_zero N)))

theorem pInf_apply_eq (x : Ad F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F x v = (homeomorphMixedSpace F x.1).1 ⟨v, IsTotallyReal.isReal v⟩ := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

theorem continuous_pInf_apply (v : InfinitePlace F) : Continuous fun x : Ad F => UpperTheory.V.TR.pInf F x v := by
  simp_rw [pInf_apply_eq]
  exact (continuous_apply (⟨v, IsTotallyReal.isReal v⟩ : {w : InfinitePlace F // w.IsReal})).comp
    (continuous_fst.comp ((homeomorphMixedSpace F).continuous.comp continuous_fst))

theorem arch_norm_le (x y : UpperTheory.V.TR.Rinf F) :
    ‖arch x y‖ ≤ Real.exp (-(Real.pi - 1) * ∑ v, (x v ^ 2 + y v ^ 2)) := by
  unfold arch
  rw [norm_prod, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => ?_
  have he : -(Real.pi : ℂ) * (((x v : ℝ) : ℂ) ^ 2 + ((y v : ℝ) : ℂ) ^ 2) =
      ((-Real.pi * (x v ^ 2 + y v ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, he, Complex.norm_exp_ofReal]
  have h1 : ‖((x v : ℝ) : ℂ) + Complex.I * ((y v : ℝ) : ℂ)‖ ≤ |x v| + |y v| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  have h2 : |x v| + |y v| ≤ Real.exp (x v ^ 2 + y v ^ 2) := by
    have := Real.add_one_le_exp (x v ^ 2 + y v ^ 2)
    nlinarith [sq_abs (x v), sq_abs (y v), sq_nonneg (|x v| - 1), sq_nonneg (|y v| - 1)]
  calc ‖((x v : ℝ) : ℂ) + Complex.I * ((y v : ℝ) : ℂ)‖ * Real.exp (-Real.pi * (x v ^ 2 + y v ^ 2))
      ≤ Real.exp (x v ^ 2 + y v ^ 2) * Real.exp (-Real.pi * (x v ^ 2 + y v ^ 2)) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    _ = Real.exp (-(Real.pi - 1) * (x v ^ 2 + y v ^ 2)) := by
        rw [← Real.exp_add]; congr 1; ring

theorem gauss_apply (m : NumberField.mixedEmbedding.mixedSpace F) :
    gauss F m = ((Real.exp (-Real.pi * ‖mixedToEuclidean F m‖ ^ 2) : ℝ) : ℂ) := rfl

theorem norm_gauss (m : NumberField.mixedEmbedding.mixedSpace F) :
    ‖gauss F m‖ = Real.exp (-Real.pi * ∑ v : InfinitePlace F, (m.1 ⟨v, IsTotallyReal.isReal v⟩) ^ 2) := by
  rw [gauss_apply, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_mixedToEuclidean_sq]
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩
  rw [Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.sum_empty, mul_zero, add_zero]
  congr 2
  exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun w => rfl

theorem invN_smul (N : ℕ) (x : Ad F) : invN F N • x = algebraMap F (Ad F) ((N : F) + 1)⁻¹ * x := by
  rw [Units.smul_def, invN, coe_diagonal, Units.val_mk0]
  rfl

theorem pInf_algebraMap_mul (a : F) (x : Ad F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F (algebraMap F (Ad F) a * x) v =
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a * UpperTheory.V.TR.pInf F x v := by
  rw [map_mul, Pi.mul_apply, pInf_apply_eq (algebraMap F (Ad F) a)]
  congr 1
  change (homeomorphMixedSpace F (algebraMap F (InfiniteAdeleRing F) a)).1 _ = _
  rw [homeomorphMixedSpace_algebraMap, mixedEmbedding_apply_isReal]

theorem norm_gJ_invN (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (x : Ad F) :
    ‖gJ J (invN F N • x)‖ = Real.exp (-Real.pi * ∑ v, (((N : ℝ) + 1)⁻¹ * UpperTheory.V.TR.pInf F x v) ^ 2) *
      (if algebraMap F (Af F) ((N : F) + 1)⁻¹ * pFin F x ∈ idealFiniteAdeles J then 1 else 0) := by
  rw [invN_smul]
  unfold gJ schwartzBruhatTensor
  rw [norm_mul, norm_gauss, cosetIndicator_apply, sub_zero]
  have hs : ∑ v : InfinitePlace F, ((homeomorphMixedSpace F (algebraMap F (Ad F) ((N : F) + 1)⁻¹ * x).1).1
      ⟨v, IsTotallyReal.isReal v⟩) ^ 2 = ∑ v, (((N : ℝ) + 1)⁻¹ * UpperTheory.V.TR.pInf F x v) ^ 2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← pInf_apply_eq, pInf_algebraMap_mul]
    congr 2
    simp [map_inv₀]
  rw [hs]
  congr 1
  · have h2 : (algebraMap F (Ad F) ((N : F) + 1)⁻¹ * x).2 = algebraMap F (Af F) ((N : F) + 1)⁻¹ * pFin F x := rfl
    rw [h2]
    split_ifs <;> simp

theorem pInf_vecMul (y : Fin 2 → Ad F) (A : Matrix (Fin 2) (Fin 2) (Ad F)) (i : Fin 2) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F ((y ᵥ* A) i) v =
      UpperTheory.V.TR.pInf F (y 0) v * UpperTheory.V.TR.pInf F (A 0 i) v + UpperTheory.V.TR.pInf F (y 1) v * UpperTheory.V.TR.pInf F (A 1 i) v := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_add (f := _), map_mul]

theorem pFin_vecMul (y : Fin 2 → Ad F) (A : Matrix (Fin 2) (Fin 2) (Ad F)) (i : Fin 2) :
    pFin F ((y ᵥ* A) i) = pFin F (y 0) * pFin F (A 0 i) + pFin F (y 1) * pFin F (A 1 i) := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_add (f := _), map_mul]

private theorem sq_lin_le {a b p q H : ℝ} (hp : |p| ≤ H) (hq : |q| ≤ H) :
    (a * p + b * q) ^ 2 ≤ 2 * H ^ 2 * (a ^ 2 + b ^ 2) := by
  have hp2 : p ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs p]; exact pow_le_pow_left₀ (abs_nonneg p) hp 2
  have hq2 : q ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs q]; exact pow_le_pow_left₀ (abs_nonneg q) hq 2
  nlinarith [sq_nonneg (a * p - b * q), mul_le_mul_of_nonneg_left hp2 (sq_nonneg a),
    mul_le_mul_of_nonneg_left hq2 (sq_nonneg b)]


open Classical in
theorem dom_gen {Kc : Set (Matrix (Fin 2) (Fin 2) (Ad F))} (hK : IsCompact Kc) {L : Set (Af F)} (hL : IsCompact L) :
    ∃ (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ), ∀ A ∈ Kc, ∀ y : Fin 2 → Ad F,
      ‖arch (UpperTheory.V.TR.pInf F (y 0)) (UpperTheory.V.TR.pInf F (y 1))‖ *
          (if pFin F (y 0) ∈ L ∧ pFin F (y 1) ∈ L then (1 : ℝ) else 0) ≤
        ‖gJ J (invN F N • (y ᵥ* A) 0)‖ * ‖gJ J (invN F N • (y ᵥ* A) 1)‖ := by

  have hb : ∀ p : Fin 2 × Fin 2 × InfinitePlace F, ∃ C : ℝ, ∀ A ∈ Kc,
      ‖UpperTheory.V.TR.pInf F (A p.1 p.2.1) p.2.2‖ ≤ C := fun p =>
    hK.exists_bound_of_continuousOn
      ((continuous_pInf_apply p.2.2).comp (continuous_id.matrix_elem p.1 p.2.1)).continuousOn
  choose C hC using hb
  set H : ℝ := 1 + ∑ p, |C p| with hH
  have hent : ∀ A ∈ Kc, ∀ i j v, |UpperTheory.V.TR.pInf F (A i j) v| ≤ H := by
    intro A hA i j v
    have h1 := hC (i, j, v) A hA
    rw [Real.norm_eq_abs] at h1
    have h2 : |C (i, j, v)| ≤ ∑ p, |C p| :=
      Finset.single_le_sum (f := fun p => |C p|) (fun p _ => abs_nonneg _) (Finset.mem_univ _)
    linarith [le_abs_self (C (i, j, v))]

  set N : ℕ := ⌈4 * Real.pi * H ^ 2 / (Real.pi - 1)⌉₊ with hNdef
  have hpi1 : 0 < Real.pi - 1 := by linarith [Real.pi_gt_three]
  have hN : 4 * Real.pi * H ^ 2 ≤ (Real.pi - 1) * ((N : ℝ) + 1) ^ 2 := by
    have h1 : 4 * Real.pi * H ^ 2 / (Real.pi - 1) ≤ (N : ℝ) := Nat.le_ceil _
    have h0 : (0 : ℝ) ≤ N := N.cast_nonneg
    have h2 : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
    rw [div_le_iff₀ hpi1] at h1
    nlinarith
  set c : ℝ := ((N : ℝ) + 1)⁻¹ with hcdef
  have hc2 : Real.pi * c ^ 2 * (4 * H ^ 2) ≤ Real.pi - 1 := by
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hc : c ^ 2 * ((N : ℝ) + 1) ^ 2 = 1 := by
      rw [hcdef, ← mul_pow, inv_mul_cancel₀ hN1.ne', one_pow]
    calc Real.pi * c ^ 2 * (4 * H ^ 2) = c ^ 2 * (4 * Real.pi * H ^ 2) := by ring
      _ ≤ c ^ 2 * ((Real.pi - 1) * ((N : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hN (sq_nonneg c)
      _ = Real.pi - 1 := by rw [mul_left_comm, hc, mul_one]

  let f : Fin 2 → (Af F × Af F) × Matrix (Fin 2) (Fin 2) (Ad F) → Af F := fun i p =>
    algebraMap F (Af F) ((N : F) + 1)⁻¹ * (p.1.1 * pFin F (p.2 0 i) + p.1.2 * pFin F (p.2 1 i))
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    have hp : ∀ j, Continuous fun p : (Af F × Af F) × Matrix (Fin 2) (Fin 2) (Ad F) => pFin F (p.2 j i) :=
      fun j => continuous_snd.comp (continuous_snd.matrix_elem j i)
    exact continuous_const.mul (((continuous_fst.comp continuous_fst).mul (hp 0)).add
      ((continuous_snd.comp continuous_fst).mul (hp 1)))
  set S : Set (Af F) := f 0 '' ((L ×ˢ L) ×ˢ Kc) ∪ f 1 '' ((L ×ˢ L) ×ˢ Kc) with hSdef
  have hS : IsCompact S :=
    (((hL.prod hL).prod hK).image (hfc 0)).union (((hL.prod hL).prod hK).image (hfc 1))
  obtain ⟨J, hJ⟩ := exists_subset_idealFiniteAdeles hS
  refine ⟨J, N, fun A hA y => ?_⟩
  split_ifs with hy
  swap
  · rw [mul_zero]; positivity
  rw [mul_one]
  have hfin : ∀ i : Fin 2, algebraMap F (Af F) ((N : F) + 1)⁻¹ * pFin F ((y ᵥ* A) i) ∈ idealFiniteAdeles J := by
    intro i
    apply hJ
    rw [pFin_vecMul]
    have hmem : f i ((pFin F (y 0), pFin F (y 1)), A) ∈ S := by
      fin_cases i
      · exact Or.inl ⟨_, ⟨⟨hy.1, hy.2⟩, hA⟩, rfl⟩
      · exact Or.inr ⟨_, ⟨⟨hy.1, hy.2⟩, hA⟩, rfl⟩
    exact hmem
  rw [norm_gJ_invN, norm_gJ_invN, if_pos (hfin 0), if_pos (hfin 1), mul_one, mul_one, ← Real.exp_add]
  refine (arch_norm_le _ _).trans (Real.exp_le_exp.2 ?_)
  simp_rw [pInf_vecMul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  set a := UpperTheory.V.TR.pInf F (y 0) v
  set b := UpperTheory.V.TR.pInf F (y 1) v
  have L1 : (a * UpperTheory.V.TR.pInf F (A 0 0) v + b * UpperTheory.V.TR.pInf F (A 1 0) v) ^ 2 +
      (a * UpperTheory.V.TR.pInf F (A 0 1) v + b * UpperTheory.V.TR.pInf F (A 1 1) v) ^ 2 ≤ 4 * H ^ 2 * (a ^ 2 + b ^ 2) := by
    have e1 := sq_lin_le (a := a) (b := b) (hent A hA 0 0 v) (hent A hA 1 0 v)
    have e2 := sq_lin_le (a := a) (b := b) (hent A hA 0 1 v) (hent A hA 1 1 v)
    linarith
  have hab : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left L1 (by positivity : (0 : ℝ) ≤ Real.pi * c ^ 2)
  have h4 : Real.pi * c ^ 2 * (4 * H ^ 2 * (a ^ 2 + b ^ 2)) ≤ (Real.pi - 1) * (a ^ 2 + b ^ 2) := by
    calc Real.pi * c ^ 2 * (4 * H ^ 2 * (a ^ 2 + b ^ 2)) = (Real.pi * c ^ 2 * (4 * H ^ 2)) * (a ^ 2 + b ^ 2) := by ring
      _ ≤ (Real.pi - 1) * (a ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_right hc2 hab
  nlinarith [h3, h4]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Imports
section
noncomputable section

open NumberField NumberField.mixedEmbedding
open scoped Classical

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def toR : mixedSpace F →ₗ[ℝ] UpperTheory.V.TR.Rinf F where
  toFun x v := x.1 ⟨v, IsTotallyReal.isReal v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
end
end

