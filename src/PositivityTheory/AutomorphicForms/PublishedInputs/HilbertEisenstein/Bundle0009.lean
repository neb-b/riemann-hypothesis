module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0006
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0003
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0004
public import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import GroundTheory.LocalFields.LocalZetaGauss
public import GroundTheory.LocalFields.LocalZeta
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.UnitaryTransvectionZeroSecondMemClosure
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import GroundTheory.GlobalFields.WeilGroups.QuasiCharacterDecomposition

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.AestronglyMeasurableColumnWeight
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem isClosed_valuation_le (w : HeightOneSpectrum (𝓞 F)) (γ : WithZero (Multiplicative ℤ)) :
    IsClosed {x : w.adicCompletion F | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : γ < Valued.v x := lt_of_not_ge hx
  filter_upwards [Valued.locally_const (lt_of_le_of_lt zero_le hx').ne'] with y hy
  intro hy'
  have e : Valued.v y = Valued.v x := hy
  exact absurd (e ▸ hy') (not_le.mpr hx')

theorem continuous_pLoc (w : HeightOneSpectrum (𝓞 F)) : Continuous (pLoc F w) :=
  RestrictedProduct.continuous_eval w

theorem continuous_pFin : Continuous (pFin F) := continuous_snd

theorem continuous_pInf : Continuous (UpperTheory.V.TR.pInf F) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem isClosed_row (c : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsClosed {y : Fin 2 → Ad F | ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F (y 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun w => IsClosed.inter ?_ ?_
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 0)))
  · exact (isClosed_valuation_le w _).preimage
      (((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 1))).sub continuous_const)

theorem isClosed_col (c : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsClosed {y : Fin 2 → Ad F | ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
      Valued.v (pLoc F w (pFin F (y 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun w => IsClosed.inter ?_ ?_
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 0)))
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 1)))

theorem coe_scalar (a : Ideles F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      Matrix.diagonal fun _ => (a : Ad F) := rfl

theorem continuous_av : Continuous (av (F := F)) :=
  ((continuous_moduleSection (w0 F)).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

theorem continuous_rowv (g : GA F 2) (ξ : Fin 2 → F) : Continuous fun a : Ideles F => rowv g a ξ := by
  unfold rowv Mrow
  simp only [Units.val_mul, coe_scalar]
  exact continuous_const.matrix_vecMul
    ((continuous_pi fun _ => Units.continuous_val).matrix_diagonal.matrix_mul continuous_const)

theorem continuous_colv (g : GA F 2) (ξ : Fin 2 → F) : Continuous fun a : Ideles F => colv g a ξ := by
  unfold colv Mcol
  simp only [Units.val_mul, coe_scalar]
  exact (continuous_const.matrix_mul
    (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal).matrix_mulVec continuous_const

theorem continuous_vInf : Continuous (vInf (F := F)) :=
  continuous_pi fun i => continuous_pInf.comp (continuous_apply i)

theorem measurable_finRow (c : HeightOneSpectrum (𝓞 F) → ℕ) {f : Pp F → Fin 2 → Ad F} (hf : Continuous f) :
    Measurable fun p => finRow c (f p) := by
  unfold finRow
  exact Measurable.ite ((isClosed_row c).preimage hf).measurableSet measurable_const measurable_const

theorem measurable_finCol (c : HeightOneSpectrum (𝓞 F) → ℕ) {f : Pp F → Fin 2 → Ad F} (hf : Continuous f) :
    Measurable fun p => finCol c (f p) := by
  unfold finCol
  refine Measurable.ite ((isClosed_col c).preimage hf).measurableSet ?_ measurable_const
  exact (continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_pFin.comp ((continuous_apply 1).comp hf)))).measurable

theorem measurable_chi (χ : HChar F) : Measurable fun p : Pp F => ((χ.1 (av p) : ℂˣ) : ℂ)⁻¹ :=
  ((Units.continuous_val.comp (χ.2.1.comp continuous_av)).measurable).inv

theorem measurable_first_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) :
    Measurable (kap1 χ c g) := by
  refine measurable_from_prod_countable_left fun ξ => ?_
  exact ((measurable_finRow c ((continuous_rowv g ξ.1).comp continuous_av)).mul (measurable_chi χ)).mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable

theorem measurable_second_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) :
    Measurable (kap2 χ c g) := by
  refine measurable_from_prod_countable_left fun ξ => ?_
  exact ((measurable_finCol c ((continuous_colv g ξ.1).comp continuous_av)).mul (measurable_chi χ)).mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable.inv

theorem measurable_row_weight (g : GA F 2) : Measurable (w1 (F := F) g) :=
  measurable_from_prod_countable_left fun ξ =>
    (continuous_vInf.comp ((continuous_rowv g ξ.1).comp continuous_av)).measurable

theorem measurable_column_weight (g : GA F 2) : Measurable (w2 (F := F) g) :=
  measurable_from_prod_countable_left fun ξ =>
    (continuous_vInf.comp ((continuous_colv g ξ.1).comp continuous_av)).measurable

theorem aestronglyMeasurable_first_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (S : Set {r : ℝ // 0 < r}) :
    AEStronglyMeasurable (kap1 χ c g) (μS F S) := (measurable_first_kernel χ c g).aestronglyMeasurable

theorem aestronglyMeasurable_second_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (S : Set {r : ℝ // 0 < r}) :
    AEStronglyMeasurable (kap2 χ c g) (μS F S) := (measurable_second_kernel χ c g).aestronglyMeasurable

theorem aestronglyMeasurable_row_weight (g : GA F 2) (S : Set {r : ℝ // 0 < r}) : AEStronglyMeasurable (w1 g) (μS F S) :=
  (measurable_row_weight g).aestronglyMeasurable

theorem aestronglyMeasurable_column_weight (g : GA F 2) (S : Set {r : ℝ // 0 < r}) : AEStronglyMeasurable (w2 g) (μS F S) :=
  (measurable_column_weight g).aestronglyMeasurable

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CoefficientDivisorHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.DivisorSumOrder

variable {F : Type} [Field F] [NumberField F]

theorem ordI_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) : ordI v w.asIdeal = 0 := by
  by_contra h0
  have h1 := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).1 h0
  exact h (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))

theorem ordI_top (v : HeightOneSpectrum (𝓞 F)) : ordI v (⊤ : Ideal (𝓞 F)) = 0 := by
  by_contra h0
  have h1 := (Associates.count_ne_zero_iff_dvd top_ne_bot v.irreducible).1 h0
  exact v.isPrime.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 h1))

open Classical in
theorem ordI_pow (v w : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    ordI v (w.asIdeal ^ k) = if v = w then k else 0 := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, ordI_top]; split_ifs <;> rfl
  | succ k ih =>
    rw [pow_succ, Fresh.ordI_mul_of_ne_bot v (pow_ne_zero _ w.ne_bot) w.ne_bot, ih]
    by_cases h : v = w
    · rw [if_pos h, if_pos h, h, Fresh.ordI_asIdeal_self]
    · rw [if_neg h, if_neg h, ordI_ne h]

theorem prodS_ne_bot (T : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F) → ℕ) :
    (∏ w ∈ T, w.asIdeal ^ p w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro w _
  exact pow_ne_zero _ w.ne_bot

open Classical in
theorem ordI_prodS (T : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F) → ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : ordI v (∏ w ∈ T, w.asIdeal ^ p w) = if v ∈ T then p v else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top, ordI_top]; simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Fresh.ordI_mul_of_ne_bot v (pow_ne_zero _ a.ne_bot) (prodS_ne_bot T p), ordI_pow, ih]
    by_cases h1 : v = a
    · subst h1
      simp [ha]
    · by_cases h2 : v ∈ T
      · simp [h1, h2]
      · simp [h1, h2]

theorem eq_of_ordI {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ w : HeightOneSpectrum (𝓞 F), ordI w I = ordI w J) :
    I = J := by
  classical
  have key : Associates.mk I = Associates.mk J := by
    refine Associates.eq_of_eq_counts (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) fun p hp => ?_
    obtain ⟨P, rfl⟩ := Associates.exists_rep p
    have hP : Irreducible P := Associates.irreducible_mk.1 hp
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, Ideal.isPrime_of_prime hP.prime, hP.ne_zero⟩
    have := h v
    unfold ordI at this
    convert this using 2
  exact associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 key)

theorem ordI_le_of_dvd {r m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (h : r ∣ m) (w : HeightOneSpectrum (𝓞 F)) :
    ordI w r ≤ ordI w m := by
  obtain ⟨s, rfl⟩ := h
  have hr : r ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.bot_mul])
  have hs : s ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.mul_bot])
  rw [Fresh.ordI_mul_of_ne_bot w hr hs]
  exact Nat.le_add_right _ _

theorem dvd_fin {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) : {r : Ideal (𝓞 F) | r ∣ m}.Finite := by
  have := UniqueFactorizationMonoid.fintypeSubtypeDvd m hm
  exact Set.finite_coe_iff.1 (Finite.of_fintype {r // r ∣ m})


open Classical in
def ext (S : Finset (HeightOneSpectrum (𝓞 F))) (p : S → ℕ) (w : HeightOneSpectrum (𝓞 F)) : ℕ :=
  if h : w ∈ S then p ⟨w, h⟩ else 0

theorem ordI_prod_ext (S : Finset (HeightOneSpectrum (𝓞 F))) (p : S → ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    ordI v (∏ w ∈ S, w.asIdeal ^ ext S p w) = ext S p v := by
  classical
  rw [ordI_prodS]
  unfold ext
  split_ifs <;> rfl

theorem divS_eq (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ w ∉ S, ordI w m = 0) :
    divS ω c m = ∏ w ∈ S, ∑ j ∈ Finset.range (ordI w m + 1), L4.chiW ω c w ^ j := by
  classical
  rw [← Finset.prod_coe_sort S, Finset.prod_univ_sum]
  unfold divS
  rw [finsum_mem_eq_finite_toFinset_sum _ (dvd_fin hm)]
  symm
  refine Finset.sum_nbij' (fun p => ∏ w ∈ S, w.asIdeal ^ ext S p w) (fun r => fun w : S => ordI w.1 r) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hp' : ∀ w : S, p w ≤ ordI w.1 m := fun w => by
      have := Fintype.mem_piFinset.1 hp w
      rw [Finset.mem_range] at this
      omega
    refine ⟨∏ w ∈ S, w.asIdeal ^ (ordI w m - ext S p w), ?_⟩
    have hne : (∏ w ∈ S, w.asIdeal ^ ext S p w) * (∏ w ∈ S, w.asIdeal ^ (ordI w m - ext S p w)) ≠ ⊥ := by
      rw [Ne, Ideal.mul_eq_bot, not_or]
      exact ⟨prodS_ne_bot _ _, prodS_ne_bot _ _⟩
    refine eq_of_ordI hm hne fun v => ?_
    rw [Fresh.ordI_mul_of_ne_bot v (prodS_ne_bot _ _) (prodS_ne_bot _ _), ordI_prod_ext, ordI_prodS]
    by_cases hv : v ∈ S
    · rw [if_pos hv]
      have h1 : ext S p v = p ⟨v, hv⟩ := by unfold ext; rw [dite_eq_left hv]
      have h2 : p ⟨v, hv⟩ ≤ ordI v m := hp' ⟨v, hv⟩
      rw [h1]
      omega
    · rw [if_neg hv, hS v hv]
      unfold ext
      rw [dite_eq_right hv]
  · intro r hr
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hr
    rw [Fintype.mem_piFinset]
    intro w
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (ordI_le_of_dvd hm hr w)
  · intro p _
    funext w
    rw [ordI_prod_ext]
    unfold ext
    rw [dite_eq_left w.2]
  · intro r hr
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hr
    have hr0 : r ≠ ⊥ := fun h0 => hm (by rw [h0] at hr; exact zero_dvd_iff.1 hr)
    refine eq_of_ordI (prodS_ne_bot _ _) hr0 fun v => ?_
    rw [ordI_prod_ext]
    unfold ext
    split_ifs with hv
    · rfl
    · have := ordI_le_of_dvd hm hr v
      rw [hS v hv] at this
      omega
  · intro p _
    unfold chiI
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [ordI_prod_ext]
      unfold ext L4.chiW
      rw [dite_eq_left w.2]
    · intro v hv
      by_contra hvS
      apply hv
      beta_reduce
      rw [ordI_prod_ext]
      unfold ext
      rw [dite_eq_right fun h => hvS (Finset.mem_coe.2 h), pow_zero]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.DivisorSumOrder

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open DivisorSumOrder

theorem coefficient_divisor_holds : CoefDiv := by
  intro F _ _ _ ω c z m S hz hS
  classical
  unfold coefAt
  by_cases hpos : ∀ w ∈ S, 0 ≤ m w
  · rw [if_pos hpos]
    have hex : ∃ 𝔪, GenD z 𝔪 := by
      refine ⟨∏ w ∈ S, w.asIdeal ^ (m w).toNat, prodS_ne_bot _ _, fun w => ?_⟩
      rw [hz w, ordI_prodS]
      congr 1
      by_cases hw : w ∈ S
      · rw [if_pos hw, Int.toNat_of_nonneg (hpos w hw)]; rfl
      · rw [if_neg hw, hS w hw]; rfl
    rw [dite_eq_left hex]
    have hspec := hex.choose_spec
    set 𝔪 := hex.choose
    have hord : ∀ w, (ordI w 𝔪 : ℤ) = m w := by
      intro w
      have h := (hspec.2 w).symm.trans (hz w)
      rw [WithZero.exp_inj] at h
      unfold dd at h
      omega
    rw [divS_eq ω c hspec.1 S fun w hw => by have := hord w; rw [hS w hw] at this; omega]
    refine Finset.prod_congr rfl fun w _ => ?_
    congr 2
    have := hord w
    omega
  · rw [if_neg hpos, dite_eq_right]
    rintro ⟨𝔪, -, h𝔪⟩
    apply hpos
    intro w _
    have h := (h𝔪 w).symm.trans (hz w)
    rw [WithZero.exp_inj] at h
    unfold dd at h
    omega

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection


open Classical in
def finK (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : F) (b : (Af F)ˣ) : ℂ :=
  if (∀ w, Valued.v (pLoc F w ((b : Af F) * (yf : Af F))) ≤ WithZero.exp (-(c w : ℤ))) ∧
      (∀ w, Valued.v (pLoc F w (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ)) ≤
        WithZero.exp ((c w : ℤ) + dd w))
  then ((finiteAdelicChar F (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ) : Circle) : ℂ) else 0

def ωF (ω : HChar F) (b : (Af F)ˣ) : ℂ := ((ω.1 (ofFinite b) : ℂˣ) : ℂ)

def qc (ω : HChar F) : QuasiCharacter F where
  toMonoidHom := QuotientGroup.lift _ ω.1 (by
    rintro _ ⟨a, rfl⟩
    exact ω.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ω.2.1

theorem norm_qc (ω : HChar F) (h : IsOfFinOrder ω) (c : GroundTheory.Global.IdeleClassGroup F) :
    ‖((qc ω c : ℂˣ) : ℂ)‖ = 1 := by
  induction c using QuotientGroup.induction_on with
  | H x => exact L2.norm_omega_eq_one h x

def hc (ω : HChar F) (h : IsOfFinOrder ω) : HeckeCharacter F := QuasiCharacter.toUnitary (qc ω) (norm_qc ω h)

theorem hc_toIdele (ω : HChar F) (h : IsOfFinOrder ω) (x : IdeleGroup F) :
    (((hc ω h).toIdele x : Circle) : ℂ) = ((ω.1 x : ℂˣ) : ℂ) := rfl

def xiF (ξ : Fˣ) : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom ξ

def ordAt (b : (Af F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : ℤ := ord (pLoc F v (b : Af F))


open Classical in
def locF (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : F) (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) : ℂ :=
  (if Valued.v ((a : v.adicCompletion F) * pLoc F v (yf : Af F)) ≤ WithZero.exp (-(c v : ℤ)) ∧
      Valued.v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * algebraMap F (v.adicCompletion F) ξ) ≤
        WithZero.exp ((c v : ℤ) + dd v)
    then (localAdelicChar F v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) ξ) : ℂ) else 0) * ((ω.loc v a : ℂˣ) : ℂ)⁻¹

def cst (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if c v = 0 then ((ω.val v : ℂˣ) : ℂ) ^ (-dd v) else
    ∫ x in ordShell (v.adicCompletion F) (-((c v : ℤ) + dd v)), ((ω.loc v x : ℂˣ) : ℂ) *
      (localAdelicChar F v (x : v.adicCompletion F) : ℂ) ∂multHaar (v.adicCompletion F)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 GroundTheory.Automorphic.GodementSection

def InvSubst : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (f : (v.adicCompletion F)ˣ → ℂ) (t : (v.adicCompletion F)ˣ),
    (Integrable f (multHaar (v.adicCompletion F)) ↔
      Integrable (fun x => f (t * x⁻¹)) (multHaar (v.adicCompletion F))) ∧
    ∫ a, f a ∂multHaar (v.adicCompletion F) = ∫ x, f (t * x⁻¹) ∂multHaar (v.adicCompletion F)

def LocInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (yf : (Af F)ˣ) (ξ : Fˣ) (v : HeightOneSpectrum (𝓞 F)),
    Integrable (locF ω c yf (ξ : F) v) (multHaar (v.adicCompletion F)) ∧
    ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F) =
      ((ω.loc v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ξ) : ℂˣ) : ℂ)⁻¹ *
        if ordAt (xiF ξ * yf) v + dd v < 0 then 0 else
          cst ω c v * ∑ j ∈ Finset.range ((ordAt (xiF ξ * yf) v + dd v).toNat + 1), chiW ω c v ^ j

def OmegaProd : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (b : (Af F)ˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w ∉ S, c w = 0 ∧ IsIntegralUnitAt b w) →
    ωF ω b = ∏ v ∈ S, ((ω.loc v (finUnitAt v b) : ℂˣ) : ℂ)

def FinSplit : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (yf : (Af F)ˣ) (ξ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w ∉ S, c w = 0 ∧ dd w = 0 ∧ IsIntegralUnitAt yf w ∧ IsIntegralUnitAt (xiF ξ) w) →
    (∀ v, Integrable (locF ω c yf (ξ : F) v) (multHaar (v.adicCompletion F))) →
    Integrable (fun b => finK c yf (ξ : F) b * (ωF ω b)⁻¹) (finiteIdeleMeasure F) ∧
      ∫ b, finK c yf (ξ : F) b * (ωF ω b)⁻¹ ∂finiteIdeleMeasure F =
        ∏ v ∈ S, ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F)

def OmegaPos : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ ξ : Fˣ, (∀ v, 0 < reAt v (ξ : F)) → ωF ω (xiF ξ) = 1

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

