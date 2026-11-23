module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLAssoc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0267
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralQuadraticCharEventuallyConst
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology Classical

namespace GlobalTheory.KSp

theorem setIntegral_addSubgroup_add {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] (H : AddSubgroup X)
    (hH : MeasurableSet (H : Set X)) {h : X} (hh : h ∈ H) (g : X → ℂ) :
    ∫ x in (H : Set X), g (x + h) ∂μ = ∫ x in (H : Set X), g x ∂μ := by
  rw [← integral_indicator hH, ← integral_indicator hH]
  have key : (Set.indicator (H : Set X) fun x => g (x + h)) =
      fun x => Set.indicator (H : Set X) g (x + h) := by
    funext x
    by_cases hx : x ∈ H
    · have hx' : x + h ∈ H := H.add_mem hx hh
      simp [Set.indicator_apply, hx, hx']
    · have hx' : x + h ∉ H := fun h' => hx (by simpa using H.sub_mem h' hh)
      simp [Set.indicator_apply, hx, hx']
  rw [key, integral_add_right_eq_self (Set.indicator (H : Set X) g) h]

theorem setIntegral_pair_char {X : Type} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] {e : X → X → ℂ} (he : IsPair e)
    (M : AddSubgroup X) (hM : MeasurableSet (M : Set X)) (x : X) :
    ∫ m in (M : Set X), e x m ∂μ =
      if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0 := by
  split_ifs with hx
  · rw [setIntegral_congr_fun hM (g := fun _ => (1 : ℂ)) (fun m hm => by
      simp only; rw [he.symm]; exact hx m hm)]
    rw [setIntegral_const]
    simp
  · push_neg at hx
    obtain ⟨m₀, hm₀, hne⟩ := hx
    have h := setIntegral_addSubgroup_add μ M hM hm₀ (fun m => e x m)
    have hsplit : ∀ m, e x (m + m₀) = e x m * e x m₀ := fun m => by
      rw [he.symm x, he.add, he.symm m, he.symm m₀]
    simp only [hsplit] at h
    rw [integral_mul_const] at h
    have hne' : e x m₀ ≠ 1 := by rwa [he.symm]
    have h2 : (∫ m in (M : Set X), e x m ∂μ) * (e x m₀ - 1) = 0 := by
      rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hne'

theorem gauss_integral_eventually_const : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e →
    ∀ f : X → ℂ, IsLocallyConstant f → f 0 = 1 → (∀ x y, f (x + y) = f x * f y * e x y) →
    ∃ (γ : ℂ) (K : Set X), IsCompact K ∧ ∀ L : AddSubgroup X, IsCompact (L : Set X) → IsOpen (L : Set X) →
      K ⊆ L → ∫ x in (L : Set X), f x ∂μ = γ := by
  intro X _ _ _ _ hG μ _ e he f hf hf0 hfe
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  obtain ⟨M, hMc, hMo, hMf⟩ := hG.small {x | f x = 1} ((hf.isOpen_fiber 1).mem_nhds hf0)
  have hMn : (M : Set X) ∈ 𝓝 (0 : X) := hMo.mem_nhds M.zero_mem
  obtain ⟨K₀, hK₀c, hK₀⟩ := he.big _ hMn
  have hecont : ∀ m, Continuous (fun y => e m y) := fun m =>
    (he.lc.comp_continuous (continuous_const.prodMk continuous_id)).continuous
  set M' : Set X := {y | ∀ m ∈ (M : Set X), e m y = 1} with hM'
  have hM'cl : IsClosed M' := by
    have : M' = ⋂ m ∈ (M : Set X), {y | e m y = 1} := by ext; simp [M']
    rw [this]
    exact isClosed_biInter fun m _ => isClosed_eq (hecont m) continuous_const
  refine ⟨∫ x in M', f x ∂μ, (M : Set X) ∪ K₀, hMc.union hK₀c, ?_⟩
  intro L hLc hLo hKL
  have hML : (M : Set X) ⊆ L := Set.subset_union_left.trans hKL
  have hM'L : M' ⊆ L := fun y hy => hKL (Or.inr (hK₀ y hy))
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hMm : MeasurableSet (M : Set X) := hMo.measurableSet
  have hM'm : MeasurableSet M' := hM'cl.measurableSet
  haveI : IsFiniteMeasure (μ.restrict (L : Set X)) := isFiniteMeasure_restrict.mpr hLc.measure_lt_top.ne
  haveI : IsFiniteMeasure (μ.restrict (M : Set X)) := isFiniteMeasure_restrict.mpr hMc.measure_lt_top.ne
  set A := ∫ x in (L : Set X), f x ∂μ with hA
  have h1 : ∀ m ∈ (M : Set X), ∫ x in (L : Set X), f x * e x m ∂μ = A := by
    intro m hm
    rw [hA, ← setIntegral_addSubgroup_add μ L hLm (hML hm) f]
    congr 1; funext x
    rw [hfe, show f m = 1 from hMf hm]; ring
  obtain ⟨C, hC⟩ := hLc.exists_bound_of_continuousOn hf.continuous.continuousOn
  have hint : Integrable (Function.uncurry fun m x => f x * e x m)
      ((μ.restrict (M : Set X)).prod (μ.restrict (L : Set X))) := by
    refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (Continuous.mul (hf.continuous.comp continuous_snd)
        (he.lc.continuous.comp (continuous_snd.prodMk continuous_fst))).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (hMm.prod hLm) fun p hp => ?_
      show ‖f p.2 * e p.2 p.1‖ ≤ C
      rw [norm_mul, he.norm, mul_one]
      exact hC p.2 hp.2
  have h3 := integral_integral_swap hint
  rw [setIntegral_congr_fun hMm h1, setIntegral_const] at h3
  simp_rw [integral_const_mul, setIntegral_pair_char μ he M hMm] at h3
  have h4 : ∫ x in (L : Set X), f x * (if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0) ∂μ
      = ((μ.real (M : Set X) : ℝ) : ℂ) * ∫ x in M', f x ∂μ := by
    have : (fun x => f x * (if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0)) =
        Set.indicator M' (fun x => ((μ.real (M : Set X) : ℝ) : ℂ) * f x) := by
      funext x
      by_cases hx : x ∈ M'
      · rw [Set.indicator_of_mem hx, if_pos (show ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
      · rw [Set.indicator_of_notMem hx, if_neg (show ¬ ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
    rw [this, integral_indicator hM'm, Measure.restrict_restrict hM'm, Set.inter_eq_left.mpr hM'L,
      integral_const_mul]
  rw [h4, Complex.real_smul] at h3
  have hpos : ((μ.real (M : Set X) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨(hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne', hMc.measure_lt_top.ne⟩
  exact mul_left_cancel₀ hpos h3

end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseFlatNoetherianIntClosedStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibreBase_flat_noetherian_intClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    Module.Flat A (Localization.AtPrime QA) ∧ IsNoetherianRing (Localization.AtPrime QA) ∧
      algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X ∈ nonZeroDivisors (Localization.AtPrime QA) ∧
      ∀ f : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA), IsIntegral (Localization.AtPrime QA) f →
        ∃ r : Localization.AtPrime QA, algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r = f := by
  first | (exact @GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed) | (exact GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed) | (intros; apply GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

def ClosureEtaleAt (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (P : Ideal R) [P.IsPrime] : Prop :=
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  Algebra.Etale (Localization.AtPrime P)
    (TensorProduct R (Localization.AtPrime P) (GlobalTheory.KeyOriginNoeth.closure A R D))

theorem good_iff_etaleAt (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) :
    GlobalTheory.KeyOriginNoeth.Good A R D ρ ↔
      ((∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
          ClosureEtaleAt A R D P) ∧ PointAtZero A R D ρ) := Iff.rfl

end GlobalTheory.KeyOriginEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLAssocStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_assoc : ∀ (F : Type) [Field F] [Finite F], ∀ (a b c n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (γ : GL (Fin c) F → ℂ), IsCl α → IsCl β → IsCl γ → n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n := by
  first | (exact @GlobalTheory.Shin.HcAssoc.hc_assoc) | (exact GlobalTheory.Shin.HcAssoc.hc_assoc) | (intros; apply GlobalTheory.Shin.HcAssoc.hc_assoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacter
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.HCChar

theorem gal_id_apply {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem hc_isChar : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  intro F _ _ a b n hn α β hα hβ
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  haveI : Finite (GL (Fin n) F) := inferInstance
  have h1 : IsChar ℂ ℂ (fun p : H => α (π p).1) := by
    obtain ⟨m, ρ, hρ⟩ := hα
    exact ⟨m, ρ.comp ((MonoidHom.fst _ _).comp π), fun p => hρ _⟩
  have h2 : IsChar ℂ ℂ (fun p : H => β (π p).2) := by
    obtain ⟨m, ρ, hρ⟩ := hβ
    exact ⟨m, ρ.comp ((MonoidHom.snd _ _).comp π), fun p => hρ _⟩
  have hψ : IsChar ℂ ℂ ((fun p : H => α (π p).1) * (fun p : H => β (π p).2)) := isChar_mul_complex h1 h2
  have hind := isChar_ind ℂ ℂ (GL (Fin n) F) H _ hψ
  convert hind using 1
  funext x
  have hcard : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) = (Nat.card H : ℂ) := by
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hH x).symm))
  unfold hc hcTw ind
  rw [hcard]
  congr 1
  apply finsum_congr
  intro y
  rw [gal_id_apply]
  unfold ext0
  by_cases hy : y⁻¹ * x * y ∈ H
  · rw [dite_eq_left hy, if_pos ((hH _).1 hy), Pi.mul_apply, hπ]
  · rw [dite_eq_right hy, if_neg (fun e => hy ((hH _).2 e))]

end GlobalTheory.Shin.HCChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLTrivialOrthogonalHyperpl
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem hc_one_orth_hfree : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b →
    ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y →
    ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  intro F _ _ a b n hn hb α Y hY hF
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  have hn0 : 0 < n := by omega
  have hcl : ∀ g x : GL (Fin n) F, Y (x⁻¹ * g * x) = Y g :=
    (virt_mul_comap_conj_ind_linear (GL (Fin n) F)).2.2.1 Y (isChar_mem_virt_complex hY)
  let Pm : GL (Fin n) F → Prop := fun x => ∀ i j : Fin n, (j : ℕ) + 1 < n →
    (x : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j
  have hR : ∀ (M : Matrix (Fin n) (Fin n) F) (x : GL (Fin n) F), Pm x → ∀ i j : Fin n, (j : ℕ) + 1 < n →
      (M * (x : Matrix (Fin n) (Fin n) F)) i j = M i j := by
    intro M x hx i j hj
    rw [Matrix.mul_apply]
    simp only [hx _ j hj]
    rw [← Matrix.mul_apply, Matrix.mul_one]
  let H : Subgroup (GL (Fin n) F) :=
    { carrier := {x | Pm x}
      one_mem' := fun i j _ => by simp
      mul_mem' := fun {x y : GL (Fin n) F} hx hy i j hj => by
        show ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _
        rw [Units.val_mul, hR _ y hy i j hj]; exact hx i j hj
      inv_mem' := fun {x : GL (Fin n) F} hx i j hj => by
        have h1 : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have := hR ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) x hx i j hj
        rw [h1] at this
        exact this.symm }
  have hH : ∑ᶠ u : H, Y u = 0 := by
    have := hF hn0
    rw [← finsum_set_coe_eq_finsum_mem] at this
    exact this
  have hcos := char_coset_sum_eq_zero (GL (Fin n) F) Y hY H hH
  haveI : Fintype H := Fintype.ofFinite _
  let f : GL (Fin n) F → ℂ := fun x => if InPar a x then α (tlG a x) else 0
  have hent : ∀ x : GL (Fin n) F, ∀ h ∈ H, ∀ i j : Fin n, (j : ℕ) < a →
      ((x * h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = (x : Matrix (Fin n) (Fin n) F) i j := by
    intro x h hh i j hj
    rw [Units.val_mul]
    exact hR _ h hh i j (by omega)
  have hinv : ∀ x : GL (Fin n) F, ∀ h ∈ H, f (x * h) = f x := by
    intro x h hh
    have h1 : InPar a (x * h) ↔ InPar a x := by
      unfold InPar
      constructor
      · intro H' i j hj hi; rw [← hent x h hh i j hj]; exact H' i j hj hi
      · intro H' i j hj hi; rw [hent x h hh i j hj]; exact H' i j hj hi
    have h2 : tlG a (x * h) = tlG a x := by
      unfold tlG
      congr 1
      funext i j
      unfold tl ent
      split_ifs with hij
      · exact hent x h hh _ _ j.2
      · rfl
    simp only [f, h1, h2]
  have hS : ∑ x, f x * star (Y x) = 0 := by
    have hh : ∀ h : H, ∑ x, f x * star (Y x) = ∑ x, f x * star (Y (x * h)) := by
      intro h
      refine Fintype.sum_equiv (Equiv.mulRight (h : GL (Fin n) F)).symm _ _ ?_
      intro x
      simp only [Equiv.coe_mulRight, Equiv.mulRight_symm]
      rw [inv_mul_cancel_right, hinv x _ (H.inv_mem h.2)]
    have hsum : (Fintype.card H : ℂ) * ∑ x, f x * star (Y x) = 0 := by
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      rw [Finset.sum_congr rfl fun h _ => hh h, Finset.sum_comm]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← Finset.mul_sum, ← star_sum]
      have := hcos x
      rw [finsum_eq_sum_of_fintype] at this
      rw [this, star_zero, mul_zero]
    have hc0 : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp hsum).resolve_left hc0
  have hmain : ∀ y : GL (Fin n) F, ∑ x, f (y⁻¹ * x * y) * star (Y x) = 0 := by
    intro y
    rw [← hS]
    refine Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv _ _ ?_
    intro x
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, hcl]
  have hg : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y := fun y => by
    ext i j; simp [gal]
  rw [finsum_eq_sum_of_fintype]
  unfold hc hcTw
  simp only [hg, mul_one, finsum_eq_sum_of_fintype]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [← Finset.mul_sum]
  have := hmain y
  simp only [f, mul_assoc] at this
  rw [this, mul_zero]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid (k := k)}

theorem isLocallyConstant_of_isTensor {ϖ : kˣ} {e : ℕ} {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) :
    IsLocallyConstant T := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq T).2 fun x => ?_
  have h : ∀ᶠ y in nhds x, ∀ b ∈ γ.toFinset, ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) ∈ 𝒪[k] := by
    refine (Filter.eventually_all_finset _).2 fun b _ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun y : G.Args => (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) :=
      continuous_const.mul (((continuous_apply b).matrix_elem i j).sub continuous_const)
    exact (Model.isOpen_int.preimage hc).mem_nhds (by simp)
  filter_upwards [h] with y hy
  rw [← hT.2.2 x (fun b => if b ∈ γ then y b - x b else 0) fun b => ?_]
  · exact hT.1 fun b hb => by simp [show b ∈ γ from hb]
  · split_ifs with hb
    · exact fun i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => hy b (List.mem_toFinset.2 hb) i j)
    · exact zero_mem _

theorem continuous_stepPt {n n' : Type*} {c : ℕ} (x₀ : Matrix n n' k) :
    Continuous fun e : StepVar n c n' → k => stepPt x₀ e := by
  refine continuous_const.add (continuous_matrix fun r s => ?_)
  simp only [of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_fill (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) : Continuous (fill hs x y) := by
  refine continuous_pi ?_
  rintro (⟨i, j⟩ | ⟨i, j⟩) <;> simp only [fill] <;> split_ifs
  · refine Continuous.matrix_transpose (Continuous.matrix_submatrix ?_ _ _)
    unfold downMap
    split_ifs with h
    · exact ((continuous_stepPt _).comp (continuous_apply (⟨j, h⟩ : Fin (G.m - 1)))).matrix_reindex _ _
    · exact continuous_const
    · exact continuous_const
  all_goals exact continuous_const

theorem continuous_phase (x : ColArgs G) : Continuous (phase x) := by
  have hp : ∀ (j : Fin (G.m - 1)) r s, Continuous fun e : Vars G => stepPt (x j) (e j) r s := fun j r s =>
    ((continuous_stepPt _).comp (continuous_apply j)).matrix_elem r s
  refine continuous_finsetSum _ fun j _ => (continuous_finsetSum _ fun i _ => hp j _ _).add ?_
  split_ifs
  · refine continuous_finsetSum _ fun r _ => Continuous.mul ?_ (hp j _ _)
    unfold rowVar
    split_ifs with h
    · refine continuous_finsetSum _ fun l _ => ?_
      split_ifs
      · exact hp ⟨_, h⟩ _ _
      · exact continuous_const
    · exact continuous_const
  · exact continuous_const


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_fill_entry (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) (j : Fin (G.m - 1))
    (rs : StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    ∃ a b c, ∀ e : Vars G, e j rs = fill hs x y e (.theta G.m j) a b - c := by
  refine ⟨frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega) rs.1.2,
    frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) rs.1.1,
    basePt _ (x j) rs.1.1 rs.1.2, fun e => ?_⟩
  rw [fill_theta, transpose_apply, downMap, dite_eq_left j.2]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, Matrix.add_apply, of_apply]
  rw [dite_eq_left rs.2, add_sub_cancel_left]

theorem exists_isCompact_of_mul_mem {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : GL m k) (B : GL n k) :
    ∃ K : Set (Matrix m n k), IsCompact K ∧ ∀ X, A.val * X * B.val ∈ matLat m (stdLat k n) → X ∈ K := by
  have hO : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have hC : IsCompact (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => (𝒪[k] : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO
  have hc : Continuous fun M : Matrix m n k => (A⁻¹).val * M * (B⁻¹).val :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨_, hC.image hc, fun X hX => ⟨A.val * X * B.val, fun i _ j _ => mem_matLat_stdLat.1 hX i j, ?_⟩⟩
  show (A⁻¹).val * (A.val * X * B.val) * (B⁻¹).val = X
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

theorem continuous_flatIntegrand (hs : 1 ≤ G.s) {ψ : AddChar k Circle} (hψ : Continuous ψ) {ϖ : kˣ} {e : ℕ}
    {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : Continuous (flatIntegrand hs ψ (moved G keep g T) x y) := by
  have hm : Continuous (G.moveArgs .one g) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  exact (continuous_const.mul (continuous_const.mul
    ((isLocallyConstant_of_isTensor hT).continuous.comp (hm.comp (continuous_fill hs x y))))).mul
    (continuous_subtype_val.comp (hψ.comp (continuous_phase x).neg))

theorem hasCompactSupport_flatIntegrand (hs : 1 ≤ G.s) (ψ : AddChar k Circle) {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : HasCompactSupport (flatIntegrand hs ψ (moved G keep g T) x y) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  choose a b c h using exists_fill_entry hs x y
  choose K hK hK' using fun j : Fin (G.m - 1) => exists_isCompact_of_mul_mem
    (Assignment.one.read (g (Edge.theta G.m j).tgt))⁻¹ (Assignment.one.read (g (Edge.theta G.m j).src))
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => Set.univ.pi fun rs =>
    (fun M => M (a j rs) (b j rs) - c j rs) '' K j) (isCompact_univ_pi fun j => isCompact_univ_pi fun rs =>
      (hK j).image ((continuous_id.matrix_elem _ _).sub continuous_const)) fun v hv => ?_
  have h0 : T (G.moveArgs .one g (fill hs x y v)) = 0 := by
    by_contra hne
    refine hv fun j _ rs _ => ⟨_, hK' j _ ?_, (h j rs v).symm⟩
    by_contra hn
    exact hne (hT.2.1 _ (.theta G.m j) (by have := j.2; simp [oppositePath]; omega) hn)
  simp [flatIntegrand, moved, Grid.pathAct, h0]

theorem flatIntegrable_of_isTensor [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hψ : Continuous ψ)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) : FlatIntegrable hs ψ ν T := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  intro g x y
  unfold varsVol
  exact (continuous_flatIntegrand hs hψ hT true g x y).integrable_of_hasCompactSupport
    (hasCompactSupport_flatIntegrand hs ψ hT true g x y)

theorem flatIntegrable [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} :
    IsUnif ϖ → Continuous ψ → G.IsTensor ϖ e (oppositePath G.m) T → FlatIntegrable hs ψ ν T :=
  fun _ hψ hT => flatIntegrable_of_isTensor hs ψ ν hψ hT

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinZeroFrequencyPartIsSmoothHolomorpStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinZeroFrequencyPart_isSmoothHolomorphic : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb R : ℂ → ℂ), Differentiable ℂ R → (∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) → GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bZero Zb 𝔞 𝔟) := by
  first | exact @GlobalTheory.HeckeTwo.bZero_isGood | exact GlobalTheory.HeckeTwo.bZero_isGood | (intros; apply GlobalTheory.HeckeTwo.bZero_isGood <;> assumption)
end

