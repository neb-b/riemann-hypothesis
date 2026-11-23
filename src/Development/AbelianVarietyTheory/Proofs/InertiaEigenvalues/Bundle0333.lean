module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfRationalLocalDuality
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

variable {l : ℕ} [Fact l.Prime]

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    (PD : PeriodData G ℚ_[l] K₀ K B BdR)

theorem cyclotomicTwist_differential_apply {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (f : G → LL) (x : G × G) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f x =
      algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1 := by
  simp [ReciprocityTheory.Def.d1, charRep, cycLL, Algebra.smul_def]

theorem cobL_iff_trace {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    [FiniteDimensional ℚ_[l] LL] [IsModuleTopology ℚ_[l] LL] (z : G × G → LL) :
    CobL PD z ↔ ∀ c : LL, CobL PD (fun x => Algebra.trace ℚ_[l] LL (c * z x)) := by
  haveI : ContinuousAdd LL := IsModuleTopology.toContinuousAdd ℚ_[l] LL
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  constructor
  · rintro ⟨f, hf, rfl⟩ c
    refine ⟨fun g => Algebra.trace ℚ_[l] LL (c * f g), ?_, ?_⟩
    · exact (IsModuleTopology.continuous_of_linearMap
        ((Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c))).comp hf
    · funext x
      rw [cyclotomicTwist_differential_apply, cyclotomicTwist_differential_apply]
      have e1 : c * (algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1) =
          (PD.χ x.1 : ℚ_[l]) • (c * f x.2) - c * f (x.1 * x.2) + c * f x.1 := by
        rw [Algebra.smul_def]; ring
      rw [e1, map_add (f := _), map_sub, map_smul, smul_eq_mul]
      simp
  · intro h
    choose f hf using h
    have hB := traceForm_nondegenerate ℚ_[l] LL
    let b := Module.finBasis ℚ_[l] LL
    let d := (Algebra.traceForm ℚ_[l] LL).dualBasis hB b
    refine ⟨fun g => ∑ i, f (b i) g • d i, ?_, ?_⟩
    · exact continuous_finsetSum _ fun i _ => ((hf (b i)).1).smul continuous_const
    · funext x
      rw [cyclotomicTwist_differential_apply]
      have hz : z x = ∑ i, (d.repr (z x) i) • d i := (d.sum_repr (z x)).symm
      have hc : ∀ i, d.repr (z x) i = (PD.χ x.1 : ℚ_[l]) * f (b i) x.2 - f (b i) (x.1 * x.2) + f (b i) x.1 := by
        intro i
        rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm,
          ← congrFun (hf (b i)).2 x, cyclotomicTwist_differential_apply]
        simp
      rw [hz]
      simp_rw [hc, add_smul, sub_smul, mul_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.smul_sum, Algebra.smul_def]

end Cob

section Main

variable (P : LocPrime l) {K : FinExt l}

def trPair {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l] :=
  LinearMap.mk₂ ℚ_[l] (fun x y => Algebra.trace ℚ_[l] LL (Pr x y))
    (fun x x' y => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])
    (fun x y y' => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])

theorem trPair_apply {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (x : V) (y : V') :
    trPair Pr x y = Algebra.trace ℚ_[l] LL (Pr x y) := rfl

theorem isDual1_trPair {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {Pr : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : IsDual1 (P.PD K) ρ ρ' Pr) : IsDual1 (P.PD K) (resQ ρ) (resQ ρ') (trPair Pr) := by
  have hB := traceForm_nondegenerate ℚ_[l] LL
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨fun g x y => ?_, fun x hx => h2 x fun y => ?_, fun y hy => h3 y fun x => ?_, ?_⟩
  · rw [resQ_apply, resQ_apply, trPair_apply, trPair_apply, h1]
    have e : ((cycLL (P.PD K) LL g : LLˣ) : LL) * Pr x y = ((P.PD K).χ g : ℚ_[l]) • Pr x y := by
      simp [cycLL, Algebra.smul_def]
    rw [e, map_smul, smul_eq_mul]
    simp [cycLL]
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul]
    exact hx (c • y)
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul]
    exact hy (c • x)
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', h4]

end Main

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkACore_of_rationalDuality (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
    (h : GlobalTheory.Published.BlochKato.RationalDuality (P.PD K)) : bkACore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A A' Pr hdR hP
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : FiniteDimensional ℚ_[l] A'.V := Module.Finite.trans LL A'.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  haveI : IsModuleTopology ℚ_[l] A'.V := isModuleTopology_of_tower ℚ_[l] LL A'.V
  haveI : ContinuousConstSMul ℚ_[l] A.V := ⟨fun c => by
    have hc : Continuous fun x : A.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  haveI : ContinuousConstSMul ℚ_[l] A'.V := ⟨fun c => by
    have hc : Continuous fun x : A'.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  have key := h A.V A'.V (resQ A.ρ) (resQ A'.ρ) (trPair Pr) A.cont A'.cont
    ((isDR_resQ_iff P A.ρ).mpr hdR) (isDual1_trPair P hP)
  have cupS : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a (c • b) = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cupS' : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) (c • a) b = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cup1 : ∀ (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a b = fun x => Algebra.trace ℚ_[l] LL (1 * cupL A'.ρ Pr a b x) := by
    intro a b; funext x
    simp [cupL, trPair_apply]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.1 a ha)]
    constructor
    · intro H b hb
      rw [cobL_iff_trace]
      intro c
      rw [← cupS]
      exact H (c • b) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A'.ρ).smul_mem c hb))
    · intro H b hb
      have := (cobL_iff_trace (P.PD K) _).mp (H b ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp hb)) 1
      rwa [← cup1] at this
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.2 b hb)]
    constructor
    · intro H a ha
      rw [cobL_iff_trace]
      intro c
      rw [← cupS']
      exact H (c • a) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A.ρ).smul_mem c ha))
    · intro H a ha
      have := (cobL_iff_trace (P.PD K) _).mp (H a ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp ha)) 1
      rwa [← cup1] at this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEisensteinImageTeichmullerPow
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EisImage

theorem isUnit_of_constantCoeff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : WittVector l O) (h : IsUnit (WittVector.constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have h1 : c * WittVector.teichmuller l ((u⁻¹ : Oˣ) : O) - 1 ∈ Ideal.span {(l : WittVector l O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have h2 := IsAdicComplete.le_jacobson_bot (Ideal.span {(l : WittVector l O)}) h1
  have h3 := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ h2
  exact isUnit_of_mul_isUnit_left h3

theorem exists_eq {R : Type} [CommRing R] (l : R) (P : Polynomial R) (hm : P.Monic) (hd : 0 < P.natDegree)
    (hc : ∀ i < P.natDegree, l ∣ P.coeff i) (w : R) (h0 : P.coeff 0 = l * w) :
    ∃ G : Polynomial R, P = Polynomial.X ^ P.natDegree +
      Polynomial.C l * (Polynomial.C w + Polynomial.X * G) := by
  have h1 : Polynomial.C l ∣ (P - Polynomial.X ^ P.natDegree).divX := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_divX, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy (i + 1) P.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]
      exact hc _ h
    · rw [if_pos h, h, hm.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]
      exact dvd_zero _
  obtain ⟨G, hG⟩ := h1
  refine ⟨G, ?_⟩
  have h2 := Polynomial.X_mul_divX_add (P - Polynomial.X ^ P.natDegree)
  rw [hG, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hd.ne, sub_zero, h0, map_mul] at h2
  linear_combination -h2

theorem map_E_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsLocalRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ¬ IsUnit (ψ bk.flat) → ∃ w : WittVector l O, IsUnit w ∧ WittVector.map ψ (bk.ev bk.E) = WittVector.teichmuller l (ψ bk.flat) ^ bk.Ep.natDegree + ((l : ℕ) : WittVector l O) * w := by
  intro l _ K bk O _ _ _ _ ψ hψ
  obtain ⟨w₀, hw₀⟩ := bk.coeff_zero
  obtain ⟨G, hG⟩ := exists_eq (l : Wq l bk.a) bk.Ep bk.monic bk.deg_pos bk.dvd_coeff w₀ hw₀
  let f : Polynomial (Wq l bk.a) →+* WittVector l O :=
    (WittVector.map ψ).comp (bk.ev.comp (Polynomial.coeToPowerSeries.ringHom))
  have hX : f Polynomial.X = WittVector.teichmuller l (ψ bk.flat) := by
    change WittVector.map ψ (bk.ev ((Polynomial.X : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧)) = _
    rw [Polynomial.coe_X, bk.ev_X, WittVector.map_teichmuller]
  refine ⟨f (Polynomial.C (w₀ : Wq l bk.a) + Polynomial.X * G), ?_, ?_⟩
  · apply isUnit_of_constantCoeff
    have hu : IsUnit (WittVector.constantCoeff (f (Polynomial.C (w₀ : Wq l bk.a)))) :=
      ((w₀.isUnit.map Polynomial.C).map f).map _
    rw [map_add (f := _), map_mul, hX, map_add (f := _), map_mul, WittVector.constantCoeff_apply (WittVector.teichmuller l _),
      WittVector.teichmuller_coeff_zero]
    by_contra hn
    have h1 : ψ bk.flat * WittVector.constantCoeff (f G) ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ hψ
    have h2 := Ideal.sub_mem _ (show _ ∈ IsLocalRing.maximalIdeal O from hn) h1
    rw [add_sub_cancel_right] at h2
    exact h2 hu
  · have h1 := congrArg f hG
    rw [map_add (f := _), map_pow, hX, map_mul, map_natCast Polynomial.C, map_natCast f] at h1
    exact h1

end GlobalTheory.BSP.EisImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

section Red

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

def evRed : bk.S →+* OCb l := (WittVector.constantCoeff (p := l) (R := OCb l)).comp bk.ev

theorem evRed_X : bk.evRed X = bk.flat := by
  simp [evRed, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem flat_ne_zero : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0]; exact WittVector.teichmuller_zero l
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE : bk.ev bk.E = (l : Ainf l) * wA l bk.a (w : Wq l bk.a) := by
    conv_lhs => rw [eq_X_mul_shift_add_const bk.E]
    rw [map_add (f := _), map_mul, hX, zero_mul, zero_add, bk.ev_C, Polynomial.constantCoeff_coe, hw, map_mul,
      map_natCast]
  have hl' : (l : Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev, hE, Ideal.span_singleton_mul_right_unit ((w.isUnit).map (wA l bk.a))]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_natCast] at hl'
  exact Nat.cast_ne_zero.2 hl.out.ne_zero hl'

theorem dvd_of_evRed_eq_zero (x : bk.S) (hx : bk.evRed x = 0) : (l : bk.S) ∣ x := by
  set r := WittVector.constantCoeff (p := l) (R := Fq l bk.a) with hr
  by_cases h : PowerSeries.map r x = 0
  · exact dvd_of_map_eq_zero l bk.a x h
  exfalso
  set xb := PowerSeries.map r x with hxb
  set m := xb.order.toNat
  set vb := divXPowOrder xb
  have hvb : constantCoeff vb ≠ 0 := fun h' => h (constantCoeff_divXPowOrder_eq_zero_iff.1 h')
  let v : bk.S := PowerSeries.mk fun n => WittVector.teichmuller l (coeff n vb)
  have hv : PowerSeries.map r v = vb := by
    ext n
    simp [v, hr, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  have hvu : IsUnit v := by
    rw [isUnit_iff_constantCoeff]
    have : constantCoeff v = WittVector.teichmuller l (constantCoeff vb) := by
      simp [v, ← coeff_zero_eq_constantCoeff]
    rw [this]
    exact (Ne.isUnit hvb).map _
  obtain ⟨y, hy⟩ := dvd_of_map_eq_zero l bk.a (x - X ^ m * v) (by
    rw [map_sub, map_mul, map_pow, PowerSeries.map_X, hv, X_pow_order_mul_divXPowOrder, sub_self])
  have h1 : bk.evRed x = bk.flat ^ m * bk.evRed v := by
    have : x = X ^ m * v + (l : bk.S) * y := by linear_combination hy
    rw [this, map_add (f := _), map_mul, map_mul, map_pow, evRed_X, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
  rw [hx] at h1
  exact mul_ne_zero (pow_ne_zero _ bk.flat_ne_zero) (hvu.map bk.evRed).ne_zero h1.symm

theorem dvd_of_dvd_ev (x : bk.S) (h : (l : Ainf l) ∣ bk.ev x) : (l : bk.S) ∣ x := by
  apply bk.dvd_of_evRed_eq_zero
  obtain ⟨z, hz⟩ := h
  simp only [evRed, RingHom.comp_apply, hz, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem eq_zero_of_forall_pow_dvd (w : Wq l bk.a) (h : ∀ n : ℕ, (l : Wq l bk.a) ^ n ∣ w) : w = 0 := by
  by_contra hw
  obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul w hw
  obtain ⟨c, hc⟩ := h (m + 1)
  have hbc : b = (l : Wq l bk.a) * c := by
    apply mul_left_cancel₀ (pow_ne_zero m (WittVector.p_nonzero l (Fq l bk.a)))
    rw [← hb, hc]; ring
  apply hb0
  have := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) hbc
  rwa [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, WittVector.constantCoeff_apply] at this

theorem ev_injective : Function.Injective bk.ev := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have key : ∀ n : ℕ, ∀ x : bk.S, bk.ev x = 0 → (l : bk.S) ^ n ∣ x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      obtain ⟨x', rfl⟩ := bk.dvd_of_dvd_ev x (by rw [hx]; exact dvd_zero _)
      have h2 : bk.ev x' = 0 := ainf_torsionFree _ (by rw [← map_natCast bk.ev, ← map_mul]; exact hx)
      obtain ⟨z, hz⟩ := ih x' h2
      exact ⟨z, by rw [hz, pow_succ]; ring⟩
  refine PowerSeries.ext fun k => ?_
  rw [map_zero]
  refine bk.eq_zero_of_forall_pow_dvd _ fun n => ?_
  obtain ⟨z, hz⟩ := key n x hx
  refine ⟨coeff k z, ?_⟩
  rw [hz, ← map_natCast (C : Wq l bk.a →+* (Wq l bk.a)⟦X⟧), ← map_pow, coeff_C_mul]

end Red

theorem evW_isUnit_injective_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsUnit (bk.evW bk.E) ∧ Function.Injective bk.evW ∧
      ∀ x : bk.S, ((l : ℕ) : Ainf l) ∣ bk.ev x → ((l : ℕ) : bk.S) ∣ x :=
  fun _ _ _ bk => ⟨isUnit_inclW_of_span bk.span_ev, GlobalTheory.Prism.inclW_injective.comp bk.ev_injective,
    bk.dvd_of_dvd_ev⟩

end GlobalTheory.BSP.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExistsAdicSumOfNullFamily
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem TopBasis.exists_sum_of_null {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (σ : ι → S) (hσ : ∀ n : ℕ, {i | σ i ∉ I ^ n}.Finite) :
    ∃ L : A, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, s (σ i) * TB.b i ∈ (I ^ n).map s := by
  classical
  let F : ℕ → Finset ι := fun n => (hσ n).toFinset
  have memF : ∀ n i, i ∈ F n ↔ σ i ∉ I ^ n := fun n i => by simp [F]
  have tail : ∀ m (G : Finset ι), F m ⊆ G →
      ∑ i ∈ G, s (σ i) * TB.b i - ∑ i ∈ F m, s (σ i) * TB.b i ∈ (I ^ m).map s := by
    intro m G hG
    rw [← Finset.sum_sdiff_eq_sub hG]
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h : i ∉ F m := (Finset.mem_sdiff.1 hi).2
    rw [memF] at h
    exact not_not.1 h
  have mono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} h i hi => by
    rw [memF] at hi ⊢
    exact fun h' => hi (Ideal.pow_le_pow_right h h')
  have key : ∀ (n : ℕ) (x : A), x ∈ ((I.map s) ^ n • ⊤ : Submodule A A) ↔ x ∈ (I ^ n).map s := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.map_pow]
  obtain ⟨L, hL⟩ := TB.complete.toIsPrecomplete.prec (f := fun n => ∑ i ∈ F n, s (σ i) * TB.b i)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, key, ← neg_sub]
      exact neg_mem (tail m (F n) (mono hmn)))
  refine ⟨L, fun n => ⟨F n, fun G hG => ?_⟩⟩
  have h1 := hL n
  rw [SModEq.sub_mem, key] at h1
  have h2 := tail n G hG
  have e : L - ∑ i ∈ G, s (σ i) * TB.b i =
      -((∑ i ∈ F n, s (σ i) * TB.b i - L) + (∑ i ∈ G, s (σ i) * TB.b i - ∑ i ∈ F n, s (σ i) * TB.b i)) := by
    ring
  rw [e]
  exact neg_mem (add_mem h1 h2)

theorem exists_sum_null_ev : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type)
    (TB : TopBasis bk.ev bk.J ι) (σ : ι → bk.S), (∀ n : ℕ, {i | σ i ∉ bk.J ^ n}.Finite) →
    ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
  fun _ _ _ _ _ TB σ hσ => TB.exists_sum_of_null σ hσ

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMemIdealPowOfXPowMulMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem X_pow_natDegree_mem_lE (bk : BK K) : (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have hdvd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
    · subst h; rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hdvd
  have h1 := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hq
  simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
    Polynomial.coe_C] at h1
  rw [map_natCast] at h1
  have h2 : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * (q : bk.S) := by
    linear_combination -h1
  rw [h2]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem E_mem_span_l_X (bk : BK K) : bk.E ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hc : constantCoeff bk.E = (l : Wq l bk.a) * w := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hw]
  rw [eq_shift_mul_X_add_const bk.E, hc, map_mul, map_natCast]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

end GlobalTheory.BSP.BK

theorem GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ),
    ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S,
      (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  intro l _ K bk N
  refine ⟨N, fun m => ⟨N + (m + bk.Ep.natDegree * N), fun s hs => ?_⟩⟩
  have hJ : bk.J ≤ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} :=
    sup_le le_sup_left (Ideal.span_singleton_le_iff_mem _ |>.2 (BK.E_mem_span_l_X bk))
  have h1 : bk.J ^ (N + (m + bk.Ep.natDegree * N)) ≤
      Ideal.span {(l : bk.S) ^ N} ⊔ Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)} := by
    refine (Ideal.pow_right_mono hJ _).trans ?_
    have := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {(X : bk.S)})
      (n := N) (m := m + bk.Ep.natDegree * N)
    rwa [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at this
  have hs' := (sup_le h1 le_sup_left : _ ≤ Ideal.span {(l : bk.S) ^ N} ⊔
      Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)}) hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hs'
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  set t := s - (X : bk.S) ^ (bk.Ep.natDegree * N) * g with ht
  have htm : (X : bk.S) ^ m * t = C ((l : Wq l bk.a) ^ N) * h := by
    rw [ht, map_pow, map_natCast, mul_sub, ← hyz]; ring
  have ht' : t = C ((l : Wq l bk.a) ^ N) * PowerSeries.mk (fun k => coeff (k + m) h) := by
    ext k
    have := congrArg (coeff (k + m)) htm
    rw [coeff_X_pow_mul', if_pos (Nat.le_add_left m k), Nat.add_sub_cancel, coeff_C_mul] at this
    rw [this, coeff_C_mul, coeff_mk]
  have hs2 : s = ((X : bk.S) ^ bk.Ep.natDegree) ^ N * g + (l : bk.S) ^ N * PowerSeries.mk (fun k => coeff (k + m) h) := by
    have : s = t + (X : bk.S) ^ (bk.Ep.natDegree * N) * g := by rw [ht]; ring
    rw [this, ht', map_pow, map_natCast, ← pow_mul]; ring
  rw [hs2]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (BK.X_pow_natDegree_mem_lE bk) N))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) N))
end
end

