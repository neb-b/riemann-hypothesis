module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitPlace

theorem isSplit_of_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal →
      Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) : IsSplit (E := E) v := by
  classical
  haveI hfin : Module.Finite (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI hint : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_finite (𝓞 F) (𝓞 E)

  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact h2

  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [hdeg] at hsum

  have hover : ∀ Q : Ideal (𝓞 E), Q.LiesOver v.asIdeal → (p : 𝓞 E) ∈ Q := by
    intro Q hQo
    have hmem : (p : 𝓞 F) ∈ Q.under (𝓞 F) := by
      rw [← hQo.over]
      exact hv
    have hmem' : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ Q := hmem
    simpa using hmem'

  have hf : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.inertiaDeg (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hN : Ideal.absNorm Q = p := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).1
    have key : Ideal.absNorm v.asIdeal ^ Q.inertiaDeg (𝓞 F) = p := by
      rw [Ideal.absNorm_pow_inertiaDeg v.asIdeal Q]
      exact hN
    exact Nat.Prime.eq_one_of_pow (by rw [key]; exact hp)

  have he : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hsq : (p : 𝓞 E) ∉ Q ^ 2 := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).2
    have hle : Q.ramificationIdx (𝓞 F) ≤ 1 := by
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot]
      by_contra hlt
      push_neg at hlt
      have hmap : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q ^ 2 :=
        Ideal.le_pow_of_le_ramificationIdx' hlt
      apply hsq
      have hin := hmap (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv)
      simpa using hin
    have hpos : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) Q
    show Q.ramificationIdx (𝓞 F) = 1
    omega

  by_contra hns
  obtain ⟨Q0, hQ0p, hQ0o⟩ : ∃ Q0 : Ideal (𝓞 E), Q0.IsPrime ∧ Q0.LiesOver v.asIdeal := by
    first
    | obtain ⟨Q0, hQ0m, hQ0o⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
      exact ⟨Q0, hQ0m.isPrime, hQ0o⟩
    | obtain ⟨Q0, hQ0⟩ := Set.nonempty_of_ncard_ne_zero
        (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))
      exact ⟨Q0, hQ0.1, hQ0.2⟩
  let q0 : v.asIdeal.primesOver (𝓞 E) := ⟨Q0, hQ0p, hQ0o⟩
  have honly : ∀ q : v.asIdeal.primesOver (𝓞 E), q = q0 := by
    rintro ⟨Q, hQp, hQo⟩
    by_contra hne
    apply hns
    haveI := hQo
    haveI := hQ0o
    refine ⟨⟨Q, hQp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      ⟨Q0, hQ0p, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q0⟩, ?_, hQo.over.symm, hQ0o.over.symm⟩
    intro hPQ
    exact hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ))
  rw [Finset.sum_eq_single q0 (fun b _ hb => absurd (honly b) hb)
    (fun h0 => absurd (Finset.mem_univ q0) h0), he q0, hf q0] at hsum
  omega

theorem isSplit_of_splitsCompletely : ∀ (D : D7) (p : ℕ), SplitsCompletely D p → ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal → IsSplit (E := D.host.E) v := by
  intro D p hp v hv
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    first
    | haveI : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx
      exact IsQuadraticExtension.finrank_eq_two _ _
    | have hE := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
      have hF := Formalism.HC.HostAx.finrank_hostF D.host.toHostAx
      have hm := Module.finrank_mul_finrank ℚ D.host.F D.host.E
      have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
      rw [hE, hF] at hm
      rw [hF] at hpos
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  exact isSplit_of_norm h2 hp.1 hp.2 v hv

end GlobalTheory.SplitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.L2.Host (IsUnifAt atFin)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

namespace InertValue

theorem single_ne' {K : Type} [Field K] [NumberField K] {P Q : HeightOneSpectrum (𝓞 K)} (h : Q ≠ P)
    (u : (P.adicCompletion K)ˣ) : (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 K) K) Q = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem exists_isUnifAt (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    ∃ a : (Fv F v)ˣ, IsUnifAt w (Units.map (complMap h).toMonoidHom a) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 (algebraMap F (Fv F v) π) ((map_ne_zero _).2 hπ0), ?_⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have : w.asIdeal.LiesOver v.asIdeal := ⟨by subst h; rfl⟩
  have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [pow_one, hw']
    · exact InertChart.not_map_le_sq hw
  show Valued.v (complMap h (algebraMap F (Fv F v) π)) = WithZero.exp (-1)
  rw [complMap_algebraMap]
  have hvw : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap F E π)) = w.valuation E (algebraMap F E π) := by
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap F E π)
  rw [hvw, ← HeightOneSpectrum.valuation_liesOver E v w,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot, he, pow_one, hπ]

theorem locIdele_complMap (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (a : (Fv F v)ˣ) :
    locIdele F w (Units.map (complMap h).toMonoidHom a) =
      ideleMap F E (GlobalTheory.CMVal.finIdele F (GlobalTheory.CMVal.single v a)) := by
  subst h
  have key : (finAdEquiv F E).symm ((GlobalTheory.CMVal.single w (Units.map (complMap rfl).toMonoidHom a) :
      (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) =
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E) := by
    rw [RingEquiv.symm_apply_eq]
    refine FiniteAdeleRing.ext (h := fun u => ?_)
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = _)]
    simp only [Algebra.TensorProduct.map_tmul, toCompl_tmul, map_one, mul_one]
    classical
    have same : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (z : (P.adicCompletion K)ˣ),
        ((GlobalTheory.CMVal.single P z : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) P = z :=
      fun K _ _ P z => Pi.mulSingle_eq_same (M := fun R : HeightOneSpectrum (𝓞 K) => R.adicCompletion K) P
        (z : P.adicCompletion K)
    by_cases hu : u = w
    · subst hu
      rw [same]
      exact congrArg (complMap (rfl : u.under (𝓞 F) = _)) (same F _ a).symm
    · have hne : u.under (𝓞 F) ≠ w.under (𝓞 F) := fun h' => hu ((InertChart.under_eq_iff hw u).1 h')
      rw [single_ne' hu]
      have e2 : ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
          FiniteAdeleRing (𝓞 F) F) (u.under (𝓞 F)) = 1 := single_ne' hne a
      exact ((congrArg (complMap (rfl : u.under (𝓞 F) = _)) e2).trans (map_one _)).symm
  apply Units.ext
  show 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm ((GlobalTheory.CMVal.single w
      (Units.map (complMap rfl).toMonoidHom a) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)) =
    algebraMap (AF F) (AF F ⊗[F] E) ((MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  rw [key]
  generalize ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = s
  have h2 : extZero F E 1 = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ 1 1
  have h3 : extZero F E (s ⊗ₜ[F] (1 : E)) = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ s 1
  have h4 : algebraMap (AF F) (AF F ⊗[F] E) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) ⊗ₜ[F] (1 : E) := rfl
  have hX : (1 : AF F) - (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) +
      (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) := by
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) - 0 + 0 = 1
      simp
    · show (1 : Af F) - 1 + s = s
      simp
  rw [h2, h3, h4, ← hX, TensorProduct.add_tmul, TensorProduct.sub_tmul]
  rfl

theorem eta_sq (h2 : Module.finrank F E = 2) {η : (AF F)ˣ →* Circle} (hη : IsEta F E η) (a : (AF F)ˣ) :
    η a ^ 2 = 1 := by
  have hn := hη.2.2.1 (ideleMap F E a)
  have hnorm : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (ideleMap F E a) = a ^ 2 := by
    apply Units.ext
    show Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (a : AF F)) = ((a ^ 2 : (AF F)ˣ) : AF F)
    rw [Units.val_pow_eq_pow_val,
      Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)), Fintype.card_fin, h2]
  rw [hnorm, map_pow] at hn
  exact hn

end InertValue


open InertValue in
theorem val_sq_eq_one_of_isInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ) (hμ : ResEta F E μ b)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : IsInertAt F E v w) (hu : UnrAt μ w) :
    val μ w ^ 2 = 1 := by
  obtain ⟨⟨η, hη⟩, hres⟩ := hμ
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hv : w.under (𝓞 F) = v := by
    ext1
    symm
    refine v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top ?_
    exact Ideal.map_le_iff_le_comap.1 hw'.le
  obtain ⟨a, ha⟩ := exists_isUnifAt hw hv
  rw [← UnrAt.locChar_eq_val hu ha]
  simp only [locChar, MonoidHom.comp_apply]
  rw [locIdele_complMap hw hv a, hres η hη, ← map_pow, ← pow_mul, mul_comm, pow_mul, eta_sq h2 hη, one_pow,
    map_one]

end GlobalTheory.LFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleNormalizedAbsEqAdelicAbsNorm
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem absE_eq_prod_norm_fstA_sndA (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] (y : (AF F ⊗[F] E)ˣ) :
    (∏ w, ‖(fstA F (Algebra.norm (AF F) (y : AF F ⊗[F] E))) w‖) *
      ∏ᶠ v, ‖evalV F v (sndA F (Algebra.norm (AF F) (y : AF F ⊗[F] E)))‖ = (GlobalTheory.Doubling.absE F E y : ℝ) := by
  have hf := GlobalTheory.Doubling.finite_mulSupport_absEv (F := F) (E := E) y
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  simp only [GlobalTheory.Doubling.absEw_unitInf] at *
  simp only [GlobalTheory.Doubling.absEv_unitFin] at hf ⊢
  rw [show ((∏ᶠ v, ‖GlobalTheory.AdelicU.evFin F v (Algebra.norm (AF F) y.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v, ((‖GlobalTheory.AdelicU.evFin F v (Algebra.norm (AF F) y.1)‖₊ : ℝ≥0) : ℝ) from
    NNReal.toRealHom.toMonoidHom.map_finprod hf]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w), pow_one, coe_nnnorm]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TprodNeZeroOfNe
section
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Contr

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]


omit [CompleteSpace H₁] [CompleteSpace FF] in
theorem norm_isoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_isContr {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  let L : H₂ → (H₁ →L[ℂ] FF) := fun y =>
    (Tm.flip y).mkContinuous ‖y‖ fun x => by simp [norm_isoBilin hI, mul_comm]
  let f : FF → H₂ → H₁ := fun φ y => ContinuousLinearMap.adjoint (L y) φ
  have hf : ∀ φ y x, ⟪x, f φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := fun φ y x => by
    simp only [f, ContinuousLinearMap.adjoint_inner_right]
    rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f ?_ ?_ ?_ ?_, hf⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, RingHom.id_apply]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf, map_add (f := _), inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, map_smul, inner_smul_left]


omit [CompleteSpace H₁] [CompleteSpace FF] in
theorem isContr_unique {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} {It It' : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁}
    (h : IsContr Tm It) (h' : IsContr Tm It') : It = It' := by
  ext φ y
  exact ext_inner_left ℂ fun x => by rw [h, h']

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  obtain ⟨It, hIt⟩ := exists_isContr hI
  exact ⟨⟨It, hIt, fun It' h' => isContr_unique h' hIt⟩, fun It' h' => contrProps_of hI hE h'⟩

theorem tprod_ne_zero_of_ne {ι : Type} [Fintype ι] {B : ι → Type} [∀ τ, AddCommGroup (B τ)]
    [∀ τ, Module ℂ (B τ)] (w : ∀ τ, B τ) (hw : ∀ τ, w τ ≠ 0) : PiTensorProduct.tprod ℂ w ≠ 0 := by
  classical
  have : ∀ τ, ∃ f : Module.Dual ℂ (B τ), f (w τ) ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hw τ ((Module.forall_dual_apply_eq_zero_iff ℂ (w τ)).1 hc)
  choose f hf using this
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f)) h
  simp [Finset.prod_eq_zero_iff, hf] at this

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ Itl
  classical
  have hinj : ∀ τ, Function.Injective fun s : σ τ => e ⟨τ, s⟩ := fun τ =>
    e.injective.comp sigma_mk_injective
  let r : (Var →₀ ℕ) → ∀ τ, σ τ →₀ ℕ := fun m τ => m.comapDomain (fun s => e ⟨τ, s⟩) (hinj τ).injOn
  let It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ :=
    (MvPolynomial.basisMonomials Var ℂ).constr ℂ fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1)
  have hr : ∀ m : ∀ τ, σ τ →₀ ℕ, r (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩) = m := by
    intro m
    funext τ
    ext s
    simp only [r, Finsupp.comapDomain_apply, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply_of_injective (hinj τ) _ _
    · intro τ' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨s', hs'⟩
      exact hne (congrArg Sigma.fst (e.injective hs'))
    · simp
  have key : It.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun τ => (MvPolynomial.rename (fun s : σ τ => e ⟨τ, s⟩)).toLinearMap) =
      (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap Itl := by
    apply Module.Basis.ext_multilinear fun τ => MvPolynomial.basisMonomials (σ τ) ℂ
    intro m
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials,
      MvPolynomial.rename_monomial, PiTensorProduct.mapMultilinear_apply]
    rw [← MvPolynomial.monomial_sum_one]
    have := (MvPolynomial.basisMonomials Var ℂ).constr_basis ℂ (fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1))
      (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩)
    rw [hr] at this
    simpa [It] using this
  have hT : IsTensorIt e Itl It := by
    intro P v
    have := congrArg (fun F => F P (PiTensorProduct.tprod ℂ v)) key
    simpa using this
  refine ⟨It, hT, fun hne h0 => ?_⟩
  have : ∀ τ, ∃ P v, Itl τ P v ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hne τ (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using this
  apply tprod_ne_zero_of_ne _ hPv
  rw [← hT P v, h0]
  rfl

theorem contraction : Contraction := ⟨contrHilbert, contrTensor⟩

end GlobalTheory.Contr

end
end

