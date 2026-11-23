module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNormalisationModelLocalizationX

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInCurveComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchInCurveComponent.proof (h₁ : BranchInComponent.Statement) :
    BranchInCurveComponent.Statement := by
  intro n I q c hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2
  have hq : q ∈ zeroSet J := c.map_zero ▸ hmaps (Metric.mem_ball_self c.radius_pos)
  refine ⟨J, hJ, ?_, Filter.mem_of_superset (Metric.ball_mem_nhds _ c.radius_pos) hmaps⟩
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := inferInstance
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have he1 : (e : WithBot ℕ∞) ≤ 1 := by
    rw [← LocalDimDomain.proof n e J hJp he q hq, ← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.map_mono hIJ))
      (Ideal.Quotient.factor_surjective _)
  have he0 : e ≠ 0 := by
    rintro rfl
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.2 (by simpa using he)
    have hJq : J = RingHom.ker (eval q) :=
      (Ideal.Quotient.maximal_of_isField J Ring.KrullDimLE.isField_of_isDomain).eq_of_le
        (RingHom.ker_ne_top _) fun f hf ↦ RingHom.mem_ker.2 (hq f hf)
    have hr := c.radius_pos
    have ht : (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
      rw [mem_ball_zero_iff, pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      linarith
    have hct : c.toFun (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) = c.toFun 0 := by
      rw [c.map_zero]
      funext i
      have hmem : X i - C (q i) ∈ J := by
        rw [hJq, RingHom.mem_ker]
        simp
      simpa [sub_eq_zero] using hmaps ht _ hmem
    have h0 := congrFun (c.injOn ht (Metric.mem_ball_self hr) hct) 0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h0
    linarith
  rw [he]
  have : e ≤ 1 := by exact_mod_cast he1
  have : e = 1 := by omega
  subst this
  rfl

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchNormalisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchNormalisation.proof (h₀ : BranchGermDimOne.Statement) (h₁ : BranchPlace.Statement)
    (h₂ : SameOrderBranchesMeet.Statement) (h₃ : PlaceHasBranch.Statement)
    (h₄ : OrdDeterminesPlace.Statement) (h₅ : CurveResidueDegree.Statement)
    (h₆ : OrdFiniteNonZeroDivisor.Statement) : BranchNormalisation.Statement := by
  intro n I q m c hrad hm hcov hdisj
  have hdim := h₀ n I q m c hm hcov
  refine ⟨hdim, fun f hf ↦ h₆ n I q f hrad hdim fun P ↦ ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj P
    rw [hb f]
    exact hf b
  choose P hP using fun b ↦ h₁ n I q (c b) hrad hdim

  have hcongr : ∀ Q Q' : MaximalSpectrum (curveNormalisation I q), Q = Q' → ∀ f : MvPolynomial (Fin n) ℂ,
      Ring.ord (Localization.AtPrime Q.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
      Ring.ord (Localization.AtPrime Q'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
    rintro Q _ rfl f
    rfl
  have hinj : Function.Injective P := by
    intro b b' hbb
    by_contra hne
    obtain ⟨x, hx, hxq⟩ := h₂ n I q (c b) (c b') hrad hdim fun f ↦
      (hP b f).symm.trans ((hcongr _ _ hbb f).trans (hP b' f))
    exact hxq (hdisj b b' hne hx)
  have hsurj : Function.Surjective P := by
    intro Q
    obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj Q
    exact ⟨b, h₄ n I q hrad hdim (P b) Q fun f ↦ (hP b f).trans (hb f).symm⟩
  exact ⟨Equiv.ofBijective P ⟨hinj, hsurj⟩, fun b ↦ ⟨h₅ n I q hrad hdim (P b), hP b⟩⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMHeightAddDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

theorem CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime (hreg : CMRegularElement.Statement.{u}) :
    ∀ (n : ℕ) (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B], ringKrullDim B = n →
      ∀ (P : Ideal B) [P.IsPrime], (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) = ringKrullDim B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B _ _ hn P hP
  refine le_antisymm (height_add_ringKrullDim_quotient_le P) ?_
  by_cases hmin : P ∈ minimalPrimes B
  · rw [Ideal.height_eq_zero_iff.mpr hmin, ringKrullDim_quotient_eq_of_mem_minimalPrimes hmin]
    simp

  have hfin := minimalPrimes.finite_of_isNoetherianRing (R := B)
  obtain ⟨y, hyP, hyq⟩ : ∃ y ∈ P, ∀ q ∈ minimalPrimes B, y ∉ q := by
    by_contra! h
    have hsub : (P : Set B) ⊆ ⋃ i ∈ (↑hfin.toFinset : Set (Ideal B)), (id i : Set B) := by
      intro z hz
      obtain ⟨q, hq, hzq⟩ := h z hz
      exact Set.mem_biUnion (by simpa using hq) hzq
    obtain ⟨q, hq, hPq⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun i hi _ _ => ((Set.Finite.mem_toFinset hfin).mp hi).1.1)).mp hsub
    have hq' : q ∈ minimalPrimes B := (Set.Finite.mem_toFinset hfin).mp hq
    have hqP : q ≤ P := hq'.2 ⟨hP, bot_le⟩ hPq
    exact hmin (le_antisymm hPq hqP ▸ hq')
  have hym : y ∈ maximalIdeal B := le_maximalIdeal hP.ne_top hyP
  obtain ⟨hynzd, hCM⟩ := hreg B y hym hyq
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hynzd hym
  obtain ⟨rs', -, -, hd'⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B ⧸ Ideal.span {y})
  have hlt : rs'.length < n := by
    have h1 : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hn, ← hdim, hd']
      push_cast
      rfl
    have h2 : rs'.length + 1 = n := by exact_mod_cast h1
    omega
  have hle : Ideal.span {y} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk (Ideal.span {y}))).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hle
  have hIH := ih rs'.length hlt (B ⧸ Ideal.span {y}) hd' (P.map (Ideal.Quotient.mk (Ideal.span {y})))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hIH
  have hc := height_map_add_one_le_of_mem_nonZeroDivisors hynzd P hyP
  calc ringKrullDim B = ringKrullDim (B ⧸ Ideal.span {y}) + 1 := hdim.symm
    _ = ((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) + 1 := by
        rw [hIH]
    _ = (((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        rw [WithBot.coe_add, WithBot.coe_one, add_right_comm]
    _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        gcongr

theorem CMHeightAddDim.proof (hreg : CMRegularElement.Statement.{u}) : CMHeightAddDim.Statement.{u} := by
  intro B _ _ J hJ
  obtain ⟨rs, -, -, hd⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hprime := CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime hreg rs.length B hd
  refine le_antisymm ?_ ?_
  ·
    have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    have : Nonempty (PrimeSpectrum (B ⧸ J)) := inferInstance
    rw [show ringKrullDim (B ⧸ J) = Order.krullDim (PrimeSpectrum (B ⧸ J)) from rfl,
      Order.krullDim_eq_iSup_coheight_of_nonempty, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (OrderTop.bddAbove _)]
    refine iSup_le fun a => ?_
    obtain ⟨a, ha⟩ := a
    set Q := a.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hJQ : J ≤ Q := fun z hz => by
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact Ideal.zero_mem _
    have hmap : a = Q.map (Ideal.Quotient.mk J) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective a).symm
    have hco : (Order.coheight (⟨a, ha⟩ : PrimeSpectrum (B ⧸ J)) : WithBot ℕ∞) = ringKrullDim (B ⧸ Q) := by
      rw [← ringKrullDim_quotient_eq_coheight a,
        ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE hJQ))]
    rw [WithBot.coe_add, hco, ← hprime Q]
    gcongr
  ·
    obtain ⟨P, hPmin, hPle⟩ := Set.exists_min_image J.minimalPrimes Ideal.height
      (Ideal.finite_minimalPrimes_of_isNoetherianRing B J) (Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes hJ))
    have : P.IsPrime := hPmin.1.1
    have hht : J.height = P.height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      exact le_antisymm (iInf₂_le P hPmin) (le_iInf₂ fun Q hQ => hPle Q hQ)
    rw [hht, ← hprime P]
    gcongr
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hPmin.1.2)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMLengthParameters
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

theorem mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq (hCM : CMRegularElement.Statement.{u})
    {B : Type u} [CommRing B] [IsCohenMacaulayLocalRing B] {P : Ideal B} (hmin : minimalPrimes B = {P})
    {s : B} (hs : s ∉ P) : s ∈ nonZeroDivisors B := by
  by_cases hsm : s ∈ maximalIdeal B
  · refine (hCM B s hsm fun p hp => ?_).1
    rw [hmin, Set.mem_singleton_iff] at hp
    rwa [hp]
  · exact ((IsLocalRing.notMem_maximalIdeal.1 hsm)).mem_nonZeroDivisors

theorem length_localization_maximalIdeal (B : Type u) [CommRing B] [IsLocalRing B] :
    Module.length (Localization.AtPrime (maximalIdeal B)) (Localization.AtPrime (maximalIdeal B)) =
      Module.length B B := by
  have hU : (maximalIdeal B).primeCompl ≤ IsUnit.submonoid B := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.1 hs
  let e := IsLocalization.atUnits B (maximalIdeal B).primeCompl
    (S := Localization.AtPrime (maximalIdeal B)) hU
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime (maximalIdeal B))) :=
    e.surjective
  rw [← Module.length_eq_of_surjective (S := B) hsurj]
  exact e.toLinearEquiv.length_eq.symm

theorem withBot_natCast_le_of_add_one_le {k : ℕ} {D : WithBot ℕ∞}
    (h : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ D + 1) : ((k : ℕ) : WithBot ℕ∞) ≤ D := by
  induction D using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe n =>
      have h' : k + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : k ≤ n)

theorem spanFinrank_span_range_le {R : Type*} [CommRing R] {k : ℕ} (z : Fin k → R) :
    (Ideal.span (Set.range z)).spanFinrank ≤ k := by
  classical
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
  have hz : Set.range z = ((Finset.univ.image z : Finset R) : Set R) := by simp
  rw [hz, Set.ncard_coe_finset]
  exact Finset.card_image_le.trans (by simp)

theorem span_range_eq_span_range_succ {R : Type*} [CommRing R] {k : ℕ} (z : Fin (k + 1) → R) (h0 : z 0 = 0) :
    Ideal.span (Set.range z) = Ideal.span (Set.range fun j : Fin k => z j.succ) := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => rw [h0]; exact Ideal.zero_mem _
    | succ j => exact Ideal.subset_span ⟨j, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩

theorem maximalIdeal_quotient_eq_span {B : Type u} [CommRing B] [IsLocalRing B] {I : Ideal B} {k : ℕ}
    (x : Fin k → B) (hI : Ideal.span (Set.range x) ⊔ I = maximalIdeal B) [IsLocalRing (B ⧸ I)] :
    maximalIdeal (B ⧸ I) = Ideal.span (Set.range fun i => Ideal.Quotient.mk I (x i)) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← hI, Ideal.map_sup,
    Ideal.map_span, ← Set.range_comp, Ideal.map_quotient_self, sup_bot_eq]
  rfl

theorem notMem_and_isPrime_sup_span {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {P : Ideal B} [hP : P.IsPrime] {k : ℕ} (x : Fin (k + 1) → B)
    (hdim : ringKrullDim (B ⧸ P) = ((k + 1 : ℕ) : WithBot ℕ∞))
    (hmax : Ideal.span (Set.range x) ⊔ P = maximalIdeal B) :
    x 0 ∉ P ∧ (P ⊔ Ideal.span {x 0}).IsPrime ∧
      ringKrullDim (B ⧸ (P ⊔ Ideal.span {x 0})) = ((k : ℕ) : WithBot ℕ∞) := by
  have hPm : P ≤ maximalIdeal B := hmax ▸ le_sup_right
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  have : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have : IsLocalRing (B ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hA := maximalIdeal_quotient_eq_span x hmax
  have hy : x 0 ∉ P := by
    intro hyP
    have h0 : Ideal.Quotient.mk P (x 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hyP
    have hle := ringKrullDim_le_spanFinrank_maximalIdeal (B ⧸ P)
    rw [hA, span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk P (x i)) h0, hdim] at hle
    have hk := spanFinrank_span_range_le (fun j : Fin k => Ideal.Quotient.mk P (x j.succ))
    have h2 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞) := hle.trans (by exact_mod_cast hk)
    have h3 : k + 1 ≤ k := by exact_mod_cast h2
    omega
  set Q₀ := P ⊔ Ideal.span {x 0} with hQ₀
  have hQ₀m : Q₀ ≤ maximalIdeal B := sup_le hPm ((Ideal.span_singleton_le_iff_mem _).2 (hxm 0))
  have hmaxQ : Ideal.span (Set.range x) ⊔ Q₀ = maximalIdeal B :=
    le_antisymm (sup_le (hmax ▸ le_sup_left) hQ₀m) (hmax ▸ sup_le_sup_left le_sup_left _)
  have : Nontrivial (B ⧸ Q₀) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hQ₀m))
  have : IsLocalRing (B ⧸ Q₀) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Q₀) Ideal.Quotient.mk_surjective
  have hA' := maximalIdeal_quotient_eq_span x hmaxQ
  have h0' : Ideal.Quotient.mk Q₀ (x 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk Q₀ (x i)) h0'] at hA'
  have hfin : (maximalIdeal (B ⧸ Q₀)).spanFinrank ≤ k := hA' ▸ spanFinrank_span_range_le _
  have hge : ((k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Q₀) := by
    have e : (B ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P (x 0)} ≃+* B ⧸ Q₀ :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup P (Ideal.span {x 0}))
    have hj : ({Ideal.Quotient.mk P (x 0)} : Set (B ⧸ P)) ⊆ Ring.jacobson (B ⧸ P) := by
      rw [Set.singleton_subset_iff, IsLocalRing.ringJacobson_eq_maximalIdeal, hA]
      exact Ideal.subset_span ⟨0, rfl⟩
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard _ hj
    rw [hdim, Set.encard_singleton, ringKrullDim_eq_of_ringEquiv e] at h
    exact withBot_natCast_le_of_add_one_le (by exact_mod_cast h)
  have hle : ringKrullDim (B ⧸ Q₀) ≤ ((k : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans (by exact_mod_cast hfin)
  have : IsRegularLocalRing (B ⧸ Q₀) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ((by exact_mod_cast hfin :
      ((maximalIdeal (B ⧸ Q₀)).spanFinrank : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞)).trans hge)
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := B ⧸ Q₀)
  exact ⟨hy, (Ideal.Quotient.isDomain_iff_prime Q₀).1 inferInstance, le_antisymm hle hge⟩

theorem CMLengthParameters.proof (hCM : CMRegularElement.Statement.{u})
    (hLen : LengthLocalizedQuotient.Statement.{u}) : CMLengthParameters.Statement.{u} := by
  suffices h : ∀ d : ℕ, ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime]
      (x : Fin d → B), minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
      Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
        Module.length B (B ⧸ Ideal.span (Set.range x)) =
          Module.length (Localization.AtPrime P) (Localization.AtPrime P) from
    fun B _ _ P _ d x => h d B P x
  intro d
  induction d with
  | zero =>
    intro B _ _ P _ x _ _ hmax
    have hx : Ideal.span (Set.range x) = ⊥ := by rw [Set.range_eq_empty, Ideal.span_empty]
    rw [hx, bot_sup_eq] at hmax
    subst hmax
    rw [hx, length_localization_maximalIdeal]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq
  | succ k ih =>
    intro B _ _ P _ x hmin hdim hmax
    obtain ⟨hyP, hQ₀, hdimQ⟩ := notMem_and_isPrime_sup_span x hdim hmax
    set y := x 0 with hy
    set Q₀ := P ⊔ Ideal.span {y} with hQ₀def
    have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
    have hnzd : ∀ s ∉ P, s ∈ nonZeroDivisors B := fun s hs =>
      mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq hCM hmin hs
    have hyQ : Ideal.span {y} ≤ Q₀ := le_sup_right

    have hB'CM : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y}) := (hCM B y (hxm 0) fun p hp => by
      rw [hmin, Set.mem_singleton_iff] at hp
      rwa [hp]).2
    set f := Ideal.Quotient.mk (Ideal.span {y}) with hf
    have hfs : Function.Surjective f := Ideal.Quotient.mk_surjective
    have hker : RingHom.ker f ≤ Q₀ := by rw [hf, Ideal.mk_ker]; exact hyQ
    set P' := Q₀.map f with hP'def
    have hP' : P'.IsPrime := Ideal.map_isPrime_of_surjective hfs hker
    have hcomap : P'.comap f = Q₀ := by
      rw [hP'def, Ideal.comap_map_of_surjective' f hfs, sup_eq_left.2 hker]

    have hall : ∀ q : Ideal (B ⧸ Ideal.span {y}), q.IsPrime → P' ≤ q := by
      intro q hq
      have hqc : (q.comap f).IsPrime := Ideal.comap_isPrime f q
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q.comap f)
      have hpP : p = P := by
        have : p ∈ minimalPrimes B := hp
        rw [hmin, Set.mem_singleton_iff] at this
        exact this
      subst hpP
      have hyq : Ideal.span {y} ≤ q.comap f := fun z hz => by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hz]
        exact q.zero_mem
      rw [hP'def, Ideal.map_le_iff_le_comap]
      exact sup_le hpq hyq
    have hmin' : minimalPrimes (B ⧸ Ideal.span {y}) = {P'} := by
      ext q
      rw [Set.mem_singleton_iff]
      constructor
      · intro hq
        exact le_antisymm (hq.2 ⟨hP', bot_le⟩ (hall q hq.1.1)) (hall q hq.1.1)
      · rintro rfl
        exact ⟨⟨hP', bot_le⟩, fun q hq _ => hall q hq.1⟩
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {y}) ⧸ P') = (k : ℕ) := by
      rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hyQ)]
      exact hdimQ

    set x' : Fin k → B ⧸ Ideal.span {y} := fun j => f (x j.succ) with hx'
    have hmB' : (maximalIdeal B).map f = maximalIdeal (B ⧸ Ideal.span {y}) :=
      map_maximalIdeal_of_surjective f hfs
    have hmax' : Ideal.span (Set.range x') ⊔ P' = maximalIdeal (B ⧸ Ideal.span {y}) := by
      apply le_antisymm
      · refine sup_le (Ideal.span_le.2 ?_) (IsLocalRing.le_maximalIdeal hP'.ne_top)
        rintro _ ⟨j, rfl⟩
        rw [← hmB']
        exact Ideal.mem_map_of_mem f (hxm _)
      · rw [← hmB', Ideal.map_le_iff_le_comap, ← hmax]
        refine sup_le (Ideal.span_le.2 ?_) fun p hp => ?_
        · rintro _ ⟨i, rfl⟩
          cases i using Fin.cases with
          | zero =>
            exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
          | succ j => exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
        · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_left hp))
    have key := ih (B ⧸ Ideal.span {y}) P' x' hmin' hdim' hmax'
    rw [hLen B P y hmin hnzd hyP P' hcomap] at key
    rw [← key]

    have hyx : Ideal.span {y} ≤ Ideal.span (Set.range x) :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span ⟨0, rfl⟩)
    have hJ : (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y})) = Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      refine span_range_eq_span_range_succ _ ?_
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    calc Module.length B (B ⧸ Ideal.span (Set.range x))
        = Module.length B ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          (DoubleQuot.quotQuotEquivQuotOfLEₐ B hyx).toLinearEquiv.length_eq.symm
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸ Ideal.span (Set.range x')) := by
          rw [hJ]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalisationModelLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem NormalisationModelLocalization.full : NormalisationModelLocalization.Statement :=
  NormalisationModelLocalization.proof

end GroundTheory.Heights₂.Heights
end

