module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem zeroSetIn_isAnalyticNear {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨Set.univ, s.card, fun i z => eval z (s.equivFin.symm i : MvPolynomial σ ℂ), isOpen_univ, trivial,
    fun i => AnalyticOnNhd.eval_mvPolynomial _, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq, true_and]
  constructor
  · intro hz i
    apply hz
    rw [← hs]
    exact Submodule.subset_span (s.equivFin.symm i).2
  · intro hz q hq
    have hle : Ideal.span (s : Set (MvPolynomial σ ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
      rw [Ideal.span_le]
      intro p hp
      rw [SetLike.mem_coe, RingHom.mem_ker]
      simpa using hz (s.equivFin ⟨p, hp⟩)
    rw [← hs] at hq
    exact hle hq

theorem NormalComplementConnected.proof (hvan : VanishNearPoint.Statement)
    (hgerm : NormalGermIrreducible.Statement) (hconn : IrreducibleGermComplementConnected.Statement) :
    NormalComplementConnected.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  have hne : ¬ ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z h = 0 := by
    intro hev
    have hcl := zeroSetIn_subset_closure_diff hvan I h hI hh hw
    rw [mem_closure_iff_nhds] at hcl
    obtain ⟨z, hzt, hzZ, hzh⟩ := hcl _ hev
    exact hzh (hzt hzZ)
  exact hconn σ (zeroSetIn I) w (fun z => eval z h) (zeroSetIn_isAnalyticNear I w)
    (hgerm σ I w hI hnorm hw) (AnalyticOnNhd.eval_mvPolynomial h w trivial) hne U hU

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDivisorChartGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalDivisorChartGeneric

theorem ringKrullDim_le_of_injective_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hint : f.IsIntegral) : ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  refine iSup_le fun l => ?_
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    intro r hr
    have : f r = 0 := hr
    rw [show r = 0 from hinj (by rw [this, map_zero])]
    exact Ideal.zero_mem _
  obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
  have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hlen])

theorem isIntegral_mk_comp_rename {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) {B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)} (hB : M.ideal ≤ B) :
    ((Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom).IsIntegral := by
  set f := (Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom with hf
  let : Algebra (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) := f.toAlgebra
  have hX : ∀ s, IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B (X s)) := by
    rintro (i | i)
    · have h : Ideal.Quotient.mk B (X (Sum.inl i)) =
          algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (X i) := by
        show _ = f (X i)
        simp [hf]
      rw [h]
      exact isIntegral_algebraMap
    · obtain ⟨P, hPm, hP⟩ := M.integral i
      refine ⟨P, hPm, ?_⟩
      have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hB hP)
      rw [Polynomial.hom_eval₂] at h
      exact h
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  show IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B p)
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk B (C a) =
        algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (C a) := by
      show _ = f (C a)
      simp [hf]
    rw [h]
    exact isIntegral_algebraMap
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hp.add hq
  | mul_X p s hp =>
    rw [map_mul]
    exact hp.mul (hX s)

theorem proof (hUp : NormalModelDivisorChartGeneric.Statement) : NormalDivisorChartGeneric.Statement := by
  intro n d J u M hJ hdim hu
  obtain ⟨B, hleB, hdimB, hB⟩ := hUp n d J u M hJ hdim hu
  refine ⟨B.comap (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom, ?_, ?_, ?_⟩
  · refine sup_le ?_ ((Ideal.span_le).2 (Set.singleton_subset_iff.2 ?_))
    · exact M.comap_eq.symm.le.trans (Ideal.comap_mono (le_sup_left.trans hleB))
    · exact hleB (Ideal.mem_sup_right (Ideal.subset_span rfl))
  · refine lt_of_le_of_lt ?_ hdimB
    exact ringKrullDim_le_of_injective_isIntegral _ Ideal.quotientMap_injective
      ((isIntegral_quotientMap_iff _).2 (isIntegral_mk_comp_rename M (le_sup_left.trans hleB)))
  · intro q _ hqu hqI w hw hwq
    refine hB w hw (hwq ▸ hqu) fun hwB => hqI fun f hf => ?_
    have h := hwB _ hf
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename] at h
    rw [← hwq]
    exact h

end NormalDivisorChartGeneric

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDoublePointsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

namespace NormalDoublePointsGeneric

theorem ringKrullDim_quotient_le_of_primes {R : Type*} [CommRing R] (I : Ideal R) (k : WithBot ℕ∞)
    (h : ∀ W : Ideal R, W.IsPrime → I ≤ W → ∃ K : Ideal R, K ≤ W ∧ ringKrullDim (R ⧸ K) ≤ k) :
    ringKrullDim (R ⧸ I) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨K, hKW, hK⟩ := h l.head.1.asIdeal l.head.1.isPrime l.head.2
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) K) :=
    ⟨l.length, fun i => ⟨(l i).1, show (K : Set R) ⊆ (l i).1.asIdeal from hKW.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) K) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ K) := (ringKrullDim_quotient K).symm
    _ ≤ k := hK

theorem ringKrullDim_quotient_anti {R : Type*} [CommRing R] {K K' : Ideal R} (h : K ≤ K') :
    ringKrullDim (R ⧸ K') ≤ ringKrullDim (R ⧸ K) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

theorem ringKrullDim_quot_sup_span_add_one_le {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h

def belowNat : ℕ → WithBot ℕ∞
  | 0 => ⊥
  | e + 1 => (e : WithBot ℕ∞)

theorem belowNat_lt (d : ℕ) : belowNat d < (d : WithBot ℕ∞) := by
  cases d with
  | zero => exact WithBot.bot_lt_coe _
  | succ e =>
    show ((e : ℕ) : WithBot ℕ∞) < ((e + 1 : ℕ) : WithBot ℕ∞)
    exact_mod_cast Nat.lt_succ_self e

theorem le_belowNat_of_add_two_le {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) : x ≤ belowNat d := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_add, top_add] at h
        exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k =>
      have h2 : k + 1 + 1 ≤ d + 1 := by exact_mod_cast h
      cases d with
      | zero => omega
      | succ e => show ((k : ℕ∞) : WithBot ℕ∞) ≤ ((e : ℕ) : WithBot ℕ∞); exact_mod_cast (by omega : k ≤ e)

theorem proof : NormalDoublePointsGeneric.Statement := by
  intro n d J u M hJ hdim hu
  classical
  choose a b hbJ hab using M.birational
  set bb : MvPolynomial (Fin n) ℂ := ∏ i, b i with hbb
  have hbbJ : bb ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  set K : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {bb} with hK
  have hfin : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  set S : Finset (Ideal (MvPolynomial (Fin n) ℂ)) := hfin.toFinset.filter (fun P => linForm u ∉ P) with hS
  have memS : ∀ P, P ∈ S ↔ P ∈ K.minimalPrimes ∧ linForm u ∉ P := fun P => by
    simp [hS]
  refine ⟨S.inf (fun P => P ⊔ Ideal.span {linForm u}), ?_, ?_, ?_⟩
  · refine Finset.le_inf fun P hP => sup_le_sup_right ?_ _
    exact le_sup_left.trans ((memS P).1 hP).1.1.2
  · have := hJ
    have hdimK : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
      hdim ▸ ringKrullDim_quot_sup_span_add_one_le J hbbJ
    refine lt_of_le_of_lt (ringKrullDim_quotient_le_of_primes _ (belowNat d) fun W hW hIW => ?_) (belowNat_lt d)
    obtain ⟨P, hPS, hPW⟩ := (hW.inf_le').1 hIW
    refine ⟨_, hPW, le_belowNat_of_add_two_le ?_⟩
    obtain ⟨hPm, huP⟩ := (memS P).1 hPS
    have := hPm.1.1
    have h1 := ringKrullDim_quot_sup_span_add_one_le P huP
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) :=
      ringKrullDim_quotient_anti hPm.1.2
    calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (P ⊔ Ideal.span {linForm u})) + 1 + 1
        ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 := by gcongr; exact h1.trans h2
      _ ≤ _ := hdimK
  · intro q _ hqu hqI
    have evu : ∀ x, eval x (linForm u) = linEval u x := fun x => by simp [linForm, linEval]
    have hqP : ∀ P ∈ S, q ∉ zeroSet P := by
      intro P hP hqP
      apply hqI
      intro f hf
      have hf' : f ∈ P ⊔ Ideal.span {linForm u} := (Finset.inf_le (f := fun P => P ⊔ Ideal.span {linForm u}) hP) hf
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.1 hf'
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      simp [hqP p hp, evu, hqu]
    have hclosed : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet P) := fun P => by
      have : zeroSet P = ⋂ f ∈ P, {x : Fin n → ℂ | eval x f = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
    refine ⟨⋂ P ∈ S, (zeroSet P)ᶜ, (Filter.biInter_finset_mem S).2 fun P hP =>
      (hclosed P).isOpen_compl.mem_nhds (hqP P hP), ?_⟩
    intro w hw w' hw' hww hxN hne
    set x := IndefiniteRowSideFullHecke.ComplexSets.firstCoords w with hx
    have hwx : (w ∘ Sum.inl) = x := rfl
    have hw'x : (w' ∘ Sum.inl) = x := by rw [hww]; rfl
    have hxJ : ∀ f ∈ J, eval x f = 0 := fun f hf => by
      have hf' : rename Sum.inl f ∈ M.ideal := by
        rw [← M.comap_eq] at hf; exact hf
      have := hw _ hf'
      rwa [eval_rename, hwx] at this
    have hbx : eval x bb = 0 := by
      by_contra hb
      apply hne
      funext s
      rcases s with i | i
      · exact congrFun hww i
      · have hbi : eval x (b i) ≠ 0 := fun h0 => hb (by
          rw [hbb, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h0)
        have e1 := hw _ (hab i)
        have e2 := hw' _ (hab i)
        simp only [map_sub, map_mul, eval_rename, eval_X, hwx, hw'x] at e1 e2
        exact mul_left_cancel₀ hbi (by linear_combination e1 - e2)
    have hKx : K ≤ RingHom.ker (eval x) := sup_le (fun f hf => RingHom.mem_ker.2 (hxJ f hf))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.2 hbx)))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPm, hPx⟩ := Ideal.exists_minimalPrimes_le hKx
    by_cases huP : linForm u ∈ P
    · rw [← evu]; exact RingHom.mem_ker.1 (hPx huP)
    · exfalso
      have hPS : P ∈ S := (memS P).2 ⟨hPm, huP⟩
      have hxP : x ∈ zeroSet P := fun f hf => RingHom.mem_ker.1 (hPx hf)
      exact (Set.mem_iInter₂.1 hxN P hPS) hxP

end NormalDoublePointsGeneric

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalGermIrreducible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem eq_zero_of_mem_closure_of_continuousAt {σ : Type} [Fintype σ] {k : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} {u : σ → ℂ} (hk : ContinuousAt k u) (hu : u ∈ closure S)
    (h0 : ∀ y ∈ S, k y = 0) : k u = 0 := by
  have h1 := hk.continuousWithinAt.mem_closure_image hu
  have h2 : k '' S ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    exact h0 y hy
  have h3 := closure_mono h2 h1
  rwa [closure_singleton, Set.mem_singleton_iff] at h3

theorem NormalGermIrreducible.proof (hreg : RegularLocusIdentity.Statement)
    (hext : NormalRiemannExtensionLocal.Statement) (hvan : VanishNearPoint.Statement) :
    NormalGermIrreducible.Statement := by
  classical
  intro σ _ I w hI hnorm hw
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  set X := zeroSetIn I with hX
  obtain ⟨h, hhI, hid⟩ := hreg σ I hI

  set U : Set (σ → ℂ) := {z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z} ∩
    {z | ∀ᶠ y in 𝓝 z, y ∈ X → f y * g y = 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g) |>.inter isOpen_setOfPred_eventually_nhds
  have hwU : w ∈ U := ⟨⟨hf, hg⟩, hfg⟩

  set E : (σ → ℂ) → Prop := fun z => ∀ᶠ y in 𝓝 z, y ∈ X → f y = 0 with hE

  have key : ∀ z ∈ X ∩ U, eval z h ≠ 0 → ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ((∀ u ∈ X ∩ V, E u) ∨ (∀ u ∈ X ∩ V, ¬ E u ∧ g u = 0)) := by
    rintro z ⟨hzX, hzU⟩ hhz
    obtain ⟨V, hVo, hzV, hVU, hVid⟩ := hid z hzX hhz U (hUo.mem_nhds hzU)
    refine ⟨V, hVo, hzV, hVU, ?_⟩
    have hfV : AnalyticOnNhd ℂ f V := fun y hy => (hVU hy).1.1
    have hgV : AnalyticOnNhd ℂ g V := fun y hy => (hVU hy).1.2
    by_cases hA : ∃ y ∈ X ∩ V, E y
    · left
      have hf0 := hVid f hfV hA
      intro u hu
      filter_upwards [hVo.mem_nhds hu.2] with y hyV hyX using hf0 y ⟨hyX, hyV⟩
    · right
      push Not at hA
      have hnz : ¬ E z := hA z ⟨hzX, hzV⟩
      have hfr : ∃ᶠ y in 𝓝 z, y ∈ X ∧ f y ≠ 0 := by
        rw [Filter.not_eventually] at hnz
        refine hnz.mono fun y hy => ?_
        by_contra hc
        exact hy fun hyX => by_contra fun hne => hc ⟨hyX, hne⟩
      obtain ⟨y, ⟨hyX, hfy⟩, hyV⟩ := (hfr.and_eventually (hVo.mem_nhds hzV)).exists
      have hg0 : ∀ᶠ u in 𝓝 y, u ∈ X → g u = 0 := by
        filter_upwards [(hVU hyV).2, (hfV y hyV).continuousAt.eventually_ne hfy] with u hu hfu huX
        exact (mul_eq_zero.1 (hu huX)).resolve_left hfu
      have hg0V := hVid g hgV ⟨y, ⟨hyX, hyV⟩, hg0⟩
      exact fun u hu => ⟨hA u hu, hg0V u hu⟩

  set φ : (σ → ℂ) → ℂ := fun z => if E z then 0 else 1 with hφ
  set S := (X ∩ U) \ {z | eval z h = 0} with hS
  have hφhol : HolomorphicOnSubset φ S := by
    rintro z ⟨hzXU, hhz⟩
    obtain ⟨V, hVo, hzV, -, hcase⟩ := key z hzXU hhz
    refine ⟨V, hVo, hzV, ?_⟩
    rcases hcase with h0 | h1
    · refine ⟨fun _ => 0, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_pos (h0 u ⟨hu.1.1.1, hu.2⟩)]
    · refine ⟨fun _ => 1, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_neg (h1 u ⟨hu.1.1.1, hu.2⟩).1]
  have hφb : Bornology.IsBounded (φ '' S) := by
    refine ((Set.finite_singleton (1 : ℂ)).insert 0).isBounded.subset ?_
    rintro _ ⟨z, -, rfl⟩
    by_cases hz : E z
    · simp [hφ, hz]
    · simp [hφ, hz]
  obtain ⟨V, hVo, hwV, hVU, F, hFd, hFeq⟩ :=
    hext σ I h w U φ hI hnorm hhI hw (hUo.mem_nhds hwU) hφhol hφb

  set N := V ∩ F ⁻¹' Metric.ball (F w) (1 / 2) with hN
  have hNo : IsOpen N := hFd.continuousOn.isOpen_inter_preimage hVo Metric.isOpen_ball
  have hwN : w ∈ N := ⟨hwV, Set.mem_preimage.mpr (Metric.mem_ball_self (by norm_num))⟩
  have hdense := zeroSetIn_subset_closure_diff hvan I h hI hhI

  have spread : ∀ k : (σ → ℂ) → ℂ, (∀ y ∈ U, ContinuousAt k y) →
      (∀ y ∈ X ∩ N, eval y h ≠ 0 → k y = 0) → ∀ᶠ u in 𝓝 w, u ∈ X → k u = 0 := by
    intro k hk h0
    filter_upwards [hNo.mem_nhds hwN] with u huN huX
    have hcl : u ∈ closure (N ∩ (X \ {z | eval z h = 0})) := hNo.inter_closure ⟨huN, hdense huX⟩
    exact eq_zero_of_mem_closure_of_continuousAt (hk u (hVU huN.1)) hcl
      fun y hy => h0 y ⟨hy.2.1, hy.1⟩ hy.2.2
  have hφN : ∀ y ∈ X ∩ N, eval y h ≠ 0 → ‖φ y - F w‖ < 1 / 2 := by
    rintro y ⟨hyX, hyV, hyF⟩ hhy
    rw [← hFeq ⟨⟨hyX, hyV⟩, hhy⟩]
    simpa [dist_eq_norm] using hyF
  by_cases hc : ‖F w‖ < 1 / 2
  · left
    refine spread f (fun y hy => hy.1.1.continuousAt) fun y hy hhy => ?_
    have hEy : E y := by
      by_contra hnE
      have h1 := hφN y hy hhy
      simp only [hφ, if_neg hnE] at h1
      have : ‖(1 : ℂ)‖ < 1 := by
        calc ‖(1 : ℂ)‖ = ‖(1 - F w) + F w‖ := by ring_nf
          _ ≤ ‖1 - F w‖ + ‖F w‖ := norm_add_le _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add h1 hc
          _ = 1 := by norm_num
      simp at this
    exact hEy.self_of_nhds hy.1
  · right
    refine spread g (fun y hy => hy.1.2.continuousAt) fun y hy hhy => ?_
    have hnE : ¬ E y := by
      intro hEy
      have h1 := hφN y hy hhy
      simp only [hφ, if_pos hEy, zero_sub, norm_neg] at h1
      exact hc h1
    obtain ⟨V', -, hyV', -, hcase⟩ := key y ⟨hy.1, hVU hy.2.1⟩ hhy
    rcases hcase with h0 | h1
    · exact absurd (h0 y ⟨hy.1, hyV'⟩) hnE
    · exact (h1 y ⟨hy.1, hyV'⟩).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

theorem PosPartSplit.proof : PosPartSplit.Statement := by
  classical
  intro n d J A f φ E y hA hE hcov
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]

  set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x =>
    if h : ∃ s, IsSheetAt J A x s then
      max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT
  have hT0 : ∀ g x, 0 ≤ T g x := fun g x => by
    simp only [hT]; split_ifs <;> simp
  have hpt : ∀ x ∈ hfin.toFinset,
      ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x) := by
    intro x hx
    have hx' : x ∈ fibre J A y := hfin.mem_toFinset.mp hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    · obtain ⟨k₀, hk₀⟩ := hcov x hx' hs
      rw [tsum_eq_single k₀]
      · simp only [hT, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : x ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [hT, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [hT, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm

end

end GroundTheory.Heights₂.Heights
end

