module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ZeroLocusDimHGeo
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPiQuotCokerFiniteLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem PiQuotCokerFiniteLength.proof : PiQuotCokerFiniteLength.Statement := by
  intro B _ _ _ J hJ hQ
  have : Finite J.minimalPrimes := (J.finite_minimalPrimes_of_isNoetherianRing B).to_subtype
  let : Fintype J.minimalPrimes := Fintype.ofFinite _
  classical
  have hfac : ∀ (P : J.minimalPrimes) (x : B),
      quotToPiMinimalPrimes J (Submodule.Quotient.mk x) P = Ideal.Quotient.mk (P : Ideal B) x :=
    fun _ _ => rfl
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hxP : ∀ P : J.minimalPrimes, x ∈ (P : Ideal B) := fun P => by
      have h1 := congrFun hy P
      rwa [hfac, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
    have hx : x ∈ sInf J.minimalPrimes := Submodule.mem_sInf.mpr fun p hp => hxP ⟨p, hp⟩
    rw [Ideal.sInf_minimalPrimes, hJ.radical] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

  have hkey : ∀ Q : Ideal B, Q.IsPrime → ∀ P P' : J.minimalPrimes, P ≠ P' →
      (P : Ideal B) ≤ Q → (P' : Ideal B) ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp P P' hne hPQ hP'Q
    rcases hQ Q hQp (P.2.1.2.trans hPQ) with hmin | hm
    · exfalso
      apply hne
      have e1 : (P : Ideal B) = Q := le_antisymm hPQ (hmin.2 P.2.1 hPQ)
      have e2 : (P' : Ideal B) = Q := le_antisymm hP'Q (hmin.2 P'.2.1 hP'Q)
      exact Subtype.ext (e1.trans e2.symm)
    · exact hm
  let IP : J.minimalPrimes → Ideal B := fun P =>
    (Finset.univ.filter (· ≠ P)).inf fun P' : J.minimalPrimes => (P' : Ideal B)
  let I : Ideal B := Finset.univ.inf fun P => IP P ⊔ (P : Ideal B)
  have hI : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp hIQ
    obtain ⟨P, -, hPQ⟩ := hQp.inf_le'.mp hIQ
    obtain ⟨P', hP', hP'Q⟩ := hQp.inf_le'.mp (le_sup_left.trans hPQ)
    exact hkey Q hQp P P' (Finset.mem_filter.mp hP').2.symm (le_sup_right.trans hPQ) hP'Q
  have htors : Module.IsTorsionBySet B
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))
      (I : Set B) := by
    intro c z
    obtain ⟨y, hy⟩ := z
    show y • c = 0
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hyP : ∀ P, y ∈ IP P ⊔ (P : Ideal B) := fun P =>
      Submodule.mem_finsetInf.mp hy P (Finset.mem_univ _)
    choose a ha b hb hab using fun P => Submodule.mem_sup.mp (hyP P)
    choose x hx using fun P => Ideal.Quotient.mk_surjective (v P)
    refine ⟨Submodule.Quotient.mk (∑ P, a P * x P), ?_⟩
    funext Q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfac, Pi.smul_apply, ← hx Q, map_sum, Finset.sum_eq_single Q]
    · rw [← hab Q, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add (f := _), map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hb Q), add_zero]
    · intro P _ hPQ
      have hle : IP P ≤ (Q : Ideal B) :=
        Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hPQ.symm⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (hle (ha P)))
    · intro h
      exact absurd (Finset.mem_univ Q) h
  by_cases hItop : I = ⊤
  · haveI : Subsingleton
        (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
      ⟨fun c d => by
        have hc := @htors c ⟨1, by rw [hItop]; trivial⟩
        have hd := @htors d ⟨1, by rw [hItop]; trivial⟩
        rw [one_smul] at hc hd
        rw [hc, hd]⟩
    exact IsFiniteLength.of_subsingleton
  have hmax : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes :=
    ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hItop⟩, fun q hq _ => (hI q hq.1 hq.2).ge⟩
  have : IsArtinianRing (B ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmax
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  let := htors.module
  have : IsScalarTower B (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    htors.isScalarTower
  have : Module.Finite (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    Module.Finite.of_restrictScalars_finite B _ _
  have : IsArtinian (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    isArtinian_of_fg_of_artinian'
  exact isArtinian_of_surjective_algebraMap (R := B ⧸ I) Ideal.Quotient.mk_surjective

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegAdjoinLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Algebra Cardinal Set AlgebraicIndependent

noncomputable section

section TrdegRank

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem matroid_subalgebra_eq_comap (S : Subalgebra K Ω) :
    AlgebraicIndependent.matroid K S = (AlgebraicIndependent.matroid K Ω).comap ((↑) : S → Ω) := by
  refine Matroid.ext_indep (by simp) fun I _ => ?_
  have hinj : InjOn ((↑) : S → Ω) I := Subtype.val_injective.injOn
  rw [Matroid.comap_indep_iff, matroid_indep_iff, matroid_indep_iff]
  simp only [hinj, and_true]
  change AlgebraicIndependent K (fun i : I => (i : S)) ↔
    AlgebraicIndependent K (fun x : (((↑) : S → Ω) '' I) => (x : Ω))
  rw [← algebraicIndependent_image hinj]
  exact (S.val.algebraicIndependent_iff Subtype.val_injective).symm

theorem trdeg_adjoin_eq_cRk (A : Set Ω) :
    Algebra.trdeg K (Algebra.adjoin K A) = (AlgebraicIndependent.matroid K Ω).cRk A := by
  rw [← matroid_cRank_eq, matroid_subalgebra_eq_comap, ← Matroid.cRk_ground, Matroid.comap_ground_eq,
    Matroid.cRk_comap, matroid_e, preimage_univ, image_univ, Subtype.range_coe]
  refine le_antisymm ?_ (Matroid.cRk_le_of_subset _ Algebra.subset_adjoin)
  refine (Matroid.cRk_le_of_subset _ ?_).trans_eq (Matroid.cRk_closure _ A)
  intro x hx
  rw [matroid_closure_eq]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin K A)

end TrdegRank

theorem TrdegAdjoinLe.proof : TrdegAdjoinLe.Statement := by
  intro K Ω _ _ _ s ι _ t ι' w hw
  set M := AlgebraicIndependent.matroid K Ω
  rw [trdeg_adjoin_eq_cRk, trdeg_adjoin_eq_cRk]
  have hcl : range w ⊆ M.closure (s ∪ range t) := by
    rintro _ ⟨i, rfl⟩
    rw [matroid_closure_eq]
    exact hw i
  calc M.cRk (range w) ≤ M.cRk (M.closure (s ∪ range t)) := M.cRk_le_of_subset hcl
    _ = M.cRk (s ∪ range t) := M.cRk_closure _
    _ ≤ M.cRk (s ∩ range t) + M.cRk (s ∪ range t) := le_add_self
    _ ≤ M.cRk s + M.cRk (range t) := M.cRk_inter_add_cRk_union_le s (range t)
    _ ≤ M.cRk s + #(range t) := by gcongr; exact M.cRk_le_cardinalMk _
    _ ≤ M.cRk s + #ι := by gcongr; exact mk_range_le
    _ = M.cRk s + Fintype.card ι := by rw [mk_fintype]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegBaseAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Cardinal

theorem TrdegBaseAlgebraic.proof : TrdegBaseAlgebraic.Statement := by
  intro F K Ω _ _ _ _ _ _ _ hKF ι z
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F Ω, A = Algebra.adjoin F (Set.range z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subalgebra K Ω, B = Algebra.adjoin K (Set.range z) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hAB : ∀ w ∈ A, w ∈ B := by
    intro w hw
    rw [hA] at hw
    rw [hB]
    induction hw using Algebra.adjoin_induction with
    | mem w hw => exact Algebra.subset_adjoin hw
    | algebraMap c =>
      rw [IsScalarTower.algebraMap_apply F K Ω c]
      exact Subalgebra.algebraMap_mem _ _
    | add u v _ _ hu hv => exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv => exact Subalgebra.mul_mem _ hu hv

  let i : A →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis F A
  let x : t → B := fun a => i a
  set C : Subalgebra K B := Algebra.adjoin K (Set.range x) with hC

  have hFC : ∀ r ∈ Algebra.adjoin F (Set.range ((↑) : t → A)), i r ∈ C := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
      obtain ⟨a, rfl⟩ := hr
      exact Algebra.subset_adjoin ⟨a, rfl⟩
    | algebraMap c =>
      have : i (algebraMap F A c) = algebraMap K B (algebraMap F K c) := by
        apply Subtype.ext
        exact (IsScalarTower.algebraMap_apply F K Ω c)
      rw [this]
      exact C.algebraMap_mem _
    | add r s _ _ hr hs =>
      rw [map_add (f := _)]
      exact C.add_mem hr hs
    | mul r s _ _ hr hs =>
      rw [map_mul]
      exact C.mul_mem hr hs
  let f : Algebra.adjoin F (Set.range ((↑) : t → A)) →+* C :=
    { toFun := fun r => ⟨i r, hFC r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => ((c : B) : Ω)) hab
  have key : ∀ (w : Ω), w ∈ Algebra.adjoin K (Set.range z) →
      ∀ (hw : w ∈ B), IsAlgebraic C (⟨w, hw⟩ : B) := by
    intro w hw'
    induction hw' using Algebra.adjoin_induction with
    | mem w hw' =>
      intro hw
      obtain ⟨m, rfl⟩ := hw'
      have hzA : z m ∈ A := hA ▸ Algebra.subset_adjoin ⟨m, rfl⟩
      have h1 : IsAlgebraic (Algebra.adjoin F (Set.range ((↑) : t → A))) (⟨z m, hzA⟩ : A) :=
        ht.isAlgebraic.isAlgebraic _
      exact h1.ringHom_of_comp_eq f i hf (RingHom.ext fun _ => rfl)
    | algebraMap k =>
      intro hw
      exact (hKF.isAlgebraic k).ringHom_of_comp_eq ((algebraMap K C).comp (algebraMap F K))
        (algebraMap K B) (RingHom.injective _) (RingHom.ext fun _ => rfl)
    | add u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).add (hv (hB ▸ hv'))
    | mul u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).mul (hv (hB ▸ hv'))
  have alg : Algebra.IsAlgebraic C B := ⟨fun b => key b.1 (hB ▸ b.2) b.2⟩
  calc Algebra.trdeg K B ≤ #(Set.range x) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range x)
    _ ≤ #t := Cardinal.mk_range_le
    _ = Algebra.trdeg F A := ht.cardinalMk_eq_trdeg

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PZeroLocusDimH
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ZeroLocusDimH

theorem eval_eval₂_aeval {n s : ℕ} (π : Fin s → MvPolynomial (Fin n) ℂ)
    (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (x : Fin n → ℂ) (i : Fin n) :
    MvPolynomial.eval x (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
      Polynomial.eval (x i) (Q.map (MvPolynomial.eval (paramMap π x))) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval_map, MvPolynomial.eval_X]
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · simp
  · simp [paramMap]

theorem mem_zeroSet_iff {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    (∀ q ∈ I, MvPolynomial.eval x q = 0) ↔ I ≤ RingHom.ker (MvPolynomial.eval x) :=
  ⟨fun h q hq => RingHom.mem_ker.2 (h q hq), fun h _ hq => RingHom.mem_ker.1 (h hq)⟩

theorem ringKrullDim_quot_sup_add_one_le {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    (g : MvPolynomial (Fin n) ℂ) (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h

theorem le_of_add_one_le_succ {a : WithBot ℕ∞} {k : ℕ} (h : a + 1 ≤ ((k + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (k : WithBot ℕ∞) :=
  _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ h

theorem dimH_le_of_step {n : ℕ} (d : ℕ)
    (hIH : ∀ J' : Ideal (MvPolynomial (Fin n) ℂ), ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal))
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d) :
    dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by

  have hcover : {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ⊆
      ⋃ p ∈ J.minimalPrimes, {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} := by
    intro x hx
    rw [Set.mem_ofPred_eq, mem_zeroSet_iff] at hx
    have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le hx
    exact Set.mem_biUnion hp ((mem_zeroSet_iff p x).2 hpx)
  refine (dimH_mono hcover).trans ?_
  rw [dimH_bUnion (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).countable]
  refine iSup₂_le fun p hp => ?_
  have : p.IsPrime := hp.1.1
  have hpd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤ d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hp.1.2)).trans hJ
  obtain ⟨s, hs, π, P, hP, hP'⟩ := exists_simple_root_data p
  set g := ∏ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) with hgdef
  have hg : g ∉ p := by
    rw [hgdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, -, hi⟩
    exact hP' i hi
  have hsplit : {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ⊆
      {x | x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ∧ ∀ i, Polynomial.eval (x i)
        ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0} ∪
      {x : Fin n → ℂ | ∀ q ∈ p ⊔ Ideal.span {g}, MvPolynomial.eval x q = 0} := by
    intro x hx
    by_cases h : ∀ i, Polynomial.eval (x i)
        ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0
    · exact Or.inl ⟨hx, h⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Set.mem_ofPred_eq, mem_zeroSet_iff, sup_le_iff, Ideal.span_singleton_le_iff_mem,
        RingHom.mem_ker]
      refine ⟨(mem_zeroSet_iff p x).1 hx, ?_⟩
      rw [hgdef, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eval_eval₂_aeval]; exact hi)
  refine (dimH_mono hsplit).trans ?_
  rw [dimH_union]
  refine max_le ?_ ?_
  · have hV : ∀ x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0}, ∀ i,
        Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0 := by
      intro x hx i
      rw [← eval_eval₂_aeval]
      exact hx _ (hP i)
    refine (dimH_simple_roots_le π P _ hV).trans ?_
    have hsd : s ≤ d := by exact_mod_cast hs.trans hpd
    have : (s : ENNReal) ≤ d := by exact_mod_cast hsd
    gcongr
  · exact hIH _ ((ringKrullDim_quot_sup_add_one_le p g hg).trans hpd)

theorem dimH_zeroLocus_le (d : ℕ) : ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by
  induction d with
  | zero =>
    intro n J hJ
    refine dimH_le_of_step 0 (fun J' hJ' => ?_) J hJ
    by_cases htop : J' = ⊤
    · have : {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
        exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
      rw [this, dimH_empty]
      simp
    · have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J') := Ideal.Quotient.nontrivial_iff.2 htop
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J')
      have h1 : (0 : WithBot ℕ∞) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 := by gcongr
      have h2 := h1.trans hJ'
      rw [zero_add, Nat.cast_zero] at h2
      exact absurd h2 (not_le.2 zero_lt_one)
  | succ k ih =>
    intro n J hJ
    refine dimH_le_of_step (k + 1) (fun J' hJ' => ?_) J hJ
    refine (ih n J' (le_of_add_one_le_succ hJ')).trans ?_
    have : (k : ENNReal) ≤ ((k + 1 : ℕ) : ENNReal) := by exact_mod_cast Nat.le_succ k
    gcongr

theorem proof : Statement := fun n d J hJ => dimH_zeroLocus_le d n J hJ

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Swap

variable {F : Type*} [Field F] {n k : ℕ}

theorem comp_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)} {u : Fin k × Fin n → AlgebraicClosure F}
    (hu : u ∈ incidence I k) (τ : Equiv.Perm (Fin k)) : u ∘ Prod.map τ id ∈ incidence I k := by
  obtain ⟨x, hx, hI, hlin⟩ := hu
  exact ⟨x, hx, hI, fun i => by simpa using hlin (τ i)⟩

theorem IsChowForm.dvd_rename {I : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) : f ∣ rename (Prod.map τ id) f := by
  refine (hf.2 _).mp fun u hu => ?_
  rw [aeval_rename]
  exact (hf.2 f).mpr dvd_rfl _ (comp_mem_incidence hu τ)

theorem rename_prodMap_mul (σ τ : Equiv.Perm (Fin k)) (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map (σ * τ) id) p = rename (Prod.map σ id) (rename (Prod.map τ id) p) := by
  rw [rename_rename]
  rfl

theorem rename_prodMap_one (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map ⇑(1 : Equiv.Perm (Fin k)) id) p = p := by
  have : Prod.map ⇑(1 : Equiv.Perm (Fin k)) (id : Fin n → Fin n) = id := by
    funext ij
    rfl
  rw [this]
  exact rename_id_apply p

theorem IsChowForm.rename_eq_C_mul {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) :
    ∃ c : F, rename (Prod.map τ id) f = C c * f := by
  obtain ⟨a, ha⟩ := hf.dvd_rename τ
  obtain ⟨b, hb⟩ := hf.dvd_rename (τ⁻¹ : Equiv.Perm (Fin k))
  have hback : rename (Prod.map τ id) (rename (Prod.map ⇑(τ⁻¹ : Equiv.Perm (Fin k)) id) f) = f := by
    rw [← rename_prodMap_mul, mul_inv_cancel, rename_prodMap_one]
  have hab : a * rename (Prod.map τ id) b = 1 := by
    have h1 : f * (a * rename (Prod.map τ id) b) = f * 1 := by
      rw [mul_one, ← mul_assoc, ← ha]
      conv_rhs => rw [← hback, hb]
      rw [map_mul]
    exact mul_left_cancel₀ hf.1 h1
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (IsUnit.of_mul_eq_one _ hab)
  exact ⟨c, by rw [ha, mul_comm]⟩

theorem IsChowForm.rename_swap {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (x y : Fin k) :
    ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map (Equiv.swap x y) id) f = C c * f := by
  obtain ⟨c, hc⟩ := hf.rename_eq_C_mul (Equiv.swap x y)
  refine ⟨c, ?_, hc⟩
  have h2 : rename (Prod.map (Equiv.swap x y * Equiv.swap x y) id) f = C (c ^ 2) * f := by
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hc, ← mul_assoc, ← C_mul, sq]
  rw [Equiv.swap_mul_self, rename_prodMap_one] at h2
  have h3 : (C (c ^ 2) - 1) * f = 0 := by
    rw [sub_mul, ← h2, one_mul, sub_self]
  have h4 : C (c ^ 2) - 1 = (0 : MvPolynomial (Fin k × Fin n) F) :=
    (mul_eq_zero.mp h3).resolve_right hf.1
  rw [sub_eq_zero, ← C_1] at h4
  exact C_injective _ _ h4

theorem chowFormSwap : ChowFormSwap.Statement := by
  intro F _ n k I f hf τ
  induction τ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_pow 2, by rw [C_1, one_mul, rename_prodMap_one]⟩
  | swap_mul σ x y _ ih =>
    obtain ⟨c, hc2, hc⟩ := ih
    obtain ⟨d, hd2, hd⟩ := hf.rename_swap x y
    refine ⟨d * c, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hd, C_mul]
    ring

end Swap

end

end GroundTheory.Heights₂.Heights
end

