module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ChineseRemainderFiniteCover
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem exists_of_li {Q ι : Type} [AddCommGroup Q] [Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ)
    (h : LinearIndependent ℂ f) (v : ι → ℂ) : ∃ q, ∀ i, f i q = v i :=
  _root_.UpperTheory.Reformulated.B.Qe54.exists_of_li f h v

private theorem chineseRemainder_finiteCover {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (hc : IsFinCover ℂ K x) :
    Finite (fib ℂ K x) ∧ ∀ v : fib ℂ K x → ℂ, ∃ h : rB ℂ K x {0}, ∀ e, e.1 h = v e := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    let I : Ideal (rB ℂ K x {0}) :=
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0}))
    let mk : rB ℂ K x {0} →ₐ[ℂ] (rB ℂ K x {0} ⧸ I) := Ideal.Quotient.mkₐ ℂ I
    have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F K d x hc {0} (Finset.singleton_nonempty 0)).1
    have hmem : ∀ y (hy : y ∈ rA ℂ x {0}), algebraMap F K y ∈ rB ℂ K x {0} := fun y hy =>
      (integralClosure (rA ℂ x {0}) K).algebraMap_mem ⟨y, hy⟩
    have hA : ∀ y (hy : y ∈ rA ℂ x {0}), ∃ c : ℂ,
        mk ⟨algebraMap F K y, hmem y hy⟩ = algebraMap ℂ _ c := by
      intro y hy
      refine Algebra.adjoin_induction (p := fun y hy => ∃ c : ℂ,
        mk ⟨algebraMap F K y, hmem y hy⟩ = algebraMap ℂ _ c) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, hi, j, rfl⟩
        obtain rfl : i = 0 := Finset.mem_singleton.1 hi
        induction j using Fin.cases with
        | zero =>
          refine ⟨1, ?_⟩
          rw [map_one, ← map_one mk]
          congr 1
          ext
          simp [div_self (hc.pd.ne 0)]
        | succ j =>
          refine ⟨0, ?_⟩
          rw [map_zero]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
      · intro r
        refine ⟨r, ?_⟩
        rw [← mk.commutes r]
        congr 1
        ext
        simp [← IsScalarTower.algebraMap_apply]
      · rintro a b ha hb ⟨c, hc1⟩ ⟨c', hc2⟩
        refine ⟨c + c', ?_⟩
        have e : (⟨algebraMap F K (a + b), hmem _ (add_mem ha hb)⟩ : rB ℂ K x {0}) =
            ⟨_, hmem a ha⟩ + ⟨_, hmem b hb⟩ := Subtype.ext (map_add _ _ _)
        exact (congrArg mk e).trans (by rw [map_add mk, hc1, hc2, map_add (algebraMap ℂ _)])
      · rintro a b ha hb ⟨c, hc1⟩ ⟨c', hc2⟩
        refine ⟨c * c', ?_⟩
        have e : (⟨algebraMap F K (a * b), hmem _ (mul_mem ha hb)⟩ : rB ℂ K x {0}) =
            ⟨_, hmem a ha⟩ * ⟨_, hmem b hb⟩ := Subtype.ext (map_mul _ _ _)
        exact (congrArg mk e).trans (by rw [map_mul, hc1, hc2, map_mul])
    have hQ : Module.Finite ℂ (rB ℂ K x {0} ⧸ I) := by
      obtain ⟨s, hs⟩ := hfin.fg_top
      let g : integralClosure (rA ℂ x {0}) K → (rB ℂ K x {0} ⧸ I) := fun y => mk ⟨y.1, y.2⟩
      have key : ∀ y, y ∈ Submodule.span (rA ℂ x {0}) (s : Set (integralClosure (rA ℂ x {0}) K)) →
          g y ∈ Submodule.span ℂ (g '' (s : Set (integralClosure (rA ℂ x {0}) K))) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero =>
          have h0 : g 0 = 0 := map_zero mk
          rw [h0]
          exact Submodule.zero_mem _
        | add a b _ _ ha hb =>
          have : g (a + b) = g a + g b := by
            simp only [g, ← map_add (f := _)]
            rfl
          rw [this]
          exact Submodule.add_mem _ ha hb
        | smul a y _ hy =>
          obtain ⟨c, hc1⟩ := hA a.1 a.2
          have e : (⟨((a • y : integralClosure (rA ℂ x {0}) K)).1, ((a • y : integralClosure (rA ℂ x {0}) K)).2⟩ : rB ℂ K x {0}) = ⟨_, hmem a.1 a.2⟩ * ⟨y.1, y.2⟩ :=
            Subtype.ext (Algebra.smul_def a y.1)
          have : g (a • y) = c • g y :=
            (congrArg mk e).trans (by rw [map_mul, hc1, ← Algebra.smul_def])
          rw [this]
          exact Submodule.smul_mem _ _ hy
      refine ⟨⟨(s.image g), ?_⟩⟩
      rw [eq_top_iff]
      rintro q -
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
      have := key ⟨b.1, b.2⟩ (hs ▸ Submodule.mem_top)
      rw [Finset.coe_image]
      exact this
    have hker : ∀ e : fib ℂ K x, ∀ a ∈ I, e.1 a = 0 := by
      intro e a ha
      have : I ≤ RingHom.ker (e.1 : rB ℂ K x {0} →+* ℂ) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨j, rfl⟩
        exact e.2 j
      exact this ha
    let L : fib ℂ K x → ((rB ℂ K x {0} ⧸ I) →ₐ[ℂ] ℂ) := fun e => Ideal.Quotient.liftₐ I e.1 (hker e)
    have hL : ∀ e b, L e (mk b) = e.1 b := fun e b => by
      first | rfl | exact Ideal.Quotient.lift_mk _ _ _
    have hinj : Function.Injective L := by
      intro e e' h
      refine Subtype.ext (AlgHom.ext fun b => ?_)
      rw [← hL, ← hL, h]
    have li : LinearIndependent ℂ (fun e => (L e).toLinearMap) :=
      (linearIndependent_algHom_toLinearMap' ℂ (rB ℂ K x {0} ⧸ I) ℂ).comp L hinj
    have hF : Finite (fib ℂ K x) := li.finite
    refine ⟨hF, fun v => ?_⟩
    obtain ⟨q, hq⟩ := exists_of_li _ li v
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨b, fun e => ?_⟩
    rw [← hq e, ← hL]
    rfl

theorem UpperTheory.Gal.productCup_of_system.cRT_of :
    CRT := by
  intro F K _ _ _ _ _ _ d x hc
  exact chineseRemainder_finiteCover (xv x) hc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DeRhamRestrictionTraceDegreeOne
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.deRham_restriction_trace_degree_one :
    ResidueOfTraceIsFiberSum := by
  intro F L _ _ _ _ _ _ d x hc hred ρ hρ h
  obtain ⟨⟨τ, hτ⟩, -⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F L d (xv x) hc
  have hloc : locCoch ℂ L (xv x) (h : L) Finset.univ = (h : L) • vol0 ℂ L (xv x) := if_pos rfl
  have h1 : trF ℂ τ ρ (locCoch ℂ L (xv x) (h : L) Finset.univ) = ρ (Algebra.trace F L (h : L)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← h1]
  exact GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre ℂ F L d (xv x) hc τ hτ ρ hρ inferInstance hred h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ExistsInv
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {A : Type} [Field A] [Algebra ℂ A]

end

end UpperTheory.Gal.productCup_of_system

private theorem stab_lemma {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro b hb m hm
  change b • m ∈ omB ℂ L B q
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    exact ⟨b * a, B.mul_mem hb ha, v, hv, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

private theorem kos_Z_mono_of_le {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) {κ : Type} [LinearOrder κ] {M M' : Submodule ℂ E}
    (h : M ≤ M') (r : κ → S) (m : ℤ) : (kos act M r).Z m ≤ (kos act M' r).Z m := by
  intro c hc
  simp only [GlobalTheory.PD.Cx.Z, kos, acx, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ,
    forall_const, true_implies, LinearMap.mem_ker] at hc ⊢
  refine ⟨fun s => ?_, hc.2⟩
  have hs := hc.1 s
  split_ifs at hs ⊢ with hcard
  · exact h hs
  · exact hs

theorem UpperTheory.Gal.productCup_of_system.yKE_of :
    LG → OmLoc → RYFT → Htpy → K1 → LocReg → ValBasic → RYBasic → YKE := by
  intro hLG hOm hFT hH hK1 hLR hVB hRB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY κ _ _ r I J hI hr
  have hact : (sysY x j2 d).act = Algebra.lsmul ℂ ℂ (DR ℂ K') := rfl
  have hM : (sysY x j2 d).M I J = omB ℂ K' (RY (xv x) j2 I J) d := rfl
  rw [hact, hM]
  haveI : Algebra.FiniteType ℂ ↥(RY (xv x) j2 I J) := hFT F K K' d x j2 hY I J hI
  set B := RY (xv x) j2 I J with hB
  have hglob : ∀ (m : ℤ) (c : Finset κ → DR ℂ K'),
      (∀ e : ↥B →ₐ[ℂ] ℂ, c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) r).B m) →
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' B d) r).B m := by
    intro m c hc
    refine (hLG K' B (DR ℂ K') κ (fun _ => omB ℂ K' B d) r (fun _ => stab_lemma B d)).1 m c
      (fun e => ?_)
    simp only [(hOm K' B e d).1]
    exact hc e
  have hloc : ∀ e : ↥B →ₐ[ℂ] ℂ, ¬ (∀ l, Val B e (r l) 0) → ∃ l, r l ≠ 0 ∧ (r l)⁻¹ ∈ loc B e := by
    intro e h
    push_neg at h
    obtain ⟨l, hl⟩ := h
    obtain ⟨-, -, hval, hinv⟩ := hVB K' B e
    have hv := hval ⟨r l, hr l⟩
    have hc0 : e ⟨r l, hr l⟩ ≠ 0 := by
      intro h0
      rw [h0] at hv
      exact hl hv
    exact ⟨l, hinv _ _ hv hc0⟩
  have hle : ∀ e : ↥B →ₐ[ℂ] ℂ, omB ℂ K' B d ≤ omB ℂ K' (loc B e) d :=
    fun e => (hOm K' B e d).2.2 _ (hVB K' B e).1
  have hbad : ∀ (m : ℤ) (c : Finset κ → DR ℂ K'),
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' B d) r).Z m →
      ∀ e : ↥B →ₐ[ℂ] ℂ, ¬ (∀ l, Val B e (r l) 0) →
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) r).B m := by
    intro m c hc e h
    obtain ⟨l, hl0, hlinv⟩ := hloc e h
    have hIn : InSp (loc B e) r 1 := by
      refine ⟨fun l' => if l' = l then (r l)⁻¹ else 0, fun l' => ?_, ?_⟩
      · dsimp only
        split_ifs
        · exact hlinv
        · exact (loc B e).zero_mem
      · simp [ite_mul, hl0]
    have := hH K' (DR ℂ K') (Algebra.lsmul ℂ ℂ (DR ℂ K')) κ (loc B e)
      (omB ℂ K' (loc B e) d) r (stab_lemma _ d) m c (kos_Z_mono_of_le _ (hle e) r m hc) 1 hIn
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · intro hyp m hm c hc
    apply hglob m c
    intro e
    by_cases h : ∀ l, Val B e (r l) 0
    · obtain ⟨e0, hOv, hIn⟩ := hyp e h
      have hlocEq : loc B e = loc (rB ℂ K' (xv x) {0}) e0.1 := hOv.2.1
      have hReg : Reg (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) (tt K' x) := by
        rw [hlocEq]
        exact hLR F K' d x hY.covY hY.red e0
      have hKE := hK1 K' (DR ℂ K') (Algebra.lsmul ℂ ℂ (DR ℂ K')) κ (loc B e)
        (omB ℂ K' (loc B e) d) r d (tt K' x) (stab_lemma _ d) (fun l => (hVB K' B e).1 (hr l))
        hReg (fun j => by rw [hlocEq]; exact hIn j)
      exact hKE m hm (kos_Z_mono_of_le _ (hle e) r m hc)
    · exact hbad m c hc e h
  · intro m c hc hyp
    apply hglob m c
    intro e
    by_cases h : ∀ l, Val B e (r l) 0
    · exact hyp e h
    · exact hbad m c hc e h
  · intro y hy hyp
    refine (hLG K' B (DR ℂ K') κ (fun _ => omB ℂ K' B d) r (fun _ => stab_lemma B d)).2 y
      (fun e => ?_)
    simp only [(hOm K' B e d).1]
    by_cases h : ∀ l, Val B e (r l) 0
    · exact hyp e h
    · obtain ⟨l, hl0, hlinv⟩ := hloc e h
      unfold sm
      refine Submodule.mem_iSup_of_mem (r l) (Submodule.mem_iSup_of_mem (Set.mem_range_self l) ?_)
      refine Submodule.mem_map.mpr ⟨_, stab_lemma (loc B e) d _ hlinv y (hle e hy), ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel₀ hl0, map_one, Module.End.one_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ExistsPt
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section IntegralMvPolynomialLemmas
variable {L V σ : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
  [AddCommGroup V] [Module L V] [Module ℂ V] [IsScalarTower ℂ L V]

variable [LinearOrder σ]

end IntegralMvPolynomialLemmas

end UpperTheory.Gal.productCup_of_system

private theorem lG_of_lemma {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (I : Ideal B) (hI : I ≠ ⊤) :
    ∃ e : B →ₐ[ℂ] ℂ, ∀ b ∈ I, e b = 0 := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  letI := Ideal.Quotient.field M
  haveI : Module.Finite ℂ (B ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ M)
  haveI : Algebra.IsIntegral ℂ (B ⧸ M) := Algebra.IsIntegral.of_finite ℂ _
  have hbij : Function.Bijective (algebraMap ℂ (B ⧸ M)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ := AlgEquiv.ofBijective (Algebra.ofId ℂ (B ⧸ M)) hbij
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M), fun b hb => ?_⟩
  have h0 : Ideal.Quotient.mk M b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hb)
  simp [h0]

private theorem lG_of_lemma_2 {L W : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [AddCommGroup W] [Module L W] [Module ℂ W] [IsScalarTower ℂ L W] (N : Submodule ℂ W)
    (hN : ∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) (e : B →ₐ[ℂ] ℂ) :
    ∃ S : Submodule ℂ W, (∀ x ∈ S, ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) ∧
      ∀ x, (∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) → x ∈ S := by
  refine ⟨{ carrier := {x | ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N}
            add_mem' := ?_
            zero_mem' := ⟨1, by simp, by simp⟩
            smul_mem' := ?_ }, fun x hx => hx, fun x hx => hx⟩
  · rintro x y ⟨b1, h1, hx⟩ ⟨b2, h2, hy⟩
    refine ⟨b1 * b2, by simp [h1, h2], ?_⟩
    rw [smul_add]
    apply N.add_mem
    · rw [Subalgebra.coe_mul, mul_comm (b1 : L), mul_smul]
      exact hN b2 _ hx
    · rw [Subalgebra.coe_mul, mul_smul]
      exact hN b1 _ hy
  · rintro c x ⟨b, hb, hx⟩
    exact ⟨b, hb, by rw [smul_comm]; exact N.smul_mem c hx⟩

private theorem lG_of_lemma_3 {L W : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] [AddCommGroup W] [Module L W] [Module ℂ W] [IsScalarTower ℂ L W]
    (N : Submodule ℂ W) (hN : ∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) (x : W)
    (hx : ∀ e : B →ₐ[ℂ] ℂ, ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) : x ∈ N := by
  let I : Ideal B :=
    { carrier := {b | (b : L) • x ∈ N}
      add_mem' := fun {a c} ha hc => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *
        exact N.add_mem ha hc
      zero_mem' := by simp
      smul_mem' := fun c {b} hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *
        exact hN c _ hb }
  by_cases hI : I = ⊤
  · have h1 : (1 : B) ∈ I := by rw [hI]; exact Submodule.mem_top
    change ((1 : B) : L) • x ∈ N at h1
    simpa using h1
  · obtain ⟨e, he⟩ := lG_of_lemma B I hI
    obtain ⟨b, hb, hbx⟩ := hx e
    exact absurd (he b hbx) hb

theorem UpperTheory.Gal.productCup_of_system.lG_of :
    LG := by
  intro L _ _ B _ V σ _ _ _ _ _ _ A w hA
  have hAs : ∀ s, ∀ b : B, ∀ v ∈ A s, (b : L) • v ∈ A s := fun s b v hv => by
    simpa using hA s (b : L) b.2 v hv
  have hloc : ∀ (e : B →ₐ[ℂ] ℂ) (N : Submodule ℂ V), (∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) →
      ∀ v ∈ locM B e N, ∃ b : B, e b ≠ 0 ∧ (b : L) • v ∈ N := by
    intro e N hN v hv
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B N hN e
    have hle : locM B e N ≤ S := by
      unfold locM
      rw [Submodule.span_le]
      intro u hu
      exact hS2 u hu
    exact hS1 v (hle hv)
  constructor
  · intro n c hc
    have hwd : ∀ (b : L) (x : Finset σ → V),
        wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) (b • x) =
          b • wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) x := by
      intro b x
      funext t
      simp [wd, Finset.smul_sum, smul_comm b]
    have hC : ∀ (A' : Finset σ → Submodule ℂ V) (x : Finset σ → V),
        x ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1) ↔
          ∀ s, x s ∈ (if (s.card : ℤ) = n - 1 then A' s else ⊥) := by
      intro A' x
      simp [acx, Submodule.mem_pi]
    have hB : ∀ (A' : Finset σ → Submodule ℂ V) (c : Finset σ → V),
        c ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).B n ↔
          ∃ x ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1),
            wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) x = c := by
      intro A' c
      simp [Cx.B, acx]
    have hCstab : ∀ b : B, ∀ x ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1),
        (b : L) • x ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1) := by
      intro b x hx
      rw [hC] at hx ⊢
      intro s
      have hxs := hx s
      simp only [Pi.smul_apply]
      split_ifs at hxs ⊢ with h
      · exact hAs s b _ hxs
      · rw [Submodule.mem_bot] at hxs ⊢
        simp [hxs]
    have hNstab : ∀ b : B, ∀ c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n,
        (b : L) • c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n := by
      intro b c hc
      rw [hB] at hc ⊢
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨_, hCstab b x hx, hwd _ _⟩
    refine lG_of_lemma_3 B _ hNstab c fun e => ?_
    obtain ⟨x, hx, rfl⟩ := (hB _ _).1 (hc e)
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B _ hCstab e
    have hxS : x ∈ S := by
      rw [← Finset.univ_sum_single x]
      refine S.sum_mem fun s _ => ?_
      have hxs := (hC _ x).1 hx s
      split_ifs at hxs with h
      · obtain ⟨b, hb, hbv⟩ := hloc e (A s) (hAs s) _ hxs
        apply hS2
        refine ⟨b, hb, ?_⟩
        rw [hC]
        intro t
        by_cases hts : t = s
        · subst hts
          simpa [h] using hbv
        · simp [hts]
      · rw [Submodule.mem_bot] at hxs
        rw [hxs, Pi.single_zero]
        exact S.zero_mem
    obtain ⟨b, hb, hbx⟩ := hS1 x hxS
    exact ⟨b, hb, (hB _ _).2 ⟨_, hbx, hwd _ _⟩⟩
  · intro m hm
    have hmem : ∀ r ∈ Set.range w, ∀ u ∈ A ∅,
        r • u ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) := by
      intro r hr u hu
      unfold sm
      exact (le_iSup₂ (f := fun r (_ : r ∈ Set.range w) =>
        Submodule.map (Algebra.lsmul ℂ ℂ V r) (A ∅)) r hr) (Submodule.mem_map_of_mem hu)
    have hstab : ∀ b : B, ∀ v ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w),
        (b : L) • v ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) := by
      intro b v hv
      have hle : sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) ≤
          (sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w)).comap (Algebra.lsmul ℂ ℂ V (b : L)) := by
        conv_lhs => unfold sm
        refine iSup₂_le fun r hr => ?_
        rintro _ ⟨u, hu, rfl⟩
        rw [Submodule.mem_comap]
        simp only [Algebra.lsmul_coe]
        rw [smul_comm]
        exact hmem r hr _ (hAs ∅ b u hu)
      simpa using hle hv
    refine lG_of_lemma_3 B _ hstab m fun e => ?_
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B _ hstab e
    apply hS1
    have hle : sm (Algebra.lsmul ℂ ℂ V) (locM B e (A ∅)) (Set.range w) ≤ S := by
      conv_lhs => unfold sm
      refine iSup₂_le fun r hr => ?_
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨b, hb, hbv⟩ := hloc e (A ∅) (hAs ∅) v hv
      apply hS2
      refine ⟨b, hb, ?_⟩
      simp only [Algebra.lsmul_coe]
      rw [smul_comm]
      exact hmem r hr _ hbv
    exact hle (hm e)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PMinorSum
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem det_submatrix_orderEmbOfFin_eq_subtype {R : Type*} [CommRing R] {d k : ℕ}
    (B : Matrix (Fin d) (Fin d) R) (s : Finset (Fin d)) (h : s.card = k) :
    (B.submatrix (s.orderEmbOfFin h) (s.orderEmbOfFin h)).det =
      (B.submatrix (Subtype.val : s → Fin d) Subtype.val).det := by
  rw [← Matrix.det_submatrix_equiv_self (s.orderIsoOfFin h).toEquiv
    (B.submatrix (Subtype.val : s → Fin d) Subtype.val)]
  rfl

theorem UpperTheory.Gal.productCup_of_system.minorSum_of :
    MinorSum := by
  intro d a A
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact (det_submatrix_orderEmbOfFin_eq_subtype A S _).symm
end

