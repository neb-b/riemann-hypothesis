module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionIntegralStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

open scoped Pointwise in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_slice_section_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice (k := k) a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  have hInvariant : ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice (k := k) a d,
        Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
    obtain ⟨⟨hlc, hcpt⟩, hrk⟩ := hΦ

    have hcl : IsClosed (Function.support Φ) := by
      have : Function.support Φ = (Φ ⁻¹' {0})ᶜ := by ext; simp
      rw [this, isClosed_compl_iff]; exact hlc.isOpen_fiber 0
    have hS : tsupport Φ ⊆ {Y | Y.rank = a} := by
      intro Y hY
      rw [tsupport, hcl.closure_eq] at hY
      by_contra h; exact hY (hrk Y h)
    set f : Matrix (Fin a) (Fin d) k → GL (Fin a) k × Matrix (Fin a) (Fin d) k :=
      fun Y => (s Y, ((s Y)⁻¹).val * Y) with hf
    have hfc : ContinuousOn f (tsupport Φ) := by
      have hs' := hs.mono hS
      refine ContinuousOn.prodMk hs' ?_
      exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_continuousOn
        ((Units.continuous_val.comp_continuousOn hs'.inv).prodMk continuousOn_id)
    have hA : IsCompact (f '' tsupport Φ) := hcpt.image_of_continuousOn hfc
    set n : Set ((GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k) :=
      {p | Φ (p.1.1.val * p.2.val * p.1.2) = Φ (p.1.1.val * p.1.2)} with hn
    have hno : IsOpen n := by
      have h1 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
          Φ (p.1.1.val * p.2.val * p.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      have h2 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
          Φ (p.1.1.val * p.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      exact (h1.prodMk h2) {q | q.1 = q.2}
    have hsub : (f '' tsupport Φ) ×ˢ ({1} : Set (GL (Fin a) k)) ⊆ n := by
      rintro ⟨⟨g, Z⟩, x⟩ ⟨_, hx⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp [hn]
    obtain ⟨u, v, -, hv, hAu, h1v, huv⟩ := generalized_tube_lemma hA isCompact_singleton hno hsub

    have key : ∀ (h : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d → Φ (h.val * Z) ≠ 0 →
        (h, Z) ∈ f '' tsupport Φ := by
      intro h Z hZ hne
      have hY : h.val * Z ∈ tsupport Φ := subset_tsupport _ hne
      have hr := hS hY
      have e : (s (h.val * Z))⁻¹ * h = 1 := by
        apply huniq Z _ hZ
        have := hsl _ hr
        simpa [Units.val_mul, Matrix.mul_assoc] using this
      have e' : s (h.val * Z) = h := by
        have := congrArg (fun t => s (h.val * Z) * t) e
        simpa [mul_assoc] using this.symm
      refine ⟨h.val * Z, hY, ?_⟩
      simp only [hf, e', Prod.mk.injEq, true_and]
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    refine ⟨v ∩ v⁻¹, Filter.inter_mem (hv.mem_nhds (h1v rfl)) ?_, ?_⟩
    · exact (hv.inv).mem_nhds (by simpa using h1v rfl)
    rintro x ⟨hxv, hxv'⟩ g Z hZ
    by_cases h0 : Φ (g.val * Z) ≠ 0
    · exact huv (Set.mk_mem_prod (hAu (key g Z hZ h0)) hxv)
    by_cases h0' : Φ (g.val * x.val * Z) ≠ 0
    · have hm : (g * x, Z) ∈ f '' tsupport Φ := key (g * x) Z hZ (by simpa [Units.val_mul] using h0')
      have := huv (Set.mk_mem_prod (hAu hm) (show x⁻¹ ∈ v from hxv'))
      simp only [hn, Set.mem_ofPred_eq] at this
      rw [Units.val_mul, Matrix.mul_assoc g.val x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one] at this
      rw [this]
    push Not at h0 h0'
    rw [h0, h0']
  exact hInvariant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionMeasureStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_slice_section_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ (g : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d →
      Φ (g.val * Z) ≠ 0 → g ∈ C := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcs⟩, hrank⟩ := hΦ
  have hclosed : IsClosed (Function.support Φ) :=
    (hlc.isClopen_fiber (0 : ℂ)).compl.isClosed
  have hsub : tsupport Φ ⊆ {Y | Y.rank = a} := by
    change closure (Function.support Φ) ⊆ _
    rw [hclosed.closure_eq]
    intro Y hY
    by_contra h
    exact hY (hrank Y h)
  refine ⟨s '' tsupport Φ, hcs.isCompact.image_of_continuousOn (hs.mono hsub), ?_⟩
  intro g Z hZ hne
  have hY : g.val * Z ∈ tsupport Φ := subset_tsupport _ hne
  have hslice : ((s (g.val * Z))⁻¹ * g).val * Z ∈ slice (k := k) a d := by
    rw [Units.val_mul, Matrix.mul_assoc]
    exact hsl _ (hsub hY)
  have heq := huniq Z _ hZ hslice
  rw [inv_mul_eq_one] at heq
  exact ⟨g.val * Z, hY, heq⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGramSize
section
set_option autoImplicit false
noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.TrBasisQuot

theorem isTranscendenceBasis_quot_polynomial {k : Type} [Field k] {m : ℕ}
    (p : Polynomial (MvPolynomial (Fin m) k)) (hp : Prime p) (hdeg : 0 < p.natDegree) :
    IsTranscendenceBasis k (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
  classical
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let φ : MvPolynomial (Fin m) k →ₐ[k] Polynomial (MvPolynomial (Fin m) k) ⧸ Ideal.span {p} :=
    (Ideal.Quotient.mkₐ k (Ideal.span {p})).comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k) _)
  have hφ : ∀ b, φ b = Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C b) := fun b => rfl
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
    by_contra hb0
    have := Polynomial.natDegree_le_of_dvd hb (Polynomial.C_ne_zero.2 hb0)
    rw [Polynomial.natDegree_C] at this
    omega
  have haev : MvPolynomial.aeval (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) = φ :=
    MvPolynomial.algHom_ext fun j => by simp [hφ]
  have hind : AlgebraicIndependent k (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
    rw [algebraicIndependent_iff_injective_aeval, haev]
    exact hinj
  rw [hind.isTranscendenceBasis_iff_isAlgebraic]
  have hS : ∀ b, φ b ∈ Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
    intro b
    rw [Algebra.adjoin_range_eq_range_aeval, haev]
    exact AlgHom.mem_range_self φ b
  let ψ := RingHom.codRestrict φ.toRingHom (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j)))) (fun b => hS b)
  have hψ : Function.Injective ψ := fun a b h => hinj (congrArg Subtype.val h)
  have hr : IsAlgebraic (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))))
      (Ideal.Quotient.mk (Ideal.span {p}) Polynomial.X) := by
    refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff hψ).2 hp.ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hc : (algebraMap _ (Polynomial (MvPolynomial (Fin m) k) ⧸ Ideal.span {p})).comp ψ =
        (Ideal.Quotient.mk (Ideal.span {p})).comp Polynomial.C := RingHom.ext fun b => rfl
    rw [hc, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self p
  have htop : Algebra.adjoin (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))))
      {Ideal.Quotient.mk (Ideal.span {p}) Polynomial.X} = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine Polynomial.induction_on q (fun b => ?_) (fun f g hf hg => ?_) (fun n b ih => ?_)
    · exact Subalgebra.algebraMap_mem _ (⟨φ b, hS b⟩ : Algebra.adjoin k _)
    · rw [map_add (f := _)]
      exact add_mem hf hg
    · rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem ih (Algebra.subset_adjoin rfl)
  have h1 := (Algebra.isAlgebraic_adjoin_singleton_iff).2 hr
  exact ⟨fun z => h1 z (by rw [htop]; trivial)⟩

theorem trBasis_mod_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F),
    AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) →
    ∀ t : A, Irreducible t → Prime t ∧ ∃ m : ℕ, d = m + 1 ∧ ∃ y : Fin m → A,
      IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) := by
  intro k F _ _ _ d u hu A hA t ht
  subst hA
  classical
  have ht0 : Irreducible (hu.aevalEquiv.symm t) :=
    (MulEquiv.irreducible_iff hu.aevalEquiv.symm.toMulEquiv).2 ht
  cases d with
  | zero =>
    exfalso
    have h := MvPolynomial.eq_C_of_isEmpty (hu.aevalEquiv.symm t)
    apply ht0.not_isUnit
    rw [h]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 fun hc => ht0.ne_zero ?_)
    rw [h, hc, map_zero]
  | succ m =>
    obtain ⟨i, hi⟩ : ∃ i, (hu.aevalEquiv.symm t).degreeOf i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : (hu.aevalEquiv.symm t).totalDegree = 0 := by
        rw [MvPolynomial.totalDegree_eq_zero_iff]
        intro mm hmm x
        have := MvPolynomial.monomial_le_degreeOf x hmm
        rw [hcon x] at this
        omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
      apply ht0.not_isUnit
      rw [h0]
      refine IsUnit.map _ (isUnit_iff_ne_zero.2 fun hc => ht0.ne_zero ?_)
      rw [h0, hc, map_zero]
    let E := hu.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin (m + 1)) i)).trans
      (MvPolynomial.finSuccEquiv k m))
    have hdeg : 0 < (E t).natDegree := by
      have h1 : (E t).natDegree = ((MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) i))
          (hu.aevalEquiv.symm t)).degreeOf 0 :=
        MvPolynomial.natDegree_finSuccEquiv _
      have h2 := MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (0 : Fin (m + 1)) i).injective
        (p := hu.aevalEquiv.symm t) i
      rw [Equiv.swap_apply_right] at h2
      rw [h1, h2]
      omega
    have hpE : Prime (E t) :=
      ((MulEquiv.irreducible_iff E.toMulEquiv).2 ht).prime
    have hpt : Prime t := (MulEquiv.prime_iff E.toMulEquiv).1 hpE
    refine ⟨hpt, m, rfl, fun j => E.symm (Polynomial.C (MvPolynomial.X j)), ?_⟩
    have hI : Ideal.span {E t} = (Ideal.span {t}).map (E : _ →+* _) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    have hb := (Ideal.quotientEquivAlg (Ideal.span {t}) (Ideal.span {E t}) E hI).symm.isTranscendenceBasis
      (GlobalTheory.TrBasisQuot.isTranscendenceBasis_quot_polynomial (E t) hpE hdeg)
    have hfun : (⇑((Ideal.span {t}).quotientEquivAlg (Ideal.span {E t}) E hI).symm ∘ fun j : Fin m =>
        (Ideal.Quotient.mk (Ideal.span {E t})) (Polynomial.C (MvPolynomial.X j))) =
        fun j => Ideal.Quotient.mk (Ideal.span {t}) (E.symm (Polynomial.C (MvPolynomial.X j))) := by
      funext j
      simp only [Function.comp_apply, Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    rw [hfun] at hb
    exact hb

end GlobalTheory.TrBasisQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicPrimitiveRootsFilteredColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicPrimitiveRoots_filtered_colimit : ∀ (q : ℕ) (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ ζ : Prim q c.pt, ∃ (j : J) (ξ : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = ζ) ∧ ∀ (j : J) (ξ ξ' : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = Prim.map (c.ι.app j).hom ξ' → ∃ (k : J) (f : j ⟶ k), Prim.map (D.map f).hom ξ = Prim.map (D.map f).hom ξ' := by
  first | (exact @GlobalTheory.EtC.prim_filtered_colimit) | (exact GlobalTheory.EtC.prim_filtered_colimit) | (intros; apply GlobalTheory.EtC.prim_filtered_colimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTCompDTStatement
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero : ∀ a b c d : ℕ, c + d + 2 = a + b → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  first | (exact @GlobalTheory.EZ.TotSq.dT_sq) | (exact GlobalTheory.EZ.TotSq.dT_sq) | (intros; apply GlobalTheory.EZ.TotSq.dT_sq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DadjCombination
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem dadj_combination : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (n : ℕ) (u : Fin n → F), ∀ v ∈ Algebra.adjoin k (Set.range u), ∃ c : Fin n → F, (∀ j, c j ∈ Algebra.adjoin k (Set.range u)) ∧ D k K (algebraMap F K v) = ∑ j, algebraMap F K (c j) • D k K (algebraMap F K (u j)) := by
  intro k F K _ _ _ _ _ _ _ n u v hv
  induction hv using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨Pi.single j 1, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using Subalgebra.one_mem _
      · simpa [Pi.single_apply, h] using Subalgebra.zero_mem _
    · simp [Pi.single_apply]
  | algebraMap r =>
    refine ⟨0, fun _ => Subalgebra.zero_mem _, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap]
    simp
  | add x y hx hy ihx ihy =>
    obtain ⟨cx, hcx, ex⟩ := ihx
    obtain ⟨cy, hcy, ey⟩ := ihy
    refine ⟨cx + cy, fun j => add_mem (hcx j) (hcy j), ?_⟩
    simp only [map_add (f := _), ex, ey, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | mul x y hx hy ihx ihy =>
    obtain ⟨cx, hcx, ex⟩ := ihx
    obtain ⟨cy, hcy, ey⟩ := ihy
    refine ⟨fun j => x * cy j + y * cx j, fun j => add_mem (mul_mem hx (hcy j)) (mul_mem hy (hcx j)), ?_⟩
    rw [map_mul, Derivation.leibniz, ex, ey]
    simp only [Finset.smul_sum, smul_smul, map_add (f := _), map_mul, add_smul, Finset.sum_add_distrib]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthGeThreeFiniteEtalePuncturedRegular
section
open IsLocalRing

namespace GlobalTheory.LocalLefschetz

lemma two_le_of_add_one {x y : WithBot ℕ∞} (h : x + 1 = y) (hy : 3 ≤ y) : 2 ≤ x := by
  subst h
  induction x using WithBot.recBotCoe with
  | bot => simp at hy
  | coe n =>
    have h3 : (3 : ℕ∞) ≤ n + 1 := WithBot.coe_le_coe.mp hy
    have : (2 : ℕ∞) ≤ n := by
      induction n using ENat.recTopCoe with
      | top => simp
      | coe m =>
        have : (3 : ℕ) ≤ m + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : 2 ≤ m)
    exact WithBot.coe_le_coe.mpr this

theorem depth_three : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  intro R _ _ hcomp hdim f hf hf2 _ hpur A _ _ _ hdep hEt
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (Ideal.zero_mem _)
  haveI : IsDomain R := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain R
  have hreg : IsSMulRegular A f :=
    _root_.GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hdep) hEt f hf0
  haveI hRb : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
  have hdimb : 2 ≤ ringKrullDim (R ⧸ Ideal.span {f}) :=
    two_le_of_add_one
      (ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2) hdim
  haveI : Module.Finite R (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R A))).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hdepb := GlobalTheory.modDepthGE_quotient_map_span_singleton R A f hf hreg 1 hdep
  have hEtb := _root_.GlobalTheory.etale_quotient_of_etale_punctured R A f hEt
  obtain ⟨A', _, _, hA'fin, ι, hι, hdep', hEt', k, hk⟩ := _root_.GlobalTheory.exists_finite_depth_two_hull_of_etale_off_closed_point _ hdimb _ hdepb hEtb
  have hfree : Module.Free (R ⧸ Ideal.span {f}) A' := hpur A' hdep' hEt'
  obtain ⟨_, _⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (R ⧸ Ideal.span {f})
  have hnf : ¬ IsField (R ⧸ Ideal.span {f}) := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [this] at hdimb
    exact absurd hdimb (by decide)
  have hEtA' : Algebra.Etale (R ⧸ Ideal.span {f}) A' := by
    refine _root_.GlobalTheory.PurityDisc.etale_of_etale_height_one _ A' hnf fun p _ hp => hEt' p ?_
    rintro rfl
    have h1 := maximalIdeal_height_eq_ringKrullDim (R := R ⧸ Ideal.span {f})
    rw [hp] at h1
    rw [← h1] at hdimb
    exact absurd hdimb (by decide)
  obtain ⟨B, _, _, hBfin, hBfree, hBet, ⟨e⟩⟩ := _root_.GlobalTheory.EtaleLiftQuot.exists_finite_free_etale_lift R hcomp f hf A'
  let φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B) :=
    { toRingHom := e.symm.toRingHom.comp (ι.toRingHom.comp (Ideal.Quotient.mk _))
      commutes' := fun r => by
        have h1 : (Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) (algebraMap R A r)) =
            algebraMap (R ⧸ Ideal.span {f}) _ (algebraMap R (R ⧸ Ideal.span {f}) r) := by
          rw [← IsScalarTower.algebraMap_apply]; rfl
        show e.symm (ι (Ideal.Quotient.mk _ (algebraMap R A r))) = _
        rw [h1, ι.commutes, e.symm.commutes, ← IsScalarTower.algebraMap_apply] }
  have hφ : ∀ a, φ a = e.symm (ι (Ideal.Quotient.mk _ a)) := fun a => rfl
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.LiftHom.liftHom_of_etale_punctured R hcomp hdim f hf hf0 A hEt B φ
  have hψa : ∀ a, Ideal.Quotient.mk _ (ψ a) = φ a := fun a => by
    rw [← hψ]; rfl
  have hBreg : IsSMulRegular B f := fun x y h => smul_right_injective B hf0 h
  have hsat : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
      a ∈ (Ideal.span {f}).map (algebraMap R A) := by
    intro a ha
    have h1 : φ a = 0 := by
      rw [← hψa]; exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [hφ] at h1
    have h2 : ι (Ideal.Quotient.mk _ a) = 0 := by
      simpa using h1
    have h3 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) a = 0 :=
      hι (by rw [h2, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨hinj, hfsat⟩ := _root_.GlobalTheory.injective_and_saturated_of_injective_mod_regular R A B f hf hBreg ψ hsat
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f})) ≤ maximalIdeal (R ⧸ Ideal.span {f}) := by
    rw [Ideal.map_le_iff_le_comap]
    have : (maximalIdeal (R ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      haveI := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective (K := maximalIdeal (R ⧸ Ideal.span {f}))
      exact IsLocalRing.eq_maximalIdeal this
    rw [this]
  have hspan : ∀ z : B, z ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : B, z = f • c := by
    intro z hz
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hz
    obtain ⟨c, hc⟩ := hz
    exact ⟨c, by rw [Algebra.smul_def, ← hc, mul_comm]⟩
  have hcok : ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c := by
    refine ⟨k, fun x hx b => ?_⟩
    have hx' : Ideal.Quotient.mk (Ideal.span {f}) x ∈ maximalIdeal (R ⧸ Ideal.span {f}) ^ k := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {f})) hx
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono hmap k this
    obtain ⟨abar, habar⟩ := hk _ hx' (e (Ideal.Quotient.mk _ b))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
    refine ⟨a, ?_⟩
    have h1 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R B)) (x • b - ψ a) = 0 := by
      rw [map_sub, hψa, hφ]
      change Ideal.Quotient.mk _ (x • b) - e.symm (ι (Ideal.Quotient.mk _ a)) = 0
      have habar' : ι (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk (Ideal.span {f}) x • e (Ideal.Quotient.mk _ b) := habar
      have h2 : ∀ z, e.symm (Ideal.Quotient.mk (Ideal.span {f}) x • e z) =
          Ideal.Quotient.mk (Ideal.span {f}) x • z := fun z => by
        rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, AlgEquiv.symm_apply_apply, ← Algebra.smul_def]
      rw [habar', h2]
      change Ideal.Quotient.mkₐ R _ (x • b) - _ = 0
      rw [map_smul, ← algebraMap_smul (R ⧸ Ideal.span {f}) x, Ideal.Quotient.algebraMap_eq]
      exact sub_eq_zero.mpr rfl
    obtain ⟨c, hc⟩ := hspan _ (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    exact ⟨c, by rw [← hc]; abel⟩
  have hdim1 : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) := le_trans (by decide) hdimb
  obtain ⟨s, hs0, hs⟩ := _root_.GlobalTheory.cokernel_torsion_of_finiteLength_mod R f hdim1 A B ψ hcok
  have hEtB : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B) :=
    fun p _ _ => inferInstance
  obtain ⟨k2, hk2⟩ := GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum R A B hEt hEtB ψ hinj ⟨s, hs0, hs⟩
  have hdesc : ∀ (n : ℕ) (b : B), f ^ n • b ∈ ψ.range → b ∈ ψ.range := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      apply ih
      apply hfsat
      rwa [← mul_smul, ← pow_succ']
  have hsurj : Function.Surjective ψ := fun b => by
    obtain ⟨a, ha⟩ := hdesc k2 b (hk2 _ (Ideal.pow_mem_pow hf k2) b)
    exact ⟨a, ha⟩
  let eqv : A ≃ₐ[R] B := AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  haveI : Module.Free R A := Module.Free.of_equiv eqv.symm.toLinearEquiv
  haveI : Nontrivial A := by
    obtain ⟨rs, -, -, hr⟩ := hdep
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hr.top_ne_smul (Subsingleton.elim _ _)
  exact _root_.GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing R hdim A

end GlobalTheory.LocalLefschetz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhoodStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  first | (exact @GlobalTheory.HilbAff.exists_basic_nhd) | (exact GlobalTheory.HilbAff.exists_basic_nhd) | (intros; apply GlobalTheory.HilbAff.exists_basic_nhd  <;> assumption)
end

