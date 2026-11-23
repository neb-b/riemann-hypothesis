module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeModuleGeneratorKaehlerWedgeRegularPairCons
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing KaehlerDifferential Module

theorem mem_maximalIdeal_of_mul_add_mul_mem_sq {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {t u : R} (h : Ideal.span {t, u} = maximalIdeal R)
    (hd : ringKrullDim R = 2) {a b : R} (hab : a * t + b * u ∈ maximalIdeal R ^ 2) :
    a ∈ maximalIdeal R := by
  by_contra ha
  have hau : IsUnit a := by simpa [mem_maximalIdeal, mem_nonunits_iff] using ha
  have hu : u ∈ maximalIdeal R := h ▸ Ideal.subset_span (by simp)
  have hle : maximalIdeal R ≤ Ideal.span {u} ⊔ maximalIdeal R ^ 2 := by
    conv_lhs => rw [← h]
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · obtain ⟨c, hc⟩ := hau.exists_left_inv
      have e : x = c * (a * x + b * u) + (-(c * b)) * u := by
        linear_combination (-x) * hc
      rw [e]
      exact add_mem (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hab))
        (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self u)))
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have h1 := spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq (Set.finite_singleton u)
    ((Ideal.span_singleton_le_iff_mem _).2 hu) hle
  rw [Set.ncard_singleton] at h1
  have h2 := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at h2
  have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
  have := h2.trans h3
  norm_num at this

theorem isFreeGen_dForm_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (t u : Q),
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
    ringKrullDim Q = 2 →
    ∃ (m : ℕ) (z : Fin m → Q),
      (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
      IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem)
        (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  intro L _ cL Q hQ t u hspan hdim
  letI := hQ.isLocalRing
  letI : Algebra ℂ Q := (cL.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  haveI : IsRegularLocalRing Q := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q ?_
    rw [hdim, ← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Q) (Set.toFinite ({t, u} : Set Q))
    have h2 : ({t, u} : Set Q).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    exact_mod_cast h1.trans h2
  haveI : Algebra.FormallySmooth ℂ Q := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ Q
  have hs : Function.Surjective (algebraMap Q (ResidueField Q)) := residue_surjective
  haveI : Algebra.EssFiniteType ℂ (ResidueField Q) := .comp ℂ Q _
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := ℂ) hs).mpr
    inferInstance
  have hker : RingHom.ker (algebraMap Q (ResidueField Q)) = maximalIdeal Q := ker_residue
  have htm : t ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have hum : u ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have ht0 : algebraMap Q (ResidueField Q) t = 0 := (residue_eq_zero_iff t).mpr htm
  have hu0 : algebraMap Q (ResidueField Q) u = 0 := (residue_eq_zero_iff u).mpr hum

  obtain ⟨s, hsb⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  haveI := hsb.isAlgebraic_field
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin ℂ (Set.range ((↑) : s → ResidueField Q))) (ResidueField Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨bκ, hbκ⟩ := exists_basis_kaehler_of_algebraicIndependent hsb.1
  haveI : Finite s := Module.Finite.finite_basis bκ
  let e : Fin (Nat.card s) ≃ s := (Finite.equivFin s).symm
  let b' := bκ.reindex e.symm
  have hb' : ∀ i, b' i = D ℂ (ResidueField Q) (e i) := fun i => by
    rw [Basis.reindex_apply, Equiv.symm_symm, hbκ]
  let z : Fin (Nat.card s) → Q := fun i => Function.surjInv hs (e i : ResidueField Q)
  have hz : ∀ i, algebraMap Q (ResidueField Q) (z i) = e i := fun i => Function.surjInv_eq hs _
  refine ⟨Nat.card s, z, fun P hP => ?_, ?_⟩
  · have e1 : algebraMap Q (ResidueField Q) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)
        = MvPolynomial.aeval (fun i => (e i : ResidueField Q)) P := by
      rw [show (fun i => (e i : ResidueField Q)) = algebraMap Q (ResidueField Q) ∘ z from
        funext fun i => (hz i).symm, MvPolynomial.aeval_algebraMap_apply]
      rfl
    refine (residue_ne_zero_iff_isUnit _).mp ?_
    change algebraMap Q (ResidueField Q) _ ≠ 0
    rw [e1]
    exact fun h0 => hP ((algebraicIndependent_iff.1 (hsb.1.comp e e.injective)) P h0)
  · let v : Fin (Nat.card s + 2) → Q := Fin.cons t (Fin.cons u z : Fin (Nat.card s + 1) → Q)
    let w : Fin (Nat.card s + 2) → (ResidueField Q) ⊗[Q] Ω[Q⁄ℂ] := TensorProduct.mk Q (ResidueField Q) Ω[Q⁄ℂ] 1 ∘ fun i => D ℂ Q (v i)
    have hw0 : w 0 = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q t := rfl
    have hw1 : w (Fin.succ 0) = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q u := rfl
    have hwz : ∀ i : Fin (Nat.card s), w i.succ.succ = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (z i) := fun i => rfl
    have hmb : ∀ x : Q, mapBaseChange ℂ Q (ResidueField Q) ((1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x) = D ℂ (ResidueField Q) (algebraMap Q (ResidueField Q) x) :=
      fun x => by rw [mapBaseChange_tmul, one_smul, map_D]
    have hpair : ∀ a b : Q, (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) =
        algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0) := fun a b => by
      rw [hw0, hw1]
      simp only [map_add (f := _), Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul]
      rw [← algebraMap_smul (ResidueField Q) t, ← algebraMap_smul (ResidueField Q) u, ht0, hu0]
      simp only [zero_smul, add_zero, algebraMap_smul]
    have hkc : ∀ x (hx : x ∈ RingHom.ker (algebraMap Q (ResidueField Q))),
        kerCotangentToTensor ℂ Q (ResidueField Q) ((RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨x, hx⟩) =
          (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x := fun x hx => kerCotangentToTensor_toCotangent _ _ _ _

    have hsp : Submodule.span (ResidueField Q) (Set.range w) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      let c := b'.repr (mapBaseChange ℂ Q (ResidueField Q) y)
      have hy0 : mapBaseChange ℂ Q (ResidueField Q) (y - ∑ i, c i • w i.succ.succ) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum, sub_eq_zero]
        conv_lhs => rw [← b'.sum_repr (mapBaseChange ℂ Q (ResidueField Q) y)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hwz, hmb, hz, hb']
      obtain ⟨c', hc'⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ Q (ResidueField Q) hs _).mp hy0
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c'
      have hx' := hx
      rw [hker, ← hspan, Ideal.mem_span_pair] at hx'
      obtain ⟨a, b, rfl⟩ := hx'
      rw [hkc, hpair] at hc'
      have hy : y = (algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0)) + ∑ i, c i • w i.succ.succ := by
        rw [hc', sub_add_cancel]
      rw [hy]
      refine add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.succ 0, rfl⟩)))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

    have hli : LinearIndependent (ResidueField Q) w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hg
      have hφ := congrArg (mapBaseChange ℂ Q (ResidueField Q)) hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul, map_zero] at hφ
      rw [hw0, hmb, ht0, Derivation.map_zero, smul_zero, zero_add] at hφ
      rw [hw1, hmb, hu0, Derivation.map_zero, smul_zero, zero_add] at hφ
      simp only [hwz, hmb, hz, ← hb'] at hφ
      have hrest : ∀ i : Fin (Nat.card s), g i.succ.succ = 0 :=
        Fintype.linearIndependent_iff.mp b'.linearIndependent (fun i => g i.succ.succ) hφ
      simp only [hrest, zero_smul, Finset.sum_const_zero, add_zero] at hg
      obtain ⟨a, ha⟩ := hs (g 0)
      obtain ⟨b, hb⟩ := hs (g (Fin.succ 0))
      have hg' : (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) = 0 := by
        rw [hpair, ha, hb]
        exact hg
      have hmem : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) := by
        rw [hker]
        exact add_mem (Ideal.mul_mem_left _ _ htm) (Ideal.mul_mem_left _ _ hum)
      have hsq : a * t + b * u ∈ maximalIdeal Q ^ 2 := by
        have h1 : (RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨_, hmem⟩ = 0 :=
          hinj (by rw [hkc, map_zero]; exact hg')
        have h2 : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) ^ 2 :=
          (Ideal.toCotangent_eq_zero _ _).mp h1
        rwa [hker] at h2
      have ham : a ∈ maximalIdeal Q := mem_maximalIdeal_of_mul_add_mul_mem_sq hspan hdim hsq
      have hbm : b ∈ maximalIdeal Q := by
        refine mem_maximalIdeal_of_mul_add_mul_mem_sq (t := u) (u := t) (a := b) (b := a)
          (by rw [Set.pair_comm]; exact hspan) hdim ?_
        rw [add_comm]; exact hsq
      have h0 : g 0 = 0 := by rw [← ha]; exact (residue_eq_zero_iff a).mpr ham
      have h1 : g (Fin.succ 0) = 0 := by rw [← hb]; exact (residue_eq_zero_iff b).mpr hbm
      intro i
      refine Fin.cases h0 (fun j => Fin.cases h1 (fun k => hrest k) j) i
    haveI : Module.FinitePresentation Q Ω[Q⁄ℂ] := Module.finitePresentation_of_finite Q _
    obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := Q) (fun i => D ℂ Q (v i)) hli hsp
      (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal Q).subtype
        Subtype.val_injective)
    exact isFreeGen_dForm v b hb

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedOfIsEtaleTowerOverNormalLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.EtNormal

theorem isDomain_and_isIntegrallyClosed_of_formallyEtale (A T : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing T] [IsLocalRing T] [Algebra A T]
    [Algebra.FormallyEtale A T] [Algebra.EssFiniteType A T] :
    IsDomain T ∧ IsIntegrallyClosed T := by
  let B := Algebra.EssFiniteType.subalgebra A T
  let P : Ideal B := (IsLocalRing.maximalIdeal T).comap (algebraMap B T)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hM : Algebra.EssFiniteType.submonoid A T = P.primeCompl := by
    ext x
    change IsUnit (algebraMap B T x) ↔ x ∉ P
    simp [P, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI hloc : IsLocalization.AtPrime T P := by
    have := Algebra.EssFiniteType.isLocalization A T
    rw [hM] at this
    exact this
  haveI : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType).1 inferInstance
  let e : T ≃ₐ[A] Localization.AtPrime P :=
    (IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars A
  haveI : Algebra.FormallySmooth A (Localization.AtPrime P) := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.IsSmoothAt A P := inferInstance
  obtain ⟨f, hfP, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := P)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) P ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) T
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

end GlobalTheory.EtNormal

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T), IsEtTower cK R cL T ι ψ τ → IsIntegrallyClosed T := by
  intro K L _ _ cK cL r R T ι ψ τ h
  haveI := h.top.isLocalRing
  haveI := h.normal
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra A T := φ.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  haveI : Algebra.FormallyEtale A T := h.etale
  haveI : Algebra.EssFiniteType ℂ T := h.top.essFiniteType
  haveI : IsScalarTower ℂ A T := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change cT a = φ (MvPolynomial.C (c0 a))
    have e : φ (MvPolynomial.C (c0 a)) = ι (c0 a) := MvPolynomial.eval₂Hom_C _ _ _
    rw [e]
    exact Subtype.ext (h.const a).symm
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_comp ℂ A T
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_mvPolynomial_fin R r
  exact (GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale A T).2

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocModelLocRingAndExistsTrBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem preimage_fromSpecStalk_eq_constFn {k : Type} [Field k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) :
    (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom = Cartier.constFn p := by
  ext a
  have n := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k)).inv a))
    (Scheme.ΓSpecIso_naturality (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)))
  simp only [Spec.map_preimage, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at n
  rw [← n]
  have hid : (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ≤ ⊤))
      = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rw [hid, CommRingCat.id_apply, Iso.inv_hom_id_apply]
  have e2 : Scheme.Hom.appLE p ⊤ ⊤ (by simp) = Scheme.Hom.appTop p := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  simp only [Cartier.constFn, Cartier.fnOf, algX, e2, RingHom.comp_apply]

theorem isLocModel_locRing_and_exists_trBasis {k : Type} [Field k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ) (x : X) (hn : topologicalKrullDim X = n) :
    IsLocModel (Cartier.constFn p) (locRing x) ∧
      ∃ z : Fin n → X.functionField, TrBasis (Cartier.constFn p) z := by
  refine ⟨isLocModel_locRing x, ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : (U : Set X).Nonempty := ⟨x, hxU⟩
  obtain ⟨d, h₁, h₂⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen k p hU hne
  have e₁ := GlobalTheory.OpenDim.topologicalKrullDim_open k p U hne
  have e₂ : topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have hdn : d = n := by
    have : ((d : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by rw [← h₁, ← e₂, e₁, hn]
    exact_mod_cast this
  subst hdn
  rw [preimage_fromSpecStalk_eq_constFn] at h₂
  letI := (Cartier.constFn p).toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k X.functionField
  have hc : Cardinal.mk s = (d : Cardinal) := hs.cardinalMk_eq_trdeg.trans h₂
  have hfin : Fintype s := (Cardinal.lt_aleph0_iff_fintype.mp (hc ▸ Cardinal.natCast_lt_aleph0 (n := d))).some
  have hcard : Fintype.card s = d := by
    have := hc; rw [Cardinal.mk_fintype] at this; exact_mod_cast this
  let e : Fin d ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (e i : X.functionField), ?_⟩
  unfold TrBasis
  exact hs.comp_equiv e

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

theorem exists_mul_mem_tens (E : Place (algebraMap ℂ K)) (w : K ⊗[ℂ] κ') :
    ∃ d ∈ E.ring, d ≠ 0 ∧ (d ⊗ₜ[ℂ] (1 : κ')) * w ∈ tens (κ' := κ') (placeAlg E) := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, one_ne_zero, by simpa using zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := E.ring) x
    have hb0 : (b : K) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
    have he : x * (b : K) = (a : K) := by
      rw [← e]
      exact div_mul_cancel₀ _ hb0
    refine ⟨b, b.2, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, he]
    exact tmul_mem a.2 y
  | add u v hu hv =>
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := hu
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := hv
    refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, mul_ne_zero hd₁0 hd₂0, ?_⟩
    have e : ((d₁ * d₂) ⊗ₜ[ℂ] (1 : κ')) * (u + v) =
        (d₂ ⊗ₜ[ℂ] (1 : κ')) * ((d₁ ⊗ₜ[ℂ] (1 : κ')) * u) +
          (d₁ ⊗ₜ[ℂ] (1 : κ')) * ((d₂ ⊗ₜ[ℂ] (1 : κ')) * v) := by
      rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁, mul_add]
    rw [e]
    exact add_mem (mul_mem (tmul_mem hd₂ 1) h₁) (mul_mem (tmul_mem hd₁ 1) h₂)

theorem isLocModel_locAt : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ E 𝔭 _ hO
  obtain ⟨O', hO'⟩ := hO
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ L
  have hc : ∀ a : ℂ, algebraMap ℂ L a ∈ locAt (L := L) 𝔭 := fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L]
    exact (toQ (L := L) 𝔭 (algebraMap ℂ (tens (κ' := κ') (placeAlg E)) a)).2
  refine
    { const_mem := hc
      isLocalRing := isLocalRing_locAt 𝔭 hinj
      essFiniteType := ?_
      frac := ?_ }
  · have e : (algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc =
        (toQ (L := L) 𝔭).comp (algebraMap ℂ (tens (κ' := κ') (placeAlg E))) := by
      ext a
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, coe_toQ]
      exact IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L a
    rw [e]

    letI : Algebra ℂ O' := ((algebraMap ℂ κ').codRestrict O' hO'.const_mem).toAlgebra
    haveI : IsScalarTower ℂ O' κ' := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.EssFiniteType ℂ O' := hO'.essFiniteType
    haveI : IsFractionRing O' κ' := IsFractionRing.of_field O' κ' fun f => by
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hO'.frac f
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩
    haveI : Algebra.EssFiniteType O' κ' :=
      Algebra.EssFiniteType.of_isLocalization κ' (nonZeroDivisors O')
    haveI : Algebra.EssFiniteType ℂ κ' := Algebra.EssFiniteType.comp ℂ O' κ'

    haveI : Algebra.EssFiniteType ℂ (placeAlg E) := by
      let φ : E.ring →+* placeAlg E :=
        { toFun := fun x => ⟨x.1, x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hφ : φ.FiniteType := RingHom.FiniteType.of_surjective φ fun y => ⟨⟨y.1, y.2⟩, rfl⟩
      have e : φ.comp ((algebraMap ℂ K).codRestrict E.ring E.const_mem) =
          algebraMap ℂ (placeAlg E) := RingHom.ext fun _ => rfl
      have h := RingHom.EssFiniteType.comp E.essFiniteType hφ.essFiniteType
      rw [e] at h
      exact RingHom.essFiniteType_algebraMap.1 h
    haveI : Algebra.EssFiniteType (placeAlg E) (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.baseChange ℂ κ' (placeAlg E)
    haveI : Algebra.EssFiniteType ℂ (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.comp ℂ (placeAlg E) (placeAlg E ⊗[ℂ] κ')
    haveI : Algebra.EssFiniteType ℂ (tens (κ' := κ') (placeAlg E)) :=
      Algebra.EssFiniteType.of_surjective (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom
        (tensEquiv (κ' := κ') (placeAlg E)).surjective
    have h1 : (algebraMap ℂ (tens (κ' := κ') (placeAlg E))).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 inferInstance

    letI : Algebra (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) := (toQ (L := L) 𝔭).toAlgebra
    haveI : IsLocalization 𝔭.primeCompl (locAt (L := L) 𝔭) :=
      { map_units := fun s => isUnit_toQ 𝔭 hinj s.2
        surj := fun x => by
          obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
          exact ⟨(a, ⟨s, hs⟩), hx⟩
        exists_of_eq := fun {x y} h => ⟨1, by
          simp only [OneMemClass.coe_one, one_mul]
          exact Subtype.ext (hinj (congrArg Subtype.val h))⟩ }
    haveI : Algebra.EssFiniteType (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) :=
      Algebra.EssFiniteType.of_isLocalization (locAt (L := L) 𝔭) 𝔭.primeCompl
    have h2 : (toQ (L := L) 𝔭).EssFiniteType := RingHom.essFiniteType_algebraMap.2 this
    exact RingHom.EssFiniteType.comp h1 h2
  · intro f
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') f
    have hv0 : algebraMap (K ⊗[ℂ] κ') L v ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := exists_mul_mem_tens (κ' := κ') E u
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := exists_mul_mem_tens (κ' := κ') E v
    set D : K ⊗[ℂ] κ' := (d₁ * d₂) ⊗ₜ[ℂ] (1 : κ') with hD
    have hD1 : D = (d₂ ⊗ₜ[ℂ] (1 : κ')) * (d₁ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁]
    have hD2 : D = (d₁ ⊗ₜ[ℂ] (1 : κ')) * (d₂ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hu : D * u ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD1, mul_assoc]; exact mul_mem (tmul_mem hd₂ 1) h₁
    have hv' : D * v ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD2, mul_assoc]; exact mul_mem (tmul_mem hd₁ 1) h₂
    have hDu : IsUnit D := by
      refine IsUnit.of_mul_eq_one ((d₁ * d₂)⁻¹ ⊗ₜ[ℂ] (1 : κ')) ?_
      rw [hD, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        mul_inv_cancel₀ (mul_ne_zero hd₁0 hd₂0)]
      rfl
    have hD0 : algebraMap (K ⊗[ℂ] κ') L D ≠ 0 := (hDu.map _).ne_zero
    refine ⟨_, (toQ (L := L) 𝔭 ⟨D * u, hu⟩).2, _, (toQ (L := L) 𝔭 ⟨D * v, hv'⟩).2, ?_, ?_⟩
    · show algebraMap (K ⊗[ℂ] κ') L (D * v) ≠ 0
      rw [map_mul]; exact mul_ne_zero hD0 hv0
    · show _ * algebraMap (K ⊗[ℂ] κ') L (D * v) = algebraMap (K ⊗[ℂ] κ') L (D * u)
      rw [map_mul, map_mul]
      field_simp

end GlobalTheory.GraphLocal
end
end

