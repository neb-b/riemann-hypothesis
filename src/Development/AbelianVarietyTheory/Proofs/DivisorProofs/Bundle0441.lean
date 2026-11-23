module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeGeneratorTopForm
section
open GlobalTheory GlobalTheory.TopForm

namespace GlobalTheory

open KaehlerDifferential IsLocalRing Module

theorem isFreeGen_dForm_uniformiser_cons : ∀ (k V : Type) [Field k] [CharZero k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (α : k →+* V) (n : ℕ) (t : V) (w : Fin n → V), α.EssFiniteType →
    Irreducible t → Nonempty (Module.Basis (Fin (n + 1)) V (Omega α)) →
    (∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ α w P)) →
    IsFreeGen V (dForm α (Fin.cons t w : Fin (n + 1) → V)) := by
  intro k V _ _ _ _ _ α n t w hft ht hb₀ hw
  obtain ⟨b₀⟩ := hb₀
  letI := α.toAlgebra
  haveI : Algebra.EssFiniteType k V := hft
  haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V
  let κ := ResidueField V
  let wb : Fin n → κ := fun i => algebraMap V κ (w i)

  have hai : AlgebraicIndependent k wb := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    have hu := hw P hne
    have e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ α w P) := by
      rw [show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e] at hP
    exact (residue_ne_zero_iff_isUnit _).mpr hu hP

  have hdli : LinearIndependent κ fun i => D k κ (wb i) := by
    have hs : AlgebraicIndepOn k id (Set.range wb) := by
      exact (algebraicIndependent_subtype_range hai.injective).mpr hai
    obtain ⟨s, hsub, hs⟩ := exists_isTranscendenceBasis_superset hs
    haveI := hs.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
    let ι : Fin n → s := fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩
    have hι : Function.Injective ι := fun i j h => hai.injective (congrArg Subtype.val h)
    have := b.linearIndependent.comp ι hι
    convert this using 1
    funext i
    simp [ι, hb]
  have ht₀ : algebraMap V κ t = 0 := (residue_eq_zero_iff t).mpr (by
    rw [ht.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self t)
  let z : Fin (n + 1) → V := Fin.cons t w
  have hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg
    have hφ := congrArg (mapBaseChange k V κ) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀,
      Derivation.map_zero, smul_zero, zero_add] at hφ
    have hs : ∀ i : Fin n, g i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h (one_tmul_D_ne_zero k ht)
    intro i
    exact Fin.cases h0 hs i
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])
  haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀
  haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀
  haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)
  exact isFreeGen_dForm z b hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocalisationAtElementsTrivSqZeroExtForms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

theorem mOm_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] {α : A →+* B}
    (h : SemiHom (RingHom.id R) α) (e : ∀ a, α a = algebraMap A B a) (j : ℕ) (x : Om R A j) :
    h.mOm j x = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B) x := by
  let L : Om R A j →ₗ[A] Om R B j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply, e]; exact algebraMap_smul B a _ }
  have hL : L = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti]
    apply Subtype.ext
    change h.mDR _ = _
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun i ↦ ?_)
    exact (h.mDR_ι (v i)).trans (congrArg _ (h.oneFormMap_eq_kaehlerDifferential_map e (v i)))
  exact LinearMap.congr_fun hL x

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExtJ

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

theorem surj_keyJ {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
    (y : TrivSqZeroExt (F.obj T') (Om R (F.obj T') j)) (a₀ : F.obj T) (η₀ : Om R (F.obj T) j)
    (k₁ k₂ : ℕ) (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀)
    (hη : mp F l (c.fst ^ k₂) • y.snd = pOm F j l η₀) :
    y * extMapJ F j l c ^ (k₁ + k₂ + 1) = extMapJ F j l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMapJ, fst_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMapJ, fst_extMapJ, snd_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      pOm_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_keyJ {T : C} (c x : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_omjExt (H : Desc.HasLoc F) : Desc.HasLoc (omjExt F j) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := FormExt.isLocalization_of_data F l c.fst h1 h2 h3
  haveI : Algebra.FormallyEtale (F.obj T) (F.obj T') :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c.fst)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R (F.obj T) (F.obj T')) j
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c.fst) (F.obj T') _).2 hb
  have hp : ∀ ω, pOm F j l ω =
      GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')) ω :=
    mOm_eq_exteriorPowerMapOver _ (fun _ ↦ rfl) j
  have hs : ∀ (a : F.obj T) (η : Om R (F.obj T') j), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_omjExt_iff F j l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_omjExt_iff F j u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T'))) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    refine ⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩
    exact surj_keyJ F j l c y a₀ η₀ k₁ k₂ ha hη
  · have e1 : mp F l x.fst = 0 := (fst_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : GlobalTheory.exteriorPowerMapOver (F.obj T') j
        (KaehlerDifferential.map R R (F.obj T) (F.obj T')) x.snd = 0 :=
      (hp _).symm.trans ((snd_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')))
      (x₁ := x.snd) (x₂ := 0) (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_keyJ F j c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.CechDR.FormExtJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDim
section
namespace GlobalTheory.FinTypeIntCatenary

open ReciprocityTheory.CA

theorem isCM_atPrime_of_le {S : Type*} [CommRing S] (𝔓 𝔑 : Ideal S) [𝔓.IsPrime] [𝔑.IsPrime]
    (hle : 𝔓 ≤ 𝔑) (h : IsCM (Localization.AtPrime 𝔑)) : IsCM (Localization.AtPrime 𝔓) := by
  have hdisj : Disjoint (𝔑.primeCompl : Set S) (𝔓 : Set S) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)
  let q : Ideal (Localization.AtPrime 𝔑) := 𝔓.map (algebraMap S (Localization.AtPrime 𝔑))
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔑.primeCompl _ 𝔓 inferInstance hdisj
  have h2 := h.localization_atPrime q
  have hc : q.comap (algebraMap S (Localization.AtPrime 𝔑)) = 𝔓 :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔑.primeCompl _ inferInstance hdisj
  haveI : IsLocalization 𝔓.primeCompl (Localization.AtPrime q) := by
    have h0 : IsLocalization (q.comap (algebraMap S (Localization.AtPrime 𝔑))).primeCompl
        (Localization.AtPrime q) :=
      IsLocalization.isLocalization_atPrime_localization_atPrime (M := 𝔑.primeCompl) q
    have hsub : (q.comap (algebraMap S (Localization.AtPrime 𝔑))).primeCompl = 𝔓.primeCompl :=
      Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hc]
    rw [hsub] at h0
    exact h0
  exact h2.of_ringEquiv (IsLocalization.algEquiv 𝔓.primeCompl (Localization.AtPrime q) (Localization.AtPrime 𝔓)).toRingEquiv

theorem height_comap_mk {S : Type*} [CommRing S] (Q : Ideal S) [Q.IsPrime] (J : Ideal (S ⧸ Q))
    [J.IsPrime] (h : IsCM (Localization.AtPrime (J.comap (Ideal.Quotient.mk Q)))) :
    (J.comap (Ideal.Quotient.mk Q)).height = Q.height + J.height := by
  have hle : Q ≤ J.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, J.zero_mem]
  have := height_eq_add_of_isCM_localization (J.comap (Ideal.Quotient.mk Q)) Q h hle
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this

theorem height_le_of_equidim {S : Type*} [CommRing S] (d : ℕ)
    (hS : ∀ (𝔑 : Ideal S) [𝔑.IsMaximal], IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = d)
    (Q : Ideal S) [Q.IsPrime] (P M : Ideal (S ⧸ Q)) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim ((S ⧸ Q) ⧸ P) := by
  haveI hMt : (M.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨hCM1, hd1⟩ := hS (M.comap (Ideal.Quotient.mk Q))
  have e1 := height_comap_mk Q M hCM1
  obtain ⟨M', hM', hPM'⟩ := Ideal.exists_le_maximal (P.comap (Ideal.Quotient.mk Q))
    (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨hCM2, hd2⟩ := hS M'
  have e2 := height_eq_add_of_isCM_localization M' (P.comap (Ideal.Quotient.mk Q)) hCM2 hPM'
  have e3 := height_comap_mk Q P (isCM_atPrime_of_le _ M' hPM' hCM2)
  have hQM : Q ≤ M.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M.zero_mem]
  have hQP : Q ≤ P.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, P.zero_mem]
  have hQle : Q.height ≤ d := hd1 ▸ Ideal.height_mono hQM
  have hQt : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
  have key : M.height = P.height +
      (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height := by
    have hsum : Q.height + M.height = Q.height + (P.height +
        (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height) := by
      rw [← e1, hd1, ← hd2, e2, e3, add_assoc]
    exact WithTop.add_left_cancel hQt hsum
  haveI : (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPM')
  have hb : ((M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height : WithBot ℕ∞) ≤
      ringKrullDim (S ⧸ P.comap (Ideal.Quotient.mk Q)) := Ideal.height_le_ringKrullDim_of_isPrime
  have hdim : ringKrullDim ((S ⧸ Q) ⧸ (P.comap (Ideal.Quotient.mk Q)).map (Ideal.Quotient.mk Q)) =
      ringKrullDim (S ⧸ P.comap (Ideal.Quotient.mk Q)) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQP)
  rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hdim
  rw [key, hdim]
  push_cast
  exact add_le_add le_rfl hb

theorem isMaximal_comap_C_int (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ)).IsMaximal := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) ℤ ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

theorem isCM_localization_int (p : Ideal ℤ) [p.IsMaximal] :
    IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = 1 := by
  have hp : p ≠ ⊥ := by
    intro h
    have : (⊥ : Ideal ℤ).IsMaximal := h ▸ inferInstance
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr this)
  haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hp _
  have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
  refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, hd⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
  refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact IsSMulRegular.of_ne_zero hϖ.ne_zero

theorem exists_maximal_mvPolynomial_localization (N : ℕ) (p : Ideal ℤ) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) ℤ) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) ℤ)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) ℤ) ∈ J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_under W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap ℤ (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

theorem isCM_and_height_of_isMaximal (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = ((N + 1 : ℕ) : ℕ∞) := by
  haveI := isMaximal_comap_C_int N 𝔑
  obtain ⟨hCM, hdim⟩ := isCM_localization_int (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

theorem height_maximal_le (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (P M : Ideal A) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ A›
  haveI : (RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)).IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) ℤ →+* A)) hf
  haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  have h := height_le_of_equidim (N + 1) (isCM_and_height_of_isMaximal N) _ (P.comap e) (M.comap e)
  rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
  have hdim : ringKrullDim ((MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ⧸
      P.comap e) = ringKrullDim (A ⧸ P) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
      (Ideal.map_comap_of_surjective _ e.surjective P).symm)
  rwa [hdim] at h

end GlobalTheory.FinTypeIntCatenary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherFormsOneCocycleCoboundaryOfRestrict
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExtJ

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

abbrev inrJ {T : C} (x : Om R (F.obj T) j) : (omjExt F j).obj T := TrivSqZeroExt.inr x

theorem inrJ_add {T : C} (x y : Om R (F.obj T) j) : inrJ F j (x + y) = inrJ F j x + inrJ F j y :=
  TrivSqZeroExt.inr_add _ x y

theorem inrJ_sub {T : C} (x y : Om R (F.obj T) j) : inrJ F j (x - y) = inrJ F j x - inrJ F j y :=
  TrivSqZeroExt.inr_sub _ x y

theorem snd_subJ {T : C} (a b : (omjExt F j).obj T) :
    TrivSqZeroExt.snd (a - b) = TrivSqZeroExt.snd a - TrivSqZeroExt.snd b :=
  TrivSqZeroExt.snd_sub a b

theorem oneCocycle_coboundary_of_restrict_coboundary {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (j : ℕ)
    (hinj : Function.Injective (CoefMap.restrict (FormExtJ.omjExt F j) G).pull1)
    (κ : W1 F j) (hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      κ T T'' (φ ≫ ψ) = pOm F j ψ (κ T T' φ) + κ T' T'' ψ)
    (θ' : ∀ t, Om R (F.obj (G.obj t)) j)
    (hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F j (G.map a) (θ' t)) :
    ∃ θ : W0 F j, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F j φ (θ T) := by
  let E := omjExt F j
  let f : Z1 E := ⟨fun T T' φ ↦ inrJ F j (κ T T' φ), fun T T' T'' φ ψ ↦ by
    change inrJ F j (κ T T'' (φ ≫ ψ)) = mp E ψ (inrJ F j (κ T T' φ)) + inrJ F j (κ T' T'' ψ)
    rw [mp_omjExt_inr, hκ φ ψ, inrJ_add]⟩
  have hpull : (CoefMap.restrict E G).pull1 (H1.mk E f) = (CoefMap.restrict E G).pull1 0 := by
    rw [map_zero, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨fun t ↦ inrJ F j (θ' t), ?_⟩
    funext t t' a
    change inrJ F j (θ' t') - mp E (G.map a) (inrJ F j (θ' t)) = inrJ F j (κ _ _ (G.map a))
    rw [mp_omjExt_inr, hθ' a, inrJ_sub]
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 (hinj hpull)
  refine ⟨fun T ↦ (g T).snd, fun T T' φ ↦ ?_⟩
  have e := congrArg TrivSqZeroExt.snd (congrFun (congrFun (congrFun hg T) T') φ)
  rw [amitsur_d0_apply, snd_subJ, snd_mp_omjExt] at e
  exact e.symm

end GlobalTheory.CechDR.FormExtJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafOfLinearMapsFromModuleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule : ∀ (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M], Injective ((homSh J).obj (op M)) := by
  first | (exact @GlobalTheory.EtC.homSh_injective) | (exact GlobalTheory.EtC.homSh_injective) | (intros; apply GlobalTheory.EtC.homSh_injective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSheafProjBundleCochainPresheafEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ), Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  first | (exact @GlobalTheory.EtC.cotPre_isSheaf) | (exact GlobalTheory.EtC.cotPre_isSheaf) | (intros; apply GlobalTheory.EtC.cotPre_isSheaf  <;> assumption)
end

