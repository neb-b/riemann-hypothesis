module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import GroundTheory.LocalFields.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealFamilyEqTopOfDisjoint
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent


open MvPolynomial in
theorem normIdeal_top (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
    [FiniteDimensional K L] [CommRing B] [Algebra B L] :
    GlobalTheory.NormSheaf.normIdeal A K L B (⊤ : Ideal B) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  refine ⟨1, fun _ => 1, fun _ => Submodule.mem_top, Finsupp.single 0 (Module.finrank K L), ?_⟩
  have hform : GlobalTheory.NormSheaf.normForm K L (fun _ : Fin 1 => algebraMap B L 1) =
      X 0 ^ Module.finrank K L := by
    unfold GlobalTheory.NormSheaf.normForm
    simp [Fin.sum_univ_one, map_one, Matrix.det_smul]
  rw [hform, coeff_X_pow]
  simp

theorem ideal_eq_top_of_forall_not_mem {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ x ∈ I.support, x ∉ V.1) : I.ideal V = ⊤ := by
  have hV : IsAffineOpen V.1 := V.2
  have hempty : X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) ∩ V.1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxV
    exact h x ((Scheme.IdealSheafData.mem_support_iff_of_mem hxV).2 hx) hxV
  rw [← hV.fromSpec_image_zeroLocus] at hempty
  have h0 : PrimeSpectrum.zeroLocus (I.ideal V : Set Γ(X, V.1)) = ∅ := Set.image_eq_empty.mp hempty
  rw [PrimeSpectrum.zeroLocus_empty_iff_eq_top] at h0
  exact h0

theorem famIdeal_eq_top_of_disjoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  intro Y Z π _ _ hK hfd I U hU
  unfold famIdeal
  split_ifs with h
  · have hV : I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ = ⊤ :=
      ideal_eq_top_of_forall_not_mem I _ (fun y hy hyV => hU y hy hyV)
    simp only [hV]
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    exact normIdeal_top _ _ _ _
  · rfl

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFiltrationComplete
section
open Polynomial Matrix Formalism.UG

noncomputable section

open Filter Topology

namespace GlobalTheory.NormEq.Cmpl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_pow_lt {w γ : WithZero (Multiplicative ℤ)}
    (hw : w = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (hγ : γ ≠ 0) :
    ∃ N : ℕ, w ^ N < γ := by
  subst hw
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hγ
  refine ⟨(-Multiplicative.toAdd g).toNat + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe, ← ofAdd_toAdd g, ← ofAdd_nsmul, Multiplicative.ofAdd_lt]
  simp only [toAdd_ofAdd, smul_neg, nsmul_eq_mul, mul_one]
  omega

theorem ball_mem_nhds_of_ne {x c : L} (hc : c ≠ 0) : {y | Valued.v (y - x) < Valued.v c} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c ≠ 0 := by simp [hc]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

theorem exists_lim_of_cauchy [CompleteSpace L] {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (s : ℕ → L) (hsO : ∀ n, Valued.v (s n) ≤ 1)
    (hs : ∀ N : ℕ, ∃ M, ∀ m ≥ M, ∀ n ≥ M, Valued.v (s n - s m) ≤ Valued.v ϖ ^ N) :
    ∃ ℓ, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) ≤ Valued.v ϖ ^ N := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hcs : CauchySeq s := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) γ.1
    have hc' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c = γ.1 := hc
    have hc0 : Valued.v c ≠ 0 := by
      intro h0
      rw [(Valued.v).zero_iff.mp h0, map_zero] at hc'
      exact γ.ne_zero hc'.symm
    obtain ⟨N, hN⟩ := exists_pow_lt hϖ hc0
    obtain ⟨M, hM⟩ := hs N
    refine ⟨M, fun m hm n hn => ?_⟩
    change (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict (s n - s m) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact lt_of_le_of_lt (hM m hm n hn) hN
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcs
  have hev : ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) < Valued.v ϖ ^ N := fun N => by
    have := hℓ (ball_mem_nhds_of_ne (x := ℓ) (pow_ne_zero N hϖ0))
    simpa [map_pow] using this
  refine ⟨ℓ, ?_, fun N => (hev N).mono fun n hn => hn.le⟩
  obtain ⟨n, hn⟩ := (hev 0).exists
  rw [pow_zero] at hn
  have e : ℓ = s n - (s n - ℓ) := by ring
  rw [e]
  exact (Valued.v.map_sub _ _).trans (max_le (hsO n) hn.le)

variable {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1))

theorem mem_piPow_iff {N : ℕ} {a : GlobalTheory.UTr.Alg P} :
    a ∈ piPow h P N ↔ ∀ i, Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : intL L) : L) ≤ Valued.v ϖ ^ N := by
  with_unfolding_all
    unfold GlobalTheory.UTr.Alg at *
    have hϖ0 : ϖ ≠ 0 := fun h0 => by
      have := h.2.2.2.1; rw [h0, map_zero] at this; exact WithZero.zero_ne_coe this
    constructor
    · intro ha i
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      set_option backward.isDefEq.respectTransparency false in
        rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Subring.coe_mul,
        SubmonoidClass.coe_pow, coe_piO, map_mul, map_pow]
      calc _ ≤ Valued.v ϖ ^ N * 1 := mul_le_mul' le_rfl (((GlobalTheory.UTr.powBasis P).repr c i).2)
        _ = _ := mul_one _
    · intro ha
      have hϖN : ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ0
      let d : Fin P.1.natDegree → intL L := fun i => ⟨((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N, by
        change Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N) ≤ 1
        rw [map_div₀, map_pow]
        exact (div_le_one₀ (zero_lt_iff.mpr (pow_ne_zero _ ((Valued.v).ne_zero_iff.mpr hϖ0)))).mpr (ha i)⟩
      refine Ideal.mem_span_singleton'.mpr ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm d, ?_⟩
      refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
      have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm d) i = d i := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      set_option backward.isDefEq.respectTransparency false in
        rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hd]
      apply Subtype.ext
      rw [Subring.coe_mul, SubmonoidClass.coe_pow, coe_piO]
      exact mul_div_cancel₀ _ hϖN

theorem eq_zero_of_forall_mem_piPow {z : GlobalTheory.UTr.Alg P} (hz : ∀ N, z ∈ piPow h P N) : z = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  by_contra hne
  have hne' : (((GlobalTheory.UTr.powBasis P).repr z i : intL L) : L) ≠ 0 := fun h0 => hne (Subtype.ext h0)
  obtain ⟨N, hN⟩ := exists_pow_lt h.2.2.2.1 ((Valued.v).ne_zero_iff.mpr hne')
  exact absurd ((mem_piPow_iff h P).mp (hz N) i) (not_le.mpr hN)

theorem exists_lim_alg [CompleteSpace L] (a : ℕ → GlobalTheory.UTr.Alg P)
    (ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, a n - a m ∈ piPow h P N) :
    ∃ y, ∀ N, ∀ᶠ n in atTop, a n - y ∈ piPow h P N := by
  have hco : ∀ i, ∃ ℓ : L, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop,
      Valued.v ((((GlobalTheory.UTr.powBasis P).repr (a n) i : intL L) : L) - ℓ) ≤ Valued.v ϖ ^ N := by
    intro i
    refine exists_lim_of_cauchy h.2.2.2.1 _ (fun n => ((GlobalTheory.UTr.powBasis P).repr (a n) i).2) fun N => ?_
    obtain ⟨M, hM⟩ := ha N
    refine ⟨M, fun m hm n hn => ?_⟩
    have := (mem_piPow_iff h P).mp (hM m hm n hn) i
    rwa [map_sub, Finsupp.sub_apply, AddSubgroupClass.coe_sub] at this
  choose ℓ hℓO hℓ using hco
  refine ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩), fun N => ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => hℓ i N)] with n hn
  rw [mem_piPow_iff]
  intro i
  have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩)) i =
      ⟨ℓ i, hℓO i⟩ := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [map_sub, Finsupp.sub_apply, hd, AddSubgroupClass.coe_sub]
  exact hn i

end GlobalTheory.NormEq.Cmpl

namespace GlobalTheory.NormEq


open Cmpl in
theorem filtrationComplete_filt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)),
    GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  with_unfolding_all
    intro L _ _ _ σ ϖ q h P x hx
    have ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, (((x n).val : (AdjoinRoot P.1)) - (x m).val) ∈ piPow h P N := by
      intro N
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have h1 : ((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1 ∈ piPow h P N := hM m hm n hn
      have e : ((x n).val : (AdjoinRoot P.1)) - x m = ((x m).val : (AdjoinRoot P.1)) * (((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1) := by
        rw [div_eq_mul_inv, Units.val_mul]
        linear_combination (-((x n).val : (AdjoinRoot P.1))) * (x m).mul_inv
      rw [e]; exact Ideal.mul_mem_left _ _ h1
    have hb : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M,
        (((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - ((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) ∈ piPow h P N := by
      intro N
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have h1 : ((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1 ∈ piPow h P N := hM m hm n hn
      have e : (((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - ((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) =
          -(((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) * (((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1) := by
        rw [div_eq_mul_inv, Units.val_mul]
        linear_combination (((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) * (x n).inv_mul
      rw [e]; exact Ideal.mul_mem_left _ _ h1
    obtain ⟨y, hy⟩ := exists_lim_alg h P _ ha
    obtain ⟨y', hy'⟩ := exists_lim_alg h P _ hb
    unfold GlobalTheory.UTr.Alg at y y' hy hy'
    have hyy : y * y' = 1 := by
      rw [← sub_eq_zero]
      refine eq_zero_of_forall_mem_piPow h P fun N => ?_
      obtain ⟨n, hn1, hn2⟩ := ((hy N).and (hy' N)).exists
      have e : y * y' - 1 = -(((x n).val : (AdjoinRoot P.1)) - y) * y' -
          ((x n).val : (AdjoinRoot P.1)) * ((((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - y') := by
        linear_combination (x n).mul_inv
      rw [e]
      exact (piPow h P N).sub_mem ((piPow h P N).mul_mem_right _ ((piPow h P N).neg_mem hn1))
        ((piPow h P N).mul_mem_left _ hn2)
    refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, fun N => ?_⟩
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hy N)
    refine ⟨M, fun n hn => ?_⟩
    rw [mem_filt, div_eq_mul_inv, Units.val_mul, Units.inv_mk, Units.val_mk]
    have e : ((x n).val : (AdjoinRoot P.1)) * y' - 1 = (((x n).val : (AdjoinRoot P.1)) - y) * y' := by
      linear_combination hyy
    rw [e]
    exact (piPow h P N).mul_mem_right _ (hM n hn)

end GlobalTheory.NormEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFormCoefficientIdealMapLocalizationAway
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheaf

theorem normForm_coeff_smul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (y : Fin m → L) (c : K) (s : Fin m →₀ ℕ) :
    (normForm K L (fun i => algebraMap K L c * y i)).coeff s =
      c ^ Module.finrank K L * (normForm K L y).coeff s := by
  have hM : ∀ i, (Algebra.leftMulMatrix (Module.finBasis K L) (algebraMap K L c * y i)).map
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) =
      (MvPolynomial.C c : MvPolynomial (Fin m) K) • (Algebra.leftMulMatrix (Module.finBasis K L) (y i)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) := by
    intro i
    rw [← Algebra.smul_def, map_smul]
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, MvPolynomial.C_mul]
  have : normForm K L (fun i => algebraMap K L c * y i) =
      MvPolynomial.C (c ^ Module.finrank K L) * normForm K L y := by
    unfold normForm
    simp_rw [hM, smul_comm (MvPolynomial.X _ : MvPolynomial (Fin m) K) (MvPolynomial.C c), ← Finset.smul_sum,
      Matrix.det_smul, Fintype.card_fin, map_pow]
  rw [this, MvPolynomial.coeff_C_mul]

end GlobalTheory.NormSheaf

namespace GlobalTheory.NormSheaf

theorem normIdeal_map_away : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  intro A K L B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ _ h1 h2 h3 hinj hcoef J
  have e1 : ∀ x : A, algebraMap A' K (algebraMap A A' x) = algebraMap A K x := fun x => by
    simpa using RingHom.congr_fun h1 x
  have e2 : ∀ x : B, algebraMap B' L (algebraMap B B' x) = algebraMap B L x := fun x => by
    simpa using RingHom.congr_fun h2 x
  have e3 : ∀ x : A, algebraMap K L (algebraMap A K x) = algebraMap B L (algebraMap A B x) := fun x => by
    simpa using RingHom.congr_fun h3 x
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    unfold normIdeal
    rw [Ideal.span_le]
    rintro a ⟨m, g, hg, s, hs⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    refine ⟨m, fun i => algebraMap B B' (g i), fun i => Ideal.mem_map_of_mem _ (hg i), s, ?_⟩
    rw [e1, hs]
    simp only [e2]
  · unfold normIdeal
    rw [Ideal.span_le]
    rintro a' ⟨m, g', hg', s, hs⟩
    set b := algebraMap A B f with hb
    have hloc : ∀ i, ∃ (j : B) (n : ℕ), j ∈ J ∧ g' i * algebraMap B B' (b ^ n) = algebraMap B B' j := by
      intro i
      obtain ⟨⟨⟨j, hj⟩, ⟨_, n, rfl⟩⟩, h⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b) B').1 (hg' i)
      exact ⟨j, n, hj, h⟩
    choose j n hj hn using hloc
    set N := ∑ i, n i
    have hN : ∀ i, g' i * algebraMap B B' (b ^ N) = algebraMap B B' (j i * b ^ (N - n i)) := by
      intro i
      have hle : n i ≤ N := Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) (Finset.mem_univ i)
      rw [← Nat.add_sub_cancel' hle, pow_add, map_mul, ← mul_assoc, hn i, Nat.add_sub_cancel_left, map_mul]
    have hjJ : ∀ i, j i * b ^ (N - n i) ∈ J := fun i => J.mul_mem_right _ (hj i)
    set c := algebraMap A K f
    have himg : ∀ i, algebraMap B L (j i * b ^ (N - n i)) =
        algebraMap K L (c ^ N) * algebraMap B' L (g' i) := by
      intro i
      rw [← e2, ← hN i, map_mul, e2, map_pow, map_pow, hb, ← e3, mul_comm]
    obtain ⟨a, ha⟩ := hcoef (fun i => j i * b ^ (N - n i)) s
    have hcoef' : algebraMap A K a = (c ^ N) ^ Module.finrank K L * algebraMap A' K a' := by
      rw [ha, hs]
      simp only [himg]
      exact normForm_coeff_smul K L _ _ s
    have hmem : a ∈ normIdeal A K L B J := Ideal.subset_span ⟨m, _, hjJ, s, ha⟩
    have key : algebraMap A A' a = algebraMap A A' (f ^ (N * Module.finrank K L)) * a' := by
      apply hinj
      rw [map_mul, e1, e1, hcoef', map_pow, pow_mul]
    have hu : IsUnit (algebraMap A A' (f ^ (N * Module.finrank K L))) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow _
    rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ hu, ← key]
    exact Ideal.mem_map_of_mem _ hmem

end GlobalTheory.NormSheaf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivProdCoordLeLeibniz
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.LeibnizProd

theorem countPerms_le_factorial {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : Sym ι n) :
    ((p : Multiset ι).countPerms : ℝ) ≤ (n.factorial : ℝ) := by
  have h1 : (p : Multiset ι).countPerms =
      Nat.multinomial Finset.univ (fun j => (p : Multiset ι).count j) := by
    rw [Multiset.countPerms, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
    rfl
  have h2 : ∑ j, (p : Multiset ι).count j = n := by
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    exact p.2
  have h3 := Nat.multinomial_spec Finset.univ (fun j => (p : Multiset ι).count j)
  rw [h2] at h3
  have h4 : (p : Multiset ι).countPerms ≤ n.factorial := by
    rw [h1]
    exact Nat.le_of_dvd (Nat.factorial_pos n) (Dvd.intro_left _ h3)
  exact_mod_cast h4

theorem sum_sym_le {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (a : ι → ℕ → ℝ)
    (ha : ∀ i k, 0 ≤ a i k) :
    ∑ p ∈ (Finset.univ : Finset ι).sym n, ∏ j, a j ((p : Multiset ι).count j) ≤
      ∏ j, ∑ k ∈ Finset.range (n + 1), a j k := by
  rw [← Finset.sum_prod_piFinset]
  let φ : Sym ι n → (ι → ℕ) := fun p j => (p : Multiset ι).count j
  have hinj : Set.InjOn φ ↑((Finset.univ : Finset ι).sym n) := by
    intro p _ q _ h
    apply Sym.coe_injective
    ext j
    exact congrFun h j
  have hs := Finset.sum_image (f := fun c : ι → ℕ => ∏ j, a j (c j)) hinj
  rw [← hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hc
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc (p : Multiset ι).count j ≤ Multiset.card (p : Multiset ι) := Multiset.count_le_card _ _
      _ = n := p.2
  · intro c _ _
    exact Finset.prod_nonneg fun j _ => ha j _

theorem norm_iteratedFDeriv_comp_apply_le {ι : Type} [Fintype ι] (g : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (j : ι) (z : ι → ℂ) (hz : z j ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : ι → ℂ => g (w j)) z‖ ≤ ‖iteratedFDeriv ℝ k g (z j)‖ := by
  set P : (ι → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) j
  have hPo : IsOpen (P ⁻¹' U) := hU.preimage P.continuous
  have hzP : P z ∈ U := hz
  have hzP' : z ∈ P ⁻¹' U := hz
  have e := P.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hPo.uniqueDiffOn hzP (i := k)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hPo hzP', iteratedFDerivWithin_of_isOpen k hU hzP] at e
  have hfun : (fun w : ι → ℂ => g (w j)) = g ∘ P := rfl
  rw [hfun, e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun w => by simpa [P] using norm_le_pi_norm w j)
  calc ‖iteratedFDeriv ℝ k g (P z)‖ * ∏ _i : Fin k, ‖P‖ ≤ ‖iteratedFDeriv ℝ k g (P z)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hP)
    _ = ‖iteratedFDeriv ℝ k g (z j)‖ := by rw [mul_one]; rfl

theorem norm_iteratedFDeriv_prod_apply_le : ∀ (ι : Type) [Fintype ι] (g : ι → ℂ → ℂ) (U : ι → Set ℂ), (∀ i, IsOpen (U i)) →
    (∀ i, ContDiffOn ℝ ∞ (g i) (U i)) → ∀ z : ι → ℂ, (∀ i, z i ∈ U i) → ∀ n : ℕ,
      ‖iteratedFDeriv ℝ n (fun z : ι → ℂ => ∏ i, g i (z i)) z‖ ≤
        n.factorial * ∏ i, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g i) (z i)‖ := by
  intro ι _ g U hU hg z hz n
  classical
  set V : Set (ι → ℂ) := ⋂ i, (fun w : ι → ℂ => w i) ⁻¹' U i with hVdef
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => (hU i).preimage (continuous_apply i)
  have hzV : z ∈ V := Set.mem_iInter.2 hz
  have hf : ∀ i ∈ (Finset.univ : Finset ι), ContDiffOn ℝ ∞ (fun w : ι → ℂ => g i (w i)) V := by
    intro i _
    exact (hg i).comp (contDiff_apply ℝ (fun _ => ℂ) i).contDiffOn (fun w hw => Set.mem_iInter.1 hw i)
  have key := norm_iteratedFDerivWithin_prod_le (u := Finset.univ) hf hV.uniqueDiffOn hzV (n := n)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hV hzV] at key
  refine key.trans ?_
  calc _ ≤ ∑ p ∈ (Finset.univ : Finset ι).sym n, (n.factorial : ℝ) *
        ∏ j, ‖iteratedFDeriv ℝ ((p : Multiset ι).count j) (g j) (z j)‖ := by
        gcongr with p hp j
        · exact_mod_cast countPerms_le_factorial p
        · rw [iteratedFDerivWithin_of_isOpen _ hV hzV]
          exact norm_iteratedFDeriv_comp_apply_le (g j) (U j) (hU j) (hg j) j z (hz j) _
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        gcongr
        exact sum_sym_le n (fun j k => ‖iteratedFDeriv ℝ k (g j) (z j)‖) (fun _ _ => norm_nonneg _)

end GlobalTheory.LeibnizProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationMulEqAevalRootStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_eq_aeval_root_normalisation : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (φ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π))
    (b : integralClosure D (TensorProduct S D L)),
    ∃ (f : Polynomial (integralClosure S L)) (s : S), s ≠ 0 ∧
      algebraMap S (integralClosure D (TensorProduct S D L)) s * b =
        Polynomial.aeval (algebraMap D (integralClosure D (TensorProduct S D L))
          (φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)))) f := by
  first | (exact @GlobalTheory.normalisation_mul_eq_aeval_root) | (exact GlobalTheory.normalisation_mul_eq_aeval_root) | (intros; apply GlobalTheory.normalisation_mul_eq_aeval_root  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_pair_lift_to_prime_power_field : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k → Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧ ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  first | (exact @GlobalTheory.Shin.reg_norm_frob) | (exact GlobalTheory.Shin.reg_norm_frob) | (intros; apply GlobalTheory.Shin.reg_norm_frob  <;> assumption)
end

