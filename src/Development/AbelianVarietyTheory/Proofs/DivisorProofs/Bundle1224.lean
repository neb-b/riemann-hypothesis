module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureWeylCellOddUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalConjLastSimpleReflectionCell
section
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

section Diag

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

theorem diag_inv_of_diag (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∀ i j, i ≠ j → (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro i j hij
  have h := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 i j
  rw [Subgroup.coe_inv, h, ht _ _ (fun e => hij (Fin.rev_injective e).symm), map_zero]

theorem diag_mul_mul_diag_apply (s u t : GU σ n)
    (hs : ∀ i j, i ≠ j → ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i j : Fin n) :
    (((s * u * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
        ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
    Finset.sum_eq_single j (fun b _ hb => by rw [ht b j hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single i (fun b _ hb => by rw [hs i b (Ne.symm hb), zero_mul]) (by simp)]

theorem diag_inv_mul_diag (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i : Fin n) :
    (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
  have h := diag_mul_mul_diag_apply t⁻¹ 1 t (diag_inv_of_diag t ht) ht i i
  rw [mul_one, inv_mul_cancel] at h
  simpa using h.symm

end Diag

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_cornerU_conj {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (k : Fin (n / 2))
    (t : GU σ n) (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (u : GU σ n) :
    Valued.v (cornerU k (t⁻¹ * u * t)) =
      WithZero.exp (2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) *
        Valued.v (cornerU k u) := by
  unfold cornerU
  rw [diag_mul_mul_diag_apply _ _ _ (diag_inv_of_diag t ht) ht]
  have h1 := diag_inv_mul_diag t ht (lo k)
  have h2 := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 (lo k) (lo k)
  rw [← Subgroup.coe_inv] at h2
  have h0 : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have h3 : Valued.v ((((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)) =
      WithZero.exp (ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) := by
    rw [eq_inv_of_mul_eq_one_left h1, map_inv₀, GlobalTheory.BorelUMod.v_eq_exp h0, ← WithZero.exp_neg, neg_neg]
  have h4 : Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k).rev (lo k).rev) =
      WithZero.exp (ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) := by
    rw [← h3, h2, hσ]
  rw [map_mul, map_mul, h3, h4, two_mul, WithZero.exp_add, mul_right_comm]

theorem conj_mem_cellU_last [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q)
    {n : ℕ} {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n)
    {y : GU σ n} (hy : y ∈ KU σ n) (hw : IsWeylRep (simpleU k) (y : GL (Fin n) L))
    (t : GU σ n) (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0)
    (u : GU σ n) (hu : u ∈ cellU y) : t⁻¹ * u * t ∈ cellU y := by
  rw [mem_cellU_last_iff L ϖ σ q hU n k hk hn y hy hw] at hu ⊢
  obtain ⟨⟨hb, hd⟩, hz⟩ := hu
  have e := diag_mul_mul_diag_apply t⁻¹ u t (diag_inv_of_diag t ht) ht
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij h => ?_⟩
  · rw [e, hb i j hij, mul_zero, zero_mul]
  · rw [e, hd i, mul_one, diag_inv_mul_diag t ht]
  · rw [e, hz i j hij h, mul_zero, zero_mul]

theorem integral_conj_diag_cellU_last :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) * ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal, ∫⁻ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        ‖(q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)))‖ₑ * ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw _ _ μ _ hμ t ht
  have hsh := (_root_.GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup L ϖ σ q hU n k hk hn y hy hw).1
  have hvol := _root_.GlobalTheory.WeylCell.WeylUnipotentShell.measure_shellU L ϖ σ q hU n k hk hn y hy hw μ hμ
  have hcv := v_cornerU_conj hU.2.1 k t ht
  have hq : (2 : ℕ) ≤ q := hU.2.2.2.2.2.1
  generalize ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)) = o at hcv ⊢
  have hm := conj_mem_cellU_last hU hk hn hy hw t ht
  have hm' := conj_mem_cellU_last hU hk hn hy hw t⁻¹ (diag_inv_of_diag t ht)
  let κ : cellU y ≃* cellU y :=
    { toFun := fun u => ⟨t⁻¹ * u * t, hm u u.2⟩
      invFun := fun u => ⟨t⁻¹⁻¹ * u * t⁻¹, hm' u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hc : Continuous κ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hc' : Continuous κ.symm := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let e : cellU y ≃ᵐ cellU y := (Homeomorph.mk κ.toEquiv hc hc').toMeasurableEquiv
  have he : ∀ u : cellU y, ((e u : cellU y) : GU σ n) = t⁻¹ * u * t := fun u => rfl
  haveI : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ κ hc hc'
  haveI : LocallyCompactSpace (cellU y) :=
    (hsh 0).2.1.locallyCompactSpace_of_mem_nhds_of_group ((hsh 0).1.mem_nhds (hsh 0).2.2.1)
  have hpre : ∀ j : ℤ, e ⁻¹' shellU k y j = shellU k y (j - 2 * o) := by
    intro j
    ext u
    simp only [Set.mem_preimage, shellU, Set.mem_setOf_eq, he, hcv]
    rw [WithZero.exp_sub, le_div_iff₀' (WithZero.exp_pos)]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hnorm : ‖(q : ℂ) ^ (-4 * o)‖ = (q : ℝ) ^ (-4 * o) := by
    rw [norm_zpow, Complex.norm_natCast]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = |o| := ⟨o.natAbs, by simp⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = a - o := ⟨(a - o).toNat, by
    rw [Int.toNat_of_nonneg]; rw [ha]; linarith [le_abs_self o]⟩
  have key : μ.map e = ‖(q : ℂ) ^ (-4 * o)‖ₑ • μ := by
    refine _root_.GlobalTheory.haar_unique_of_sigmaCompact_normalised (cellU y) μ (μ.map e) (fun j : ℕ => shellU k y j)
      (fun j => ⟨(hsh j).2.1, (hsh j).1.measurableSet⟩) ?_ (shellU k y ((2 * a : ℕ) : ℤ)) _ (hsh _).1 (hsh _).2.1
      ⟨1, (hsh _).2.2.1⟩ ?_
    · exact Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ⟨_, mem_shellU_depth k y u⟩
    · rw [e.map_apply, hpre]
      have h2 : ((2 * a : ℕ) : ℤ) - 2 * o = ((2 * b : ℕ) : ℤ) := by push_cast; rw [hb]; ring
      rw [h2, hvol, hvol, ← ofReal_norm_eq_enorm, hnorm, ← ENNReal.ofReal_natCast q,
        ← ENNReal.ofReal_pow (Nat.cast_nonneg q), ← ENNReal.ofReal_pow (Nat.cast_nonneg q),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0]
      congr 1
      have e1 : 2 * a / 2 = a := by omega
      have e2 : 2 * b / 2 = b := by omega
      rw [e1, e2]
      push_cast
      rw [hb]; ring
  refine ⟨fun F => ?_, fun F => ?_⟩
  · have h := integral_map_equiv (μ := μ) e (fun u : cellU y => F (u : GU σ n))
    rw [key, integral_smul_measure, toReal_enorm, hnorm, Complex.real_smul] at h
    simp only [he] at h
    rw [← h]
    push_cast
    rfl
  · have h := lintegral_map_equiv (μ := μ) (fun u : cellU y => F (u : GU σ n)) e
    rw [key, lintegral_smul_measure, smul_eq_mul] at h
    simp only [he] at h
    exact h.symm

end WeylUnipotentShell

end WeylCell

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningLastEven
section
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem chiDeltaU_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n m : ℕ}
    (q : ℕ) (α : Fin m → ℂ) (b c : GU σ n)
    (h : ∀ i, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) :
    chiDeltaU q α b = chiDeltaU q α c := by
  unfold chiDeltaU
  simp only [h]

end GlobalTheory.WeylCell.RankOneUnitary

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem ordL_of_v_eq {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x : L) (z : ℤ)
    (hx : Valued.v x = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) : ordL x = -z := by
  unfold ordL
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have : WithZero.unzero h0 = Multiplicative.ofAdd z := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, hx]
  rw [this]; rfl

end GlobalTheory.WeylCell.RankOneUnitary

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertTensorField

theorem isField_tensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ B hB v w hvw
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  exact GlobalTheory.InertField.isField_of_inert F E hB.cm.2.2.1 v hp

end GlobalTheory.InertTensorField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenTopFormEtaleTowerTranscendenceBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem IsEtTower.eval₂Hom_pderiv_eq_zero {K L : Type} [Field K] [Field L] {cK : ℂ →+* K} {cL : ℂ →+* L} {r : ℕ}
    {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T}
    (h : IsEtTower cK R cL T ι ψ τ) (P : MvPolynomial (Fin r) R) (i : Fin r)
    (hP : MvPolynomial.eval₂Hom ι τ P = 0) :
    MvPolynomial.eval₂Hom ι τ (MvPolynomial.pderiv i P) = 0 := by
  letI : Algebra R T := ι.toAlgebra
  letI : Algebra (MvPolynomial (Fin r) R) T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) T := IsScalarTower.of_algebraMap_eq' (by
    ext a; simp [RingHom.algebraMap_toAlgebra])
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) T := h.etale
  let d : Derivation R (MvPolynomial (Fin r) R) T :=
    (Algebra.linearMap (MvPolynomial (Fin r) R) T).compDer (MvPolynomial.pderiv i)
  let f : Ω[MvPolynomial (Fin r) R⁄R] →ₗ[MvPolynomial (Fin r) R] T := d.liftKaehlerDifferential
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale R (MvPolynomial (Fin r) R) T
  let g : Ω[T⁄R] →ₗ[T] T := hb.lift f
  have key : g (KaehlerDifferential.D R T (algebraMap (MvPolynomial (Fin r) R) T P)) =
      algebraMap (MvPolynomial (Fin r) R) T (MvPolynomial.pderiv i P) := by
    rw [← KaehlerDifferential.map_D R R (MvPolynomial (Fin r) R) T]
    erw [hb.lift_eq]
    simp [f, d]
  have h0 : algebraMap (MvPolynomial (Fin r) R) T P = 0 := hP
  rw [h0, map_zero, map_zero] at key
  exact key.symm

theorem charZero_subring_of_complex {K : Type} [Field K] (cK : ℂ →+* K) (R : Subring K) :
    CharZero R := by
  haveI : CharZero K := charZero_of_injective_ringHom cK.injective
  exact ⟨fun a b h => by
    have := congrArg (fun t : R => (t : K)) h
    simpa using this⟩

theorem IsEtTower.eval₂Hom_injective {K L : Type} [Field K] [Field L] {cK : ℂ →+* K}
    {cL : ℂ →+* L} {r : ℕ} {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R}
    {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ) :
    Function.Injective (MvPolynomial.eval₂Hom ι τ) := by
  haveI := charZero_subring_of_complex cK R
  have hI := _root_.GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable r (RingHom.ker (MvPolynomial.eval₂Hom ι τ))
    (fun P hP i => h.eval₂Hom_pderiv_eq_zero P i hP)
    (fun a ha => by
      rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_C] at ha
      simpa [h.retr] using congrArg ψ ha)
  exact (RingHom.injective_iff_ker_eq_bot _).2 hI

theorem isFreeGen_dForm_tower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L)
    (n r : ℕ) (R : Subring K) (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T)
    (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  IsFreeGen L (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  have hinj := h.eval₂Hom_injective
  letI := cL.toAlgebra
  have hind := GlobalTheory.T.algebraicIndependent_etaleTower_coordinates cK cL n r R T ι ψ τ x h hx hinj
  have halg : Algebra.IsAlgebraic
      (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))) L := by
    refine ⟨fun z => GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring _ _ z ?_ (_root_.GlobalTheory.FieldPair.isAlgebraic_range_eval₂Hom_of_isEtTower cK cL r R T ι ψ τ h hinj z)⟩
    rintro b ⟨a, rfl⟩
    exact GlobalTheory.T.isAlgebraic_mvPolynomialEval_adjoin_etaleTowerCoords cK cL n r R T ι ψ τ x h hx a
  have htr : TrBasis cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨hind, halg⟩
  exact isFreeGen_dForm_of_trBasis cL htr

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptyGenericMemberLinearSystem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory

theorem GenericMember.isIntegral_or_isEmpty_zeroScheme : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → ∀ (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec), ⨆ i, nonzeroLocus (b i) = ⊤ → ∃ t : (L.pull π).Sec, t ≠ 0 ∧ (IsIntegral (secIdeal (LB.isLB_pull hL π) t).subscheme ∨ IsEmpty (secIdeal (LB.isLB_pull hL π) t).subscheme) := by
  intro k _ N X X' _ _ f f' π hP L hL b hb

  have loc : ∀ x : X, ∃ (V : X.Opens) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N),
      IsAffineOpen V ∧ x ∈ V ∧ IsUnit (resG X hVc ((b j).f c)) := by
    intro x
    have hx : x ∈ (⨆ i, nonzeroLocus (b i)) := hb.ge (Set.mem_univ x)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 hj
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hc
    have hVc : V ≤ L.U c := hVle.trans (X.basicOpen_le _)
    refine ⟨V, c, hVc, j, hVa, hxV, ?_⟩
    have h1 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((b j).f c)
    have h2 := h1.map (X.presheaf.map (homOfLE hVle).op).hom
    convert h2 using 1
    simp only [resG]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  choose V c hVc j hVa hxV hu using loc
  have hW : ∀ x, IsAffineOpen (π ⁻¹ᵁ V x) := fun x => (GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)).1
  have key : ∀ x, (genSec k N f' π L b).f (fun _ => c x) ≠ 0 ∧
      ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩ = ⊤ ∨
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).IsPrime ∧
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).comap
          (π.app (V x)).hom = ⊥) := fun x => by
    obtain ⟨-, e, he1, he2⟩ := GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)
    exact GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart k N X X' f f' π L hL b (V x) ⟨x, hxV x⟩ (hW x) (c x) (hVc x) (j x) (hu x) e he1 he2
  refine ⟨genSec k N f' π L b, fun h0 => ?_, ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact (key x).1 (by rw [h0]; rfl)
  · refine _root_.GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme X' _ X (fun x => ⟨π ⁻¹ᵁ V x, hW x⟩) ?_ (fun x => ?_) (fun x y hx hy => ?_)
    · refine eq_top_iff.2 fun z _ => Opens.mem_iSup.2 ⟨π z, hxV (π z)⟩
    · rcases (key x).2 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    · rcases (key x).2 with h | h
      · exact absurd h hx.ne_top
      · have hg := _root_.GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint X X' π (V x) (hVa x) (hW x) _ hx h.2
        show π _ ∈ V y
        rw [hg]
        exact (genericPoint_spec X).mem_open_set_iff (V y).isOpen |>.2 ⟨y, trivial, hxV y⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

theorem atPl_mem_range_map {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)) (N : ∀ i, Submodule ℂ (V i)) (hN : ∀ i, ∀ y ∈ N i, L i y ∈ N i)
    (w : ι) (y : ⨂[ℂ] i, V i) (hy : y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype)) :
    atPl w (L w) y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : ∀ j, (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w) j) (x j : V j) ∈ N j := by
      intro j
      by_cases h : j = w
      · subst h
        simp only [Function.update_self]
        exact hN j _ (x j).2
      · simp only [Function.update_of_ne h, LinearMap.id_apply]
        exact (x j).2
    refine ⟨r • PiTensorProduct.tprod ℂ (fun j => (⟨_, hx j⟩ : N j)), ?_⟩
    simp [atPl, PiTensorProduct.map_tprod]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem locFin_sumPl : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) →
    GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := by
  intro ι _ _ V _ _ L hL v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose N hNf hfN hN using fun i => hL i (f i)
    refine ⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩
    · exact ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)), by simp [PiTensorProduct.map_tprod]⟩
    · intro y hy
      rw [sumPl, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun w _ => atPl_mem_range_map L N hN w y hy
  | add a b ha hb =>
    obtain ⟨N₁, h₁, ha₁, hs₁⟩ := ha
    obtain ⟨N₂, h₂, hb₂, hs₂⟩ := hb
    refine ⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, ?_⟩
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hs₁ y₁ hy₁) (hs₂ y₂ hy₂)

end GlobalTheory.RealLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairFormRatioLocalScalarNormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ P₁ : Pair G, ∃ S : Finset ℕ, ∀ (P : Pair G), P.γ = P₁.γ → P.c = P₁.c → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf), f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (P₁.γ : G.C)) ∧ inC G ℚ_[ℓ] ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (P₁.β : G.C) * (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.CxRegPair.local_pair_scalar_norm) | (exact GlobalTheory.CxRegPair.local_pair_scalar_norm) | (intros; apply GlobalTheory.CxRegPair.local_pair_scalar_norm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantLaplacianEqCasimirDecompositionStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftInvariantLaplacian_eq_casimir_decomposition : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    lapOp E a = (2 : ℂ) • casKOp E a + ∑ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := by
  first | exact @GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas | exact GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas | (intros; apply GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas <;> assumption)
end

