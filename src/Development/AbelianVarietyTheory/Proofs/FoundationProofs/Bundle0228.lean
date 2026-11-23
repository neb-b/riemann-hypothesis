module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanInfPosLogLe
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchMean

theorem sum_comp_algHom (K M : Type) [Field K] [Field M] [Algebra ℚ K] [Algebra ℚ M] [Algebra K M]
    [IsScalarTower ℚ K M] [FiniteDimensional ℚ K] [FiniteDimensional ℚ M]
    (F : (K →ₐ[ℚ] ℂ) → ℝ) :
    ∑ ρ : M →ₐ[ℚ] ℂ, F (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) =
      (Module.finrank K M : ℝ) * ∑ φ : K →ₐ[ℚ] ℂ, F φ := by
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  haveI : CharZero K := algebraRat.charZero K
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun ρ : M →ₐ[ℚ] ℂ => ρ.comp (IsScalarTower.toAlgHom ℚ K M)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F φ)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  letI : Algebra K ℂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq fun q => (φ.commutes q).symm
  rw [← AlgHom.card K M ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun ψ _ => ψ.restrictScalars ℚ) ?_ ?_ ?_
  · intro ψ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext a
    exact ψ.commutes a
  · intro a _ b _ h
    exact AlgHom.restrictScalars_injective ℚ h
  · intro ρ hρ
    have h := (Finset.mem_filter.1 hρ).2
    exact ⟨{ ρ.toRingHom with commutes' := fun a => DFunLike.congr_fun h a },
      Finset.mem_univ _, rfl⟩

theorem sum_algHom_eq (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (f : InfinitePlace K → ℝ) :
    ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom) = 2 * ∑ v, f v := by
  have h1 : ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom)
      = ∑ φ : K →+* ℂ, f (InfinitePlace.mk φ) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun _ => rfl
  rw [h1, ← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : K →+* ℂ => InfinitePlace.mk φ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f v)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 1
  have := InfinitePlace.card_filter_mk_eq v
  rw [IsTotallyComplex.mult_eq] at this
  exact_mod_cast this

theorem posLog_sum_le {ι : Type} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (a b : ι → ℂ) :
    Real.posLog ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      (Real.posLog (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) + Real.posLog (∑ i, (w i : ℝ) * ‖b i‖ ^ 2)) / 2 := by
  have hw' : ∀ i, (0 : ℝ) ≤ w i := fun i => by exact_mod_cast hw i
  have h1 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      ∑ i, (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    have h := Real.mul_self_sqrt (hw' i)
    rw [norm_mul, norm_mul, Complex.norm_ratCast, abs_of_nonneg (hw' i)]
    linear_combination (-(‖a i‖ * ‖b i‖)) * h
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i) * ‖a i‖) (fun i => Real.sqrt (w i) * ‖b i‖)
  simp only [mul_pow, Real.sq_sqrt (hw' _)] at h2
  have h3 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ^ 2 ≤
      (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) * ∑ i, (w i : ℝ) * ‖b i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have h4 := (Real.posLog_le_posLog (le_trans (by norm_num) (sq_nonneg _)) h3).trans Real.posLog_mul
  rw [Real.posLog_pow] at h4
  push_cast at h4
  linarith

theorem meanInf_posLog_le :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) (x : K) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] [IsGalois ℚ M] (ι : Type) [Fintype ι] (w : ι → ℚ) (z : ι → M), (∀ a, σ a ∈ M) → (∀ i, 0 ≤ w i) → σ x = ∑ i, (w i : ℂ) * ((z i : ℂ) * starRingEnd ℂ (z i : ℂ)) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2)) / (Module.finrank ℚ M : ℝ) := by
  intro K _ _ _ σ x M _ _ ι _ w z hσ hw hx
  let σ' : K →+* M := σ.codRestrict M hσ
  letI : Algebra K M := σ'.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let j : M →ₐ[ℚ] ℂ := ((starRingEnd ℂ).toRatAlgHom).comp M.val
  have hj : ∀ y : M, starRingEnd ℂ (y : ℂ) ∈ M := fun y => by
    have : j y ∈ j.fieldRange := ⟨y, rfl⟩
    exact (@AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ M (IsGalois.to_normal (F := ℚ) (E := M)) j).le this
  let c : M →ₐ[ℚ] M := (j.toRingHom.codRestrict M hj).toRatAlgHom
  have hc : ∀ y : M, (c y : ℂ) = starRingEnd ℂ (y : ℂ) := fun _ => rfl
  have hcc : ∀ y, c (c y) = y := fun y => Subtype.ext (by rw [hc, hc, Complex.conj_conj])
  have hxM : algebraMap K M x = ∑ i, (w i : M) * (z i * c (z i)) := by
    apply Subtype.ext
    change σ x = M.val _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_ratCast]
    rfl
  set A : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2) with hA
  have hinv : Function.Involutive (fun ρ : M →ₐ[ℚ] ℂ => ρ.comp c) := fun ρ => by
    ext y
    simp [hcc]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, A (ρ.comp c) = ∑ ρ, A ρ :=
    Fintype.sum_equiv hinv.toPerm _ _ fun _ => rfl
  have h1 := sum_comp_algHom K M (fun φ => Real.posLog ‖φ x‖)
  have h2 := sum_algHom_eq K (fun v => Real.posLog ‖v.embedding x‖)
  have h3 : ∑ φ : K →ₐ[ℚ] ℂ, Real.posLog ‖φ x‖ =
      2 * ∑ v : InfinitePlace K, Real.posLog ‖v.embedding x‖ := by
    rw [← h2]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
    rfl
  have h4 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog ‖(ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x‖
      ≤ ∑ ρ, A ρ := by
    calc _ ≤ ∑ ρ : M →ₐ[ℚ] ℂ, (A ρ + A (ρ.comp c)) / 2 := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          have : (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x
              = ∑ i, (w i : ℂ) * (ρ (z i) * ρ (c (z i))) := by
            change ρ (algebraMap K M x) = _
            set_option synthInstance.maxHeartbeats 100000 in
              rw [hxM, map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, map_mul, map_ratCast]
          rw [this]
          exact posLog_sum_le w hw _ _
      _ = ∑ ρ, A ρ := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, hsum]; ring
  rw [h1, h3] at h4
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hM : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [le_div_iff₀ hM, ← ht]
  refine le_trans (le_of_eq ?_) h4
  field_simp

end GlobalTheory.ArchMean
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProd
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PullNorm

noncomputable def coordLin (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b j
  map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
  map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc]

theorem coordLin_apply (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) (z : VC D N N') : coordLin D T b j z = coordB D T b j z := rfl

theorem coordB_sum (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (h1 : ∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) (u : Fin r → ℂ) (k : Fin r) :
    coordB D T b k (∑ j, u j • embV D T (b j)) = u k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coordLin_apply, map_sum]
  simp [coordLin_apply, h1]

theorem parseval (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (z : VC D N N') (h2 : z = ∑ j, coordB D T b j z • embV D T (b j)) :
    (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (z τ i j)) = ((∑ k, ‖coordB D T b k z‖ ^ 2 : ℝ) : ℂ) := by
  have key : ∀ c : Fin r → ℂ,
      (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) ((∑ k, c k • embV D T (b k)) τ i j))
        = ∑ k, coordB D T b k z * (starRingEnd ℂ) (c k) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coordB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum,
      Finset.sum_mul, embV]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have h := key fun k => coordB D T b k z
  rw [← h2] at h
  rw [h]
  push_cast
  exact Finset.sum_congr rfl fun k _ => Complex.mul_conj' _

theorem gaussianWeight_thetaTranslate_normSq (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) (ω z : ℂ) :
    ‖U1 Λ ω g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)
      = ‖g (ω + z)‖ ^ 2 * Real.exp (-Real.pi * ‖ω + z‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, add_comm z ω]
  congr 2
  have h2 : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
  push_cast
  ring

theorem normSq_pullB : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ T.abelian₂ = AddSubgroup.closure {w₁, w₂}) → (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → (∀ z : VC D N N', z = ∑ j, coordB D T b j z • embV D T (b j)) → ∀ g : ℂ → ℂ, Continuous g → (∀ ω ∈ T.abelian₂, ∀ z, ‖U1 T.abelian₂ ω g z‖ = ‖g z‖) → normSq D T (LaB D T b) (pullB D T b g) = nrm1Sq T.abelian₂ g ^ r := by
  intro D T N N' r b hΛ h1 h2 g _ hg
  let eC : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ) :=
    { LinearMap.pi (fun j => coordLin D T b j) with
      invFun := fun u => ∑ j, u j • embV D T (b j)
      left_inv := fun z => (h2 z).symm
      right_inv := fun u => funext fun k => coordB_sum D T b h1 u k }
  let e : VC D N N' ≃ₗ[ℝ] (Fin r → ℂ) := eC.restrictScalars ℝ
  have he : ∀ z k, e z k = coordB D T b k z := fun _ _ => rfl
  have hA : ∀ x, x ∈ LaB D T b ↔ ∀ k, e x k ∈ T.abelian₂ := by
    intro x
    constructor
    · intro hx k
      unfold LaB at hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, j, rfl⟩ := hy
        rw [he, ← coordLin_apply, map_smul, coordLin_apply, h1]
        split_ifs
        · simpa using hw
        · simp
      | zero => simp
      | add y z _ _ hy hz => simpa only [map_add, Pi.add_apply] using add_mem hy hz
      | neg y _ hy => rw [map_neg]; exact neg_mem hy
    · intro hx
      rw [h2 x]
      exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨_, hx j, j, rfl⟩
  haveI i1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have main := GlobalTheory.LatticeMean.mean_prod_eq_pow T.abelian₂ hΛ
    (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area T.abelian₂))
    (fun ω hω z => by rw [← gaussianWeight_thetaTranslate_normSq, hg ω hω]) (VC D N N') MeasureTheory.volume r e (LaB D T b) hA
  unfold normSq nrm1Sq
  simp only []
  rw [← main]
  congr 1
  funext z
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Hf, parseval D T b z (h2 z), Complex.div_ofReal_re,
    Complex.ofReal_re, pullB, norm_prod, ← Finset.prod_pow]
  simp only [he]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]

end GlobalTheory.PullNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonempty
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ),
    Nonempty (Frac Ω ε) := by
  intro Ω _ _ _ ε
  classical
  haveI : IsDomain (ring ε.range) := _root_.GlobalTheory.FN.ring_isDomain ε.range
  obtain ⟨hmem, hconst⟩ := _root_.GlobalTheory.FN.mem_ring_iff_inR ε.range
  obtain ⟨-, huniq, hC, -, -⟩ := _root_.GlobalTheory.FNExp.exp_props Ω ε
  obtain ⟨e, he_inj, he_exp⟩ := _root_.GlobalTheory.FN.expansion_injective_ringHom Ω ε
  obtain ⟨hexp_mem, -, -, -, -, -⟩ := _root_.GlobalTheory.FNRoots.main Ω ε
  obtain ⟨⟨G, hG⟩, hmd, -, -, hHs⟩ := _root_.GlobalTheory.FN.germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := _root_.GlobalTheory.FN.germ_main

  let cst : Ω →+* ring ε.range :=
    { toFun := fun x => ⟨fun _ => ε x, (hmem _).2 (hconst _ ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (funext fun _ => by simp)
      map_mul' := fun x y => Subtype.ext (funext fun _ => by simp)
      map_zero' := Subtype.ext (funext fun _ => by simp)
      map_add' := fun x y => Subtype.ext (funext fun _ => by simp) }
  have hcst : ∀ x, ((cst x : ring ε.range) : ℍ → ℂ) = fun _ => ε x := fun _ => rfl
  have hec : ∀ x, e (cst x) = algebraMap Ω (HahnSeries ℚ Ω) x := by
    intro x
    refine huniq _ _ _ (he_exp (cst x)) ?_
    simpa [hcst, HahnSeries.algebraMap_apply'] using hC x

  have hsl := fun g : GQ => _root_.GlobalTheory.FN.cmp_ringEquiv ε.range g hexp_mem
  choose σ hσ using hsl
  have hslc : ∀ g x, σ g (cst x) = cst x := by
    intro g x
    apply Subtype.ext
    rw [hσ]
    rfl

  have hga := fun s : Ω ≃ₐ[ℚ] Ω => _root_.GlobalTheory.FN.exists_ringEquiv_coeff_conj Ω ε s.toRingEquiv
  choose τ hτ using hga

  let A : ring ε.range →+* Mero := G.comp (ring ε.range).subtype
  have hA : ∀ a : ring ε.range, A a = ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) := fun a => hG a
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs :=
    fun a => (hmd _).1 (_root_.GlobalTheory.FN.inR_mdifferentiable _ _ ((hmem _).1 a.2))
  have hAunit : ∀ a, a ≠ 0 → IsUnit (A a) := by
    intro a ha
    rw [hA]
    refine (hunit _ (hdiff a) ?_).2
    intro h0
    apply ha
    have h0' : ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((up ((0 : ring ε.range) : ℍ → ℂ) : ℂ → ℂ) : Mero) := by
      rw [h0, ← hA, map_zero]
    have heq := hid _ _ (hdiff a) (hdiff 0) h0'
    apply Subtype.ext
    funext t
    have := heq t (hHs t)
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  obtain ⟨K, fK, aK, io, e', sl', ga', A', hinj, hsurj, hioc, he', hsl', hga', hA'⟩ :=
    _root_.GlobalTheory.fraction_field_extension Ω (ring ε.range) (HahnSeries ℚ Ω) Mero GQ (Ω ≃ₐ[ℚ] Ω) cst e σ τ A he_inj hec hslc hAunit
  refine ⟨{
    K := K
    fld := fK
    alg := aK
    io := io
    io_inj := hinj
    io_surj := hsurj
    io_c := fun x a ha => ?_
    exp := e'
    exp_io := fun a => ?_
    sl := sl'
    sl_io := fun g a a' ha => ?_
    gal := ga'
    gal_exp := fun s f r => ?_
    an := A'
    an_io := fun a => ?_ }⟩
  · have : a = cst x := Subtype.ext ha
    rw [this, hioc]
  · rw [he']
    exact he_exp a
  · rw [hsl']
    congr 1
    exact Subtype.ext ((hσ g a).trans ha.symm)
  · obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.FNTwist.exists_scale_twist_ringHom Ω Ω (s : Ω →+* Ω) 1 (fun _ => 1) one_pos rfl (fun _ _ => (mul_one 1).symm)
    have hΦ' : ∀ h r, (Φ h).coeff r = s (h.coeff r) := by
      intro h r
      have := hΦ h r
      simpa using this
    have key : ∀ a, e' (ga' s (io a)) = Φ (e' (io a)) := by
      intro a
      rw [hga', he', he']
      ext r
      rw [hτ s a (e a) (e (τ s a)) (he_exp a) (he_exp _) r, hΦ']
      rfl
    obtain ⟨a, b, hb, hf⟩ := hsurj f
    have hib : io b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hf' : f = io a * (io b)⁻¹ := by rw [← hf, mul_assoc, mul_inv_cancel₀ hib, mul_one]
    have hfe : e' (ga' s f) = Φ (e' f) := by
      rw [hf']
      simp only [map_mul, map_inv₀, key]
    rw [hfe, hΦ']
  · rw [hA', hA]
    rfl

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowth
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GaussCauchy

theorem factor_le (A B : ℝ) (hA : 0 < A) (n : ℕ) (hn : (n : ℝ) ≤ 2 * B) :
    ((n.factorial : ℝ)) ^ 2 * Real.exp n / (A * n / Real.pi) ^ n
      ≤ (2 * Real.exp 1 * Real.pi * B / A) ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h
  have hpi := Real.pi_pos
  rw [div_le_iff₀ (by positivity), ← mul_pow]
  have h1 : 2 * Real.exp 1 * Real.pi * B / A * (A * n / Real.pi) = (2 * B) * n * Real.exp 1 := by
    field_simp
  have h2 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h3 : (n : ℝ) ^ n ≤ (2 * B) ^ n := pow_le_pow_left₀ hn0.le hn n
  rw [h1, mul_pow, mul_pow (2 * B), ← Real.exp_nat_mul, mul_one, sq]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul (h2.trans h3) h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (n : ℝ) ^ n).trans h3)

theorem pderivIter_sq_le {ι : Type*} [DecidableEq ι] [Fintype ι] (F : (ι → ℂ) → ℂ) (S A B : ℝ)
    (hA : 0 < A) (hS : 0 ≤ S) (hF : Differentiable ℂ F)
    (hb : ∀ z, ‖F z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ k, ‖z k‖ ^ 2) / A))
    (α : ι →₀ ℕ) (hα : ∀ k, (α k : ℝ) ≤ 2 * B) :
    ‖pderivIter α F 0‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (∑ k, α k) := by
  have hpi := Real.pi_pos
  have hsq : ∀ k, Real.sqrt (A * α k / Real.pi) ^ 2 = A * α k / Real.pi := fun k =>
    Real.sq_sqrt (by positivity)
  have h := norm_pderivIter_le_of_differentiable (F := F) (a := 0)
    (r := fun k => Real.sqrt (A * α k / Real.pi))
    (M := Real.sqrt (S * Real.exp (∑ k, (α k : ℝ)))) α (fun k => Real.sqrt_nonneg _)
    (fun k hk => by
      have : (0 : ℝ) < α k := by exact_mod_cast Nat.pos_of_ne_zero hk
      exact Real.sqrt_pos.mpr (by positivity)) hF
    (fun z hz => by
      apply Real.le_sqrt_of_sq_le
      refine (hb z).trans (le_of_eq ?_)
      congr 2
      simp only [Pi.zero_apply, sub_zero] at hz
      simp only [hz, hsq, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp)
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans ?_
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), ← Finset.prod_pow, ← Finset.prod_pow,
    Real.exp_sum, ← Finset.prod_pow_eq_pow_sum, mul_left_comm, mul_div_assoc,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_) hS
  rw [← pow_mul, mul_comm (α k) 2, pow_mul, hsq]
  exact factor_le A B hA _ (hα k)

noncomputable def curry (D : D7) (N N' : ℕ) :
    (D.what₂.Tau × Fin N' × Fin N → ℂ) →ₗ[ℂ] VC D N N' where
  toFun w := fun τ i j => w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem curry_single (D : D7) (N N' : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    curry D N N' (Pi.single k 1) = coordV D k := by
  funext τ i j
  obtain ⟨a, b, c⟩ := k
  simp [curry, coordV, Pi.single_apply, Prod.ext_iff]

theorem factorial_mul_taylor (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α
      = pderivIter α (fun w => G (curry D N N' w)) 0 := by
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have han : AnalyticAt ℂ G 0 := SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)
  rw [taylor, mul_div_cancel₀ _ hne, pderivIter, pderivList, lineDerivList_comp_linearMap,
    ← lineDerivList_ofFn han]
  simp only [map_zero, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [curry_single]

theorem monomial_deriv_bound : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  intro D N N' G S A B hA _ hS hG hb α hα
  rw [factorial_mul_taylor D N N' G hG, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine pderivIter_sq_le _ S A B hA hS
    (hG.comp (LinearMap.toContinuousLinearMap (curry D N N')).differentiable) (fun z => ?_) α hα
  simp only [Fintype.sum_prod_type]
  exact hb (curry D N N' z)

end GlobalTheory.GaussCauchy
end

