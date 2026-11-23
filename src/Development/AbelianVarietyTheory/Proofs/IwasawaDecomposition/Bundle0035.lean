module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjoinGelfandInvariantsDualPairEq
section
open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Capelli

variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}

def trAlg (M : Matrix (Fin n) (Fin n) A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ (Set.range fun k : ℕ => (M ^ (k + 1)).trace)

theorem trace_pow_mem (M : Matrix (Fin n) (Fin n) A) (k : ℕ) : (M ^ k).trace ∈ trAlg M := by
  cases k with
  | zero => simpa using natCast_mem (trAlg M) n
  | succ k => exact Algebra.subset_adjoin ⟨k, rfl⟩

theorem trAlg_le {M : Matrix (Fin n) (Fin n) A} {S : Subalgebra ℂ A} (h : ∀ k, (M ^ (k + 1)).trace ∈ S) :
    trAlg M ≤ S := Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact h k)

theorem trAlg_shift_le (M : Matrix (Fin n) (Fin n) A) (s c : ℂ) : trAlg (s • M + c • 1) ≤ trAlg M := by
  have key : ∀ k j : ℕ, (M ^ j * (s • M + c • 1) ^ k).trace ∈ trAlg M := by
    intro k
    induction k with
    | zero => intro j; simpa using trace_pow_mem M j
    | succ k ih =>
      intro j
      rw [pow_succ', ← mul_assoc, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
        mul_one, ← pow_succ, trace_add, trace_smul, trace_smul]
      exact add_mem (Subalgebra.smul_mem _ (ih _) _) (Subalgebra.smul_mem _ (ih _) _)
  exact trAlg_le fun k => by simpa using key (k + 1) 0

theorem trAlg_shift (M : Matrix (Fin n) (Fin n) A) {s : ℂ} (hs : s ≠ 0) (c : ℂ) :
    trAlg (s • M + c • 1) = trAlg M := by
  refine le_antisymm (trAlg_shift_le M s c) ?_
  have h := trAlg_shift_le (s • M + c • (1 : Matrix (Fin n) (Fin n) A)) s⁻¹ (-(s⁻¹ * c))
  rwa [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, neg_smul, add_neg_cancel_right] at h

theorem adjoin_gelfA (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA E)) = trAlg (Matrix.of E) := by
  rw [trAlg]
  congr 2
  funext k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  rfl

section CCR

variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)

omit [Algebra ℂ A] in
include hdd hdx in
theorem comm_one (a : Fin m) (l i j : Fin n) :
    D a l * (X * D) i j = (X * D) i j * D a l + if i = l then D a j else 0 := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, hdx, add_mul, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => by rw [mul_assoc, mul_assoc, hdd]
  · by_cases h : i = l <;> simp [h]

omit [Algebra ℂ A] in
include hdd hdx in
theorem comm_pow (p : ℕ) (a : Fin m) (l i j : Fin n) :
    D a l * ((X * D) ^ p) i j = ((X * D) ^ p) i j * D a l
      + ∑ r ∈ Finset.range p, ((X * D) ^ r) i l * (D * (X * D) ^ (p - (r + 1))) a j := by
  induction p generalizing i with
  | zero => by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ p ih =>
    have h1 : ∀ k, D a l * ((X * D) i k * ((X * D) ^ p) k j) =
        (X * D) i k * ((X * D) ^ p) k j * D a l
        + (∑ r ∈ Finset.range p, (X * D) i k * ((X * D) ^ r) k l * (D * (X * D) ^ (p - (r + 1))) a j
          + if i = l then D a k * ((X * D) ^ p) k j else 0) := fun k => by
      rw [← mul_assoc, comm_one X D hdd hdx, add_mul, mul_assoc, ih, mul_add, Finset.mul_sum, add_assoc]
      simp only [mul_assoc, ite_mul, zero_mul]
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.sum_range_succ']
    simp only [h1, Finset.sum_add_distrib]
    congr 2
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_mul, ← Matrix.mul_apply, ← pow_succ', Nat.add_sub_add_right]
    · by_cases h : i = l <;> simp [h, Matrix.one_apply, Matrix.mul_apply]

omit [Algebra ℂ A] in
include hdd hdx in
theorem trace_rec (p : ℕ) :
    ((D * X) ^ (p + 1)).trace = ((X * D) ^ (p + 1)).trace + (m : A) * ((X * D) ^ p).trace
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * ((D * X) ^ (p - (r + 1) + 1)).trace := by
  have hN : ∀ q : ℕ, (D * X) ^ (q + 1) = D * (X * D) ^ q * X := fun q => by
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]
  have hY : ∀ a j, (D * (X * D) ^ p) a j = ∑ u, ((X * D) ^ p) u j * D a u
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * (D * (X * D) ^ (p - (r + 1))) a j := fun a j => by
    rw [Matrix.mul_apply]
    simp only [comm_pow X D hdd hdx, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [trace, diag_apply, Finset.sum_mul]
  have hT : ∀ q : ℕ, ((D * X) ^ (q + 1)).trace = ∑ a, ∑ j, (D * (X * D) ^ q) a j * X j a := fun q => by
    rw [hN]; rfl
  have hE : ∀ u j, ∑ a, D a u * X j a = (X * D) j u + if j = u then (m : A) else 0 := fun u j => by
    simp only [hdx, Finset.sum_add_distrib, Matrix.mul_apply]
    by_cases h : j = u <;> simp [h]
  simp only [hT]
  simp only [hY, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  congr 1
  · rw [Finset.sum_comm]
    have : ∀ j, ∑ a, ∑ u, ((X * D) ^ p) u j * (D a u * X j a)
        = ∑ u, ((X * D) ^ p) u j * (X * D) j u + (m : A) * ((X * D) ^ p) j j := fun j => by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hE, mul_add, Finset.sum_add_distrib]
      simp [Nat.cast_comm]
    simp only [this, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm, pow_succ]; rfl
    · simp only [trace, diag_apply, Finset.mul_sum]
  · rw [Finset.sum_comm (s := Finset.range p)]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

include hdd hdx in
theorem trAlg_mul_comm : trAlg (X * D) = trAlg (D * X) := by
  apply le_antisymm
  · have key : ∀ p : ℕ, ((X * D) ^ p).trace ∈ trAlg (D * X) := fun p => by
      induction p using Nat.strong_induction_on with
      | _ p ih =>
        cases p with
        | zero => simpa using natCast_mem (trAlg (D * X)) n
        | succ p =>
          have h := trace_rec X D hdd hdx p
          rw [add_assoc, ← sub_eq_iff_eq_add] at h
          rw [← h]
          refine sub_mem (trace_pow_mem _ _) (add_mem (mul_mem (natCast_mem _ _) (ih p (by omega)))
            (sum_mem fun r hr => mul_mem (ih r ?_) (trace_pow_mem _ _)))
          have := Finset.mem_range.1 hr
          omega
    exact trAlg_le fun k => key _
  · refine trAlg_le fun p => ?_
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      rw [trace_rec X D hdd hdx p]
      refine add_mem (add_mem (trace_pow_mem _ _) (mul_mem (natCast_mem _ _) (trace_pow_mem _ _)))
        (sum_mem fun r hr => mul_mem (trace_pow_mem _ _) (ih _ ?_))
      have := Finset.mem_range.1 hr
      omega

end CCR

theorem adjoin_gelfA_dual_pair : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  intro A _ _ n m x d h c c'
  obtain ⟨-, hdd, hdx⟩ := h
  let X : Matrix (Fin n) (Fin m) A := Matrix.of fun i a => x (i, a)
  let D : Matrix (Fin m) (Fin n) A := Matrix.of fun a i => d (i, a)
  have hdx' : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0 := fun a l i b => by
    have := hdx (i, b) (l, a)
    rw [sub_eq_iff_eq_add'] at this
    simpa [X, D] using this
  have h1 : (Matrix.of fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)
      = (1 : ℂ) • (X * D) + c • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [X, D, Matrix.mul_apply, Matrix.one_apply, hij, Algebra.algebraMap_eq_smul_one]
  have h2 : (Matrix.of fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)
      = (-1 : ℂ) • (D * X) + (c' + n) • 1 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, hdx', Finset.sum_add_distrib]
    by_cases hab : a = b
    · subst hab
      simp [X, D, Algebra.algebraMap_eq_smul_one, add_smul, Nat.cast_smul_eq_nsmul]
      abel
    · simp [X, D, hab, Ne.symm hab]
  rw [adjoin_gelfA, adjoin_gelfA, h1, h2, trAlg_shift _ one_ne_zero, trAlg_shift _ (by norm_num)]
  exact trAlg_mul_comm X D (fun a l b j => hdd _ _) hdx'

end GlobalTheory.Mem.Capelli
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgHomEqOrConj
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitPlaceExt

variable {L : Type} [Field L] [NumberField L] [IsCMField L]


open NumberField IsDedekindDomain in
variable {L : Type} [Field L] [NumberField L] [IsCMField L] in
theorem _root_.GlobalTheory.SplitPlaceExt.eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s s' : _root_.ReciprocityTheory.Aut.SplitPlace L), s'.w = s.w → s' = s := by
  intro L _ _ _ s s' h
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  obtain rfl : v = v' := hv.symm
  have key : ∀ x : 𝓞 L, Valued.v (i' x) < 1 ↔ Valued.v (i x) < 1 := fun x =>
    Iff.of_eq (congrArg (fun P : HeightOneSpectrum (𝓞 L) => x ∈ P.asIdeal) h)
  obtain ⟨e, he1, he2⟩ := _root_.GlobalTheory.SplitSep.exists_sep (L := L) ⟨v, i⟩
  set c := i.comp (IsCMField.complexConj L).toAlgHom with hc
  have hce : c e = i (IsCMField.complexConj L e) := rfl
  have hic : i ≠ c := by
    intro hi
    have : Valued.v (i e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 this.ne
  have hi'c : i' ≠ c := by
    intro hi
    have : Valued.v (i' e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 ((key e).1 this).ne
  by_contra hne
  have hii' : i' ≠ i := fun hh => hne (by rw [hh])
  have hinj : Function.Injective ![i, c, i'] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h3 : Nat.card (Fin 3) ≤ _ := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h3
  have h2 := card_algHom_le_finrank (maximalRealSubfield L) L
    (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  omega

end GlobalTheory.SplitPlaceExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionElementFrobeniusPowerStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_element_frobenius_power : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (L : IntermediateField E Ω), FiniteDimensional E L → ∀ g : G E Ω, g ∈ Dec (F := E) A → ∃ k : ℕ, ∀ x ∈ L, IsIntegral ℤ x → A.valuation ((g x) ^ (normV w ^ k) - x) < 1 := by
  first | exact @GlobalTheory.WeilDeligne.exists_pow_normV_resPow | exact GlobalTheory.WeilDeligne.exists_pow_normV_resPow | (intros; apply GlobalTheory.WeilDeligne.exists_pow_normV_resPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCompAtEqZero
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct

namespace GlobalTheory.AdelicComp

theorem coord_compAt (L : Type) [Field L] [NumberField L] [IsCMField L] {ι : Type} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι (maximalRealSubfield L) L)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i : ι) (z : AL L) :
    TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ (compAt L w z))
      = evalAt L w (TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    have h : compAt L w (x ⊗ₜ a) = x ⊗ₜ evalAt L w a := rfl
    rw [h]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem eq_sum_coord {K V M : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (z : V ⊗[K] M) :
    z = ∑ i, b i ⊗ₜ[K] TensorProduct.lid K M ((b.coord i).rTensor M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, Module.Basis.coord_apply, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hx, ← hy]

theorem eq_zero_of_compAt_eq_zero :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (z : AL L), (∀ w, compAt L w z = 0) → z = 0 := by
  intro L _ _ _ z hz
  classical
  let b := Module.finBasis (maximalRealSubfield L) L
  rw [eq_sum_coord b z]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z) = 0 := by
    refine Subtype.ext (funext fun w => ?_)
    have h := coord_compAt L b w i z
    rw [hz w, map_zero, map_zero] at h
    exact h.symm
  rw [this, TensorProduct.tmul_zero]

end GlobalTheory.AdelicComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.exists_continuous_extension_adicCompletion (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] (τ : E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (v : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1) :
    ∃ j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l, Continuous j ∧
      j.comp (algebraMap E (v.adicCompletion E)) = τ := by
  unfold _root_.Formalism.ConjugateSelfDual.Qbar at τ h ⊢

  let b := Module.finBasis ℚ E
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    IntermediateField.adjoin ℚ_[l] (Set.range fun i => τ (b i))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  have hmem : ∀ x, τ x ∈ K := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem K _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

  let g : WithVal (v.valuation E) →+* PadicAlgCl l := τ.comp (WithVal.equiv (v.valuation E)).toRingHom
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E v
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have hπ1 : ‖τ π‖ < 1 := (h π).1 (by rw [hπ]; decide)
  have hπpos : 0 < ‖τ π‖ := norm_pos_iff.2 ((map_ne_zero τ).2 hπ0)
  have hg : Continuous g := by
    refine continuous_of_continuousAt_zero g ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ1
    let y : WithVal (v.valuation E) := (WithVal.equiv (v.valuation E)).symm (π ^ n)
    have hy : Valued.v.restrict y ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero _).2 (pow_ne_zero n hπ0)
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    refine ⟨Units.mk0 _ hy, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx ⊢
    have hz : v.valuation E (WithVal.equiv (v.valuation E) x) < v.valuation E (π ^ n) := hx
    have hπn : v.valuation E (π ^ n) ≠ 0 := by
      rw [map_pow, hπ]; exact pow_ne_zero _ (WithZero.coe_ne_zero)
    have hq : v.valuation E (WithVal.equiv (v.valuation E) x / π ^ n) < 1 := by
      rw [map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.2 hπn)).2 hz
    have hτq := (h _).1 hq
    rw [map_div₀, map_pow, norm_div, norm_pow, div_lt_one (pow_pos hπpos n)] at hτq
    rw [dist_zero_right]
    exact lt_trans hτq hn
  let τ' : WithVal (v.valuation E) →+* K :=
    (τ.codRestrict K hmem).comp (WithVal.equiv (v.valuation E)).toRingHom
  have hτ' : Continuous τ' := continuous_induced_rng.2 hg
  let ext : (v.valuation E).Completion →+* K := UniformSpace.Completion.extensionHom τ' hτ'
  let φ : v.adicCompletion E →+* (v.valuation E).Completion :=
    { toFun := HeightOneSpectrum.adicCompletion.toCompletion
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Continuous φ := uniformContinuous_comap.continuous
  refine ⟨(algebraMap K (PadicAlgCl l)).comp (ext.comp φ), ?_, ?_⟩
  · exact continuous_subtype_val.comp (UniformSpace.Completion.continuous_extension.comp hφ)
  · ext x
    simp only [RingHom.comp_apply, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply]
    change ((ext ((WithVal.equiv (v.valuation E)).symm (algebraMap E E x) : (v.valuation E).Completion) : K) :
      PadicAlgCl l) = τ x
    rw [UniformSpace.Completion.extensionHom_coe]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCCRXOpDOp
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.Ccr

theorem comm_comb {A : Type} [Ring A] [Algebra ℂ A] (p p' q q' : A) (s t c₁ c₂ c₃ c₄ : ℂ)
    (h₁ : p * q = q * p + c₁ • (1 : A)) (h₂ : p * q' = q' * p + c₂ • (1 : A))
    (h₃ : p' * q = q * p' + c₃ • (1 : A)) (h₄ : p' * q' = q' * p' + c₄ • (1 : A)) :
    (p + s • p') * (q + t • q') = (q + t • q') * (p + s • p') + (c₁ + t * c₂ + s * c₃ + s * t * c₄) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h₁, h₂, h₃, h₄]
  module

theorem exists_om {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) :
    ∃ om : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ, ∀ x y, om x y = (star y ⬝ᵥ H *ᵥ x).im := by
  let b : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
    (fun x x' y => by simp [mulVec_add, dotProduct_add])
    (fun r x y => by simp [mulVec_smul, dotProduct_smul])
    (fun x y y' => by simp [add_dotProduct])
    (fun r x y => by simp [smul_dotProduct])
  exact ⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ b), fun x y => rfl⟩

theorem im_self {ι : Type} [Fintype ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (x : ι → ℂ) :
    (star x ⬝ᵥ H *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ H *ᵥ x) = star x ⬝ᵥ H *ᵥ x := by
    rw [← star_dotProduct_star, star_star, star_mulVec, hH, dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem pair_inv {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (k l : ι) :
    star (H⁻¹ *ᵥ Pi.single l 1) ⬝ᵥ H *ᵥ Pi.single k 1 = if k = l then (1 : ℂ) else 0 := by
  rw [star_mulVec, conjTranspose_nonsing_inv, hH, ← dotProduct_mulVec, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), one_mulVec, dotProduct_single]
  by_cases h : k = l <;> simp [h]

end GlobalTheory.Mem.Lift.Ccr


open GlobalTheory.Mem.Lift.Ccr in
theorem GlobalTheory.Mem.Lift.exists_isCCR_xOp_dOp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∃ x d : ι → Module.End ℂ (smS ρ), (∀ k f, (x k f).1 = xOp ρ k f.1) ∧ (∀ k f, (d k f).1 = dOp ρ H k f.1) ∧ IsCCR x d := by
  intro ι _ _ H hH hd B _ _ ρ hρ
  obtain ⟨om, hom⟩ := exists_om H
  have hρ' : IsHeis (fun x y => om x y) ρ := by simpa only [hom] using hρ
  have key := _root_.GlobalTheory.Mem.Lift.DCalc.dH_calculus (ι → ℂ) B om ρ (fun x => by rw [hom, im_self hH]) hρ'
  let D : (ι → ℂ) → Module.End ℂ (smS ρ) := fun v =>
    { toFun := fun f => ⟨dH ρ v f.1, (key f.1 f.2).1 v⟩
      map_add' := fun f g => Subtype.ext (dH_add v f.2 g.2)
      map_smul' := fun a f => Subtype.ext (dH_smul v a f.2) }
  have hD : ∀ u v, D u * D v = D v * D u + (2 * π * I * ((star v ⬝ᵥ H *ᵥ u).im : ℂ)) • (1 : Module.End ℂ (smS ρ)) := by
    intro u v
    refine LinearMap.ext fun f => Subtype.ext ?_
    have := (key f.1 f.2).2.2.2.2 u v
    rw [hom, sub_eq_iff_eq_add'] at this
    exact this
  have hc : ∀ (u v : ι → ℂ) (s t : ℂ), (D u + s • D (I • u)) * (D v + t • D (I • v)) =
      (D v + t • D (I • v)) * (D u + s • D (I • u)) +
        (2 * π * I * ((1 + s * t) * (star v ⬝ᵥ H *ᵥ u).im + (s - t) * (star v ⬝ᵥ H *ᵥ u).re)) •
          (1 : Module.End ℂ (smS ρ)) := by
    intro u v s t
    rw [comm_comb _ _ _ _ s t _ _ _ _ (hD u v) (hD u (I • v)) (hD (I • u) v) (hD (I • u) (I • v))]
    congr 2
    simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    simp
    ring
  have hII : (1 : ℂ) + I * I = 0 := by simp
  refine ⟨fun k => D (Pi.single k 1) + (-I) • D (I • Pi.single k 1),
    fun l => (-(1 / (4 * π)) : ℂ) • (D (H⁻¹ *ᵥ Pi.single l 1) + I • D (I • H⁻¹ *ᵥ Pi.single l 1)),
    fun k f => ?_, fun k f => rfl, fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
  · rw [xOp, sub_eq_add_neg, ← neg_smul]
    rfl
  · beta_reduce
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc (Pi.single k 1), pair_inv hH hd, ← smul_sub, sub_add_cancel_left, ← neg_smul, smul_smul]
    by_cases h : k = l
    · simp only [h, if_true, one_im, one_re, ofReal_zero, ofReal_one]
      have hp : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have : (-(1 / (4 * π)) : ℂ) * -(2 * π * I * ((1 + -I * I) * 0 + (-I - I) * 1)) = 1 := by
        field_simp
        linear_combination (-4) * hII
      rw [this, one_smul]
    · simp [h]
end

