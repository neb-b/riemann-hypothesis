module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfMem
section
namespace GlobalTheory.IntegralElementNorm

theorem norm_algebraMap_le_one {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact (PadicAlgCl.norm_extends (p := l) _).trans_le (PadicInt.norm_le_one a)

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact l.Prime] {x : PadicAlgCl l} (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨f, hmon, hf⟩ := hx
  by_contra hbig
  push Not at hbig

  have hn : f.natDegree ≠ 0 := by
    intro h0
    simp [Polynomial.eq_one_of_monic_natDegree_zero hmon h0] at hf
  have key : x ^ f.natDegree =
      -∑ i ∈ Finset.range f.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.Monic.coeff_natDegree hmon, map_one,
      one_mul] at hf
    linear_combination hf
  have hsum : ‖∑ i ∈ Finset.range f.natDegree,
      algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (f.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    have hi' : i ≤ f.natDegree - 1 := by
      have := Finset.mem_range.1 hi
      omega
    rw [norm_mul, norm_pow]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i :=
          mul_le_mul_of_nonneg_right (norm_algebraMap_le_one _) (by positivity)
      _ ≤ ‖x‖ ^ (f.natDegree - 1) := by
          rw [one_mul]
          exact pow_le_pow_right₀ hbig.le hi'
  have hnorm : ‖x‖ ^ f.natDegree ≤ ‖x‖ ^ (f.natDegree - 1) := by
    rw [← norm_pow, key, norm_neg]
    exact hsum
  have hlt : ‖x‖ ^ (f.natDegree - 1) < ‖x‖ ^ f.natDegree := pow_lt_pow_right₀ hbig (by omega)
  linarith

theorem norm_le_one_of_mem {l : ℕ} [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {x : Formalism.ConjugateSelfDual.Qbar l}
    (hx : x ∈ UpperTheory.V.HV.Coef.O c) : ‖x‖ ≤ (1 : ℝ) := by

  have : Module.Finite ℤ_[l] c.O := c.fin
  have hint : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  exact norm_le_one_of_isIntegral (hint.map c.O.val)

end GlobalTheory.IntegralElementNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Coef.norm_le_norm_pow_iff_dvd :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O),
      ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  intro l _ c n x
  have hlnorm : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  obtain ⟨-, -, -, -, -, he0, -, he, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have key := UpperTheory.V.Base.normO l c.O x hx
  set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def
  have hEtop : UpperTheory.V.Base.eO l c.O ≠ ⊤ := by
    rw [he]; exact fun h => hl0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have hEcast : UpperTheory.V.Base.eO l c.O = (e : ℕ∞) := (ENat.coe_toNat hEtop).symm
  have hepos : e ≠ 0 := by
    intro h0; apply he0; rw [hEcast, h0]; rfl
  have hxtop : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ :=
    fun h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def
  have hvcast : IsDiscreteValuationRing.addVal c.O x = (v : ℕ∞) := (ENat.coe_toNat hxtop).symm
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hllt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : l.Prime).one_lt)
  rw [norm_pow, hlnorm, ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    ← he, hEcast, hvcast, ← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hepos, key, ← pow_mul,
    pow_le_pow_iff_right_of_lt_one₀ hlpos hllt]
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLeOne
section
noncomputable section

open Formalism.ConjugateSelfDual
open scoped Matrix

namespace GlobalTheory.SmallMat

variable {l : ℕ} [Fact l.Prime]

def Sm (ε : ℝ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) : Prop := ∀ i j, ‖M i j‖ ≤ ε

theorem Sm.mono {ε δ : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (h : Sm ε M) (hεδ : ε ≤ δ) : Sm δ M :=
  fun i j => (h i j).trans hεδ

theorem Sm.add {ε : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm ε N) : Sm ε (M + N) := fun i j => by
  simp only [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (hN i j))

theorem Sm.neg {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) : Sm ε (-M) := fun i j => by
  simpa using hM i j

theorem Sm.sub {ε : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm ε N) : Sm ε (M - N) := by
  rw [sub_eq_add_neg]; exact hM.add hN.neg

theorem sm_zero {ε : ℝ} (hε : 0 ≤ ε) : Sm (l := l) ε 0 := fun i j => by simpa using hε

theorem Sm.mul {ε δ : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm δ N) (hε : 0 ≤ ε) :
    Sm (ε * δ) (M * N) := fun i j => by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact mul_le_mul (hM _ _) (hN _ _) (norm_nonneg _) hε

theorem Sm.smul {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (a : Qbar l) : Sm (‖a‖ * ε) (a • M) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul]; exact mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg _)

theorem Sm.smul_le {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hε : 0 ≤ ε) {a : Qbar l} (ha : ‖a‖ ≤ 1) :
    Sm ε (a • M) :=
  (hM.smul a).mono (by simpa using mul_le_mul_of_nonneg_right ha hε)

theorem sm_scalar {ε : ℝ} {a : Qbar l} (ha : ‖a‖ ≤ ε) (hε : 0 ≤ ε) : Sm ε (a • (1 : Matrix (Fin 2) (Fin 2) (Qbar l))) :=
  fun i j => by
    by_cases h : i = j
    · subst h; simpa using ha
    · simpa [Matrix.one_apply_ne h] using hε

theorem Sm.sum {ι : Type*} (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (M : ι → Matrix (Fin 2) (Fin 2) (Qbar l))
    (h : ∀ i ∈ s, Sm ε (M i)) : Sm ε (∑ i ∈ s, M i) := fun a b => by
  rw [Matrix.sum_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun i hi => h i hi a b

theorem norm_natCast_le_one (b : ℕ) : ‖(b : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ b

theorem Sm.det {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hε : 0 ≤ ε) : ‖M.det‖ ≤ ε ^ 2 := by
  rw [Matrix.det_fin_two, sq, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> simp only [norm_neg, norm_mul] <;>
    exact mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _) hε

end GlobalTheory.SmallMat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSmulLeSelf
section
namespace GlobalTheory.BoundedScalarNorm

theorem norm_smul_le_self {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) (y : PadicAlgCl l) : ‖a • y‖ ≤ ‖y‖ := by
  have h : a • y = (a : ℚ_[l]) • y := by
    rw [← IsScalarTower.algebraMap_smul ℚ_[l] a y]; rfl
  rw [h, norm_smul]
  have h1 : ‖(a : ℚ_[l])‖ ≤ 1 := a.2
  exact mul_le_of_le_one_left (norm_nonneg _) h1

theorem bounded {l : ℕ} [Fact l.Prime] (M : Submodule ℤ_[l] (PadicAlgCl l)) (h : M.FG) :
    ∃ C : ℝ, ∀ y ∈ M, ‖y‖ ≤ C := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨∑ z ∈ s, ‖z‖, fun y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem z hz => exact Finset.single_le_sum (f := fun z => ‖z‖) (fun _ _ => norm_nonneg _) hz
  | zero => rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  | add u v _ _ hu hv => exact (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)
  | smul a u _ hu => exact (norm_smul_le_self a u).trans hu

theorem norm_le_one : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ UpperTheory.V.HV.Coef.O c → ‖x‖ ≤ (1 : ℝ) := by
  intro l _ c x hx
  have hfg : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.mp c.fin
  obtain ⟨C, hC⟩ := bounded _ hfg
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
  have := hC (x ^ n) (c.O.pow_mem hx n)
  rw [norm_pow] at this
  exact absurd hn (not_lt.mpr this)

end GlobalTheory.BoundedScalarNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NsmulMemSpanOfCardLe
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.CycIndex

theorem nsmul_mem_span_of_card_le : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (C r : ℕ), ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (H : Type) [AddCommGroup H] [Module c.O H] [Finite H], (∀ h : H, ((l : ℕ) : c.O) ^ n • h = 0) → Nat.card H ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) → ∀ z : H, (∀ x : c.O, x • z = 0 → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ h : H, ∃ x : c.O, m • h = x • z := by
  intro l _ c C r
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hfin : ∀ k : ℕ, Finite (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ k)) := fun k =>
    (UpperTheory.V.X.So.levFacts l c.O _ (pow_ne_zero k hl0) _ ⟨LinearEquiv.refl _ _⟩).1
  refine ⟨(C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ r))).factorial, Nat.factorial_pos _, ?_⟩
  intro n H _ _ _ hkill hcard z hann h
  set L : c.O := ((l : ℕ) : c.O) with hL
  haveI := hfin n
  haveI := hfin r
  let f : UpperTheory.V.X.Lev (L ^ n) →ₗ[c.O] H :=
    (Ideal.span {L ^ n}).liftQ (LinearMap.toSpanSingleton c.O H z) (by
      rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hkill z)
  have hf : ∀ x : c.O, f (UpperTheory.V.X.Lev.mk (L ^ n) x) = x • z := fun x => rfl
  let g : UpperTheory.V.X.Lev (L ^ r) →ₗ[c.O] UpperTheory.V.X.Lev (L ^ n) :=
    (Ideal.span {L ^ r}).liftQ ((L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n)) (by
      rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul,
        UpperTheory.V.X.Lev.mk_eq_zero, smul_eq_mul, ← pow_add]
      exact pow_dvd_pow _ (by omega))
  have hg : ∀ w : c.O, g (UpperTheory.V.X.Lev.mk (L ^ r) w) = UpperTheory.V.X.Lev.mk (L ^ n) (L ^ (n - r) * w) := by
    intro w
    show (L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n) w = _
    rw [← map_smul, smul_eq_mul]
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro y hy
    obtain ⟨x, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective (L ^ n) y
    rw [LinearMap.mem_ker, hf] at hy
    obtain ⟨w, rfl⟩ := hann x hy
    exact ⟨UpperTheory.V.X.Lev.mk (L ^ r) w, hg w⟩
  have hK : Nat.card (LinearMap.ker f) ≤ Nat.card (UpperTheory.V.X.Lev (L ^ r)) :=
    (Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hker)).trans
      (Nat.card_le_card_of_surjective _ g.surjective_rangeRestrict)
  have h1 : Nat.card (UpperTheory.V.X.Lev (L ^ n)) =
      Nat.card (LinearMap.ker f) * Nat.card (UpperTheory.V.X.Lev (L ^ n) ⧸ LinearMap.ker f) :=
    Submodule.card_eq_card_quotient_mul_card _
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have h2 : Nat.card H = Nat.card (LinearMap.range f) * Nat.card (H ⧸ LinearMap.range f) :=
    Submodule.card_eq_card_quotient_mul_card _
  have hSpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have hQ : Nat.card (H ⧸ LinearMap.range f) ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ r)) := by
    have : Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) ≤
        (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))) * Nat.card (LinearMap.range f) := by
      calc Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) = Nat.card H := by
              rw [h2, mul_comm]
        _ ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ n)) := hcard
        _ = C * (Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f)) := by rw [h1]
        _ ≤ C * (Nat.card (UpperTheory.V.X.Lev (L ^ r)) * Nat.card (LinearMap.range f)) := by gcongr
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hSpos
  haveI : Finite (H ⧸ LinearMap.range f) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hdvd : Nat.card (H ⧸ LinearMap.range f) ∣ (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial :=
    Nat.dvd_factorial Nat.card_pos hQ
  obtain ⟨k, hk⟩ := hdvd
  have hmem : (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial • h ∈ LinearMap.range f := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_nsmul, hk, mul_comm, mul_nsmul,
      card_nsmul_eq_zero']
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨x, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective (L ^ n) y
  exact ⟨x, by rw [← hy, hf]⟩

end GlobalTheory.CycIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicHomSmallOnDeepCongruenceSubgroups
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lam_small_of_deep_congruence : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → Continuous lam → r.ker ≤ lam.ker → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖) → ‖(lam g).toAdd‖ ≤ ε := by
  intro l _ Γ _ _ _ r lam hr hlam hker ε hε
  have hl : ‖((l:ℕ) : Qbar l)‖ = (l:ℝ)⁻¹ := by
    have : ((l:ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    simp [Padic.norm_p]
  have hl1 : ‖((l:ℕ) : Qbar l)‖ < 1 := by
    rw [hl]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  by_contra hcon
  push_neg at hcon
  set F : ℕ → Set Γ := fun N => {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} ∩ {g | ε ≤ ‖(lam g).toAdd‖} with hF
  have hcm : Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) := (Units.continuous_val.comp hr).sub continuous_const
  have hclosed : ∀ N, IsClosed (F N) := by
    intro N
    refine IsClosed.inter ?_ ?_
    · have : {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} = ⋂ i, ⋂ j, {g | ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} := by
        ext g; simp
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_le (continuous_norm.comp ((continuous_apply j).comp ((continuous_apply i).comp hcm))) continuous_const
    · exact isClosed_le continuous_const (continuous_norm.comp (continuous_toAdd.comp hlam))
  have hmono : ∀ N, F (N+1) ⊆ F N := by
    intro N g hg
    refine ⟨fun i j => (hg.1 i j).trans ?_, hg.2⟩
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ N)
  have hne : ∀ N, (F N).Nonempty := by
    intro N
    obtain ⟨g, hg1, hg2⟩ := hcon N
    exact ⟨g, hg1, hg2.le⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono hne (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hg
  have hzero : ∀ i j, ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j = 0 := by
    intro i j
    by_contra hx
    have hpos : 0 < ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ := norm_pos_iff.mpr hx
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hl1
    have := (hg N).1 i j
    rw [norm_pow] at this
    linarith
  have hrg : r g = 1 := by
    apply Units.ext
    have : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1 = 0 := by
      ext i j; exact hzero i j
    simpa [sub_eq_zero] using this
  have hlg : lam g = 1 := hker (MonoidHom.mem_ker.mpr hrg)
  have h2 : ε ≤ ‖(lam g).toAdd‖ := (hg 0).2
  rw [hlg] at h2
  simp at h2
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducible
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory

theorem ad_invariant_eq_zero_of_isIrr {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ]
    (ρ : Γ →* GL (Fin 2) K) (hρ : IsIrr ρ) (v : Fin 3 → K) (hv : ∀ g, ad (ρ g) *ᵥ v = v) : v = 0 := by
  set Y : Matrix (Fin 2) (Fin 2) K := ofCoord v with hY

  have hcomm : ∀ g, ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
    intro g
    have h1 : coord ((ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = coord Y := by
      rw [coord_conj_ofCoord, hv g, coord_ofCoord]
    have h2 : (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Y := by
      have := congrArg ofCoord h1
      rwa [ofCoord_coord (by rw [trace_conj, trace_ofCoord]), ofCoord_coord (trace_ofCoord v)] at this
    calc (ρ g : Matrix (Fin 2) (Fin 2) K) * Y
        = (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_assoc _ _ (ρ g : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by rw [h2]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Y)
  set W := Module.End.eigenspace (Matrix.toLin' Y) μ with hW
  have hWne : W ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
  have hWinv : IsInv ρ W := by
    intro g x hx
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← hcomm g, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  have hWtop : W = ⊤ := by
    rcases hρ.2.2 W le_top hWinv with h | h
    · exact absurd h hWne
    · exact h
  have hYμ : Y = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    have hx : (Pi.single j 1 : Fin 2 → K) ∈ W := by rw [hWtop]; trivial
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_single_one] at hx
    have := congrFun hx i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  have htr : (2 : K) * μ = 0 := by
    have := trace_ofCoord v
    rw [← hY, hYμ, Matrix.trace_smul, Matrix.trace_one] at this
    simpa [mul_comm] using this
  have hμ0 : μ = 0 := by
    rcases mul_eq_zero.mp htr with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hY0 : Y = 0 := by rw [hYμ, hμ0, zero_smul]
  rw [← coord_ofCoord v, ← hY, hY0]
  ext i; fin_cases i <;> simp [coord]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SrcOfRepIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SrcConj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem tw_conj (r r' : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : GL (Fin n) k)
    (h : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) : tw r' χ s = g * tw r χ s * g⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, tw_val, tw_val, h s, Units.val_mul, Units.val_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem isSSRep_conj (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (h : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsSSRep r) : IsSSRep r' := by
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ?_ ?_ hr
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · intro s
    rw [h s, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

theorem att_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k' : ℕ}
    (f : Newform k') (V V' : G ℚ Ω →* GL (Fin 2) (Qbar l)) (g : GL (Fin 2) (Qbar l))
    (h : ∀ s, V' s = g * V s * g⁻¹) (hV : f.Att ι V) : f.Att ι V' := by
  refine ⟨isSSRep_conj V V' g h hV.1, hV.2.mono fun w hw A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hw A hA
  refine ⟨fun s hs => by rw [h s, hI s hs, mul_one, mul_inv_cancel], fun σ hσ => ?_⟩
  rw [← hF σ hσ, h σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end GlobalTheory.Ord2.SrcConj

end
end

