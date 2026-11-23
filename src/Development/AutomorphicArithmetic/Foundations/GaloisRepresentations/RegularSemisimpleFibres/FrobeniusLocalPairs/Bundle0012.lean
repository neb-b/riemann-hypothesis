module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.BallLev
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ScalarCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormDiag
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ConjEntry
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem conj_entry (d : Fin n → kˣ) (g : GL (Fin n) k) (i j : Fin n) :
    (((diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (d i : k)⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j * (d j : k) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

private theorem conj_ball {r : ValueGroupWithZero k} {d : Fin n → kˣ} (hd : ∀ i, valuation k (d i : k) = 1)
    {g : GL (Fin n) k} (hg : g ∈ ball n r) :
    (diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d ∈ ball n r := by
  intro i j
  rw [conj_entry]
  by_cases h : i = j
  · subst h
    have e : (d i : k)⁻¹ * (g : Matrix (Fin n) (Fin n) k) i i * (d i : k) = (g : Matrix (Fin n) (Fin n) k) i i := by
      have := (d i).ne_zero
      field_simp
    rw [e]
    exact hg i i
  · have := hg i j
    rw [Matrix.one_apply_ne h, sub_zero] at this ⊢
    rw [map_mul, map_mul, hd j, mul_one, map_inv₀, hd i, inv_one, one_mul]
    exact this

private theorem diag_ball {r : ValueGroupWithZero k} {a : GL (Fin n) k} (ha : a ∈ ball n r) {d : Fin n → kˣ}
    (hd : ∀ i, valuation k (d i : k) = 1)
    (h : ∀ i, ((a * diagT k (Fin n) d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = 1) :
    diagT k (Fin n) d ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases hij : i = j
  · subst hij
    have e := h i
    rw [Units.val_mul, val_diagT, Matrix.mul_diagonal] at e
    have e' : (d i : k) - 1 = (d i : k) * -((a : Matrix (Fin n) (Fin n) k) i i - 1) := by
      linear_combination e
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, e', map_mul, hd i, one_mul, Valuation.map_neg]
    have := ha i i
    rwa [Matrix.one_apply_eq] at this
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero, map_zero]
    exact zero_le'

end

theorem levOf : LevOf := by
  intro k _ _ _ _ n r h0 h1 D hDc hDv
  obtain ⟨B, hB, hBo, hBc⟩ := ballSub k n r h0 h1
  obtain ⟨hBI, hBd⟩ := ballLev k n r h0 h1 B hB
  have mB : ∀ {g : GL (Fin n) k}, g ∈ B ↔ g ∈ ball n r := fun {g} => by rw [← SetLike.mem_coe, hB]
  have hconj : ∀ d ∈ D, ∀ g ∈ B, (diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d ∈ B :=
    fun d hd g hg => mB.2 (conj_ball (hDv d hd) (mB.1 hg))
  have hconj' : ∀ d ∈ D, ∀ g ∈ B, diagT k (Fin n) d * g * (diagT k (Fin n) d)⁻¹ ∈ B := fun d hd g hg => by
    have := hconj d⁻¹ (D.inv_mem hd) g hg
    rwa [map_inv, inv_inv] at this
  have hcomm : ∀ s t : Fin n → kˣ, diagT k (Fin n) s * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) s :=
    fun s t => by rw [← map_mul, ← map_mul, mul_comm]
  let K : Subgroup (GL (Fin n) k) :=
    { carrier := {g | ∃ a ∈ B, ∃ d ∈ D, g = a * diagT k (Fin n) d}
      one_mem' := ⟨1, B.one_mem, 1, D.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, d, hd, rfl⟩ ⟨a', ha', d', hd', rfl⟩
        refine ⟨a * (diagT k (Fin n) d * a' * (diagT k (Fin n) d)⁻¹), B.mul_mem ha (hconj' d hd a' ha'), d * d',
          D.mul_mem hd hd', ?_⟩
        rw [map_mul]
        group
      inv_mem' := by
        rintro _ ⟨a, ha, d, hd, rfl⟩
        refine ⟨(diagT k (Fin n) d)⁻¹ * a⁻¹ * diagT k (Fin n) d, hconj d hd _ (B.inv_mem ha), d⁻¹, D.inv_mem hd, ?_⟩
        rw [map_inv]
        group }
  have hK : ∀ {g}, g ∈ K ↔ ∃ a ∈ B, ∃ d ∈ D, g = a * diagT k (Fin n) d := Iff.rfl
  have hBK : B ≤ K := fun a ha => ⟨a, ha, 1, D.one_mem, by simp⟩
  have hDK : ∀ d ∈ D, diagT k (Fin n) d ∈ K := fun d hd => ⟨1, B.one_mem, d, hd, by simp⟩
  have hK1 : ∀ g ∈ K, (∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1) → g ∈ B := by
    rintro _ ⟨a, ha, d, hd, rfl⟩ h
    exact B.mul_mem ha (mB.2 (diag_ball (mB.1 ha) (hDv d hd) h))
  have hdc : Continuous (diagT k (Fin n)) := (continuous_leviEmb k _).comp (continuous_leviTorus k (Fin n))
  refine ⟨K, fun g => ⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨a, ha, d, hd, rfl⟩
    exact ⟨a, mB.1 ha, d, hd, rfl⟩
  · rintro ⟨a, ha, d, hd, rfl⟩
    exact ⟨a, mB.2 ha, d, hd, rfl⟩
  · have := (hBc.prod hDc).image (f := fun p : GL (Fin n) k × (Fin n → kˣ) => p.1 * diagT k (Fin n) p.2)
      (continuous_fst.mul (hdc.comp continuous_snd))
    convert this using 1
    ext g
    constructor
    · rintro ⟨a, ha, d, hd, rfl⟩
      exact ⟨(a, d), ⟨ha, hd⟩, rfl⟩
    · rintro ⟨⟨a, d⟩, ⟨ha, hd⟩, rfl⟩
      exact ⟨a, ha, d, hd, rfl⟩
  · exact Subgroup.isOpen_mono hBK hBo
  · rintro _ ⟨a, ha, d, hd, rfl⟩
    obtain ⟨u, hu, d', hd', c, hc, e⟩ := hBI.fact a ha
    refine ⟨u, ⟨hBK hu.1, hu.2⟩, d' * d, ?_, (diagT k (Fin n) d)⁻¹ * c * diagT k (Fin n) d,
      ⟨hBK (hconj d hd c hc.1), ?_⟩, ?_⟩
    · rw [map_mul]
      exact K.mul_mem (hBK hd') (hDK d hd)
    · have := GlobalTheory.IwahoriTraceProof.conj_mem_unipBLower d⁻¹ hc.2
      rwa [map_inv, inv_inv] at this
    · rw [e, map_mul]
      group
  · intro t ht u hu
    exact hBK (hBI.up t ht u ⟨hK1 u hu.1 ((mem_unipB k).1 hu.2).2, hu.2⟩)
  · intro t ht c hc
    exact hBK (hBI.low t ht c ⟨hK1 c hc.1 (GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hc.2).2, hc.2⟩)
  · intro t
    ext g
    constructor
    · rintro ⟨_, ⟨a, ha, d, hd, rfl⟩, _, ⟨a', ha', d', hd', rfl⟩, rfl⟩
      refine ⟨a, mB.1 ha, (diagT k (Fin n) d')⁻¹ * a' * diagT k (Fin n) d', mB.1 (hconj d' hd' a' ha'),
        t * (d * d'), ⟨d * d', D.mul_mem hd hd', rfl⟩, ?_⟩
      have e := hcomm d t
      rw [map_mul, map_mul]
      calc a * diagT k (Fin n) d * diagT k (Fin n) t * (a' * diagT k (Fin n) d')
          = a * (diagT k (Fin n) d * diagT k (Fin n) t) * (a' * diagT k (Fin n) d') := by group
        _ = a * (diagT k (Fin n) t * diagT k (Fin n) d) * (a' * diagT k (Fin n) d') := by rw [e]
        _ = _ := by group
    · rintro ⟨a, ha, b, hb, _, ⟨d, hd, rfl⟩, rfl⟩
      refine ⟨a * diagT k (Fin n) d, ⟨a, mB.2 ha, d, hd, rfl⟩, b, hBK (mB.2 hb), ?_⟩
      have e := hcomm d t
      rw [map_mul]
      calc a * (diagT k (Fin n) t * diagT k (Fin n) d) * b
          = a * (diagT k (Fin n) d * diagT k (Fin n) t) * b := by rw [e]
        _ = _ := by group

end UpperTheory.Gal.InertialTypesAlt.L
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemLoc
section
open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.elemLoc :
    UpperTheory.Gal.InertialTypesAlt.L.ElemLoc := elemLoc_of suppE oneField reps normOpen normDiag align volRatio
  (fun E _ _ _ _ n r h0 h1 => UpperTheory.ConvolutionTheory.Loc.ballSub E n r h0 h1)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormFin
section
private theorem UpperTheory.Gal.InertialTypesAlt.L.range_eq_ker_of_exact {U : Type} [CommGroup U] [Finite U]
    (N D : U →* U) (h1 : N.range ≤ D.ker) (h2 : N.ker = D.range) : N.range = D.ker := by
  apply Subgroup.eq_of_le_of_card_ge h1
  have c1 := Subgroup.card_mul_index N.ker
  have c2 := Subgroup.card_mul_index D.ker
  rw [Subgroup.index_ker, h2] at c1
  rw [Subgroup.index_ker] at c2
  have hp : 0 < Nat.card D.range := Nat.card_pos
  have e : Nat.card D.range * Nat.card N.range = Nat.card D.range * Nat.card D.ker := by
    nlinarith
  exact (Nat.eq_of_mul_eq_mul_left hp e).ge

theorem UpperTheory.Gal.InertialTypesAlt.L.normFin :
    UpperTheory.Gal.InertialTypesAlt.L.NormFin := by
  intro F₀ F₁ _ _ _ _ _ sb hsb A _ _ _ τ hτ hper x hx hfix
  have H := UpperTheory.Gal.InertialTypesAlt.L.hilbert_ninety_frobenius_twisted_finite_algebra F₀ F₁ sb hsb A τ hτ hper
  generalize Module.finrank F₀ F₁ = d at hper H ⊢
  have hit : ∀ i (a b : A), (⇑τ)^[i] (a * b) = (⇑τ)^[i] a * (⇑τ)^[i] b := by
    intro i
    induction i with
    | zero => intro a b; rfl
    | succ n ih => intro a b; simp only [Function.iterate_succ_apply', ih, map_mul]
  have hit1 : ∀ i, (⇑τ)^[i] (1 : A) = 1 := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]
  have hmul : ∀ a b : A, UpperTheory.Gal.InertialTypesAlt.L.itN τ d (a * b)
      = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a * UpperTheory.Gal.InertialTypesAlt.L.itN τ d b := by
    intro a b
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, hit, Finset.prod_mul_distrib]
  have hone : UpperTheory.Gal.InertialTypesAlt.L.itN τ d 1 = 1 := by
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, hit1, Finset.prod_const_one]
  have hinv : ∀ a : A, τ (UpperTheory.Gal.InertialTypesAlt.L.itN τ d a) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a := by
    intro a
    have ha := hper a
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, map_prod]
    have e : ∀ i, τ ((⇑τ)^[i] a) = (⇑τ)^[i + 1] a :=
      fun i => (Function.iterate_succ_apply' _ _ _).symm
    simp only [e]
    cases d with
    | zero => simp
    | succ k =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (⇑τ)^[i] a), ha]
      rfl
  have hτN : ∀ a : A, UpperTheory.Gal.InertialTypesAlt.L.itN τ d (τ a) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a := by
    intro a
    rw [← hinv a]
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'])
  obtain ⟨N, hN⟩ : ∃ N : Aˣ →* Aˣ, ∀ u, (N u : A) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d u :=
    ⟨Units.map { toFun := UpperTheory.Gal.InertialTypesAlt.L.itN τ d, map_one' := hone, map_mul' := hmul },
      fun u => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Aˣ →* Aˣ, ∀ u, (T u : A) = τ u :=
    ⟨Units.map (MonoidHomClass.toMonoidHom τ), fun u => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Aˣ →* Aˣ, ∀ u, D u = u / T u := ⟨MonoidHom.id _ / T, fun u => rfl⟩
  have hr : N.range ≤ D.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, hD, div_eq_one]
    ext
    rw [hT, hN, hinv]
  have hk : N.ker = D.range := by
    ext c
    constructor
    · intro hc
      rw [MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one] at hc
      obtain ⟨y, hy⟩ := H c hc
      refine ⟨y, ?_⟩
      rw [hD, div_eq_iff_eq_mul]
      ext
      rw [Units.val_mul, hT]
      exact hy.symm
    · rintro ⟨y, rfl⟩
      rw [MonoidHom.mem_ker, hD, map_div, div_eq_one]
      ext
      rw [hN, hN, hT, hτN]
  have heq := UpperTheory.Gal.InertialTypesAlt.L.range_eq_ker_of_exact N D hr hk
  have hu : hx.unit ∈ D.ker := by
    rw [MonoidHom.mem_ker, hD, div_eq_one]
    ext
    rw [hT, IsUnit.unit_spec, hfix]
  rw [← heq] at hu
  obtain ⟨y, hy⟩ := hu
  exact ⟨y, by rw [← hN, hy, IsUnit.unit_spec]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.RedNorm
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Val

variable {k K : Type} [Field k] [ValuativeRel k] [Field K] [ValuativeRel K] [Algebra k K]
  [ValuativeExtension k K]

private theorem val_le_one_iff (x : k) :
    valuation K (algebraMap k K x) ≤ 1 ↔ valuation k x ≤ 1 := by
  rw [← ValuativeExtension.mapValueGroupWithZero_valuation,
    ← (ValuativeExtension.mapValueGroupWithZero k K).map_one]
  exact ValuativeExtension.mapValueGroupWithZero_strictMono.le_iff_le

private theorem val_eq_one_of_alg {x : k} (hx : valuation K (algebraMap k K x) = 1) :
    valuation k x = 1 := by
  rw [← ValuativeExtension.mapValueGroupWithZero_valuation,
    ← (ValuativeExtension.mapValueGroupWithZero k K).map_one] at hx
  exact ValuativeExtension.mapValueGroupWithZero_strictMono.injective hx

end Val

section Int

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K]
  [ValuativeExtension k K]

private theorem incl_mem_iff (n : ℕ) (g : GL (Fin n) k) : incl K n g ∈ KO K n ↔ g ∈ KO k n := by
  have hmem : ∀ x : k, algebraMap k K x ∈ 𝒪[K] ↔ x ∈ 𝒪[k] := fun x => by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
    exact val_le_one_iff x
  change incl K n g ∈ GroundTheory.Automorphic.GLnLocal.integralGL K n ↔
    g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n
  rw [GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff, GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff,
    ← map_inv]
  simp only [GlobalTheory.LBC.incl_apply, hmem]

private theorem intEl_of_conj (n : ℕ) (γ : GL (Fin n) k) (g : GL (Fin n) K)
    (hg : g⁻¹ * incl K n γ * g ∈ KO K n) : IntEl γ := by
  obtain ⟨y, hy⟩ := hg
  have hM : ((g⁻¹ * incl K n γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (y : Matrix (Fin n) (Fin n) 𝒪[K]).map (algebraMap 𝒪[K] K) := by
    rw [← hy]
    rfl
  have hγ : ((incl K n γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k K) := by
    ext i j
    simp [GlobalTheory.LBC.incl_apply]
  have hinv : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    simp
  have hchar : ((γ : Matrix (Fin n) (Fin n) k).charpoly).map (algebraMap k K) =
      ((y : Matrix (Fin n) (Fin n) 𝒪[K]).charpoly).map (algebraMap 𝒪[K] K) := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, ← hM, Units.val_mul, Units.val_mul,
      Matrix.charpoly_mul_comm, ← mul_assoc, hinv, one_mul, hγ]
  have hdet : algebraMap k K (γ : Matrix (Fin n) (Fin n) k).det =
      algebraMap 𝒪[K] K (y : Matrix (Fin n) (Fin n) 𝒪[K]).det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hM,
      ← hγ, Units.val_mul, Units.val_mul, Matrix.det_units_conj']
  constructor
  · intro i
    rw [← val_le_one_iff (K := K)]
    have h := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hchar
    simp only [Polynomial.coeff_map] at h
    rw [h]
    exact (Valuation.mem_integer_iff _ _).1 ((y : Matrix (Fin n) (Fin n) 𝒪[K]).charpoly.coeff i).2
  · apply val_eq_one_of_alg (K := K)
    rw [hdet]
    exact (Valuation.integer.integers _).one_of_isUnit (y.isUnit.map Matrix.detMonoidHom)

end Int

section Norm

variable {k K : Type} [Field k] [Field K] [Algebra k K]

private theorem aut_pow_finrank [FiniteDimensional k K] (s : K ≃ₐ[k] K) :
    s ^ Module.finrank k K = 1 := by
  have h1 := IntermediateField.finrank_fixedField_eq_card (F := k) (E := K) (Subgroup.zpowers s)
  rw [Nat.card_zpowers] at h1
  rw [← (letI : Module.Free (IntermediateField.fixedField (Subgroup.zpowers s)) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank k (IntermediateField.fixedField (Subgroup.zpowers s)) K), h1,
    pow_mul', pow_orderOf_eq_one, one_pow]

private theorem ofFn_twConj (s : K ≃ₐ[k] K) (n : ℕ) (δ g : GL (Fin n) K) (m : ℕ) :
    (List.ofFn fun j : Fin m => galAct (s ^ (j : ℕ)) n (g⁻¹ * δ * galAct s n g)).prod =
      g⁻¹ * (List.ofFn fun j : Fin m => galAct (s ^ (j : ℕ)) n δ).prod * galAct (s ^ m) n g := by
  induction m with
  | zero => simp [galAct_one]
  | succ m ih =>
    simp only [List.ofFn_succ', List.prod_concat, Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    simp only [map_mul, map_inv]
    rw [pow_succ, galAct_mul, MonoidHom.comp_apply]
    group

private theorem norm_twConj [FiniteDimensional k K] (s : K ≃ₐ[k] K) (n : ℕ) (δ g : GL (Fin n) K) :
    GlobalTheory.LBC.norm k s (g⁻¹ * δ * galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s δ * g := by
  unfold GlobalTheory.LBC.norm
  rw [ofFn_twConj, aut_pow_finrank, galAct_one, MonoidHom.id_apply]

end Norm

section Lift

variable {K : Type} [Field K] [ValuativeRel K] {k F₀ F₁ : Type} [Field k] [Algebra k K] [Field F₀]
  [Field F₁] [Algebra F₀ F₁] {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁} {n : ℕ}

private theorem lift_pow
    (hf : ∀ y : GL (Fin n) 𝒪[K], ∃ y' : GL (Fin n) 𝒪[K],
      GeneralLinearGroup.map (algebraMap 𝒪[K] K) y' = galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) ∧
      GeneralLinearGroup.map rK y' = galAct sb n (GeneralLinearGroup.map rK y))
    (j : ℕ) (y : GL (Fin n) 𝒪[K]) : ∃ y' : GL (Fin n) 𝒪[K],
      GeneralLinearGroup.map (algebraMap 𝒪[K] K) y' =
        galAct (s ^ j) n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) ∧
      GeneralLinearGroup.map rK y' = galAct (sb ^ j) n (GeneralLinearGroup.map rK y) := by
  induction j generalizing y with
  | zero => exact ⟨y, by simp [galAct_one], by simp [galAct_one]⟩
  | succ j ih =>
    obtain ⟨y1, h1, h2⟩ := hf y
    obtain ⟨y2, h3, h4⟩ := ih y1
    refine ⟨y2, ?_, ?_⟩
    · rw [h3, h1, pow_succ, galAct_mul, MonoidHom.comp_apply]
    · rw [h4, h2, pow_succ, galAct_mul, MonoidHom.comp_apply]

private theorem lift_prod
    (hf : ∀ y : GL (Fin n) 𝒪[K], ∃ y' : GL (Fin n) 𝒪[K],
      GeneralLinearGroup.map (algebraMap 𝒪[K] K) y' = galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) ∧
      GeneralLinearGroup.map rK y' = galAct sb n (GeneralLinearGroup.map rK y))
    (y : GL (Fin n) 𝒪[K]) (m : ℕ) : ∃ z : GL (Fin n) 𝒪[K],
      GeneralLinearGroup.map (algebraMap 𝒪[K] K) z =
        (List.ofFn fun j : Fin m =>
          galAct (s ^ (j : ℕ)) n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y)).prod ∧
      GeneralLinearGroup.map rK z =
        (List.ofFn fun j : Fin m => galAct (sb ^ (j : ℕ)) n (GeneralLinearGroup.map rK y)).prod := by
  induction m with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨z, h1, h2⟩ := ih
    obtain ⟨y', h3, h4⟩ := lift_pow hf m y
    refine ⟨z * y', ?_, ?_⟩
    · simp only [List.ofFn_succ', List.prod_concat, Fin.coe_castSucc, Fin.val_last, map_mul, h1, h3]
    · simp only [List.ofFn_succ', List.prod_concat, Fin.coe_castSucc, Fin.val_last, map_mul, h2, h4]

end Lift

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.redNorm :
    UpperTheory.Gal.InertialTypesAlt.L.RedNorm := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb hres n
  obtain ⟨-, hfr⟩ := frobFacts k K F₀ F₁ rk rK s sb hres
  obtain ⟨-, -, hlift⟩ := hfr n
  obtain ⟨-, -, -, -, hformK, hsuppK⟩ := inflFacts K F₁ rK hres.onto₁ n
  obtain ⟨-, -, -, -, hformk, -⟩ := inflFacts k F₀ rk hres.onto₀ n
  have hnormKO : ∀ β ∈ KO K n, GlobalTheory.LBC.norm k s β ∈ KO K n := by
    rintro β ⟨y, rfl⟩
    obtain ⟨z, hz, -⟩ := lift_prod hlift y (Module.finrank k K)
    exact ⟨z, hz⟩
  refine ⟨fun h => incl_mem_iff n h, hnormKO, fun β g => norm_twConj s n β g,
    fun γ g hg => intEl_of_conj n γ g hg, ?_⟩
  intro fb hfb
  obtain ⟨hlv1, hlv2⟩ := liftVal F₀ F₁ sb hres.frob n fb hfb
  refine ⟨?_, ?_⟩
  · intro β hβ γ hγ
    have hγmem : γ ∈ KO k n := (incl_mem_iff n γ).1 (hγ ▸ hnormKO β hβ)
    obtain ⟨y, rfl⟩ := hβ
    obtain ⟨x, rfl⟩ := hγmem
    rw [hformK, hformk]
    apply hlv1
    obtain ⟨z, hz1, hz2⟩ := lift_prod hlift y (Module.finrank F₀ F₁)
    have hz1' : GeneralLinearGroup.map (algebraMap 𝒪[K] K) z =
        incl K n (GeneralLinearGroup.map (algebraMap 𝒪[k] k) x) := by
      rw [hz1, ← hγ, hres.deg]
      rfl
    have hzx : GeneralLinearGroup.map rK z = incl F₁ n (GeneralLinearGroup.map rk x) := by
      ext i j
      have h := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K) i j) hz1'
      simp only [incl_apply] at h ⊢
      exact hres.inc _ _ h
    show IsConj _ _
    rw [show GlobalTheory.LBC.norm F₀ sb (GeneralLinearGroup.map rK y) = GeneralLinearGroup.map rK z from hz2.symm,
      hzx]
  · intro κ hκ y
    have hsκ : galAct s n κ ∈ KO K n := by
      obtain ⟨u, rfl⟩ := hκ
      obtain ⟨u', hu1, -⟩ := hlift u
      exact ⟨u', hu1⟩
    by_cases hy : y ∈ KO K n
    · obtain ⟨w, rfl⟩ := hy
      obtain ⟨u, rfl⟩ := hκ
      obtain ⟨u', hu1, hu2⟩ := hlift u
      rw [← hu1, ← map_inv, ← map_mul, ← map_mul, hformK, hformK, map_mul, map_mul, map_inv, hu2]
      exact hlv2 _ _
    · have hy' : κ⁻¹ * y * galAct s n κ ∉ KO K n := by
        intro h
        apply hy
        have hy2 : y = κ * (κ⁻¹ * y * galAct s n κ) * (galAct s n κ)⁻¹ := by group
        rw [hy2]
        exact mul_mem (mul_mem hκ h) (inv_mem hsκ)
      have h0 : ∀ x, x ∉ KO K n → infl rK (normLift sb fb) x = 0 := fun x hx =>
        by_contra fun h => hx ((hsuppK (normLift sb fb)).2.2 x h)
      rw [h0 _ hy, h0 _ hy']
end
end

