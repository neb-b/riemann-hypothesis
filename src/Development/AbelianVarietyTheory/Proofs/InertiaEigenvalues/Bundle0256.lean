module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersLevelOneEqSumZetaPow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.Cyc.FirstLevel

open Polynomial GlobalTheory.Cyc.IntBasis

variable {l : ℕ} [Fact l.Prime]

private theorem norm_primitiveRoot_sub_one' (ζ : Om l) (hζ : IsPrimitiveRoot ζ l) :
    ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1)) := by
  have h1 : IsPrimitiveRoot (algebraMap (Om l) (PadicComplex l) ζ) (l ^ 1) := by
    rw [pow_one]
    exact hζ.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  have h2 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl _ h1
  have h3 : ‖algebraMap (Om l) (PadicComplex l) (ζ - 1)‖ = ‖ζ - 1‖ :=
    PadicComplex.norm_extends l (ζ - 1)
  rw [map_sub, map_one, h2] at h3
  rw [← h3]
  simp

theorem norm_term (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : Om l) (hz : z ∈ K0 K) (h0 : z ≠ 0) :
    ∃ n : ℤ, ‖z‖ = (l : ℝ) ^ n ∧ ∀ a : ℕ, ‖z * (ζ - 1) ^ a‖ =
        (l : ℝ) ^ (((n * (l - 1) - a : ℤ) : ℝ) / ((l : ℝ) - 1)) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (0 : ℝ) < l := by linarith
  have hm : (l : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K z hz h0
  refine ⟨n, hn, fun a => ?_⟩
  rw [norm_mul, norm_pow, hn, norm_primitiveRoot_sub_one' ζ hζ, ← Real.rpow_intCast,
    ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_add hl0]
  congr 1
  push_cast
  field_simp
  try ring

theorem term_le (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : ℕ → Om l) (hz : ∀ a, z a ∈ K0 K) (a : ℕ) (ha : a < l - 1) :
    ‖z a * (ζ - 1) ^ a‖ ≤ ‖∑ b ∈ Finset.range (l - 1), z b * (ζ - 1) ^ b‖ := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  refine norm_le_norm_sum (Finset.range (l - 1)) (fun b => z b * (ζ - 1) ^ b) ?_ a
    (Finset.mem_range.2 ha)
  intro b hb c hc hbc hb0 hc0 heq
  have hb' : z b ≠ 0 := fun h => hb0 (by simp [h])
  have hc' : z c ≠ 0 := fun h => hc0 (by simp [h])
  have heq' : ‖z b * (ζ - 1) ^ b‖ = ‖z c * (ζ - 1) ^ c‖ := heq
  obtain ⟨nb, -, hnb⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ (z b) (hz b) hb'
  obtain ⟨nc, -, hnc⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ (z c) (hz c) hc'
  rw [hnb b, hnc c] at heq'
  have he := le_antisymm ((Real.rpow_le_rpow_left_iff hl1).1 heq'.le)
    ((Real.rpow_le_rpow_left_iff hl1).1 heq'.ge)
  rw [div_left_inj' hm.ne'] at he
  have he' : nb * ((l : ℤ) - 1) - b = nc * ((l : ℤ) - 1) - c := by exact_mod_cast he
  rw [Finset.mem_range] at hb hc
  have hb2 : (b : ℤ) < (l : ℤ) - 1 := by omega
  have hc2 : (c : ℤ) < (l : ℤ) - 1 := by omega
  have hb3 : (0 : ℤ) ≤ b := by omega
  have hc3 : (0 : ℤ) ≤ c := by omega
  have hm' : (0 : ℤ) ≤ (l : ℤ) - 1 := by omega
  apply hbc
  rcases lt_trichotomy nb nc with h | h | h
  · exfalso
    nlinarith [mul_le_mul_of_nonneg_right (show nb + 1 ≤ nc by omega) hm']
  · subst h
    have : (b : ℤ) = c := by linarith
    exact_mod_cast this
  · exfalso
    nlinarith [mul_le_mul_of_nonneg_right (show nc + 1 ≤ nb by omega) hm']

theorem coeff_le (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : Om l) (hz : z ∈ K0 K) (a : ℕ) (ha : a < l - 1) (h : ‖z * (ζ - 1) ^ a‖ ≤ 1) :
    ‖z‖ ≤ 1 := by
  by_cases h0 : z = 0
  · rw [h0, norm_zero]
    exact zero_le_one
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  obtain ⟨n, hn, hna⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ z hz h0
  rw [hna a] at h
  have h' := (Real.rpow_le_rpow_left_iff hl1).1 (h.trans_eq (Real.rpow_zero (l : ℝ)).symm)
  rw [div_le_iff₀ hm, zero_mul] at h'
  have key : n * ((l : ℤ) - 1) - a ≤ 0 := by exact_mod_cast h'
  have ha' : (a : ℤ) < (l : ℤ) - 1 := by omega
  have hn0 : n ≤ 0 := by
    by_contra hc
    have hm' : (0 : ℤ) ≤ (l : ℤ) - 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ n by omega) hm']
  rw [hn]
  exact zpow_le_one_of_nonpos₀ hl1.le hn0

theorem exists_poly (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (x : Om l) (hx : x ∈ Ks K 1) :
    ∃ p : (↥(K0 K))[X], p.natDegree < l - 1 ∧ aeval ζ p = x := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have : NeZero l := ⟨by omega⟩
  have hint : IsIntegral (↥(K0 K)) ζ := by
    refine IsIntegral.of_pow (n := l) (by omega) ?_
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  have hle : Ks K 1 ≤ (IntermediateField.adjoin (↥(K0 K)) {ζ}).restrictScalars ℚ_[l] := by
    unfold Ks
    refine sup_le ?_ ?_
    · intro y hy
      rw [IntermediateField.mem_restrictScalars]
      exact IntermediateField.algebraMap_mem _ (⟨y, hy⟩ : ↥(K0 K))
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y ^ l = 1 := by simpa using hy
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy'
      rw [SetLike.mem_coe, IntermediateField.mem_restrictScalars]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self _ ζ) i
  have hx' : x ∈ (IntermediateField.adjoin (↥(K0 K)) {ζ}).toSubalgebra :=
    (IntermediateField.mem_restrictScalars ℚ_[l]).1 (hle hx)
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx'
  obtain ⟨p, rfl⟩ := hx'
  have hmon := minpoly.monic hint
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly (↥(K0 K)) ζ).natDegree ≤ l - 1 := by
    have hdvd : minpoly (↥(K0 K)) ζ ∣ Polynomial.cyclotomic l (↥(K0 K)) := by
      apply minpoly.dvd
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
      exact hζ.isRoot_cyclotomic (by omega)
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.cyclotomic_ne_zero l (↥(K0 K)))
    rwa [Polynomial.natDegree_cyclotomic, Nat.totient_prime (Fact.out : l.Prime)] at this
  refine ⟨p %ₘ minpoly (↥(K0 K)) ζ, ?_, ?_⟩
  · have hne : minpoly (↥(K0 K)) ζ ≠ 1 := by
      intro h
      rw [h, Polynomial.natDegree_one] at hpos
      exact lt_irrefl 0 hpos
    exact lt_of_lt_of_le (Polynomial.natDegree_modByMonic_lt p hmon hne) hdeg
  · exact Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)

end GlobalTheory.Cyc.FirstLevel


open Polynomial GlobalTheory.Cyc.IntBasis in
theorem GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : Om l), IsPrimitiveRoot ζ l → ∀ α : Om l, α ∈ Ks K 1 → ‖α‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ K0 K ∧ ‖y a‖ ≤ 1) ∧ α = ∑ a : Fin l, ζ ^ (a : ℕ) * y a := by
  intro l _ K ζ hζ α hα hα1
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨p, hpdeg, hp⟩ := GlobalTheory.Cyc.FirstLevel.exists_poly K ζ hζ α hα
  set q := Polynomial.taylor (1 : ↥(K0 K)) p with hq
  have hqdeg : q.natDegree < l - 1 := by
    rw [hq, Polynomial.natDegree_taylor]
    exact hpdeg
  let z : ℕ → Om l := fun b => ((q.coeff b : ↥(K0 K)) : Om l)
  have hzK : ∀ b, z b ∈ K0 K := fun b => (q.coeff b).2
  have hsum : α = ∑ b ∈ Finset.range (l - 1), z b * (ζ - 1) ^ b := by
    rw [← hp]
    have h1 : aeval ζ p = aeval (ζ - 1) q := by
      rw [hq, aeval_taylor']
      congr 1
      simp
    rw [h1, Polynomial.aeval_eq_sum_range' hqdeg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Algebra.smul_def]
    rfl
  have hzle : ∀ b, ‖z b‖ ≤ 1 := by
    intro b
    by_cases hb : b < l - 1
    · apply GlobalTheory.Cyc.FirstLevel.coeff_le K ζ hζ (z b) (hzK b) b hb
      calc ‖z b * (ζ - 1) ^ b‖ ≤ ‖∑ c ∈ Finset.range (l - 1), z c * (ζ - 1) ^ c‖ :=
            GlobalTheory.Cyc.FirstLevel.term_le K ζ hζ z hzK b hb
        _ = ‖α‖ := by rw [← hsum]
        _ ≤ 1 := hα1
    · have hc : q.coeff b = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [z, hc]
  let Q : (intRing (K0 K))[X] := ∑ b ∈ Finset.range (l - 1),
    Polynomial.C (⟨z b, ⟨hzK b, hzle b⟩⟩ : intRing (K0 K)) * (Polynomial.X - Polynomial.C 1) ^ b
  have hQdeg : Q.natDegree < l := by
    have : Q.natDegree ≤ l - 2 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro b hb
      rw [Finset.mem_range] at hb
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine Polynomial.natDegree_pow_le.trans ?_
      rw [Polynomial.natDegree_X_sub_C]
      omega
    omega
  have hQ : aeval ζ Q = α := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, Polynomial.aeval_C, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      map_one]
    rfl
  have hmem : ∀ s : intRing (K0 K), (s : Om l) ∈ K0 K ∧ ‖(s : Om l)‖ ≤ 1 := fun s => s.2
  refine ⟨fun a : Fin l => ((Q.coeff (a : ℕ) : intRing (K0 K)) : Om l),
    fun a => hmem _, ?_⟩
  rw [← hQ, Polynomial.aeval_eq_sum_range' hQdeg, Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Algebra.smul_def, mul_comm]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem tmul_gen_cancel (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    (e : T.V) (he : e ≠ 0) (heT : e ∈ T.L.T) (e₀ : ↥T.L.T) (h₀ : Submodule.span O {e₀} = ⊤)
    {R : Type} [CommRing R] [Algebra O R] (r r' : R)
    (h : (r ⊗ₜ[O] e₀ : TW R T) = r' ⊗ₜ[O] e₀) : r = r' := by
  have hne : (e₀ : T.V) ≠ 0 := by
    intro h0
    have hm : (⟨e, heT⟩ : ↥T.L.T) ∈ Submodule.span O {e₀} := by rw [h₀]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    apply he
    have := congrArg Subtype.val hc
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro c hc
      have h1 : c • (e₀ : T.V) = 0 := congrArg Subtype.val hc
      rw [← algebraMap_smul LL c, smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact hO (by rw [h1, map_zero])
      · exact absurd h1 hne
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h₀]
  let φ := LinearEquiv.ofBijective _ hb
  have hφ : φ.symm e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [φ]
  have := congrArg (fun z => TensorProduct.rid O R (LinearMap.lTensor R φ.symm.toLinearMap z)) h
  simpa [hφ] using this

theorem etTie_io_act (hO : Function.Injective (algebraMap O LL)) {W : LocWach PD LL O v n}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {incl : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW incl φR gR πA) (g : G) (a : LetA O n) :
    incl (E.io (W.γA (W.resΓ g) a)) = gR g (incl (E.io a)) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
  have h1 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by
    simp [TWact, hact]
  have h2 := E.jD_act W.one g (algebraMap (LetA O n) W.EE a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, hj, TWact_smul, h1, W.γE_ext, E.ioE_ext,
    E.ioE_ext, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h2
  exact tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

end Generic


set_option synthInstance.maxHeartbeats 400000 in
theorem io_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  intro l _ P AI K s LL h W E g a
  exact etTie_io_act Subtype.val_injective E.tie g a

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaTmulOneMem
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HfZero

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

include PD in
theorem nontrivial_cris : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact Submodule.zero_mem _

include PD in
theorem tmul_one_inj {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have := nontrivial_cris PD
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qp B)
    (LinearMap.ker_eq_bot.2 (algebraMap Qp B).injective)
  have h1 : r 1 = 1 := by simpa using LinearMap.congr_fun hr 1
  have := congrArg (fun z => TensorProduct.rid Qp V (r.lTensor V z)) h
  simpa [h1] using this

theorem frob_act (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB, actVB, PD.φ_comm]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem iota_act (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem frob_tmul_one (v : V) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : B) := by
  simp [φVB]

theorem act_tmul_one (g : G) (v : V) :
    actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem tmul_mem_filV (v : V) (a : ℤ) (b : BdR) (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

theorem iota_tmul_one_mem (v : V) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) ∈ FilV PD (LL := LL) (V := V) 0 := by
  have : ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : BdR) := by simp [ιV]
  rw [this]
  exact tmul_mem_filV PD v 0 1 PD.one_mem

theorem filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) :=
  antitone_int_of_succ_le (filV_succ_le PD)

theorem exists_mem_filV (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, tmul_mem_filV PD v a b ha⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem mem_dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_ddR_iff (x : V ⊗[Qp] BdR) : x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem iota_mem_ddR (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) x ∈ DdR PD ρ := by
  rw [mem_ddR_iff]
  intro g
  rw [← iota_act, (mem_dcris_iff PD ρ x).1 hx g]

end

theorem z1f_le_b1 : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], TateFilteredInvariants PD → fontCore PD → GoodO (Qp := Qp) LL O → ∀ A : GRep G Qp LL O, IsDR PD A.ρ → DdR PD A.ρ ≤ FilV PD (LL := LL) (V := A.V) 0 → H0V A.ρ = ⊥ → finiteCocycles PD A.ρ ≤ B1 A.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ LL _ _ _ O _ _ h5 hfont hO A
    hdR hFil hH0 c hc
  obtain ⟨-, x, hx⟩ := hc
  have : Module.Finite LL ↥(Dcris PD A.ρ) := (hfont LL O hO A).1.1
  let ψ : A.V ⊗[Qp] B →ₗ[LL] A.V ⊗[Qp] B := LinearMap.id - φVB PD (LL := LL) (V := A.V)
  have hψ : ∀ z, ψ z = z - φVB PD (LL := LL) (V := A.V) z := fun z => rfl
  have hstab : ∀ z ∈ Dcris PD A.ρ, ψ z ∈ Dcris PD A.ρ := by
    intro z hz
    rw [mem_dcris_iff] at hz ⊢
    intro g
    rw [hψ, map_sub, ← frob_act, hz g]
  have hinj : Function.Injective (ψ.restrict hstab) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨z, hz⟩ h0
    have h1 : ψ z = 0 := congrArg Subtype.val h0
    rw [hψ, sub_eq_zero] at h1
    obtain ⟨v, rfl⟩ := exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD (LL := LL) z h1.symm
      (hFil (iota_mem_ddR PD A.ρ z hz))
    have hv : v ∈ H0V A.ρ := by
      simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply tmul_one_inj PD
      rw [← act_tmul_one PD A.ρ, (mem_dcris_iff PD A.ρ _).1 hz g]
    rw [hH0, Submodule.mem_bot] at hv
    subst hv
    exact Subtype.ext (TensorProduct.zero_tmul _ _)
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hy : ψ x ∈ Dcris PD A.ρ := by
    rw [mem_dcris_iff]
    intro g
    have h1 := frob_tmul_one PD (LL := LL) (c g)
    rw [hx g, map_sub, frob_act] at h1
    rw [hψ, map_sub, sub_eq_sub_iff_sub_eq_sub, h1]
  obtain ⟨⟨x', hx'⟩, hxx⟩ := hsurj ⟨ψ x, hy⟩
  have h2 : ψ x' = ψ x := congrArg Subtype.val hxx
  have hfix : φVB PD (LL := LL) (V := A.V) (x - x') = x - x' := by
    rw [hψ, hψ, sub_eq_sub_iff_sub_eq_sub] at h2
    rw [map_sub, ← neg_sub x' x, h2, neg_sub]
  obtain ⟨a, ha⟩ := exists_mem_filV PD (LL := LL) (ιV PD (LL := LL) (V := A.V) x)
  obtain ⟨w, ⟨hw, -⟩, hw'⟩ := h5 LL O hO A hdR a 0 _ ha (fun g => by
    rw [← iota_act, ← map_sub, ← hx g]
    exact iota_tmul_one_mem PD (c g))
  have hF : ιV PD (LL := LL) (V := A.V) (x - x') ∈ FilV PD (LL := LL) (V := A.V) 0 := by
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hw' (hFil hw))
      (hFil (iota_mem_ddR PD A.ρ x' hx'))
    rwa [sub_add_cancel, ← map_sub] at h3
  obtain ⟨v, hv⟩ := exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD (LL := LL) _ hfix hF
  refine ⟨v, funext fun g => ?_⟩
  change A.ρ g v - v = c g
  apply tmul_one_inj PD
  rw [hx g, TensorProduct.sub_tmul, ← act_tmul_one PD A.ρ, ← hv, map_sub,
    (mem_dcris_iff PD A.ρ _).1 hx' g]
  abel

end GlobalTheory.HfZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntExistsPowSubNormLeOfExactLevelStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' : ∀ (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ), 1 ≤ m → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m → ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m → ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  first | exact @GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level | exact GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level | (intros; apply GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwiseStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serreTate_linearIndependent_of_weightwise : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l)), (∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E)) → ∀ (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ), (∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k) → (∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) → ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) → LinearIndependent (PadicComplex l) e := by
  first | exact @GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | exact GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | (intros; apply GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise <;> assumption)
end

