module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNeZeroFiniteLocalZmodPrimePow
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocalTraceNonzero

theorem isUnit_of_cast_ne_zero (l b : ℕ) [Fact l.Prime] (hb : b ≠ 0) (x : ZMod (l ^ b))
    (hx : ZMod.castHom (dvd_pow_self l hb) (ZMod l) x ≠ 0) : IsUnit x := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ne_eq, ZMod.natCast_eq_zero_iff] at hx
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hx))

theorem henselian_of_finite (A : Type) [CommRing A] [Finite A] [IsLocalRing A] :
    HenselianLocalRing A := by
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

theorem exists_trace_ne_zero_adjoinRoot (l : ℕ) [Fact l.Prime] (p : (ZMod l)[X]) (hp : Irreducible p) :
    ∃ z : AdjoinRoot p, Algebra.trace (ZMod l) (AdjoinRoot p) z ≠ 0 := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  haveI : FiniteDimensional (ZMod l) (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  haveI : Algebra.IsSeparable (ZMod l) (AdjoinRoot p) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (ZMod l) (AdjoinRoot p) 1
  exact ⟨z, by rw [hz]; exact one_ne_zero⟩

theorem exists_trace_ne_zero : ∀ (l b e : ℕ) [Fact l.Prime] (B : Type) [CommRing B] [Finite B] [Algebra (ZMod (l ^ b)) B] (π : B), 0 < e → (∀ x : B, ¬ IsUnit x ↔ π ∣ x) → Ideal.span {((l : ℕ) : B)} = Ideal.span {π ^ e} → Nat.card B = Nat.card (B ⧸ Ideal.span {π}) ^ (b * e) → ¬ l ^ b ∣ e → ∃ c : B, Algebra.trace (ZMod (l ^ b)) B c ≠ 0 := by
  intro l b e _ B _ _ _ π he hunit hspan hcard hdvd
  have hb : b ≠ 0 := by rintro rfl; exact hdvd (by simp)
  have hl := (Fact.out : l.Prime)
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (hunit 0).2 (dvd_zero π) (by rw [Subsingleton.elim (0 : B) 1]; exact isUnit_one)
  have hnon : ∀ x : B, x ∈ nonunits B ↔ π ∣ x := fun x => hunit x
  haveI : IsLocalRing B := IsLocalRing.of_nonunits_add
    (fun a c ha hc => (hnon _).2 (dvd_add ((hnon a).1 ha) ((hnon c).1 hc)))
  have hmax : IsLocalRing.maximalIdeal B = Ideal.span {π} := by
    ext x; rw [IsLocalRing.mem_maximalIdeal, hnon, Ideal.mem_span_singleton]
  set K := IsLocalRing.ResidueField B
  have hlmax : ((l : ℕ) : B) ∈ IsLocalRing.maximalIdeal B := by
    rw [hmax, Ideal.mem_span_singleton]
    have : ((l : ℕ) : B) ∈ Ideal.span {π ^ e} := hspan ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at this
    exact (dvd_pow_self π he.ne').trans this
  haveI : CharP K l := by
    rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue B),
      IsLocalRing.residue_eq_zero_iff]
    exact hlmax
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  haveI : Finite K := Finite.of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨a, p, hpm, hpirr, hpa, hpa', hgen, hcardK⟩ := _root_.GlobalTheory.finiteField_exists_generator_minpoly l K
  set g : ZMod (l ^ b) →+* ZMod l := ZMod.castHom (dvd_pow_self l hb) (ZMod l) with hg
  have hgs : Function.Surjective g := ZMod.ringHom_surjective g
  obtain ⟨h, hhp, hdeg, hmon⟩ :=
    lifts_and_natDegree_eq_and_monic ((mem_lifts p).2 (map_surjective g hgs p)) hpm
  have hcomp : (algebraMap B K).comp (algebraMap (ZMod (l ^ b)) B) =
      (algebraMap (ZMod l) K).comp g := RingHom.ext_zmod _ _
  have key : ∀ q : (ZMod (l ^ b))[X],
      aeval a (q.map (algebraMap (ZMod (l ^ b)) B)) = aeval a (q.map g) := by
    intro q
    simp only [aeval_def, eval₂_map, hcomp]
  haveI : HenselianLocalRing B := henselian_of_finite B
  have H2 := ((HenselianLocalRing.TFAE B).out 1 2).mp ‹_›
  obtain ⟨ω, hω, hωa⟩ := H2 (h.map (algebraMap _ B)) (hmon.map _) a
    (by rw [key, hhp]; exact hpa)
    (by rw [derivative_map, key, ← derivative_map, hhp]; exact hpa')
  have hω' : eval₂ (algebraMap (ZMod (l ^ b)) B) ω h = 0 := by
    rw [← eval_map]; exact hω

  set C := AdjoinRoot h
  let φ : C →+* B := AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω'
  have hsurj : ∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π} := by
    intro x
    obtain ⟨q, hq⟩ := hgen (IsLocalRing.residue B x)
    obtain ⟨q', rfl⟩ := map_surjective g hgs q
    refine ⟨AdjoinRoot.mk h q', ?_⟩
    rw [← hmax, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hq]
    show _ = IsLocalRing.residue B (AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω' (AdjoinRoot.mk h q'))
    rw [AdjoinRoot.lift_mk, hom_eval₂, hωa, ← key, aeval_def, eval₂_map]
    rfl
  have hlb : ((l : ℕ) : B) ^ b = 0 := by
    rw [← Nat.cast_pow, ← map_natCast (algebraMap (ZMod (l ^ b)) B), ZMod.natCast_self, map_zero]
  have hpe : π ^ e ∈ Ideal.span {φ (l : C)} := by
    rw [map_natCast, hspan]; exact Ideal.mem_span_singleton_self _
  have hE := _root_.GlobalTheory.span_powers_of_uniformizer_of_nilpotent C B φ π (l : C) e b hsurj hpe (by rw [map_natCast]; exact hlb)

  letI : Algebra C B := φ.toAlgebra
  have hsmul : ∀ (c : C) (x : B), c • x = φ c * x := fun c x => Algebra.smul_def c x
  let T : (Fin e → C) →ₗ[C] B := Fintype.linearCombination C (fun j : Fin e => π ^ (j : ℕ))
  have hTsurj : Function.Surjective T := by
    intro x
    obtain ⟨c, hc⟩ := hE x
    refine ⟨c, ?_⟩
    rw [Fintype.linearCombination_apply, hc]
    simp only [hsmul]
  let pb := AdjoinRoot.powerBasis' hmon
  have hcardC : Nat.card C = (l ^ b) ^ p.natDegree := by
    rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin, AdjoinRoot.powerBasis'_dim, hdeg]
  have hcardB : Nat.card B = Nat.card (Fin e → C) := by
    rw [Nat.card_fun, hcardC, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin, hcard, ← hmax]
    change Nat.card K ^ (b * e) = _
    rw [hcardK, ← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Module.Finite (ZMod (l ^ b)) C := pb.finite
  haveI : Finite C := Module.finite_of_finite (ZMod (l ^ b))
  have hTbij : Function.Bijective T := hTsurj.bijective_of_nat_card_le hcardB.ge
  let bB : Module.Basis (Fin e) C B := Module.Basis.ofEquivFun (LinearEquiv.ofBijective T hTbij).symm
  haveI : IsScalarTower (ZMod (l ^ b)) C B := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have htr : ∀ y : C, Algebra.trace (ZMod (l ^ b)) B (φ y) = (e : ZMod (l ^ b)) * Algebra.trace (ZMod (l ^ b)) C y := by
    intro y
    rw [← Algebra.trace_trace_of_basis pb.basis bB]
    change Algebra.trace (ZMod (l ^ b)) C (Algebra.trace C B (algebraMap C B y)) = _
    rw [Algebra.trace_algebraMap_of_basis bB, map_nsmul, Fintype.card_fin, nsmul_eq_mul]

  have hirr' : Irreducible (h.map g) := hhp ▸ hpirr
  obtain ⟨z, hz⟩ := exists_trace_ne_zero_adjoinRoot l (h.map g) hirr'
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨q', rfl⟩ := map_surjective g hgs q
  have hmap : AdjoinRoot.map g h (h.map g) dvd_rfl (AdjoinRoot.mk h q') =
      AdjoinRoot.mk (h.map g) (q'.map g) := by
    rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map,
      AdjoinRoot.algebraMap_eq]
  have hu : IsUnit (Algebra.trace (ZMod (l ^ b)) C (AdjoinRoot.mk h q')) := by
    apply isUnit_of_cast_ne_zero l b hb
    rw [← hg, _root_.GlobalTheory.trace_adjoinRoot_map _ _ g h hmon, hmap]; exact hz
  refine ⟨φ (AdjoinRoot.mk h q'), ?_⟩
  rw [htr]
  intro h0
  exact hdvd ((ZMod.natCast_eq_zero_iff _ _).1 (hu.mul_left_eq_zero.1 h0))

end GlobalTheory.LocalTraceNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPower
section
open GlobalTheory.PMonE Finset

namespace GlobalTheory.PMonE

theorem gsum_sub_of_charP {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] {m : Type*} [Fintype m]
    (e D : ℕ) (M : ℕ → Matrix m m F) (x y : m → F) :
    gsum (p ^ e) D M (x - y) = gsum (p ^ e) D M x - gsum (p ^ e) D M y := by
  unfold gsum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simpa [pow_mul] using (sub_pow_char_pow (R := F) (p := p) (x i) (y i) (e * n))

theorem norm_gsum_le_of_small {F : Type*} [NormedField F] [IsUltrametricDist F] {m : Type*} [Fintype m]
    (q D : ℕ) (hq : 0 < q) (M : ℕ → Matrix m m F) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ n, n ≤ D → ∀ i j, ‖M n i j‖ ≤ δ) (z : m → F) (hz : ‖z‖ ≤ 1) :
    ‖gsum q D M z‖ ≤ δ * ‖z‖ := by
  have h0 : 0 ≤ δ * ‖z‖ := mul_nonneg hδ (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg h0]
  intro i
  unfold gsum
  rw [Finset.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun n hn => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun j _ => ?_
  rw [norm_mul, norm_pow]
  have hj : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
  refine mul_le_mul (hM n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) i j) ?_ (by positivity) hδ
  exact (pow_le_of_le_one (norm_nonneg _) (hj.trans hz) (pow_pos hq n).ne').trans hj

theorem gsum_eq_add_gsum_update {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
    (q D : ℕ) (U : ℕ → Matrix m m F) (y : m → F) :
    gsum q D U y = y + gsum q D (fun n => if n = 0 then U 0 - 1 else U n) y := by
  unfold gsum
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp [Matrix.sub_mulVec]
  abel

theorem existsUnique_integral_gsum_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ) (_he : 0 < e)
    (U : ℕ → Matrix m m F) (h0 : ∀ i j, ‖(U 0 - 1) i j‖ < 1) (h1 : ∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1)
    (b : m → F) (hb : Integral b) : ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  set V : ℕ → Matrix m m F := fun n => if n = 0 then U 0 - 1 else U n with hV
  have hVs : ∀ n i j, ‖V n i j‖ < 1 := by
    intro n i j
    by_cases hn : n = 0
    · simpa [hV, hn] using h0 i j
    · simpa [hV, hn] using h1 n (Nat.one_le_iff_ne_zero.mpr hn) i j
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : NNReal, δ < 1 ∧ ∀ n, n ≤ D → ∀ i j, ‖V n i j‖ ≤ δ := by
    refine ⟨((range (D + 1)) ×ˢ (univ : Finset (m × m))).sup fun t => ‖V t.1 t.2.1 t.2.2‖₊, ?_, ?_⟩
    · rw [Finset.sup_lt_iff (by simp)]
      intro t _
      exact_mod_cast hVs t.1 t.2.1 t.2.2
    · intro n hn i j
      have := Finset.le_sup (f := fun t : ℕ × m × m => ‖V t.1 t.2.1 t.2.2‖₊)
        (s := (range (D + 1)) ×ˢ (univ : Finset (m × m))) (b := (n, i, j))
        (by simp [Nat.lt_succ_iff, hn])
      exact_mod_cast this
  have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hint : ∀ y : m → F, Integral y ↔ ‖y‖ ≤ 1 := fun y => (pi_norm_le_iff_of_nonneg zero_le_one).symm
  have hbound := norm_gsum_le_of_small (p ^ e) D hq V δ δ.2 hδ
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hsub : ∀ x y : m → F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x - y‖ ≤ 1 := by
    intro x y hx hy
    rw [← hint] at *
    intro i
    rw [Pi.sub_apply, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) ?_)
    rw [norm_neg]; exact hy i
  let T : (m → F) → (m → F) := fun y => b - gsum (p ^ e) D V y
  let S : Set (m → F) := Metric.closedBall 0 1
  have hS : ∀ y, y ∈ S ↔ ‖y‖ ≤ 1 := fun y => mem_closedBall_zero_iff
  have hT : ∀ x y : m → F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖T x - T y‖ ≤ δ * ‖x - y‖ := by
    intro x y hx hy
    have : T x - T y = - gsum (p ^ e) D V (x - y) := by
      rw [gsum_sub_of_charP]; simp only [T]; abel
    rw [this, norm_neg]
    exact hbound _ (hsub x y hx hy)
  have hmaps : Set.MapsTo T S S := by
    intro y hy
    rw [hS] at hy ⊢
    refine hsub _ _ ((hint b).mp hb) ((hbound y hy).trans ?_)
    exact mul_le_one₀ hδ1'.le (norm_nonneg _) hy
  have hc : ContractingWith δ (hmaps.restrict T S S) := by
    refine ⟨hδ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hT x y ((hS _).mp x.2) ((hS _).mp y.2)
  have hfix : ∀ y, gsum (p ^ e) D U y = b ↔ T y = y := by
    intro y
    rw [gsum_eq_add_gsum_update]
    simp only [T]
    constructor
    · intro h; rw [← h]; simp [hV]
    · intro h; rw [sub_eq_iff_eq_add] at h; exact h.symm
  obtain ⟨y, hyS, hy, -⟩ := hc.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps
    (x := 0) ((hS 0).mpr (by simp)) (edist_ne_top _ _)
  refine ⟨y, ⟨(hint y).mpr ((hS y).mp hyS), (hfix y).mpr hy⟩, ?_⟩
  rintro x ⟨hx, hx'⟩
  have h := hT x y ((hint x).mp hx) ((hS y).mp hyS)
  rw [(hfix x).mp hx', show T y = y from hy] at h
  have hn := norm_nonneg (x - y)
  have : ‖x - y‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigma
section
noncomputable section

namespace GlobalTheory.UnitLemma.UnitBase

open GlobalTheory.UnitLemma Polynomial

theorem mem_adjoin_of_mul_eq_one' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  obtain ⟨p, hp, hpt⟩ := ht
  have e : aeval t p = 0 := hpt
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul] at e
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at e
    simp at e
    have : t = 0 := by simpa using congrArg (t * ·) e
    rw [this]; exact Subalgebra.zero_mem _
  obtain ⟨k, hk⟩ : ∃ k, p.natDegree = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hk] at e
  have hts : t * s = 1 := by rw [mul_comm]; exact h
  have h1 : t ^ (k + 1) * s ^ k = t := by
    rw [pow_succ', mul_assoc, ← mul_pow, hts, one_pow, mul_one]
  have h2 : ∀ i ∈ Finset.range (k + 1), p.coeff i • t ^ i * s ^ k = p.coeff i • s ^ (k - i) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [smul_mul_assoc]
    congr 1
    rw [show s ^ k = s ^ i * s ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hik], ← mul_assoc,
      ← mul_pow, hts, one_pow, one_mul]
  have e2 := congrArg (· * s ^ k) e
  simp only [add_mul, zero_mul, Finset.sum_mul] at e2
  rw [Finset.sum_congr rfl h2, h1] at e2
  have key : t = -∑ i ∈ Finset.range (k + 1), p.coeff i • s ^ (k - i) := by
    linear_combination e2
  rw [key]
  exact Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton O s) _) _)

theorem exists_isUnit_add_mul_twist {R : Type} [CommRing R] (τ : R ≃+* R) (hτ : ∀ y, τ (τ y) = y)
    (a : R) (ha : IsUnit a) (hfin : {M : Ideal R | M.IsMaximal}.Finite)
    (x : R) (hx : IsUnit (τ x - x)) : ∃ y : R, IsUnit (y + a * τ y) := by
  classical
  haveI : Finite {M : Ideal R // M.IsMaximal} := hfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin {M : Ideal R // M.IsMaximal}
  let pt : {M : Ideal R // M.IsMaximal} → {M : Ideal R // M.IsMaximal} := fun M =>
    ⟨M.1.comap (τ : R →+* R), by haveI := M.2; exact Ideal.comap_isMaximal_of_surjective _ τ.surjective⟩
  have mem_pt : ∀ M z, z ∈ (pt M).1 ↔ τ z ∈ M.1 := fun M z => Iff.rfl
  have pt_pt : ∀ M, pt (pt M) = M := by
    intro M; apply Subtype.ext; ext z; rw [mem_pt, mem_pt, hτ]
  let t : {M : Ideal R // M.IsMaximal} → R := fun M =>
    if pt M = M then (if 1 + a ∈ M.1 then x else 1) else if e M < e (pt M) then 1 else 0
  have hcop : Pairwise (Function.onFun IsCoprime fun M : {M : Ideal R // M.IsMaximal} => M.1) := by
    intro M N hne
    haveI := M.2; haveI := N.2
    exact Ideal.isCoprime_of_isMaximal (fun h => hne (Subtype.ext h))
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun M => Ideal.Quotient.mk M.1 (t M))
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : ∀ M : {M : Ideal R // M.IsMaximal}, y - t M ∈ M.1 := by
    intro M
    have := congrFun hq M
    rw [Ideal.quotientInfToPiQuotient_mk'] at this
    exact Ideal.Quotient.eq.1 this
  refine ⟨y, ?_⟩
  by_contra hnu
  obtain ⟨M0, hM0, hyM⟩ := exists_max_ideal_of_mem_nonunits hnu
  set M : {M : Ideal R // M.IsMaximal} := ⟨M0, hM0⟩ with hMdef
  have hyM' : y + a * τ y ∈ M.1 := hyM
  have hne1 : (1 : R) ∉ M.1 := fun h => hM0.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hunit : ∀ {u : R}, IsUnit u → u ∉ M.1 := fun hu h => hM0.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  by_cases hfix : pt M = M
  · have hτM : ∀ z, z ∈ M.1 → τ z ∈ M.1 := by
      intro z hz; rw [← mem_pt, hfix]; exact hz
    have hd := hy M
    have ht : t M + a * τ (t M) ∈ M.1 := by
      have : t M + a * τ (t M) = (y + a * τ y) - (y - t M) - a * τ (y - t M) := by
        rw [map_sub]; ring
      rw [this]
      exact M.1.sub_mem (M.1.sub_mem hyM' hd) (M.1.mul_mem_left _ (hτM _ hd))
    by_cases h1a : 1 + a ∈ M.1
    · have htx : t M = x := by simp only [t, if_pos hfix, if_pos h1a]
      rw [htx] at ht
      have : a * (τ x - x) ∈ M.1 := by
        have : a * (τ x - x) = (x + a * τ x) - x * (1 + a) := by ring
        rw [this]; exact M.1.sub_mem ht (M.1.mul_mem_left _ h1a)
      exact hunit (ha.mul hx) this
    · have ht1 : t M = 1 := by simp only [t, if_pos hfix, if_neg h1a]
      rw [ht1, map_one, mul_one, add_comm] at ht
      exact h1a (by rwa [add_comm])
  · have hfix' : pt (pt M) ≠ pt M := by rw [pt_pt]; exact Ne.symm hfix
    by_cases hlt : e M < e (pt M)
    · have ht1 : t M = 1 := by simp only [t, if_neg hfix, if_pos hlt]
      have hlt' : ¬ e (pt M) < e (pt (pt M)) := by rw [pt_pt]; exact not_lt.2 hlt.le
      have ht0 : t (pt M) = 0 := by simp only [t, if_neg hfix', if_neg hlt']
      have h1 := hy M
      have h2 := hy (pt M)
      rw [ht1] at h1
      rw [ht0, sub_zero, mem_pt] at h2
      have : (1 : R) = (y + a * τ y) - (y - 1) - a * τ y := by ring
      exact hne1 (this ▸ M.1.sub_mem (M.1.sub_mem hyM' h1) (M.1.mul_mem_left _ h2))
    · have ht0 : t M = 0 := by simp only [t, if_neg hfix, if_neg hlt]
      have hne : e (pt M) ≠ e M := fun h => hfix (e.injective h)
      have hlt' : e (pt M) < e (pt (pt M)) := by
        rw [pt_pt]; exact lt_of_le_of_ne (not_lt.1 hlt) hne
      have ht1 : t (pt M) = 1 := by simp only [t, if_neg hfix', if_pos hlt']
      have h1 := hy M
      have h2 := hy (pt M)
      rw [ht0, sub_zero] at h1
      rw [ht1, mem_pt, map_sub, map_one] at h2
      have : a = (y + a * τ y) - y - a * (τ y - 1) := by ring
      exact hunit ha (this ▸ M.1.sub_mem (M.1.sub_mem hyM' h1) (M.1.mul_mem_left _ h2))

def cO (K : UQ) : K.O →+* K.O where
  toFun x := Classical.choose (K.c_int x)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' x y := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (x * y)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int x), ← Classical.choose_spec (K.c_int y)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' x y := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (x + y)), map_add (f := _), map_add (f := _), map_add (f := _),
      ← Classical.choose_spec (K.c_int x), ← Classical.choose_spec (K.c_int y)]

theorem algebraMap_cO (K : UQ) (x : K.O) : algebraMap K.O K.E (cO K x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm

theorem σ_algebraMap_O {K : UQ} (B : InvAlg K) (x : K.O) :
    B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A (cO K x) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← algebraMap_cO,
    ← IsScalarTower.algebraMap_apply]

theorem isIntegral_σ {K : UQ} (B : InvAlg K) {y : B.A} (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨p.map (cO K), hp.map _, ?_⟩
  have hc : (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) = (algebraMap K.O B.A).comp (cO K) := by
    ext x; exact σ_algebraMap_O B x
  have := congrArg (B.σ : B.A →+* B.A) hpy
  rw [map_zero, Polynomial.hom_eval₂, hc] at this
  rw [Polynomial.eval₂_map]; exact this

theorem σ_mem_adjoin {K : UQ} (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (hint : IsIntegral K.O B.g)
    {y : B.A} (hy : y ∈ Algebra.adjoin K.O {B.g}) : B.σ y ∈ Algebra.adjoin K.O {B.g} := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact mem_adjoin_of_mul_eq_one' hg (isIntegral_σ B hint)
  | algebraMap r => rw [σ_algebraMap_O]; exact Subalgebra.algebraMap_mem _ _
  | add x z _ _ hx hz => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hz
  | mul x z _ _ hx hz => rw [map_mul]; exact Subalgebra.mul_mem _ hx hz

theorem maximal_finite {K : UQ} (B : InvAlg K) (hint : IsIntegral K.O B.g) :
    {M : Ideal (Algebra.adjoin K.O {B.g}) | M.IsMaximal}.Finite := by
  haveI : Module.Finite K.O (Algebra.adjoin K.O {B.g}) := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  refine (Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal K.O)).subset ?_
  intro M hM
  have hM' : M.IsMaximal := hM
  letI : M.IsMaximal := hM'
  have hc : (M.comap (algebraMap K.O (Algebra.adjoin K.O {B.g}))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap K.O (Algebra.adjoin K.O {B.g}))
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) M
  exact ⟨hM'.isPrime, ⟨(IsLocalRing.eq_maximalIdeal hc).symm⟩⟩

theorem exists_unit_base : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by
  intro K B hg _ hint ε hε
  set R := Algebra.adjoin K.O {B.g} with hR
  have hσR : ∀ y : R, B.σ (y : B.A) ∈ R := fun y => σ_mem_adjoin B hg hint y.2
  let τ : R ≃+* R :=
    { toFun := fun y => ⟨B.σ (y : B.A), hσR y⟩
      invFun := fun y => ⟨B.σ (y : B.A), hσR y⟩
      left_inv := fun y => Subtype.ext (B.σ_σ (y : B.A))
      right_inv := fun y => Subtype.ext (B.σ_σ (y : B.A))
      map_mul' := fun x y => Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
      map_add' := fun x y => Subtype.ext (map_add B.σ (x : B.A) (y : B.A)) }
  have hτc : ∀ y : R, ((τ y : R) : B.A) = B.σ y := fun y => rfl
  have hτ : ∀ y, τ (τ y) = y := fun y => Subtype.ext (B.σ_σ (y : B.A))

  obtain ⟨ε', hε'c, hε'u, hεε, hσε⟩ : ∃ ε' : R, (ε' : B.A) = ε ∧ IsUnit ε' ∧ ε * ε = 1 ∧ B.σ ε = ε := by
    rcases hε with rfl | rfl
    · exact ⟨1, by simp, isUnit_one, by simp, by simp⟩
    · exact ⟨-1, by simp, isUnit_one.neg, by simp, by simp⟩

  let g' : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  let h' : R := τ g'
  have hgh : g' * h' = 1 := Subtype.ext hg
  have hh'u : IsUnit h' := ⟨⟨h', g', by rw [mul_comm]; exact hgh, hgh⟩, rfl⟩

  obtain ⟨x0, y0, hxy, hxy0⟩ := K.c_res
  have hcx : cO K x0 = y0 := IsFractionRing.injective K.O K.E (by rw [algebraMap_cO, hxy])
  have hx : IsUnit (τ (algebraMap K.O R x0) - algebraMap K.O R x0) := by
    have hu : IsUnit (y0 - x0) := by
      have : IsUnit (x0 - y0) := by
        by_contra hn; exact hxy0 ((IsLocalRing.mem_maximalIdeal _).2 hn)
      simpa [neg_sub] using this.neg
    have : τ (algebraMap K.O R x0) - algebraMap K.O R x0 = algebraMap K.O R (y0 - x0) := by
      apply Subtype.ext
      simp only [hτc, Subalgebra.coe_sub, Subalgebra.coe_algebraMap, σ_algebraMap_O, hcx, map_sub]
    rw [this]; exact hu.map _
  obtain ⟨y, hy⟩ := exists_isUnit_add_mul_twist τ hτ (ε' * h') (hε'u.mul hh'u) (maximal_finite B hint) _ hx
  refine ⟨Units.map (R.val : R →* B.A) hy.unit, ?_, ?_, ?_⟩
  · have hc : ((Units.map (R.val : R →* B.A) hy.unit : B.Aˣ) : B.A) = (y : B.A) + ε * B.σ B.g * B.σ y := by
      simp [Units.coe_map, IsUnit.unit_spec, hε'c, hτc, h', g', mul_assoc]
    rw [hc, map_add (f := _), map_mul, map_mul, hσε, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ (y : B.A)) * ε * ε) * hg - B.σ (y : B.A) * hεε
  · simp only [Units.coe_map]; exact (hy.unit : R).2
  · rw [← map_inv]; simp only [Units.coe_map]; exact ((hy.unit⁻¹ : Rˣ) : R).2

end GlobalTheory.UnitLemma.UnitBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntCastTraceEqTraceQuotientOfMemStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intCast_trace_eq_trace_quotient_of_mem' : ∀ (L : Type) [Field L] [NumberField L] (l b : ℕ) [Fact l.Prime] (I Q : Ideal (𝓞 L)), I ⊔ Q = ⊤ → I * Q = Ideal.span {((l ^ b : ℕ) : 𝓞 L)} → ∀ [Algebra (ZMod (l ^ b)) (𝓞 L ⧸ I)] (x : 𝓞 L), x ∈ Q → ((Algebra.trace ℤ (𝓞 L) x : ℤ) : ZMod (l ^ b)) = Algebra.trace (ZMod (l ^ b)) (𝓞 L ⧸ I) (Ideal.Quotient.mk I x) := by
  first | exact @GlobalTheory.intCast_trace_eq_trace_quotient_of_mem | exact GlobalTheory.intCast_trace_eq_trace_quotient_of_mem | (intros; apply GlobalTheory.intCast_trace_eq_trace_quotient_of_mem <;> assumption)
end

