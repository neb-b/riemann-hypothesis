module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenSubgroupFiniteSubset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SmallSub

theorem eq_zero_of_pow_mul {K : Type} [NormedField K] {C : Set K} (hC : IsCompact C) {c x : K} (hc : ‖c‖ < 1)
    (h : ∀ n : ℕ, ∃ u ∈ C, x = c ^ n * u) : x = 0 := by
  obtain ⟨B, hB⟩ := hC.isBounded.exists_norm_le
  have ht : Filter.Tendsto (fun n : ℕ => ‖c‖ ^ n * B) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg c) hc).mul_const B
  refine norm_le_zero_iff.1 (ge_of_tendsto' ht fun n => ?_)
  obtain ⟨u, hu, rfl⟩ := h n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB u hu) (by positivity)

theorem finiteAdele_eq_zero (F : Type) [Field F] [NumberField F] {C : Set (Af F)} (hC : IsCompact C) {x : Af F}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change evalV F v x = 0
  have hv : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have h1 := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  rw [map_natCast, map_natCast] at h1
  have h0 : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  refine eq_zero_of_pow_mul (hC.image hv) h1 fun n => ?_
  obtain ⟨u, hu, rfl⟩ := h _ (pow_pos h0 n)
  exact ⟨_, ⟨u, hu, rfl⟩, by rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow]⟩

theorem tensor_eq_zero (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {C : Set (Af F ⊗[F] E)} (hC : IsCompact C) {x : Af F ⊗[F] E}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)
  refine b.ext_elem fun i => ?_
  have hc : Continuous (b.coord i) := IsModuleTopology.continuous_of_linearMap _
  rw [map_zero, Finsupp.zero_apply]
  change b.coord i x = 0
  refine finiteAdele_eq_zero F (hC.image hc) fun M hM => ?_
  obtain ⟨u, hu, rfl⟩ := h M hM
  exact ⟨_, ⟨u, hu, rfl⟩, map_nsmul _ _ _⟩

theorem mem_GinfC_of_cong {D : D7} (V : HSp D) (k : GA D V)
    (h : ∀ n : ℕ, GlobalTheory.Ker.CongK V (GlobalTheory.SW.stdL D.host.E V.rank) n.factorial k) : k ∈ GinfC V := by
  obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat D.host.F D.host.E (GlobalTheory.SW.stdL D.host.E V.rank)
    (Submodule.fg_span (Set.finite_range _))
  refine Units.ext ?_
  change GlobalTheory.Ker.fmt V k = 1
  ext i j
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  have hy : (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (D := D) (GlobalTheory.SW.stdL D.host.E V.rank) := by
    refine AddSubgroup.subset_closure ⟨1, h1, Pi.single j 1, Submodule.subset_span ⟨j, rfl⟩, ?_⟩
    funext a
    by_cases e : a = j
    · subst e
      simp only [Pi.single_eq_same]
      rfl
    · simp [Pi.single_eq_of_ne e]
  have key : (GlobalTheory.Ker.fmt V k *ᵥ Pi.single j 1 - (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D)) i = 0 := by
    refine tensor_eq_zero D.host.F D.host.E (hC.image (continuous_apply i)) fun M hM => ?_
    obtain ⟨u, hu, e⟩ := (h M).2 _ hy
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hM le_rfl
    refine ⟨_, ⟨c • u, hLC _ (nsmul_mem hu c), rfl⟩, ?_⟩
    rw [e, hc, mul_smul]
    rfl
  rw [Pi.sub_apply, sub_eq_zero, Matrix.mulVec_single_one] at key
  rw [Matrix.one_apply, ← Pi.single_apply]
  exact key

theorem exists_open_subgroup_finite_subset : ∀ (D : D7) (V : HSp D), ∀ N ∈ 𝓝 (1 : GA D V), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ N := by
  intro D V N hN
  obtain ⟨i0, -, -, i3, -, -, hK⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  choose K hK1 hK2 hK3 _ using fun n : ℕ => hK _ n.factorial hL n.factorial_pos
  have hanti : Antitone fun n => (K n : Set (GA D V)) ∩ GfC V := by
    intro m n hmn k hk
    refine ⟨(hK1 m k).2 ⟨((hK1 n k).1 hk.1).1, fun u hu => ?_⟩, hk.2⟩
    obtain ⟨w, hw, e⟩ := ((hK1 n k).1 hk.1).2 u hu
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hmn
    exact ⟨c • w, nsmul_mem hw c, by rw [e, hc, mul_smul]⟩
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' (U := N) hanti.directed_ge hK3 (fun n => (hK3 n).isClosed)
    (mem_nhdsSet_iff_forall.2 fun x hx => by
      rw [Set.mem_iInter] at hx
      rwa [GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (hx 0).2 (mem_GinfC_of_cong V x fun n => (hK1 n x).1 (hx n).1)])
  exact ⟨K n, hK2 n, fun k hk hf => hn ⟨hk, hf⟩⟩

end GlobalTheory.Mem.SmallSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrobTeich

variable {Ω : Type} [Field Ω]

theorem eq_of_pow_eq_self_of_cong (A : ValuationSubring Ω) {N : ℕ} (hN : A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = a) (hb : b ^ N = b) (hab : A.valuation (a - b) < 1) : a = b := by
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · interval_cases N
    · rw [pow_zero] at ha hb; rw [← ha, ← hb]
    · simp at hN
  have hle : ∀ c : Ω, c ^ N = c → A.valuation c ≤ 1 := by
    intro c hc
    by_contra hc1
    have h1 : 1 < A.valuation c := not_le.mp hc1
    have h2 : A.valuation c ^ 1 < A.valuation c ^ N := pow_lt_pow_right₀ h1 (by omega)
    rw [← map_pow, ← map_pow, hc, pow_one] at h2
    exact lt_irrefl _ h2
  have ha1 := hle a ha
  have hb1 := hle b hb
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  set S := ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i) with hS
  have hS1 : S = 1 := by
    have h1 : S * (a - b) = a - b := by rw [hS, geom_sum₂_mul, ha, hb]
    have h2 : (S - 1) * (a - b) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hsub
  have hdiff : A.valuation (S - ∑ i ∈ Finset.range N, a ^ i * a ^ (N - 1 - i)) < 1 := by
    rw [hS, ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [← mul_sub, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (GlobalTheory.WeilDeligne.val_pow_le_one ha1 i))
      (GlobalTheory.WeilDeligne.cong_pow hb1 ha1 (GlobalTheory.WeilDeligne.cong_symm hab) _)
  rw [geom_sum₂_self] at hdiff
  have hNa : A.valuation ((N : Ω) * a ^ (N - 1)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (GlobalTheory.WeilDeligne.val_pow_le_one ha1 _)) hN
  have hS' : A.valuation S < 1 := by
    have e : S = (S - (N : Ω) * a ^ (N - 1)) + (N : Ω) * a ^ (N - 1) := by ring
    rw [e]; exact Valuation.map_add_lt _ hdiff hNa
  rw [hS1, map_one] at hS'
  exact lt_irrefl _ hS'


open Polynomial in
theorem exists_pow_eq_self_cong [IsAlgClosed Ω] (A : ValuationSubring Ω) {N : ℕ} (hN : 2 ≤ N)
    {x : Ω} (hx : A.valuation (x ^ N - x) < 1) : ∃ ζ : Ω, ζ ^ N = ζ ∧ A.valuation (x - ζ) < 1 := by
  set P : Polynomial Ω := X ^ N - X with hP
  have hdeg : P.natDegree = N := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
  have hmon : P.Monic := by
    rw [hP]; exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < N))
  have hsplit : P = (P.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [IsAlgClosed.card_roots_eq_natDegree])).symm
  have hev : x ^ N - x = (P.roots.map fun a => x - a).prod := by
    have := congrArg (eval x) hsplit
    rw [eval_multiset_prod, Multiset.map_map] at this
    simpa [hP, Function.comp_def] using this
  by_contra hno
  push_neg at hno
  have hge : ∀ a ∈ P.roots, 1 ≤ A.valuation (x - a) := by
    intro a ha
    refine hno a ?_
    have := (mem_roots hmon.ne_zero).mp ha
    simpa [hP, sub_eq_zero] using this
  have h1 : 1 ≤ A.valuation (x ^ N - x) := by
    rw [hev, map_multiset_prod]
    refine Multiset.prod_induction (fun c => 1 ≤ c) _ (fun a b ha hb => ?_) le_rfl ?_
    · simpa using mul_le_mul' ha hb
    · intro c hc
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hc
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
      exact hge a ha
  exact absurd hx (not_lt.mpr h1)

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem exists_prime_pow_normV (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) : ∃ p f : ℕ, p.Prime ∧ 0 < f ∧ normV w = p ^ f ∧ A.valuation (p : Ω) < 1 := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  set p := ringChar (𝓞 E ⧸ w.asIdeal) with hp_def
  obtain ⟨n, hp, hn⟩ := FiniteField.card (𝓞 E ⧸ w.asIdeal) p
  have hpw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  refine ⟨p, n, hp, n.pos, ?_, ?_⟩
  · show Nat.card (𝓞 E ⧸ w.asIdeal) = p ^ (n : ℕ)
    rw [Nat.card_eq_fintype_card, hn]
  · have := (h _).mpr hpw
    simpa using this

theorem exists_pow_char_pow_eq_self {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (P : Polynomial ℤ) (hP : P.map (Int.castRingHom k) ≠ 0) {y : k}
    (hy : P.eval₂ (Int.castRingHom k) y = 0) : ∃ r : ℕ, 0 < r ∧ y ^ p ^ r = y := by
  have hroot : ∀ i : ℕ, y ^ p ^ i ∈ {z : k | (P.map (Int.castRingHom k)).IsRoot z} := by
    intro i
    show (P.map (Int.castRingHom k)).eval (y ^ p ^ i) = 0
    rw [Polynomial.eval_map, ← iterateFrobenius_def (R := k) p i,
      ← RingHom.ext_int ((iterateFrobenius k p i).comp (Int.castRingHom k)) (Int.castRingHom k),
      ← Polynomial.hom_eval₂, hy, map_zero]
  obtain ⟨i, j, hij, heq⟩ := (Polynomial.finite_setOf_isRoot hP).exists_lt_map_eq_of_forall_mem hroot
  refine ⟨j - i, by omega, ?_⟩
  apply (iterateFrobenius k p i).injective
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  exact heq.symm

theorem exists_pow_prime_pow_cong [CharZero Ω] (A : ValuationSubring Ω) {x : Ω}
    (halg : IsAlgebraic ℤ x) (hx : A.valuation x ≤ 1) {p : ℕ} (hp : p.Prime)
    (hpA : A.valuation (p : Ω) < 1) : ∃ r : ℕ, 0 < r ∧ A.valuation (x ^ p ^ r - x) < 1 := by
  obtain ⟨P, hP0, hPx⟩ := halg
  set Q := P.primPart with hQ
  have hQprim : Q.IsPrimitive := P.isPrimitive_primPart
  have hQx : Polynomial.aeval x Q = 0 := by
    have e := congrArg (Polynomial.aeval x) P.eq_C_content_mul_primPart
    rw [hPx, map_mul, Polynomial.aeval_C] at e
    have hc : (algebraMap ℤ Ω) P.content ≠ 0 := by
      rw [eq_intCast, Int.cast_ne_zero]; exact (Polynomial.content_eq_zero_iff.not).mpr hP0
    exact (mul_eq_zero.mp e.symm).resolve_left hc
  haveI : Fact p.Prime := ⟨hp⟩
  set k := IsLocalRing.ResidueField A
  set y : A := ⟨x, (A.valuation_le_one_iff x).mp hx⟩ with hy_def
  haveI : CharP k p := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    simpa using hpA
  have hmap : Q.map (Int.castRingHom k) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ Q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun g => _root_.AddMonoidAlgebra.coeff (M := ℕ) g i) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
      exact (CharP.intCast_eq_zero_iff k p _).mp this
    have hu := hQprim (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    rcases hu with hu | hu <;> omega
  have hyA : Q.eval₂ (Int.castRingHom A) y = 0 := by
    apply Subtype.ext
    have e := Polynomial.hom_eval₂ Q (Int.castRingHom A) A.subtype y
    rw [RingHom.ext_int (A.subtype.comp (Int.castRingHom A)) (algebraMap ℤ Ω)] at e
    change A.subtype _ = A.subtype 0
    rw [e, map_zero]; exact hQx
  have hyk : Q.eval₂ (Int.castRingHom k) (IsLocalRing.residue A y) = 0 := by
    rw [← RingHom.ext_int ((IsLocalRing.residue A).comp (Int.castRingHom A)) (Int.castRingHom k),
      ← Polynomial.hom_eval₂, hyA, map_zero]
  obtain ⟨r, hr, hyr⟩ := exists_pow_char_pow_eq_self p Q hmap hyk
  refine ⟨r, hr, ?_⟩
  have hmem : y ^ p ^ r - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hyr, sub_self]
  have := (A.valuation_lt_one_iff _).mp hmem
  simpa [hy_def] using this

theorem exists_pow_normV_pow_cong [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ A.valuation (x ^ normV w ^ m - x) < 1 := by
  obtain ⟨p, f, hp, hf, hq, hpA⟩ := exists_prime_pow_normV A w h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨r, hr, hxr⟩ := exists_pow_prime_pow_cong A halg hx hp hpA
  refine ⟨r, hr, ?_⟩
  have key : ∀ j : ℕ, A.valuation (x ^ (p ^ r) ^ j - x) < 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := GlobalTheory.WeilDeligne.cong_pow (GlobalTheory.WeilDeligne.val_pow_le_one hx _) hx ih (p ^ r)
      rw [← pow_mul, ← pow_succ] at h1
      exact GlobalTheory.WeilDeligne.cong_trans h1 hxr
  have e : normV w ^ r = (p ^ r) ^ f := by rw [hq, ← pow_mul, ← pow_mul, mul_comm]
  rw [e]; exact key f

end GlobalTheory.FrobTeich

open GlobalTheory.FrobTeich in
theorem GlobalTheory.FrobTeich.isFrob_iff_teichmuller : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (σ : G E Ω), IsFrob (F := E) A (normV w) σ ↔ σ ∈ Dec (F := E) A ∧ ∀ (ζ : Ω) (m : ℕ), 0 < m → ζ ^ normV w ^ m = ζ → σ ζ = ζ ^ normV w := by
  intro E Ω _ _ _ _ _ A w h σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨p, f, hp, hf, hq, hpA⟩ := exists_prime_pow_normV A w h
  set q := normV w with hq_def
  have hqA : A.valuation (q : Ω) < 1 := by
    rw [hq, Nat.cast_pow, map_pow]; exact pow_lt_one₀ zero_le hpA hf.ne'
  have hq2 : 2 ≤ q := by rw [hq]; exact le_trans hp.two_le (Nat.le_self_pow hf.ne' p)
  constructor
  · rintro ⟨hD, hc⟩
    refine ⟨hD, fun ζ m hm hζ => ?_⟩
    have hNA : A.valuation ((q ^ m : ℕ) : Ω) < 1 := by
      rw [Nat.cast_pow, map_pow]; exact pow_lt_one₀ zero_le hqA hm.ne'
    have hζ1 : A.valuation ζ ≤ 1 := by
      by_contra hc1
      have h1 : 1 < A.valuation ζ := not_le.mp hc1
      have h2 : A.valuation ζ ^ 1 < A.valuation ζ ^ (q ^ m) :=
        pow_lt_pow_right₀ h1 (Nat.one_lt_pow hm.ne' (by omega))
      rw [← map_pow, ← map_pow, hζ, pow_one] at h2
      exact lt_irrefl _ h2
    refine eq_of_pow_eq_self_of_cong A hNA ?_ ?_ (hc ζ hζ1)
    · rw [← map_pow, hζ]
    · rw [← pow_mul, mul_comm, pow_mul, hζ]
  · rintro ⟨hD, hT⟩
    refine ⟨hD, fun x hx => ?_⟩
    obtain ⟨m, hm, hxm⟩ := exists_pow_normV_pow_cong A w h hx
    obtain ⟨ζ, hζ, hxζ⟩ := exists_pow_eq_self_cong A
      (le_trans hq2 (Nat.le_self_pow hm.ne' q)) hxm
    have hσζ := hT ζ m hm hζ
    have hζ1 : A.valuation ζ ≤ 1 := by
      have e : ζ = x - (x - ζ) := by ring
      rw [e]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hx hxζ.le)
    have e : σ x - x ^ q = σ (x - ζ) + (ζ ^ q - x ^ q) := by
      rw [map_sub, hσζ]; ring
    rw [e]
    refine Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hD _).mpr hxζ) ?_
    exact GlobalTheory.WeilDeligne.cong_pow hζ1 hx (GlobalTheory.WeilDeligne.cong_symm hxζ) q
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOver
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

section Generic

variable {Ω : Type} [Field Ω] {J : Type} [Fintype J] [DecidableEq J]

def genPoly (Ω : Type) [Field Ω] (j₀ j : J) : MvPolynomial {j // j ≠ j₀} Ω :=
  if h : j = j₀ then 1 else MvPolynomial.X ⟨j, h⟩

def genPt (Ω : Type) [Field Ω] (j₀ j : J) : FractionRing (MvPolynomial {j // j ≠ j₀} Ω) :=
  algebraMap _ _ (genPoly Ω j₀ j)

omit [Fintype J] in
theorem genPt_self (j₀ : J) : genPt Ω j₀ j₀ = 1 := by simp [genPt, genPoly]


omit [Fintype J] in
theorem eq_top_of_genPt_mem (j₀ : J) (K : Subfield (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)))
    (h1 : ∀ a : Ω, algebraMap Ω _ a ∈ K) (h2 : ∀ j, genPt Ω j₀ j ∈ K) : K = ⊤ := by
  have h : ∀ p : MvPolynomial {j // j ≠ j₀} Ω, algebraMap _ _ p ∈ K := fun p => by
    induction p using MvPolynomial.induction_on with
    | C a => exact h1 a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      simpa [genPt, genPoly, j.2] using h2 j.1
  refine top_unique fun x _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial {j // j ≠ j₀} Ω) x
  exact div_mem (h p) (h q)

theorem eq_zero_of_sum_genPt (j₀ : J) (b : J → Ω) (h : ∑ j, algebraMap Ω _ (b j) * genPt Ω j₀ j = 0) : b = 0 := by
  have h' : ∑ j, MvPolynomial.C (b j) * genPoly Ω j₀ j = 0 := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum, ← h]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; rfl
  have e : ∀ x : J → Ω, x j₀ = 1 → ∑ j, b j * x j = 0 := fun x hx => by
    have := congrArg (MvPolynomial.eval fun j : {j // j ≠ j₀} => x j.1) h'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj; simp [genPoly, hx]
    · simp [genPoly, hj]
  have h0 : b j₀ = 0 := by simpa [Pi.single_apply] using e (Pi.single j₀ 1) (by simp)
  funext j
  by_cases hj : j = j₀
  · exact hj ▸ h0
  · have := e (fun l => Pi.single (M := fun _ => Ω) j₀ 1 l + Pi.single (M := fun _ => Ω) j 1 l) (by simp [Ne.symm hj])
    simpa [Pi.single_apply, mul_add, Finset.sum_add_distrib, h0] using this

theorem genPt_ratio (j₀ : J) (B : Matrix J J Ω) (hB : B.det ≠ 0) (i : J) :
    (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i ≠ 0 ∧ AlgebraicIndependent Ω fun j : {j // j ≠ i} =>
      (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) j.1 / (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i := by
  set u := (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) with hu
  have hi : u i ≠ 0 := fun h => hB (Matrix.det_eq_zero_of_row_eq_zero i
    (congrFun (eq_zero_of_sum_genPt j₀ (B i) h)))
  refine ⟨hi, ?_⟩
  set r : {j // j ≠ i} → _ := fun j => u j.1 / u i
  have hs : (B⁻¹.map (algebraMap Ω _)).mulVec u = genPt Ω j₀ := by
    rw [hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  set K := IntermediateField.adjoin Ω (Set.range r)
  have h1 : ∀ j, u j / u i ∈ K := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hi]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨j, hj⟩, rfl⟩
  have h2 : ∀ j, genPt Ω j₀ j / u i ∈ K := fun j => by
    rw [← hs, Matrix.mulVec, dotProduct, Finset.sum_div]
    refine sum_mem fun l _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (K.algebraMap_mem _) (h1 l)
  have h3 : K.toSubfield = ⊤ := eq_top_of_genPt_mem j₀ _ K.algebraMap_mem fun j => by
    have := div_mem (h2 j) (h2 j₀)
    rwa [div_div_div_cancel_right₀ hi, genPt_self, div_one] at this
  have h4 : Algebra.IsAlgebraic K (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)) := ⟨fun x =>
    isAlgebraic_algebraMap (⟨x, (h3 ▸ Subfield.mem_top x : x ∈ K.toSubfield)⟩ : K)⟩
  have h5 := IntermediateField.isAlgebraic_adjoin_iff_top.1 h4
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω r ?_).1
  have h6 := trdeg_add_eq Ω (MvPolynomial {j // j ≠ j₀} Ω) (A := FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
  rw [← h6, MvPolynomial.trdeg_of_isDomain]
  refine le_trans (le_of_eq ?_) le_self_add
  simp [Cardinal.mk_fintype]

end Generic

theorem exists_projBundle : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  intro F Ω _ _ _ M J _ inst ⟨j₀⟩ EE hM
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  let : DecidableEq J := fun a b => Classical.propDecidable (a = b)
  let Ω' := FractionRing (MvPolynomial {j // j ≠ j₀} Ω)
  let φ : Ω →ₐ[F] Ω' := IsScalarTower.toAlgHom F Ω Ω'
  obtain ⟨M', f, hf, hp, hc⟩ := RatModel.exists_projBundle_closure F Ω M Ω' φ J EE (genPt Ω j₀) hM
    ⟨j₀, by rw [genPt_self]; exact one_ne_zero⟩
    (eq_top_of_genPt_mem j₀ _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun j => Subfield.subset_closure (Or.inr ⟨j₀, j, by rw [genPt_self, div_one]⟩))
  refine ⟨Ω', inferInstance, inferInstance, M', φ, f, genPt Ω j₀, ⟨hf, fun B hB i => ?_, hc⟩, hp⟩
  obtain ⟨h1, h2⟩ := genPt_ratio j₀ B hB i
  exact ⟨h1, fun P hP => algebraicIndependent_iff.1 h2 P hP⟩

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizer
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finite_image_of_isOpen_stabilizer (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (hH : IsOpen {g : G | ρ g v = v})
    (S : Set G) (hS : IsCompact S) : ((fun g => ρ g v) '' S).Finite := by
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun s : G => (fun x => s⁻¹ * x) ⁻¹' {g : G | ρ g v = v})
    (fun s => hH.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ((t : Set G).toFinite.image (fun g => ρ g v)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx)
  refine ⟨s, hs, ?_⟩
  have h1 : ρ (s⁻¹ * x) v = v := hxs
  have hx' : x = s * (s⁻¹ * x) := by group
  show ρ s v = ρ x v
  conv_rhs => rw [hx', map_mul, Module.End.mul_apply, h1]

end GlobalTheory
end

