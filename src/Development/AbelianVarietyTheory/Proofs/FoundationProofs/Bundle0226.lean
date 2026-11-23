module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory

open NumberField IsDedekindDomain in
open Polynomial Matrix in
private theorem eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero {K : Type} [Field K] [CharZero K]
    {a : ℕ} (B : Subalgebra K (Matrix (Fin a) (Fin a) K)) {z : Matrix (Fin a) (Fin a) K}
    (hzB : z ∈ B) (htr : ∀ y ∈ B, (z * y).trace = 0) {v : Fin a → K} (hv : z *ᵥ v = v) :
    v = 0 := by
  classical
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd z.charpoly
    (Matrix.charpoly_monic z).ne_zero 0
  set m := z.charpoly.rootMultiplicity 0 with hm
  simp only [map_zero, sub_zero] at hpq hq
  have hc : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  set c := q.coeff 0 with hcdef
  set R := aeval z q.divX with hR
  have hq' : aeval z q = z * R + c • 1 := by
    calc aeval z q = aeval z (X * q.divX + C (q.coeff 0)) := by rw [Polynomial.X_mul_divX_add]
      _ = z * R + c • 1 := by
        rw [map_add (f := _), map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have h0 : z ^ m * (z * R + c • 1) = 0 := by
    have := Matrix.aeval_self_charpoly z
    rwa [hpq, map_mul, map_pow, aeval_X, hq'] at this
  have hRz : z * R = R * z := by
    have := congrArg (aeval z) (mul_comm X q.divX)
    simpa [R] using this
  have h1 : z ^ (m + 1) * R = -(c • z ^ m) := by
    rw [pow_succ, mul_assoc]
    rw [mul_add, mul_smul_comm, mul_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hkey : z ^ m = z ^ (m + 1) * ((-c⁻¹) • R) := by
    rw [mul_smul_comm, h1, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hc, neg_smul, one_smul,
      neg_neg]
  set u := (-c⁻¹) • R with hu
  have hcomm : Commute z u := (show Commute z R from hRz).smul_right _
  have hstep : ∀ i, z ^ (m + i) = z ^ (m + i + 1) * u := by
    intro i
    rw [pow_add z m i, hkey, mul_assoc, ← (hcomm.pow_left i).eq, ← mul_assoc, ← pow_add,
      show m + 1 + i = m + i + 1 by omega]
  have hpow : ∀ k, z ^ (m + 1) = z ^ (m + 1 + k) * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, show m + 1 + k = m + (k + 1) by omega, hstep (k + 1), mul_assoc, ← pow_succ',
        show m + (k + 1) + 1 = m + 1 + (k + 1) by omega]
  have hRB : R ∈ B :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hzB) (Polynomial.aeval_mem_adjoin_singleton K z)
  have huB : u ∈ B := B.smul_mem hRB _
  set n := m + 1 with hn
  have hnn := hpow n
  have hc' : u ^ n * z ^ n = z ^ n * u ^ n := (hcomm.pow_pow n n).eq.symm
  have he : IsIdempotentElem (z ^ n * u ^ n) := by
    show z ^ n * u ^ n * (z ^ n * u ^ n) = z ^ n * u ^ n
    rw [mul_assoc, ← mul_assoc (u ^ n) (z ^ n) (u ^ n), hc', ← mul_assoc, ← mul_assoc, ← pow_add,
      ← hnn]
  have hez : z ^ n * u ^ n * z ^ n = z ^ n := by
    rw [mul_assoc, hc', ← mul_assoc, ← pow_add, ← hnn]
  have htre : (z ^ n * u ^ n).trace = 0 := by
    have : z ^ n * u ^ n = z * (z ^ m * u ^ n) := by
      show z ^ (m + 1) * u ^ n = _
      rw [pow_succ', mul_assoc]
    rw [this]
    exact htr _ (B.mul_mem (B.pow_mem hzB m) (B.pow_mem huB n))
  have he0 : z ^ n * u ^ n = 0 := by
    have h1 : IsIdempotentElem (Matrix.toLin' (z ^ n * u ^ n)) := by
      unfold IsIdempotentElem at he ⊢
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
    have h2 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff h1).1
      (by rw [Matrix.trace_toLin'_eq, htre])
    exact Matrix.toLin'.injective (by rw [h2, map_zero])
  have hzn : z ^ n = 0 := by rw [← hez, he0, zero_mul]
  have hvn : ∀ k, (z ^ k) *ᵥ v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  rw [← hvn n, hzn, Matrix.zero_mulVec]


open NumberField IsDedekindDomain in
open Polynomial Matrix in
theorem _root_.GlobalTheory.isSSRep_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] [CharZero K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), _root_.Formalism.MainNotions.N.IsSSRep ρ → (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  intro Γ K _ _ _ a ρ hss x hx htrx
  classical
  unfold _root_.Formalism.MainNotions.N.IsSSRep at hss
  set P : Γ → Matrix (Fin a) (Fin a) K :=
    fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) with hP
  have hPmul : ∀ g h, P (g * h) = P g * P h := fun g h => by simp [hP, map_mul]
  have hP1 : P 1 = 1 := by simp [hP]
  have hgen : ∀ g, P g ∈ Submodule.span K (Set.range P) := fun g => Submodule.subset_span ⟨g, rfl⟩
  have hleft : ∀ g, ∀ y ∈ Submodule.span K (Set.range P),
      P g * y ∈ Submodule.span K (Set.range P) := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨h, rfl⟩ := hy; rw [← hPmul]; exact hgen _
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y w _ _ hy hw => rw [mul_add]; exact Submodule.add_mem _ hy hw
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  have hAmul : ∀ y ∈ Submodule.span K (Set.range P), ∀ w ∈ Submodule.span K (Set.range P),
      y * w ∈ Submodule.span K (Set.range P) := by
    intro y hy w hw
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hleft g w hw
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add y t _ _ hy ht => rw [add_mul]; exact Submodule.add_mem _ hy ht
    | smul c y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hy
  let B : Subalgebra K (Matrix (Fin a) (Fin a) K) :=
    { carrier := Submodule.span K (Set.range P)
      mul_mem' := fun hy hw => hAmul _ hy _ hw
      add_mem' := fun hy hw => Submodule.add_mem _ hy hw
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, ← hP1]
        exact Submodule.smul_mem _ c (hgen 1) }
  let J : Matrix (Fin a) (Fin a) K → Prop :=
    fun z => z ∈ Submodule.span K (Set.range P) ∧ ∀ g, (z * P g).trace = 0
  have hJtr : ∀ z, J z → ∀ y ∈ B, (z * y).trace = 0 := by
    intro z hz y hy
    have hy' : y ∈ Submodule.span K (Set.range P) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hg => obtain ⟨g, rfl⟩ := hg; exact hz.2 g
    | zero => simp
    | add y w _ _ h1 h2 => rw [mul_add, Matrix.trace_add, h1, h2, add_zero]
    | smul c y _ h => rw [mul_smul_comm, Matrix.trace_smul, h, smul_zero]
  have hJleft : ∀ g z, J z → J (P g * z) := by
    intro g z hz
    refine ⟨hleft g z hz.1, fun h => ?_⟩
    rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc, ← hPmul]
    exact hz.2 _
  have hJright : ∀ g z, J z → J (z * P g) := by
    intro g z hz
    refine ⟨hAmul _ hz.1 _ (hgen g), fun h => ?_⟩
    rw [mul_assoc, ← hPmul]
    exact hz.2 _
  have hJ0 : J 0 := ⟨Submodule.zero_mem _, fun g => by simp⟩
  have hJadd : ∀ y z, J y → J z → J (y + z) := fun y z hy hz =>
    ⟨Submodule.add_mem _ hy.1 hz.1, fun g => by rw [add_mul, Matrix.trace_add, hy.2, hz.2, add_zero]⟩
  have hJsmul : ∀ (c : K) z, J z → J (c • z) := fun c z hz =>
    ⟨Submodule.smul_mem _ c hz.1, fun g => by rw [smul_mul_assoc, Matrix.trace_smul, hz.2, smul_zero]⟩
  have hfix : ∀ z, J z → ∀ v, z *ᵥ v = v → v = 0 := fun z hz v hv =>
    eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero B hz.1 (hJtr z hz) hv
  have hpres : ∀ S : Submodule K (Fin a → K), _root_.Formalism.MainNotions.N.IsInv ρ S →
      ∀ y ∈ Submodule.span K (Set.range P), ∀ s ∈ S, y *ᵥ s ∈ S := by
    intro S hS y hy s hs
    unfold _root_.Formalism.MainNotions.N.IsInv at hS
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hS g s hs
    | zero => rw [Matrix.zero_mulVec]; exact S.zero_mem
    | add y w _ _ h1 h2 => rw [Matrix.add_mulVec]; exact S.add_mem h1 h2
    | smul c y _ h => rw [Matrix.smul_mulVec]; exact S.smul_mem c h
  let W : Submodule K (Fin a → K) :=
    { carrier := {v | ∀ z, J z → z *ᵥ v = 0}
      add_mem' := fun {v w} hv hw z hz => by rw [Matrix.mulVec_add, hv z hz, hw z hz, add_zero]
      zero_mem' := fun z _ => Matrix.mulVec_zero z
      smul_mem' := fun c v hv z hz => by rw [Matrix.mulVec_smul, hv z hz, smul_zero] }
  have hWst : _root_.Formalism.MainNotions.N.IsInv ρ W := by
    unfold _root_.Formalism.MainNotions.N.IsInv
    intro g v hv
    have hv' : ∀ z, J z → z *ᵥ v = 0 := hv
    show ∀ z, J z → z *ᵥ (P g *ᵥ v) = 0
    intro z hz
    rw [Matrix.mulVec_mulVec]
    exact hv' _ (hJright g z hz)
  obtain ⟨W', hW'st, hcompl⟩ := hss W hWst
  have hW'bot : W' = ⊥ := by
    by_contra hne
    obtain ⟨S, ⟨hSst, hSW', hSne⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
      {S : Submodule K (Fin a → K) | _root_.Formalism.MainNotions.N.IsInv ρ S ∧ S ≤ W' ∧ S ≠ ⊥} ⟨W', hW'st, le_rfl, hne⟩
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
    let T : Submodule K (Fin a → K) :=
      { carrier := {w | ∃ z, J z ∧ z *ᵥ s = w}
        add_mem' := by
          rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, hJadd y z hy hz, Matrix.add_mulVec _ _ _⟩
        zero_mem' := ⟨0, hJ0, Matrix.zero_mulVec _⟩
        smul_mem' := by
          rintro c _ ⟨z, hz, rfl⟩
          exact ⟨c • z, hJsmul c z hz, Matrix.smul_mulVec _ _ _⟩ }
    have hTS : T ≤ S := by
      rintro _ ⟨z, hz, rfl⟩
      exact hpres S hSst z hz.1 s hsS
    have hTst : _root_.Formalism.MainNotions.N.IsInv ρ T := by
      unfold _root_.Formalism.MainNotions.N.IsInv
      rintro g _ ⟨z, hz, rfl⟩
      exact ⟨P g * z, hJleft g z hz, (Matrix.mulVec_mulVec _ _ _).symm⟩
    by_cases hT : T = ⊥
    · apply hs0
      have hsW : s ∈ W := by
        show ∀ z, J z → z *ᵥ s = 0
        intro z hz
        have hzT : z *ᵥ s ∈ T := ⟨z, hz, rfl⟩
        rw [hT] at hzT
        exact (Submodule.mem_bot K).1 hzT
      exact (Submodule.disjoint_def.1 hcompl.disjoint) s hsW (hSW' hsS)
    · have hTeq : T = S := by
        by_contra hTS'
        exact hmin T ⟨hTst, hTS.trans hSW', hT⟩ (lt_of_le_of_ne hTS hTS')
      have hsT : s ∈ T := hTeq ▸ hsS
      obtain ⟨z, hz, hzs⟩ := hsT
      exact hs0 (hfix z hz s hzs)
  have hWtop : W = ⊤ := by
    have h := hcompl.sup_eq_top
    rwa [hW'bot, sup_bot_eq] at h
  have hxJ : J x := ⟨hx, htrx⟩
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [Matrix.zero_mulVec]
  have hv : ∀ z, J z → z *ᵥ v = 0 := (hWtop ▸ Submodule.mem_top : v ∈ W)
  exact hv x hxJ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.LatticeInvariants

lemma tsum_subtype_congr {p q : ℂ → Prop} (f : ℂ → ℂ) (h : ∀ w, f w ≠ 0 → (p w ↔ q w)) :
    ∑' w : {w // p w}, f w = ∑' w : {w // q w}, f w := by
  refine (tsum_subtype {w | p w} f).trans (Eq.trans ?_ (tsum_subtype {w | q w} f).symm)
  congr with w
  by_cases h0 : f w = 0
  · simp [Set.indicator, h0]
  · simp [Set.indicator, h w h0]

lemma eisG_eq_tsum (Λ : AddSubgroup ℂ) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = ∑' w : Λ, ((w : ℂ) ^ (2 * k))⁻¹ := by
  simp only [eisG, one_div]
  refine tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0) (q := fun w ↦ w ∈ Λ)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w hw ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rintro rfl
  simp [hk] at hw

section

variable {L : PeriodPair} {Λ : AddSubgroup ℂ} (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
include h

lemma eisG_eq_G {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  rw [eisG_eq_tsum Λ hk]
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w _ ↦ h w

lemma g2_eq : g2 Λ = L.g₂ := by rw [g2, eisG_eq_G h two_ne_zero]; rfl

lemma lattice_invariant_g3_eq : g3 Λ = L.g₃ := by rw [g3, eisG_eq_G h three_ne_zero]; rfl

lemma wpD_eq (z : ℂ) : wpD Λ z = L.derivWeierstrassP z := by
  rw [wpD, PeriodPair.derivWeierstrassP, neg_mul, ← tsum_mul_left]
  simp only [mul_one_div]
  congr 1
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ 2 / (z - w) ^ 3) fun w _ ↦ h w

lemma wpF_eq (z : ℂ) : wpF Λ z = L.weierstrassP z := by
  rw [← L.weierstrassPExcept_add 0, wpF, add_comm]
  congr 1
  · refine Eq.trans (tsum_congr fun w ↦ ?_) (tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0)
      (q := fun w ↦ w ∈ L.lattice)
      (fun w ↦ if w = 0 then 0 else 1 / (z - w) ^ 2 - 1 / w ^ 2) fun w hw ↦ ?_)
    · rw [if_neg w.2.2]
    · have : w ≠ 0 := by rintro rfl; simp at hw
      simp [h, this]
  · simp

lemma area_eq : area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  refine IsLeast.csInf_eq ⟨⟨?_, L.ω₂, (h _).2 L.ω₂_mem_lattice, L.ω₁, (h _).2 L.ω₁_mem_lattice,
    by rw [mul_comm]⟩, ?_⟩
  · rw [abs_pos]
    intro h0
    have hi := LinearIndependent.pair_iff.mp L.indep
    simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re] at h0
    have h1 := hi L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp
      · ring
      · linarith)
    have h2 := hi L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp
      · linarith
      · ring)
    have h3 : L.ω₂ = 0 := Complex.ext h1.1 h2.1
    simpa using (hi 0 1 (by simp [h3])).2
  · rintro a ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₁)
    obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₂)
    have e : (starRingEnd ℂ (m * L.ω₁ + n * L.ω₂) * (p * L.ω₁ + q * L.ω₂)).im =
        (n * p - m * q : ℤ) * (L.ω₁ * starRingEnd ℂ L.ω₂).im := by
      simp
      ring
    rw [e, abs_mul] at ha ⊢
    have h1 : (n * p - m * q : ℤ) ≠ 0 := by
      intro h0
      simp [h0] at ha
    have h2 : (1 : ℝ) ≤ |((n * p - m * q : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h1
    exact le_mul_of_one_le_left (abs_nonneg _) h2

end

lemma discrete_of_eisG_ne_zero {Λ : AddSubgroup ℂ} {k : ℕ} (hk : k ≠ 0) (h : eisG Λ k ≠ 0) :
    DiscreteTopology Λ := by
  rw [eisG_eq_tsum Λ hk] at h
  have hs : Summable fun w : Λ ↦ ((w : ℂ) ^ (2 * k))⁻¹ := by
    by_contra hs
    exact h (tsum_eq_zero_of_not_summable hs)
  have hf : {w : Λ | ¬ ‖((w : ℂ) ^ (2 * k))⁻¹‖ < 1}.Finite :=
    Filter.eventually_cofinite.1
      ((tendsto_zero_iff_norm_tendsto_zero.1 hs.tendsto_cofinite_zero).eventually_lt_const one_pos)
  refine discreteTopology_iff_isOpen_singleton_zero.2 ?_
  have ho : IsOpen {w : Λ | ‖(w : ℂ)‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  convert ho.sdiff hf.isClosed using 1
  ext w
  simp only [Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_setOf_eq, not_not]
  constructor
  · rintro rfl
    simp [hk]
  · rintro ⟨h1, h2⟩
    by_contra h0
    have h3 : 0 < ‖(w : ℂ)‖ := by simpa using h0
    rw [norm_inv, norm_pow] at h2
    exact absurd h2 (not_lt.2 ((one_le_inv₀ (by positivity)).2 (pow_le_one₀ h3.le h1.le)))

lemma eisG_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ) (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = (a ^ (2 * k))⁻¹ * (2 * riemannZeta (2 * k : ℕ)) := by
  rw [eisG_eq_tsum Λ hk]
  rcases eq_or_ne a 0 with rfl | h0
  · have : ∀ w : Λ, (w : ℂ) = 0 := fun w ↦ by simpa [eq_comm] using h w w.2
    simp [this, hk]
  let e : ℤ → Λ := fun m ↦ ⟨m • a, Λ.zsmul_mem ha m⟩
  have he : Function.Bijective e := ⟨fun m n hmn ↦ by simpa [e, h0] using hmn,
    fun w ↦ (h w w.2).imp fun m hm ↦ Subtype.ext hm⟩
  rw [← (Equiv.ofBijective e he).tsum_eq,
    two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by omega) (even_two_mul k), ← tsum_mul_left]
  congr with m
  simp [e, mul_pow]

lemma discr_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ)
    (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w) : TaylorLogMetric.discr Λ = 0 := by
  have h6 : riemannZeta 6 = Real.pi ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [TaylorLogMetric.discr, g2, g3, eisG_of_cyclic ha h two_ne_zero, eisG_of_cyclic ha h three_ne_zero]
  norm_num only [riemannZeta_four, h6]
  simp only [← inv_pow]
  ring

lemma exists_periodPair_of_discr_ne_zero {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  have hd : DiscreteTopology Λ := by
    by_cases h2 : eisG Λ 2 = 0
    · refine discrete_of_eisG_ne_zero three_ne_zero fun h3 ↦ h ?_
      simp [TaylorLogMetric.discr, g2, g3, h2, h3]
    · exact discrete_of_eisG_ne_zero two_ne_zero h2
  let M : Submodule ℤ ℂ := AddSubgroup.toIntSubmodule Λ
  have hM : DiscreteTopology M := hd
  by_cases hs : Submodule.span ℝ (M : Set ℂ) = ⊤
  · have hZ : IsZLattice ℝ M := ⟨hs⟩
    let b := Module.finBasisOfFinrankEq ℤ M ((ZLattice.rank ℝ M).trans Complex.finrank_real_complex)
    have hi := (b.ofZLatticeBasis ℝ M).linearIndependent
    have e : ⇑(b.ofZLatticeBasis ℝ M) = ![(b 0 : ℂ), b 1] := by
      ext i
      fin_cases i <;> simp
    refine ⟨⟨b 0, b 1, e ▸ hi⟩, fun z ↦ ?_⟩
    change z ∈ M ↔ z ∈ Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)}
    rw [← Matrix.range_cons_cons_empty _ _ ![], ← e, b.ofZLatticeBasis_span ℝ M]
  · have h1 : Module.finrank ℤ M ≤ 1 := by
      have e := Real.finrank_eq_int_finrank_of_discrete (s := (M : Set ℂ))
        (by rw [Submodule.span_eq]; exact hM)
      rw [Set.finrank, Set.finrank, Submodule.span_eq] at e
      have := Submodule.finrank_lt hs
      rw [Complex.finrank_real_complex] at this
      omega
    obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
    exact absurd (discr_of_cyclic (a := v) v.2 fun w hw ↦
      (hv ⟨w, hw⟩).imp fun m hm ↦ congrArg Subtype.val hm) h

lemma exists_periodPair_of_invariants {a b : ℂ} (h : a ^ 3 - 27 * b ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq (1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2))
  let L := periodPairOfTau τ
  have h1 := g₂_cube_div_eq_modularJ one_ne_zero (mem_lattice_periodPairOfTau τ)
  have h0 := g₂_cube_sub_g₃_sq_ne_zero L
  rw [modularJ_def, hτ, div_eq_div_iff h0 h] at h1
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq h0 h (by linear_combination h1 / 1728)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hu (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  refine ⟨scalePeriods L c hc0, ?_, ?_⟩
  · rw [H.g₂_eq, h2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; simp
  · rw [H.g₃_eq, h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; simp

theorem invariants_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  intro L Λ h
  have hΔ : TaylorLogMetric.discr Λ ≠ 0 := by
    rw [TaylorLogMetric.discr, g2_eq h, lattice_invariant_g3_eq h]
    exact g₂_cube_sub_g₃_sq_ne_zero L
  refine ⟨g2_eq h, lattice_invariant_g3_eq h, hΔ, area_eq h, fun z _ ↦ ⟨wpF_eq h z, wpD_eq h z⟩,
    fun Λ' h2 h3 ↦ ?_, fun a b ↦ exists_periodPair_of_invariants⟩
  obtain ⟨L', h'⟩ := exists_periodPair_of_discr_ne_zero (Λ := Λ')
    (by rwa [TaylorLogMetric.discr, h2, h3])
  rw [g2_eq h, g2_eq h'] at h2
  rw [lattice_invariant_g3_eq h, lattice_invariant_g3_eq h'] at h3
  ext z
  rw [h, h', lattice_eq_of_g₂_eq_of_g₃_eq h2 h3]

end GlobalTheory.LatticeInvariants
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RatOfImEqZero
section
namespace GlobalTheory.RationalOfReal

open IntermediateField

theorem exists_coords {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] (β : E) (d : ℚ)
    (hβ : β * β = -(d : E)) (y : E) (hy : y ∈ ℚ⟮β⟯) : ∃ u v : ℚ, y = (u : E) + (v : E) * β := by
  have hint : IsIntegral ℚ β := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : β ^ 2 = algebraMap ℚ E (-d) := by rw [pow_two, hβ]; simp
    rw [this]
    exact isIntegral_algebraMap
  have hy' : y ∈ Algebra.adjoin ℚ ({β} : Set E) := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  clear hy
  induction hy' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - d * v * v', u * v' + v * u', ?_⟩
    push_cast
    linear_combination (v : E) * (v' : E) * hβ

theorem rat_of_im_eq_zero {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] (φ : E →+* ℂ) (β : E)
    (d : ℕ) (hd : 0 < d) (hφ : φ β = Complex.I * (Real.sqrt d : ℂ)) (y : E) (hy : y ∈ ℚ⟮β⟯)
    (him : (φ y).im = 0) : ∃ a : ℚ, y = (a : E) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hβ : β * β = -(((d : ℚ)) : E) := by
    apply φ.injective
    have h2 : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    rw [map_mul, hφ, map_neg, map_ratCast]
    push_cast
    linear_combination (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) * Complex.I_mul_I - h2
  obtain ⟨u, v, rfl⟩ := exists_coords β d hβ y hy
  rw [map_add (f := _), map_mul, map_ratCast, map_ratCast, hφ] at him
  have hv : (v : ℝ) * Real.sqrt d = 0 := by simpa using him
  have hv0 : v = 0 := by
    have := (mul_eq_zero.1 hv).resolve_right hs.ne'
    exact_mod_cast this
  exact ⟨u, by simp [hv0]⟩

theorem rat_of_real (D : Formalism.BasicNotions.D7) (x : D.host.K)
    (hx : (D.host.φ₀ (x : D.host.E)).im = 0) : ∃ a : ℚ, x = (a : D.host.K) := by
  obtain ⟨a, ha⟩ := rat_of_im_eq_zero D.host.φ₀ (D.host.sqd) D.host.d
    D.host.hyp.2.1.pos D.host.φ₀_mem (x : D.host.E) x.2 hx
  exact ⟨a, Subtype.ext (by simpa using ha)⟩

end GlobalTheory.RationalOfReal
end

