module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPeriodRatioMemUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.PeriodQuot

theorem iter_mul {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j : ℕ) (a b : A) : f^[j] (a * b) = f^[j] a * f^[j] b := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem iter_one {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j : ℕ) : f^[j] (1 : A) = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_one]

theorem iter_natCast_mul {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j m q : ℕ) (a : A) : f^[j] ((m : A) ^ q * a) = (m : A) ^ q * f^[j] a := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem galois_periodRatio_mem_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x := by
  intro l _ P AI hT K x hx hn h1 h2 hj g
  obtain ⟨u, rfl⟩ := hx
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  have npos : 0 < n := by
    haveI := (P.PD K).finK₀
    exact Module.finrank_pos
  set y : P.R.B := ((u⁻¹ : (P.R.B)ˣ) : P.R.B) with hy
  have huy : (u : P.R.B) * y = 1 := u.mul_inv
  set c : P.R.B := P.actQ (g : GQ l) u * y with hc
  have hcx : P.actQ (g : GQ l) u = c * u := by rw [hc, mul_assoc, u.inv_mul, mul_one]
  have hcomm : ∀ b, P.φB (P.actQ (g : GQ l) b) = P.actQ (g : GQ l) (P.φB b) := by
    intro b
    have := (P.PD K).φ_comm g b
    rwa [P.PD_φ, P.PD_actB, P.PD_actB, P.PD_φ] at this
  have hcommj : ∀ j b, (⇑P.φB)^[j] (P.actQ (g : GQ l) b) = P.actQ (g : GQ l) ((⇑P.φB)^[j] b) :=
    fun j b => (Function.Commute.iterate_left (f := ⇑P.φB) (g := ⇑(P.actQ (g : GQ l)))
      (fun b => hcomm b) j) b

  have hlB : IsUnit ((l : ℕ) : P.R.B) := by
    have h0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have := (isUnit_iff_ne_zero.mpr h0).map (algebraMap ℚ_[l] P.R.B)
    simpa using this

  have hφc : (⇑P.φB)^[n] c = c := by
    have hu : IsUnit ((l : P.R.B) * u) := hlB.mul u.isUnit
    apply hu.mul_left_injective
    show (⇑P.φB)^[n] c * ((l : P.R.B) * u) = c * ((l : P.R.B) * u)
    rw [← hn, ← iter_mul, ← hcx, hcommj, hn, map_mul, map_natCast, hcx]
    ring

  have hpow : ∀ q : ℕ, (⇑P.φB)^[n * q] (u : P.R.B) = (l : P.R.B) ^ q * u := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hn,
        show (l : P.R.B) * (u : P.R.B) = (l : P.R.B) ^ 1 * u by rw [pow_one],
        iter_natCast_mul, ih, ← mul_assoc, ← pow_add, add_comm 1 q]
  have hsmul : ∀ (q : ℕ) (z : P.R.B), P.ιB ((l : P.R.B) ^ q * z) =
      (((l : ↥K.1) ^ q : ↥K.1)) • P.ιB z := by
    intro q z
    rw [map_mul, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  have hne : ∀ q : ℕ, ((l : ↥K.1) ^ q : ↥K.1) ≠ 0 := fun q =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hdeg : ∀ j : ℕ, ∃ d : ℤ, P.ιB ((⇑P.φB)^[j] (u : P.R.B)) ∈ (P.PD K).Fil d ∧
      P.ιB ((⇑P.φB)^[j] (u : P.R.B)) ∉ (P.PD K).Fil (d + 1) := by
    intro j
    have hj_eq : j = j % n + n * (j / n) := (Nat.mod_add_div j n).symm
    have hw : (⇑P.φB)^[j] (u : P.R.B) = (l : P.R.B) ^ (j / n) * (⇑P.φB)^[j % n] u := by
      conv_lhs => rw [hj_eq]
      rw [Function.iterate_add_apply, hpow, iter_natCast_mul]
    rw [hw, hsmul]
    rcases Nat.eq_zero_or_pos (j % n) with h0 | hr
    · refine ⟨1, ?_, ?_⟩
      · rw [h0, Function.iterate_zero_apply]
        exact Submodule.smul_mem _ _ h1
      · rw [h0, Function.iterate_zero_apply, Submodule.smul_mem_iff _ (hne _)]
        simpa using h2
    · obtain ⟨ha, hb⟩ := hj (j % n) hr (Nat.mod_lt _ npos)
      refine ⟨0, Submodule.smul_mem _ _ ha, ?_⟩
      rw [Submodule.smul_mem_iff _ (hne _)]
      simpa using hb
  have hF : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0 := by
    intro j
    obtain ⟨d, hd1, hd2⟩ := hdeg j
    have hinv : P.ιB ((⇑P.φB)^[j] (u : P.R.B)) * P.ιB ((⇑P.φB)^[j] y) = 1 := by
      rw [← map_mul, ← iter_mul, huy, iter_one, map_one]
    have hyF := _root_.GlobalTheory.FilInv.inv_mem_Fil_neg l P AI hT K d _ _ hinv hd1 hd2
    have hgF : P.ιB (P.actQ (g : GQ l) ((⇑P.φB)^[j] (u : P.R.B))) ∈ (P.PD K).Fil d := by
      have := (P.PD K).ι_comm g ((⇑P.φB)^[j] (u : P.R.B))
      rw [P.PD_ι, P.PD_actB, P.PD_ι] at this
      rw [this]
      exact (P.PD K).Fil_G g d _ hd1
    have := (P.PD K).Fil_mul d (-d) _ _ hgF hyF
    rw [add_neg_cancel] at this
    rw [hc, iter_mul, hcommj, map_mul]
    exact this
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt l P AI hT K c hφc hF
  exact ⟨a, by rw [hcx, ha]⟩

end GlobalTheory.PeriodQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGl
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.UnitaryDual GlobalTheory.GenericUnitary

namespace GlobalTheory.GenericUnitaryBridge

theorem eq_of_isSpeh_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ w : IrrGL (k := k)} (h : IsSpeh δ 1 w.rep) : w = δ := by
  obtain ⟨n, c⟩ := w
  obtain ⟨n', c'⟩ := δ
  obtain ⟨hd1, hc1⟩ := h
  obtain ⟨hd2, hc2⟩ := isSpeh_one (⟨n', c'⟩ : IrrGL (k := k))
  obtain rfl : n = n' := hd1.symm.trans hd2
  obtain ⟨φ⟩ := hc2.unique hc1
  exact ((IrrGL.of_rep _).symm.trans (IrrGL.of_eq_of.2 ⟨φ⟩)).trans (IrrGL.of_rep _)

theorem of_lemmas (hA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) (hB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π) (hD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep) (hF : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ), (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ))) :
    GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL →
      GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := by
  intro hU hSq hGen hLM hSC k _ _ _ _ _ N V _ _ π hs hi hu hg
  have ord := GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes k
  let Good : Segment k → Prop := fun Δ => ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)
  have key : ∀ (w : IrrGL (k := k)) (r : ℝ), IsUnitarySpeh w → ∃ 𝔫 : Multiset (Segment k), IsL 𝔫 (w.nu (r : ℂ)).rep ∧
      (∀ Γ ∈ 𝔫, Good Γ) ∧ (IsUnitaryLSeg w ∨ ∃ (Γ : Segment k) (t : ℝ), Γ.nu (t : ℂ) ∈ 𝔫 ∧
        Γ.nu ((t - 1 : ℝ) : ℂ) ∈ 𝔫) := by
    rintro w r ⟨δ, m, hsq, hm, hsp⟩
    obtain ⟨Δ, hΔ⟩ := hSq k δ hsq
    refine ⟨_, hD k ord δ w Δ m hΔ hsq.2.1 hsp r, ?_, ?_⟩
    · intro Γ hΓ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hΓ)
      exact ⟨δ, Δ, _, hΔ, hsq.2.1, rfl⟩
    · rcases Nat.lt_or_ge m 2 with h2 | h2
      · left
        obtain rfl : m = 1 := by omega
        obtain rfl := eq_of_isSpeh_one hsp
        exact ⟨⟨Δ, hΔ⟩, hsq.2.1⟩
      · right
        refine ⟨Δ, r + ((m : ℝ) - 1) / 2, Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨0, by omega⟩, ?_⟩),
          Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨1, by omega⟩, ?_⟩)⟩
        · simp
        · congr 2
          push_cast
          ring
  obtain ⟨u, τ, hu1, hτ1, h, x, hd, hx, ⟨φ⟩⟩ := hU k N V π hs hi hu
  have hfac : ∀ j, ∃ (y : IrrGL (k := k)) (s : ℝ), IsUnitarySpeh y ∧ x j = y.nu (s : ℂ) := by
    intro j
    have hm : x j ∈ factors u τ := hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact ⟨x j, 0, hu1 _ hm, by simp⟩
    · obtain ⟨p, hp, hm⟩ := List.mem_flatMap.1 hm
      rcases List.mem_pair.1 hm with e | e
      · exact ⟨p.1, p.2, (hτ1 p hp).1, e⟩
      · exact ⟨p.1, -p.2, (hτ1 p hp).1, e⟩
  choose y s hy hxs using hfac
  have h𝔪 : ∀ j, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (x j).rep ∧ ∀ Γ ∈ 𝔪, Good Γ := fun j => by
    obtain ⟨𝔪, h1, h2, -⟩ := key (y j) (s j) (hy j)
    exact ⟨𝔪, hxs j ▸ h1, h2⟩
  choose 𝔪 h𝔪L h𝔪G using h𝔪
  have hL : IsL (∑ j, 𝔪 j) π :=
    hB k hLM Good (fun 𝔫 h𝔫 => hA k hSC ord 𝔫 h𝔫) h N x hd 𝔪 h𝔪L h𝔪G V π hi ⟨φ⟩
  obtain ⟨h', Δ', z, hd', hunl, hz, ⟨ψ⟩⟩ := hGen k N V π hs hi hg
  have hL' : IsL (Finset.univ.val.map Δ') π :=
    ⟨h', z, hd', ⟨Δ', ⟨rfl, fun i j hij hP => hunl i j hij.ne hP.1⟩, hz⟩,
      (isCosocle_self hi).of_equiv (.refl _) ψ⟩
  have heq : ∑ j, 𝔪 j = Finset.univ.val.map Δ' :=
    (hLM k).1 _ _ (IrrGL.of π hs hi) (hL.of_equiv (IrrGL.equivOf π hs hi)) (hL'.of_equiv (IrrGL.equivOf π hs hi))
  have hno : ∀ Γ ∈ ∑ j, 𝔪 j, ∀ Γ' ∈ ∑ j, 𝔪 j, ¬ Γ.Linked Γ' := by
    rw [heq]
    intro Γ hΓ Γ' hΓ' hl
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΓ
    obtain ⟨i', -, rfl⟩ := Multiset.mem_map.1 hΓ'
    by_cases e : i = i'
    · subst e
      exact Segment.not_linked_self _ hl
    · exact hunl i i' e hl
  have hgood : ∀ (w : IrrGL (k := k)) (r : ℝ), IsUnitarySpeh w → w.nu (r : ℂ) ∈ List.ofFn x → IsUnitaryLSeg w := by
    intro w r hw hmem
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 hmem
    obtain ⟨𝔫, h1, -, h3⟩ := key w r hw
    rcases h3 with h3 | ⟨Γ, t, h4, h5⟩
    · exact h3
    · have e : 𝔫 = 𝔪 j := (hLM k).1 _ _ (x j) (hj ▸ h1) (h𝔪L j)
      subst e
      exact absurd (hF k Γ t) (hno _ (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h4⟩) _
        (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h5⟩))
  refine ⟨u, τ, fun w hw => hgood w 0 (hu1 w hw) ?_, fun p hp => ⟨hgood p.1 p.2 (hτ1 p hp).1 ?_, (hτ1 p hp).2⟩,
    h, x, hd, hx, ⟨φ⟩⟩
  · rw [hx]
    simp only [Complex.ofReal_zero, IrrGL.nu_zero]
    exact List.mem_append_left _ hw
  · rw [hx]
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, by simp⟩)

theorem genericUnitaryDualGL_of_hypotheses : GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment →
    GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL →
    GlobalTheory.Published.GenericUnitaryDualGL :=
  of_lemmas GlobalTheory.T.langlands_classification_unitary GlobalTheory.T.standard_module_properties GlobalTheory.T.speh_langlands_quotient _root_.GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one

end GlobalTheory.GenericUnitaryBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfRowsGuarded
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSpan

theorem hkSS_of_rows_guarded {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y)
    (hG : CommG D) (hC : HkComm D) (hSF : SupFull D)
    (X : NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0))
    (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (hEmb : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x,
      D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x))
    (hBr : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, LinearMap.range (D.nexp.embB i j b) =
      D.nexp.Bsup i j b ⊓ (V0 D.nexp i j b).restrictScalars (D.ntw.O i))
    (hSp : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ((LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).Splits) :
    HkSS D := by
  intro i hi j hj b
  have := D.nexp.towFm i j b

  have hspan : ∀ x ∈ V0 D.nexp i j b,
      x ∈ Submodule.span (FractionRing (D.ntw.O i)) (Set.range (D.nexp.embB i j b)) := by
    intro x hx
    have hx' : x ∈ Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) := by
      rw [(hSF i hi j hj b).2]; exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (D.ntw.O i))).1 hx'
    rw [Submodule.span_eq] at hy
    have hyV : y ∈ V0 D.nexp i j b := by
      have e : y = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (z : D.ntw.O i)) •
          (IsLocalization.mk' (FractionRing (D.ntw.O i)) (1 : D.ntw.O i) z • y) := by
        rw [smul_smul, mul_comm, IsLocalization.mk'_spec, map_one, one_smul]
      rw [e]; exact Submodule.smul_mem _ _ hx
    have hyR : y ∈ LinearMap.range (D.nexp.embB i j b) := by
      rw [hBr i hi j hj b]
      exact Submodule.mem_inf.2 ⟨hy, (Submodule.restrictScalars_mem _ _ _).2 hyV⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (LinearMap.mem_range.1 hyR))

  have hpoly : ∀ k P, HkIdx i k P → ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧ p.Splits ∧
      ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
    intro k P hkP
    obtain ⟨p1, hp10, hp1s, hp1k⟩ := _root_.GlobalTheory.charpoly_split_kills_span (D.ntw.O i) (D.nexp.Fm i j b) (D.ntw.B i j b)
      (D.nexp.embB i j b) (D.ntw.hk i j b k P) (D.nexp.hkF i j b k P) (hEmb i hi j hj b k P hkP)
      (hSp i hi j hj b k P hkP)
    obtain ⟨p2, hp2s, hp2k⟩ :=
      GlobalTheory.GoodSS.hkF_separable Rl F cG S Y H hG hC X hR hU hI hS0c hS02 hS0b i hi j hj b k P hkP
    classical
    refine ⟨EuclideanDomain.gcd p1 p2, hp2s.of_dvd (EuclideanDomain.gcd_dvd_right _ _),
      hp1s.of_dvd hp10 (EuclideanDomain.gcd_dvd_left _ _), ?_⟩
    intro x hx
    rw [EuclideanDomain.gcd_eq_gcd_ab, mul_comm p1, mul_comm p2, map_add (f := _), map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp1k x (hspan x hx), hp2k x hx,
      map_zero, map_zero, add_zero]

  have hJ := GlobalTheory.JointDiag.le_iSup_jointEigenspace_inf (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) {a : ℕ × PlE D.host // HkIdx i a.1 a.2}
    (fun a => D.nexp.hkF i j b a.1.1 a.1.2) (V0 D.nexp i j b)
    (fun a c => hC i hi j hj b _ _ _ _ a.2 c.2)
    (fun a x hx => _root_.GlobalTheory.HkGoodStable.hkF_mem_V0 D hG i hi j hj b _ _ a.2 x hx)
    (fun a => hpoly _ _ a.2)
  refine hJ.trans (iSup_le fun ev => ?_)
  classical
  refine le_iSup_of_le (fun k P => if h : HkIdx i k P then ev ⟨(k, P), h⟩ else 0) (inf_le_inf_right _ ?_)
  unfold Eigsp
  refine le_iInf fun k => le_iInf fun P => le_iInf fun h => ?_
  refine (iInf_le _ ⟨(k, P), h⟩).trans ?_
  simp only [dif_pos h]
  exact le_rfl

end GlobalTheory.GoodSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficients
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo_mat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)), IsRat r σ → (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) → (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) → (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) → (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) = (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) → ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) = ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  intro l _ P AI T n _ _ K r σ Q hσ hQ c hcr hcc hcoc hdR
  obtain ⟨ω, W, hW, hω, hcoef⟩ := _root_.GlobalTheory.PMon.coef_unr_continuous l r hσ.pos
  obtain ⟨ρ₀, p, hρc, hpK, hint, hc₀⟩ := _root_.GlobalTheory.PMon.exists_ratForm l n K r σ ω W hσ hW hω hcoef
  obtain ⟨c₀, hc₀c, hpc⟩ := hc₀ c hcr hcc
  have hcoc₀ := _root_.GlobalTheory.PMon.cocycle_rat_coords l n K r σ ρ₀ p c c₀ hint hpc hcoc
  obtain ⟨Q₀, hQ₀⟩ := _root_.GlobalTheory.PMon.period_resScalars l P n K r σ Q ρ₀ p hQ hpK hint
  have hsst : IsSst P (repOf ρ₀) :=
    _root_.GlobalTheory.PMon.isSst_of_periodMatrix l P AI T (n × Fin r) K (n × Fin r → ℚ_[l]) (Pi.basisFun ℚ_[l] _) (repOf ρ₀) Q₀
      (fun g => by rw [toMatrix_repOf]; exact hQ₀ g)
  obtain ⟨β, hβ⟩ := _root_.GlobalTheory.PMon.DRvec.ratCocycle_trivial l P n K r σ ρ₀ p c c₀ hpK hint hpc hdR
  obtain ⟨bd, hbd⟩ := _root_.GlobalTheory.CobColumn.coboundary_tmul_of_column l P K _ ρ₀ c₀ β hβ
  have hcontρ : ∀ v : n × Fin r → ℚ_[l], Continuous fun g => repOf ρ₀ g v := by
    intro v
    simp only [repOf_apply]
    refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (hρc i j).mul continuous_const
  obtain ⟨bs, hbs⟩ := _root_.GlobalTheory.PMon.hyodo l P AI T K (n × Fin r → ℚ_[l]) (repOf ρ₀) hcontρ hsst c₀ hc₀c
    hcoc₀ ⟨bd, hbd⟩
  obtain ⟨β', hβ'⟩ := _root_.GlobalTheory.PMonCob.coboundary_cols l P K _ ρ₀ c₀ bs hbs
  exact _root_.GlobalTheory.PMon.coboundary_block_zero l P n K r hσ.pos σ ρ₀ p c c₀ β' hpK hint hpc hβ'

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralEqTsumRealPointsLevelCosetTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CosetSum

open GlobalTheory.AutMult

theorem mem_realLevSet_iff {D : D7} {W : HSp D} {K : Subgroup (GA D W)} (hK : K ≤ GfC W) (h : GA D W) :
    (∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k) ↔ toFin W h ∈ K.subgroupOf (GfC W) := by
  constructor
  · rintro ⟨u, hu, k, hk, rfl⟩
    have h1 : toFin W u = 1 := toFin_coe_inf (V := W) ⟨u, hu⟩
    have h2 : toFin W k = ⟨k, hK hk⟩ := toFin_coe (V := W) ⟨k, hK hk⟩
    rw [map_mul, h1, h2, one_mul, Subgroup.mem_subgroupOf]
    exact hk
  · intro h'
    exact ⟨toInf W h, (toInf W h).2, toFin W h, (Subgroup.mem_subgroupOf).1 h', (toInf_mul_toFin h).symm⟩

theorem integral_eq_sum_cosets : ∀ (D : D7) (W : HSp D) (ν : Measure (GA D W)) (K : Subgroup (GA D W)), ν.IsHaarMeasure → K ≤ GfC W → IsOpen {g : GfC W | (g : GA D W) ∈ K} → ∀ Φ : GA D W → ℂ, Integrable Φ ν → MeasurableSet {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} ∧ HasSum (fun q : GfC W ⧸ K.subgroupOf (GfC W) => ∫ h in {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k}, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) (∫ g, Φ g ∂ν) := by
  intro D W ν K hν hKf hKo Φ hΦ
  obtain ⟨i0, -, i2, -, i4, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D W
  haveI := i0; haveI := i2; haveI := i4
  set K' := K.subgroupOf (GfC W) with hK'
  set C : Set (GA D W) := {h : GA D W | ∃ u ∈ GinfC W, ∃ k ∈ K, h = u * k} with hCdef
  have hK'o : IsOpen (K' : Set (GfC W)) := hKo
  have hC : C = toFin W ⁻¹' (K' : Set (GfC W)) := Set.ext fun h => mem_realLevSet_iff hKf h
  have hCo : IsOpen C := hC ▸ hK'o.preimage (continuous_toFin W)
  have hCm : MeasurableSet C := hCo.measurableSet
  refine ⟨hCm, ?_⟩

  let s : GfC W ⧸ K' → Set (GA D W) := fun q => (fun g => ((Quotient.out q : GfC W) : GA D W)⁻¹ * g) ⁻¹' C
  have hmem : ∀ q g, g ∈ s q ↔ q = QuotientGroup.mk (toFin W g) := by
    intro q g
    show _ ∈ C ↔ _
    rw [hC, Set.mem_preimage, map_mul, map_inv, toFin_coe, SetLike.mem_coe]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq]
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_mul _) hCm
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    exact Set.disjoint_left.2 fun g h1 h2 => hne (((hmem q g).1 h1).trans ((hmem q' g).1 h2).symm)
  have hU : (⋃ q, s q) = Set.univ := Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, (hmem _ g).2 rfl⟩

  haveI : Countable (GfC W ⧸ K') := by
    have hpd : (Set.univ : Set (GfC W ⧸ K')).PairwiseDisjoint
        (fun q => (fun x => (Quotient.out q : GfC W)⁻¹ * x) ⁻¹' (K' : Set (GfC W))) := by
      intro q _ q' _ hne
      refine Set.disjoint_left.2 fun x h1 h2 => hne ?_
      have e1 : QuotientGroup.mk (Quotient.out q) = (QuotientGroup.mk x : GfC W ⧸ K') := QuotientGroup.eq.2 h1
      have e2 : QuotientGroup.mk (Quotient.out q') = (QuotientGroup.mk x : GfC W ⧸ K') := QuotientGroup.eq.2 h2
      rw [QuotientGroup.out_eq'] at e1 e2
      exact e1.trans e2.symm
    exact Set.countable_univ_iff.1 (hpd.countable_of_isOpen
      (fun q _ => hK'o.preimage (continuous_const.mul continuous_id))
      (fun q _ => ⟨Quotient.out q, by simp [K'.one_mem]⟩))
  have hsum := hasSum_integral_iUnion hsm hd (by rw [hU]; exact hΦ.integrableOn)
  rw [hU, Measure.restrict_univ] at hsum
  refine (funext fun q => ?_ : (fun q : GfC W ⧸ K' => ∫ h in C, Φ (((Quotient.out q : GfC W) : GA D W) * h) ∂ν) =
    fun q => ∫ x in s q, Φ x ∂ν) ▸ hsum
  have hpre : (fun h => ((Quotient.out q : GfC W) : GA D W) * h) ⁻¹' s q = C := by
    ext h; simp [s]
  rw [← hpre]
  exact ((measurePreserving_mul_left ν _).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft _) Φ (s q))

end GlobalTheory.CosetSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSphericalStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedChar_of_cuspidal_spherical : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), x.IsCusp → IsSpherical x.rep → x.IsUnramChar := by
  first | exact @GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical | exact GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical | (intros; apply GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical <;> assumption)
end

