module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0010
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0078
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0009

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CommonMult
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gen_red {M : Type*} [AddCommGroup M] (P : Submodule ℤ M) (hP : P.FG) (N : ℤ) (hN : N ≠ 0) :
    ∃ Rs : Set M, Rs.Finite ∧ ∀ x ∈ P, ∃ q ∈ P, ∃ ρ ∈ Rs, x = N • q + ρ := by
  obtain ⟨s, hs⟩ := hP
  refine ⟨Set.range (fun r : s → Fin N.natAbs => ∑ g : s, ((r g : ℕ) : ℤ) • (g : M)), Set.finite_range _, ?_⟩
  intro x hx
  rw [← hs] at hx
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hx
  refine ⟨∑ g ∈ s, (f g / N) • g, ?_, ∑ g ∈ s, (f g % N) • g, ?_, ?_⟩
  · rw [← hs]
    exact Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span hg)
  · refine ⟨fun g => ⟨(f g % N).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (f g) hN
      have h2 := Int.emod_lt (f g) hN
      omega
    · rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN)]
  · rw [← hf, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_smul, ← add_smul, Int.mul_ediv_add_emod]

theorem int_mult (D : Formalism.BasicNotions.D7) (s : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k ∈ s, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨n, hn, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  exact ⟨n, hn, fun k hk => ⟨⟨n • k, h k hk⟩, zsmul_eq_mul k n⟩⟩

theorem lat_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (v : (VS D).V) : ∃ n : ℤ, n ≠ 0 ∧ (n : D.host.E) • v ∈ Λ := by
  exact UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D hΛ v

theorem common_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (vs : Finset (VS D).V) (ks : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ (∀ v ∈ vs, (n : D.host.E) • v ∈ Λ) ∧
      ∀ k ∈ ks, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have hv : ∃ n : ℤ, n ≠ 0 ∧ ∀ v ∈ vs, (n : D.host.E) • v ∈ Λ := by
    induction vs using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert v vs hv ih =>
      obtain ⟨n, hn, h⟩ := ih
      obtain ⟨m, hm, hmv⟩ := lat_mult D hΛ v
      refine ⟨m * n, mul_ne_zero hm hn, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · have : ((m * n : ℤ) : D.host.E) • w = (n : D.host.E) • ((m : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul, mul_comm]
        rw [this]; exact smul_int_mem D ⟨n, by simp⟩ hmv
      · have : ((m * n : ℤ) : D.host.E) • w = (m : D.host.E) • ((n : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul]
        rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h w hw)
  obtain ⟨n, hn, h1⟩ := hv
  obtain ⟨m, hm, h2⟩ := int_mult D ks
  refine ⟨n * m, mul_ne_zero hn hm, fun v hv => ?_, fun k hk => ?_⟩
  · have : ((n * m : ℤ) : D.host.E) • v = (m : D.host.E) • ((n : D.host.E) • v) := by
      rw [smul_smul, Int.cast_mul, mul_comm]
    rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h1 v hv)
  · obtain ⟨o, ho⟩ := h2 k hk
    refine ⟨(n : 𝓞 D.host.E) * o, ?_⟩
    rw [map_mul, ho, map_intCast]; push_cast; ring

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSC
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel

theorem latBasis_exists (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (S : Submodule 𝒪[F] (Fin n → F))
    (hfg : S.FG) (hsp : Submodule.span F (S : Set (Fin n → F)) = ⊤) :
    ∃ b : Module.Basis (Fin n) F (Fin n → F), (∀ k, b k ∈ S) ∧
      ∀ v, v ∈ S ↔ ∀ k, b.repr v k ∈ 𝒪[F] := by
  have : Module.Finite 𝒪[F] S := Module.Finite.of_fg hfg
  have : S.IsLattice F := Submodule.IsLattice.of_fg F hfg
  have : S.IsFullLattice F := ⟨hsp⟩
  have hr : Module.finrank 𝒪[F] S = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq F S).trans (Module.finrank_fintype_fun_eq_card F))
  have : Module.Free 𝒪[F] S := Submodule.IsLattice.free F S
  let b0 : Module.Basis (Fin n) 𝒪[F] S := Module.finBasisOfFinrankEq 𝒪[F] S hr
  let b := b0.extendOfIsFullLattice F
  have hb : ∀ k, b k = (b0 k : Fin n → F) := fun k => by simp [b]
  refine ⟨b, fun k => by rw [hb]; exact (b0 k).2, fun v => ⟨fun hv k => ?_, fun h => ?_⟩⟩
  · have key : v = b.equivFun.symm (fun k => ((b0.repr ⟨v, hv⟩ k : 𝒪[F]) : F)) := by
      rw [Module.Basis.equivFun_symm_apply]
      have h1 : ∑ i, ((b0.repr ⟨v, hv⟩ i • b0 i : S) : Fin n → F) = v := by
        rw [← Submodule.coe_sum, b0.sum_repr]
      conv_lhs => rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Submodule.coe_smul]
      rfl
    have h2 := congrArg b.equivFun key
    rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at h2
    rw [h2]
    exact (b0.repr ⟨v, hv⟩ k).2
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun k _ => ?_
    have := S.smul_mem (⟨b.repr v k, h k⟩ : 𝒪[F]) (show b k ∈ S by rw [hb]; exact (b0 k).2)
    exact this

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

end Herm

section Coord

variable {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V]

def sig (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x : V) : (Fin n → F) × (Fin n → F) :=
  (fun k => (e (β.repr x k)).1, fun k => (e (β.repr x k)).2)

def tau (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p : (Fin n → F) × (Fin n → F)) : V :=
  ∑ k, e.symm (p.1 k, p.2 k) • β k

theorem sig_tau (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p : (Fin n → F) × (Fin n → F)) :
    sig e β (tau e β p) = p := by
  unfold sig tau
  first
  | simp only [Basis.repr_sum_self, AlgEquiv.apply_symm_apply]
  | simp [map_sum, Finsupp.single_apply]

theorem tau_sig (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x : V) :
    tau e β (sig e β x) = x := by
  unfold sig tau
  simp only [Prod.mk.eta, AlgEquiv.symm_apply_apply]
  exact β.sum_repr x

theorem sig_add (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x y : V) :
    sig e β (x + y) = sig e β x + sig e β y := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_add (f := _)]

theorem sig_smul (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (a : E) (x : V) :
    sig e β (a • x) = ((e a).1 • (sig e β x).1, (e a).2 • (sig e β x).2) := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_mul]

theorem tau_add (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p q : (Fin n → F) × (Fin n → F)) :
    tau e β (p + q) = tau e β p + tau e β q := by
  unfold tau
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul, ← map_add (f := _)]
  rfl

theorem tau_smul (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (a : E)
    (p : (Fin n → F) × (Fin n → F)) :
    tau e β ((e a).1 • p.1, (e a).2 • p.2) = a • tau e β p := by
  unfold tau
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  have h1 : (((e a).1 • p.1) k, ((e a).2 • p.2) k) = e a * (p.1 k, p.2 k) :=
    Prod.ext (by simp) (by simp)
  rw [h1, map_mul, AlgEquiv.symm_apply_apply]

theorem sig_zero (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) : sig e β 0 = 0 := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig]

end Coord

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlCoeMul
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

theorem fl_hensel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    (hl : IsNonarchimedeanLocalField F) : HenselianRing 𝒪[F] 𝓂[F] := by
  haveI := hl
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  exact IsAdicComplete.henselianRing _ _

theorem fl_coe_mul {F : Type} [Field F] [ValuativeRel F] (a b : 𝒪[F]) :
    ((a * b : 𝒪[F]) : F) = (a : F) * b := rfl

theorem fl_sq_div {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (b n : 𝒪[F]) (hbn : b * b = n) (hn : n ∈ 𝓂[F]) :
    ∃ z ∈ L.O, algebraMap F E b = algebraMap F E ϖ * z := by
  haveI := hl
  have hb : b ∈ 𝓂[F] := by
    have h2 : b * b ∈ 𝓂[F] := hbn ▸ hn
    rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem h2 with h | h <;> exact h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  exact ⟨algebraMap F E c, fl_int_mem L c, by rw [fl_coe_mul, map_mul]⟩

theorem fl_local {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hinj : Function.Injective (algebraMap F E))
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x ∈ L.O, (¬ ∃ z ∈ L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ L.O, x * y = 1 := by
  intro x hx hnd
  haveI := hl
  obtain ⟨n, hn⟩ := fl_norm L hinj hx
  obtain ⟨t, ht⟩ := fl_trace L hinj hx
  have hquad : x * x = algebraMap F E t * x - algebraMap F E n := by
    rw [ht, hn]; ring
  by_cases hnu : IsUnit n
  · obtain ⟨u, rfl⟩ := hnu
    refine ⟨L.cj x * algebraMap F E ((↑u⁻¹ : 𝒪[F]) : F), mul_mem (fl_cj_mem L hx) (fl_int_mem L _), ?_⟩
    rw [← mul_assoc, ← hn, ← map_mul, ← fl_coe_mul, Units.mul_inv]
    simp
  · exfalso
    have hnm : n ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal n).2 hnu
    have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    by_cases htm : t ∈ 𝓂[F]
    · apply hnd
      rw [hspan, Ideal.mem_span_singleton] at htm hnm
      obtain ⟨t', rfl⟩ := htm
      obtain ⟨n', rfl⟩ := hnm
      have hsp : x * x ∈ Submodule.span L.O {algebraMap F E ϖ} := by
        refine Submodule.mem_span_singleton.2 ⟨⟨algebraMap F E t' * x - algebraMap F E n',
          sub_mem (mul_mem (fl_int_mem L t') hx) (fl_int_mem L n')⟩, ?_⟩
        rw [hquad, fl_coe_mul, fl_coe_mul, map_mul, map_mul]
        show (algebraMap F E t' * x - algebraMap F E n') * algebraMap F E ϖ = _
        ring
      obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 (L.unram ϖ hϖ x hx hsp)
      exact ⟨z, z.2, by rw [← hz, Subring.smul_def]; exact mul_comm _ _⟩
    · haveI := fl_hensel hl
      haveI := IsLocalRing.maximalIdeal.isMaximal 𝒪[F]
      let f : Polynomial 𝒪[F] := X ^ 2 + (C n - C t * X)
      have hf : f.Monic := by
        refine (monic_X_pow 2).add_of_left ?_
        rw [degree_X_pow]
        refine lt_of_le_of_lt (degree_sub_le _ _) ?_
        exact max_lt (lt_of_le_of_lt degree_C_le (by norm_num))
          (lt_of_le_of_lt (degree_C_mul_X_le t) (by norm_num))
      have h0 : f.eval 0 ∈ 𝓂[F] := by simpa [f] using hnm
      have h1 : IsUnit (Ideal.Quotient.mk 𝓂[F] (f.derivative.eval 0)) := by
        letI := Ideal.Quotient.field 𝓂[F]
        have hne : Ideal.Quotient.mk 𝓂[F] (f.derivative.eval 0) ≠ 0 := by
          rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
          simpa [f, Polynomial.derivative_sub, Polynomial.derivative_mul] using htm
        exact hne.isUnit
      obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian f hf 0 h0 h1
      have hroot : a ^ 2 + (n - t * a) = 0 := by simpa [f, Polynomial.IsRoot] using ha
      have hrootE : algebraMap F E (a : F) ^ 2 + (algebraMap F E (n : F) -
          algebraMap F E (t : F) * algebraMap F E (a : F)) = 0 := by
        have := congrArg (fun r : 𝒪[F] => algebraMap F E (r : F)) hroot
        simpa [map_sub, map_mul, map_pow, map_add (f := _)] using this
      have hfac : (x - algebraMap F E (a : F)) * (x - (algebraMap F E (t : F) - algebraMap F E (a : F))) = 0 := by
        linear_combination hquad - hrootE
      have hxF : ∃ b : 𝒪[F], x = algebraMap F E (b : F) := by
        by_cases hxa : x - algebraMap F E (a : F) = 0
        · exact ⟨a, sub_eq_zero.1 hxa⟩
        · obtain ⟨u, hu⟩ := hE _ hxa
          have : x - (algebraMap F E (t : F) - algebraMap F E (a : F)) = 0 := by
            have h2 := congrArg (fun y => (↑u⁻¹ : E) * y) hfac
            simp only [mul_zero] at h2
            rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h2
            exact h2
          refine ⟨t - a, ?_⟩
          rw [sub_eq_zero.1 this]
          simp
      obtain ⟨b, rfl⟩ := hxF
      have hcj : L.cj (algebraMap F E (b : F)) = algebraMap F E (b : F) := L.cj.commutes _
      rw [hcj, ← map_mul, ← fl_coe_mul] at hn
      have hbn : b * b = n := Subtype.val_injective (hinj hn).symm
      exact hnd (fl_sq_div L hl ϖ hϖ b n hbn hnm)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlatBasisOf
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

theorem flb_main {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hnt : Nontrivial E)
    (hden : ∀ x : E, ∃ s ∈ M.L.O, s ≠ 0 ∧ s * x ∈ M.L.O)
    (hpid : IsPrincipalIdealRing M.L.O)
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ) :
      ∃ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) ∧ LinearIndependent E b ∧
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) ∧
        ∃ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) ∧
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1 := by
  classical
  haveI : NoZeroDivisors E := ⟨fun {a b} hab => by
    by_contra hne
    push_neg at hne
    obtain ⟨u, hu⟩ := hE a hne.1
    apply hne.2
    have h2 := congrArg (fun t => (↑u⁻¹ : E) * t) hab
    simp only [mul_zero, ← mul_assoc] at h2
    rwa [← hu, Units.inv_mul, one_mul] at h2⟩
  haveI : IsDomain E := NoZeroDivisors.to_isDomain E
  obtain ⟨hfg, hspan, hdual⟩ := hΛ
  haveI : Module.Finite M.L.O Λ := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors M.L.O Λ := ⟨fun {r x} h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hr' : (r : E) ≠ 0 := fun h0 => hr (Subtype.ext h0)
    obtain ⟨u, hu⟩ := hE _ hr'
    have h1 : (r : E) • (x : V) = 0 := by
      have := congrArg Subtype.val h
      simpa [Submodule.coe_smul, Subring.smul_def] using this
    apply Subtype.ext
    have h2 := congrArg (fun v => (↑u⁻¹ : E) • v) h1
    simp only [smul_zero, smul_smul] at h2
    rw [← hu, Units.inv_mul, one_smul] at h2
    simpa using h2⟩
  haveI : Module.Free M.L.O Λ := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis M.L.O Λ
  let bb : Module.Free.ChooseBasisIndex M.L.O Λ → V := fun i => (B i : V)
  have hexp : ∀ (x : V) (hx : x ∈ Λ), x = ∑ i, ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i := by
    intro x hx
    have h2 := congrArg Subtype.val (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def] at h2
    exact h2.symm
  have hli : LinearIndependent E bb := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose s hsO hs using fun j => hden (g j)
    set t := ∏ j, s j with ht
    have htO : t ∈ M.L.O := Subring.prod_mem _ fun j _ => hsO j
    have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hs j).1
    have htg : ∀ j, t * g j ∈ M.L.O := by
      intro j
      have e : t * g j = (∏ j' ∈ Finset.univ.erase j, s j') * (s j * g j) := by
        rw [ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
        ring
      rw [e]
      exact M.L.O.mul_mem (Subring.prod_mem _ fun j' _ => hsO j') (hs j).2
    let g' : Module.Free.ChooseBasisIndex M.L.O Λ → M.L.O := fun j => ⟨t * g j, htg j⟩
    have hsum : ∑ j, g' j • B j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def, Submodule.coe_zero]
      have : ∑ j, (t * g j) • bb j = t • ∑ j, g j • bb j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
      simpa [g', bb, hg] using this
    have h0 := Fintype.linearIndependent_iff.mp B.linearIndependent g' hsum i
    have h0' : t * g i = 0 := congrArg Subtype.val h0
    exact (mul_eq_zero.mp h0').resolve_left ht0
  have hsp : ⊤ ≤ Submodule.span E (Set.range bb) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let BE := Basis.mk hli hsp
  have hcard : Module.finrank E V = Fintype.card (Module.Free.ChooseBasisIndex M.L.O Λ) :=
    Module.finrank_eq_card_basis BE
  let eι := Fintype.equivFinOfCardEq hcard.symm
  let b : Fin (Module.finrank E V) → V := fun k => bb (eι.symm k)
  have hbΛ : ∀ k, b k ∈ Λ := fun k => (B (eι.symm k)).2
  have hlib : LinearIndependent E b := hli.comp _ eι.symm.injective
  have hexpb : ∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧
      x = ∑ k, c k • b k := by
    intro x hx
    refine ⟨fun k => ((B.repr ⟨x, hx⟩ (eι.symm k) : M.L.O) : E), fun k => Subtype.property _, ?_⟩
    exact (hexp x hx).trans
      (Equiv.sum_comp eι.symm (fun i => ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i)).symm
  refine ⟨b, hbΛ, hlib, hexpb, ?_⟩
  set G : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E :=
    Matrix.of (fun k l => H.h (b k) (b l)) with hG
  have hdet0 : G.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    set x := ∑ k, v k • b k with hx
    have hxb : ∀ l, H.h x (b l) = 0 := by
      intro l
      rw [hx, flb_h_sum_left]
      have := congrFun hv l
      simpa [Matrix.vecMul, dotProduct, hG] using this
    have hx0 : x = 0 := by
      apply H.nondeg
      intro y
      have hy := BE.sum_repr y
      rw [← hy, flb_h_sum_right]
      apply Finset.sum_eq_zero
      intro i _
      have : BE i = b (eι i) := by simp [BE, b]
      rw [this, hxb, mul_zero]
    apply hv0
    funext k
    exact Fintype.linearIndependent_iff.mp hlib v hx0.symm.symm k
  have hdet : IsUnit G.det := hE _ hdet0
  refine ⟨G⁻¹, ?_, Matrix.nonsing_inv_mul G hdet⟩
  have hQG := Matrix.nonsing_inv_mul G hdet
  intro k m
  set d := ∑ m', G⁻¹ k m' • b m' with hd
  have hdb : ∀ l, H.h d (b l) = if k = l then 1 else 0 := by
    intro l
    rw [hd, flb_h_sum_left]
    have := congrFun (congrFun hQG k) l
    simpa [Matrix.mul_apply, hG, Matrix.one_apply] using this
  have hdΛ : d ∈ Λ := by
    rw [hdual]
    intro y hy
    obtain ⟨c, hcO, rfl⟩ := hexpb y hy
    rw [flb_h_sum_right]
    simp only [hdb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact flb_cj_mem M.L (hcO k)
  obtain ⟨c', hc'O, hc'⟩ := hexpb d hdΛ
  have hz : ∑ m', (G⁻¹ k m' - c' m') • b m' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hd, ← hc', sub_self]
  have := Fintype.linearIndependent_iff.mp hlib _ hz m
  rw [sub_eq_zero.mp this]
  exact hc'O m

theorem flatBasis_of (h1 : FLocO) : FLatBasis := by
  intro F E _ _ _ _ _ _ _ M hF hc hE V _ _ H Λ hΛ
  haveI := hF
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hden0, hfac⟩ := h1 F E M.L hF hc hE ϖ hϖ
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  refine flb_main M hE hnt ?_ (flb_pid M.L.O _ (flb_int_mem M.L ϖ) hfac) V H Λ hΛ
  intro x
  obtain ⟨c, hc0, hcx⟩ := hden0 x
  refine ⟨_, flb_int_mem M.L c, ?_, hcx⟩
  have hcF : (c : F) ≠ 0 := by exact_mod_cast hc0
  exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hcF

end PI.UnitaryGroupMassFormula.CntFormula
end
end

