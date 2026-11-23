module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGDefs
section
noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TrDual : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D), ∀ c ∈ 𝒪[(D.s.atP p).Fp],
      haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
      ‖Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (c * (δ p)⁻¹)‖ ≤ 1

def DualApprox : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) [Fact (Loc.resChar p).Prime]
    (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp]
    [Algebra ℚ_[Loc.resChar p] Fp], Continuous (algebraMap ℚ_[Loc.resChar p] Fp) →
    FiniteDimensional ℚ_[Loc.resChar p] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
    (∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) →
    ∀ z : Fp, (∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[Loc.resChar p] Fp (c * z)‖ ≤ 1) →
    ∀ k : ℕ, ∃ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) ∧
      ∃ μ ∈ 𝒪[Fp], ι t = z + ((Loc.resChar p : ℕ) : Fp) ^ k * μ

def LocDiff : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D), ∃ t : D.host.F,
      (∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) ∧
      δ p * (D.s.atP p).ιF t ≠ 0 ∧ δ p * (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p * (D.s.atP p).ιF t)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

def PowSmall : Prop :=
  ∀ (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] (x y : Fp),
    valuation Fp y < 1 → ∃ k : ℕ, valuation Fp (y ^ k * x) < 1

def DualPow : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (t : D.host.F), (∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) →
    ∀ m : ℕ, ((t : D.host.E) ^ m) ∈
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

end PI.CntNotIntW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NotIntAllOfLoc
section
noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def NormAt {L : Loc.LocE F E} (g : Loc.SplitG L) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) : Prop :=
  (∃ s : 𝒪[F], (g.e (Zh a b)).1 + (if a = Fin.last r ∧ b = Fin.last r then T else 0) = (g.q : F) * s) ∧
  (∃ s : 𝒪[F], (g.e (Zh a b)).2 + (if a = Fin.last r ∧ b = Fin.last r then T else 0) = (g.q : F) * s) ∧
  (∃ s : 𝒪[F], (g.e (Zh a b)).1 + (g.e (Zh b a)).2 + (if a = Fin.last r ∧ b = Fin.last r then T + T' else 0) =
    (g.q : F) ^ 2 * s)

theorem mem_R_split (M : Loc.Model F E) (g : Loc.SplitG M.L) (hs : M.split = some g) (x : E) (s1 s2 : 𝒪[F])
    (he : g.e x = ((s1 : F), (s2 : F))) (hc : s1 - s2 ∈ Ideal.span {g.q}) : x ∈ M.R := by
  unfold Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  refine ⟨(s1, s2), ?_, ?_⟩
  · rw [RingHom.mem_eqLocus]
    simp only [RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd]
    exact Ideal.Quotient.eq.2 hc
  · simp [he]

theorem zzplus_mem (M : Loc.Model F E) (g : Loc.SplitG M.L) (hs : M.split = some g) {r : ℕ}
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (hTT : ∃ k : 𝒪[F], T - T' = (g.q : F) * k)
    (h : ∀ a b, NormAt g Zh T T' a b) (a b : Fin (r + 1)) : Loc.HermSp.ZZplusOf M Zh T T' a b ∈ M.R := by
  have hq : (g.q : F) ≠ 0 := by
    intro h0
    have : g.q = 0 := Subtype.ext h0
    exact g.q_irr.ne_zero this
  obtain ⟨k, hk⟩ := hTT
  obtain ⟨⟨s1, hs1⟩, -, ⟨s3, hs3⟩⟩ := h a b
  obtain ⟨-, ⟨s2, hs2⟩, -⟩ := h b a
  set c : Prop := a = Fin.last r ∧ b = Fin.last r with hc_def
  have hcs : (b = Fin.last r ∧ a = Fin.last r) ↔ c := and_comm
  unfold Loc.HermSp.ZZplusOf
  rw [hs]
  simp only [Matrix.of_apply]
  by_cases hcc : c
  · have hcc' : b = Fin.last r ∧ a = Fin.last r := hcs.2 hcc
    rw [if_pos hcc]
    rw [if_pos hcc] at hs1 hs3
    rw [if_pos hcc'] at hs2
    refine mem_R_split M g hs _ s1 (k - s2) ?_ ?_
    · rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      ext
      · simp only [Prod.fst_sub]
        field_simp
        linear_combination hs1
      · simp only [Prod.snd_sub]
        push_cast
        field_simp
        linear_combination -hs2 + hk
    · rw [Ideal.mem_span_singleton']
      refine ⟨s3, ?_⟩
      apply Subtype.ext
      push_cast
      apply mul_left_cancel₀ hq
      linear_combination hs1 + hs2 - hs3 - hk
  · rw [if_neg hcc, sub_zero]
    have hcc' : ¬ (b = Fin.last r ∧ a = Fin.last r) := fun h' => hcc (hcs.1 h')
    rw [if_neg hcc, add_zero] at hs1
    rw [if_neg hcc, add_zero] at hs3
    rw [if_neg hcc', add_zero] at hs2
    refine mem_R_split M g hs _ s1 (-s2) ?_ ?_
    · rw [AlgEquiv.apply_symm_apply]
      ext
      · simp only
        field_simp
        linear_combination hs1
      · simp only
        push_cast
        field_simp
        linear_combination -hs2
    · rw [Ideal.mem_span_singleton']
      refine ⟨s3, ?_⟩
      apply Subtype.ext
      push_cast
      apply mul_left_cancel₀ hq
      linear_combination hs1 + hs2 - hs3

end Generic

theorem tt_mod_q (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word)
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (p : PlF D) (g : Loc.SplitG (M p).L)
    (hs : (M p).split = some g) :
    ∃ k : 𝒪[(D.s.atP p).Fp], (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) - (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) =
      (g.q : (D.s.atP p).Fp) * k := by
  have hm := (hA p).2.2.2.2.2
  rw [hs] at hm
  rcases hsp : (D.s.atP p).split with _ | sg
  · rw [hsp] at hm
    exact hm.elim
  · rw [hsp] at hm
    have hqq : g.q = sg.q := hm.2
    have hell : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (D.s_split p).1 (by rw [hsp]; rfl)
    have hdvd : Loc.resChar p ∣ Lat.gS D ^ 2 := by
      apply Dvd.dvd.pow _ two_ne_zero
      unfold Lat.gS
      rcases Finset.mem_insert.1 hell with h0 | h1
      · rw [h0]; exact dvd_mul_right _ _
      · rw [Finset.mem_singleton.1 h1]; exact dvd_mul_left _ _
    have hmod : (D.mem u).A.T ≡ (D.mem u').A.T [MOD Loc.resChar p] := Nat.ModEq.of_dvd hdvd hT
    have hz : ((Loc.resChar p : ℕ) : ℤ) ∣ ((D.mem u').A.T : ℤ) - ((D.mem u).A.T : ℤ) :=
      (Nat.modEq_iff_dvd).1 hmod
    obtain ⟨k, hk⟩ := hz
    refine ⟨⟨((-k : ℤ) : (D.s.atP p).Fp), intCast_mem _ (-k)⟩, ?_⟩
    rw [hqq, sg.q_eq]
    have hk' : (((D.mem u').A.T : ℤ) : (D.s.atP p).Fp) - (((D.mem u).A.T : ℤ) : (D.s.atP p).Fp) =
        (((Loc.resChar p : ℕ) : ℤ) : (D.s.atP p).Fp) * ((k : ℤ) : (D.s.atP p).Fp) := by
      rw [← Int.cast_sub, hk, Int.cast_mul]
    simp only [Int.cast_natCast] at hk'
    push_cast
    linear_combination -hk'

end PI.CntNotIntW
end
end

