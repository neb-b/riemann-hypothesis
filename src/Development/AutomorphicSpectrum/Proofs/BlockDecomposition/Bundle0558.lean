module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinety
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0532
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjection
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp

def IsI {K : Type} [Field K] [NumberField K] (x : K) : Prop :=
  ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x

section I

variable {K : Type} [Field K] [NumberField K]

theorem IsI.add {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x + y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o + p, by simp⟩

theorem IsI.neg {x : K} (hx : IsI x) : IsI (-x) := by
  obtain ⟨o, rfl⟩ := hx
  exact ⟨-o, by simp⟩

theorem IsI.mul {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x * y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o * p, by simp⟩

theorem isI_zero : IsI (0 : K) := ⟨0, by simp⟩

theorem isI_sum {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, IsI (f i)) :
    IsI (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isI_zero : IsI (0 : K))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Kc_le_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc c ≤ Kc (c + h) := by
  intro y hy i
  have h1 : IsI ((c *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := hy i
  have h2 : IsI ((h *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := by
    show IsI (∑ j, h i j * algebraMap (𝓞 K) K (y j))
    exact isI_sum (K := K) Finset.univ _ fun j _ => (hh i j).mul ⟨y j, rfl⟩
  have h3 := h1.add h2
  rw [Matrix.add_mulVec]
  exact h3

theorem Kc_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc (c + h) = Kc c := by
  refine le_antisymm ?_ (Kc_le_add c h hh)
  have := Kc_le_add (c + h) (-h) fun a b => by simpa using IsI.neg (hh a b)
  simpa using this

theorem delta_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    delta (c + h) = delta c := by
  unfold delta
  rw [Kc_add c h hh]

theorem vec_out {m : ℕ} (t : Fin m → K) (i : Fin m) :
    IsI ((Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) : Fin m → K) i - t i) := by
  have h : Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m))
      = (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) := Quotient.out_eq _
  have h2 := (Submodule.Quotient.eq _).1 h
  exact h2 i

end I

section H

variable {F E : Type} [Field F] [Field E] [Algebra F E] [NumberField E]

theorem herm_out (σ : E →ₐ[F] E) {n : ℕ} (t : hermE σ n) (a b : Fin n) :
    IsI ((Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b) := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) :
      hermE σ n ⧸ hermO σ n) = QuotientAddGroup.mk t := Quotient.out_eq _
  have h2 : IsI ((-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b) :=
    (QuotientAddGroup.eq.1 h) a b
  have h3 := h2.neg
  have e : -(-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b =
      (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b := by
    simp
    ring
  rwa [e] at h3

def topB (σ : E →ₐ[F] E) {m : ℕ} (C : hermE σ (m + 1)) : hermE σ m :=
  ⟨fun a b => C.1 a.castSucc b.castSucc, fun a b => C.2 a.castSucc b.castSucc⟩

def lastCol {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : Fin m → E :=
  fun a => C a.castSucc (Fin.last m)

theorem blk_cc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a b : Fin m) : blk σ c u d a.castSucc b.castSucc = c a b := by simp [blk]

theorem blk_cl (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a : Fin m) : blk σ c u d a.castSucc (Fin.last m) = u a := by simp [blk]

theorem blk_lc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (b : Fin m) : blk σ c u d (Fin.last m) b.castSucc = σ (u b) := by simp [blk]

theorem blk_ll (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    blk σ c u d (Fin.last m) (Fin.last m) = d := by simp [blk]

theorem blk_sub_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (C : hermE σ (m + 1)) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (hc : ∀ a b : Fin m, IsI (c a b - C.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (u a - C.1 a.castSucc (Fin.last m)))
    (hd : IsI (d - C.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) :
    IsI (blk σ c u d i j - C.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_ll]; exact hd
    | cast b =>
      rw [blk_lc, ← C.2 (Fin.last m) b.castSucc, ← map_sub]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [blk_cl]; exact hu a
    | cast b => rw [blk_cc]; exact hc a b

theorem herm_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (D : hermE σ (m + 1))
    (hc : ∀ a b : Fin m, IsI (D.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (D.1 a.castSucc (Fin.last m)))
    (hd : IsI (D.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) : IsI (D.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact hd
    | cast b =>
      rw [← D.2 (Fin.last m) b.castSucc]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => exact hu a
    | cast b => exact hc a b

end H

theorem isI_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {y : F} (hy : IsI y) : IsI (algebraMap F E y) := by
  obtain ⟨o, rfl⟩ := hy
  have h : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F o)) :=
    (RingOfIntegers.isIntegral_coe o).algebraMap
  exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ h⟩

theorem hermClass_blocks : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ m : ℕ, ∃ ι : (hermE σ (m + 1) ⧸ hermO σ (m + 1)) → (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F, Function.Injective ι ∧ ∀ x, delta (Quotient.out x).1 = delta (blk σ (Quotient.out (ι x).1).1 (Quotient.out (ι x).2.1) (algebraMap F E ((Quotient.out (ι x).2.2 : Fin 1 → F) 0))) := by
  intro F E _ _ _ _ _ σ hcm m
  obtain ⟨-, hfix, hsO, -⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers F E σ hcm
  have hσ : ∀ x : E, IsI x → IsI (σ x) := by
    rintro x ⟨o, rfl⟩
    exact ⟨sO σ o, hsO o⟩
  have hcorner : ∀ C : hermE σ (m + 1), ∃ y : F,
      algebraMap F E y = C.1 (Fin.last m) (Fin.last m) := fun C => hfix _ (C.2 _ _)
  choose dd hdd using hcorner
  refine ⟨fun x => (QuotientAddGroup.mk (topB σ (Quotient.out x)),
    Submodule.Quotient.mk (lastCol (Quotient.out x).1),
    Submodule.Quotient.mk (fun _ => dd (Quotient.out x))), ?_, ?_⟩
  · intro x x' hxx
    obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := by simpa [Prod.ext_iff] using hxx
    have h1' := QuotientAddGroup.eq.1 h1
    have h2' := (Submodule.Quotient.eq _).1 h2
    have h3' := (Submodule.Quotient.eq _).1 h3
    rw [← Quotient.out_eq x, ← Quotient.out_eq x']
    refine QuotientAddGroup.eq.2 ?_
    refine fun i j => herm_isI σ hσ (-(Quotient.out x) + Quotient.out x') ?_ ?_ ?_ i j
    · intro a b
      exact h1' a b
    · intro a
      have : IsI (lastCol (Quotient.out x).1 a - lastCol (Quotient.out x').1 a) := h2' a
      have e := this.neg
      simpa [lastCol, add_comm, sub_eq_add_neg] using e
    · have : IsI (dd (Quotient.out x) - dd (Quotient.out x')) := h3' 0
      have e := (isI_algebraMap (E := E) this).neg
      simpa [hdd, add_comm, sub_eq_add_neg] using e
  · intro x
    dsimp only
    set C := Quotient.out x with hC
    set M := blk σ (Quotient.out (QuotientAddGroup.mk (topB σ C) : hermE σ m ⧸ hermO σ m)).1
      (Quotient.out (Submodule.Quotient.mk (lastCol C.1) : (Fin m → E) ⧸ intVec E m))
      (algebraMap F E ((Quotient.out (Submodule.Quotient.mk (fun _ => dd C) : FQ F) : Fin 1 → F) 0))
      with hM
    have hI : ∀ i j, IsI ((M - C.1) i j) := by
      intro i j
      refine blk_sub_isI σ hσ C _ _ _ ?_ ?_ ?_ i j
      · intro a b
        exact herm_out σ (topB σ C) a b
      · intro a
        exact vec_out (lastCol C.1) a
      · have h := isI_algebraMap (E := E) (vec_out (fun _ : Fin 1 => dd C) 0)
        rw [map_sub, hdd] at h
        exact h
    have := delta_add C.1 (M - C.1) hI
    rw [add_sub_cancel] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnitaryContraction

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_zpow (x : Lˣ) (k : ℤ) : ordL ((x ^ k : Lˣ) : L) = k * ordL (x : L) := by
  have h0 : Valued.v (x : L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hk : Valued.v ((x ^ k : Lˣ) : L) = ((a ^ k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, WithZero.coe_zpow]
  rw [UnitaryCorrection.ordL_of_eq hk, UnitaryCorrection.ordL_of_eq ha.symm, toAdd_zpow]
  simp

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem diagT_mem_iwGL (w : Pl E) (n : ℕ) (s : Fin n → (w.adicCompletion E)ˣ)
    (hs : ∀ i, Valued.v (s i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w := by
  have hle : ∀ t : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (t i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) t).val i j) ≤ 1 := by
    intro t ht i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, ht]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le_one
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1]
  refine ⟨hle s hs, ?_, ?_⟩
  · rw [← map_inv]
    refine hle _ fun i => ?_
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, fU n w b ϖ l γ ≠ 0 → ∃ m ∈ iwU n w b, ∃ u : Fin n → (w.adicCompletion E)ˣ, (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (m⁻¹ * γ * m).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ hγ
  obtain ⟨-, hcc, hcv, -⟩ := _root_.GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨hW1, hW2, -, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  obtain ⟨hanti, hrev⟩ := GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl
  have hγ' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b,
      γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra h
    exact hγ (if_neg h)
  obtain ⟨x, hx, z, hz, e⟩ := hγ'
  obtain ⟨δ, hδ⟩ : ∃ δ : GLw n w, δ = b⁻¹ * γ.1 * b := ⟨_, rfl⟩
  have hγδ : γ.1 = b * δ * b⁻¹ := by rw [hδ]; group
  have hδd : dcos n w (tdiag ϖ (wexp n l)) δ ≠ 0 := by
    have h : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ (wexp n l) * z :=
      ⟨_, (hW2 x).1 hx, _, (hW2 z).1 hz, by rw [hδ, e]; group⟩
    simp only [dcos, if_pos h]
    exact one_ne_zero
  have hδU : δ ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) :=
    (hW1 δ).1 (by rw [← hγδ]; exact γ.2)
  obtain ⟨m0, hm0, τ, ⟨hτ0, hτ1⟩, hmτ⟩ := hyp (wexp n l) hanti δ hδd
  have hne : ∀ i, τ.val i i ≠ 0 := fun i h => by
    have := hτ1 i
    rw [h, map_zero] at this
    exact zero_ne_one this
  obtain ⟨v, hv⟩ : ∃ v : Fin n → (w.adicCompletion E)ˣ, ∀ i, (v i : w.adicCompletion E) = τ.val i i :=
    ⟨fun i => Units.mk0 _ (hne i), fun i => rfl⟩
  have hτv : τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
    apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hv]
    · rw [Matrix.diagonal_apply_ne _ h, hτ0 i j h]
  obtain ⟨u, hu⟩ : ∃ u : Fin n → (w.adicCompletion E)ˣ, u = fun i => ϖ ^ wexp n l i * v i := ⟨_, rfl⟩
  have htu : tdiag ϖ (wexp n l) * τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [hτv, hu, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (u i : w.adicCompletion E) = wexp n l i := by
    intro i
    rw [hu]
    simp only [Units.val_mul]
    rw [UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _), ordL_zpow, hϖ.1,
      UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, hτ1, map_one]),
      UnitaryCorrection.ordL_one]
    simp
  have hm0e := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n m0).1.1 hm0
  have hδe : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * m0⁻¹ = δ := by
    rw [← htu, ← hmτ]
    group
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.CompanionTheory.UnitaryCorrection.main (w.adicCompletion E) (cj w) hcc hcv
    (_root_.GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq E hU w hw) n (wexp n l) hanti.injective hrev u hord m0 hm0e.1 hm0e.2.1
    (by rw [hδe]; exact hδU)
  have hm1 : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w :=
    mul_mem hm0 (diagT_mem_iwGL w n s hs1)
  have hcomm : (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ *
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp [mul_comm]
  refine ⟨⟨b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹, (hW1 _).2 hs2⟩,
    (hW2 _).2 ?_, u, hord, ?_⟩
  · have : b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b =
        m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by group
    change b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b ∈ iwGL n w
    rw [this]
    exact hm1
  · change (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹)⁻¹ * γ.1 *
      (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) = _
    rw [hγδ]
    have hd : m0⁻¹ * δ * m0 = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by rw [hmτ, htu]
    calc _ = b * ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ * (m0⁻¹ * δ * m0) *
          GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹ := by group
      _ = _ := by rw [hd, hcomm]

end GlobalTheory.CompanionTheory.UnitaryContraction
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnEvPtP
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem differentiableOn_eval₂_ratio (N : ℕ) (c : Fin (N + 1))
    (p : MvPolynomial {j : Fin (N + 1) // j ≠ c} ℤ) :
    DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ =>
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c) p)
      {w | w c ≠ 0} := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact differentiableOn_const _
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at hp ⊢
    have hj : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => w j.1) {w | w c ≠ 0} :=
      (differentiable_apply j.1).differentiableOn
    have hc : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => w c) {w | w c ≠ 0} :=
      (differentiable_apply c).differentiableOn
    have hinv : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => (w c)⁻¹) {w | w c ≠ 0} :=
      fun w hw => (hc w hw).inv hw
    simp only [div_eq_mul_inv]
    exact hp.mul (hj.mul hinv)

theorem differentiableOn_ev_ptP (N : ℕ) (c : Fin (N + 1)) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    DifferentiableOn ℂ (fun w => CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w))
      {w | w c ≠ 0} := by
  have h : (fun w => CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w)) =
      fun w : Fin (N + 1) → ℂ => MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun j : {j // j ≠ c} => w j.1 / w c) ((chartAlgEquiv ℤ N c).symm a) := by
    funext w
    exact CxPts.ev_ofHom _ _ _ a
  rw [h]
  exact differentiableOn_eval₂_ratio N c _

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProduct
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

theorem contra_contra_of_equiv {G V W U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} {υ : Representation ℂ G U}
    (E₁ : (contra σ).Equiv τ) (E₂ : (contra τ).Equiv υ) (E₃ : υ.Equiv σ) :
    Nonempty ((contra (contra σ)).Equiv σ) :=
  ⟨((GlobalTheory.ContraRefl.contraEquiv E₁).symm.trans E₂).trans E₃⟩

theorem prodIrr_equiv_of_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : y = x)
    (hy : ∑ a, (y a).1 = N) (hx : ∑ a, (x a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr x hx)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem contra_contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  intro k _ _ _ _ hA h N x hd
  refine Exists.elim (contra_prodIrr hA x hd) fun hd₁ H₁ => H₁.elim fun E₁ => ?_
  refine Exists.elim (contra_prodIrr hA (fun a => Zc.dualCl (x a)) hd₁) fun hd₂ H₂ => H₂.elim fun E₂ => ?_
  refine (prodIrr_equiv_of_eq (funext fun a => GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA (x a)) hd₂ hd).elim fun E₃ => ?_
  exact contra_contra_of_equiv E₁ E₂ E₃

end GlobalTheory.CompanionTheory.ContraProd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_vertical_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧ ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  first | exact @GlobalTheory.CompanionTheory.EisHalf.eis_half_plane | exact GlobalTheory.CompanionTheory.EisHalf.eis_half_plane | (intros; apply GlobalTheory.CompanionTheory.EisHalf.eis_half_plane <;> assumption)
end

