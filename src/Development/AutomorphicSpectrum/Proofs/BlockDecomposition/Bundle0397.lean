module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0047
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0048
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0027
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0366
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotent
section
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

theorem e_upper_mul_pow_succ_eq {i j : Fin n} (hij : (j : ℕ) = i + 1) (m : ℕ) :
    e (i, j) * e (j, i) ^ (m + 1) =
      e (j, i) ^ (m + 1) * e (i, j) + ((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
        (((m : ℂ) + 1) * m) • e (j, i) ^ m := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hxy : e (i, j) * e (j, i) = e (j, i) * e (i, j) + (e (i, i) - e (j, j)) := by
    have := e_mul_sub_mul (i, j) (j, i)
    simp only [if_true] at this
    rw [← this]; abel
  have hh : ∀ p : ℕ, (e (i, i) - e (j, j)) * e (j, i) ^ p =
      e (j, i) ^ p * (e (i, i) - e (j, j)) - (2 * (p : ℂ)) • e (j, i) ^ p := by
    intro p
    rw [sub_mul, e_diag_mul_e_pow, e_diag_mul_e_pow, rootAt_lower_self hne, rootAt_lower_other hne,
      mul_sub]
    module
  induction m with
  | zero =>
    simp only [pow_zero, pow_one, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero, zero_smul,
      sub_zero]
    exact hxy
  | succ m ih =>
    have e1 : e (i, j) * e (j, i) ^ (m + 1 + 1) =
        e (j, i) * (e (i, j) * e (j, i) ^ (m + 1)) + (e (i, i) - e (j, j)) * e (j, i) ^ (m + 1) := by
      rw [pow_succ' _ (m + 1), ← mul_assoc, hxy, add_mul, mul_assoc]
    rw [e1, hh, ih]
    simp only [mul_sub, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ']
    push_cast
    module

theorem h_mul_sub_mem_Jp {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) {i j : Fin n}
    (hij : (j : ℕ) = i + 1) :
    (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x ∈ Jp n := by
  have hi := hx i
  have hj := hx j
  have hd := rhoVec_sub (n := n) hij
  have key : (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x =
      x * (e (i, i) - algebraMap ℂ (U n) (rhoVec n i)) -
        x * (e (j, j) - algebraMap ℂ (U n) (rhoVec n j)) := by
    have h1 : e (i, i) * x = x * e (i, i) + (μ i : ℂ) • x := by rw [← hi]; abel
    have h2 : e (j, j) * x = x * e (j, j) + (μ j : ℂ) • x := by rw [← hj]; abel
    have h3 : rhoVec n i = rhoVec n j + 1 := by rw [← hd]; ring
    rw [sub_mul, h1, h2]
    simp only [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, h3]
    module
  rw [key]
  exact vermaIdeal_le_Jp (Submodule.sub_mem _ (mul_e_sub_mem_vermaIdeal _ _ i)
    (mul_e_sub_mem_vermaIdeal _ _ j))

theorem natural_of_primitive {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n) (hx : IsAdW μ x)
    (hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hxJ : x ∉ Jp n)
    (hij : (j : ℕ) = i + 1) (hN : ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) :
    ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  classical
  have hp := Nat.find_spec hN
  have hmin := fun m => Nat.find_min hN (m := m)
  obtain ⟨q, hq⟩ : ∃ q, Nat.find hN = q + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => hxJ ?_
    rw [h0] at hp
    simpa using hp
  rw [hq] at hp
  have hqn : e (j, i) ^ q * x ∉ Jp n := hmin q (by omega)
  have hEx : e (i, j) * x ∈ Jp n := hup (i, j) (by
    simp only [IsUpper]; rw [Fin.lt_def, hij]; omega)
  set c : ℂ := (1 : ℂ) + (μ i : ℂ) - (μ j : ℂ) with hc
  have h1 := mul_mem_Jp (e (i, j)) hp
  have h2 := mul_mem_Jp (e (j, i) ^ (q + 1)) hEx
  have h3 := mul_mem_Jp (e (j, i) ^ q) (h_mul_sub_mem_Jp hx hij)
  have key : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) =
      e (i, j) * (e (j, i) ^ (q + 1) * x) - e (j, i) ^ (q + 1) * (e (i, j) * x) -
        ((q : ℂ) + 1) • (e (j, i) ^ q * ((e (i, i) - e (j, j)) * x - c • x)) := by
    rw [← mul_assoc (e (i, j)), e_upper_mul_pow_succ_eq hij q]
    simp only [mul_sub, sub_mul, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    module
  have hmem : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) ∈ Jp n := by
    rw [key]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ h3)
  have hzero : ((q : ℂ) + 1) * (c - q) = 0 := by
    by_contra hne
    exact hqn ((Submodule.smul_mem_iff _ hne).1 hmem)
  have hq1 : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hcq : c = q := sub_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left hq1)
  refine ⟨q, ?_⟩
  have : ((1 + μ i - μ j : ℤ) : ℂ) = ((q : ℤ) : ℂ) := by
    push_cast
    exact hcq
  exact_mod_cast this

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermEqOneOfMonomialMem
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.CompanionTheory.LbElem.ConjMonomial

namespace GlobalTheory.CompanionTheory.LbElem.MonomialInJ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem diag_ne_zero_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  intro h0
  have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [Finset.sum_eq_zero] at h1
  · exact zero_ne_one h1
  · intro l _
    by_cases hl : i = l
    · subst hl
      rw [h0, zero_mul]
    · rw [h i l hl, zero_mul]

private def o {N : ℕ} (a : Fin N) : Fin (ones N a) := ⟨0, by simp [ones]⟩

theorem nup_entries {N : ℕ} {c : GL (Fin N) k} (hc : c ∈ unipRad k (stdBlocks (ones N) (sum_ones N))) :
    (∀ i j : Fin N, j < i → (c : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i : Fin N, (c : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hc
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := mem_parab_iff.1 h1 i j (o i) (o j) hij
    rwa [stdBlocks_ones, stdBlocks_ones] at this
  · have := h2 i (o i) (o i)
    rwa [stdBlocks_ones, Matrix.one_apply_eq] at this

theorem nlo_entries {N : ℕ} {a : GL (Fin N) k}
    (ha : a ∈ unipRadLower k (stdBlocks (ones N) (sum_ones N))) :
    (∀ i j : Fin N, i < j → (a : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i : Fin N, (a : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipRadLower k).1 ha
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := (mem_parabLower_iff k).1 h1 i j (o i) (o j) hij
    rwa [stdBlocks_ones, stdBlocks_ones] at this
  · have := h2 i (o i) (o i)
    rwa [stdBlocks_ones, Matrix.one_apply_eq] at this

end GlobalTheory.CompanionTheory.LbElem.MonomialInJ

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PosNorm
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.PosNormFD

theorem posNorm : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.PosNorm := by
  intro E _ _ _ N _ _ μ _ 𝓕 h𝓕 φ hA hS hne
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  have hc : Continuous φ.1 := GlobalTheory.CuspRep.IsAutForm.continuous hA
  have hl := GlobalTheory.DiscreteUnit.left_latticeGL hA hS
  by_contra h0
  have h0' : ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ = 0 := by simpa using h0
  have hm : Measurable fun g => ‖φ.1 g‖ₑ ^ 2 := hc.enorm.measurable.pow_const 2
  have hz := (lintegral_eq_zero_iff hm).1 h0'
  have hSo : IsOpen {g | φ.1 g ≠ 0} := isOpen_ne_fun hc continuous_const
  have hSF : μ ({g | φ.1 g ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply hSo.measurableSet]
    refine measure_mono_null (fun g hg => ?_) (ae_iff.1 hz)
    have hg' : φ.1 g ≠ 0 := hg
    simpa [hg'] using hg'
  have hinv : ∀ γ : latticeGL E N, γ • {g | φ.1 g ≠ 0} = {g | φ.1 g ≠ 0} := fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have e : φ.1 (γ⁻¹ • x) = φ.1 x := hl _ (γ⁻¹).2 x
    simp only [Set.mem_setOf_eq, e]
  set_option synthInstance.maxHeartbeats 200000 in
    have hS0 := h𝓕.measure_zero_of_invariant _ hinv hSF
  have hemp := (hSo.measure_eq_zero_iff μ).1 hS0
  refine hne (Subtype.ext (funext fun g => ?_))
  by_contra hg
  exact (Set.eq_empty_iff_forall_notMem.1 hemp g) hg

end GlobalTheory.CompanionTheory.PosNormFD
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowUnifLeOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial (stdBlocks_ones)

namespace GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_block {N : ℕ} {a : Fin N} (i j : Fin (ones N a)) :
    (1 : Matrix (Fin (ones N a)) (Fin (ones N a)) k) i j = 1 := by
  have : i = j := by
    apply Fin.ext
    have h1 := i.2
    have h2 := j.2
    simp only [ones] at h1 h2
    omega
  subst this
  exact Matrix.one_apply_eq i

theorem mem_Nup_of {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ Nup k N := by
  refine mem_unipRad.2 ⟨mem_parab_iff.2 ?_, ?_⟩
  · intro a b i j hab
    rw [stdBlocks_ones, stdBlocks_ones]
    exact h0 a b hab
  · intro a i j
    rw [stdBlocks_ones, stdBlocks_ones, h1, one_block]

theorem mem_Nlo_of {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, i < j → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ Nlo k N := by
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 ?_, ?_⟩
  · intro a b i j hab
    rw [stdBlocks_ones, stdBlocks_ones]
    exact h0 a b hab
  · intro a i j
    rw [stdBlocks_ones, stdBlocks_ones, h1, one_block]

end GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquiv
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdSingle

theorem prodIrr_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL (k := k)) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL (k := k)) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  intro k _ _ _ _ h N Y hd i₀ h0
  have hN : (Y i₀).1 = N := by
    rw [← hd]
    exact (Finset.sum_eq_single i₀ (fun i _ hi => h0 i hi) (fun hi => absurd (Finset.mem_univ _) hi)).symm
  subst hN
  refine ⟨(Y i₀).2, Sigma.eta _, ?_⟩
  have hd' : ∑ a : Fin 1, (Y ((fun _ : Fin 1 => i₀) a)).1 = (Y i₀).1 := by simp
  obtain ⟨e₁⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y hd (fun _ : Fin 1 => i₀) (Subsingleton.strictMono _)
    (fun j hj => ⟨0, by
      by_contra hne
      exact hj (h0 j (fun e => hne e.symm))⟩) hd'
  obtain ⟨e₂⟩ := nonempty_equiv_prodIrr_one (Y i₀) hd'
  exact ⟨e₁.trans e₂.symm⟩

end GlobalTheory.CompanionTheory.FineProd.ProdSingle
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarOnWeightSpace
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.Asm

open Formalism.REAL (GlRel qdet)
open GlobalTheory.CompanionTheory.PairMult
open GlobalTheory.CompanionTheory.RgCOBlock (sz shift fb)
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

theorem mem_down {S : Finset (Fin n)} (hS : ∀ a b, b ≤ a → a ∈ S → b ∈ S) (a : Fin n) :
    a ∈ S ↔ (a : ℕ) < S.card :=
  _root_.UpperTheory.Reformulated.B.DYlb8.main hS a

theorem twice_sum_Ico (m d : ℕ) :
    2 * ∑ k ∈ Finset.Ico m (m + d), (k : ℝ) = 2 * (d : ℝ) * m + d * ((d : ℝ) - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), mul_add, ih]
    push_cast
    ring

theorem level_sum (lev : Fin n → ℕ) (hm : Monotone lev) (c : ℕ) :
    2 * ∑ a ∈ univ.filter (fun a => lev a = c), ((a : ℕ) : ℝ) =
      2 * ((univ.filter fun a => lev a = c).card : ℝ) * ((univ.filter fun a => lev a < c).card : ℝ) +
        ((univ.filter fun a => lev a = c).card : ℝ) * (((univ.filter fun a => lev a = c).card : ℝ) - 1) := by
  set d := (univ.filter fun a => lev a = c).card with hd
  set m := (univ.filter fun a => lev a < c).card with hmm
  have hlow : ∀ a, lev a < c ↔ (a : ℕ) < m := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    simpa using this
  have hcard : (univ.filter fun a => lev a < c + 1).card = m + d := by
    rw [hmm, hd, ← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    · rw [Finset.disjoint_left]
      intro a h1 h2
      have := (mem_filter.1 h1).2
      have := (mem_filter.1 h2).2
      omega
  have hup : ∀ a, lev a < c + 1 ↔ (a : ℕ) < m + d := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c + 1) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    rw [hcard] at this
    simpa using this
  have hle : m + d ≤ n := by
    rw [← hcard]
    exact (card_le_univ _).trans_eq (Fintype.card_fin n)
  have hmap : (univ.filter fun a => lev a = c).map Fin.valEmbedding = Finset.Ico m (m + d) := by
    ext k
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 := hlow a
      have h2 := hup a
      omega
    · rintro ⟨k1, k2⟩
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩
      have h1 := hlow ⟨k, by omega⟩
      have h2 := hup ⟨k, by omega⟩
      simp only at h1 h2
      omega
  rw [← twice_sum_Ico, ← hmap, Finset.sum_map]
  rfl

section Alg

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end Alg

section Spaces

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end Spaces

end GlobalTheory.CompanionTheory.PairMult.Asm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMirabolicKernelEqZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

theorem eq_zero_of_forall_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), IsSmooth τ → ∀ v : V, v ∈ twKer τ (MirUin k (m + 1)) 1 → (∀ g : GL (Fin (m + 1)) k, τ (levi k (m + 1) g) v ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) → v = 0 := by
  intro k _ _ _ _ ψ hψ hψ1 m V _ _ τ hτ v h0 hg
  have hρ : IsSmooth (τ.comp (unipMir k (m + 1))) := _root_.GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir k (m + 1) V τ hτ
  have hall : ∀ a : Fin (m + 1) → k,
      v ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ a ⊤) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      exact mem_chi_zero ψ τ h0
    · obtain ⟨g, hgr⟩ := GlobalTheory.T.exists_invertible_matrix_last_line_given k m a ha
      have e : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) = a := funext hgr
      have := mem_chi_row ψ τ g (hg g)
      rw [e, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply] at this
      exact this
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed k (m + 1) V _ hρ v
  obtain ⟨J, hJ⟩ := GlobalTheory.T.uniform_twisted_invariance_on_ball k ψ hψ (m + 1) V _ v (addCharConductor ψ - N)
    (fun a => GlobalTheory.T.twisted_invariant_small_boxes k (m + 1) V _ (chi k ψ a) v (hall a))
  exact _root_.GlobalTheory.CompanionTheory.MirFourier.FiniteInversion.fourier_finite k ψ hψ hψ1 (m + 1) V _ hρ v N (min J N) (min_le_right _ _) hN
    (fun a ha => hJ (min J N) (min_le_left _ _) a ha)

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqIntAt
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.SqIntFD

theorem sqIntAt : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.SqIntAt := by
  intro E _ _ _ N mG bG μ _ 𝓕 h𝓕 φ h h'
  obtain rfl : mG = borel _ := bG.measurable_eq
  have hm := GlobalTheory.CuspRep.CuspidalL2GL.memL2_of_isAutForm (μ := μ) h h'
  have hc := ((memL2_iff_fundamental_domain h𝓕).1 hm).2
  simpa using lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
    two_ne_zero ENNReal.ofNat_ne_top hc.eLpNorm_lt_top

end GlobalTheory.CompanionTheory.SqIntFD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCycWordEqEtr
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CycWordTrace

theorem sum_cycWord_eq_etr : ∀ (B : Type) [Ring B] (n m : ℕ) (X : Fin n → Fin n → B),
    ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => X p.1 p.2).prod
      = Formalism.REAL.etr X (m + 1) := by
  intro B _ n m X
  exact (GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord X m).symm

end GlobalTheory.CompanionTheory.CycWordTrace
end

