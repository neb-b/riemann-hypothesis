module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialOfConjTorus
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.ConjMonomial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  apply Fin.ext
  rw [stdBlocks_val]
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [ones] at this
    omega
  simp [ones, hi]

theorem tor_offDiag {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨s, rfl⟩ := hx
  have h : (leviEmb k (stdBlocks (ones N) (sum_ones N)) s : Matrix (Fin N) (Fin N) k)
      (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
      (stdBlocks (ones N) (sum_ones N) ⟨j, ⟨0, by simp [ones]⟩⟩) = 0 := by
    classical
    simp [leviEmb, Matrix.blockDiagonal'_apply, hij]
  rwa [stdBlocks_ones, stdBlocks_ones] at h

theorem mem_tor_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  have hd : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    intro i h0
    have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro l _
      by_cases hl : i = l
      · subst hl
        rw [h0, zero_mul]
      · rw [h i l hl, zero_mul]
  refine ⟨fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
    (Units.mk0 _ (hd a)), ?_⟩

  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    have h1 : (leviEmb k (stdBlocks (ones N) (sum_ones N))
        (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
          (Units.mk0 _ (hd a))) : Matrix (Fin N) (Fin N) k)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩) = (x : Matrix (Fin N) (Fin N) k) i i := by
      simp [leviEmb, Matrix.blockDiagonal'_apply_eq, Matrix.algebraMap_matrix_apply]
    rw [stdBlocks_ones] at h1
    rw [h1]
  · have h1 : (leviEmb k (stdBlocks (ones N) (sum_ones N))
        (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
          (Units.mk0 _ (hd a))) : Matrix (Fin N) (Fin N) k)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
        (stdBlocks (ones N) (sum_ones N) ⟨j, ⟨0, by simp [ones]⟩⟩) = 0 := by
      classical
      simp [leviEmb, Matrix.blockDiagonal'_apply, hij]
    rw [stdBlocks_ones, stdBlocks_ones] at h1
    rw [h i j hij]
    exact h1

end GlobalTheory.CompanionTheory.LbElem.ConjMonomial

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulInvMemQOfRowQEq
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZPhiPhi

section Alg

variable {k : Type} [Field k]

theorem mul_inv_mem_Q_of_rowQ_eq (n : ℕ) (a b : Mir k (n + 1)) (h : rowQ k n a = rowQ k n b) :
    a * b⁻¹ ∈ Q k n := by
  show GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹) ∈ GlobalTheory.BZMir.Mir k n
  have hab : Matrix.vecMul (GlobalTheory.BZMir.eLast k n)
      (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) a) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      Matrix.vecMul (GlobalTheory.BZMir.eLast k n)
      (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) b) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    rw [GlobalTheory.BZMir.vecMul_eLast, GlobalTheory.BZMir.vecMul_eLast]
    funext j
    exact congrFun h j
  rw [GlobalTheory.BZMir.mem_Mir_iff, ← GlobalTheory.BZMir.vecMul_eLast k n
    (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
    map_mul, map_inv, Units.val_mul, ← Matrix.vecMul_vecMul, hab, Matrix.vecMul_vecMul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

def rowMat (n : ℕ) (r : Fin (n + 1) → k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k :=
  (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k).updateRow (Fin.castSucc (Fin.last n))
    (Fin.lastCases (motive := fun _ => k) 0 r)

theorem rowMat_single (n : ℕ) : rowMat n (Pi.single (Fin.last n) (1 : k)) = 1 := by
  ext i j
  rw [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_apply]
  split_ifs with hi
  · subst hi
    induction j using Fin.lastCases with
    | last => simp [Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j =>
      by_cases hj : j = Fin.last n
      · subst hj
        simp [Matrix.one_apply]
      · simp [Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  · rfl

def rowEl (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) : Mir k (n + 1) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (rowMat n r) h, by
    rw [mem_Mir_iff]
    show rowMat n r (Fin.last (n + 1)) = eLast k (n + 1)
    rw [rowMat, updateRow_ne (Fin.castSucc_ne_last _).symm]
    funext j
    simp only [GlobalTheory.BZMir.eLast, Matrix.one_apply, Pi.single_apply, eq_comm]⟩

theorem rowQ_rowEl (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) :
    rowQ k n (rowEl n r h) = r := by
  funext j
  show GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r (Fin.castSucc (Fin.last n)) (Fin.castSucc j) = r j
  rw [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_self, Fin.lastCases_castSucc]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_rowMat (n : ℕ) : Continuous (rowMat (k := k) n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat]
  by_cases hi : i = Fin.castSucc (Fin.last n)
  · subst hi
    simp only [Matrix.updateRow_self]
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      exact continuous_const
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact continuous_apply j
  · simp only [Matrix.updateRow_ne hi]
    exact continuous_const

theorem continuous_rowEl (n : ℕ) :
    Continuous fun r : {r : Fin (n + 1) → k // (rowMat n r).det ≠ 0} => rowEl n r.1 r.2 := by
  have hM : Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} =>
      GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1 :=
    (GlobalTheory.CompanionTheory.BZPhiPhi.continuous_rowMat n).comp continuous_subtype_val
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  refine ⟨hM, ?_⟩
  simp only [Function.comp_apply, Matrix.coe_units_inv]
  show Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} =>
    (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1)⁻¹
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM.matrix_det.inv₀ fun r => r.2).smul hM.matrix_adjugate

end Top

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.UnrCM

theorem algebraMap_int_ringOfIntegers_surjective (F : Type) [Field F] [NumberField F]
    (h : Module.finrank ℚ F = 1) : Function.Surjective (algebraMap ℤ (𝓞 F)) := by
  intro x
  obtain ⟨q, hq⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2 (x : F)
  have hx : IsIntegral ℤ (x : F) := x.isIntegral_coe
  have hint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff).1 (hq.symm ▸ hx)
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  simpa using hq

theorem finrank_maximalRealSubfield_of_subsingleton (E : Type) [Field E] [NumberField E] [IsCMField E]
    [Subsingleton (InfinitePlace E)] : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
  have h1 : Fintype.card (InfinitePlace E) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 inferInstance) Fintype.card_pos
  have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  have h4 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have h5 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h5
  omega

theorem nontrivial_infinitePlace_of_forall_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hU : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Nontrivial (InfinitePlace E) := by
  by_contra hn
  haveI : Subsingleton (InfinitePlace E) := not_nontrivial_iff_subsingleton.1 hn
  have hF := finrank_maximalRealSubfield_of_subsingleton E
  have hE : Module.finrank ℚ E ≠ 1 := by
    have h5 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, hF] at h5
    omega
  obtain ⟨P, hP, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := E) (𝒪 := 𝓞 E) hE
  have hbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hw := hU ⟨P, hP.isPrime, hbot⟩
  apply hram
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P) := hw
  haveI : Algebra.FormallyUnramified ℤ (𝓞 (maximalRealSubfield E)) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ _)
      (algebraMap_int_ringOfIntegers_surjective _ hF)
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P)

theorem nontrivial_infinitePlace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) :=
  fun E _ _ _ hU => nontrivial_infinitePlace_of_forall_isUnramifiedAt E hU

end GlobalTheory.CompanionTheory.UnrCM
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialSubrepresentation
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.DegPrinSeries

theorem nontrivial_subrepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → Nontrivial (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))) := by
  intro k _ _ _ _ a b χ₁ χ₂ hχ₁ hχ₂
  have hdetChar : ∀ (m : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ →
      GlobalTheory.PRep.IsSmooth (GlobalTheory.SmGL.detRep (Fin m) χ) := by
    intro m χ hχ
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ) := by
      rw [Units.continuous_iff]
      constructor
      · have hval : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)) =
            fun g : GL (Fin m) k => Matrix.det (g : Matrix (Fin m) (Fin m) k) := by
          funext g
          exact Matrix.GeneralLinearGroup.val_det_apply g
        rw [hval]
        exact Units.continuous_val.matrix_det
      · have hinv : (fun g : GL (Fin m) k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
            fun g => Matrix.det ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) := by
          funext g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [hinv]
        exact Units.continuous_coe_inv.matrix_det
    unfold GlobalTheory.SmGL.detRep
    rw [GlobalTheory.SmGL.isSmooth_ofChar_iff]
    unfold GlobalTheory.SmGL.IsSmoothChar at hχ ⊢
    exact hc.isOpen_preimage _ hχ
  have hsmooth := GlobalTheory.SmGL.isSmooth_comp
    (GlobalTheory.SmGL.isSmooth_extTensor (hdetChar a χ₁ hχ₁) (hdetChar b χ₂ hχ₂))
    (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm.toMonoidHom
    (by exact (continuous_apply Bool.false).prodMk (continuous_apply Bool.true))
  have hu : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid ℂ ℂ) h0
    simp at this
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : a + b = a + b))) _
    hsmooth ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  refine ⟨⟨⟨⊥, fun g ⦃v⦄ hv => ?_⟩, ⟨⊤, fun _ ⦃_⦄ _ => Submodule.mem_top⟩, fun hEq => ?_⟩⟩
  · rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  · have hsub := congrArg Subrepresentation.toSubmodule hEq
    have hf : f = 0 := (Submodule.mem_bot ℂ).1 (Submodule.eq_top_iff'.1 hsub f)
    rw [hf] at hf1
    apply hu
    rw [← hf1]
    first
    | rfl
    | simp

end GlobalTheory.CompanionTheory.DegPrinSeries
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Fin n × Fin n

abbrev Ix (n : ℕ) : Type := Bool × Pos n

abbrev Cr (n : ℕ) (V : Type) : Type := Finset (Ix n) → V

def keyR (i : Ix n) : ℕ := (if i.1 then n * n else 0) + CompanionTheory.D.LK.key i.2

def sgR (i : Ix n) (A : Finset (Ix n)) : ℂ := (-1) ^ (A.filter fun j => keyR j < keyR i).card

def cp (p q r : Pos n) : ℂ :=
  (if p.1.2 = q.1.1 ∧ r.1 = (p.1.1, q.1.2) then 1 else 0) - (if q.1.2 = p.1.1 ∧ r.1 = (q.1.1, p.1.2) then 1 else 0)

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then 0 else sgR i A • x (insert i A)
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def creR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then sgR i A • x (A.erase i) else 0
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def liftR (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cr n V →ₗ[ℂ] Cr n V' :=
  T.compLeft (Finset (Ix n))

def rl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (i : Ix n) : Module.End ℂ V :=
  if i.1 then E1 i.2.1.1 i.2.1.2 + E2 i.2.1.1 i.2.1.2 else E2 i.2.1.1 i.2.1.2

def torV (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Bool × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2 p.2 else E2 p.2 p.2

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Lt n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2.1 p.2.2 else E2 p.2.1 p.2.2

structure Pair2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl1 : GlRel E1
  gl2 : GlRel E2
  comm : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b

end Chains

def Inv2 (a : FreeAlgebra ℂ (Lt n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def LiftInv : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Pair2 E1 E2 → (∀ a b (x y : V), inner ℂ (kF E1 E2 a b x) y = inner ℂ x (kF E1 E2 b a y)) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ (μ : Fin n → ℝ) (v w : V), v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a : FreeAlgebra ℂ (Lt n), Inv2 a ∧ ev2 E1 E2 a v = w

end GlobalTheory.CompanionTheory.RealMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicElementBlockForm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ParabBlock

theorem parab_eq_blk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (p : parab (w.adicCompletion E) (two (stdSum h))), ∃ X, (p : GLw n w) = GlobalTheory.BCT.blk h w ((leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm (leviProj (w.adicCompletion E) (two (stdSum h)) p)) X := by
  intro E _ _ _ n a b h w p
  obtain ⟨m, hm⟩ : ∃ m, m = (leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (leviProj (w.adicCompletion E) (two (stdSum h)) p) := ⟨_, rfl⟩
  have h1 : ∀ i j, (m.1 : Matrix _ _ (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) := by
    intro i j; rw [hm]; rfl
  have h2 : ∀ i j, (m.2 : Matrix _ _ (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) := by
    intro i j; rw [hm]; rfl
  have h0 : ∀ (i : Fin b) (j : Fin a),
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
    intro i j
    exact mem_parab_iff.1 p.2 true false i j (by decide)
  rw [← hm]
  let B : Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun i j =>
    ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j))
  refine ⟨(m.1⁻¹).val * B, ?_⟩
  have hM : Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * ((m.1⁻¹).val * B)) 0 m.2.val) =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) := by
    have hc : m.1.val * ((m.1⁻¹).val * B) = B := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [hc]
    refine Matrix.ext fun i j => ?_
    obtain ⟨i, rfl⟩ := (stdSum h).surjective i
    obtain ⟨j, rfl⟩ := (stdSum h).surjective j
    have hs : finSumFinEquiv.trans (finCongr h) = stdSum h := rfl
    rw [hs]
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · exact h1 i j
    · rfl
    · exact (h0 i j).symm
    · exact h2 i j
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * ((m.1⁻¹).val * B)) 0 m.2.val)) := by
    rw [hM]; exact (p : GLw n w).isUnit
  unfold GlobalTheory.BCT.blk
  simp only
  rw [dite_eq_left hU]
  exact Units.ext (by rw [IsUnit.unit_spec, hM])

end GlobalTheory.CompanionTheory.ParabBlock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowQMulOfMemQ
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

namespace GlobalTheory.CompanionTheory.BZPhiPhi

theorem rowQ_mul_of_mem_Q (k : Type) [Field k] (n : ℕ) (q g : Mir k (n + 1)) (hq : q ∈ Q k n) :
    rowQ k n (q * g) = rowQ k n g := by
  have hb : (blockMat k (n + 1) ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)) (Fin.last n) =
      eLast k n := by
    have h := (mem_Mir_iff k (mirabolicProjection k (n + 1) q)).1 hq
    exact h
  have hg : ∀ j : Fin (n + 1), ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.last (n + 1)) (Fin.castSucc j) = 0 := by
    intro j
    have := congrFun ((mem_Mir_iff k (g : GL (Fin (n + 2)) k)).1 g.2) (Fin.castSucc j)
    simpa [eLast, Fin.castSucc_ne_last] using this
  funext j
  have hb' : ∀ l : Fin (n + 1), ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.castSucc (Fin.last n)) (Fin.castSucc l) = eLast k n l := fun l => congrFun hb l
  simp only [rowQ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc (n := n + 1), hg, hb', mul_zero, add_zero]
  simp [eLast, Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_open_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ThetaOpen k := by
  first | exact @GlobalTheory.CompanionTheory.BZFun.thetaOpen | exact GlobalTheory.CompanionTheory.BZFun.thetaOpen | (intros; apply GlobalTheory.CompanionTheory.BZFun.thetaOpen <;> assumption)
end

