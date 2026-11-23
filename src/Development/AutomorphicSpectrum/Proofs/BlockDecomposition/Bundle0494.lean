module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
public import GroundTheory.AutomorphicForms.ReductionFinite
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

section Join

variable {R : Type*} {m r s : ℕ}

def colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) : Matrix (Fin m) (Fin (r + s)) R :=
  Matrix.of fun i k => Sum.elim (y₁ i) (y₂ i) (finSumFinEquiv.symm k)

def colL (y : Matrix (Fin m) (Fin (r + s)) R) : Matrix (Fin m) (Fin r) R := Matrix.of fun i j => y i (Fin.castAdd s j)

def colR (y : Matrix (Fin m) (Fin (r + s)) R) : Matrix (Fin m) (Fin s) R := Matrix.of fun i j => y i (Fin.natAdd r j)

@[simp] theorem colJoin_castAdd (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) (i : Fin m) (j : Fin r) :
    colJoin y₁ y₂ i (Fin.castAdd s j) = y₁ i j := by
  simp [colJoin]

@[simp] theorem colJoin_natAdd (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) (i : Fin m) (j : Fin s) :
    colJoin y₁ y₂ i (Fin.natAdd r j) = y₂ i j := by
  simp [colJoin]

@[simp] theorem colL_colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colL (colJoin y₁ y₂) = y₁ := by
  ext i j; simp [colL]

@[simp] theorem colR_colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colR (colJoin y₁ y₂) = y₂ := by
  ext i j; simp [colR]

@[simp] theorem colJoin_colL_colR (y : Matrix (Fin m) (Fin (r + s)) R) : colJoin (colL y) (colR y) = y := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [colL]
  · simp [colR]

theorem colJoin_injective {y₁ y₁' : Matrix (Fin m) (Fin r) R} {y₂ y₂' : Matrix (Fin m) (Fin s) R}
    (h : colJoin y₁ y₂ = colJoin y₁' y₂') : y₁ = y₁' ∧ y₂ = y₂' :=
  ⟨by rw [← colL_colJoin y₁ y₂, h, colL_colJoin], by rw [← colR_colJoin y₁ y₂, h, colR_colJoin]⟩

def joinEquiv : Matrix (Fin m) (Fin r) R × Matrix (Fin m) (Fin s) R ≃ Matrix (Fin m) (Fin (r + s)) R where
  toFun z := colJoin z.1 z.2
  invFun y := (colL y, colR y)
  left_inv z := by simp
  right_inv y := by simp

theorem colJoin_map {R' : Type*} (f : R → R') (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    (colJoin y₁ y₂).map f = colJoin (y₁.map f) (y₂.map f) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_add [Add R] (y₁ y₁' : Matrix (Fin m) (Fin r) R) (y₂ y₂' : Matrix (Fin m) (Fin s) R) :
    colJoin (y₁ + y₁') (y₂ + y₂') = colJoin y₁ y₂ + colJoin y₁' y₂' := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_neg [Neg R] (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colJoin (-y₁) (-y₂) = -colJoin y₁ y₂ := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_sub [Sub R] (y₁ y₁' : Matrix (Fin m) (Fin r) R) (y₂ y₂' : Matrix (Fin m) (Fin s) R) :
    colJoin (y₁ - y₁') (y₂ - y₂') = colJoin y₁ y₂ - colJoin y₁' y₂' := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

end Join

variable {D : D7}

theorem rat_colJoin {m r s : ℕ} (p : Matrix (Fin m) (Fin r) D.host.E) (q : Matrix (Fin m) (Fin s) D.host.E) :
    rat (colJoin p q) = colJoin (rat p) (rat q) :=
  colJoin_map _ p q

def cellTerm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) : ℂ :=
  ψ (trA (Matrix.trace (inner V (rat q) y₂))) *
    (ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r))) *
      Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a)))

end GlobalTheory.CompanionTheory.EisUnfold

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicNormBounded
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

open GroundTheory.Automorphic.Reduction

theorem finprod_le_prod_of_le {α : Type*} {f b : α → ℝ} (S : Finset α) (h0 : ∀ a, 0 ≤ f a)
    (hS : ∀ a ∈ S, f a ≤ b a) (hb : ∀ a ∈ S, 1 ≤ b a) (h1 : ∀ a, a ∉ S → f a ≤ 1) :
    ∏ᶠ a, f a ≤ ∏ a ∈ S, b a := by
  classical
  have hone : (1 : ℝ) ≤ ∏ a ∈ S, b a := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) hb
    simpa using this
  by_cases hf : (Function.mulSupport f).Finite
  · set c : α → ℝ := fun a => if a ∈ S then b a else 1 with hc
    have hcs : Function.mulSupport c ⊆ (S : Set α) := fun a ha => by
      by_contra h
      exact ha (by simp only [hc]; exact if_neg fun h' => h (Finset.mem_coe.2 h'))
    have hcf : (Function.mulSupport c).Finite := S.finite_toSet.subset hcs
    have hle : ∏ᶠ a, f a ≤ ∏ᶠ a, c a :=
      finprod_le_finprod_of_nonneg hf hcf h0 fun a => by
        simp only [hc]
        split_ifs with h
        · exact hS a h
        · exact h1 a h
    rw [finprod_eq_prod_of_mulSupport_subset c hcs] at hle
    refine hle.trans (le_of_eq (Finset.prod_congr rfl fun a ha => ?_))
    simp only [hc]
    rw [if_pos ha]
  · rw [finprod_of_infinite_mulSupport hf]
    exact hone

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin N → AF F) :=
  {y | ∀ i, ∀ v, v ∉ S → (y i).2 v ∈ v.adicCompletionIntegers F}

theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (N := N) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)
  have h2 : IsOpen {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} :=
    h.preimage continuous_snd
  have : integralOutside (N := N) S = ⋂ i : Fin N, (fun y : Fin N → AF F => y i) ⁻¹'
      {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [integralOutside, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isOpen_iInter_of_finite fun i => h2.preimage (continuous_apply i)

theorem exists_mem_integralOutside (y : Fin N → AF F) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), y ∈ integralOutside S := by
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.2
  have hfin := Filter.eventually_cofinite.1 h
  refine ⟨hfin.toFinset, fun i v hv => ?_⟩
  by_contra hc
  exact hv (hfin.mem_toFinset.2 fun h' => hc (h' i))

theorem exists_finset_subset_integralOutside {D : Set (Fin N → AF F)} (hD : IsCompact D) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), D ⊆ integralOutside S := by
  classical
  obtain ⟨T, hT⟩ := hD.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => integralOutside (N := N) S)
    isOpen_integralOutside (fun y _ => by
      obtain ⟨S, hS⟩ := exists_mem_integralOutside y
      exact Set.mem_iUnion.2 ⟨S, hS⟩)
  refine ⟨T.sup id, fun y hy i v hv => ?_⟩
  obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 (hT hy)
  exact hyS i v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

theorem norm_finComp_le_one {y : Fin N → AF F} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F) : ‖finComp v y‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
    (Valued.toNormedField.norm_le_one_iff).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h i))

theorem continuous_euclidNorm_infComp (w : InfinitePlace F) :
    Continuous fun y : Fin N → AF F => euclidNorm (infComp w y) :=
  continuous_euclidNorm.comp (continuous_pi fun i =>
    (continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))

theorem continuous_norm_finComp (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun y : Fin N → AF F => ‖finComp v y‖ :=
  (continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (continuous_apply i))).norm

end GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

namespace GlobalTheory.CompanionTheory.RedCov.Simple


open GroundTheory.Automorphic.Reduction NormBound in
theorem exists_adelicNorm_le_of_isCompact :
    ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D →
      ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  intro F _ _ N D hD
  classical
  obtain ⟨S, hS⟩ := exists_finset_subset_integralOutside hD
  choose a ha1 ha using fun w : InfinitePlace F =>
    exists_one_le_bound hD (continuous_euclidNorm_infComp (N := N) w)
  choose b hb1 hb using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_one_le_bound hD (continuous_norm_finComp (N := N) v)
  have hA : (1 : ℝ) ≤ ∏ w, a w ^ w.mult := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : InfinitePlace F => (1 : ℝ))
      (g := fun w => a w ^ w.mult) (fun _ _ => zero_le_one)
      (fun w _ => one_le_pow₀ (ha1 w))
    simpa using this
  have hB : (1 : ℝ) ≤ ∏ v ∈ S, b v := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) (fun v _ => hb1 v)
    simpa using this
  refine ⟨(∏ w, a w ^ w.mult) * ∏ v ∈ S, b v, by positivity, fun y hy => ?_⟩
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (ha w y hy) _
  · exact finprod_le_prod_of_le S (fun _ => norm_nonneg _) (fun v _ => hb v y hy)
      (fun v _ => hb1 v) fun v hv => norm_finComp_le_one fun i => hS hy i v hv

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralFiniteLargeExponent
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

namespace GlobalTheory.CompanionTheory.ConeInt

theorem setLIntegral_Ici_rpow_lt_top {a b : ℝ} (ha : a < -1) (hb : 0 < b) :
    ∫⁻ x in Ici b, ENNReal.ofReal (x ^ a) < ⊤ := by
  have h : IntegrableOn (fun x : ℝ => x ^ a) (Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2 (integrableOn_Ioi_rpow_of_lt ha hb)
  exact h.lintegral_lt_top

theorem le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (i : Fin r) :
    min c 1 ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hb0 : 0 < min c 1 := lt_min hc one_pos
  have hb1 : min c 1 ≤ 1 := min_le_right _ _
  have key : ∀ (k : ℕ) (i : Fin r), i.val + k + 1 = r → min c 1 ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simpa using (min_le_left c 1).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp only; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : min c 1 * t ⟨i.val + 1, hj⟩ ≤ c * t ⟨i.val + 1, hj⟩ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hpos _).le
      calc min c 1 ^ (k + 1 + 1) = min c 1 * min c 1 ^ (k + 1) := pow_succ' _ _
        _ ≤ min c 1 * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hb0.le
        _ ≤ t i := h3.trans h2
  have hk : i.val + (r - i.val - 1) + 1 = r := by omega
  refine le_trans ?_ (key (r - i.val - 1) i hk)
  exact pow_le_pow_of_le_one hb0.le hb1 (by omega)

theorem integrand_eq (F : Type) [Field F] [NumberField F] (n : ℕ) {r : ℕ} (m : ℕ) {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) =
      ∏ i, ENNReal.ofReal (t i ^ (-(m : ℝ) -
        ((2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1)) := by
  have hnn : (0 : ℝ) ≤ ∏ i, (t i)⁻¹ ^ m := Finset.prod_nonneg fun i _ => pow_nonneg (inv_pos.2 (ht i)).le _
  rw [← ENNReal.ofReal_mul hnn, ← ENNReal.ofReal_prod_of_nonneg fun i _ => Real.rpow_nonneg (ht i).le _]
  congr 1
  unfold modulus
  rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := ht i
  rw [Real.rpow_sub h, Real.rpow_sub h, Real.rpow_neg h.le, Real.rpow_natCast, Real.rpow_intCast, Real.rpow_one,
    inv_pow, mul_inv]
  field_simp

end GlobalTheory.CompanionTheory.ConeInt

namespace GlobalTheory.CompanionTheory.ConeInt


open GlobalTheory.SiegelSet in
theorem lintegral_cone_lt_top : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) (c : ℝ), 0 < c → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n r c hc
  refine ⟨2 * Module.finrank ℚ F * (2 * r + 1) + 1, fun m hm => ?_⟩
  have hb : 0 < min c 1 ^ r := pow_pos (lt_min hc one_pos) _
  let a : Fin r → ℝ := fun i => -(m : ℝ) -
    ((2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1
  have ha : ∀ i, a i < -1 := by
    intro i
    have hz : (-(m : ℤ)) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) < 0 := by
      have hi : (i.val : ℤ) + 1 ≤ r := by exact_mod_cast i.isLt
      have hm' : 2 * (Module.finrank ℚ F : ℤ) * (2 * r + 1) + 1 ≤ m := by exact_mod_cast hm
      have hd : (0 : ℤ) ≤ 2 * (Module.finrank ℚ F : ℤ) := by positivity
      have hn : (0 : ℤ) ≤ n := by positivity
      have : 2 * (Module.finrank ℚ F : ℤ) * (-(n : ℤ) + 2 * (i.val : ℤ) + 1) ≤
          2 * (Module.finrank ℚ F : ℤ) * (2 * r + 1) :=
        mul_le_mul_of_nonneg_left (by omega) hd
      nlinarith
    have hz' : ((-(m : ℤ) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) < 0 := by
      exact_mod_cast hz
    have : a i = ((-(m : ℤ) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1 := by
      simp only [a]; push_cast; ring
    rw [this]; linarith
  have hsub : cone r c ⊆ Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r) :=
    fun t ht i _ => le_of_mem_cone hc ht i
  have hmeas : MeasurableSet (Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ici
  calc ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹)
      ≤ ∫⁻ t in Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r),
          ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ t in Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r), ∏ i, ENNReal.ofReal (t i ^ a i) :=
        setLIntegral_congr_fun hmeas fun t ht =>
          integrand_eq F n m fun i => hb.trans_le (ht i (mem_univ i))
    _ = ∏ i, ∫⁻ x in Ici (min c 1 ^ r), ENNReal.ofReal (x ^ a i) := by
        rw [volume_pi, Measure.restrict_pi_pi]
        exact GlobalTheory.RestrMeas.lintegral_fin_prod_eq_prod (E := fun _ => ℝ)
          (f := fun i x => ENNReal.ofReal (x ^ a i))
          fun i => ((measurable_id.pow_const (a i)).ennreal_ofReal).aemeasurable
    _ < ⊤ := ENNReal.prod_lt_top fun i _ => setLIntegral_Ici_rpow_lt_top (ha i) hb

end GlobalTheory.CompanionTheory.ConeInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBiadditiveBounded
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Arch

theorem continuous_biadditive_bounded :
    ∀ (N₁ N₂ N₃ : ℕ) (β : (Fin N₁ → ℝ) → (Fin N₂ → ℝ) → (Fin N₃ → ℝ)),
      (∀ u u' v, β (u + u') v = β u v + β u' v) →
      (∀ u v v', β u (v + v') = β u v + β u v') →
      Continuous (fun p : (Fin N₁ → ℝ) × (Fin N₂ → ℝ) => β p.1 p.2) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, ‖β u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  intro N₁ N₂ N₃ β h₁ h₂ hβ
  have smul₁ : ∀ (c : ℝ) u v, β (c • u) v = c • β u v := by
    intro c u v
    exact map_real_smul (AddMonoidHom.mk' (fun u => β u v) fun u u' => h₁ u u' v)
      (hβ.comp (continuous_id.prodMk continuous_const)) c u
  have smul₂ : ∀ (c : ℝ) u v, β u (c • v) = c • β u v := by
    intro c u v
    exact map_real_smul (AddMonoidHom.mk' (fun v => β u v) fun v v' => h₂ u v v')
      (hβ.comp (continuous_const.prodMk continuous_id)) c v
  have zero₁ : ∀ v, β 0 v = 0 := fun v => by simpa using smul₁ 0 0 v
  have zero₂ : ∀ u, β u 0 = 0 := fun u => by simpa using smul₂ 0 u 0
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuous_iff.mp hβ 0 1 one_pos
  have key : ∀ u v, ‖u‖ < δ → ‖v‖ < δ → ‖β u v‖ < 1 := by
    intro u v hu hv
    have h := hsmall (u, v) (by rw [dist_zero_right, Prod.norm_def]; exact max_lt hu hv)
    simpa [zero₁, dist_zero_right] using h
  obtain ⟨s, rfl⟩ : ∃ s, δ = 2 * s := ⟨δ / 2, by ring⟩
  have hs0 : 0 < s := by linarith
  have hsδ : s < 2 * s := by linarith
  refine ⟨4 / (2 * s) ^ 2, by positivity, fun u v => ?_⟩
  by_cases hu : u = 0
  · simp [hu, zero₁]
  by_cases hv : v = 0
  · simp [hv, zero₂]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnu : ‖(s / ‖u‖) • u‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (div_pos hs0 hu').le]
    field_simp
  have hnv : ‖(s / ‖v‖) • v‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (div_pos hs0 hv').le]
    field_simp
  have hb := key ((s / ‖u‖) • u) ((s / ‖v‖) • v) (by rw [hnu]; exact hsδ) (by rw [hnv]; exact hsδ)
  rw [smul₁, smul₂, smul_smul, norm_smul,
    Real.norm_of_nonneg (mul_pos (div_pos hs0 hu') (div_pos hs0 hv')).le] at hb
  have e : s / ‖u‖ * (s / ‖v‖) * ‖β u v‖ = (‖β u v‖ * (s * s)) / (‖u‖ * ‖v‖) := by ring
  rw [e, div_lt_one (mul_pos hu' hv')] at hb
  rw [show 4 / (2 * s) ^ 2 * ‖u‖ * ‖v‖ = (‖u‖ * ‖v‖) / (s * s) by ring,
    le_div_iff₀ (mul_pos hs0 hs0)]
  exact hb.le

end GlobalTheory.CompanionTheory.Arch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFourierCharacterOfMatrix
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem continuous_chiT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ T : Matrix (Fin n) (Fin n) E, Continuous (chiT σ ψ T) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ ψ hψ T
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AF F ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing (AF F)
  have htr : Continuous (Algebra.trace (AF F) (AF F ⊗[F] E)) := GlobalTheory.CompanionTheory.SW.TopK.continuous_trace (AF F)
  unfold chiT
  refine hψ.1.comp (Continuous.neg (continuous_const.mul (htr.comp ?_)))
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_trace

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

abbrev Idx (n d : ℕ) : Type := Fin n ⊕ (Fin d × {p : Fin n × Fin n // p.1 < p.2})

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hCo (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ}
    (S : HermR R σ n) : Idx n d → R :=
  Sum.elim
    (fun i => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    (fun q => (Algebra.TensorProduct.basis R b).repr
      ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) q.2.1.1 q.2.1.2) q.1)

def coordForm (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) : Matrix (Idx n d) (Idx n d) F :=
  Matrix.fromBlocks 1 0 0
    (Matrix.blockDiagonal fun _ : {p : Fin n × Fin n // p.1 < p.2} =>
      Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l)))

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummerStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariant_cup_kummer : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → ∀ (ϖ' : 𝓞 F) (y' : Ω) (κ' χ' : Dec (F := F) A → ZMod (l ^ r)) (z' : Z2 (muLoc F l r A)), ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → y' ^ (l ^ r) = algebraMap F Ω (ϖ' : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y' = ζ ^ (κ' g).val * y') → (∀ g h, χ' (g * h) = χ' g + χ' h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) → (∀ g h, z'.1 (g, h) = κ' g * χ' h) → (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk z' := by
  first | exact @GlobalTheory.CompanionTheory.KapChi.cup_class_eq | exact GlobalTheory.CompanionTheory.KapChi.cup_class_eq | (intros; apply GlobalTheory.CompanionTheory.KapChi.cup_class_eq <;> assumption)
end

