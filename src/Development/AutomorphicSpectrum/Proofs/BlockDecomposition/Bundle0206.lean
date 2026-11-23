module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0199
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.KUFactsU

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem iwGL_entries {n : ℕ} {x : GL (Fin n) L} (hx : x ∈ IwGL L n) (i j : Fin n) :
    (x : Matrix (Fin n) (Fin n) L) i j ∈ intL L := by
  have hk := (Subgroup.mem_iInf.1 hx) (Fin.last n)
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
  have hmem : (Pi.single j 1 : Fin n → L) ∈ latK L n (Fin.last n) := by
    intro l
    simp only [Fin.val_last, l.isLt, if_true]
    by_cases hl : l = j
    · subst hl
      simp
    · simp [Pi.single_apply, hl]
  have h2 : (Matrix.GeneralLinearGroup.toLin : GL (Fin n) L ≃* _).toMonoidHom x •
      (Pi.single j 1 : Fin n → L) ∈ latK L n (Fin.last n) := by
    rw [← hk]
    exact Set.smul_mem_smul_set hmem
  have h3 := h2 i
  simp only [Fin.val_last, i.isLt, if_true] at h3
  show (x : Matrix (Fin n) (Fin n) L) i j ∈ Valued.v.integer
  rw [Valuation.mem_integer_iff]
  convert h3 using 2
  simp [Units.smul_def, Matrix.GeneralLinearGroup.toLin, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem iwU_le_KU (σ : L →+* L) (n : ℕ) : IwU σ n ≤ KU σ n := by
  intro x hx
  have hx' : (x : GL (Fin n) L) ∈ IwGL L n := Subgroup.mem_subgroupOf.1 hx
  have hxi : ((x : GL (Fin n) L))⁻¹ ∈ IwGL L n := inv_mem hx'
  have hmem : x ∈ ((KU σ n : Subgroup (GU σ n)) : Set (GU σ n)) := by
    rw [GlobalTheory.LFun.IntPtsUnitary.coe_KU, Set.mem_preimage, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    exact ⟨fun i j => iwGL_entries hx' i j, fun i j => iwGL_entries hxi i j⟩
  exact hmem

theorem ordL_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (d : ℤ) : ordL (ϖ ^ d) = d := by
  have h1 : Valued.v (ϖ ^ d) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_neg, smul_eq_mul, mul_one]
  have hne : Valued.v (ϖ ^ d) ≠ 0 := by
    rw [h1]
    exact WithZero.coe_ne_zero
  unfold ordL
  rw [dite_eq_right hne]
  have key : WithZero.unzero hne = Multiplicative.ofAdd (-d) :=
    WithZero.coe_injective (by rw [WithZero.coe_unzero, h1])
  rw [key, toAdd_ofAdd, neg_neg]

def expo (n : ℕ) (i : Fin n) : ℤ := (n : ℤ) - 1 - 2 * (i.val : ℤ)

def tGL {ϖ : L} (h0 : ϖ ≠ 0) (n : ℕ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ expo n i
  inv := Matrix.diagonal fun i => ϖ ^ (-expo n i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ h0]; simp

theorem tGL_mem {ϖ : L} (h0 : ϖ ≠ 0) {σ : L →+* L} (hσ : σ ϖ = ϖ) (n : ℕ) : tGL h0 n ∈ GU σ n := by
  show cT σ ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n *
    ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n
  have hc : cT σ ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => ϖ ^ expo n i := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [cT, tGL, map_zpow₀, hσ]
    · simp [cT, tGL, hab, Ne.symm hab]
  rw [hc]
  ext a b
  simp only [tGL, Matrix.diagonal_mul, Matrix.mul_diagonal, antiJ]
  split_ifs with hab
  · have he : expo n a + expo n b = 0 := by
      unfold expo
      omega
    rw [mul_one, ← zpow_add₀ h0, he, zpow_zero]
  · simp

theorem exists_strictDom {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ t : GU σ n, IsDiagM (t : GL (Fin n) L) ∧ IsStrictDom (t : GL (Fin n) L) := by
  obtain ⟨-, -, hσ, hϖ, -⟩ := h
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨⟨tGL h0 n, tGL_mem h0 hσ n⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · show (Matrix.diagonal fun i => ϖ ^ expo n i) i j = 0
    exact Matrix.diagonal_apply_ne _ hij
  · show ordL ((Matrix.diagonal fun i => ϖ ^ expo n i) j j) <
      ordL ((Matrix.diagonal fun i => ϖ ^ expo n i) i i)
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ordL_zpow hϖ, ordL_zpow hϖ]
    unfold expo
    have hlt : (i : ℕ) < j := hij
    omega

theorem kuFacts : PositivityTheory.SphericalProduct.KUFacts := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  exact ⟨ho, hc, iwU_le_KU σ n, exists_strictDom h n⟩

end GlobalTheory.CompanionTheory.KUFactsU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Rapid (h : C₀(ℝ, ℂ)) : Prop := ∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y

def lTr {n : ℕ} {V : Type} (x : G n) (f : Mat n → V) : Mat n → V := fun y => f (x.val * y)

def secCls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) : Set (Lp E.V 2 μ) :=
  {x | ∃ f, Sob μ f ∧ IsSec E f ∧ cls μ f = x}

def Std {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) [CompleteSpace E.V]
    {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ) : Prop :=
  LgFacts ∧ Unimod ∧ RCalc ∧ SobG ∧ AlgEst ∧ WaveSpeed ∧ WaveCpt ∧ CalcSteps ∧ SmoothOp ∧ PWdecay ∧
    (∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x) ∧
    (∀ x y : Msob μ E.V, ⟪(Ω x : Lp E.V 2 μ), y⟫_ℂ = ⟪(x : Lp E.V 2 μ), Ω y⟫_ℂ) ∧
    (∀ x : Msob μ E.V, ∃ v : Msob μ E.V, (v : Lp E.V 2 μ) = T x ∧ (v : Lp E.V 2 μ) + (Ω (Ω v) : Lp E.V 2 μ) = x) ∧
    (∀ x : Msob μ E.V, T ((x : Lp E.V 2 μ) + (Ω (Ω x) : Lp E.V 2 μ)) = x) ∧
    (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) ∧
    ∀ f : Mat n → E.V, Sob μ f → IsSec E f → (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2

def Row {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) [CompleteSpace E.V]
    {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (h : C₀(ℝ, ℂ)) (v : E.V) (f : Mat n → E.V) : Prop :=
  Sob μ f ∧ IsSec E f ∧ ∀ φ f' : Mat n → E.V, Sob μ φ → IsSec E φ → Sob μ f' → IsSec E f' →
    cls μ f' = F.Φ h (cls μ φ) → ⟪cls μ f, cls μ φ⟫_ℂ = ⟪v, f' 1⟫_ℂ

def FactorRapid : Prop :=
  ∀ h : C₀(ℝ, ℂ), Rapid h → ∃ h₁ h₂ : C₀(ℝ, ℂ), Rapid h₁ ∧ Rapid h₂ ∧ Rapid (star h₂) ∧ h = h₁ * h₂

def EvAdj : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), Rapid h → ∀ v : E.V, ∃ κ ∈ closure (secCls μ E), ∀ φ f' : Mat n → E.V, Sob μ φ → IsSec E φ →
      Sob μ f' → IsSec E f' → cls μ f' = F.Φ h (cls μ φ) → ⟪κ, cls μ φ⟫_ℂ = ⟪v, f' 1⟫_ℂ

def RowExists : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), Rapid h → ∀ v : E.V, ∃ f, Row μ E F h v f

def RowMatrix : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), (∀ v : E.V, ∃ f, Row μ E F h v f) →
      ∃ A : Mat n → (E.V →L[ℂ] E.V), ∀ v, Row μ E F h v (fun y => A y v)

def AdjSmooth : Prop :=
  ∀ (W V : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (A : W → (V →L[ℂ] V)) (s : Set W),
    (∀ v, ContDiffOn ℝ ∞ (fun y => A y v) s) → ContDiffOn ℝ ∞ (fun y => ContinuousLinearMap.adjoint (A y)) s

def LtSob : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], LgFacts → Unimod → RCalc →
    ∀ (x : G n) (f : Mat n → V), Sob μ f → Sob μ (lTr x f) ∧ ∀ g ∈ GLs n, Om (lTr x f) g = Om f (x.val * g)

def LtComm : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (x : G n) (f f' : Mat n → E.V), Sob μ f → Sob μ f' → cls μ f' = F.Φ h (cls μ f) →
      cls μ (lTr x f') = F.Φ h (cls μ (lTr x f))

def RowLeft : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (A : Mat n → (E.V →L[ℂ] E.V)), Rapid h → (∀ v, Row μ E F h v (fun y => A y v)) →
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ y ∈ GLs n, ∀ v, A (k.1 * y) v = A y (E.ρ k⁻¹ v)

def ActFormula : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (A : Mat n → (E.V →L[ℂ] E.V)), (∀ v, Row μ E F h v (fun y => A y v)) →
      ∀ f ∈ CE E, Cpt f → ∀ f', Sob μ f' → IsSec E f' → cls μ f' = F.Φ h (cls μ f) →
        ∀ x ∈ GLs n, act μ E (fun y => ContinuousLinearMap.adjoint (A y)) f x = f' x

def WaveRep : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ f ∈ CE E, Cpt f → ∃ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N ∧ (T ^ N) b = cls μ f ∧ IsWave E U ∧
      (∀ x ∈ GLs n, U 0 x = f x) ∧ ∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b

def WaveUniq : Prop :=
  WaveSpeed → CalcSteps → RCalc → ∀ (n : ℕ) (E : KMod n) (u u' : ℝ → Mat n → E.V), IsWave E u → IsWave E u' →
    (∀ x ∈ GLs n, u 0 x = u' 0 x) → ∀ t, ∀ x ∈ GLs n, u t x = u' t x

def PhiRes : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ), IsBump g T₀ → ∀ N : ℕ, 1 ≤ N →
      F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) = F.Φ (toC0 (hg c g)) * T ^ N

def WaveInt : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ), IsBump g T₀ → ∀ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N → IsWave E U →
      (∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b) →
      ∀ f', Sob μ f' → cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b →
        ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • U t x = f' x

def SupportRow : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ) (h : C₀(ℝ, ℂ)), IsBump g T₀ → Rapid h →
      (∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
        cls μ f' = F.Φ h (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x) →
      ∃ R : ℝ, ∀ (v : E.V) (f : Mat n → E.V), Row μ E F h v f → ∀ y ∈ GLs n, R < lg y → f y = 0

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisOpenSubgroupLocalUnits
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.InertOpen

section Local

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finiteSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.finiteSingle L v) := by
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Function.update (fun _ => 1) v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Function.update_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_const.update v continuous_id
  exact (RestrictedProduct.continuous_inclusion hle).comp hf

theorem continuous_localIdele' (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finiteSingle v)

theorem isOpen_valued_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    IsOpen {x : w.adicCompletion L | Valued.v x < 1} := by
  have := Valued.isOpen_ball (w.adicCompletion L) 1
  simpa [Valuation.restrict_lt_one_iff] using this

theorem isCompact_setOf_isUnitAt (w : HeightOneSpectrum (𝓞 L)) :
    IsCompact {x : (w.adicCompletion L)ˣ | IsUnitAt w x} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have e : ((↑) : (w.adicCompletion L)ˣ → w.adicCompletion L) '' {x | IsUnitAt w x} =
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) \ {x | Valued.v x < 1} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, not_lt, IsUnitAt]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.le, hx.ge⟩
    · rintro ⟨h1, h2⟩
      have hy : Valued.v y = 1 := le_antisymm h1 h2
      have h0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      exact ⟨Units.mk0 y h0, hy, rfl⟩
  rw [e]
  exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers L w).diff (isOpen_valued_lt_one w)

end Local

section Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem continuous_toAb' : Continuous (toAb E Ω) := continuous_quot_mk

theorem hausdorff_absolute_galois_abelianization : T2Space (Gab E Ω) := by
  haveI : Algebra.IsIntegral E Ω := (IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isIntegral
  haveI : T2Space (G E Ω) := krullTopology_t2
  haveI : IsClosed (((commutator (G E Ω)).topologicalClosure : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

end Gal

end GlobalTheory.CompanionTheory.InertOpen

namespace GlobalTheory.CompanionTheory.InertOpen

theorem exists_openSubgroup_ine_art_units : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (U : Subgroup (w.adicCompletion E)ˣ), IsOpen (U : Set (w.adicCompletion E)ˣ) → (∀ x ∈ U, IsUnitAt w x) →
    ∃ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) ∧
      ∀ σ ∈ V, σ ∈ Ine (F := E) A → ∃ x ∈ U, art (localIdele E w x) = toAb E Ω σ := by
  intro E Ω _ _ _ _ _ l _ art hart w A hA U hUo _
  haveI := hausdorff_absolute_galois_abelianization (E := E) (Ω := Ω)
  let f : (w.adicCompletion E)ˣ →* Gab E Ω := art.comp (localIdele E w)
  have hf : Continuous f := hart.quot.continuous.comp (continuous_localIdele' w)
  let K : Set (w.adicCompletion E)ˣ := {y | ∃ u ∈ U, f u = f y}
  have hK : IsOpen K := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨u, hu, hux⟩
    refine ⟨{y | x⁻¹ * y ∈ U}, ?_, hUo.preimage (continuous_const.mul continuous_id), ?_⟩
    · intro y hy
      refine ⟨u * (x⁻¹ * y), U.mul_mem hu hy, ?_⟩
      rw [map_mul, hux, ← map_mul, mul_inv_cancel_left]
    · show x⁻¹ * x ∈ U
      rw [inv_mul_cancel]
      exact U.one_mem
  let C : Set (Gab E Ω) := f '' ({x | IsUnitAt w x} \ K)
  have hC : IsClosed C := (((isCompact_setOf_isUnitAt w).diff hK).image hf).isClosed
  have h1 : (1 : Gab E Ω) ∉ C := by
    rintro ⟨y, ⟨-, hyK⟩, hy⟩
    exact hyK ⟨1, U.one_mem, by rw [map_one, hy]⟩
  have hW : (toAb E Ω) ⁻¹' Cᶜ ∈ nhds (1 : G E Ω) :=
    (hC.isOpen_compl.preimage continuous_toAb').mem_nhds (by simpa using h1)
  obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff E Ω _).1 hW
  refine ⟨M.fixingSubgroup, M.fixingSubgroup_isOpen, fun σ hσV hσI => ?_⟩
  obtain ⟨x, hxu, hx⟩ := (hart.ine w A hA (toAb E Ω σ)).2 ⟨σ, hσI, rfl⟩
  have hnot : toAb E Ω σ ∉ C := hMs hσV
  by_contra hne
  apply hnot
  refine ⟨x, ⟨hxu, ?_⟩, hx⟩
  rintro ⟨u, hu, hux⟩
  exact hne ⟨u, hu, hux.trans hx⟩

end GlobalTheory.CompanionTheory.InertOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.CompanionTheory.LTHodge

variable {l : ℕ} [Fact l.Prime]

def lineRep {K LL : FinExt l} (ψ : ↥(GK K) →* (↥LL.1)ˣ) :
    Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin 1) (Fin 1) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL.1).comp ψ))

def ltSeries {K : FinExt l} (π : ↥(OL K)) : PowerSeries ↥(OL K) :=
  PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card (↥(OL K) ⧸ Ideal.span {π})

def IsLTChar (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) : Prop :=
  ∃ (π : ↥(OL K)) (z : ℕ → Om l), Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, z (n + 1) ^ Nat.card (↥(OL K) ⧸ Ideal.span {π}) +
      (((π : ↥K.1) : Om l)) * z (n + 1) = z n) ∧
    ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
      ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) →
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
      ∀ n, HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
        ((g : GQ l) (z n))

def HasPeriods (P : LocPrime l) (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) : Prop :=
  ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ∃ y : P.R.BdR,
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ x : ↥K.1, g (μ x) = μ x) →
      P.actQdR g y = algebraMap (Om l) P.R.BdR (μ ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * y) ∧
    (μ = K.1.val → y ∈ (P.PD K).Fil 1 ∧ y ∉ (P.PD K).Fil 2) ∧
    (μ ≠ K.1.val → y ∈ (P.PD K).Fil 0 ∧ y ∉ (P.PD K).Fil 1)

end GlobalTheory.CompanionTheory.LTHodge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

section U

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

def IsPermW (w : GU σ n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ a c : Fin n, ((w : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a c = if c = π a then 1 else 0

variable [Valued L (WithZero (Multiplicative ℤ))]

def permWt (t : GU σ n) (π : Equiv.Perm (Fin n)) : ℤ :=
  ∑ a : Fin n, ((a.val : ℤ) + 1) * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a))

end U

def aOp {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) : G → ℂ :=
  fun g => ∑ r ∈ R, φ (g * r * t)

end GlobalTheory.CompanionTheory.SatPow

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointRegularStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_adjoint_regular : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg | exact GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
section
noncomputable section

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

def Lap {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) : Mat n → V :=
  fun g => -∑ p, Rd (bs p) (Rd (bs p) f) g

end GlobalTheory.CompanionTheory.FcSmooth
end
end

