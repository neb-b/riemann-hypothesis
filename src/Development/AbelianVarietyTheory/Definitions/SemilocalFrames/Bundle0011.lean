module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKFIff
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.NoPr

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.CellAmp

def AmpKF0 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

end GlobalTheory.NoPr

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CellDataExists
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellAmp.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
private theorem inv_mul_conj_mul_cancel {n : Type*} [Fintype n] [DecidableEq n] (A B C D γ a : Matrix n n ℂ)
    (hγ : IsUnit γ.det) (ha : IsUnit a.det) :
    A⁻¹ * (a * B)⁻¹ * γ * (γ⁻¹ * a * γ * C) * D = A⁻¹ * B⁻¹ * γ * C * D := by
  rw [Matrix.mul_inv_rev]
  have h1 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hγ
  have h2 : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  calc A⁻¹ * (B⁻¹ * a⁻¹) * γ * (γ⁻¹ * a * γ * C) * D
      = A⁻¹ * B⁻¹ * (a⁻¹ * ((γ * γ⁻¹) * a)) * γ * C * D := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul, h2, Matrix.mul_one]


open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.pairMaj_stabAct {k r : ℕ} (γ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : IsUnit γ.det)
    (ha : IsUnit a.det) (b : ℝ) (p : _root_.Formalism.MainNotions.S.PairSp k r) : _root_.GlobalTheory.CellAmp.pairMaj γ b (_root_.Formalism.MainNotions.S.stabAct γ a p) = _root_.GlobalTheory.CellAmp.pairMaj γ b p :=
  congrArg (fun M => _root_.Formalism.FourierDecayAlt.B.gN M ^ (-b))
    (inv_mul_conj_mul_cancel (of p.1.1) (of p.1.2) (of p.2.2) (of p.2.1) γ a hγ ha)

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.ell_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) : _root_.Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold _root_.Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp [_root_.Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [_root_.Formalism.QuantumDeterminants.eI]))


open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.cellData_open {k r : ℕ} (L : _root_.Formalism.MainNotions.S.LocBessel k r) (μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) (hinv : g⁻¹ * g = 1)
    (hG : 0 < _root_.Formalism.QuantumDeterminants.Gf k r L.z L.z' g) (hm : _root_.Formalism.FourierDecayAlt.C2.IsMonomial (_root_.Formalism.QuantumDeterminants.Zhat k r L.z L.z' g))
    (hR : _root_.Formalism.MainNotions.S.RStab k r g = {1}) :
    _root_.GlobalTheory.CellAmp.CellData L μG g (Measure.dirac (fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j)) μG (_root_.Formalism.MainNotions.S.pairMeas L) := by
  have hone : (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) = 1 := rfl
  refine ⟨hg, hG, hm, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    subst ha
    rw [Matrix.mul_one, hinv]
    unfold _root_.Formalism.QuantumDeterminants.psi
    rw [_root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz.1, _root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz'.1]
  · refine ⟨inferInstance, Measure.dirac_ne_zero, ?_, ?_⟩
    · rw [hR, Measure.dirac_apply]
      simp only [Set.mem_singleton_iff, Set.indicator_apply, Set.mem_setOf_eq]
      rw [hone]
      simp
    · intro s hs
      rw [hR, Set.mem_singleton_iff] at hs
      subst hs
      have hid : _root_.Formalism.QuantumDeterminants.lmulM (k := k) (r := r) 1 = id := funext fun x => by
        unfold _root_.Formalism.QuantumDeterminants.lmulM
        rw [Matrix.one_mul]
        rfl
      rw [hid, Measure.map_id]
  · intro f hf
    have hstab : ∀ x, _root_.Formalism.MainNotions.S.stabAct g (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) x = x := by
      intro x
      unfold _root_.Formalism.MainNotions.S.stabAct
      rw [hone, Matrix.one_mul, Matrix.mul_one, hinv, Matrix.one_mul]
      rfl
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hstab]
  · intro f hf
    rw [Measure.map_congr (ae_eq_dirac _)]
    erw [Measure.map_const]
    rw [measure_univ, one_smul]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hone, Matrix.mul_one, hinv, hone, Matrix.one_mul]
    rfl

end GlobalTheory.CellAmp.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def qEps {n : ℕ} (ε : Fin n → Bool) (y : Fin n → ℂ) : ℝ := ∑ i, (if ε i then 1 else -1) * ‖y i‖ ^ 2

def gauss {n : ℕ} (y : Fin n → ℂ) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def gaussDens {n : ℕ} (ε : Fin n → Bool) (β : ℝ) : ℝ :=
  deriv (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) β

def sgn (R : Type) [Ring R] (s : Bool) : R := if s then 1 else -1

def gaussSum (I : AutInst) (β : I.E) (x : I.GA) : ENNReal :=
  ∑' y : {y : Fin I.n → I.E // y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = β},
    ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y.1 i)))

def meanConst (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2) * (Formalism.HermitianLatticesTheory.vInv E ^ (M * Formalism.HermitianLatticesTheory.fDeg E))⁻¹ /
    Formalism.HermitianLatticesTheory.lValEta E M

def SiegelMean : Prop :=
  ∀ (I : AutInst), 3 ≤ I.n → ∀ (s : Bool) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (fund : Set I.GA), I.IsFundDom (I.muA μf) fund →
    I.muA μf fund < ⊤ ∧
    ∫⁻ x in fund, gaussSum I (sgn I.E s) x ∂(I.muA μf) =
      I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s))

def IsPerpInst (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf) : Prop :=
  (∀ y, e (star y) = star (e y)) ∧ I'.n + 1 = I.n ∧ star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s ∧
    star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = I'.J.map e ∧ x ∈ lamX I (1, xf) ∧
    ∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)

def GaugeUnfold : Prop :=
  ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E)
    (xf : I.Gf), 3 ≤ I.n → IsPerpInst I I' e s x A xf →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
      (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure]
      (fund : Set I.GA), IsGaugeAll I c → IsGaugeAll I' c' → I.IsFundDom (I.muA μf) fund →
      ENNReal.ofReal (∏ v, c v) * (∫⁻ g in fund, gaussSum I (sgn I.E s) g ∂(I.muA μf)) / μf I.Kset =
        gaugeVol I' c' μf' * ENNReal.ofReal (2 ^ (I.n * I.f) * ∏ v, gaussDens (I.ε v) (sgn ℝ s))

theorem gauss_pos {n : ℕ} (y : Fin n → ℂ) : 0 < gauss y := Real.exp_pos _

end GlobalTheory.GaussMean
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegVol
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def IsReal (H : HermSpace K V) (k r : ℕ) (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ x y, Φ (x + y) = Φ x + Φ y) ∧ (∀ (c : K) x, Φ (c • x) = σ c • Φ x) ∧
    (∀ x y, herm (Hpk k r) (Φ x) (Φ y) = σ (H.B x y)) ∧ Submodule.span ℂ (Set.range Φ) = ⊤

def IsFrameOf {H : HermSpace K V} {r : ℕ} (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ)
    (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Prop :=
  IsReal H k r σ Φ ∧ inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧ (∃ c : ℂ, IsNormal0 k r N.j_le β c z z' g) ∧
    (∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) ∧
      g *ᵥ Φ (N.F'.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a)) ∧
    (∀ b : Fin r, N.j ≤ b.val → Φ (N.ist b) = (((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) • bvec (esI k r b)) ∧
    Φ N.F.z = z' ∧ g *ᵥ Φ N.F'.z = z

def IsPlaces {ι : Type} (σ : ι → (K →+* ℂ)) : Prop :=
  (∀ v a, σ v (star a) = starRingEnd ℂ (σ v a)) ∧ ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w

def realPts {ι : Type} {k r : ℕ} (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) : Set (ι → Mt k r) :=
  {m | ∃ s ∈ Γ, ∀ v x, Matrix.of (m v) *ᵥ Φ v x = Φ v (s x)}

def mulP {ι : Type} {k r : ℕ} (m x : ι → Mt k r) : ι → Mt k r := fun v => lmulM (Matrix.of (m v)) (x v)

def IsFund {ι : Type} {k r : ℕ} (Γ R Ω : Set (ι → Mt k r)) : Prop :=
  MeasurableSet Ω ∧ ∀ x ∈ R, ∃! m, m ∈ Γ ∧ mulP m x ∈ Ω

def RP {ι : Type} (k r : ℕ) (g : ι → Mat k r) : Set (ι → Mt k r) := {x | ∀ v, Matrix.of (x v) ∈ Rset k r (g v)}

end GlobalTheory.DegVol
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagBase

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def IsAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E) : Prop :=
  (∀ y, e (star y) = star (e y)) ∧ I.n = I₀.n + 2 * ∑ i, j i ∧ (∀ i, Submodule.IsFullLattice I.E (Λ i)) ∧
    (∀ i k, (T i)ᴴ * I.J * T k = 0 ∧ (T' i)ᴴ * I.J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * I.J * T' k = 0)) ∧
    (∀ i, (T i)ᴴ * I.J * T' i = 1 ∧ (T i)ᴴ * I.J * T₀ = 0 ∧ (T' i)ᴴ * I.J * T₀ = 0) ∧
    T₀ᴴ * I.J * T₀ = I₀.J.map e ∧
    (∀ z, z ∈ lamX I (1, xf) ↔ ∃ (u u' : ∀ i, Fin (j i) → I.E) (y : Fin I₀.n → I₀.E), (∀ i, u i ∈ Λ i) ∧
      (∀ i, ∀ t ∈ Λ i, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ y ∈ lamX I₀ (1, x₀) ∧
      z = ∑ i, T i *ᵥ u i + ∑ i, T' i *ᵥ u' i + T₀ *ᵥ fun l => e (y l)) ∧
    ∀ k z, z ∈ S k ↔ ∃ u : ∀ i, Fin (j i) → I.E, (∀ i, u i ∈ Λ i) ∧ (∀ i : Fin a, ¬ i.castSucc < k → u i = 0) ∧
      z = ∑ i, T i *ᵥ u i

def latGroup (I : AutInst) (xf : I.Gf) : Set I.Ginf :=
  {g | ∃ γ ∈ I.GFset, γ.1 = g ∧ xf⁻¹ * γ.2 * xf ∈ I.Kset}

def flagGroup (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set I.Ginf :=
  {g | g ∈ latGroup I xf ∧ ∀ v k, ∀ y ∈ flagAt I S v k, uMat (g v) *ᵥ y ∈ flagAt I S v k}

def leviGroup (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set I.Ginf :=
  {m | (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ∧
    ∃ g ∈ flagGroup I xf S, ∃ u : I.Ginf, (∀ v, u v ∈ flagN (I.ε v) (flagAt I S v)) ∧ g = u * m}

def sizesAt (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (g : I.Ginf) : Fin a → ℝ :=
  fun i => Formalism.HN.sizeQ (bas I) (frm I (g, xf)) (S i.succ) (S i.castSucc)

def slabVol (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ENNReal :=
  covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1}

section Mean

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

abbrev VecInf : Type := InfinitePlace E → Fin j → ℂ

def latAt (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) : Submodule ℤ (VecInf E j) :=
  Submodule.span ℤ ((fun (y : Fin j → E) (w : InfinitePlace E) =>
    (Matrix.of (g w))⁻¹ *ᵥ fun a => w.embedding (y a)) '' (Λ : Set (Fin j → E)))

def dualAt (L : Submodule ℤ (VecInf E j)) : Submodule ℤ (VecInf E j) :=
  Submodule.span ℤ {y | ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z}

def latMean (F : Submodule ℤ (VecInf E j) → ENNReal) : ENNReal :=
  ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1),
    covol (autGL E j (Quot.out c).1) ((haarGL E j).withDensity fun g => F (latAt E j (Quot.out c).1 g))
      {g | 0 < detNorm E j g}

def covAt (L : Submodule ℤ (VecInf E j)) : ℝ := ZLattice.covolume L volume

def gaussV (x : VecInf E j) : ℝ := Real.exp (-Real.pi * ∑ w, ∑ a, ‖x w a‖ ^ 2)

end Mean

end GlobalTheory.FlagBase
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocDecOfDecGap
section
open MeasureTheory NumberField Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace

namespace GlobalTheory.Dec

theorem locDec_of_decGap (hD : GlobalTheory.DSId.DecGap) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ)
    (hB : IsDSData B d) (hg : GapGe B h)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) : LocDec B h := by
  intro v g
  obtain ⟨h1, h2, h3, -⟩ := hB v
  simpa [h3.1] using (hD _ _ _ _ _ h1 h2 h (hg v) (hh v) (uMat g) g.2 _ h3.2 _ h3.2).2

end GlobalTheory.Dec
end

