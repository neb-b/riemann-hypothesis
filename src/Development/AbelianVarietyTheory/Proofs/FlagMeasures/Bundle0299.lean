module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardLatticeDualVectorsChangeUnipotent
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0284
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairChangedDualVectors
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ToC

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ}

def swapEs (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) : LocNG.FrameD H r :=
  ⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ LocNG.img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [LocNG.img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * k) Λ = LocNG.img g (LocNG.img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  induction s using Finset.induction_on with
  | empty => simp [H.h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

lemma pair_eq (hM : M.OK) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) (hT : Fr.T ≠ 0) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    (b : Fin (r + 1)) (a : Fin r) : H.h (n (Fr.f b)) (es₂ a) = H.h (n (Fr.f b)) (Fr.es a) := by
  obtain ⟨A, -, hA⟩ := (GlobalTheory.LocOver.UnipOnto.unipotent_onto M hM H r Fr hT).2.1 n hn
  have hb : ∀ c, H.h (Fr.f c) (es₂ a) = H.h (Fr.f c) (Fr.es a) := by
    intro c
    induction c using Fin.lastCases with
    | last =>
      have e1 : H.h (Fr.f (Fin.last r)) (es₂ a) = M.L.cj (H.h (es₂ a) (Fr.f (Fin.last r))) := H.h_herm _ _
      have e2 : H.h (Fr.f (Fin.last r)) (Fr.es a) = M.L.cj (H.h (Fr.es a) (Fr.f (Fin.last r))) := H.h_herm _ _
      rw [e1, e2, h3, Fr.h_sz]
    | cast i => rw [h2, Fr.h_es]
  rw [show n (Fr.f b) = _ from hA b, h_sum_left, h_sum_left]
  exact Finset.sum_congr rfl fun c _ => by rw [hb c]

lemma pulled (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (he : ∀ x y, S.h (e x) (e y) = H.h x y)
    (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hg : ∀ a, g a = e (f a))
    (hdual : ∀ a j, hf M.L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hiso : ∀ i j, hf M.L S.Hm (gs i) (gs j) = 0) :
    (∀ i j, H.h (e.symm (gs i)) (e.symm (gs j)) = 0) ∧
    (∀ i j : Fin r, H.h (f i.castSucc) (e.symm (gs j)) = if i = j then 1 else 0) ∧
    (∀ i, H.h (e.symm (gs i)) (f (Fin.last r)) = 0) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [← he, e.apply_symm_apply, e.apply_symm_apply]; exact hiso i j
  · rw [← he, e.apply_symm_apply, ← hg]
    change hf M.L S.Hm _ _ = _
    rw [hdual]; simp [Fin.castSucc_inj]
  · rw [H.h_herm, ← he, e.apply_symm_apply, ← hg]
    change M.L.cj (hf M.L S.Hm _ _) = _
    rw [hdual]
    have : Fin.last r ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
    simp [this]

variable {P : LocNG.FPair H r} {S : Frames M.L r k}

def pair₂ (c : WCoord P S) : LocNG.FPair H r :=
  ⟨swapEs P.A (fun a => c.e.symm (S.es a))
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).1
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).2.1
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).2.2,
    swapEs P.B (fun a => c.e.symm (S.es' a))
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').1
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').2.1
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').2.2⟩

def coord₂ (c : WCoord P S) : Coord (pair₂ c) S :=
  ⟨c.e, c.h_eq, c.f_eq, c.f'_eq, fun a => (c.e.apply_symm_apply _).symm,
    fun a => (c.e.apply_symm_apply _).symm, c.T_eq, c.T'_eq, c.gg_none, c.gg_some⟩

def datEq (c : WCoord P S) : LocNG.Datum P ≃ LocNG.Datum (pair₂ c) where
  toFun d := ⟨d.L, d.L', d.hL, d.hL', d.io, d.io_L⟩
  invFun d := ⟨d.L, d.L', d.hL, d.hL', d.io, d.io_L⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem std_swap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0) (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0) (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0), Fr.T ≠ 0 → ∀ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L → ∃ m ∈ Fr.N, (∀ b, m (Fr.f b) = Fr.f b) ∧ (⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩ : LocNG.FrameD H r).LamStd L = LocNG.img m (Fr.LamStd L) :=
  _root_.GlobalTheory.SwapStd.lamStd_swap

lemma inv_fix {m : V ≃ₗ[E] V} {x : V} (hx : m x = x) : m⁻¹ x = x := by
  conv_lhs => rw [← hx]
  show (m⁻¹ * m) x = x
  rw [inv_mul_cancel]; rfl

lemma side_iff (hM : M.OK) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) (hT : Fr.T ≠ 0)
    (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L) (f : Fin (r + 1) → V) (Λ : Submodule M.L.O V) :
    (∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = LocNG.img n (Fr.LamStd L)) ↔
      ∃ n ∈ (swapEs Fr es₂ h1 h2 h3).N, f = (fun b => n ((swapEs Fr es₂ h1 h2 h3).f b)) ∧
        Λ = LocNG.img n ((swapEs Fr es₂ h1 h2 h3).LamStd L) := by
  obtain ⟨m, hm, hmf, hmΛ⟩ := std_swap M hM H r Fr es₂ h1 h2 h3 hT L hL
  have e : (swapEs Fr es₂ h1 h2 h3).LamStd L = LocNG.img m (Fr.LamStd L) := hmΛ
  rw [e]
  constructor
  · rintro ⟨n, hn, hf, hΛ⟩
    refine ⟨n * m⁻¹, Fr.N.mul_mem hn (Fr.N.inv_mem hm), ?_, ?_⟩
    · rw [hf]; funext b; show n (Fr.f b) = n (m⁻¹ (Fr.f b)); rw [inv_fix (hmf b)]
    · rw [← img_mul, mul_assoc, inv_mul_cancel, mul_one]; exact hΛ
  · rintro ⟨n, hn, hf, hΛ⟩
    refine ⟨n * m, Fr.N.mul_mem hn hm, ?_, ?_⟩
    · rw [hf]; funext b; show n (Fr.f b) = n (m (Fr.f b)); rw [hmf b]
    · rw [img_mul]; exact hΛ

end

theorem changed_duals : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), ∃ (P₂ : LocNG.FPair H r) (c₂ : Coord P₂ S) (φ : LocNG.Datum P ≃ LocNG.Datum P₂), c₂.e = c.e ∧ P₂.St = P.St ∧ P₂.K0 = P.K0 ∧ P₂.UW0 = P.UW0 ∧ P₂.Hp = P.Hp ∧ (P₂.PrimeTo ↔ P.PrimeTo) ∧ (∀ d, c₂.dat (φ d) = c.dat d) ∧ (∀ d t, LocNG.IsTermOver P d t ↔ LocNG.IsTermOver P₂ (φ d) t) ∧ (∀ d t, LocNG.IsTermOver P d t → LocNG.om P₂ t = LocNG.om P t) ∧ ∀ g d d', LocNG.Datum.Moves g d d' ↔ LocNG.Datum.Moves g (φ d) (φ d') := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have hTA : P.A.T ≠ 0 := by rw [← c.T_eq]; exact S.T.ne_zero
  have hTB : P.B.T ≠ 0 := by rw [← c.T'_eq]; exact S.T'.ne_zero
  have pA := pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso
  have pB := pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso'
  have kA : ∀ n ∈ P.A.N, ∀ b a, H.h (n ((pair₂ c).A.f b)) ((pair₂ c).A.es a) = H.h (n (P.A.f b)) (P.A.es a) :=
    fun n hn b a => pair_eq hM P.A _ pA.1 pA.2.1 pA.2.2 hTA hn b a
  have kB : ∀ n ∈ P.B.N, ∀ b a, H.h (n ((pair₂ c).B.f b)) ((pair₂ c).B.es a) = H.h (n (P.B.f b)) (P.B.es a) :=
    fun n hn b a => pair_eq hM P.B _ pB.1 pB.2.1 pB.2.2 hTB hn b a
  refine ⟨pair₂ c, coord₂ c, datEq c, rfl, rfl, ?_, rfl, rfl, Iff.rfl, fun d => rfl, ?_, ?_, fun g d d' => Iff.rfl⟩
  · unfold LocNG.FPair.K0
    congr 1
    ext s
    constructor
    · rintro ⟨hs, h⟩
      have hs' := Subgroup.mem_inf.mp hs
      refine ⟨hs, fun a b => ?_⟩
      rw [← kA s hs'.1 b a, ← kB s hs'.2 b a]
      exact h a b
    · rintro ⟨hs, h⟩
      have hs' := Subgroup.mem_inf.mp hs
      refine ⟨hs, fun a b => ?_⟩
      rw [kA s hs'.1 b a, kB s hs'.2 b a]
      exact h a b
  · intro d t
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (side_iff hM P.A _ pA.1 pA.2.1 pA.2.2 hTA d.L d.hL t.f t.abelian₂)
        (and_congr (side_iff hM P.B _ pB.1 pB.2.1 pB.2.2 hTB d.L' d.hL' t.f' t.abelian₂) Iff.rfl)))
  · rintro d t ⟨-, -, ⟨n, hn, hf, -⟩, ⟨n', hn', hf', -⟩, -⟩
    have e1 : (pair₂ c).A.coefSum t.f = P.A.coefSum t.f := by
      unfold LocNG.FrameD.coefSum; rw [hf]
      exact Finset.sum_congr rfl fun a _ => kA n hn a.succ a
    have e2 : (pair₂ c).B.coefSum t.f' = P.B.coefSum t.f' := by
      unfold LocNG.FrameD.coefSum; rw [hf']
      exact Finset.sum_congr rfl fun a _ => kB n' hn' a.succ a
    unfold LocNG.om LocNG.FrameD.psiOf
    rw [e1, e2]

end GlobalTheory.HL.ToC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptotic
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric

noncomputable section

namespace GlobalTheory.GaugeSubLoc

variable {n : ℕ} {ε : Fin n → Bool}

theorem eventually_bounds {S : Set (Formalism.REAL.UJ ε)} {d : ℕ} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) {θ : ℝ} (hθ : 1 < θ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ ρ} ≤
        ENNReal.ofReal (θ * ρ ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∧
      ENNReal.ofReal (ρ ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
        ENNReal.ofReal θ * μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ ρ} := by
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have h0 : ω ≠ 0 := (measure_ball_pos _ 0 one_pos).ne'
  have ht : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hθ' : 1 < ENNReal.ofReal θ := by simpa using hθ
  have h1 : ω < ENNReal.ofReal θ * ω := by
    conv_lhs => rw [← one_mul ω]
    exact ENNReal.mul_lt_mul_left h0 ht hθ'
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal θ) hμ.2.2 (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [hμ.2.2.eventually (gt_mem_nhds h1), h2.eventually (lt_mem_nhds h1),
    self_mem_nhdsWithin] with ρ a1 a2 a3
  have hρ : (0 : ℝ) < ρ := a3
  have hp : ENNReal.ofReal (ρ ^ d) ≠ 0 := by simpa using pow_pos hρ d
  constructor
  · rw [ENNReal.div_lt_iff (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)] at a1
    rw [ENNReal.ofReal_mul (by linarith), mul_right_comm]
    exact a1.le
  · rw [← mul_div_assoc, ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)] at a2
    rw [mul_comm]
    exact a2.le

open scoped Matrix.Norms.Frobenius in
theorem norm_mul_bounds {θ : ℝ} (hθ : 1 < θ) (g Z : Matrix (Fin n) (Fin n) ℂ)
    (hg : ‖g - 1‖ < 1 - θ⁻¹) : ‖g * Z‖ ≤ θ * ‖Z‖ ∧ ‖Z‖ ≤ θ * ‖g * Z‖ := by
  have h1 : ‖g * Z - Z‖ ≤ (1 - θ⁻¹) * ‖Z‖ := by
    have : g * Z - Z = (g - 1) * Z := by rw [Matrix.sub_mul, Matrix.one_mul]
    rw [this]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hg.le (norm_nonneg _))
  have h2 := abs_le.1 ((abs_norm_sub_norm_le (g * Z) Z).trans h1)
  have h3 : θ⁻¹ * θ = 1 := inv_mul_cancel₀ (by linarith)
  have h4 : 0 < θ⁻¹ := inv_pos.2 (by linarith)
  have h5 := norm_nonneg Z
  have h6 : 2 - θ⁻¹ ≤ θ := by nlinarith [sq_nonneg (θ - 1)]
  constructor
  · nlinarith
  · have : θ⁻¹ * ‖Z‖ ≤ ‖g * Z‖ := by linarith
    calc ‖Z‖ = θ * (θ⁻¹ * ‖Z‖) := by rw [← mul_assoc, mul_comm θ, h3, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by linarith)

open scoped Matrix.Norms.Frobenius in
theorem density_bounds {S : Set (Formalism.REAL.UJ ε)} {d : ℕ} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) (ψ : Formalism.REAL.UJ ε → EuclideanSpace ℝ (Fin d)) (hψ : Continuous ψ)
    {s : ℝ} (hs : 0 < s)
    (h2 : ∀ g h : Formalism.REAL.UJ ε, g ∈ S → h ∈ S → ‖uMat g - 1‖ < s → ‖uMat h - 1‖ < s →
      ‖uMat g - uMat h‖ ≤ 2 * ‖ψ g - ψ h‖)
    (hlip : ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ g h : Formalism.REAL.UJ ε, g ∈ S → h ∈ S →
      ‖uMat g - 1‖ < δ → ‖uMat h - 1‖ < δ →
      ‖ψ g - ψ h‖ ≤ ‖uMat g - uMat h‖ ∧ ‖uMat g - uMat h‖ ≤ κ * ‖ψ g - ψ h‖)
    (hsurj : ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ →
      ∃ g ∈ S, ‖uMat g - 1‖ < δ ∧ ψ g = x)
    (κ : ℝ) (hκ : 1 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ → ∀ᶠ r : ℝ in 𝓝[>] 0,
      (μ.restrict {g | ‖uMat g - 1‖ < s}).map ψ (closedBall x r) ≤
        ENNReal.ofReal κ * volume (closedBall x r) ∧
      volume (closedBall x r) ≤
        ENNReal.ofReal κ * (μ.restrict {g | ‖uMat g - 1‖ < s}).map ψ (closedBall x r) := by
  obtain ⟨θ, hθκ, hθ⟩ : ∃ θ : ℝ, θ ^ (2 * d + 1) < κ ∧ 1 < θ := by
    have : Tendsto (fun θ : ℝ => θ ^ (2 * d + 1)) (𝓝[>] 1) (𝓝 1) := by
      have : ContinuousAt (fun θ : ℝ => θ ^ (2 * d + 1)) 1 := by fun_prop
      simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    exact ((this.eventually (gt_mem_nhds hκ)).and self_mem_nhdsWithin).exists
  have hθ0 : 0 < θ := by linarith
  obtain ⟨δ₁, hδ₁, hl⟩ := hlip θ hθ
  have hη : 0 < 1 - θ⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hθ)
  obtain ⟨ρ, hρ, hsu⟩ := hsurj (min (min δ₁ s) (1 - θ⁻¹)) (lt_min (lt_min hδ₁ hs) hη)
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨g, hgS, hg, rfl⟩ := hsu x hx
  rw [lt_min_iff] at hg
  obtain ⟨hg1, hg3⟩ := hg
  have hgs : ‖uMat g - 1‖ < s := hg1.trans_le (min_le_right _ _)
  have hgδ : ‖uMat g - 1‖ < δ₁ := hg1.trans_le (min_le_left _ _)
  have hae : ∀ᵐ h ∂μ, h ∈ S := hμ.1
  have htr : ∀ t : ℝ, μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ t} =
      μ {k | Real.sqrt (Formalism.REAL.hs (uMat k - 1)) ≤ t} := by
    intro t
    conv_lhs => rw [← hμ.2.1 g hgS]
    rw [(measurableEmbedding_mulLeft g).map_apply]
    congr 1
    ext k
    simp [GlobalTheory.GaugeConst.sqrt_hs]
  have hZ : ∀ h : Formalism.REAL.UJ ε, uMat g * (uMat (g⁻¹ * h) - 1) = uMat h - uMat g := by
    intro h
    rw [Matrix.mul_sub, ← uMat_mul, mul_inv_cancel_left, Matrix.mul_one]
  have htri : ∀ h : Formalism.REAL.UJ ε, ‖uMat h - 1‖ ≤ ‖uMat h - uMat g‖ + ‖uMat g - 1‖ := fun h =>
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  filter_upwards [(GlobalTheory.GaugeConst.tendsto_mul_nhdsGT (pow_pos hθ0 2)).eventually (eventually_bounds hμ hθ),
    (GlobalTheory.GaugeConst.tendsto_mul_nhdsGT (inv_pos.2 hθ0)).eventually (eventually_bounds hμ hθ),
    Ioo_mem_nhdsGT (half_pos (sub_pos.2 hg1))] with r a1 a2 a3
  obtain ⟨hr, hr'⟩ := a3
  have hm1 := min_le_left δ₁ s
  have hm2 := min_le_right δ₁ s
  rw [Measure.map_apply hψ.measurable measurableSet_closedBall,
    Measure.restrict_apply (hψ.measurable measurableSet_closedBall),
    Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin]
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  constructor
  · have hsub : μ (ψ ⁻¹' closedBall (ψ g) r ∩ {g | ‖uMat g - 1‖ < s}) ≤
        μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ θ ^ 2 * r} := by
      refine measure_mono_ae ?_
      filter_upwards [hae] with h hS hh
      obtain ⟨b1, b2⟩ := hh
      have b1' : ‖ψ h - ψ g‖ ≤ r := mem_closedBall_iff_norm.1 b1
      have b3 := h2 h g hS hgS b2 hgs
      have b4 := (hl h g hS hgS (by linarith [htri h]) hgδ).2
      have b5 := (norm_mul_bounds hθ (uMat g) (uMat (g⁻¹ * h) - 1) hg3).2
      rw [hZ] at b5
      change ‖uMat (g⁻¹ * h) - 1‖ ≤ θ ^ 2 * r
      calc _ ≤ θ * (θ * r) := b5.trans (mul_le_mul_of_nonneg_left
            (b4.trans (mul_le_mul_of_nonneg_left b1' hθ0.le)) hθ0.le)
        _ = _ := by ring
    rw [htr] at hsub
    refine (hsub.trans a1.1).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    calc θ * (θ ^ 2 * r) ^ d = θ ^ (2 * d + 1) * r ^ d := by ring
      _ ≤ _ := by gcongr
  · have hsub : μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ θ⁻¹ * r} ≤
        μ (ψ ⁻¹' closedBall (ψ g) r ∩ {g | ‖uMat g - 1‖ < s}) := by
      refine measure_mono_ae ?_
      filter_upwards [hae] with h hS hh
      have hh' : ‖uMat (g⁻¹ * h) - 1‖ ≤ θ⁻¹ * r := hh
      have b5 := (norm_mul_bounds hθ (uMat g) (uMat (g⁻¹ * h) - 1) hg3).1
      rw [hZ] at b5
      have b6 : ‖uMat h - uMat g‖ ≤ r := by
        refine b5.trans ((mul_le_mul_of_nonneg_left hh' hθ0.le).trans_eq ?_)
        field_simp
      have b4 := (hl h g hS hgS (by linarith [htri h]) hgδ).1
      exact ⟨mem_closedBall_iff_norm.2 (b4.trans b6), show ‖uMat h - 1‖ < s by linarith [htri h]⟩
    rw [htr] at hsub
    have e : ENNReal.ofReal (r ^ d) = ENNReal.ofReal (θ ^ d) * ENNReal.ofReal ((θ⁻¹ * r) ^ d) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel_left₀ hθ0.ne']
    rw [e, mul_assoc]
    refine (mul_le_mul_right a2.2 _).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    gcongr
    calc θ ^ d * θ = θ ^ (d + 1) := by ring
      _ ≤ θ ^ (2 * d + 1) := pow_le_pow_right₀ hθ.le (by omega)
      _ ≤ _ := hθκ.le


open scoped Matrix.Norms.Frobenius in
theorem gauge_local_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub {g | uMat g - 1 ∈ A} d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ (∀ μ', IsGaugeSub {g | uMat g - 1 ∈ A} d μ' → μ' = μ) ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ r₀ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | Formalism.REAL.hs (uMat g - 1) < r₁}, φ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re / r) ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t, φ t)) := by
  intro n ε A d E hA hE hV μ hμ
  obtain ⟨a1, a2, a3⟩ := _root_.GlobalTheory.GaugeSubHaar.isGaugeSub_haar n ε (algSub ε A hA) (isClosed_algSub A hA) d μ hμ
  refine ⟨a1, a2, a3, ?_⟩
  have hlip := GlobalTheory.T.unitarySubgroupChart_almost_isometric_near_one n ε A d E hA hE hV
  have hsurj := GlobalTheory.T.unitarySubgroupChart_surjective_near_origin n ε A d E hA hE hV
  simp only [GlobalTheory.GaugeConst.sqrt_hs] at hlip hsurj
  set ψ : Formalism.REAL.UJ ε → EuclideanSpace ℝ (Fin d) :=
    fun g => WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) with hψdef
  have hψ : Continuous ψ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => Complex.continuous_re.comp ?_)
    exact (((GlobalTheory.GaugeConst.continuous_uMat ε).sub continuous_const).matrix_mul
      continuous_const).matrix_trace
  obtain ⟨δ, hδ, h2⟩ := hlip 2 one_lt_two
  obtain ⟨s₀, ⟨hs1, -⟩, hs2, hs3⟩ :=
    ((eventually_bounds hμ one_lt_two).and (Ioo_mem_nhdsGT hδ)).exists
  refine ⟨s₀ ^ 2, by positivity, fun r₁ hr₁ hr₁' φ hφ hφc => ?_⟩
  have hs : 0 < Real.sqrt r₁ := Real.sqrt_pos.2 hr₁
  have hs' : Real.sqrt r₁ ≤ s₀ := Real.sqrt_le_iff.2 ⟨hs2.le, hr₁'⟩
  have hset : {g : Formalism.REAL.UJ ε | Formalism.REAL.hs (uMat g - 1) < r₁} =
      {g | ‖uMat g - 1‖ < Real.sqrt r₁} := by
    ext g
    simp only [Set.mem_ofPred_eq, ← GlobalTheory.GaugeConst.sqrt_hs]
    exact (Real.sqrt_lt_sqrt_iff_of_pos hr₁).symm
  rw [hset]
  have hfin : IsFiniteMeasure (μ.restrict {g | ‖uMat g - 1‖ < Real.sqrt r₁}) := by
    refine isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top ?_ (le_trans (measure_mono ?_) hs1))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · intro g hg
      simp only [Set.mem_ofPred_eq, GlobalTheory.GaugeConst.sqrt_hs] at hg ⊢
      linarith
  have hd := density_bounds hμ ψ hψ hs
    (fun g h hg hh b1 b2 => (h2 g h hg hh (by linarith) (by linarith)).2) hlip hsurj
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hΦ : Continuous (fun x : EuclideanSpace ℝ (Fin d) => φ (e x)) := hφ.comp e.continuous
  have hv := _root_.GlobalTheory.tendsto_rescaled_integral_of_density_one d _ inferInstance hd (fun x => φ (e x)) hΦ
    (hφc.comp_homeomorph e.toHomeomorph)
  have hI : ∫ x : EuclideanSpace ℝ (Fin d), φ (e x) = ∫ t, φ t :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp' φ
  rw [hI] at hv
  refine hv.congr fun r => ?_
  rw [integral_map (f := fun x => φ (e (r⁻¹ • x))) hψ.aemeasurable (hΦ.comp (continuous_const_smul r⁻¹)).aestronglyMeasurable]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  refine congrArg φ (funext fun i => ?_)
  simp [e, hψdef, div_eq_inv_mul]

end GlobalTheory.GaugeSubLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianRapidDecay
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussDecay

theorem isCMFam_of_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : GlobalTheory.Mem.Vol.IsCMFam φ := by
  obtain ⟨hF, hE, h2, -⟩ := h
  unfold GlobalTheory.Mem.Vol.IsCMFam
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · have key : ∀ v, (InfinitePlace.mk (φ v)).comap (algebraMap F E) = v := by
      intro v
      rw [InfinitePlace.comap_mk, show (φ v).comp (algebraMap F E) = v.embedding from RingHom.ext (hφ v),
        InfinitePlace.mk_embedding]
    intro v w hvw
    rw [← key v, ← key w]
    exact congrArg (fun x : InfinitePlace E => x.comap (algebraMap F E)) hvw
  · have a1 := IsTotallyComplex.finrank E
    have a2 := IsTotallyReal.finrank F
    have a3 := Module.finrank_mul_finrank ℚ F E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [h2] at a3
    omega

end GlobalTheory.GaussDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizer
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.StabSet

open GlobalTheory.Mass Formalism.HermitianLatticesTheory GlobalTheory.Mass.RowMean

theorem main : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  intro D X u M₀ ψ hψ
  have hU : ∀ v, v ∈ GlobalTheory.RowsOrb.Ub X u ↔ GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) v = 0 :=
    fun v => GlobalTheory.RowsOrb.mem_Ub X u v
  have hπ : ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)),
      GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) =
        resZ (GlobalTheory.RowsOrb.hb X) hU g • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L :=
    fun g L => StabSplit.latIn_smul (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Ub X u) g.1 (smul_compl _ hU g) L
  have hY : Stable (isom (GlobalTheory.RowsOrb.hU X u)) (genus (GlobalTheory.RowsOrb.hU X u) M₀) :=
    Transp.genus_stable (R := 𝓞 D.host.E) (K := D.host.E) (V := GlobalTheory.RowsOrb.Ub X u) (h := GlobalTheory.RowsOrb.hU X u) M₀
  refine ⟨?_, fun g L => by rw [hπ]; exact hψ _ _⟩
  rintro g L ⟨h1, h2, h3, h4⟩
  have H := Formalism.HermitianLatticesTheory.isomAct (𝓞 D.host.E) D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) g.1.1 g.1.2 L
  refine ⟨H.2.2.2.2.2 h1, H.2.2.2.1.2 h2, fun t => ?_, ?_⟩
  · have hg : g.1.1 (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u := g.2
    have hs : g.1.1.symm (t • GlobalTheory.RowsOrb.zb X u) = t • GlobalTheory.RowsOrb.zb X u :=
      g.1.1.symm_apply_eq.2 (by rw [map_smul, hg])
    change t • GlobalTheory.RowsOrb.zb X u ∈ Formalism.HermitianLatticesTheory.gmap (g.1.1 : GlobalTheory.RowsOrb.Wb X ≃ₗ[D.host.E] GlobalTheory.RowsOrb.Wb X) L ↔ _
    rw [isomAct_mem_gmap, hs, h3]
  · let s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u) := resZ (GlobalTheory.RowsOrb.hb X) hU g
    have k : s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀ := hY s _ h4
    have e : GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) = s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L := hπ g L
    exact Eq.mpr (congrArg (fun N => N ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀) e) k

end GlobalTheory.RowsOrb.StabSet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegersStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V), Submodule.IsLattice K Λ → ∀ W : Submodule K V, Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.isLattice_comap_subtype_ringOfIntegers | exact GlobalTheory.isLattice_comap_subtype_ringOfIntegers | (intros; apply GlobalTheory.isLattice_comap_subtype_ringOfIntegers <;> assumption)
end

