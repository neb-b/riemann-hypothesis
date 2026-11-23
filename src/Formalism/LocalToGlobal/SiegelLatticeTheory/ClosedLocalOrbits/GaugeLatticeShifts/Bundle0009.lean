module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ColPhaseCut
section
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.NormCut

section Phase

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

def scOf {u : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u rs) (ρ : c.Cl) :
    Iof TR :=
  levi TR (((c.h (c.base (c.lamOf ρ)) : X.B.I.Gf) * X.xu u)⁻¹ * ((c.h ρ : X.B.I.Gf) * X.xu u))

def Aset {u : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u rs)
    (q : {Λ // Λ ∈ rs}) : Set (Iof TR) :=
  {x | ∃ γ : Formalism.L2.SG.PoincareInHH.PoincareSetting.Gam X u,
    ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ * (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u γ : X.B.I.Gf) *
        ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset ∧
      x = levi TR (((c.h (c.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ *
        (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u γ : X.B.I.Gf) * ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u))}

variable {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0 F0') in
def LeviCols : Prop :=
  ∀ (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl), cs.lamOf ρ = t.lam → cs'.lamOf ρ' = t.lam' →
    levi TR (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) =
      (scOf TR cs ρ)⁻¹ * iotaOf TR cs cs' t * scOf TR cs' ρ'


variable (F0 F0') in
def PhaseAt : Prop :=
  ∀ (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl), cs.lamOf ρ = t.lam → cs'.lamOf ρ' = t.lam' →
    (if kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2 then
      chiL X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) else 0) =
    psiG TR (levi TR (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt))

theorem colPhase_of (hL : LeviCols TR F0 F0' cs cs') (hP : PhaseAt TR F0 F0' cs cs') :
    ColPhase F0 F0' TR cs cs' (scOf TR cs) (scOf TR cs') := by
  intro t ρ ρ' hρ hρ'
  rw [hP t ρ ρ' hρ hρ', hL t ρ ρ' hρ hρ']

end Phase

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR
section
noncomputable section

open MeasureTheory Filter Topology Classical
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def rhoS (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (x : Mt k r) : ℝ≥0∞ :=
  ⨅ (Y : Formalism.MainNotions.S.lieE S)
    (_ : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x),
    (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)

def Qf (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : ℝ≥0∞ :=
  rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + rhoS k r (Formalism.FourierDecayAlt.B2.UWb k r) m ^ 2 +
    rhoS k r (Nset k r) n' ^ 2

def Psi (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : Mt k r :=
  fun i j => (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) i j

def Sandwich : Prop :=
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ Formalism.FourierDecayAlt.B2.UWb k r →
      Matrix.of n' ∈ Nset k r →
      (Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)) ∧
      (Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ)

def Vol (k r : ℕ) (μb : Measure (Mt k r)) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
    ∫⁻ n, ∫⁻ m, ∫⁻ n', (if Qf k r n c m n' < ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0)
      ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1)

def VolLim : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    Tendsto (fun s : ℝ => (Vol k r μb s).toReal / gVol k r s) (𝓝[>] 0) (𝓝 ((2 : ℝ) ^ r)⁻¹)

end Formalism.L2.SG.Pf.BH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGEB
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB

def RhsHaar : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∃ ν : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ν ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂ν = rhs k r μb φ

def RhsWHaar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    ∃ ν : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) ν ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂ν = rhsW k r z z' μW μW' μsec φ

def WbDataEx : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), WbData k r z z' μW μW' a a' μsec

def ExistsGaugeMeasureForEachRank : Prop := ∀ r : ℕ, ∃ μ : Measure (Mt 0 r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb 0 r) μ

end Formalism.L2.SG.Pf.GE
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWb
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.WB

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem wbConst_pos {k : ℕ} {T T' a a' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : 0 < a) (ha' : 0 < a') :
    0 < wbConst k T T' a a' := by
  unfold wbConst
  have h1 : ∀ j, 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU j := fun j => by
    unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
    exact Finset.prod_pos fun i _ => by positivity
  have := h1 k
  have := h1 (k - 1)
  positivity

theorem wbHaar_of (hI : RankGauge) (hS : GaugeShiftW) (hR : RhsWLim) : WbHaar := by
  intro k r z z' hk hz hz' hT hT' μb μW μW' hμb hW hW' a a' ha ha' hma hma' μsec hsec φ hφ
  have D : WbData k r z z' μW μW' a a' μsec := ⟨hk, hz, hz', hT, hT', hW, hW', ha, ha', hma, hma', hsec⟩
  obtain ⟨C, hC, hF⟩ := hI k r z z' μb μW μW' a a' μsec D hμb
  have hlim1 : Tendsto (fun ρ : ℝ => (μb (bBall k r ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1) := hμb.2
  have hlim2 := (hR k r z z' μW μW' a a' μsec D).const_mul (C : ℝ)
  have heq : ∀ᶠ ρ in 𝓝[>] (0:ℝ), (μb (bBall k r ρ)).toReal / bVol k r ρ =
      (C : ℝ) * ((rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    obtain ⟨hm, he⟩ := hS k r z z' μb μW μW' a a' μsec D hμb.1 ρ hρ
    have h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂μb = μb (mBall k r z z' μsec ρ) :=
      lintegral_indicator_one hm
    have h2 := hF _ (measurable_one.indicator hm)
    rw [h1, he] at h2
    rw [h2, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc]
  have hu := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have hw := wbConst_pos (k := k) hT hT' ha ha'
  have hCr : (C : ℝ) = wbConst k (Tz k r z) (Tz k r z') a a' := by
    field_simp at hu
    linarith
  have hCe : (C : ℝ≥0∞) = ENNReal.ofReal (wbConst k (Tz k r z) (Tz k r z') a a') := by
    rw [← hCr, ENNReal.ofReal_coe_nnreal]
  rw [hF φ hφ, hCe]
  rfl

end Formalism.L2.SG.Pf.WB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfC
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

section Quot

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem perp_map (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h21 : ∀ y ∈ X2, e.symm y ∈ X1) {x : V} (hx : x ∈ H.perp X1) : e x ∈ H.perp X2 := by
  intro y hy
  rw [show y = e (e.symm y) from (e.apply_symm_apply y).symm, hiso]
  exact hx _ (h21 y hy)

theorem perp_map_symm (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) {y : V} (hy : y ∈ H.perp X2) : e.symm y ∈ H.perp X1 := by
  intro x hx
  rw [← hiso, e.apply_symm_apply]
  exact hy _ (h12 x hx)

def perpEquiv (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) : ↥(H.perp X1) ≃ₗ[E] ↥(H.perp X2) :=
  e.ofSubmodules (H.perp X1) (H.perp X2) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact perp_map H e hiso X1 X2 h21 hx
    · intro hy
      exact ⟨e.symm y, perp_map_symm H e hiso X1 X2 h12 hy, e.apply_symm_apply y⟩)

def qEquiv (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) :
    (↥(H.perp X1) ⧸ X1.comap (H.perp X1).subtype) ≃ₗ[E] (↥(H.perp X2) ⧸ X2.comap (H.perp X2).subtype) :=
  Submodule.Quotient.equiv _ _ (perpEquiv H e hiso X1 X2 h12 h21) (by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hx⟩, hx1, hxy⟩
      have h' : e x = y := congrArg Subtype.val hxy
      rw [← h']
      exact h12 x hx1
    · intro hy2
      refine ⟨⟨e.symm y, perp_map_symm H e hiso X1 X2 h12 hy⟩, h21 y hy2, ?_⟩
      apply Subtype.ext
      show e (e.symm y) = y
      exact e.apply_symm_apply y)

theorem qEquiv_mk (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) (x : ↥(H.perp X1)) :
    qEquiv H e hiso X1 X2 h12 h21 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (perpEquiv H e hiso X1 X2 h12 h21 x) := rfl

theorem mk_eq_iff (X : Submodule E V) (x y : ↥(H.perp X)) :
    (Submodule.Quotient.mk x : ↥(H.perp X) ⧸ X.comap (H.perp X).subtype) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ X := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]

theorem smul_mk_eq (X : Submodule E V) (c₁ c₂ : E) (x y : ↥(H.perp X)) (h : c₁ • (x : V) - c₂ • (y : V) ∈ X) :
    c₁ • (Submodule.Quotient.mk x : ↥(H.perp X) ⧸ X.comap (H.perp X).subtype) = c₂ • Submodule.Quotient.mk y := by
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, mk_eq_iff]
  simpa using h

theorem iso_span {ι : Type} (w : ι → V) (hw : ∀ i j, H.h (w i) (w j) = 0) :
    ∀ a ∈ Submodule.span E (Set.range w), ∀ b ∈ Submodule.span E (Set.range w), H.h a b = 0 := by
  have hle : Submodule.span E (Set.range w) ≤ H.perp (Submodule.span E (Set.range w)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_perp_span]
    rintro _ ⟨j, rfl⟩
    exact hw i j
  intro a ha b hb
  exact hle ha b hb

end Quot

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

