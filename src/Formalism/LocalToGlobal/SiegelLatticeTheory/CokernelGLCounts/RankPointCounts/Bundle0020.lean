module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
section
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SchurCoreA : Prop :=
  ∀ (k : ℕ) (ι : Type) [Fintype ι] (V V' : ι → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    [∀ i, NormedAddCommGroup (V' i)] [∀ i, InnerProductSpace ℂ (V' i)] [∀ i, FiniteDimensional ℂ (V' i)]
    (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
    (tens : (∀ i, V i) → W) (tens' : (∀ i, V' i) → W'),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    (∀ x y, ⟪tens' x, tens' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Submodule.span ℂ (Set.range tens') = ⊤ →
    ∀ (π : ∀ i, Matrix (Fin k) (Fin k) ℂ → (V i →L[ℂ] V i)) (π' : ∀ i, Matrix (Fin k) (Fin k) ℂ → (V' i →L[ℂ] V' i))
      (lam lam' : ι → Fin k → ℝ),
    (∀ i, IsHCTypeU k (lam i) (π i)) → (∀ i, IsHCTypeU k (lam' i) (π' i)) →
    ∀ i₀ : ι, lam i₀ ≠ lam' i₀ →
    ∀ (C : ι → Matrix (Fin k) (Fin k) ℂ), (∀ i, C i ∈ UJset (allPos k)) →
    ∀ P : W' →L[ℂ] W,
      (∀ M : ι → Matrix (Fin k) (Fin k) ℂ, (∀ i, M i ∈ UJset (allPos k)) →
        ∃ (A : W →L[ℂ] W) (B : W' →L[ℂ] W'),
          (∀ x, A (tens x) = tens (fun i => π i (M i) (x i))) ∧
          (∀ x, B (tens' x) = tens' (fun i => π' i (C i * M i * (C i)ᴴ) (x i))) ∧
          A.comp P = P.comp B) →
      P = 0

def LeviTens : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∀ h ∈ X.SinfU u, ∀ x : ∀ v, X.Vloc u v,
    X.piU u h (X.tensU u x) = X.tensU u (fun v => X.piLoc u v (matW X.B.I (X.wfr u v) v h) (x v))

def WfrSpan : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → ℂ),
    (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) y = 0 ∧ hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) y = 0) →
    hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) y = 0 →
    y = ∑ b, hJ (X.B.I.ε v) (X.wfr u v b) y • X.wfr u v b


variable {D : D7} in
def spanAt (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (U : Submodule D.host.E (VS D).V) :
    Submodule ℂ (Fin X.B.I.n → ℂ) :=
  Submodule.span ℂ ((fun p => rv X.B.I v (X.crd p)) '' (U : Set (VS D).V))

def CplxNF : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∀ v : InfinitePlace X.B.I.F,
      (∀ y : Fin X.B.I.n → ℂ, (∀ p ∈ (lf D (X.Fu u)).fl.Xplus, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        ∃ x ∈ spanAt X v (lf D (X.Fu u)).fl.X,
          ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (y - x) = 0) ∧
      (∀ y : Fin X.B.I.n → ℂ, (∀ p ∈ (frq X q).fl.Xplus, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        ∃ x ∈ spanAt X v (frq X q).fl.X,
          ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (y - x) = 0) ∧
      (∀ y ∈ spanAt X v (lf D (X.Fu u)).fl.X, (∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        y ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl))

def GeomB : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∃ C : InfinitePlace X.B.I.F → Matrix (Fin D.R.k) (Fin D.R.k) ℂ, (∀ v, C v ∈ UJset (allPos D.R.k)) ∧
      ∀ M : InfinitePlace X.B.I.F → Matrix (Fin D.R.k) (Fin D.R.k) ℂ, (∀ v, M v ∈ UJset (allPos D.R.k)) →
        ∃ h ∈ pointwiseStabilizerInfinite X q,
          (∀ x, X.piU u h (X.tensU u x) = X.tensU u (fun v => X.piLoc u v (M v) (x v))) ∧
          (∀ x, X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1) (X.tensU u' x) =
            X.tensU u' (fun v => X.piLoc u' v (C v * M v * (C v)ᴴ) (x v)))

end PI.SchurPlaces
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData

set_option linter.dupNamespace false

namespace Formalism.L2.SG.NGCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Ctx (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) :
    Prop :=
  Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 ∧ Formalism.MainNotions.S.Cnt.Stand D u u' ∧ ConcTie X Y

def MassDataAdmissible {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) {P : Type} [Fintype P] (B : S3.MassData P)
    (Irat Ire : ℝ) : Prop :=
  (Y.tO u u').Gam1 = B.Gam1 ∧ B.d * B.d' / B.Dstar = ddC X Y u u' ∧ PN.NormInputs B ∧
    PN.FrameInputs B (2 * D.host.v) (X.B.g : ℝ) D.R.rS D.R.k D.R.f Irat Ire

def SizesRec (Cg CT : ℝ) (r f : ℕ) (b rd g TT : ℝ) : Prop :=
  1 ≤ f ∧ 16 ≤ b ∧ 0 < rd ∧ rd ≤ b ∧ 1 ≤ g ∧ g ≤ b ^ Cg ∧ 0 < TT ∧ TT ≤ b ^ (2 * CT * ((2 * r + 2 : ℕ) : ℝ))

theorem ngSizes_of {Cg CT CSt : ℝ} {r f : ℕ} {b rd g TT cSt e1 : ℝ} (h : SizesRec Cg CT r f b rd g TT)
    (h1 : 0 ≤ cSt) (h2 : cSt ≤ b ^ (CSt * ((2 * r + 2 : ℕ) : ℝ) ^ 3 * f)) (h3 : 0 ≤ e1) (h4 : e1 ≤ 2) :
    PN.NGSizes Cg CT CSt r f b rd g TT cSt e1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, h1, h2, h3, h4⟩

def StepSizes : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ Cgs CTs : ℝ, 0 ≤ Cgs ∧ 0 ≤ CTs ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      SizesRec Cgs CTs D.R.rS D.R.f large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ))

def StepClass : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
      PN.ClassInput (Y.tO u u') (NOf2 Y u u' νL νB ng)

def StepNormals : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.NormalsInput (Y.tO u u') (NOf2 Y u u' νL νB ng)
          ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
            (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f))

def StepPoints : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.PointsInput (Y.tO u u') (NOf2 Y u u' νL νB ng)

def StepHeight : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.HeightInput (Y.tO u u') (NOf2 Y u u' νL νB ng) ((X.B.g : ℝ) ^ D.R.f)

def StepAnalytic : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∀ A : ℕ, ∃ CB CSt : ℝ, 0 ≤ CB ∧ 0 ≤ CSt ∧
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (P : Type) [Fintype P] (B : S3.MassData P) (Irat Ire : ℝ), MassDataAdmissible X Y u u' B Irat Ire →
      ∃ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (cSt e1 : ℝ),
        Formalism.L2.SG.RealObj.NuQOK X u u' νL ∧ Formalism.L2.SG.RealObj.NuQOK X u u' νB ∧
        0 ≤ cSt ∧ cSt ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
        AmpVanish Y u u' νL ∧
        PN.LocalInput (Y.tO u u') (NOf2 Y u u' νL νB ng) C1 C0n D.R.k ∧
        PN.GenMassInput (Y.tO u u') (NOf2 Y u u' νL νB ng) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
        PN.MeasureInput (Y.tO u u') (NOf2 Y u u' νL νB ng) cSt ∧
        PN.PointSumInput (Y.tO u u') (NOf2 Y u u' νL νB ng) (A * (D.R.rS + 1) ^ 2)
          (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

theorem sizes_of_hypotheses : StepSizes := by
  intro Cg cb Cw cT CT C0
  refine ⟨max (2 * Cg) 0, max CT 0, le_max_right _ _, le_max_right _ _, 0, 2,
    fun C' Cl _ hCl D large₂ X Y u u' hc => ?_⟩
  obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
  unfold Formalism.MainNotions.S.StandingHypotheses at hH
  dsimp only at hH
  obtain ⟨-, -, h3, h4, -, -, -, -, -, -, h11, h12, h13, h14, h15, h16, -, -, h19, -, -, -, h23, -, h25⟩ := hH
  have hm2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  have hmr : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ) := by
    congr 1; simp only [Formalism.BasicNotions.Ranks.rS]; omega
  have hf1 : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hk16 : (16 : ℝ) ≤ D.R.k := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    have : 16 ≤ D.R.k := by omega
    exact_mod_cast this
  have hbpos : 0 < large₂.sc.b := Real.exp_pos _

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨X.pl (Classical.arbitrary _)⟩
  have hb1 := (h16 τ 1 le_rfl (by omega)).1
  have hb2 := (h16 τ 1 le_rfl (by omega)).2
  have hkCl : (D.R.k : ℝ) ^ (2 : ℝ) ≤ (D.R.k : ℝ) ^ Cl :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hCl
  have hb256 : (256 : ℝ) ≤ large₂.sc.b ^ 2 := by
    have e1 : (D.R.k : ℝ) ^ (2 : ℝ) = (D.R.k : ℝ) ^ 2 := Real.rpow_two _
    have e2 : large₂.sc.b ^ (2 : ℝ) = large₂.sc.b ^ 2 := Real.rpow_two _
    have h256 : (D.R.k : ℝ) ^ 2 ≥ 256 := by nlinarith
    have h5 := le_trans (le_max_left _ _) hb1
    rw [e1] at hkCl
    rw [e2] at hb2
    linarith
  have hb16 : (16 : ℝ) ≤ large₂.sc.b := by nlinarith
  have hb1' : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hv : 2 * D.host.v = D.host.rdE := by
    simp only [Formalism.BasicNotions.Host.v]; ring
  have hrd_pos : 0 < D.host.rdE := by rw [← hv]; linarith
  have hL : large₂.sc.L = Real.log large₂.sc.b := by simp [Formalism.BasicNotions.Scale.b]
  have hLpos : 0 < large₂.sc.L := by rw [hL]; exact Real.log_pos (by linarith)
  have hrd : D.host.rdE ≤ large₂.sc.b := by
    have : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine h11.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [hL] at this
    exact (Real.log_le_log_iff hrd_pos hbpos).1 this
  have hkb : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    apply one_le_pow₀; nlinarith
  have hg0 : (1 : ℝ) ≤ (D.host.g 0 : ℝ) := hkb.trans h12
  have hg1 : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := hkb.trans h14
  have hgX : (X.B.g : ℝ) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by
    rw [X.g_eq]; push_cast; ring
  obtain ⟨hT1, hT2⟩ := h23 u
  obtain ⟨hT1', hT2'⟩ := h23 u'
  have hTpos : 0 < ((Lat.Tu D u : ℕ) : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hbpos _) hT1
  have hTpos' : 0 < ((Lat.Tu D u' : ℕ) : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hbpos _) hT1'
  refine ⟨hf1, hb16, by rw [hv]; exact hrd_pos, by rw [hv]; exact hrd, ?_, ?_, mul_pos hTpos hTpos', ?_⟩
  · rw [hgX]; nlinarith
  · rw [hgX]
    calc (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) ≤ large₂.sc.b ^ Cg * large₂.sc.b ^ Cg :=
          mul_le_mul h13 h15 (by linarith) (Real.rpow_nonneg hbpos.le _)
      _ = large₂.sc.b ^ (2 * Cg) := by rw [← Real.rpow_add hbpos]; ring_nf
      _ ≤ large₂.sc.b ^ max (2 * Cg) 0 := Real.rpow_le_rpow_of_exponent_le hb1' (le_max_left _ _)
  · rw [hmr]
    calc ((Lat.Tu D u : ℕ) : ℝ) * ((Lat.Tu D u' : ℕ) : ℝ) ≤ large₂.sc.b ^ (CT * D.R.m) * large₂.sc.b ^ (CT * D.R.m) :=
          mul_le_mul hT2 hT2' hTpos'.le (Real.rpow_nonneg hbpos.le _)
      _ = large₂.sc.b ^ (2 * CT * D.R.m) := by rw [← Real.rpow_add hbpos]; ring_nf
      _ ≤ large₂.sc.b ^ (2 * max CT 0 * D.R.m) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1'
          have : (0 : ℝ) ≤ D.R.m := by positivity
          nlinarith [le_max_left CT 0]

def CorankOneEquivalence : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    (∀ t ∈ (Y.tO u u').ngSet, (Y.tO u u').s0 t t = 1) ∧
    (∀ t ∈ (Y.tO u u').ngSet, ∀ t' ∈ (Y.tO u u').ngSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      (Y.tO u u').s0 t t' = 1 → (Y.tO u u').s0 t' t = 1) ∧
    (∀ t ∈ (Y.tO u u').ngSet, ∀ t' ∈ (Y.tO u u').ngSet, ∀ t'' ∈ (Y.tO u u').ngSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' →
      (Y.tO u u').s0 t t' = 1 → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').s0 t t'' = 1)

theorem stepClass_of_equiv (h : CorankOneEquivalence) : StepClass := by
  intro D X Y u u' hct νL νB ng
  obtain ⟨hr, hs, htr⟩ := h D X Y u u' hct
  intro t ht t' ht'
  show ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ (Y.tO u u').s0 t t' = 1) ↔ clsOf Y u u' t = clsOf Y u u' t'
  constructor
  · rintro ⟨hrow, hst⟩
    ext t''
    simp only [clsOf, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2.trans hrow, htr t' ht' t ht t'' h1 hrow.symm h2.symm (hs t ht t' ht' hrow hst) h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2.trans hrow.symm, htr t ht t' ht' t'' h1 hrow h2.symm hst h3⟩
  · intro he
    have hmem : t' ∈ clsOf Y u u' t' := ⟨ht', rfl, hr t' ht'⟩
    rw [← he] at hmem
    exact ⟨hmem.2.1.symm, hmem.2.2⟩

def StepNormOne : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS),
        PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ∧ 1 ≤ NDPt D.host.rdE γ

theorem stepHeight_of_normOne (h : StepNormOne) : StepHeight := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C2, hh⟩ := h Cg cb Cw cT CT C0
  refine ⟨C1, C2, fun C' Cl hC' hCl D large₂ X Y u u' hctx νL νB ng γ hγ => ?_⟩
  obtain ⟨hNG, hND⟩ := hh C' Cl hC' hCl D large₂ X Y u u' hctx νL νB ng γ hγ
  refine ⟨hNG, hND, ?_⟩
  dsimp only [NOf2]
  unfold HPt
  have hpos : 0 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ * NDPt D.host.rdE γ :=
    mul_nonneg (by linarith) (by linarith)
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hpos
  rcases Nat.eq_zero_or_pos X.B.g with hg | hg
  · have ha : 0 < (2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E) :=
      Nat.mul_pos (by omega) Fintype.card_pos
    simp [hg, zero_pow ha.ne']
    try positivity
  · have hg1 : (1 : ℝ) ≤ X.B.g := by exact_mod_cast hg
    exact (inv_le_one_of_one_le₀ (one_le_pow₀ hg1)).trans (one_le_pow₀ hg1)

end Formalism.L2.SG.NGCut
end
end

