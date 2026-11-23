module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorBesselExistence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.Fam.RatDec

variable {D : D7}

theorem quad_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (v : Fin n → D.host.E) : star (A *ᵥ v) ⬝ᵥ G *ᵥ (A *ᵥ v) = star v ⬝ᵥ (Aᴴ * G * A) *ᵥ v := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem conj_mul_mul {S S' : HSp D} {a b : ℕ} (P : Matrix (Fin S'.rank) (Fin S.rank) D.host.E)
    (A : Matrix (Fin S.rank) (Fin a) D.host.E) (B : Matrix (Fin S.rank) (Fin b) D.host.E) :
    (P * A)ᴴ * S'.gram * (P * B) = Aᴴ * (Pᴴ * S'.gram * P) * B := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def pullDec {S S' S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Matrix (Fin S'.rank) (Fin S.rank) D.host.E)
    (hP : Pᴴ * S'.gram * P = S.gram) (hr : S.rank = S'.rank) : HypDec S' S₀ ρ where
  e := P * d.e
  e' := P * d.e'
  i₀ := P * d.i₀
  ee := by rw [conj_mul_mul, hP, d.ee]
  e'e' := by rw [conj_mul_mul, hP, d.e'e']
  e'e := by rw [conj_mul_mul, hP, d.e'e]
  iso := by rw [conj_mul_mul, hP, d.iso]
  i₀e := by rw [conj_mul_mul, hP, d.i₀e]
  i₀e' := by rw [conj_mul_mul, hP, d.i₀e']
  rank_add := d.rank_add.trans hr

theorem mat_of_isom (W₁ W₂ : HSp D) (φ : W₁.V ≃ₗ[D.host.E] W₂.V) (hφ : ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y) :
    ∃ P : Matrix (Fin W₂.rank) (Fin W₁.rank) D.host.E, Pᴴ * W₂.gram * P = W₁.gram := by
  refine ⟨Matrix.of fun k j => W₂.frame.equivFun (φ (W₁.frame j)) k, ?_⟩
  ext i j
  have h := GlobalTheory.LandherrSignature.form_eq W₂.hT W₂.frame (W₂.frame.equivFun (φ (W₁.frame i)))
    (W₂.frame.equivFun (φ (W₁.frame j)))
  simp only [LinearEquiv.symm_apply_apply] at h
  rw [hφ] at h
  have hG : (Matrix.of fun a b => W₂.hT (W₂.frame a) (W₂.frame b)) = W₂.gram := rfl
  rw [hG] at h
  rw [show W₁.gram i j = W₁.hT (W₁.frame i) (W₁.frame j) from rfl, h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, mulVec, Matrix.of_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [mul_assoc]
  first | exact Finset.sum_comm | (congr 1; exact Finset.sum_comm)

theorem yc_facts (j : ℕ) (hj : j ≤ D.R.m) :
    (Yc D j).SigOK ∧ (Yc D j).rank = D.R.rankY j ∧ ∀ τ, (Yc D j).sig τ = sigYD D.R j := by
  have hmin : min j D.R.m = j := min_eq_left hj
  refine ⟨D.sp.Y_sig _, ?_, fun τ => ?_⟩
  · show (D.sp.Y (min j D.R.m)).rank = _
    rw [hmin]; exact D.sp.Y_rank j hj
  · show (D.sp.Y (min j D.R.m)).sig τ = _
    rw [hmin]; exact D.Y_sigval j hj τ

theorem bes_to_Yc (j ρ : ℕ) (hj : j ≤ D.R.m) {V : HSp D} (b : BesAt V (D.sp.X j) ρ) (hr : V.rank = D.R.rankY j)
    (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = sigYD D.R j) :
    ∃ b' : BesAt (Yc D j) (D.sp.X j) ρ, star b'.ζ ⬝ᵥ b'.L.gram *ᵥ b'.ζ = star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ := by
  obtain ⟨hYs, hYr, hYsig⟩ := yc_facts (D := D) j hj
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D V (Yc D j) hs hYs (hr.trans hYr.symm)
    (fun τ => (hsig τ).trans (hYsig τ).symm)
  obtain ⟨P, hP⟩ := mat_of_isom V (Yc D j) φ hφ
  exact ⟨⟨b.V₀, b.L, pullDec b.d P hP (hr.trans hYr.symm), b.o, b.ζ, b.line, b.cpt,
    ((GlobalTheory.Unf.VolExist.measures_exist D).2.1 _ _ _ _).some⟩, rfl⟩

theorem jac_to_Yc (j ρ : ℕ) (hj : j ≤ D.R.m) {V : HSp D} (b : JacAt V (D.sp.X j) ρ) (hr : V.rank = D.R.rankY j)
    (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = sigYD D.R j) : Nonempty (JacAt (Yc D j) (D.sp.X j) ρ) := by
  obtain ⟨hYs, hYr, hYsig⟩ := yc_facts (D := D) j hj
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D V (Yc D j) hs hYs (hr.trans hYr.symm)
    (fun τ => (hsig τ).trans (hYsig τ).symm)
  obtain ⟨P, hP⟩ := mat_of_isom V (Yc D j) φ hφ
  exact ⟨⟨pullDec b.d P hP (hr.trans hYr.symm), b.cpt, ((GlobalTheory.Unf.VolExist.measures_exist D).2.1 _ _ _ _).some⟩⟩

def besOf {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : GlobalTheory.Core.Mi.SBes X h u ψ (D.sp.X 0)) : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS :=
  ⟨B.V₀, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vN⟩

def besF (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) :
    ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ
  | 0, ρ, h => cast (congrArg (BesAt (Yc D 0) (D.sp.X 0)) (show D.R.m / 2 - 1 = ρ by omega)) b0
  | j + 1, ρ, h => b' (j + 1) ρ h

theorem besF_zero (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) :
    besF b0 b' 0 D.R.rS h0 = b0 := rfl

theorem besF_norm (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) (c N : D.host.E)
    (h0 : star b0.ζ ⬝ᵥ b0.L.gram *ᵥ b0.ζ = c)
    (h' : ∀ j ρ h, star (b' j ρ h).ζ ⬝ᵥ (b' j ρ h).L.gram *ᵥ (b' j ρ h).ζ * N ^ (j / 2) = c) :
    ∀ j ρ h, star (besF b0 b' j ρ h).ζ ⬝ᵥ (besF b0 b' j ρ h).L.gram *ᵥ (besF b0 b' j ρ h).ζ * N ^ (j / 2) = c := by
  intro j ρ h
  cases j with
  | zero =>
    have hρ : D.R.rS = ρ := by
      show D.R.m / 2 - 1 = ρ
      omega
    subst ρ
    simpa only [besF_zero b0 b' h, Nat.zero_div, pow_zero, mul_one] using! h0
  | succ j => exact h' (j + 1) ρ h

theorem sbes_norm {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : GlobalTheory.Core.Mi.SBes X h u ψ (D.sp.X 0)) (hE : GlobalTheory.Core.Mi.IdE X)
    (hz : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = X.ιE (X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k))) :
    star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(((D.mem u).A.T : ℕ) : D.host.E) := by
  have hw : B.d.i₀ *ᵥ (B.o.iB *ᵥ B.ζ) = GlobalTheory.Core.SBesEx.cY X h (X.zu u) := funext hz
  rw [← B.o.isoB, ← quad_mulVec, ← B.d.iso, ← quad_mulVec, hw, GlobalTheory.Core.SBesEx.cY_isom D X h hE, X.zu_norm]

theorem tau_line {n p : ℕ} (hn : n = 1) (hp : p = 1) (G : Matrix (Fin n) (Fin n) D.host.E)
    (G₀ : Matrix (Fin p) (Fin p) D.host.E) (ζ : Fin n → D.host.E) (ζ₀ : Fin p → D.host.E) (lam c : D.host.E)
    (h₀ : star ζ₀ ⬝ᵥ G₀ *ᵥ ζ₀ ≠ 0)
    (hrel : star lam * lam * (star ζ ⬝ᵥ G *ᵥ ζ) = c * (star ζ₀ ⬝ᵥ G₀ *ᵥ ζ₀)) :
    (Matrix.of fun i k => lam * ζ i / ζ₀ k)ᴴ * (G * Matrix.of fun i k => lam * ζ i / ζ₀ k) = c • G₀ ∧
      (Matrix.of fun i k => lam * ζ i / ζ₀ k) *ᵥ ζ₀ = lam • ζ := by
  subst hn; subst hp
  simp only [dotProduct, mulVec, Fin.sum_univ_one, Pi.star_apply] at h₀ hrel
  have hz : ζ₀ 0 ≠ 0 := fun h => h₀ (by rw [h]; simp)
  have hz' : star (ζ₀ 0) ≠ 0 := star_ne_zero.2 hz
  constructor
  · refine Matrix.ext fun i k => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fin.sum_univ_one, Matrix.smul_apply,
      smul_eq_mul, star_div₀, star_mul', star_inv₀]
    field_simp
    first | linear_combination hrel | (rw [div_eq_iff (mul_ne_zero hz' hz)]; linear_combination hrel)
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
    field_simp


set_option maxHeartbeats 1000000 in
theorem exists_yRat : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ a : XGeo D, IsLineVec a.Lz a.ζ₀ → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → ∃ (y : YRat a) (B : GlobalTheory.Core.Mi.SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) ∧ B.lev = (y.bes 0 D.R.rS h0).lev (a.x 0).vol ∧ B.Adapted (W.S.tr u).wt ∧ GlobalTheory.MiTop.Framed B ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(((D.mem u).A.T : ℕ) : D.host.E) ∧ ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a hLz hT0
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hN : D.host.xi0 * star D.host.xi0 ≠ 0 := mul_ne_zero hxi (star_ne_zero.2 hxi)

  obtain ⟨lam0, hlam0, hB⟩ := GlobalTheory.Core.Mi.exists_sBes_scaled_dual D W.S.X W.Q.instEq u W.Q.Rl.ψ _ (W.S.tr u)
    hP.bot.idE W.Q.stdChar
  obtain ⟨B, hA, hvA, hz, he, he'⟩ := hB 1 (a.x 0).vol one_ne_zero
  have hz1 : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) :=
    fun k => by rw [hz k, one_mul]
  have hB0 := sbes_norm B hP.bot.idE hz1

  have hI := _root_.GlobalTheory.SeeSaw.YRat.spaces_of_index D u (fun j hj => D.X_posDef j hj)
  have hbes : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), ∃ b : BesAt (Yc D j) (D.sp.X j) ρ,
      star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E) := by
    intro j ρ h
    obtain ⟨V, b, hr, hs, hsig, hn⟩ := hI.1 j ρ h
    obtain ⟨b2, hb2⟩ := bes_to_Yc j ρ (by omega) b hr hs hsig
    exact ⟨b2, by rw [hb2]; exact hn⟩
  choose b' hb' using hbes
  have hjac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → Nonempty (JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ) := by
    intro j ρ h
    obtain ⟨V, b, hr, hs, hsig⟩ := hI.2 j ρ h
    exact jac_to_Yc (j + 1) ρ (by omega) b hr hs hsig
  obtain ⟨bes, hbes_def⟩ : ∃ f, f = besF (besOf B) b' := ⟨_, rfl⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m
    obtain ⟨k, hk⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  have hbes0 : bes 0 D.R.rS h0 = besOf B := by rw [hbes_def]; rfl
  have hnorm : ∀ j ρ h, star (bes j ρ h).ζ ⬝ᵥ (bes j ρ h).L.gram *ᵥ (bes j ρ h).ζ *
      (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [hbes_def]; exact besF_norm (besOf B) b' _ _ hB0 hb'

  have hlnk : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), Nonempty (Link ((bes j (σ + 1) h).lev (a.x j).vol)
      (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ) := by
    intro j σ h
    have hn1 := hnorm j (σ + 1) h
    have hn2 := hnorm (j + 1 + 1) σ (idx_step h)
    have e : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
    rw [e, pow_succ] at hn2
    have hrel : star (bes j (σ + 1) h).ζ ⬝ᵥ (bes j (σ + 1) h).L.gram *ᵥ (bes j (σ + 1) h).ζ =
        D.host.xi0 * star D.host.xi0 * (star (bes (j + 1 + 1) σ (idx_step h)).ζ ⬝ᵥ
          (bes (j + 1 + 1) σ (idx_step h)).L.gram *ᵥ (bes (j + 1 + 1) σ (idx_step h)).ζ) := by
      apply mul_right_cancel₀ (pow_ne_zero (j / 2) hN)
      rw [hn1]
      linear_combination -hn2
    have hl := (GlobalTheory.Unf.LinkExist.link_of_norm D (σ + 1) ((bes j (σ + 1) h).lev (a.x j).vol)
      (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ D.host.xi0
      (bes (j + 1 + 1) σ (idx_step h)).line hrel).2
    rwa [div_self hxi, one_smul] at hl
  have hvol := GlobalTheory.Unf.VolExist.measures_exist D

  have hrelT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), star (-D.host.xi0 ^ (D.R.m / 2)) * (-D.host.xi0 ^ (D.R.m / 2)) *
      (star (bes j 0 h).ζ ⬝ᵥ (bes j 0 h).L.gram *ᵥ (bes j 0 h).ζ) =
        -(D.host.xi0 * star D.host.xi0) * (star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀) := by
    intro j h
    have hn := hnorm j 0 h
    have e : D.R.m / 2 = j / 2 + 1 := by omega
    have hl : star (-D.host.xi0 ^ (D.R.m / 2)) * (-D.host.xi0 ^ (D.R.m / 2)) =
        (D.host.xi0 * star D.host.xi0) ^ (D.R.m / 2) := by
      rw [star_neg, star_pow, neg_mul_neg, mul_pow]; ring
    rw [hl, e, pow_succ, hT0]
    linear_combination (D.host.xi0 * star D.host.xi0) * hn
  refine ⟨⟨bes, fun j ρ h => (hjac j ρ h).some, fun j σ h => (hlnk j σ h).some, fun j σ h => (hvol.2.2.1 _ _).some,
    fun j h => Matrix.of fun i k => -D.host.xi0 ^ (D.R.m / 2) * (bes j 0 h).ζ i / a.ζ₀ k⟩, B, h0, ?_, ?_, hA,
    ⟨1, lam0, one_ne_zero, hlam0, hz, he, he'⟩, hB0, hz1⟩
  · intro j h
    exact tau_line (bes j 0 h).line.1 hLz.1 _ _ _ _ _ _ hLz.2 (hrelT j h)
  · show B.lev = (bes 0 D.R.rS h0).lev (a.x 0).vol
    rw [hbes0, ← hvA]
    rfl

end GlobalTheory.Fam.RatDec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCharacterConductorOneExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Topology

noncomputable section

namespace GlobalTheory.WeilCondUnif

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (p : SplitPt D k) (hU : p.UnitAA) : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := exists_idem p
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := pr_int p (hU.1 _ hm).2.2
  rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this

theorem hasConductor_of_mul {χ ψk : AddChar k Circle} {ξ : k} (hv : valuation k ξ = 1) (he : ∀ x, ψk x = χ (ξ * x))
    (h : HasConductor χ 1) : HasConductor ψk 1 := by
  intro x
  rw [← h x]
  have hξ0 : ξ ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  constructor
  · intro H y hy
    have := H (ξ⁻¹ * y) (by rw [map_mul, map_inv₀, hv, inv_one, one_mul]; exact hy)
    rwa [he, ← mul_assoc, mul_inv_cancel₀ hξ0, one_mul] at this
  · intro H y hy
    rw [he]
    exact H _ (by rw [map_mul, hv, one_mul]; exact hy)

theorem hasConductor_weil (q : SplitPt D k) (hU : q.UnitAA) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (ψk : AddChar k Circle) (h : (ofSplit q).IsChar ψ ψk) (hx : (ofSplit q).xi ≠ 0) : HasConductor ψk 1 := by
  have h' : ∀ x, (ψk x : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec x) := h
  set ξ : k := q.pr (incA D D.host.xi0) with hξ
  have hξ0 : ξ ≠ 0 := hx
  have hx0 : D.host.xi0 ≠ 0 := fun h0 => hξ0 (by rw [hξ, h0, map_zero, map_zero])
  have hinv : q.pr (incA D D.host.xi0⁻¹) = ξ⁻¹ := map_inv₀ (q.pr.comp (incA D)) D.host.xi0
  have h1 : valuation k ξ ≤ 1 := (Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral q hU)
  have h2 : valuation k ξ⁻¹ ≤ 1 := by rw [← hinv]; exact (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hv : valuation k ξ = 1 := by
    have hp : valuation k ξ * valuation k ξ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hξ0, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValueGroupWithZero k) = valuation k ξ * valuation k ξ⁻¹ := hp.symm
      _ ≤ valuation k ξ * 1 := mul_le_mul_right h2 _
      _ = valuation k ξ := mul_one _
  have hχ : q.IsChar ψ (ψk.mulShift ξ⁻¹) := fun a => by
    rw [AddChar.mulShift_apply, h', mul_comm ξ⁻¹ a, ← hinv, sec_mul_pr, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0,
      map_one, one_mul]
  refine hasConductor_of_mul hv (fun x => ?_) (hasConductor_one D k q ψ _ hψ hχ hU)
  rw [AddChar.mulShift_apply, ← mul_assoc, inv_mul_cancel₀ hξ0, one_mul]

theorem int_transfer {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : SplitPt D k) (q' : SplitPt D k') (he : q.e = q'.e) (z : AE D) : q.pr z ∈ 𝒪[k] ↔ q'.pr z ∈ 𝒪[k'] := by
  rw [q.int_iff, q'.int_iff, q.sec_pr, q'.sec_pr, he]

theorem dense_transfer {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : SplitPt D k) (q' : SplitPt D k') (he : q.e = q'.e) (hd : DenseRange (q'.pr.comp (incA D))) :
    DenseRange (q.pr.comp (incA D)) := by
  let f : k' → k := fun y => q.pr (q'.sec y)
  have hf : Continuous f := q.cont_pr.comp q'.cont_sec
  have hs : Function.Surjective f := fun a => ⟨q'.pr (q.sec a), by
    show q.pr (q'.sec (q'.pr (q.sec a))) = a
    rw [q'.sec_pr, ← he, e_mul_sec, q.pr_sec]⟩
  have hc : f ∘ (q'.pr.comp (incA D)) = q.pr.comp (incA D) := funext fun a => by
    show q.pr (q'.sec (q'.pr (incA D a))) = q.pr (incA D a)
    rw [q'.sec_pr, ← he, map_mul, pr_e, one_mul]
  have := hs.denseRange.comp hd hf
  rwa [hc] at this

end Local

section Unif

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {K : Type} [Field K] [NumberField K]

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem isUnif_of (P : HeightOneSpectrum (𝓞 K)) (ι : K →+* k) (hint : ∀ a, ι a ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P a)
    (hd : DenseRange ι) (hq : ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 K) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ (ϖ : k) = ι ((Formalism.L2.Col.qOf P : ℕ) : K) := by
  have hvN := GlobalTheory.AtTypeExists.valuation_norm P hq
  set N : K := ((Formalism.L2.Col.qOf P : ℕ) : K) with hN
  have hN0 : N ≠ 0 := fun h0 => WithZero.exp_ne_zero (hvN.symm.trans (by rw [h0, map_zero]))
  have hI : ∀ a, valuation k (ι a) ≤ 1 ↔ P.valuation K a ≤ 1 := fun a => by
    rw [← GlobalTheory.AtTypeExists.intAt_iff, ← hint, Valuation.mem_integer_iff]
  have hvN1 : P.valuation K N ≠ 0 := by rw [hvN]; exact WithZero.exp_ne_zero
  have K1 : ∀ a : K, valuation k (ι a) < 1 → valuation k (ι a) ≤ valuation k (ι N) := by
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, map_zero, map_zero]; exact zero_le'
    have ha0 : valuation k (ι a) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]; exact (map_ne_zero ι).2 a0
    have h1 : ¬ P.valuation K a⁻¹ ≤ 1 := by
      rw [← hI, map_inv₀, map_inv₀]
      intro h
      have := mul_le_mul_right h (valuation k (ι a))
      rw [mul_inv_cancel₀ ha0, mul_one] at this
      exact not_le.2 ha this
    have hPa : P.valuation K a < 1 :=
      lt_of_le_of_ne ((hI a).1 ha.le) (fun h => h1 (by rw [map_inv₀, h, inv_one]))
    have hle := lt_one_le_exp hPa
    have hdiv : P.valuation K (a / N) ≤ 1 := by
      calc P.valuation K (a / N) = P.valuation K a * (P.valuation K N)⁻¹ := by rw [map_div₀, div_eq_mul_inv]
        _ ≤ P.valuation K N * (P.valuation K N)⁻¹ := mul_le_mul_left (hle.trans_eq hvN.symm) _
        _ = 1 := mul_inv_cancel₀ hvN1
    have h2 := (hI _).2 hdiv
    calc valuation k (ι a) = valuation k (ι (a / N)) * valuation k (ι N) := by
          rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hN0]
      _ ≤ 1 * valuation k (ι N) := mul_le_mul_left h2 _
      _ = valuation k (ι N) := one_mul _
  have hexp : WithZero.exp (-1 : ℤ) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have K2 : valuation k (ι N) < 1 := by
    refine lt_of_le_of_ne ((hI N).2 (hvN.trans_le hexp)) fun h => ?_
    have h3 : valuation k (ι N⁻¹) ≤ 1 := by rw [map_inv₀, map_inv₀, h, inv_one]
    rw [hI, map_inv₀, hvN, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h3
    norm_num at h3
  refine ⟨Units.mk0 (ι N) ((map_ne_zero ι).2 hN0), fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx K2⟩, rfl⟩
  rw [Units.val_mk0]
  by_cases x0 : x = 0
  · rw [x0, map_zero]; exact zero_le'
  have hx0 : valuation k x ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact x0
  have hs : {y : k | valuation k (y - x) < valuation k x} ∈ 𝓝 x :=
    IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hx0, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.1 (hd x) _ hs
  have e : valuation k (ι a) = valuation k x := Valuation.map_eq_of_sub_lt _ hy
  rw [← e] at hx ⊢
  exact K1 a hx

end Unif

theorem cond_unif : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (PP : Pl D.host.E), PP ∈ (pk W).Pg ∨ QAll W PP → ∀ l : LocX a (pk W).βX PP, (∃ ψk : AddChar l.k Circle, (ofSplit l.q).IsChar (pk W).ψ ψk ∧ HasConductor ψk 1) ∧ (∃ ν : Measure l.k, IsUnitVol ν) ∧ (QAll W PP → ∃ ϖ : l.kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (l.q.pr.comp (incA D)) ϖ) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a PP hPP l
  have hstd : IsStdChar D (pk W).ψ (-1) := W.Q.stdChar
  refine ⟨?_, GlobalTheory.SplitWeil.exists_isUnitVol l.k, fun hQ => ?_⟩
  · obtain ⟨⟨ψk, hψk⟩, -, hxi, -⟩ := GlobalTheory.LocChar.weil_char_split D l.k (ofSplit l.q) (pk W).ψ hstd
    exact ⟨ψk, hψk, hasConductor_weil l.q l.unit _ hstd ψk hψk hxi⟩
  · obtain ⟨t, ht⟩ := hQ
    obtain ⟨⟨p, -, hcard, hp2, -⟩, -⟩ := W.Q.charW.base.lev.Q_pl t PP ht
    have hqp : Formalism.L2.Col.qOf PP = p := by
      rw [← hcard]
      unfold Formalism.L2.Col.qOf
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hq2 : ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by rw [hqp]; exact hp2
    obtain ⟨k', _, _, _, _, q', hqe, -, hint', hd'⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP l.q.e l.idem
    have hint : ∀ x, (l.q.pr.comp (incA D)) x ∈ 𝒪[l.k] ↔ Formalism.L2.Col.IntAt PP x := fun x =>
      (int_transfer l.q q' hqe.symm (incA D x)).trans (hint' x)
    have hd := dense_transfer l.q q' hqe.symm hd'
    obtain ⟨ϖ, hu, hϖ⟩ := isUnif_of PP _ hint hd hq2
    exact ⟨ϖ, hu, ⟨hint, hd, rfl, hϖ⟩⟩

end GlobalTheory.WeilCondUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalSumCoresHomotheticOffLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M M' : Lat S) (LA : Lat A) (LL : Lat L) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D) (a₀ : GA D A), IsLineVec L ζ → IsSelfDualC L LL → OrthAt o M LA LL v → TraceAt o a₀ LA M' v → SplitsAt o M' v → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' v := by
  intro D S A L o ζ M M' LA LL μ T v a₀ hζ hLL hM hTr hSp hμ hline hn hT
  obtain ⟨Λ', hΛ', hmem⟩ := _root_.GlobalTheory.Core.Mi.LineSD.exists_isSDAt_line D S A L o ζ M' μ T v hζ hμ hline hn hT
  obtain ⟨γ, hγ, hmove⟩ := _root_.GlobalTheory.IwaOrbit.selfDual_orbit D L v _ Λ' (GlobalTheory.FinPl.TamePlaces.tame D v)
    (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D L LL v hLL) hΛ'
  obtain ⟨c, hc, hc', hγc⟩ := GlobalTheory.T.exists_normOneIdele_of_supported_rankOneUnitary D L v γ hζ.1 hγ
  obtain ⟨a, ha, hma⟩ := _root_.GlobalTheory.Core.Mi.LatMatch.exists_cenAt_scalar D A v (cA D c) hc'
  refine ⟨a, c, ha, hc, ?_⟩
  intro y hy
  have hAy : ∀ i, (o.pA *ᵥ y) i ∈ idAt D (· = v) := GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy
  have hBy : ∀ i, (o.pB *ᵥ y) i ∈ idAt D (· = v) := GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy
  have hcBy : ∀ i, (c • (o.pB *ᵥ y)) i ∈ idAt D (· = v) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hBy i)
  have hcc : c * cA D c = 1 := hc.1
  have key : c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y) =
      o.jA *ᵥ (Formalism.L2.Theta.mt A a₀ *ᵥ (o.pA *ᵥ y)) + o.jB *ᵥ (c • (o.pB *ᵥ y)) := by
    rw [o.mt_emb, GlobalTheory.FinPlLoc.mt_mul, hma, GlobalTheory.FinPlLoc.mt_one]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_smul, smul_add, smul_smul, hcc, one_smul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hz : ∀ i, (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) i ∈ idAt D (· = v) := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  have hpA : o.pA *ᵥ (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) = Formalism.L2.Theta.mt A a₀ *ᵥ (o.pA *ᵥ y) := by
    rw [key, Matrix.mulVec_add, Matrix.mulVec_mulVec _ o.pA o.jA, Matrix.mulVec_mulVec _ o.pA o.jB, o.pA_jA, o.pA_jB,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  have hpB : o.pB *ᵥ (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) = c • (o.pB *ᵥ y) := by
    rw [key, Matrix.mulVec_add, Matrix.mulVec_mulVec _ o.pB o.jA, Matrix.mulVec_mulVec _ o.pB o.jB, o.pB_jA, o.pB_jB,
      Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]
  rw [hM y, hSp _ hz, hpA, hpB, ← hTr _ hAy, ← hmem _ hcBy, hmove _ hBy, hγc, Matrix.smul_mulVec,
    Matrix.one_mulVec]
end

