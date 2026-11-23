module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0073
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSA

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CjTFromBlocks
section
noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Block

variable {K : Type*} [CommRing K] (cj : K →+* K) {n : Type*} [Fintype n] [DecidableEq n]

def cjT {m n : Type*} (A : Matrix m n K) : Matrix n m K := (A.map cj)ᵀ

theorem cjT_mul {l m n : Type*} [Fintype m] (A : Matrix l m K) (B : Matrix m n K) :
    cjT cj (A * B) = cjT cj B * cjT cj A := by
  unfold cjT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cjT_cjT {m n : Type*} (h : ∀ x, cj (cj x) = x) (A : Matrix m n K) : cjT cj (cjT cj A) = A := by
  ext i j; simp [cjT, h]

theorem cjT_fromBlocks {a b c d : Type*} (A : Matrix a c K) (B : Matrix a d K) (C : Matrix b c K) (D : Matrix b d K) :
    cjT cj (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (cjT cj A) (cjT cj C) (cjT cj B) (cjT cj D) := by
  unfold cjT
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cjT_zero {m n : Type*} : cjT cj (0 : Matrix m n K) = 0 := by
  ext i j; simp [cjT]

theorem block_cong (h : ∀ x, cj (cj x) = x) (G₁ G₁' X X' G₂ G₂' Mm U : Matrix n n K)
    (h1 : cjT cj Mm * G₁ * Mm = G₁') (h2 : cjT cj Mm * X * U = X') (h3 : cjT cj U * G₂ * U = G₂') :
    cjT cj (Matrix.fromBlocks Mm 0 0 U) * Matrix.fromBlocks G₁ X (cjT cj X) G₂ * Matrix.fromBlocks Mm 0 0 U =
      Matrix.fromBlocks G₁' X' (cjT cj X') G₂' := by
  rw [cjT_fromBlocks, cjT_zero, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [h1, h3, ← h2]
  congr 1 <;> first
    | (simp only [Matrix.mul_assoc]; done)
    | (rw [cjT_mul, cjT_mul, cjT_cjT cj h]; simp only [Matrix.mul_assoc])

end Block

section GaBlocks

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

def gDiag (p : PlF D) (T : D.host.E) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => frFac δ p b * (M p).L.cj (frFac δ p a) *
    (D.s.atP p).ιE (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0)

theorem gaLoc_blocks (hA : ∀ q, Agree δ M q) (p : PlF D) (T T' : D.host.E) (Z : MatZ D) :
    GaLoc M δ p T T' Z = Matrix.fromBlocks (gDiag δ M p T) (ZhatLoc M δ p Z)
      (cjT ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (ZhatLoc M δ p Z)) (gDiag δ M p T') := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp [GaLoc, gDiag, Ga, phi]
  · simp [GaLoc, ZhatLoc, Ga, phi]
  · simp only [GaLoc, Matrix.of_apply, phi, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₁,
      Matrix.conjTranspose_apply, cjT, Matrix.transpose_apply, Matrix.map_apply, ZhatLoc, RingHom.coe_coe]
    rw [map_mul, map_mul, (M p).L.cj_cj, hcj, Formalism.MainNotions.S.Inh.tie_cj_iota]
    ring
  · simp [GaLoc, gDiag, Ga, phi]

end GaBlocks

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIB
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def LsetB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (m : (VS D).V), m ∈ γ.lam → m ∈ orth (VS D) (Xsp (repF γ)) →
        ∃ x ∈ lattice₂ D Zd.M p Λ₂, baseChange₂ D p (β₀ m) - x ∈ (locH Zd p).X (locF' Zd p F'₂)

def IotaB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ v : (VS D).V ≃ₗ[D.host.E] (VS D).V, v ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
        (∀ b, v (frame (liftF F'₂) b) = frame (liftF F'₂) b) →
        (∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), v y - y ∈ Xsp (liftF F'₂)) →
        Formalism.HermitianLatticesTheory.gmap (v * β₀) γ.lam = Λ₂ → IotaC₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀)

variable {u u' F0 what₂}

namespace BetaI

theorem isLattice_gmap' (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) {L : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Submodule.IsLattice D.host.E L) : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : ((Formalism.HermitianLatticesTheory.gmap g L : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) =
      (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' (L : Set (VS D).V) := rfl
  exact fun _ _ hli => (LinearIndependent.iff_fractionRing _ _).mp hli

theorem sd_gmap (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hSD : BwdNA.SD (VS D) Λ) : BwdNA.SD (VS D) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  intro x
  rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
  constructor
  · intro hx y hy
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff] at hy
    have h1 := (hSD _).1 hx _ hy
    have e := hβ (β.symm y) (β.symm x)
    simp only [LinearEquiv.apply_symm_apply] at e
    rwa [e]
  · intro h
    refine (hSD _).2 fun y hy => ?_
    have h1 := h (β y) (by rw [Formalism.L2.SG.Saturated.mem_gmap_iff]; simpa using hy)
    have e := hβ y (β.symm x)
    simp only [LinearEquiv.apply_symm_apply] at e
    rwa [e] at h1

end BetaI

theorem betaInt_of (hLs : LsetB Zd u u' F0 what₂) (hIo : IotaB Zd u u' F0 what₂) : BetaInt Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO
  have hB0 := hB
  obtain ⟨hC, -, hS, hΛ₂, -, hT, hPD, -⟩ := hB
  obtain ⟨hΛ₂full, hloc₂⟩ := hΛ₂
  obtain ⟨-, hT2, -⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛfull : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have hΛlat := hΛfull.toIsLattice
  have hΛ₂lat := hΛ₂full.toIsLattice
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (hT2 p).1.1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p F'₂) := fun p => (hloc₂ p).1.1.2.2.1.1
  have hSD := sd_of_loc Zd hΛfull hSDl
  have hSD₂ := sd_of_loc Zd hΛ₂full hSDl₂
  have hXiso : ∀ x ∈ Xsp (liftF F'₂), ∀ y ∈ Xsp (liftF F'₂), (VS D).hT x y = 0 :=
    fun x hx y hy => NMoveP.hT_X_X F'₂.fl hx hy
  have hzX : F'₂.fl.z ∈ orth (VS D) (Xsp (liftF F'₂)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F'₂.fl.z x]
    have h := NMoveP.hT_f_X F'₂.fl (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]
  have hznot : F'₂.fl.z ∉ Xsp (liftF F'₂) := by
    intro h
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hzX F'₂.fl.z h
    rw [F'₂.fl.z_norm, neg_eq_zero] at h0
    exact (D.mem u').A.T_prime.ne_zero (Nat.cast_eq_zero.1 h0)
  have hXo := BwdNA.X_le_orth (VS D) (Xsp (liftF F'₂)) hXiso
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) (Xsp (liftF F'₂))) → w ∈ Xsp (liftF F'₂) :=
    fun {w} hw => BwdNA.mem_of_orth_orth (VS D) _ fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXX' : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) (Xsp (repF γ))) → w ∈ Xsp (repF γ) :=
    fun {w} hw => BwdNA.mem_of_orth_orth (VS D) _ fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXmap : (Xsp (repF γ)).map (β₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (liftF F'₂) :=
    BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hsymmX : ∀ x ∈ Xsp (liftF F'₂), β₀.symm x ∈ Xsp (repF γ) := fun x hx => by
    rw [← hXmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hmapX : ∀ x ∈ Xsp (repF γ), β₀ x ∈ Xsp (liftF F'₂) := fun x hx => by
    rw [← hXmap]; exact Submodule.mem_map_of_mem hx

  have hΛ₁lat := BetaI.isLattice_gmap' β₀ hΛlat
  have hSD₁ := BetaI.sd_gmap β₀ hiso hSD

  have he : ∀ a, β₀ ((repF γ).fl.e a) = F'₂.fl.e a := BwdBetaCut.e_of_frame β₀ (repF γ) (liftF F'₂) hfr
  have hXS : Formalism.HermitianLatticesTheory.gmap β₀ (XS D (repF γ).fl) = XS D F'₂.fl := by
    unfold Formalism.HermitianLatticesTheory.gmap XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      exact ⟨a, x, hx, by simp [he]⟩
    · rintro ⟨a, x, hx, rfl⟩
      exact ⟨x • (repF γ).fl.e a, ⟨a, x, hx, rfl⟩, by simp [he]⟩
  have hFO₂ : XLam Λ₂ (liftF F'₂) = XS D F'₂.fl := hT.2.2.2.2
  have hFO : XLam γ.lam (repF γ) = XS D (repF γ).fl := hPD.2.2.2
  have hXm : ∀ x ∈ Xsp (liftF F'₂), x ∈ Λ₂ ↔ x ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam := fun x hx => by
    have h1 : x ∈ Λ₂ ↔ x ∈ XLam Λ₂ (liftF F'₂) :=
      ⟨fun h => Submodule.mem_inf.2 ⟨h, hx⟩, fun h => (Submodule.mem_inf.1 h).1⟩
    have h2 : x ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam ↔ β₀.symm x ∈ XLam γ.lam (repF γ) := by
      rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
      exact ⟨fun h => Submodule.mem_inf.2 ⟨h, hsymmX x hx⟩, fun h => (Submodule.mem_inf.1 h).1⟩
    rw [h1, h2, hFO₂, hFO, ← hXS, Formalism.L2.SG.Saturated.mem_gmap_iff]

  have hzβ : β₀ (repF γ).fl.z = F'₂.fl.z := by
    have := hfr (Fin.last _)
    rwa [BwdBetaCut.fvec_last', BwdBetaCut.fvec_last'] at this
  have hz₁ : F'₂.fl.z ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam := by
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff, ← hzβ, LinearEquiv.symm_apply_apply]
    exact hPD.1.1
  have hz₂ : F'₂.fl.z ∈ Λ₂ := hT.1.1.1

  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) (Xsp (liftF F'₂)) →
      ∃ y ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam, y - x ∈ Xsp (liftF F'₂) := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam hΛlat hSD (orth (VS D) (Xsp (repF γ))) (β₀.symm x)
      (fun m hm hmo => by
        have e := hiso m (β₀.symm x)
        rw [LinearEquiv.apply_symm_apply] at e
        rw [← e]
        refine int_of_loc Zd fun p => ?_
        rw [← localForm_baseChange]
        obtain ⟨x₁, hx₁, hd⟩ := hLs γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p m hm hmo
        have e2 : baseChange₂ D p (β₀ m) = x₁ + (baseChange₂ D p (β₀ m) - x₁) := by abel
        rw [e2, Formalism.L2.SG.Pf.ScalarFramePf.h_add_right (locH Zd p),
          (show (locH Zd p).h (baseChange₂ D p x) (baseChange₂ D p (β₀ m) - x₁) = 0 from baseChangeAt_perp' Zd p F'₂ hxo _ hd), add_zero]
        exact ((hSDl₂ p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) x₁ hx₁)
    refine ⟨β₀ w, (Formalism.L2.SG.Saturated.mem_gmap_iff _ _ _).2 (by simpa using hw), ?_⟩
    have h2 := hmapX _ (hXX' hxw)
    have e : β₀ w - x = -(β₀ (β₀.symm x - w)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact (Xsp (liftF F'₂)).neg_mem h2
  have hL' : ∀ y ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam, y ∈ orth (VS D) (Xsp (liftF F'₂)) →
      ∃ x ∈ Λ₂, x ∈ orth (VS D) (Xsp (liftF F'₂)) ∧ y - x ∈ Xsp (liftF F'₂) := fun y hy hyo => by
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff] at hy
    have hmo : β₀.symm y ∈ orth (VS D) (Xsp (repF γ)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
      have e := hiso x (β₀.symm y)
      rw [LinearEquiv.apply_symm_apply] at e
      rw [← e]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hyo _ (hmapX x hx)
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂lat hSD₂ (orth (VS D) (Xsp (liftF F'₂))) y
      (fun m₂ hm₂ hm₂o => by
        refine int_of_loc Zd fun p => ?_
        rw [← localForm_baseChange]
        obtain ⟨x₁, hx₁, hd⟩ := hLs γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p _ hy hmo
        rw [LinearEquiv.apply_symm_apply] at hd
        have e2 : baseChange₂ D p y = x₁ + (baseChange₂ D p y - x₁) := by abel
        rw [e2, (locH Zd p).h_add_left]
        have h0 : (locH Zd p).h (baseChange₂ D p y - x₁) (baseChange₂ D p m₂) = 0 := by
          rw [(locH Zd p).h_herm, (show (locH Zd p).h (baseChange₂ D p m₂) (baseChange₂ D p y - x₁) = 0 from
            baseChangeAt_perp' Zd p F'₂ hm₂o _ hd), map_zero]
        rw [h0, add_zero]
        exact ((hSDl₂ p).2.2 x₁).1 hx₁ (baseChange₂ D p m₂) (baseChange_mem_localLattice Zd hm₂ p))
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) (Xsp (liftF F'₂))).sub_mem hyo (hXo hX1)
  have hy := exists_yG Zd F'₂ hΛ₂lat hSD₂ hpr₂ hznot
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hniso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) (Xsp (liftF F'₂)) hXiso F'₂.fl.z hzX
    (Formalism.HermitianLatticesTheory.gmap β₀ γ.lam) Λ₂ hΛ₁lat hΛ₂lat hSD₁ hSD₂ hXm hz₁ hz₂ hL hL' hy htr
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hniso
  have hvI : n.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hnI
  have hvf : ∀ b, n.symm (frame (liftF F'₂) b) = frame (liftF F'₂) b := by
    intro b
    rw [LinearEquiv.symm_apply_eq]
    refine Fin.lastCases ?_ (fun i => ?_) b
    · rw [BwdBetaCut.fvec_last']; exact hnz.symm
    · rw [BwdBetaCut.fvec_cs']; exact (hnX _ (Submodule.subset_span ⟨i, rfl⟩)).symm
  have hvX : ∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), n.symm y - y ∈ Xsp (liftF F'₂) := by
    intro y hy
    have hy'o : n.symm y ∈ orth (VS D) (Xsp (liftF F'₂)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
      have e := hniso x (n.symm y)
      rw [hnX x hx, LinearEquiv.apply_symm_apply] at e
      rw [← e]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hy x hx
    have h1 := hno _ hy'o
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : n.symm y - y = -(y - n.symm y) := by abel
    rw [e]
    exact (Xsp (liftF F'₂)).neg_mem h1
  have hgm : Formalism.HermitianLatticesTheory.gmap (n.symm * β₀) γ.lam = Λ₂ := by
    ext x
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
    have e : (n.symm * β₀).symm x = β₀.symm (n x) := by
      rw [LinearEquiv.symm_apply_eq]
      show x = n.symm (β₀ (β₀.symm (n x)))
      simp
    rw [e, ← Formalism.L2.SG.Saturated.mem_gmap_iff]
    constructor
    · intro h
      have h' : n x ∈ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) := by rw [himg]; exact h
      obtain ⟨y, hy, hyx⟩ := h'
      rw [← n.injective hyx]
      exact hy
    · intro h
      have h' : n x ∈ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) := ⟨x, h, rfl⟩
      rw [himg] at h'
      exact h'
  exact ⟨n.symm, hvI, hvf, hvX, hgm, hIo γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO n.symm hvI hvf hvX hgm⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRel
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormRelC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').nzSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

end Formalism.L2.SG.Pf.FormRel

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel

theorem formNGC_of_rel (h : FormRelC) : Formalism.L2.SG.NGVanish.FormNGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u u' hx ν hν t ht hv => ?_⟩
  have hnz : t ∈ (Y.tO u u').nzSet := by
    exact ht.1
  exact hC C' Cl h1 h2 D large₂ X Y u u' hx ν hν t hnz hv

theorem formGC_of_rel (h : FormRelC) : Formalism.L2.SG.Pf.MainEqVanish.FormGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hx ν hν t ht hv => ?_⟩
  have hnz : t ∈ (Y.tO u u).nzSet := by
    exact ht.1
  exact hC C' Cl h1 h2 D large₂ X Y u u hx ν hν t hnz hv

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMapFlag
section
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem omp_congr {F G : FlagG S r T} {F' G' : FlagG S r T'} (h : ∀ a, F.fvec a = G.fvec a)
    (h' : ∀ a, F'.fvec a = G'.fvec a) : omp F F' = omp G G' ∧ Zhat F F' = Zhat G G' := by
  have hF : F.fvec = G.fvec := funext h
  have hF' : F'.fvec = G'.fvec := funext h'
  have hZ : Zhat F F' = Zhat G G' := by
    unfold Zhat
    first
      | rw [hF, hF']
      | (simp only [hF, hF']; rfl)
  refine ⟨?_, hZ⟩
  unfold omp
  rw [hZ, hF']

theorem fvec_mapFlag (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (b : Fin (r + 1)) :
    (mapFlag g hg F).fvec b = g (F.fvec b) := by
  unfold FlagG.fvec
  induction b using Fin.lastCases with
  | last => simp [mapFlag]
  | cast i => simp [mapFlag]

theorem coef_mat (F : FlagG S r T) (s : S.V →ₗ[E] S.V) (hs : ∀ j, ∀ x ∈ F.Xa (j + 1), s x - x ∈ F.Xa j)
    (hz : s F.z - F.z ∈ F.X) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c) ∧ M.det = 1 ∧
      ∀ c, M (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  have hcolE : ∀ b' : Fin r, ∃ l : Fin r →₀ E, (∀ i : Fin r, ¬ i.1 < b'.1 → l i = 0) ∧
      s (F.e b') = F.e b' + ∑ i, l i • F.e i := by
    intro b'
    have hmem : F.e b' ∈ F.Xa (b'.1 + 1) := Submodule.subset_span ⟨b', Nat.lt_succ_self _, rfl⟩
    have h1 := hs b'.1 (F.e b') hmem
    obtain ⟨l, hl, hl2⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 h1
    refine ⟨l, fun i hi => (Finsupp.mem_supported' E l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hl2
    rw [hl2]
    abel
  choose l hl0 hl using hcolE
  obtain ⟨cz, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hz
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun c b =>
    Fin.lastCases (motive := fun _ => E)
      (Fin.lastCases (motive := fun _ => E) 1 (fun i => cz i) c)
      (fun b' => Fin.lastCases (motive := fun _ => E) 0 (fun i => (if i = b' then 1 else 0) + l b' i) c) b
  have hMcol : ∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, one_smul]
      have h2 : s F.z = F.z + ∑ i, cz i • F.e i := by
        rw [hcz]
        abel
      rw [h2, add_comm]
    | cast b' =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, zero_smul, add_zero, add_smul, Finset.sum_add_distrib, ite_smul,
        one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hl b'
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [M]
    | cast i => simp [M, hl0 i i (lt_irrefl _)]
  have htri : M.BlockTriangular id := by
    intro i j hij
    induction j using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last i))
    | cast j =>
      induction i using Fin.lastCases with
      | last => simp [M]
      | cast i =>
        have hji : j < i := by simpa using hij
        have hne : i ≠ j := (ne_of_lt hji).symm
        simp [M, hne, hl0 j i (not_lt.2 (le_of_lt hji))]
  refine ⟨M, hMcol, ?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  · intro c
    induction c using Fin.lastCases with
    | last => simp [M]
    | cast c => simp [M, Fin.castSucc_ne_last]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXMasses
section
namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.L2.SG.TypedSets

theorem inMassesAt_holds :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InMassesAt X hb hK FdN FdN' u u' X0 L A :=
  massDataMasses_of' hinfCompact_holds kCompactOpen_holds classFinite_holds strongApproxN_holds

end Formalism.L2.SG.Pf.MassDataX
end

