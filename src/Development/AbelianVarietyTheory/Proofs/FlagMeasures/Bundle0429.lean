module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsLab
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsPCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0039
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCountP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFixedPlaceConjugatorLiftsActByReductions
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0102

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AllRowsAtRecord
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

noncomputable section

namespace GlobalTheory.AllRowsAtRecord

open Formalism.L2.SG.AllRowsOf

def stdChar (D : D7) (k : Fin 2) : AddChar (ZMod (D.host.g k)) ℂ :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  ZMod.stdAddChar

theorem stdChar_ne (D : D7) (k : Fin 2) : stdChar D k ≠ 1 := by
  intro hk
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩
  change (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) = 1 at hk
  have h1 : (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) 1 = (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) 0 := by
    rw [hk, AddChar.one_apply, AddChar.map_zero_eq_one]
  exact one_ne_zero (ZMod.injective_stdAddChar h1)

theorem countAllRows_of {D : D7} (A : AllRows D) {c c₃ : ℝ} (hc : 0 < c) (hcc : c ≤ c₃) (hN : 2 ≤ D.R.r)
    (hf : 1 ≤ D.R.f) (hC : Formalism.MainNotions.N.CylinderCountFamily.CountCylAt D A.toAt c₃) (hpos : 0 < DstarE A A.B.e) :
    CountAllRows A (epsC c D.R.r D.R.f) := by
  have hL : 0 < Real.log (D.R.r : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hN0 : (0 : ℝ) < D.R.r := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hf)
  have hP : 0 < (D.R.r : ℝ) * D.R.f * Real.log D.R.r := by positivity
  refine ⟨(Real.exp_pos _).le, ?_, hpos, fun k S => ?_⟩
  · unfold epsC
    have h0 : 0 < c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r := by
      have := mul_pos hc hP
      linarith [this, show c * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r) = c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r by ring]
    have h1 := Real.exp_lt_exp.mpr (show -(c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r) < 0 by linarith)
    rwa [Real.exp_zero] at h1
  · have h := hC k S
    change |((A.dimT (cyl D k S) : ℕ) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) * DstarE A (A.eT (cyl D k S)) at h
    rw [A.n_eq, A.f_eq] at h
    have hDs : 0 ≤ DstarE A (A.eT (cyl D k S)) :=
      (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (le_trans (abs_nonneg _) h)
    have hexp : Real.exp (-c₃ * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)) ≤ epsC c D.R.r D.R.f := by
      unfold epsC
      apply Real.exp_le_exp.mpr
      have e1 : -c₃ * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ) = -(c₃ * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r)) := by ring
      have e2 : -(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)) = -(c * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r)) := by ring
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_right hcc hP.le
      linarith
    exact le_trans h (mul_le_mul_of_nonneg_right hexp hDs)

theorem allRows_at_record : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (G : GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (n₀ : ℕ) (Alev C₃ c₃ cb c : ℝ), 0 < c → c ≤ c₃ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    AutTie D X.B X.pl → RowDictTie X G ι → GlobalTheory.LabPin.LabTie X ι → (∀ P, CountE.CountIdempotentsClass P D n₀ Alev C₃ c₃ cb) →
    AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n₀ Alev C₃ cb → 4 * D.R.r < D.host.g 1 →
    ∃ A : AllRows D, LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC c D.R.r D.R.f) := by
  intro hRF D large₂ X G ι n₀ Alev C₃ c₃ cb c hc hcc hG hAut hT hLab hCnt hp hg1
  have hL : RowsLab X := Formalism.L2.SG.Pf.AllRowsLab.rowsLab_holds X hRF hG G ι hT hLab hAut
  have hψ : ∀ k, stdChar D k ≠ 1 := stdChar_ne D
  have hB : CountBase X n₀ Alev C₃ cb := Formalism.L2.SG.Pf.AllRowsCountBase.countBase_of X hAut hp hg1
  refine ⟨Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X (stdChar D) hψ hL, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact thirdTie_allRows (hI := etInt_holds X)
  · refine ⟨⟨X.pl, hAut⟩, fun v => Formalism.L2.SG.Pf.AllRowsCountBase.hc_X X hAut v, fun _ => ?_⟩
    change Formalism.MainNotions.S.SplitsCompl X.B.I.E X.B.g₀
    rw [X.g0_eq]
    exact Formalism.L2.SG.Pf.AllRowsCountBase.splits_X X 0
  · exact ⟨stdChar D, hψ, fun _ _ => rfl⟩
  · have hN : 2 ≤ D.R.r := le_trans (by norm_num) hG.1
    have hf : 1 ≤ D.R.f := by exact_mod_cast Formalism.MainNotions.S.one_le_f (D := D)
    have hTC := tieCountAt_allRowsOf (X := X) (ψ₀ := stdChar D) (hJ := ejIdem_holds D (stdChar D))
      (hU := etUniv_of X (redKer_of X (redKerOne_of X (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0)
        (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))))
      (hO := Formalism.L2.SG.Pf.AllRowsClosed.etOne_holds X (stdChar D) hψ) (hI := etInt_holds X) (hL := hL) hB
      (fun _ _ => Formalism.L2.SG.Pf.AllRowsClosed.etAlg_holds X _)
      (fun k S => Formalism.L2.SG.Pf.AllRowsClosed.etUnip_holds X k S)
    have hC : Formalism.MainNotions.N.CylinderCountFamily.CountCylAt D (Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X (stdChar D) hψ hL).toAt c₃ :=
      Formalism.MainNotions.N.CylinderCountFamily.countCylAt_of D _ (hCnt Formalism.MainNotions.S.CountE.PCount) hTC
        (Formalism.L2.SG.Pf.AllRowsPCount.pCountTie_holds X (stdChar D) hψ hL)
    obtain ⟨-, -, -, -, -, -, -, hpos⟩ := hB
    exact countAllRows_of _ hc hcc hN hf hC hpos

end GlobalTheory.AllRowsAtRecord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermEqIffStabiliserOrbit
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.TermOrbit

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem ext_eq (A : Places F E sig) {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {g₁ g₂ : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)}
    (h₁ : A.Ext p g g₁) (h₂ : A.Ext p g g₂) : g₁ = g₂ := by
  have hb : ∀ i : Fin n, A.bc p (Pi.single i 1) = Pi.single i 1 := by
    intro i; funext j
    simp only [Places.bc, Pi.single_apply]
    split_ifs <;> simp
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (A.loc p).Ep (Fin n)).ext
  intro i
  simp only [Pi.basisFun_apply, LinearEquiv.coe_coe]
  rw [← hb i, h₁, h₂]

theorem mem_rat_inf (A : Places F E sig) {n : ℕ}
    (K K' : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)))
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (h : g ∈ A.rat K) (h' : g ∈ A.rat K') :
    g ∈ A.rat (fun p => K p ⊓ K' p) := by
  intro p
  obtain ⟨g₁, hg₁, e₁⟩ := h p
  obtain ⟨g₂, hg₂, e₂⟩ := h' p
  obtain rfl := ext_eq A p e₁ e₂
  exact ⟨g₁, ⟨hg₁, hg₂⟩, e₁⟩

theorem rat_mono (A : Places F E sig) {n : ℕ}
    {K K' : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))}
    (hK : ∀ p, K p ≤ K' p) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (h : g ∈ A.rat K) : g ∈ A.rat K' := by
  intro p
  obtain ⟨g₁, hg₁, e₁⟩ := h p
  exact ⟨g₁, hK p hg₁, e₁⟩

end Places

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section Coord

variable {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
  (c : GCoord Z F0 F0' FP G)

theorem grp_mul (ρ a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ (a * b) = c.grp ρ a * c.grp ρ b := by
  ext x; simp [GCoord.grp, LinearEquiv.mul_apply]

theorem grp_one (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ 1 = 1 := by
  ext x; simp [GCoord.grp]

theorem grp_inv (ρ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ a⁻¹ = (c.grp ρ a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← grp_mul, inv_mul_cancel, grp_one]

theorem grp_conj (ρ τ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp (ρ * τ) a = c.grp ρ (τ * a * τ⁻¹) := by
  ext x; simp [GCoord.grp, LinearEquiv.mul_eq_trans, LinearEquiv.symm_trans_apply]

theorem grp_surj (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : G.GLV) :
    c.grp ρ (((ρ.trans c.e).trans s).trans (ρ.trans c.e).symm) = s := by
  ext x; simp [GCoord.grp]

theorem lat_map_grp (ρ a σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (c.lat (ρ * a) Λ).map (((c.grp ρ σ : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) =
      c.lat (ρ * (σ * a)) Λ := by
  simp only [GCoord.lat]
  rw [← Submodule.map_comp]
  congr 1
  ext x; simp [GCoord.grp, LinearEquiv.mul_apply]

theorem lat_mul (ρ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    c.lat (ρ * a) Λ = c.lat ρ (Formalism.HermitianLatticesTheory.gmap a Λ) := by
  simp only [GCoord.lat, Formalism.HermitianLatticesTheory.gmap]
  rw [← Submodule.map_comp]
  congr 1

theorem lat_inj (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h : c.lat ρ Λ₁ = c.lat ρ Λ₂) : Λ₁ = Λ₂ :=
  Submodule.map_injective_of_injective
    (f := (((ρ.trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)))
    (fun x y hxy => (ρ.trans c.e).injective hxy) h

end Coord

theorem gmap_mul {D : D7} (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  simp only [Formalism.HermitianLatticesTheory.gmap]
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) Λ = Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap]
  exact Submodule.map_id Λ

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

theorem gterm_eq_of_rel {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {t t' : GTerm X u u' F0 F0' what₂ rows'}
    (h₁ : t.lam = t'.lam) (h₂ : t.lam' = t'.lam')
    (h : ∃ a ∈ NLam t.lam (lf D F0), ∃ b ∈ NLam t.lam' (lf D F0'), t'.lin = a * t.lin * b) : t = t' := by
  obtain ⟨l, hl, l', hl', cl⟩ := t
  obtain ⟨k, hk, k', hk', ck⟩ := t'
  simp only at h₁ h₂
  subst h₁ h₂
  obtain ⟨a, ha, b, hb, e⟩ := h
  have hc : cl = ck := by
    rw [← Quot.out_eq cl, ← Quot.out_eq ck]
    exact Quot.sound ⟨a, ha, b, hb, e⟩
  subst hc
  rfl

theorem term_eq_iff_lRel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t t' : TauC Y u u') n m n' m', t.lam = t₀.lam → t.lam' = t₀.lam' → t'.lam = t₀.lam → t'.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → n' ∈ NRat (lf D (X.Fu u)) ∧ m' ∈ NRat (lf D (X.Fu u')) ∧ t'.lin = n'⁻¹ * t₀.lin * m' → (t = t' ↔ G.LRel (c.lat (ρ * n) t.lam) (c.lat (ρ * n') t'.lam)) := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t t' n m n' m' e₁ e₂ e₃ e₄ hnm hnm'
  obtain ⟨hn, hm, ht⟩ := hnm
  obtain ⟨hn', hm', ht'⟩ := hnm'
  have hI := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
  have hN := hI.1
  have hN' := hI.2.1
  constructor
  · rintro rfl
    have key : n' * n⁻¹ = t₀.lin * (m' * m⁻¹) * t₀.lin⁻¹ := by
      calc n' * n⁻¹ = n' * (n⁻¹ * t₀.lin * m) * m⁻¹ * t₀.lin⁻¹ := by group
        _ = n' * (n'⁻¹ * t₀.lin * m') * m⁻¹ * t₀.lin⁻¹ := by rw [← ht, ← ht']
        _ = t₀.lin * (m' * m⁻¹) * t₀.lin⁻¹ := by group
    refine ⟨c.grp ρ (n' * n⁻¹), ?_, ?_⟩
    · have h1 : c.grp ρ (n' * n⁻¹) ∈ G.N := by
        rw [grp_mul, grp_inv]
        exact G.N.mul_mem ((hN n').1 hn') (G.N.inv_mem ((hN n).1 hn))
      have h2 : c.grp ρ (n' * n⁻¹) ∈ G.N' := by
        rw [key, ← grp_conj, grp_mul, grp_inv]
        exact G.N'.mul_mem ((hN' m').1 hm') (G.N'.inv_mem ((hN' m).1 hm))
      exact mem_rat_inf _ _ _ h1 h2
    · rw [lat_map_grp]
      congr 2
      group
  · rintro ⟨s, hs, hmap⟩
    set σ := ((ρ.trans c.e).trans s).trans (ρ.trans c.e).symm with hσdef
    have hsσ : c.grp ρ σ = s := grp_surj c ρ s
    have hsN : s ∈ G.N := rat_mono _ (fun p => inf_le_left) hs
    have hsN' : s ∈ G.N' := rat_mono _ (fun p => inf_le_right) hs
    have hΛ : Formalism.HermitianLatticesTheory.gmap (σ * n) t.lam = Formalism.HermitianLatticesTheory.gmap n' t.lam := by
      rw [← hsσ, lat_map_grp, e₃, ← e₁, lat_mul, lat_mul] at hmap
      exact lat_inj c ρ hmap
    set a := n'⁻¹ * σ * n with ha_def
    set b := m⁻¹ * t₀.lin⁻¹ * σ⁻¹ * t₀.lin * m' with hb_def
    have haN : a ∈ NRat (lf D (X.Fu u)) := by
      rw [hN, ha_def, grp_mul, grp_mul, grp_inv, hsσ]
      exact G.N.mul_mem (G.N.mul_mem (G.N.inv_mem ((hN n').1 hn')) hsN) ((hN n).1 hn)
    have hσ' : c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * σ * t₀.lin) = s := by
      rw [grp_conj, ← hsσ]
      congr 1
      group
    have hbN : b ∈ NRat (lf D (X.Fu u')) := by
      have eb : b = m⁻¹ * (t₀.lin⁻¹ * σ * t₀.lin)⁻¹ * m' := by rw [hb_def]; group
      rw [hN', eb, grp_mul, grp_mul, grp_inv, grp_inv, hσ']
      exact G.N'.mul_mem (G.N'.mul_mem (G.N'.inv_mem ((hN' m).1 hm)) (G.N'.inv_mem hsN')) ((hN' m').1 hm')
    have haΛ : Formalism.HermitianLatticesTheory.gmap a t.lam = t.lam := by
      rw [ha_def, mul_assoc, gmap_mul, hΛ, ← gmap_mul, inv_mul_cancel, gmap_one]
    have haΛ' : Formalism.HermitianLatticesTheory.gmap a⁻¹ t.lam = t.lam := by
      conv_lhs => rw [← haΛ]
      rw [← gmap_mul, inv_mul_cancel, gmap_one]
    have hl : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    have hl' : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam := t'.rep.2.2.2.1
    have eb2 : b = t.lin⁻¹ * a⁻¹ * t'.lin := by
      rw [hb_def, ha_def, ht, ht']; group
    have hbΛ : Formalism.HermitianLatticesTheory.gmap b t.lam' = t.lam' := by
      have hl'' : Formalism.HermitianLatticesTheory.gmap t'.lin t.lam' = t.lam := by rw [e₂, ← e₄, hl', e₃, e₁]
      rw [eb2, gmap_mul, gmap_mul, hl'', haΛ', ← hl, ← gmap_mul, inv_mul_cancel, gmap_one]
    refine gterm_eq_of_rel (by rw [e₁, e₃]) (by rw [e₂, e₄]) ⟨a, ⟨⟨haN.1, haΛ⟩, haN.2⟩, b, ⟨⟨hbN.1, hbΛ⟩, hbN.2⟩, ?_⟩
    rw [ht, ht', ha_def, hb_def]
    group

end GlobalTheory.HL.TermOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermsSameInnerLattices
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.lat_gmap {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T}
    {F0' : LFlag (D.sp.Y 0) D.R.rS T'} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G)
    (σ τ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    c.lat σ (Formalism.HermitianLatticesTheory.gmap τ Λ) = c.lat (σ * τ) Λ := by
  unfold GCoord.lat Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem GFrames.datOf_N_fst (G : GFrames A r k) {g : G.GLV} (hg : g ∈ G.N) (Γ : G.Lt) (p) :
    (G.datOf (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) p).1 = (G.datOf Γ p).1 := by
  have hloc : ∀ q, ∃ g' ∈ (G.S q).N, A.Ext q g g' := hg
  obtain ⟨g', hgN, hext⟩ := hloc p
  unfold Places.Ext at hext
  have := (A.loc p).lf
  have := (A.loc p).char0
  have hmove : g' • A.lat p Γ = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    unfold Places.lat
    rw [Submodule.smul_span, Submodule.map_coe, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    apply congrArg (fun f => f '' (Γ : Set G.V))
    funext x
    simp [hext]
  unfold GFrames.datOf
  rw [← hmove]
  exact (_root_.GlobalTheory.HL.DatumOf.main (A.L p) r k (G.S p)).2.2.1 g' hgN (A.lat p Γ)

theorem GFrames.datOf_N'_snd (G : GFrames A r k) {g : G.GLV} (hg : g ∈ G.N') (Γ : G.Lt) (p) :
    (G.datOf (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) p).2.1 = (G.datOf Γ p).2.1 := by
  have hloc : ∀ q, ∃ g' ∈ (G.S q).N', A.Ext q g g' := hg
  obtain ⟨g', hgN, hext⟩ := hloc p
  unfold Places.Ext at hext
  have := (A.loc p).lf
  have := (A.loc p).char0
  have hmove : g' • A.lat p Γ = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    unfold Places.lat
    rw [Submodule.smul_span, Submodule.map_coe, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    apply congrArg (fun f => f '' (Γ : Set G.V))
    funext x
    simp [hext]
  unfold GFrames.datOf
  rw [← hmove]
  exact (_root_.GlobalTheory.HL.DatumOf.main (A.L p) r k (G.S p)).2.2.2.1 g' hgN (A.lat p Γ)
end Loc

theorem datOf_dcoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).1 = (G.datOf (c.lat ρ t₀.lam) p).1 ∧ (G.datOf (c.lat (ρ * n) t.lam) p).2.1 = (G.datOf (c.lat ρ t₀.lam) p).2.1 := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hB G c t₀ ρ U U' hmv t n m hlam hlam' hnm p
  obtain ⟨hn, hm, hlin⟩ := hnm
  obtain ⟨P1, P2, P3, -⟩ := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hB G c t₀ ρ U U' hmv

  have hrel : ∀ s : TauC Y u u', Formalism.HermitianLatticesTheory.gmap (GTerm.lin s) s.lam' = s.lam :=
    fun s => (Quot.out s.cls).property.2.2.1
  constructor
  · rw [P3, hlam]
    exact GFrames.datOf_N_fst G ((P1 n).1 hn) _ p
  · have e1 : c.lat (ρ * n) t.lam = (c.lat (ρ * GTerm.lin t₀) t₀.lam').map
        (((c.grp (ρ * GTerm.lin t₀) m : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) := by
      rw [← P3, ← hrel t, GCoord.lat_gmap, hlin, hlam']
      congr 1
      group
    have e2 : c.lat (ρ * GTerm.lin t₀) t₀.lam' = c.lat ρ t₀.lam := by
      rw [← GCoord.lat_gmap, hrel t₀]
    rw [e1, ← e2]
    exact GFrames.datOf_N'_snd G ((P2 m).1 hm) _ p

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalCompactReductionStandardFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabPin

theorem frameRed_exists : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ c red, FrameRed X h t PY c red := by
  intro D X h t PY hF hstd hι
  obtain ⟨c, fr, hB⟩ := _root_.GlobalTheory.FixedConj.exists_conj_frames D X h t PY hF hstd hι (_root_.GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq D.host.E)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.RowLev.exists_red_actsBy X.B.I D.R.r D.host.g D.nd.PlG
    (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) fr X.n_eq (_root_.GlobalTheory.RowLev.FixedChoice.isChoice_wB_plGw D X)
  have hg : X.B.g = D.host.g 0 * D.host.g 1 := X.g_eq
  refine ⟨c, ρ.toFun, ⟨?_, ?_, ?_, ?_⟩, fun kv => _root_.GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D kv, ?_⟩
  · intro k hk kv
    exact (Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ k _).2
      (_root_.GlobalTheory.RowLev.redMat0_of_actsAs X.B.I D.R.r (D.host.g kv.1) _ (fr kv.1 kv.2) k hk _ (hρ k hk kv.1 kv.2))
  · exact ρ.map_mul
  · exact ρ.surj
  · intro k hk
    rw [hg]
    exact ρ.ker k hk
  · intro kv s hs x γ hx
    obtain ⟨hK, hact, hoth⟩ := hB kv s hs x γ hx
    set k := (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 with hk
    have hfin : (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).1 = 1 := by
      apply _root_.GlobalTheory.RealTrivIota.iotaX_fst_eq_one_of_mem_GfC D X h
      have hn : (GfC (D.sp.Y 0)).Normal := by unfold GfC; infer_instance
      exact hn.conj_mem _ (PY.into _) t
    refine ⟨k, hK, ?_, ?_, ?_⟩
    · obtain ⟨g, hg'⟩ : ∃ g : Formalism.L2.Theta.GA D (D.sp.Y 0), g = PY.ψ (c * x * c⁻¹) := ⟨_, rfl⟩
      have e : (Formalism.L2.SG.RowsJoinPinned.iotaX X h).symm (1, k) = MulAut.conj t g := by
        rw [ContinuousMulEquiv.symm_apply_eq, hg']
        exact Prod.ext hfin.symm rfl
      show PY.ψ (c * x * c⁻¹) = (t⁻¹ * (Formalism.L2.SG.RowsJoinPinned.iotaX X h).symm (1, k) * t : Formalism.L2.Theta.GA D (D.sp.Y 0))
      rw [e, MulAut.conj_apply, ← hg']
      exact (by group : g = t⁻¹ * (t * g * t⁻¹) * t)
    · exact Units.ext (GlobalTheory.RowLev.PlFrame.ActsAs.unique (fr kv.1 kv.2) hK (hρ k hK kv.1 kv.2) hact)
    · intro kv' hne
      exact Units.ext (GlobalTheory.RowLev.PlFrame.ActsAs.unique (fr kv'.1 kv'.2) hK (hρ k hK kv'.1 kv'.2) (hoth kv' hne))

end GlobalTheory.LabPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTupleNondegenerateGramStep
section
noncomputable section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace GlobalTheory.RowNGClosed

theorem ooVanish_all : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word),
    Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X) := by
  intro D X Y u u' t ht
  exact Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
    Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht

theorem hermitian_tuple_nondegenerate_gram_step : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    have := X.n_eq; have := D.R.rS_two; have := D.R.r_eq; have := D.R.k_ge; omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => congrFun (congrFun X.B.I.J_herm i) j
  obtain ⟨X0, h0⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  convert h0 using 2
  ext a b
  rfl

theorem closedSteps : CorankOneEquivalence ∧ StepNormals ∧ StepPoints ∧ StepNormOne ∧ NondegenerateGramTuple := by
  have h1 : StepNormOne := VanishingOrbitalPoints.stepNormOne_of_ooVanish ooVanish_all
  exact ⟨CorankRelation.corankOne_equivalence_holds,
    NormalInvariants.stepNormals_of NormalVectorPairings.NmlInv_holds NormalCount.NormCount_holds h1,
    VanishingOrbitalPoints.stepPoints_of_ooVanish ooVanish_all, h1, hermitian_tuple_nondegenerate_gram_step⟩

end GlobalTheory.RowNGClosed
end
end

