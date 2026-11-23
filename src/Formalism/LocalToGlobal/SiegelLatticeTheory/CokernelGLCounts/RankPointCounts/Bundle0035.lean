module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfSteps

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPh
section
noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf
open Classical

section Val2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalRing E]

theorem local_phase_orbit_eq (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1))
    (xy xy' : (Loc.IL (m + 1) → E) × (Loc.IN a → E))
    (l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hq : zAt a xy' = l * zAt a xy * ρ) :
    M.psiR (Loc.simpleLow (Loc.uLow xy'.1) + Loc.simpleUp (Loc.uUp a xy'.2)) = M.psiR (Loc.simpleLow (Loc.uLow xy.1) + Loc.simpleUp (Loc.uUp a xy.2)) := by
  have hψ : ∀ x ∈ M.R, M.psiR x = 1 := fun r hr => by
    simpa using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  have hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l * rI a (Loc.uLow xy.1)) :=
    Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))
  have hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy.2) * rI a ρ) :=
    Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))
  have hv : Formalism.DoubleCosetMeasures.IsLowUni (rI a (Loc.uLow xy'.1)) := lowUni_rI a (uLow_lowUni xy'.1)
  have hu : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy'.2)) := upUni_rI a (uUp_upUni a xy'.2)
  have hvPu : rI a (Loc.uLow xy'.1) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * rI a (Loc.uUp a xy'.2) =
      (rI a l * rI a (Loc.uLow xy.1)) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
        (rI a (Loc.uUp a xy.2) * rI a ρ) := by
    have h := congrArg (rI a) hq
    unfold zAt at h
    simp only [rI_mul, rI_mat] at h
    rw [h]
    simp only [Matrix.mul_assoc]
  have hLd : IsUnit (rI a l * rI a (Loc.uLow xy.1)).det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one
  have hUd : IsUnit (rI a (Loc.uUp a xy.2) * rI a ρ).det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one
  have hfix : ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * rI a (Loc.uLow xy'.1)) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
      (rI a (Loc.uUp a xy'.2) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) =
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
    calc _ = (rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a (Loc.uLow xy'.1) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          rI a (Loc.uUp a xy'.2)) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a l * rI a (Loc.uLow xy.1))) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          ((rI a (Loc.uUp a xy.2) * rI a ρ) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) := by
          rw [hvPu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]
  have h0 := Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _
    (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.DoubleCosetMeasures.isUpUni_mul E hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)) hfix
  have sa := Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum
  rw [(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)] at h0
  have hLi := (sa (rI a l * rI a (Loc.uLow xy.1))⁻¹ (rI a l * rI a (Loc.uLow xy.1))).1
    (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo
  rw [Matrix.nonsing_inv_mul _ hLd, sLow_one] at hLi
  have hUi := (sa (rI a (Loc.uUp a xy.2) * rI a ρ) (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹).2
    hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)
  rw [Matrix.mul_nonsing_inv _ hUd, sUp_one] at hUi
  rw [(sa _ _).1 (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))] at hLi
  rw [(sa _ _).2 (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))] at hUi
  have hph : Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy'.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy'.2)) =
      Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) +
      (Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy.2))) := by
    linear_combination h0 + hLi + hUi
  have h1 : Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) ∈ M.R :=
    add_mem (by rw [sLow_rI]; exact sLow_mem M.R _ hl.2.2) (by rw [sUp_rI]; exact sUp_mem M.R _ hρ.2.2)
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq,
    Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq, ← sLow_rI a (Loc.uLow xy'.1), ← sUp_rI a (Loc.uUp a xy'.2),
    ← sLow_rI a (Loc.uLow xy.1), ← sUp_rI a (Loc.uUp a xy.2), hph, AddChar.map_add_eq_mul, hψ _ h1, one_mul]

end Val2

end Formalism.L2.SG.Pf.LocOrbCut

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf
open Classical ValuativeRel

theorem phase_class_holds {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) : PhCls M δ := by
  intro T T' p w Y Y' hOK hY hO hO' hmem
  obtain ⟨w₀, hw₀, xy0, hxy0⟩ := hO
  obtain ⟨l, ρ, hl, hρ, hY'⟩ := hmem
  have hmat : w₀.mat = modMat δ T T' p w + shM δ T T' p w := modShift_holds δ T T' p w w₀ hw₀
  unfold phL
  rw [hw₀]
  try dsimp only
  by_cases h' : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y' = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2
  · by_cases h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2
    · rw [dite_eq_left h', dite_eq_left h]
      congr 1
      have e1 := zAt_eq hmat h.choose
      have e2 := zAt_eq hmat h'.choose
      rw [← h.choose_spec] at e1
      rw [← h'.choose_spec] at e2
      have hq : zAt w₀ h'.choose = l * zAt w₀ h.choose * ρ := by
        rw [e1, e2, hY', mul_add, add_mul,
          mul_shM l ρ (last_of_low l hl.1 hl.2.1) (last_of_up ρ hρ.1 hρ.2.1)]
      haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
      exact LocOrbCut.local_phase_orbit_eq (M p) hOK w₀ h.choose h'.choose l ρ hl hρ hq
    · exact absurd ⟨xy0, hxy0⟩ h
  · obtain ⟨w₁, hw₁, xy, hxy⟩ := hO'
    rw [hw₀] at hw₁
    cases hw₁
    exact absurd ⟨xy, hxy⟩ h'

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefVol
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB MeasureTheory
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section VolStep

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolIdxProd : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    EligAt γ w → PairVal.NormRep γ w F' L U →
      PairVal.volIdx D u u' F0 what₂ δ M γ w F' L =
        ((PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard : ℝ) *
          ∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w
            (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

end VolStep

section Good

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}


open Formalism.L2.SG.Pf.LocUnramB in
theorem wtL_good (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p)
    (hg : Good δ M w p) {Y : MatP D p} (hYi : IntP M p Y) (hYo : InOrbP δ T T' p w Y) :
    wtL M δ T T' p w Y = 1 := by
  obtain ⟨w₀, hw₀, xy0, hxy0⟩ := hYo
  have hint := orb_int T T' w p hA hg w₀ hw₀
  obtain ⟨h1, h2⟩ := hint xy0.1 xy0.2 (by rw [← hxy0]; exact hYi)
  have hO : kkOrb M p Y = kkOrb M p (modMat δ T T' p w) :=
    kkOrb_eq p (isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow _)) h1
      (isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp _ _)) h2 hxy0
  set H := monoW T T' w p hA hg
  have hOK := hA.1
  have := hOK.haar.sf
  unfold wtL
  rw [hw₀]
  simp only
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y} =
      (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) ×ˢ
        (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]
    rw [hO]
    constructor
    · rintro ⟨l, ρ, hl, hρ, he⟩
      have hYint : ∀ i j, (Loc.uLow x * modMat δ T T' p w * Loc.uUp w₀ y) i j ∈ (M p).R := by
        rw [he]; exact int_mul _ (int_mul _ hl.2.2 H.int) hρ.2.2
      obtain ⟨h1, h2⟩ := hint x y hYint
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h1 i.1.1 i.1.2
        simp only [Loc.uLow, if_neg (ne_of_gt i.2), dif_pos i.2] at this
        exact this
      · have := h2 i.1.1 i.1.2
        simp only [Loc.uUp, if_neg (ne_of_lt i.2.1), dif_pos i.2] at this
        exact this
    · rintro ⟨hx, hy⟩
      have hL := isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow x)
      have hN := isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp w₀ y)
      refine ⟨Loc.uLow x, Loc.uUp w₀ y, ⟨hL.1, hL.2, fun a b => ?_⟩, ⟨hN.1, hN.2, fun a b => ?_⟩, rfl⟩
      · unfold Loc.uLow
        split_ifs
        · exact (M p).R.one_mem
        · exact hx _
        · exact (M p).R.zero_mem
      · unfold Loc.uUp
        split_ifs
        · exact (M p).R.one_mem
        · exact hy _
        · exact (M p).R.zero_mem
  rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  simp [hOK.haar.volR]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem wtL_finite (hA : ∀ p, Agree δ M p) (hC : LocClsE M δ u u' F0 what₂)
    {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)} (hγ : EligAt γ w) :
    (Function.mulSupport fun p =>
      (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)).Finite := by
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine hall.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq]
  intro hg
  apply hp
  obtain ⟨hyI, hyO⟩ := hC γ w hγ p
  show (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) = 1
  rw [wtL_good _ _ w p (hA p) hg hyI hyO, Complex.ofReal_one]

theorem volProd_of (hA : ∀ p, Agree δ M p)
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hC : LocClsE M δ u u' F0 what₂)
    (hVP : VolIdxProd M δ u u' F0 what₂) : VolProd M δ u u' F0 what₂ := by
  intro γ w hγ
  refine ⟨wtL_finite hA hC hγ, ?_⟩
  have hγ0 := hγ
  have hrel : γ.relevant := PCount.eligRel_holds γ w hγ
  obtain ⟨⟨hgen, -⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat hrel hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by unfold zT; rw [hn]
  have hv : PairVal.vRdef D u u' F0 what₂ δ M γ =
      PairVal.volIdx D u u' F0 what₂ δ M γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 := by
    unfold PairVal.vRdef; rw [dif_pos ⟨hrel, hgen, hex⟩]
  have hspec := hex.choose_spec
  obtain ⟨hRep, -, hL, hU, e⟩ := hspec
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
  have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
    hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
  have hγ' : EligAt γ hex.choose.1 := hw ▸ hγ0
  have key := hVP hA hT hrows γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 hγ' hex.choose_spec
  have hcast : ((∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℝ) : ℂ) =
      ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) :=
    Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _
  rw [← hcast, hv, key, ← hw]
  simp only [yT, hz, Complex.ofReal_mul, Complex.ofReal_natCast]
  rfl

end Good

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountWt
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf MeasureTheory
open Classical

variable {D : Formalism.BasicNotions.D7}

theorem wtL_eq_wtZ (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (ha : modPt δ T T' p w = some a) (Y : MatP D p) :
    wtL M δ T T' p w Y = wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) := by
  have hmat : a.mat = modMat δ T T' p w + shM δ T T' p w := modShift_holds δ T T' p w a ha
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN a → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp a xy.2 ∈ kkOrb M p Y} =
      {xy | zAt a xy ∈ orbR (M p) (Y + shM δ T T' p w)} := by
    ext xy
    simp only [Set.mem_ofPred_eq]
    rw [mem_orbR_iff M δ T T' p w Y (zAt a xy), zAt_eq hmat xy, add_sub_cancel_right]
  unfold wtL wtZ muA
  simp only [ha]
  rw [hset]

theorem wtL_count (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (hOK : (M p).OK) (ha : modPt δ T T' p w = some a) {Y : MatP D p} (hY : ∀ i j, Y i j ∈ (M p).R) :
    {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.Finite ∧
    wtL M δ T T' p w Y = ({q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.ncard : ℝ) := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hZ0 : ∀ i j, (Y + shM δ T T' p w) i j ∈ (M p).R := fun i j =>
    add_mem (hY i j) (shM_mem M δ T T' p w i j)
  obtain ⟨hfin, hsum⟩ := LocOrbCut.wt_gen (M p) hOK a (Y + shM δ T T' p w) hZ0
  set S := {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)} with hSdef
  have hsupp : (Function.support (fun q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) =>
      if LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w) then (1 : ℂ) else 0)) = S := by
    ext q
    simp [hSdef]
  rw [hsupp] at hfin
  refine ⟨hfin, ?_⟩
  rw [wtL_eq_wtZ M δ ha Y]
  have hc : (wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) : ℂ) = (S.ncard : ℂ) := by
    rw [hsum, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [hsupp]; simp)]
    rw [Finset.sum_boole, Set.ncard_eq_toFinset_card S hfin]
    congr 2
    exact Finset.filter_true_of_mem (fun q hq => hfin.mem_toFinset.1 hq)
  exact_mod_cast hc

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadMAddCorner
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

section LeadLemmas

variable {K K' : Type*} [CommRing K] [CommRing K']

theorem det_map' {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) : (A.map f).det = f A.det :=
  (RingHom.map_det f A).symm

theorem leadM_top {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : leadM A (r + 1) = A.det := by
  unfold leadM; rw [dite_eq_left le_rfl]; rfl

theorem leadM_map {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (A.map f) l = f (leadM A l) := by
  unfold leadM
  split_ifs with hl
  · rw [RingHom.map_det]; rfl
  · simp

theorem leadM_smul {m : ℕ} (c : K) (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (c • A) l = c ^ l * leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [show (c • A).submatrix (Fin.castLE hl) (Fin.castLE hl) = c • A.submatrix (Fin.castLE hl) (Fin.castLE hl)
      from rfl, Matrix.det_smul, Fintype.card_fin]
  · simp

theorem leadM_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) K) (l : ℕ) : leadM A.transpose l = leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [← Matrix.det_transpose]; rfl
  · rfl

theorem castLE_ne_last {r : ℕ} (a : Fin r) : Fin.castLE (Nat.le_succ r) a ≠ Fin.last r := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := a.isLt
  simp at h1
  omega

theorem leadM_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    leadM (A + c • Ecorner r) r = leadM A r := by
  unfold leadM
  rw [dite_eq_left (Nat.le_succ r), dite_eq_left (Nat.le_succ r)]
  congr 1
  ext a b
  simp [Ecorner, castLE_ne_last a]

theorem det_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (A + c • Ecorner r).det = A.det + c * leadM A r := by
  have hE : A + c • Ecorner r =
      A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ecorner]
      · simp [Ecorner, hb]
    · simp [Ecorner, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r)) := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
    rfl
  rw [hs, leadM, dite_eq_left (Nat.le_succ r)]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

end LeadLemmas

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem leadZZ_model (M : Loc.Model F E) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (leadM Zh r = 0 ↔ leadM (Loc.HermSp.ZZplusOf M Zh T T') r = 0) ∧
    (IsUnit (leadM Zh r) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf M Zh T T') r)) ∧
    (leadM Zh r = 0 → IsUnit (leadM Zh (r + 1)) → IsUnit (Loc.HermSp.ZZplusOf M Zh T T').det) := by
  rcases hs : M.split with _ | g
  · have e : Loc.HermSp.ZZplusOf M Zh T T' = Zh := by unfold Loc.HermSp.ZZplusOf; rw [hs]
    rw [e, ← leadM_top]
    exact ⟨Iff.rfl, Iff.rfl, fun _ h => h⟩
  · set q : F := (g.q : F) with hq
    have hq0 : q ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
    let π₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
    let π₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
    have hzero : ∀ x : E, x = 0 ↔ π₁ x = 0 ∧ π₂ x = 0 := by
      intro x
      constructor
      · rintro rfl; simp
      · rintro ⟨h1, h2⟩
        have : g.e x = 0 := Prod.ext h1 h2
        exact (map_eq_zero_iff g.e g.e.injective).1 this
    have hunit : ∀ x : E, IsUnit x ↔ π₁ x ≠ 0 ∧ π₂ x ≠ 0 := by
      intro x
      rw [← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
      rfl
    have e1 : (Loc.HermSp.ZZplusOf M Zh T T').map π₁ = q⁻¹ • Zh.map π₁ + (T / q) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have e2 : (Loc.HermSp.ZZplusOf M Zh T T').map π₂ = (-q⁻¹) • (Zh.map π₂).transpose + (-(T' / q)) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have l1 : π₁ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = q⁻¹ ^ r * π₁ (leadM Zh r) := by
      rw [← leadM_map, e1, leadM_add_corner, leadM_smul, leadM_map]
    have l2 : π₂ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = (-q⁻¹) ^ r * π₂ (leadM Zh r) := by
      rw [← leadM_map, e2, leadM_add_corner, leadM_smul, leadM_transpose, leadM_map]
    have hq1 : q⁻¹ ^ r ≠ 0 := pow_ne_zero _ (inv_ne_zero hq0)
    have hq2 : (-q⁻¹) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))
    refine ⟨?_, ?_, ?_⟩
    · rw [hzero, hzero (leadM _ r), l1, l2, mul_eq_zero, mul_eq_zero]
      simp [hq0]
    · rw [hunit, hunit (leadM _ r), l1, l2]
      simp [hq0]
    · intro h0 hu
      rw [leadM_top] at hu
      rw [hunit] at hu ⊢
      have z := (hzero _).1 h0
      rw [← det_map', ← det_map', e1, e2, det_add_corner, det_add_corner, leadM_smul, leadM_smul,
        leadM_transpose, leadM_map, leadM_map, z.1, z.2, Matrix.det_smul, Matrix.det_smul,
        Matrix.det_transpose, det_map', det_map']
      simp only [mul_zero, add_zero, Fintype.card_fin]
      exact ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hu.1,
        mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))) hu.2⟩

end Model

theorem leadZZ_holds {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : LeadZZ Zd :=
  fun p Zh T T' => leadZZ_model (Zd.M p) Zh T T'

end Formalism.L2.SG.Pf.PCount
end
end

