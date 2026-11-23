module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0098
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TypedSplit

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BaseAt
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def BaseAt (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) : Prop :=
  ∃ c : UP p, phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = (c : GG p) • a.mat ∧
    ∀ x : UP p, ((x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) =
      phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) ↔ (x : GG p) • a.mat = a.mat)

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemXflagMapLF
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Xa_mapFlag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (j : ℕ) (x : S.V) :
    x ∈ (mapFlag γ hγ F).Xa j ↔ γ.symm x ∈ F.Xa j := by
  have h1 : (mapFlag γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V) := by
    unfold FlagG.Xa
    rw [Submodule.map_span, ← Set.image_comp]
    rfl
  rw [h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

theorem mem_Xflag_mapLF {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) (x : S.V) :
    x ∈ Xflag (mapLF γ F) j ↔ γ.symm x ∈ Xflag F j := by
  unfold Xflag mapLF
  rw [dite_eq_left hγ]
  exact mem_Xa_mapFlag γ hγ F.fl j x

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem NLam_SRat {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (D.sp.Y 0) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ F) : n ∈ SRat F := by
  obtain ⟨hA, hf, hp⟩ := hn
  refine ⟨hA.1, hf, hp _ ?_⟩
  refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
  rw [hT_swap F.fl.z x, hT_z_X F.fl hx, star_zero]

theorem NLam_transport (t : TauC Y u u') {Λ : Submodule (𝓞 D.host.E) (VS D).V} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hm : m ∈ NLam Λ t.frame) : t.lin⁻¹ * m * t.lin ∈ SRat (lf D (X.Fu u')) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hS := NLam_SRat hm
  obtain ⟨hmi, hmf, hmz⟩ := hS
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ) hmi) hγ,
    fun j x hx => ?_, ?_⟩
  · have hx' : t.lin x ∈ Xflag t.frame (j + 1) :=
      (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) (j + 1) _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hx)
    have h := hmf j _ hx'
    have h' := (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) j _).1 h
    rw [map_sub, LinearEquiv.symm_apply_apply] at h'
    exact h'
  · have h2 : m t.frame.fl.z - t.frame.fl.z ∈ t.frame.fl.X := hmz
    have h3 := (mem_frameX Y t _).1 h2
    rw [map_sub, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply] at h3
    show t.lin.symm (m (t.lin (X.Fu u').z)) - (X.Fu u').z ∈ _
    exact h3

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneDir
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneDir2

variable {D : D7} (Zd : LocDat D)

theorem nm_last (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (b : Fin (D.R.rS + 1)) :
    (fmat D G n * fmat D G₁ m - 1) (Fin.last D.R.rS) b = 0 := by
  have hNU := (stepExp D Λ G n hn).1
  have hMU := (stepExp D Λ G₁ m hm).1
  rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.last D.R.rS)]
  · rw [(hNU _ _).2 rfl, one_mul, Matrix.one_apply]
    by_cases hb : Fin.last D.R.rS = b
    · rw [(hMU _ _).2 hb, if_pos hb, sub_self]
    · have hlt : b < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last b) (Ne.symm hb)
      rw [(hMU _ _).1 hlt, if_neg hb, sub_self]
  · intro c _ hc
    have hlt : c < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last c) hc
    rw [(hNU _ _).1 hlt, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem one_dir {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hRL : IsRowLat D F0 Λ)
    (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hP₁ : Formalism.L2.SG.TermDef.PD D Λ (lf D F0) u' F₁) (hA₁ : AdmWit Λ (gS D) (lf D F0) F₁ 1)
    (hA₂ : AdmWit Λ (gS D) (lf D F0) F₂ 1) (hdc : Formalism.L2.SG.TermDef.DCRel Λ (lf D F0) F₁ F₂) (p : PlF D) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Zd.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Zd.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL (lf D F0) F₂) * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL (lf D F0) F₁) * Formalism.L2.SG.LsDatumB.sgnP p) *
          ρ := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hdc
  have hEn := stepExp D Λ (lf D F0) n hn
  have hEm := stepExp D Λ F₁ m hm
  have hrel := stepGram D (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hEn.2 hEm.2 hfr
  have hXS : XLam Λ (lf D F0) = XS D (lf D F0).fl := hRL.2.2
  have hz : (lf D F0).fl.z ∈ Λ := hRL.2.1.2.2.1.1
  have hNb := entry_mem D Λ (lf D F0) n hn hXS hz
  have hMb := entry_mem D Λ F₁ m hm hP₁.2.2.2 hP₁.1.1
  have hNU : ∀ a b, b < a → fmat D (lf D F0) n a b = 0 := fun a b h => (hEn.1 a b).1 h
  have hNd : ∀ a, fmat D (lf D F0) n a a = 1 := fun a => (hEn.1 a a).2 rfl
  have hMU : ∀ a b, b < a → fmat D F₁ m a b = 0 := fun a b h => (hEm.1 a b).1 h
  have hMd : ∀ a, fmat D F₁ m a a = 1 := fun a => (hEm.1 a a).2 rfl
  cases hs : (Zd.M p).split with
  | none => exact modeL Zd p hs u u' _ _ _ _ hNU hNd hMU hMd hNb hMb hrel
  | some g =>
    refine modeG Zd p g hs u u' _ _ _ _ hNU hNd hMU hMd hNb hMb hrel ?_
    obtain ⟨sg, hsg, -, hq⟩ := typed_split Zd p hs
    have hgP := gS_mem_of_split p hsg
    have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
      have : gS D ≠ 0 := by
        unfold Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact_mod_cast this
    have hφ := fun a => Formalism.L2.SG.Pf.BBTie.bt_typed_frFac Zd (Formalism.L2.SG.Pf.locEqC_holds D Zd)
      (Formalism.L2.SG.Pf.locDiffC_holds D Zd) p F0 Λ hRL.2.1.1.fg hRL.2.2 hRL.2.1.2.2.2 hgP a
    have hκ := (Formalism.L2.SG.Pf.BBTie.bt_kappa Zd p sg hsg).1
    have hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0 := by
      intro h
      exact sg.q_irr.ne_zero (Subtype.ext h)
    have hOO : (Zd.M p).L.O = (D.s.atP p).O := (Zd.agree p).2.2.2.1
    rw [locU_mul, locU_sub_one]
    intro i j
    rw [locU_apply]
    obtain ⟨w, hwO, hw⟩ := (hφ i).2
    have hinv : Ring.inverse (frFac Zd.δ p i) = w := by
      calc Ring.inverse (frFac Zd.δ p i) = (w * frFac Zd.δ p i) * Ring.inverse (frFac Zd.δ p i) := by
            rw [hw, one_mul]
        _ = w := by rw [mul_assoc, frFac_mul_inv, mul_one]
    induction i using Fin.lastCases with
    | last =>
      rw [nm_last Λ (lf D F0) F₁ n m hn hm j, map_zero, mul_zero, zero_mul]
      exact ⟨0, Subring.zero_mem _, by rw [mul_zero]⟩
    | cast d =>
      set x := (fmat D (lf D F0) n * fmat D F₁ m - 1) d.castSucc j with hxdef
      have hint : (D.s.atP p).ιE (x / (gS D : D.host.E)) ∈ (Zd.M p).L.O := by
        rw [hOO]
        exact iota_mem_O p _ (fun P hP => cong_at D Λ (lf D F0) F₁ F₂ n m hn hm hfr hRL.2.1.2.2.2 hP₁.2.2.1
          hA₁ hA₂ hP₁.1.1 P (hgP P hP) hg d j)
      have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) *
          ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
            (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) * (D.s.atP p).ιE (x / (gS D : D.host.E))) := by
        rw [← mul_assoc, ← mul_assoc, ← map_mul (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), mul_inv_cancel₀ hq0,
          map_one, one_mul, ← map_mul, mul_div_cancel₀ x hg]
      refine ⟨w * ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
          (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) * (D.s.atP p).ιE (x / (gS D : D.host.E))) * frFac Zd.δ p j,
        Subring.mul_mem _ (Subring.mul_mem _ hwO (Subring.mul_mem _ hκ hint)) (hφ j).1, ?_⟩
      rw [hinv, hx, hq]
      ring

end OneDir2

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMain
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem mem_stSet_of_pat (a : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a)
    (hpat : ∀ i j, Formalism.L2.SG.Pf.fσ w j < Formalism.L2.SG.Pf.fσ w i → a i j = 0) :
    ∃ b : Formalism.L2.SG.PairVal.MatR D, IsUpUni b ∧ a * ptMat w * b = ptMat w := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ x, σ (σ x) = x := Formalism.L2.SG.Pf.fσ_fσ w
  set ν : Fin (D.R.rS + 1) → D.host.E := fun x => Formalism.L2.SG.Pf.pv w.1 x
  have hν : ∀ x, IsUnit (ν x) := fun x => isUnit_iff_ne_zero.2 (Formalism.L2.SG.Pf.pv_ne' w x)
  have hfix := fix_cOf hσ ν hν a
  obtain ⟨hc1, hc2⟩ := cOf_up hσ ν a (fun i => (ha i i).2 rfl) hpat hν
  have hcU : IsUpUni (cOf σ ν a) := fun i j => ⟨fun h => hc2 i j h, fun h => by subst h; exact hc1 i⟩
  obtain ⟨hbU, -, hcb⟩ := ZsVolGrp.isUpUni_inv hcU
  refine ⟨(cOf σ ν a)⁻¹, hbU, ?_⟩
  rw [ptMat_mono, hfix, Matrix.mul_assoc, hcb, Matrix.mul_one]

theorem approx_core (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (S : Finset (PlF D))
    (hS : ∀ p, p ∉ S → ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
      (∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O) →
        ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p)
    (h : ∀ p, ProdE.StP M δ u u' w p) :
    ∃ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
      (∀ p ∈ S, (h p)⁻¹ * ProdE.πP M δ u u' w (hA p) g ∈
        ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w (hA p) L U hL hU) ∧
      ∀ p, p ∉ S → ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p := by
  classical
  set σ := Formalism.L2.SG.Pf.fσ w with hσd
  choose c hc0 hcO hcong using fun p => cong_at M δ u u' w (hA p) L U hL hU
  choose τ hτ1 hτ2 hτ3 c' hc'0 hc'O hcl using fun p => close_at M δ u u' w (hA p) (h p) (c p) (hc0 p) (hcO p)
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat (fun p => D.s.atP p) S (fun p => τ p ij.1 ij.2) c' (fun p _ => hc'0 p)
  set a : Formalism.L2.SG.PairVal.MatR D := fun i j =>
    if j < i ∧ σ i < σ j then t (i, j) else (1 : Formalism.L2.SG.PairVal.MatR D) i j with had
  have ha : IsLoUni a := by
    intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have : ¬ (j < i ∧ σ i < σ j) := fun h' => absurd h'.1 (not_lt.2 hij.le)
      simp only [had, if_neg this]
      exact Matrix.one_apply_ne (ne_of_lt hij)
    · subst hij
      have : ¬ (i < i ∧ σ i < σ i) := fun h' => lt_irrefl _ h'.1
      simp only [had, if_neg this, Matrix.one_apply_eq]
  have hpat : ∀ i j, σ j < σ i → a i j = 0 := by
    intro i j hij
    have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have : ¬ (j < i ∧ σ i < σ j) := fun h' => absurd h'.2 (not_lt.2 hij.le)
    simp only [had, if_neg this]
    exact Matrix.one_apply_ne hne
  have hdet : IsUnit a.det := by rw [ZsVolGrp.det_lo (fun x => (ha x x).2 rfl) (fun x y hxy => (ha x y).1 hxy)]; exact isUnit_one
  obtain ⟨b, hb, hab⟩ := mem_stSet_of_pat w a ha hpat
  let gGL : Formalism.L2.SG.PairVal.GLR D := Matrix.nonsingInvUnit a hdet
  have hgv : (gGL : Formalism.L2.SG.PairVal.MatR D) = a := rfl
  let g : Formalism.L2.SG.Pf.VolPinAsm.StG w := ⟨gGL, ⟨by rw [hgv]; exact ha, b, hb, by rw [hgv]; exact hab⟩⟩
  have hgv' : ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = a := rfl
  refine ⟨g, fun p hp => ?_, fun p hp => hS p hp g ?_⟩
  · have hclose : EntIn (latS (D.s.atP p) (c' p))
        (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE - τ p) := by
      intro i j
      rw [hgv', Matrix.sub_apply, Matrix.map_apply]
      by_cases hz : j < i ∧ σ i < σ j
      · simp only [had, if_pos hz]
        exact mem_latS.2 (ht1 (i, j) p hp)
      · simp only [had, if_neg hz]
        have e : (D.s.atP p).ιE ((1 : Formalism.L2.SG.PairVal.MatR D) i j) - τ p i j = 0 := by
          rcases lt_trichotomy i j with hij | hij | hij
          · rw [Matrix.one_apply_ne (ne_of_lt hij), map_zero, hτ1 p i j hij, sub_zero]
          · subst hij; rw [Matrix.one_apply_eq, map_one, hτ2 p i, sub_self]
          · have hs : σ j < σ i := by
              rcases lt_or_gt_of_ne (fun e : σ i = σ j => (ne_of_gt hij) (by
                rw [← Formalism.L2.SG.Pf.fσ_fσ w i, ← Formalism.L2.SG.Pf.fσ_fσ w j]; exact congrArg _ e)) with h' | h'
              · exact absurd ⟨hij, h'⟩ hz
              · exact h'
            rw [Matrix.one_apply_ne (ne_of_gt hij), map_zero, hτ3 p i j hs, sub_zero]
        rw [e]; exact (latS (D.s.atP p) (c' p)).zero_mem
    obtain ⟨h1, h2⟩ := hcl p g hclose
    exact hcong p _ h1 h2
  · intro i j
    rw [hgv']
    by_cases hz : j < i ∧ σ i < σ j
    · simp only [had, if_pos hz]
      exact ht2 (i, j) p hp
    · simp only [had, if_neg hz]
      rw [Matrix.one_apply]
      split_ifs
      · rw [map_one]; exact (D.s.atP p).O.one_mem
      · rw [map_zero]; exact (D.s.atP p).O.zero_mem

end Main

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCong
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_locP {W : Type*} [AddCommGroup W] [Module (𝓞 D.host.E) W] (p : Ideal (𝓞 D.host.E)) [p.IsPrime]
    (L : Submodule (𝓞 D.host.E) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ t : 𝓞 D.host.E, t ∉ p ∧ t • x ∈ L := Iff.rfl

theorem smul_O (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (t : 𝓞 D.host.E) (x : (VS D).V) : s (t • x) = t • s x := by
  rw [← algebraMap_smul D.host.E t x, LinearEquiv.map_smul, algebraMap_smul]

theorem conv_at {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hc : IsFixedConv Λ (Lat.gS D) F) (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
  obtain ⟨c, -, hc1, heq⟩ := hc.1 P
  rw [heq]
  congr 2
  ext v
  simp [hc1 hgP]

theorem int_at {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hc : IsFixedConv Λ (Lat.gS D) F) (hz : F.fl.z ∈ Λ) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu)
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (c i : Fin (D.R.rS + 1)) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (t : D.host.E) * uu c i = o := by
  have hP := P.isPrime
  have hconv := conv_at F Λ hc P hgP
  rcases lt_trichotomy c i with hci | hci | hci
  · have hcr : (c : ℕ) < D.R.rS := lt_of_lt_of_le hci (Nat.lt_succ_iff.1 i.2)
    obtain ⟨a, rfl⟩ : ∃ a : Fin D.R.rS, c = Fin.castSucc a := ⟨⟨c, hcr⟩, rfl⟩
    have hXmem : ∀ y : Fin D.R.rS → D.host.E, (∑ a, y a • F.fl.e a) ∈ Λ → (∑ a, y a • F.fl.e a) ∈ XLam Λ F := by
      intro y hy
      refine Submodule.mem_inf.2 ⟨hy, ?_⟩
      show (∑ a, y a • F.fl.e a) ∈ F.fl.X
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    induction i using Fin.lastCases with
    | last =>
      have hv : s F.fl.z - F.fl.z = ∑ a', uu (Fin.castSucc a') (Fin.last _) • F.fl.e a' := by
        have h := hfr (Fin.last _)
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_last] at h
        rw [h, (huu _ _).2 rfl, one_smul, add_sub_cancel_right]
      have hmem : s F.fl.z - F.fl.z ∈ XLam Λ F := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact Λ.sub_mem (hs _ hz) hz
      have hloc : s F.fl.z - F.fl.z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
        rw [← hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hmem⟩
      obtain ⟨t, ht, htv⟩ := (mem_locP P.asIdeal _ _).1 hloc
      have hv2 : t • (s F.fl.z - F.fl.z) = ∑ a', ((t : D.host.E) * uu (Fin.castSucc a') (Fin.last _)) • F.fl.e a' := by
        rw [hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t, smul_smul]
      obtain ⟨o, ho⟩ := coef_spanO F.fl htv _ hv2 a
      exact ⟨t, ht, o, ho.symm⟩
    | cast i' =>
      have he : F.fl.e i' ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
        rw [hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact Submodule.subset_span ⟨i', rfl⟩⟩
      obtain ⟨t1, ht1, ht1e⟩ := (mem_locP P.asIdeal _ _).1 he
      have hv : s (t1 • F.fl.e i') = ∑ a', ((t1 : D.host.E) * uu (Fin.castSucc a') (Fin.castSucc i')) • F.fl.e a' := by
        have h := hfr (Fin.castSucc i')
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_castSucc] at h
        rw [smul_O, h, (huu _ _).1 (Fin.castSucc_lt_last i'), zero_smul, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t1, smul_smul]
      have hmem : s (t1 • F.fl.e i') ∈ XLam Λ F := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact hs _ (Submodule.mem_inf.1 ht1e).1
      have hloc : s (t1 • F.fl.e i') ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
        rw [← hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hmem⟩
      obtain ⟨t2, ht2, ht2v⟩ := (mem_locP P.asIdeal _ _).1 hloc
      have hv2 : t2 • s (t1 • F.fl.e i') =
          ∑ a', ((t2 : D.host.E) * ((t1 : D.host.E) * uu (Fin.castSucc a') (Fin.castSucc i'))) • F.fl.e a' := by
        rw [hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t2, smul_smul]
      obtain ⟨o, ho⟩ := coef_spanO F.fl ht2v _ hv2 a
      refine ⟨t2 * t1, fun h => (hP.mem_or_mem h).elim ht2 ht1, o, ?_⟩
      rw [ho]
      push_cast
      ring
  · subst hci
    exact ⟨1, P.asIdeal.primeCompl.one_mem, 1, by rw [(huu c c).2 rfl]; simp⟩
  · exact ⟨1, P.asIdeal.primeCompl.one_mem, 0, by rw [(huu c i).1 hci]; simp⟩

end Formalism.L2.SG.Pf.ZsVolLat

end
end

