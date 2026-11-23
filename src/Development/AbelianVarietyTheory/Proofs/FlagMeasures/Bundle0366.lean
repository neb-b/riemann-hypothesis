module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesLeadingMinorEq
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMinor

theorem leadMinor_atBase : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS),
    AtBase Z p F F' Tn T'n P → ∀ l : ℕ, P.Dm l =
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  intro D Z p T T' F F' Tn T'n P hP l
  obtain ⟨hA, hB, -, -⟩ := hP
  have hent : ∀ a b, (locH Z p).Zhat P.A.f P.B.f a b =
      (Z.M p).L.cj (frFac Z.δ p a) * (frFac Z.δ p b *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Zhat F.fl F'.fl a b)) := by
    intro a b
    rw [hA, hB]
    show LocFacts₂ Z.M p (frFac Z.δ p b • baseChange₂ D p (frame F' b)) (frFac Z.δ p a • baseChange₂ D p (frame F a)) = _
    rw [Formalism.L2.SG.Pf.LocFacts.localForm_smul_left₂, Formalism.L2.SG.Pf.LocFacts.localForm_smul_right, baseChangeAt_form Z.M p (Z.hcj p)]
    simp only [Formalism.MainNotions.S.Zhat, frame]
    ring
  show (locH Z p).Dl P.A.f P.B.f l = _
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
  split_ifs with hl
  · rw [RingHom.map_det]
    have hM : ((locH Z p).Zhat P.A.f P.B.f).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        Matrix.of fun i j => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * (frFac Z.δ p (Fin.castLE hl j) *
          (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE) i j) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, hent]
    have e1 := Matrix.det_mul_column (fun i : Fin l => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)))
      (Matrix.of fun i j => frFac Z.δ p (Fin.castLE hl j) *
          (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE) i j)
    have e2 := Matrix.det_mul_row (fun j : Fin l => frFac Z.δ p (Fin.castLE hl j))
      (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE)
    simp only [Matrix.of_apply] at e1
    rw [RingHom.mapMatrix_apply, hM, e1, e2, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    set g : ℕ → (D.s.atP p).Ep := fun k => if h : k < D.R.rS + 1 then
      (Z.M p).L.cj (frFac Z.δ p ⟨k, h⟩) * frFac Z.δ p ⟨k, h⟩ else 1 with hg
    have h1 : (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1)
        = ∏ k ∈ Finset.range (D.R.rS + 1), if k < l then g k else 1 := by
      rw [← Fin.prod_univ_eq_prod_range (fun k => if k < l then g k else 1)]
      refine Finset.prod_congr rfl fun a _ => ?_
      show _ = (if a.val < l then g a.val else 1)
      rw [hg]; dsimp only; rw [dite_eq_left a.isLt]
    have h2 : (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i))
        = ∏ k ∈ Finset.range l, g k := by
      rw [← Fin.prod_univ_eq_prod_range g]
      refine Finset.prod_congr rfl fun i _ => ?_
      have : i.val < D.R.rS + 1 := lt_of_lt_of_le i.isLt hl
      show _ = g i.val
      rw [hg]; dsimp only; rw [dite_eq_left this]; rfl
    rw [h1, h2, ← Finset.prod_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · simp

end GlobalTheory.LocMinor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRationalPointIsPoint
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocalBlockEntries

open Formalism.L2.SG.Pf.AtPt

theorem ptEntryL_eq' {S : Type} [CommRing S] (L : List (Sˣ × ℕ+)) : ∀ i j : ℕ,
    Formalism.MainNotions.S.Loc.ptEntryL L i j = ptEntry (L.map fun b => ((b.1 : S), (b.2 : ℕ))) i j := by
  induction L with
  | nil => intro i j; rfl
  | cons b L ih =>
    intro i j
    obtain ⟨t, s⟩ := b
    simp only [Formalism.MainNotions.S.Loc.ptEntryL, List.map_cons, ptEntry]
    split_ifs <;> first | rfl | exact ih _ _

theorem modBlocks_map' {A S : Type} [CommRing S] (f : ℕ → ℕ → A → S) :
    ∀ (l : List (A × ℕ)) (a : ℕ) (L : List (Sˣ × ℕ+)),
    modBlocks f a l = some L → L.map (fun b => ((b.1 : S), (b.2 : ℕ))) = mapBlocks f a l := by
  intro l
  induction l with
  | nil =>
    intro a L h
    simp only [modBlocks, Option.some.injEq] at h
    subst L
    rfl
  | cons b l ih =>
    obtain ⟨t, s⟩ := b
    intro a L h
    simp only [modBlocks] at h
    split_ifs at h with hu
    obtain ⟨L1, hL1, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [List.map_cons, mapBlocks, ih (a + s) L1 hL1]
    rfl

theorem mapBlocks_snd' {A B : Type} (f : ℕ → ℕ → A → B) : ∀ (l : List (A × ℕ)) (a : ℕ),
    (mapBlocks f a l).map Prod.snd = l.map Prod.snd
  | [], _ => rfl
  | (t, s) :: l, a => by simp [mapBlocks, mapBlocks_snd' f l (a + s)]

theorem modBlocks_some {A S : Type} [CommRing S] (f : ℕ → ℕ → A → S) :
    ∀ (l : List (A × ℕ)) (a : ℕ), (∀ b ∈ l, 0 < b.2) → (∀ b ∈ l, ∀ a' s, IsUnit (f a' s b.1)) →
      ∃ L, modBlocks f a l = some L := by
  intro l
  induction l with
  | nil =>
    intro a _ _
    exact ⟨[], rfl⟩
  | cons b l ih =>
    obtain ⟨t, s⟩ := b
    intro a h1 h2
    obtain ⟨L1, hL1⟩ := ih (a + s) (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
        (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
    have hu : IsUnit (f a s t) ∧ 0 < s := ⟨h2 (t, s) List.mem_cons_self a s, h1 (t, s) List.mem_cons_self⟩
    rw [modBlocks, dite_eq_left hu, hL1]
    exact ⟨_, rfl⟩

end GlobalTheory.LocalBlockEntries

end

open Formalism.L2.SG.Pf.AtPt in
theorem GlobalTheory.LocOver.isPoint_of_scaled : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS), ZhatOM (ZhatL F F') = ptMat w → P.A.f = scaled Z p (frame F) → P.B.f = scaled Z p (frame F') → P.IsPoint := by
  intro D Z p T T' F F' w P hZ hA hB
  let fB : ℕ → ℕ → D.host.E → (D.s.atP p).Ep := fun a s t =>
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Z p)⁻¹ ^ nu D.R.rS a (a + s - 1)) * (D.s.atP p).ιE t
  have hunit : ∀ b ∈ w.1, ∀ a' s, IsUnit (fB a' s b.1) := fun b hb a' s =>
    (Formalism.L2.SG.Pf.BBTie.bt_alg_unit p (pow_ne_zero _ (inv_ne_zero (yP_ne Z p)))).mul
      (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p (w.2.1 b hb).1)
  obtain ⟨L, hL⟩ := GlobalTheory.LocalBlockEntries.modBlocks_some fB w.1 1 (fun b hb => (w.2.1 b hb).2) hunit
  have hLm := GlobalTheory.LocalBlockEntries.modBlocks_map' fB w.1 1 L hL
  have hsize : (L.map (fun b => (b.2 : ℕ))).sum = D.R.rS + 1 := by
    have := congrArg (List.map Prod.snd) hLm
    rw [List.map_map, GlobalTheory.LocalBlockEntries.mapBlocks_snd'] at this
    rw [← w.2.2, ← this]; rfl
  refine ⟨⟨L, hsize⟩, fun a b => ?_⟩
  have hR : (⟨L, hsize⟩ : Formalism.MainNotions.S.Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)).mat a b =
      if b = sgF w a then fB (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val) else 0 := by
    simp only [Formalism.MainNotions.S.Loc.Pt.mat]
    rw [GlobalTheory.LocalBlockEntries.ptEntryL_eq', hLm, ptEntry_eq, pSig_map, pTau_map _ _ _ _ (by rw [w.2.2]; exact a.2)]
    simp only [sgF, Fin.ext_iff]
  rw [hR]
  have hZab := congrFun (congrFun hZ a) b
  rw [zhatOM_eq, ptMat_apply'] at hZab
  simp only [Sg, Matrix.mul_diagonal] at hZab
  have hL1 : (locH Z p).Zhat P.A.f P.B.f a b =
      frFac Z.δ p b * (D.s.atP p).cj (frFac Z.δ p a) * (D.s.atP p).ιE (ZhatL F F' a b) := by
    simp only [Formalism.MainNotions.S.Loc.HermSp.Zhat, Matrix.of_apply, locH, locHerm, hA, hB, GlobalTheory.LocOver.scaled]
    rw [Formalism.L2.SG.Pf.BBTie.formP_bc, Z.hcj p]
    rfl
  rw [hL1, frFac_eq, frFac_eq, cj_alg]
  have key : ∀ (X Y : (D.s.atP p).Ep) (z : D.host.E), (-1 : (D.s.atP p).Ep) ^ (D.R.rS - b.val) * (X * Y * (D.s.atP p).ιE z) =
      X * Y * (D.s.atP p).ιE (z * (-1) ^ (D.R.rS - b.val)) := by
    intro X Y z; rw [map_mul, map_pow, map_neg, map_one]; ring
  rw [key, hZab]
  split_ifs with hb
  · subst hb
    simp only [fB]
    rw [nu_eq, pow_add, map_mul]
    ring
  · rw [map_zero, mul_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInvPowDifferentIffLocal
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

namespace GlobalTheory.DiffLoc

theorem ddS_ne (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem mem_ddPow_neg_iff : ∀ (D : D7) (Z : LocDat D) (n : ℕ), n ≤ D.R.rS → ∀ y : D.host.E,
    y ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ p : PlF D, (D.s.atP p).ιE y * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ n ∈ (Z.M p).L.O := by
  intro D Z n hn y
  let a : Fin (D.R.rS + 1) := ⟨D.R.rS - n, by omega⟩
  have he : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = n := by
    show ((D.R.rS : ℤ) - ((D.R.rS - n : ℕ) : ℤ)) = n
    rw [Nat.cast_sub hn]; ring
  have hspan : ∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
      ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) =
      Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
    intro p
    have h := locDiffC_holds D Z p a
    rw [he] at h
    exact h
  have hf : ∀ p : PlF D, frFac Z.δ p a * btT Z p ^ n = 1 := by
    intro p
    rw [bt_frFac_eq Z p a]
    have hk : D.R.rS - a.val = n := by show D.R.rS - (D.R.rS - n) = n; omega
    rw [hk]
    set U := (bt_T_unit Z p).unit
    have hU : (U : (D.s.atP p).Ep) = btT Z p := IsUnit.unit_spec _
    rw [← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  have hinv : ∀ z : D.host.E, z ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ d ∈ ddS D ^ n, z * d ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [zpow_neg, zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero n (ddS_ne D))]
  constructor
  · intro hy p
    have hm : (D.s.atP p).ιE y ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
      rw [← hspan p]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hm
    change (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_assoc, hf p, mul_one]
    exact o.2
  · intro h
    rw [hinv]
    intro d hd
    rw [FractionalIdeal.mem_one_iff]
    have hloc : ∀ p : PlF D, (D.s.atP p).ιE (y * d) ∈ (Z.M p).L.O := by
      intro p
      have hmem : ∀ x ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
          ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)),
          (D.s.atP p).ιE d * x ∈ (Z.M p).L.O := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((hinv z).1 hz d hd)
          rw [← map_mul, mul_comm, ← ho]
          exact bt_iota_int Z p o
        | zero => rw [mul_zero]; exact Subring.zero_mem _
        | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
        | smul o x _ hx => rw [Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem o.2 hx
      have hdf : (D.s.atP p).ιE d * frFac Z.δ p a ∈ (Z.M p).L.O :=
        hmem _ (by rw [hspan p]; exact Submodule.subset_span (Set.mem_singleton _))
      have hyp : (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O := h p
      have e : (D.s.atP p).ιE (y * d) =
          ((D.s.atP p).ιE y * btT Z p ^ n) * ((D.s.atP p).ιE d * frFac Z.δ p a) := by
        calc (D.s.atP p).ιE (y * d) = (D.s.atP p).ιE y * (D.s.atP p).ιE d * (frFac Z.δ p a * btT Z p ^ n) := by
              rw [hf p, mul_one, map_mul]
          _ = _ := by ring
      rw [e]
      exact mul_mem hyp hdf
    obtain ⟨o, ho⟩ := ((GlobalTheory.HL.PlacesInt.integers_local (placesOf Z)).1 (y * d)).1 hloc
    exact ⟨o, ho⟩

end GlobalTheory.DiffLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericTermClassesEqRowsInDoubleCoset
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.RowCls

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem orth_apply {U : Submodule E S.V} {x : S.V} (hx : x ∈ orth S U) {y : S.V} (hy : y ∈ U) :
    S.hT y x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
  exact hx y hy

theorem mem_orth_of {U : Submodule E S.V} {x : S.V} (h : ∀ y ∈ U, S.hT y x = 0) : x ∈ orth S U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  exact h

theorem mem_orth_Xsp {T : E} (F : LFlag S r T) (x : S.V) (hx : ∀ a, S.hT (F.fl.e a) x = 0) :
    x ∈ orth S (Xsp F) := by
  refine mem_orth_of fun y hy => ?_
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hx a
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem frame_orth_Xsp {T : E} (F : LFlag S r T) (i : Fin (r + 1)) (y : S.V) (hy : y ∈ Xsp F) :
    S.hT (F.fl.fvec i) y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    induction i using Fin.lastCases with
    | last => rw [FlagG.fvec, Fin.snoc_last, ← S.herm.eq, F.fl.z_orth b, map_zero]
    | cast a => rw [FlagG.fvec, Fin.snoc_castSucc]; exact F.fl.e_iso a b
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem mapLF_fvec {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T)
    (i : Fin (r + 1)) : (mapLF γ F).fl.fvec i = γ (F.fl.fvec i) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction i using Fin.lastCases with
  | last => simp [FlagG.fvec, mapFlag]
  | cast a => simp [FlagG.fvec, mapFlag]

end Gen

section NR

variable {D : D7}

theorem nrat_fvec_sub {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) (i : Fin (D.R.rS + 1)) : n (F.fl.fvec i) - F.fl.fvec i ∈ Xsp F := by
  induction i using Fin.lastCases with
  | last =>
    rw [FlagG.fvec, Fin.snoc_last]
    exact hn.2.2 _ (mem_orth_Xsp F _ F.fl.z_orth)
  | cast a =>
    rw [FlagG.fvec, Fin.snoc_castSucc]
    have h1 : F.fl.e a ∈ Xflag F (a.1 + 1) :=
      Submodule.subset_span ⟨a, by show a.1 < a.1 + 1; omega, rfl⟩
    exact Submodule.span_mono (Set.image_subset_range _ _) (hn.2.1 a.1 _ h1)

theorem nrat_map_Xsp {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) (y : (VS D).V) (hy : y ∈ Xsp F) : n y ∈ Xsp F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have h := nrat_fvec_sub F hn a.castSucc
    rw [FlagG.fvec, Fin.snoc_castSucc] at h
    have h2 : F.fl.e a ∈ Xsp F := Submodule.subset_span ⟨a, rfl⟩
    simpa using (Xsp F).add_mem h h2
  | zero => simp
  | add y y' _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul c y _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

theorem one_mem_NRat {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
  ⟨one_mem _, fun j x _ => by simp, fun x _ => by simp⟩

end NR

end GlobalTheory.Unfold.RowCls

namespace GlobalTheory.Unfold.RowCls

section Terms

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem nonGeneric_terms_same_coset_corank_one (t t' : TauC Y u u') (ht : t ∈ (Y.tO u u').ngSet) (hlam : t.lam = t'.lam)
    (hlam' : t.lam' = t'.lam') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NRat (lf D (X.Fu u)))
    (n' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn' : n' ∈ NRat (lf D (X.Fu u'))) (he : t'.lin = n * t.lin * n') :
    (Y.tO u u').s0 t t' = 1 := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro h
    apply ht.1
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : Submodule.IsFullLattice D.host.E t.lam := ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact t'.rep.2.2.2.2.1
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hiso' : t'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t'.rep.2.2.1
  show Formalism.L2.SG.TermOp.s0T t t' = 1
  unfold Formalism.L2.SG.TermOp.s0T
  rw [if_pos ⟨hlam, hlam'⟩]
  refine (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 ?_
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp _ _ _ _ _) fun x hx => ?_
  have hxo : ∀ i, (VS D).hT (Sum.elim (lf D (X.Fu u)).fl.fvec t.frame.fl.fvec i) x = 0 := fun i =>
    Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp t.lam _ t.frame hx
      (PI.PairCorankPos.W.frame_mem_UUE t.lam hlat _ t.frame hLF hLt i)
  have hxF : x ∈ orth (VS D) (Xsp (lf D (X.Fu u))) :=
    mem_orth_Xsp _ x fun a => by simpa [FlagG.fvec] using hxo (Sum.inl a.castSucc)
  have hxt : x ∈ orth (VS D) (Xsp t.frame) :=
    mem_orth_Xsp _ x fun a => by simpa [FlagG.fvec] using hxo (Sum.inr a.castSucc)

  have hXt : ∀ d ∈ Xsp (lf D (X.Fu u')), t.lin d ∈ Xsp t.frame := fun d hd =>
    (Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF t.lin hiso (lf D (X.Fu u')) _).2 (by simpa using hd)
  refine Submodule.mem_map.2 ⟨(x, n x), (Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs _ _ _ _ _ _).2 ⟨hx, ?_, ?_, ?_⟩, rfl⟩
  · refine Formalism.L2.SG.NGCut.CorankRelation.mem_Hp_of_orth t.lam _ t'.frame hLF hL' (n x) ?_
    rintro (a | b)
    · show (VS D).hT ((lf D (X.Fu u)).fl.fvec a) (n x) = 0
      have h1 : (VS D).hT ((lf D (X.Fu u)).fl.fvec a) x = 0 := hxo (Sum.inl a)
      have h2 := frame_orth_Xsp (lf D (X.Fu u)) a _ (hn.2.2 x hxF)
      have h3 : n x = x + (n x - x) := by abel
      rw [h3, map_add (f := _), h1, h2, add_zero]
    · show (VS D).hT (t'.frame.fl.fvec b) (n x) = 0
      have hf : t'.frame.fl.fvec b = n (t.lin (n' ((lf D (X.Fu u')).fl.fvec b))) := by
        show (mapLF t'.lin (lf D (X.Fu u'))).fl.fvec b = _
        rw [mapLF_fvec t'.lin hiso' _ b, he]
        rfl
      rw [hf, hn.1]
      have hd := nrat_fvec_sub (lf D (X.Fu u')) hn' b
      have h4 : n' ((lf D (X.Fu u')).fl.fvec b) =
          (lf D (X.Fu u')).fl.fvec b + (n' ((lf D (X.Fu u')).fl.fvec b) - (lf D (X.Fu u')).fl.fvec b) := by abel
      have h5 : (VS D).hT (t.lin ((lf D (X.Fu u')).fl.fvec b)) x = 0 := by
        have := hxo (Sum.inr b)
        simp only [Sum.elim_inr] at this
        rwa [show t.frame.fl.fvec b = t.lin ((lf D (X.Fu u')).fl.fvec b) from mapLF_fvec t.lin hiso _ b] at this
      rw [h4, map_add (f := _), map_add (f := _), LinearMap.add_apply, h5, orth_apply hxt (hXt _ hd), add_zero]
  · show x - n x ∈ Xsp (lf D (X.Fu u))
    have := (Xsp (lf D (X.Fu u))).neg_mem (hn.2.2 x hxF)
    simpa using this
  · show (t'.lin * t.lin⁻¹) x - n x ∈ Xsp t'.frame
    refine (Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF t'.lin hiso' (lf D (X.Fu u')) _).2 ?_
    set w := t.lin.symm x with hw
    have hwx : t.lin w = x := by simp [hw]
    have key : t'.lin (w - n'.symm w) = (t'.lin * t.lin⁻¹) x - n x := by
      rw [he]
      show n (t.lin (n' (w - n'.symm w))) = n (t.lin (n' (t.lin.symm x))) - n x
      rw [← hw, map_sub, LinearEquiv.apply_symm_apply, map_sub, map_sub, hwx]
    rw [← key, LinearEquiv.symm_apply_apply]

    have hwo : ∀ y ∈ Xsp (lf D (X.Fu u')), (VS D).hT y w = 0 := fun y hy => by
      rw [← hiso y w, hwx]
      exact orth_apply hxt (hXt y hy)
    have hv : n'.symm w ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) := by
      refine mem_orth_of fun y hy => ?_
      rw [← hn'.1 y (n'.symm w), LinearEquiv.apply_symm_apply]
      exact hwo _ (nrat_map_Xsp _ hn' y hy)
    have h6 := hn'.2.2 _ hv
    rw [LinearEquiv.apply_symm_apply] at h6
    exact h6

theorem clsRow_ngSet : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    ClsRow (Y.tO u u').ngSet (clsOf Y u u') := by
  intro D X Y u u' hT t ht t' ht' hn
  obtain ⟨hR, hS, hTr⟩ := Formalism.L2.SG.NGCut.CorankRelation.corankOne_equivalence_holds D X Y u u' hT
  have hiff : clsOf Y u u' t = clsOf Y u u' t' ↔
      ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ (Y.tO u u').s0 t t' = 1) := by
    constructor
    · intro heq
      have hm : t' ∈ clsOf Y u u' t' := ⟨ht', rfl, hR t' ht'⟩
      rw [← heq] at hm
      exact ⟨hm.2.1.symm, hm.2.2⟩
    · rintro ⟨hr, hs⟩
      ext x
      simp only [Formalism.L2.SG.RowsConc.clsOf, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hx, hrx, hsx⟩
        exact ⟨hx, hrx.trans hr, hTr t' ht' t ht x hx hr.symm hrx.symm (hS t ht t' ht' hr hs) hsx⟩
      · rintro ⟨hx, hrx, hsx⟩
        exact ⟨hx, hrx.trans hr.symm, hTr t ht t' ht' x hx hr hrx.symm hs hsx⟩
  rw [hiff]
  refine ⟨fun h => h.1, fun hr => ⟨hr, ?_⟩⟩
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]
    exact ⟨1, one_mem_NRat _, 1, one_mem_NRat _, by simp⟩
  obtain ⟨n, hnn, n', hnn', he⟩ := hmem
  exact nonGeneric_terms_same_coset_corank_one t t' ht hlam hlam' n hnn n' hnn' he

end Terms

end GlobalTheory.Unfold.RowCls
end
end

