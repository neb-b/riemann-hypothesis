module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0426
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsAtPointOfRelevantTermRelevantFinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalThetaGraphRationalIsometryMovedLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PulledLocalGraphsEqIffIdentificationsCompatible
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0418

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalObjectFamilyClassesDetermineRows
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs
open scoped Classical

namespace GlobalTheory.FamGen

open Formalism.MainNotions.S.Lat GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_clsLoc_self {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) {r : ℕ} (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Y0 ∈ clsLoc M Y0 := by
  have hI : IntUni M (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := by
    refine ⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun a b => ?_⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  refine ⟨1, 1, hI, hI, fun a b => ?_, ?_⟩
  · rw [sub_self]; exact Submodule.zero_mem _
  · rw [Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]

theorem exists_famTie : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), (∀ t ∈ TS, t.G ≠ 0) → (∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') → ∀ t₀ ∈ TS, t₀.relevant → ∃ Fm : LocFam (zOf Y) Cl (NuC D), FamTie TS cls (nmlOf Y u u') (ptPN t₀) Fm ∧ (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p))) ∧ (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t) ∧ (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ c, 0 ≤ Fm.rw c) := by
  intro D X Y u u' Cl TS cls hG hrow t₀ ht₀ hrel
  obtain ⟨w, hw, hat, hfin⟩ := _root_.GlobalTheory.LocOver.terms_at_point_of_relevant D X Y u u' t₀ (hG t₀ ht₀) hrel
  have hRL : IsRowLat D (X.Fu u) t₀.toTerm.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  obtain ⟨-, hG0, hcell0⟩ := hat t₀ rfl
  obtain ⟨F00, F'0, F'1, FP, d0, hn, hZ, -, hcell1, hp, hfinP⟩ :=
    _root_.GlobalTheory.BaseTerm.base_data_of_global_term D (zOf Y) u u' (X.Fu u) t₀.toTerm.lam hRL (Quot.out t₀.toTerm.cls).1
      (Quot.out t₀.toTerm.cls).2 hG0 w hcell0
  have hreps := fun p => GlobalTheory.LocOver.orbit_reps_over ((zOf Y).M p) ((zOf Y).agree p).1 (locH (zOf Y) p) D.R.rS (FP p)
  let R : ∀ p : PlF D, LocNG.Reps (FP p) := fun p => (hreps p).2.1.some
  let LT : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ∀ p : PlF D, Formalism.MainNotions.S.Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS :=
    fun s p => locU (zOf Y) p s.lam (lf D (X.Fu u)) (Quot.out s.cls).1 (Tu D u) (Tu D u')
  let rho : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ∀ p : PlF D, LocNG.Datum (FP p) :=
    fun s p => if h : ∃ d ∈ (R p).RD, Over (FP p) d (LT s p) then h.choose else d0 p

  have hover : ∀ t : TauC Y u u', ptPN t = ptPN t₀ → ∀ p, ∃ d, Over (FP p) d (LT t.toTerm p) := by
    intro t ht p
    obtain ⟨-, hGt, hct⟩ := hat t ht
    exact _root_.GlobalTheory.LocOver.GlobOver.over_local D (zOf Y) u u' (X.Fu u) t.toTerm.lam ((Y.rowsOK u).1 t.lam t.mem) (Quot.out t.toTerm.cls).1
      (Quot.out t.toTerm.cls).2 hGt w F00 F'0 hct hZ p (FP p) (hp p).1
  have hrho : ∀ t : TauC Y u u', ptPN t = ptPN t₀ → ∀ p, rho t.toTerm p ∈ (R p).RD ∧ Over (FP p) (rho t.toTerm p) (LT t.toTerm p) := by
    intro t ht p
    obtain ⟨d, hd⟩ := hover t ht p
    obtain ⟨y, hy, hyd⟩ := (R p).hRD.2.1 d (Set.mem_univ _)
    have hex : ∃ d ∈ (R p).RD, Over (FP p) d (LT t.toTerm p) := ⟨y, hy, (hreps p).2.2 d y _ ((hreps p).1.symm hyd) hd⟩
    have e : rho t.toTerm p = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec

  let γ := ptPN t₀
  let Pf : Finset (PlF D) := hfinP.toFinset
  let Om : Finset {p // p ∈ Pf} := Pf.attach.filter (fun p => ¬ (FP p.1).PrimeTo)
  let Ds : ∀ p : PlF D, Finset (LocNG.Datum (FP p)) := fun p => hfin.toFinset.image (fun s => rho s p)
  have hmemDs : ∀ t : TauC Y u u', ptPN t = γ → ∀ p, rho t.toTerm p ∈ Ds p := fun t ht p =>
    Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨t, ht, rfl⟩)
  let dat : Cl → NuC D → Option (∀ p : {p // p ∈ Pf}, {d // d ∈ Ds p.1}) := fun c ν =>
    if h : ∃ t ∈ TS, cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν then
      some (fun p => ⟨rho h.choose.toTerm p.1, hmemDs _ h.choose_spec.2.2.1 p.1⟩) else none
  let rw : Cl → ℝ := fun c => if h : ∃ t ∈ TS, cls t = c then (Formalism.L2.SG.TermOp.wt h.choose) ^ 2 else 0
  let ngenL : PlF D → ℝ := fun p => (ngenLoc (R p) (d0 p) (clsLoc ((zOf Y).M p)
    ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1)))).toReal
  let Fm0 : LocFam (zOf Y) Cl (NuC D) := ⟨Pf, Om, FP, R, d0, Ds, ngenL, 0, rw, dat⟩
  let Fm : LocFam (zOf Y) Cl (NuC D) := { Fm0 with V0 := if h : ∃ v, OrbitFamilyIdentityAt Fm0 v then h.choose else 0 }
  have hDs : ∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD := by
    intro p _ d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨t, ht, rfl⟩ := hfin.mem_toFinset.1 hs
    exact (hrho t ht p).1
  have hnotP : ∀ p, p ∉ Pf → (FP p).PrimeTo ∧ LocNG.IsTermOver (FP p) (d0 p) ⟨lattice₂ D (zOf Y).M p t₀.toTerm.lam,
      scaled (zOf Y) p (frame F00), scaled (zOf Y) p (frame F'0), ((Tu D u : ℕ) : (D.s.atP p).Fp),
      ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩ := by
    intro p hp'
    by_contra hc
    exact hp' (hfinP.mem_toFinset.2 hc)
  refine ⟨Fm, ⟨w, F00, F'0, F'1, hw, hDs, rfl, hn, hZ, fun p => (hp p).1, ?_, fun p hp' => (hnotP p hp').1, ?_,
    ⟨t₀, ht₀, rfl, fun p _ => (hp p).2.2.1⟩, fun p _ => ⟨_, (hp p).2.2.1⟩,
    ⟨t₀.toTerm.lam, hRL.1.1.toIsLattice, fun p hp' => (hnotP p hp').2⟩, ?_, hcell1, fun p _ => ⟨rfl, d0 p, _, (hp p).2.2.1, ?_⟩⟩,
    fun p _ => (hp p).2.1, fun p _ => ⟨d0 p, _, (hp p).2.2.1⟩, hDs, fun c => ?_⟩
  · intro p
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_attach _ _))
  · intro p hp' t _ ht
    obtain ⟨-, hGt, hct⟩ := hat t ht
    obtain ⟨d, g, hg, d', hdd', hto⟩ := _root_.GlobalTheory.LocOver.GlobOver.over_local D (zOf Y) u u' (X.Fu u) t.toTerm.lam ((Y.rowsOK u).1 t.lam t.mem)
      (Quot.out t.toTerm.cls).1 (Quot.out t.toTerm.cls).2 hGt w F00 F'0 hct hZ p (FP p) (hp p).1
    have hpr := (hnotP p hp').1
    have hrel' : LocNG.Datum.Rel (d0 p) d' :=
      _root_.GlobalTheory.HL.PrimeToOrbit.main ((zOf Y).M p) ((zOf Y).agree p).1 (locH (zOf Y) p) D.R.rS D.R.k (FP p) (rank_Vp p) (hp p).2.1 hpr
        (d0 p) d' _ _ (hp p).2.2.1 hto
    exact ⟨g, hg, d', hrel', hto⟩
  · intro c ν
    by_cases h : ∃ t ∈ TS, cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν
    · have e : Fm.dat c ν = some (fun p => ⟨rho h.choose.toTerm p.1, hmemDs _ h.choose_spec.2.2.1 p.1⟩) := dif_pos h
      rw [e]
      obtain ⟨hc1, hc2, hc3, hc4⟩ := h.choose_spec
      refine ⟨h, fun t ht hct hpt hnt => ⟨fun p _ => ?_, ?_⟩⟩
      · have hsame := _root_.GlobalTheory.LocOver.TermSame.same D X Y u u' h.choose t (hG _ hc1) (hrow _ hc1 t ht (hc2.trans hct.symm))
        obtain ⟨g, hg, d', hdd', hto⟩ := hsame.2 (hc4.trans hnt.symm) p (FP p) (hp p).2.1 _ (hrho _ hc3 p).2
        exact ⟨g, hg, d', hdd', hto⟩
      · have hc : ∃ t ∈ TS, cls t = c := ⟨t, ht, hct⟩
        have e2 : Fm.rw c = (Formalism.L2.SG.TermOp.wt hc.choose) ^ 2 := dif_pos hc
        rw [e2]
        obtain ⟨hh1, hh2⟩ := hc.choose_spec
        rw [(_root_.GlobalTheory.LocOver.TermSame.same D X Y u u' hc.choose t (hG _ hh1) (hrow _ hh1 t ht (hh2.trans hct.symm))).1]
    · have e : Fm.dat c ν = none := dif_neg h
      rw [e]
      exact h
  · show (locH (zOf Y) p).Zhat (locU (zOf Y) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f
      (locU (zOf Y) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f' ∈ _
    have hm := mem_clsLoc_self ((zOf Y).M p) ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1))
    convert hm using 3
    all_goals first | rfl | exact (hp p).2.2.2
  · show 0 ≤ (if h : ∃ t ∈ TS, cls t = c then (Formalism.L2.SG.TermOp.wt h.choose) ^ 2 else 0)
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

end GlobalTheory.FamGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantIsometryUnitriangularMoves
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL

theorem leadMinor_triMul {E : Type} [Field E] {m : ℕ} (A B Z : Matrix (Fin m) (Fin m) E)
    (hA : ∀ i j, i < j → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) (l : ℕ) :
    leadMinorE (A * Z * B) l = leadMinorE Z l := by
  unfold leadMinorE
  by_cases hl : l ≤ m
  · rw [dite_eq_left hl, dite_eq_left hl]
    have red : ∀ g : Fin m → E, (∀ i : Fin m, l ≤ (i : ℕ) → g i = 0) →
        ∑ i, g i = ∑ i : Fin l, g (Fin.castLE hl i) := by
      intro g hg
      refine (Finset.sum_of_injOn (Fin.castLE hl) (Fin.castLE_injective hl).injOn
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun i _ hi => hg i ?_) (fun _ _ => rfl)).symm
      by_contra h
      exact hi ⟨⟨i, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
    have key : (A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        A.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
          B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [red]
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [red]
        intro i hi
        rw [hA _ _ (by simp [Fin.lt_def]; omega), zero_mul]
      · intro i hi
        rw [hB _ _ (by simp [Fin.lt_def]; omega), mul_zero]
    have hdA : (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · simp [hA1]
      · intro i j hij
        have h2 : i < j := OrderDual.toDual_lt_toDual.1 hij
        exact hA _ _ (Fin.lt_def.2 (Fin.lt_def.1 h2))
    have hdB : (B.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · simp [hB1]
      · intro i j hij
        have h2 : j < i := hij
        exact hB _ _ (Fin.lt_def.2 (Fin.lt_def.1 h2))
    rw [key, Matrix.det_mul, Matrix.det_mul, hdA, hdB, one_mul, mul_one]
  · rw [dite_eq_right hl, dite_eq_right hl]

variable {D : D7}

theorem zhat_movesTo {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T')
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (h : MovesTo F0 F0' F F' ρ U U') :
    Zhat F.fl F'.fl = U.conjTranspose * Zhat F0.fl F0'.fl * U' := by
  obtain ⟨hρ, -, -, hU, hU'⟩ := h
  have hρ' : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ
  refine Matrix.ext fun a b => ?_
  have e1 : Zhat F.fl F'.fl a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
    rw [hρ']; rfl
  rw [e1, hU a, hU' b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, LinearMap.sum_apply,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  simp only [RingHom.id_apply, frame, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem gval_movesTo : ∀ {D : D7} {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  intro D T T' F0 F0' F F' ρ U U' h
  have hZ := zhat_movesTo F0 F0' F F' ρ U U' h
  obtain ⟨-, hu, hu', -, -⟩ := h
  have hl : ∀ l, Dl F.fl F'.fl l = Dl F0.fl F0'.fl l := by
    intro l
    show leadMinorE (Zhat F.fl F'.fl) l = leadMinorE (Zhat F0.fl F0'.fl) l
    rw [hZ]
    refine leadMinor_triMul _ _ _ (fun i j hij => ?_) (fun i => ?_) (fun i j hij => (hu' i j).1 hij)
      (fun i => (hu' i i).2 rfl) l
    · simp [Matrix.conjTranspose_apply, (hu j i).1 hij]
    · simp [Matrix.conjTranspose_apply, (hu i i).2 rfl]
  show Gflag F.fl F'.fl = Gflag F0.fl F0'.fl
  unfold Gflag
  rw [hl, hl]

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphs
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IotaGraph

open Formalism.L2.SG.Pf Formalism.L2.SG.Saturated


set_option maxHeartbeats 2000000 in
theorem graph_eq_iff_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p : PlF D, ((G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2 ↔ ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm p
  obtain ⟨hn, hm, ht⟩ := hnm
  obtain ⟨gρ, hgρ, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hMv.1
  obtain ⟨gn, hgn, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p n hn.1
  have hgρn : Ext p (ρ * n) (gρ * gn) := by
    intro x
    show gρ (gn (baseChange₂ D p x)) = baseChange₂ D p (ρ (n x))
    rw [hgn x, hgρ (n x)]
  have hmv := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv).2.2.2.2.2
  obtain ⟨A, A', -, -, -, -, hMv1⟩ := hmv t n m ⟨hn, hm, ht⟩
  have h1 := _root_.GlobalTheory.HL.graph_moved_local D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c p (ρ * n) (gρ * gn) t.frame
    (U * A) (U' * A') hMv1 hgρn t₀.lam
  have h0 := _root_.GlobalTheory.HL.graph_moved_local D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c p ρ gρ t₀.frame U U' hMv hgρ t₀.lam
  have hs : ∀ x, (gρ * gn).symm x = gn.symm (gρ.symm x) := fun x => rfl
  have hlat : G.datOf (c.lat (ρ * n) t.lam) p = G.datOf (c.lat (ρ * n) t₀.lam) p :=
    congrArg (fun Λ => G.datOf (c.lat (ρ * n) Λ) p) hl
  refine Iff.trans ?_ (_root_.GlobalTheory.PullGraph.pulled_graph_iff D X Y u u' t₀ t n m hl hl' ⟨hn, hm, ht⟩ p gn hgn)
  constructor
  · intro h a b
    rw [hlat] at h
    have hq := (h1 ((c.c p).e (gρ a), (c.c p).e (gρ b))).symm.trans
      ((iff_of_eq (congrArg (fun S => ((c.c p).e (gρ a), (c.c p).e (gρ b)) ∈ S) h)).trans
        (h0 ((c.c p).e (gρ a), (c.c p).e (gρ b))))
    have e1 : ∀ x, (gρ * gn).symm ((c.c p).e.symm ((c.c p).e (gρ x))) = gn.symm x := fun x => by
      rw [hs, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have e2 : ∀ x, gρ.symm ((c.c p).e.symm ((c.c p).e (gρ x))) = x := fun x => by
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    dsimp only at hq
    simp only [e1, e2] at hq
    exact hq
  · intro h
    rw [hlat]
    apply Set.ext
    intro q
    have hq := h (gρ.symm ((c.c p).e.symm q.1)) (gρ.symm ((c.c p).e.symm q.2))
    refine (h1 q).trans (Iff.trans ?_ (h0 q).symm)
    rw [hs, hs]
    exact hq


set_option maxHeartbeats 2000000 in
theorem iotaCompat_iff_graph : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → (IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) ↔ ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hloc := graph_eq_iff_local D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hγ0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hγ1 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hγ0)
  have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' = t₀.lam := by
    have h : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    rw [hl, hl'] at h
    exact h
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (t.lin * t₀.lin⁻¹) t₀.lam = t₀.lam := by
    rw [gmap_mul_sat, ← hg0, gmap_inv_gmap, hg1, hg0]
  constructor
  · intro hI p
    rw [hloc p]
    intro gβ hgβ x' hx' x hx hx'p hxp
    by_cases hs : (Y.M p).split = none
    · obtain ⟨g0, -, -, huniq, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p _ hβ
      have hg : gβ = g0 := huniq gβ hgβ
      have hgx : gβ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam := by
        have h := himg t₀.lam
        rw [hβΛ] at h
        rw [← h, hg]
        exact ⟨x', hx', rfl⟩
      have hth : LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p) = 1 := by
        show LocNG.theta (Y.M p) = 1
        unfold LocNG.theta; rw [hs]
      have key : ∀ (f f' : Fin (D.R.rS + 1) → Vp D p) (v : Vp D p), v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam →
          Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) f f' v := by
        intro f f' v hv
        refine ⟨v, ?_, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, Submodule.zero_mem _,
          Submodule.zero_mem _, by simp⟩
        rw [hth]
        exact Submodule.subset_span ⟨v, hv, by simp⟩
      exact ⟨fun _ => key _ _ _ (Submodule.sub_mem _ hx hgx), fun _ => key _ _ _ (Submodule.sub_mem _ hx hx')⟩
    · have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
      have hPD0 := t₀.rep.2.2.2.2
      have hPD1 : Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' t.frame := by
        have h : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' t.frame := t.rep.2.2.2.2
        rw [hl] at h
        exact h
      have hfr : ∀ a, frame t.frame a = (t.lin * t₀.lin⁻¹) (frame t₀.frame a) := by
        intro a
        show frame (mapLF t.lin (lf D (X.Fu u'))) a = (t.lin * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a)
        rw [Formalism.L2.SG.Pf.Act.frame_mapLF hγ1, Formalism.L2.SG.Pf.Act.frame_mapLF hγ0]
        show t.lin _ = t.lin (t₀.lin.symm (t₀.lin _))
        rw [LinearEquiv.symm_apply_apply]
      exact _root_.GlobalTheory.IotaLoc.iota_typed D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hrow t₀.frame t.frame hPD0 hPD1 _ hβ hβΛ hfr hI p gβ hgβ hs
        x' hx' x hx hx'p hxp
  · intro h
    exact _root_.GlobalTheory.IotaLocConv.iotaCompat_of_local D X Y u u' t₀ t hl hl' (fun p _ => (hloc p).1 (h p))

end GlobalTheory.IotaGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFramesMovedTermUnitriangularChange
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

theorem isUpperUnitriangularFinMatrix_mul_of_both {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem triMove_main : ∀ {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (f' : Fin (D.R.rS + 1) → Vp D p), MovesTo F0 F0' F F' ρ U U' → Ext p ρ g → Tri (D.s.atP p).Ep (scaled Z p (frame F')) f' → Tri (D.s.atP p).Ep (scaled Z p (frame F0)) (fun a => g (scaled Z p (frame F) a)) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F0')) (fun b => g (f' b)) := by
  intro D Z p T T' F0 F0' F F' ρ U U' g f' hM hE hf'
  obtain ⟨_, hU, hU', hρ, hρ'⟩ := hM
  have hs : ∀ (h : Fin (D.R.rS + 1) → (VS D).V) a, g (scaled Z p h a) = scaled Z p (fun b => ρ (h b)) a := by
    intro h a
    simp only [scaled, map_smul]
    rw [hE]
  have uniOf : ∀ W : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni W → Uni W :=
    fun W hW => ⟨fun a b hab => (hW a b).1 hab, fun a => (hW a a).2 rfl⟩
  obtain ⟨A1, hA1, -⟩ := tri_scaled D Z (frame F0) (fun b => ρ (frame F b)) U (uniOf U hU) (fun b => hρ b)
  obtain ⟨A2, hA2, -⟩ := tri_scaled D Z (frame F0') (fun b => ρ (frame F' b)) U' (uniOf U' hU') (fun b => hρ' b)
  refine ⟨⟨A1 p, (hA1 p).1, fun b => ?_⟩, ?_⟩
  · show g (scaled Z p (frame F) b) = _
    rw [hs]; exact (hA1 p).2 b
  · obtain ⟨A, hA, hc⟩ := hf'
    refine ⟨A2 p * A, isUpperUnitriangularFinMatrix_mul_of_both _ _ (hA2 p).1 hA, fun b => ?_⟩
    show g (f' b) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc b, map_sum]
    have h2 : ∀ a, g (A a b • scaled Z p (frame F') a) =
        ∑ d, (A a b * A2 p d a) • scaled Z p (frame F0') d := by
      intro a
      rw [map_smul, hs, (hA2 p).2 a, Finset.smul_sum]
      exact Finset.sum_congr rfl fun d _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]

end GlobalTheory.LocOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermMoveUnitaryIsTerm
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LocOver.isTerm_move_unitary : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (t : Formalism.MainNotions.S.Loc.Term V M r), H.IsTerm t → H.IsTerm (move g t) :=
  fun H _ g hg t ht => GlobalTheory.LocOver.isTerm_move_of_unitary H g t hg ht
end

