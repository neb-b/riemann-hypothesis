module

public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipAevalUniformizer
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.IntAOfNonpol
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelOneUniformizerCoeffVanish
public import Formalism.SharpRestriction.LevelLetterCocycles.CoeffAlgMul

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.InFr1OfPi0Lam
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

section Mod

variable (T : LocLat G Qp LL O) (A : ArcP n) (c : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
  (Rst : Finset (Fin d))

theorem inFr1_add {f g : W.EE} (hf : InFr W c 1 (abelian₂ W A c e) f) (hg : InFr W c 1 (abelian₂ W A c e) g) :
    InFr W c 1 (abelian₂ W A c e) (f + g) :=
  (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_add W
    ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hf) ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hg))

theorem inFr1_smul (o : O) {f : W.EE} (hf : InFr W c 1 (abelian₂ W A c e) f) :
    InFr W c 1 (abelian₂ W A c e) (o • f) :=
  (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_smul W
    ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hf) o)

theorem inFr1_zero : InFr W c 1 (abelian₂ W A c e) 0 := ⟨0, W.AΔ.zero_mem, by simp⟩

def Msub : Submodule O (Fin d → W.EE) where
  carrier := {f | (∀ k, InFr W c 1 (abelian₂ W A c e) (f k)) ∧ ∀ k ∉ Rst, f k = 0}
  add_mem' := fun {f g} hf hg => ⟨fun k => inFr1_add W A c e (hf.1 k) (hg.1 k),
    fun k hk => by simp [hf.2 k hk, hg.2 k hk]⟩
  zero_mem' := ⟨fun _ => inFr1_zero W A c e, fun _ _ => rfl⟩
  smul_mem' := fun o f hf => ⟨fun k => inFr1_smul W A c e o (hf.1 k), fun k hk => by simp [hf.2 k hk]⟩

def Isub : Submodule O (Fin d → W.EE) where
  carrier := {f | f ∈ Msub W A c e Rst ∧ InvNL W T c e (abelian₂ W A c e) b f}
  add_mem' := by
    rintro f f' ⟨hf, g, hg, hfg⟩ ⟨hf', g', hg', hfg'⟩
    refine ⟨(Msub W A c e Rst).add_mem hf hf', g + g',
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A c e b hg hg', fun k => ?_⟩
    simp only [Pi.add_apply, map_add (f := _)]
    rw [mul_add, ← hfg k, ← hfg' k]; ring
  zero_mem' := ⟨(Msub W A c e Rst).zero_mem, 0, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_zero W T A c e b,
    fun k => by simp⟩
  smul_mem' := by
    rintro o f ⟨hf, g, hg, hfg⟩
    refine ⟨(Msub W A c e Rst).smul_mem o hf, fun k => o • g k,
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A c e b o hg, fun k => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, hfg k, mul_smul_comm]

theorem inFr1_of_pi0Lam {f : W.EE} (hf : InFr W c (W.π₀ * abelian₂ W A c e) 1 f) :
    InFr W c 1 (abelian₂ W A c e) f := by
  obtain ⟨w, hw, hfw⟩ := hf
  have hΛm : abelian₂ W A c e ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem
    (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _
  refine ⟨abelian₂ W A c e * (W.π₀ * abelian₂ W A c e) * w,
    W.AΔ.mul_mem (W.AΔ.mul_mem hΛm (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) hΛm)) hw, ?_⟩
  rw [map_one, one_mul] at hfw
  rw [hfw, ← map_mul]; congr 1; ring

end Mod

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SplitPolarLOf
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O] [NeZero n]

theorem splitPolar_of [FiniteDimensional Qp LL] (C : LevC.Ctx W) (hArc : ArcCore W)
    (hJ : Formalism.MainNotions.LiftingTheory.coreJumps PD LL O) (h9 : DcrisExactStrict PD LL) : Split.SplitPolar W := by
  intro _ _ A hA T₂ Y ι π hT₂ hY hses c hc w hI hP hpx d b sol hb
  obtain ⟨p, hp, x, hx, hpx⟩ := hpx
  have hac : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  have hc' : c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  have hje : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hWY : Win W A Y := Formalism.MainNotions.UnusedSlot80.Split2.win_ext W A hJ (Formalism.MainNotions.LiftingTheory.lone_HOne0 W) hT₂ hY hses
  obtain ⟨dY, bY, hbYf⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W Y (c - ((A.len c : ℕ) : ZMod n)) (C.hmod Y hY)
  obtain ⟨solY, hbY⟩ := Formalism.MainNotions.UnusedSlot80.UnivF.hor_exists W C.hH C.hCA Y hY _ bY hbYf
  obtain ⟨-, hAC⟩ := hArc C.hCA C.h5p A hA c hc (A.len c) hje le_rfl
  obtain ⟨-, -, -, h2f⟩ := hAC T₂ hT₂
  obtain ⟨⟨hind2, hspan2⟩, -⟩ := h2f d b sol hb
  obtain ⟨-, -, -, hYf⟩ := hAC Y hWY
  obtain ⟨⟨hindY, hspanY⟩, -, -, hNY, -⟩ := hYf dY bY solY hbY
  rw [hac] at hspan2 hspanY hNY
  have hxe : x = p - W.map ι w := by rw [hpx]; abel
  have hxN : InFNc W Y c 1 x := by
    refine ⟨x, ⟨Formalism.MainNotions.UnusedSlot80.Split2.N_of_Nl W hx, fun δ hδ => ?_⟩,
      Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W Y c hx, (one_smul _ _).symm⟩
    rw [hxe, map_sub, Formalism.MainNotions.UnusedSlot80.Relay2.Pp_Δ W Y _ _ p hp δ hδ, ← W.map_γ, hI.2.1 δ hδ]
  exact polar_core W C h9 A hA _ hc' (A.len c) c hac T₂ Y ι π hT₂ hWY hses b sol hb bY solY hbY hind2 hspan2
    hindY hspanY hNY w p x hP hp hxN hpx

end Formalism.MainNotions.UnusedSlot80.SplitP

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem splitPolarL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmArcA D HW F Cm) (hArc : ArcCoordinatesTheorem D HW F Cm) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (h9 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D) : Split.SplitPolarL D HW := by
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have C := ctx_of D HW F Cm hAdm l K LL hG hCA h5l
  exact SplitP.splitPolar_of _ C ((hArc hAdm) l K LL hG hCA h5l).1 (h23 l K LL) (h9 l K LL)

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.VanishOfXU
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrC

open Formalism.MainNotions.N.Pv.LocalLengthBound.Ser PowerSeries

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem smulS_delta (g : PowerSeries LL) (w : V) (j : ℕ) :
    smulS g (fun k : ℤ => if k = 0 then w else 0) (j : ℤ) = coeff j g • w := by
  have hLB : LB 0 (fun k : ℤ => if k = 0 then w else 0) := by
    intro k hk
    simp [ne_of_lt hk]
  rw [smulS_eq_sum hLB g (j : ℤ) (j + 1) (by omega)]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg (by omega)]
    simp
  · intro hj
    simp at hj

theorem LB_delta (w : V) : LB 0 (fun k : ℤ => if k = 0 then w else 0) := by
  intro k hk
  simp [ne_of_lt hk]

theorem LB_fsum {ι : Type} (s : Finset ι) {m : ℤ} (F : ι → ℤ → V) (hF : ∀ i, LB m (F i)) :
    LB m (∑ i ∈ s, F i) := by
  refine Finset.induction_on s (fun k _ => by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha]
  exact LB_add (hF a) ih

theorem smulS_fsum {ι : Type} (s : Finset ι) (g : PowerSeries LL) {m : ℤ} (F : ι → ℤ → V)
    (hF : ∀ i, LB m (F i)) : smulS g (∑ i ∈ s, F i) = ∑ i ∈ s, smulS g (F i) := by
  refine Finset.induction_on s ?_ ?_
  · funext k
    simp [smulS]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, smulS_add (hF a) (LB_fsum s F hF), ih]

theorem smulS_shift (g : PowerSeries LL) {m : ℤ} {F : ℤ → V} (hF : LB m F) (H : ℕ) :
    smulS (X ^ H * g) F = fun r => smulS g F (r - H) := by
  rw [smulS_mul hF, smulS_X_pow (LB_smulS hF g)]

theorem LB_of_unit {U : PowerSeries LL} (hU : constantCoeff U ≠ 0) {m N : ℤ} {F : ℤ → V} (hF : LB m F)
    (h : LB N (smulS U F)) : LB N F := by
  have h2 := LB_smulS h U⁻¹
  rwa [smulS_inv hF U hU] at h2

theorem vanish_of_XU {U : PowerSeries LL} (hU : constantCoeff U ≠ 0) {m : ℤ} {F : ℤ → V} (hF : LB m F)
    (H : ℕ) (N : ℤ) (h : ∀ r < N + H, smulS (X ^ H * U) F r = 0) : LB N F := by
  apply LB_of_unit hU hF
  intro r hr
  have := h (r + H) (by omega)
  rw [smulS_shift U hF H] at this
  simpa using this

end Formalism.MainNotions.UnusedSlot80.CrC
end
end

