module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemLatGmap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarIsomG
section
noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

def lin {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) : S.V := ∑ i, c i • u i

theorem hT_lin_right {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) (x : S.V) :
    S.hT x (lin u c) = ∑ i, c i * S.hT x (u i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin, map_sum, map_smul, smul_eq_mul]

theorem hT_lin_left {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) (x : S.V) :
    S.hT (lin u c) x = ∑ i, star (c i) * S.hT (u i) x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply]

theorem hT_lin_lin {ι : Type*} [Fintype ι] (u : ι → S.V) (c d : ι → E) :
    S.hT (lin u c) (lin u d) = ∑ i, ∑ j, star (c i) * d j * S.hT (u i) (u j) := by
  rw [hT_lin_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT_lin_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem lin_add {ι : Type*} [Fintype ι] (u : ι → S.V) (c d : ι → E) : lin u (c + d) = lin u c + lin u d := by
  simp [lin, add_smul, Finset.sum_add_distrib]

theorem lin_smul {ι : Type*} [Fintype ι] (u : ι → S.V) (t : E) (c : ι → E) : lin u (t • c) = t • lin u c := by
  simp [lin, smul_smul, Finset.smul_sum]

theorem lin_sub {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) : lin u c ∈ Submodule.span E (Set.range u) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def pc {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (v : S.V) : ι → E :=
  (gram S u u)⁻¹ *ᵥ fun k => S.hT (u k) v

theorem pc_add {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (x y : S.V) :
    pc u (x + y) = pc u x + pc u y := by
  unfold pc
  rw [← Matrix.mulVec_add]
  congr 1
  funext k
  exact map_add (S.hT (u k)) x y

theorem pc_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (t : E) (x : S.V) :
    pc u (t • x) = t • pc u x := by
  unfold pc
  rw [← Matrix.mulVec_smul]
  congr 1
  funext k
  exact map_smul (S.hT (u k)) t x

theorem hT_u_lin {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (c : ι → E) (k : ι) :
    S.hT (u k) (lin u c) = (gram S u u *ᵥ c) k := by
  rw [hT_lin_right]
  simp [Matrix.mulVec, dotProduct, gram, mul_comm]

theorem hT_u_rem {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (v : S.V)
    (k : ι) : S.hT (u k) (v - lin u (pc u v)) = 0 := by
  rw [map_sub, hT_u_lin]
  unfold pc
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  simp

theorem hT_span_rem {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (v z : S.V)
    (hz : z ∈ Submodule.span E (Set.range u)) : S.hT z (v - lin u (pc u v)) = 0 ∧ S.hT (v - lin u (pc u v)) z = 0 := by
  have first : S.hT z (v - lin u (pc u v)) = 0 := by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hT_u_rem u hdet v k
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [LinearMap.map_smulₛₗ₂, hx]
  refine ⟨first, ?_⟩
  rw [← S.herm.eq z, first]
  simp

def isoG {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := v - lin u (pc u v) + lin u' (pc u v)
  map_add' x y := by
    rw [pc_add, lin_add, lin_add]; abel
  map_smul' t x := by
    rw [pc_smul, lin_smul, lin_smul, RingHom.id_apply, smul_add, smul_sub]

theorem isoG_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (v : S.V) :
    isoG u u' v = v - lin u (pc u v) + lin u' (pc u v) := rfl

theorem pc_self {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (m : ι) :
    pc u (u m) = Pi.single m 1 := by
  have hcol : (fun k => S.hT (u k) (u m)) = gram S u u *ᵥ Pi.single m 1 := by
    funext k
    simp [Matrix.mulVec, dotProduct, gram, Pi.single_apply]
  unfold pc
  rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem lin_single {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (m : ι) : lin u (Pi.single m 1) = u m := by
  simp [lin, Pi.single_apply, ite_smul]

private theorem hT_isoG_of_gram_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (hG : gram S u' u' = gram S u u)
    (hdet : (gram S u u).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range u)) (x y : S.V) :
    S.hT (isoG u u' x) (isoG u u' y) = S.hT x y := by
  have hlin : ∀ (w : ι → S.V) (c : ι → E), (∀ i, w i ∈ Submodule.span E (Set.range u)) →
      lin w c ∈ Submodule.span E (Set.range u) := by
    intro w c hw
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hw i)
  have hu : ∀ i, u i ∈ Submodule.span E (Set.range u) := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hgram : ∀ (w : ι → S.V) (c d : ι → E), S.hT (lin w c) (lin w d) =
      ∑ i, ∑ j, star (c i) * d j * gram S w w i j := by
    intro w c d
    rw [hT_lin_lin]
    simp [gram]
  have ex : x = (x - lin u (pc u x)) + lin u (pc u x) := by abel
  have ey : y = (y - lin u (pc u y)) + lin u (pc u y) := by abel
  have gx : isoG u u' x = (x - lin u (pc u x)) + lin u' (pc u x) := by rw [isoG_apply]
  have gy : isoG u u' y = (y - lin u (pc u y)) + lin u' (pc u y) := by rw [isoG_apply]
  have o1 := fun z hz => (hT_span_rem u hdet x z hz)
  have o2 := fun z hz => (hT_span_rem u hdet y z hz)
  have A1 := (o2 _ (hlin u' (pc u x) hsp)).1
  have A2 := (o1 _ (hlin u' (pc u y) hsp)).2
  have B1 := (o2 _ (hlin u (pc u x) hu)).1
  have B2 := (o1 _ (hlin u (pc u y) hu)).2
  conv_rhs => rw [ex, ey]
  rw [gx, gy]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [A1, A2, B1, B2, hgram u', hgram u, hG]

theorem isom_ext {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (hG : gram S u' u' = gram S u u)
    (hdet : (gram S u u).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range u)) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ (∀ i, g (u i) = u' i) ∧
      (∀ w, (∀ k, S.hT (u k) w = 0) → g w = w) ∧
      ∀ v, g v = v + ∑ k, S.hT (u k) v • ∑ m, (gram S u u)⁻¹ m k • (u' m - u m) := by
  haveI := S.fd
  have hinj : Function.Injective (isoG u u') := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply S.nondeg.1 x
    intro y
    rw [← hT_isoG_of_gram_eq u u' hG hdet hsp x y, hx]
    simp
  have hsurj : Function.Surjective (isoG u u') := LinearMap.injective_iff_surjective.mp hinj
  have hbij : Function.Bijective (isoG u u') := ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.ofBijective (isoG u u') hbij, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact hT_isoG_of_gram_eq u u' hG hdet hsp x y
  · intro i
    simp only [LinearEquiv.ofBijective_apply, isoG_apply, pc_self u hdet, lin_single]
    abel
  · intro w hw
    have hp : pc u w = 0 := by
      unfold pc
      have : (fun k => S.hT (u k) w) = 0 := funext hw
      rw [this, Matrix.mulVec_zero]
    simp only [LinearEquiv.ofBijective_apply, isoG_apply, hp]
    simp [lin]
  · intro v
    simp only [LinearEquiv.ofBijective_apply, isoG_apply]
    have key : lin u' (pc u v) - lin u (pc u v) =
        ∑ k, S.hT (u k) v • ∑ m, (gram S u u)⁻¹ m k • (u' m - u m) := by
      simp only [lin, pc, Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← smul_sub,
        Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
    rw [← key]
    abel

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOrbTTermOf
section
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Part

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def clsSet (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (u' : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : PairVal.MatR D) : Set (Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) :=
  {O | ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z,
    O = {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''}}

theorem cntE_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : PairVal.MatR D) :
    CntLocal.cntE (CntLocal.Tn u') F0 Λ Z = (clsSet F0 u' Λ Z).encard := rfl

theorem pd_of_ez {Λ : Submodule (𝓞 D.host.E) (VS D).V} {Z : PairVal.MatR D}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (h : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) : PD D Λ (lf D F0) u' F' :=
  ⟨h.1.1, h.1.2.1, h.2.2.2.1⟩

def termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (h : PD D Λ (lf D F0) u' F') : TermDef.Term D u u' F0 what₂ :=
  ⟨Λ, hΛ, TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F', h⟩⟩

theorem n0rel_refl (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) :
    CntLocal.NilradicalFlagMoved F0 Λ F' F' :=
  ⟨1, ⟨TermDef.one_mem_NLam Λ (lf D F0), fun _ => rfl, rfl⟩, fun _ => rfl, rfl⟩

theorem dcrel_of_n0rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (hl₁ : IsLift Λ F₁) (hl₂ : IsLift Λ F₂) (h : CntLocal.NilradicalFlagMoved F0 Λ F₁ F₂) : DCRel Λ (lf D F0) F₁ F₂ := by
  obtain ⟨n, hn, he, hz⟩ := h
  refine ⟨n, hn.1, 1, TermDef.one_mem_NLam Λ F₁, fun a => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Formalism.L2.SG.Pf.frame_last_td, Formalism.L2.SG.Pf.frame_last_td]
      exact hz.symm
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td, Formalism.L2.SG.Pf.frame_castSucc_td]
      exact (he i).symm
  · rw [hl₂.2, hl₁.2]
    exact hz.symm

theorem orbT_disj {Z : PairVal.MatR D} {γ₁ γ₂ : TermDef.Term D u u' F0 what₂} (hl : γ₁.lam = γ₂.lam)
    {O : Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))}
    (h₁ : O ∈ PairVal.orbT D u u' F0 what₂ γ₁ Z) (h₂ : O ∈ PairVal.orbT D u u' F0 what₂ γ₂ Z) : γ₁ = γ₂ := by
  obtain ⟨Λ₁, m₁, c₁⟩ := γ₁
  obtain ⟨Λ₂, m₂, c₂⟩ := γ₂
  simp only at hl
  subst hl
  obtain ⟨F₁, hF₁, ⟨p₁, hc₁⟩, rfl⟩ := h₁
  obtain ⟨F₂, hF₂, ⟨p₂, hc₂⟩, hO⟩ := h₂
  have hmem := (Set.ext_iff.1 hO F₁).1 ⟨hF₁, n0rel_refl Λ₁ F₁⟩
  have hdc := dcrel_of_n0rel hF₂.1.1 hF₁.1.1 hmem.2
  have e : TermDef.mk Λ₁ (lf D F0) (PD D Λ₁ (lf D F0) u') ⟨F₂, p₂⟩ =
      TermDef.mk Λ₁ (lf D F0) (PD D Λ₁ (lf D F0) u') ⟨F₁, p₁⟩ := Quot.sound hdc
  have hcc : c₁ = c₂ := hc₁.symm.trans (e.symm.trans hc₂)
  subst hcc
  rfl

theorem mem_orbT_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''} ∈
      PairVal.orbT D u u' F0 what₂ (termOf Λ hΛ F' (pd_of_ez hF)) Z :=
  ⟨F', hF, ⟨pd_of_ez hF, rfl⟩, rfl⟩

theorem repIn_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    RepIn u u' F0 what₂ (termOf Λ hΛ F' (pd_of_ez hF)) Z :=
  ⟨F', hF, ⟨pd_of_ez hF, rfl⟩⟩

theorem eligAt_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {w : Point D.host.E (D.R.rS + 1)} (hZ : AtMat w Z) {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    EligAt (termOf Λ hΛ F' (pd_of_ez hF)) w := by
  refine ⟨⟨⟨F', ⟨pd_of_ez hF, rfl⟩, hF.2.2.1⟩, ?_⟩, ⟨F', ⟨pd_of_ez hF, rfl⟩, hF.1.2.2, ?_⟩⟩
  · show TermDef.Gt Λ (lf D F0) (PD D Λ (lf D F0) u') (TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F', _⟩) ≠ 0
    rw [TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _)]
    exact hF.1.2.2
  · obtain ⟨L, U, hL, hU, he⟩ := hZ
    refine ⟨L, U, hL, hU, ?_⟩
    rw [← he]
    congr 1
    exact hF.2.2.2.2

end Part

end Formalism.L2.SG.Pf.FibPart
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PhaseLiftCell
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting

noncomputable section

namespace Formalism.L2.SG.Pf.PhaseLiftCell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem realLink' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.RealObj.ZhatO (Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 v) =
      (ZhatOM (ZhatL (lf D (X.Fu u)) s.frame)).map (fun x => X.B.I.φ v (X.ιE.symm x)) := by
  obtain ⟨M, _, hM1, _, hM3⟩ := s.rep.2.1
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hfam : ∀ (w : D.what₂.Word) (a : Fin (D.R.rS + 1)),
      Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) a =
        rv X.B.I v (X.crd ((X.Fu w).fvec a)) := by
    intro w a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp [Formalism.L2.SG.RealObj.fam, FlagG.fvec, X.flagZVector w, HidaSetting.zR]
    · simp [Formalism.L2.SG.RealObj.fam, FlagG.fvec, X.Fu_e w, HidaSetting.eR]
  ext a b
  simp only [Formalism.L2.SG.RealObj.ZhatO, ZhatOM, Formalism.L2.SG.RealObj.ZX, Formalism.L2.SG.RealObj.Zhat,
    Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Matrix.map_apply, Complex.ofReal_one, one_pow, inv_one,
    one_smul]
  rw [hfam u a, hfam u' b]
  have h1 : Formalism.MainNotions.S.uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
      X.B.I.P v := hM1 v
  rw [h1, Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3, Formalism.L2.SG.PoincareInHH.Cut.hJ_crd]
  have h2 : ZhatL (lf D (X.Fu u)) s.frame a b = (VS D).hT ((X.Fu u).fvec a) (s.lin ((X.Fu u').fvec b)) := by
    rw [← Formalism.L2.SG.Pf.Act.frame_mapLF hiso (X.Fu u') b]
    rfl
  rw [h2, map_mul, map_mul]
  simp only [map_pow, map_neg, map_one]
  rw [X.φ_eq, RingEquiv.apply_symm_apply]
  rfl

theorem liftCell_of_atSome {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) : Formalism.L2.SG.Pf.FinitePhase.LiftCellC X Y u u' κ := by
  intro R ρ s hrel
  obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) :=
    Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcell := ((Formalism.L2.SG.TermDef.atPt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) (Formalism.L2.SG.Pf.cell_function_holds _ _ _)
    ⟨s.1.frame, s.1.rep.2.2.2.2⟩ _).1 hat).2
  obtain ⟨L, U, hL, hU, hLU⟩ := hcell
  refine ⟨L, U, hL, hU, hLU, fun v => ?_⟩
  rw [realLink' X u u' s.1 v]
  exact congrArg (fun Z => Z.map (fun x => X.B.I.φ v (X.ιE.symm x))) hLU

theorem phaseAgreement_of_lift {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) (hF : Formalism.L2.SG.Pf.FinitePhase.FinPhaseC X Y u u' κ) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ :=
  Formalism.L2.SG.Pf.FinitePhase.phaseTieC_of X Y u u' κ (liftCell_of_atSome X Y u u' κ h1) hF

end Formalism.L2.SG.Pf.PhaseLiftCell
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RhoTieCHolds
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Final

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem weight_eq (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (h : Hfin X u) :
    ((Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) : ℕ) : ℝ)⁻¹ =
      wRow D (X.Fu u) (cls X u what₂ h) := by
  obtain ⟨-, δ, hδ, hδe⟩ := cls_spec hR hL h
  have e1 : Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) =
      Nat.card ↥(autLz D (X.Fu u) (cls X u what₂ h)) := by
    rw [show gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom = stabR X u h from rfl, card_stab, card_AH,
      ← hδe, card_autLz_gmap (X.Fu u) hδ]
  rw [e1]
  rfl

theorem massH_rows (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hI : LatInj X u) (hS : LatSurj X u) :
    Formalism.L2.SG.TypedSets.massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (Formalism.L2.SG.TypedSets.frameOf X u) =
      Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) what₂ := by
  rw [massH_eq]
  exact massCl_eq_sum (gamR X u) (kR X u) what₂ (cls X u what₂) (wRow D (X.Fu u))
    (fun h => (cls_spec hR hL h).1) (cls_rel hR hL hI) (cls_surj hR hL hS) (weight_eq X u what₂ hR hL)

end Final

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LatRowLat X u) (hI : Formalism.L2.SG.Pf.LatInj X u) (hS : Formalism.L2.SG.Pf.LatSurj X u) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  Formalism.L2.SG.RhoPf.massH_rows X u (Y.what₂ u) (Y.rowsOK u) hL hI hS

end Formalism.L2.SG.MassDataConc
end
end

