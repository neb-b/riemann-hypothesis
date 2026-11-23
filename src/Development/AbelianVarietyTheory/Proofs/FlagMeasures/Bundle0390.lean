module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0030
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalClassLatticesIffRationalClassLocalFrameP
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.RatCls

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T T' : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'}

theorem principalPolarisation_exists_unique_section : (1 : GV D) ∈ H0 F F' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩

theorem mul_mem_isometriesFixingBothFrames {g h : GV D} (hg : g ∈ H0 F F') (hh : h ∈ H0 F F') : g * h ∈ H0 F F' := by
  refine ⟨Subgroup.mul_mem _ hg.1 hh.1, fun a => ?_, fun a => ?_⟩
  · show g (h (frame F a)) = frame F a
    rw [hh.2.1 a, hg.2.1 a]
  · show g (h (frame F' a)) = frame F' a
    rw [hh.2.2 a, hg.2.2 a]

theorem inv_mem_isometriesFixingBothFrames {h : GV D} (hh : h ∈ H0 F F') : h⁻¹ ∈ H0 F F' := by
  refine ⟨Subgroup.inv_mem _ hh.1, fun a => ?_, fun a => ?_⟩
  · show h.symm (frame F a) = frame F a
    rw [LinearEquiv.symm_apply_eq, hh.2.1 a]
  · show h.symm (frame F' a) = frame F' a
    rw [LinearEquiv.symm_apply_eq, hh.2.2 a]

theorem ext_one (p : PlF D) : Ext p (1 : GV D) 1 := fun _ => rfl

theorem ext_mul {p : PlF D} {g h : GV D} {g' h' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (hg : Ext p g g') (hh : Ext p h h') : Ext p (g * h) (g' * h') := fun x => by
  show g' (h' (baseChange₂ D p x)) = baseChange₂ D p (g (h x))
  rw [hh x, hg (h x)]

theorem ext_inv {p : PlF D} {g : GV D} {g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (hg : Ext p g g') : Ext p g⁻¹ g'⁻¹ := fun x => by
  show g'.symm (baseChange₂ D p x) = baseChange₂ D p (g.symm x)
  rw [LinearEquiv.symm_apply_eq, hg, LinearEquiv.apply_symm_apply]

end GlobalTheory.Unfold.RatCls


open GlobalTheory.Unfold.RatCls in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem GlobalTheory.Unfold.ratCls_agree : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Equivalence (GRel (Z := Z) (FP := FP) F F') ∧ (∀ y y' : Dat Z FP, GRel F F' y y' → (stabY F F' y).encard = (stabY F F' y').encard) ∧ ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (LRel F F' Λ₁ Λ₂ ↔ GRel F F' y₁ y₂) ∧ stabL F F' Λ₁ = stabY F F' y₁ := by
  intro D X Y u u' F F' w hZ hG Z FP hB hR
  have hact : ∀ p, ∃ act : MulAction (FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : (FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : (FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
    intro p
    refine _root_.GlobalTheory.InnerDatumAct.exists_mulAction (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) ?_ (hR p)
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    show D.R.k + D.R.m - 1 = D.R.k + 2 * (D.R.m / 2 - 1) + 1
    omega
  choose act hmv _ using hact
  obtain ⟨hu, hw, -, hlift⟩ := _root_.GlobalTheory.RatLocMove.rat_ext_moves D X Y u u' F F' w hZ hG Z FP hB hR
  have hdict := _root_.GlobalTheory.Unfold.InnerDict.gdat_eq_iff D X Y u u' F F' w hZ hG Z FP hB hR

  have rm_fun : ∀ h ∈ H0 F F', ∀ y y₁ y₂ : Dat Z FP, RMoves h y y₁ → RMoves h y y₂ → y₁ = y₂ := by
    intro h hh y y₁ y₂ r₁ r₂
    funext p
    obtain ⟨g₁, e₁, m₁⟩ := r₁ p
    obtain ⟨g₂, e₂, m₂⟩ := r₂ p
    obtain rfl : g₁ = g₂ := (hu h p).unique e₁ e₂
    have hm := hw h hh p g₁ e₁
    exact ((hmv p ⟨g₁, hm⟩ _ _).1 m₁).symm.trans ((hmv p ⟨g₁, hm⟩ _ _).1 m₂)
  have rm_one : ∀ y : Dat Z FP, RMoves (1 : GV D) y y := by
    intro y p
    refine ⟨1, ext_one p, (hmv p 1 _ _).2 ?_⟩
    letI := act p
    exact one_smul _ _
  have rm_mul : ∀ h₁ ∈ H0 F F', ∀ h₂ ∈ H0 F F', ∀ y y' y'' : Dat Z FP,
      RMoves h₁ y y' → RMoves h₂ y' y'' → RMoves (h₂ * h₁) y y'' := by
    intro h₁ hh₁ h₂ hh₂ y y' y'' r₁ r₂ p
    obtain ⟨g₁, e₁, m₁⟩ := r₁ p
    obtain ⟨g₂, e₂, m₂⟩ := r₂ p
    let a₁ : (FP p).UW0 := ⟨g₁, hw h₁ hh₁ p g₁ e₁⟩
    let a₂ : (FP p).UW0 := ⟨g₂, hw h₂ hh₂ p g₂ e₂⟩
    refine ⟨g₂ * g₁, ext_mul e₂ e₁, (hmv p (a₂ * a₁) _ _).2 ?_⟩
    letI := act p
    have f₁ : a₁ • y p = y' p := (hmv p a₁ _ _).1 m₁
    have f₂ : a₂ • y' p = y'' p := (hmv p a₂ _ _).1 m₂
    show (a₂ * a₁) • y p = y'' p
    rw [mul_smul, f₁, f₂]
  have rm_inv : ∀ h ∈ H0 F F', ∀ y y' : Dat Z FP, RMoves h y y' → RMoves h⁻¹ y' y := by
    intro h hh y y' r p
    obtain ⟨g, e, m⟩ := r p
    let a : (FP p).UW0 := ⟨g, hw h hh p g e⟩
    refine ⟨g⁻¹, ext_inv e, (hmv p a⁻¹ _ _).2 ?_⟩
    letI := act p
    have f : a • y p = y' p := (hmv p a _ _).1 m
    show a⁻¹ • y' p = y p
    rw [inv_smul_eq_iff, f]
  have conj : ∀ h ∈ H0 F F', ∀ y y' : Dat Z FP, RMoves h y y' →
      ∀ k ∈ stabY F F' y, h * k * h⁻¹ ∈ stabY F F' y' := by
    intro h hh y y' hm k hk
    refine ⟨mul_mem_isometriesFixingBothFrames (mul_mem_isometriesFixingBothFrames hh hk.1) (inv_mem_isometriesFixingBothFrames hh), ?_⟩
    rw [mul_assoc]
    exact rm_mul _ (mul_mem_isometriesFixingBothFrames hk.1 (inv_mem_isometriesFixingBothFrames hh)) h hh _ _ _
      (rm_mul _ (inv_mem_isometriesFixingBothFrames hh) k hk.1 _ _ _ (rm_inv h hh y y' hm) hk.2) hm
  refine ⟨⟨fun y => ⟨1, principalPolarisation_exists_unique_section, rm_one y⟩, fun ⟨h, hh, hm⟩ => ⟨h⁻¹, inv_mem_isometriesFixingBothFrames hh, rm_inv h hh _ _ hm⟩,
    fun ⟨h₁, hh₁, m₁⟩ ⟨h₂, hh₂, m₂⟩ => ⟨h₂ * h₁, mul_mem_isometriesFixingBothFrames hh₂ hh₁, rm_mul h₁ hh₁ h₂ hh₂ _ _ _ m₁ m₂⟩⟩, ?_, ?_⟩
  · rintro y y' ⟨h, hh, hm⟩
    have e : stabY F F' y' = (MulAut.conj h) '' stabY F F' y := by
      ext k
      constructor
      · intro hk
        refine ⟨h⁻¹ * k * h⁻¹⁻¹, conj h⁻¹ (inv_mem_isometriesFixingBothFrames hh) y' y (rm_inv h hh y y' hm) k hk, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      · rintro ⟨k, hk, rfl⟩
        exact conj h hh y y' hm k hk
    rw [e, (MulAut.conj h).injective.encard_image]
  · intro Λ₁ Λ₂ y₁ y₂ h₁ h₂
    have key : ∀ h ∈ H0 F F', ∀ (Λ Λ' : LV D) (y y' : Dat Z FP), LocOver Λ y → LocOver Λ' y' →
        (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ' ↔ RMoves h y y') := by
      intro h hh Λ Λ' y y' hl hl'
      obtain ⟨y'', hl'', hm''⟩ := hlift h hh Λ y hl
      rw [hdict _ _ y'' y' hl'' hl']
      constructor
      · rintro rfl
        exact hm''
      · intro hm
        exact rm_fun h hh y y'' y' hm'' hm
    refine ⟨⟨fun ⟨h, hh, he⟩ => ⟨h, hh, (key h hh _ _ _ _ h₁ h₂).1 he⟩,
      fun ⟨h, hh, hm⟩ => ⟨h, hh, (key h hh _ _ _ _ h₁ h₂).2 hm⟩⟩, ?_⟩
    ext h
    exact ⟨fun ⟨hh, he⟩ => ⟨hh, (key h hh _ _ _ _ h₁ h₁).1 he⟩, fun ⟨hh, hm⟩ => ⟨hh, (key h hh _ _ _ _ h₁ h₁).2 hm⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameMiddleConjugateUnipotent
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LoopC

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

theorem rowsLift_mem_orth {U : Submodule E S.V} {x : S.V} :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem rowsLift_fix_span {ι : Type} (v : ι → S.V) (s : Set ι) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ a, n (v a) = v a) : ∀ x ∈ Submodule.span E (v '' s), n x = x := by
  intro x hx
  have hle : Submodule.span E (v '' s) ≤ LinearMap.eqLocus (n : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_eqLocus]
    simpa using hn a
  have h := hle hx
  rw [LinearMap.mem_eqLocus] at h
  simpa using h

theorem rowsLift_map_eq (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hn : ∀ x ∈ U, n x = x) :
    U.map (n : S.V →ₗ[E] S.V) = U := by
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [hn x hx]
  · intro hy
    exact ⟨y, hy, hn y hy⟩

theorem rowsLift_orth_iff (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hn : ∀ x ∈ U, n x = x) (x : S.V) : n x ∈ orth S U ↔ x ∈ orth S U := by
  have hi' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hi
  rw [rowsLift_mem_orth, rowsLift_mem_orth]
  refine forall₂_congr fun y hy => ?_
  have h := hi' y x
  rw [hn y hy] at h
  rw [h]

theorem rowsLift_Lsub_gmap (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hn : ∀ x ∈ Xsp F, n x = x)
    (hq : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  ext y
  unfold Lsub Lrep
  constructor
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨ha1, haO⟩ := Submodule.mem_inf.mp ha
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp ha1
    have hlO : l ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn l).mp haO
    have hd : n l - l ∈ Xsp F := hq l hlO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨l, Submodule.mem_inf.mpr ⟨hl, hlO⟩, (n l - l) + b, (toO S (Xsp F)).add_mem hd hb, ?_⟩, hyO⟩
    show l + (n l - l + b) = n l + b
    abel
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨hl, haO⟩ := Submodule.mem_inf.mp ha
    have hnO : n a ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn a).mpr haO
    have hd : n a - a ∈ Xsp F := hq a haO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨n a, Submodule.mem_inf.mpr ⟨Submodule.mem_map.mpr ⟨a, hl, rfl⟩, hnO⟩, b - (n a - a),
        (toO S (Xsp F)).sub_mem hb hd, ?_⟩, hyO⟩
    abel

theorem rowsLift_cancel (X W : Submodule E S.V) (hXW : ∀ x ∈ X, x ∈ W → x = 0)
    (A B : Submodule (𝓞 E) S.V) (h : (A ⊓ toO S W) ⊔ toO S X = (B ⊓ toO S W) ⊔ toO S X) :
    A ⊓ toO S W ≤ B ⊓ toO S W := by
  intro y hy
  have h1 : y ∈ (A ⊓ toO S W) ⊔ toO S X := Submodule.mem_sup_left hy
  rw [h] at h1
  obtain ⟨b, hb, x, hx, rfl⟩ := Submodule.mem_sup.mp h1
  have hxW : x ∈ W := by
    have h2 : b + x - b ∈ W := W.sub_mem (Submodule.mem_inf.mp hy).2 (Submodule.mem_inf.mp hb).2
    simpa using h2
  rw [hXW x hx hxW, add_zero]
  exact hb

end Generic

theorem rowsLift_X_inf_Wb (D : D7) (x : (hS D).V)
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) (hW : x ∈ Wb D) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).mp hx
  have hW' : (∑ i, c i • D.sp.hypE i) ∈ orth (hS D)
      (Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF)) := hW
  have hc : ∀ j, c j = 0 := by
    intro j
    have h1 : (hS D).hT (D.sp.hypF j) (∑ i, c i • D.sp.hypE i) = 0 :=
      (rowsLift_mem_orth.mp hW') _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
    have hs : ∀ i, (hS D).hT (D.sp.hypF j) (D.sp.hypE i) = if i = j then 1 else 0 := by
      intro i
      rw [← (hS D).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    simpa [hs] using h1
  simp [hc]

theorem rowsLift_fixX {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {n : (hS D).V ≃ₗ[D.host.E] (hS D).V} (hn : FixFr D (lf D F0) n) :
    (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z ∧ ∀ x ∈ F0.X, n x = x := by
  obtain ⟨-, hfr, -⟩ := hn
  have he : ∀ a, n (F0.e a) = F0.e a := by
    intro a
    have h := hfr (Fin.castSucc a)
    simpa [frame, FlagG.fvec, lf] using h
  have hz : n F0.z = F0.z := by
    have h := hfr (Fin.last _)
    simpa [frame, FlagG.fvec, lf] using h
  refine ⟨he, hz, ?_⟩
  intro x hx
  rw [FlagG.X, ← Set.image_univ] at hx
  exact rowsLift_fix_span F0.e Set.univ n he x hx

theorem rowsLift : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) → ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  intro D u _ hT3 _ F0 he hz Λ₁ Λ₂ h₁ h₂ hL
  have hT1 : 1 ≤ Tu D u := by omega
  have hB : IsBase D u F0 := ⟨he, hz⟩
  obtain ⟨n₁, hf₁, hs₁, hr₁⟩ := _root_.GlobalTheory.LoopC.RowSplit.main D u F0 Λ₁ hB h₁ hT1
  obtain ⟨n₂, hf₂, hs₂, hr₂⟩ := _root_.GlobalTheory.LoopC.RowSplit.main D u F0 Λ₂ hB h₂ hT1
  have hfx₁ := rowsLift_fixX hf₁
  have hfx₂ := rowsLift_fixX hf₂
  have hLs : ∀ (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) (Λ : LatV D), FixFr D (lf D F0) n →
      Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) (lf D F0) = Lsub Λ (lf D F0) := by
    intro n Λ hf
    have hX := (rowsLift_fixX hf).2.2
    obtain ⟨hi, -, hq⟩ := hf
    exact rowsLift_Lsub_gmap (lf D F0) Λ n hi hX hq
  have hW : ∀ Λ : LatV D, IsRowLat D F0 Λ → IsSplit D F0 Λ →
      Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X := fun Λ hr hs =>
    ((GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 Λ hT1 hB hr).1 hs).2
  have heq : (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X =
      (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X :=
    (hW _ hr₁ hs₁).symm.trans
      (((hLs n₁ Λ₁ hf₁).trans (hL.trans (hLs n₂ Λ₂ hf₂).symm)).trans (hW _ hr₂ hs₂))
  have hXW : ∀ x ∈ F0.X, x ∈ Wb D → x = 0 := fun x hx hw =>
    rowsLift_X_inf_Wb D x (by rw [← he]; exact hx) hw
  have hM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D) = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D) :=
    le_antisymm (rowsLift_cancel _ _ hXW _ _ heq) (rowsLift_cancel _ _ hXW _ _ heq.symm)
  have e₁ : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₁
  have e₂ : Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₂
  have hMM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ := by
    rw [e₁, e₂, hM]
  have hfix : ∀ v, n₁ v = v → n₂ v = v → (n₁.trans n₂.symm) v = v := by
    intro v h1 h2
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_eq, h2]
  obtain ⟨hi₁, -, hq₁⟩ := hf₁
  obtain ⟨hi₂, -, hq₂⟩ := hf₂
  have hmem : n₁.trans n₂.symm ∈ stabF D F0 := by
    simp only [stabF, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hi₂) hi₁
    · intro j
      exact rowsLift_map_eq (F0.Xa j) (n₁.trans n₂.symm) (fun x hx =>
        rowsLift_fix_span F0.e _ _ (fun a => hfix _ (hfx₁.1 a) (hfx₂.1 a)) x hx)
    · exact hfix _ hfx₁.2.1 hfx₂.2.1
  refine ⟨n₁.trans n₂.symm, hmem, ?_, ?_⟩
  · intro x hx
    have hy : n₁ x ∈ orth (hS D) F0.X := (rowsLift_orth_iff F0.X n₁ hi₁ hfx₁.2.2 x).mpr hx
    obtain ⟨w, hw⟩ : ∃ w, w = n₂.symm (n₁ x) := ⟨_, rfl⟩
    have hnw : n₂ w = n₁ x := by rw [hw, LinearEquiv.apply_symm_apply]
    have hwO : w ∈ orth (hS D) F0.X :=
      (rowsLift_orth_iff F0.X n₂ hi₂ hfx₂.2.2 w).mp (by rw [hnw]; exact hy)
    have h1 : n₁ x - x ∈ F0.X := hq₁ x hx
    have h2 : n₂ w - w ∈ F0.X := hq₂ w hwO
    rw [hnw] at h2
    have h3 : (n₁.trans n₂.symm) x - x = (n₁ x - x) - (n₁ x - w) := by
      rw [LinearEquiv.trans_apply, ← hw]
      abel
    rw [h3]
    exact F0.X.sub_mem h1 h2
  · have hcomp : Formalism.HermitianLatticesTheory.gmap (n₁.trans n₂.symm) Λ₁ =
        Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁) := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    have hback : Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂) = Λ₂ := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    rw [hcomp, hMM, hback]

end GlobalTheory.LoopC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumRationalClassesEqProdLocalSums
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass

theorem datum_wt_nonneg {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} (p : PlF D)
    (a b : LocNG.Datum (FP p)) : 0 ≤ LocNG.Datum.wt a b := by
  unfold LocNG.Datum.wt LocNG.volRel
  exact div_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem tsum_classes_eq_prod_locSums : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP) (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → BaseOK (Tu D u) (Tu D u') F F' P d0 → MassLaw F F' P d0 V → ∀ φ : ∀ p, LocNG.Datum (FP p) → ℝ≥0∞, (∀ p d d', LocNG.Datum.Rel d d' → φ p d = φ p d') → (∀ p d, (¬ ∃ τ, LocNG.IsTermOver (FP p) d τ) → φ p d = 0) → (∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p) else 0) = ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1 := by
  intro D Z FP u u' F F' P d0 R V hV hB hM φ hφ hφ0
  have hEq : ∀ p, Equivalence (LocNG.Datum.Rel (P := FP p)) := fun p => GlobalTheory.NonGenericLocalCheck.rel_equiv (FP p)
  let rep : ∀ p, LocNG.Datum (FP p) → (R p).RD := fun p y =>
    ⟨Classical.choose ((R p).hRD.2.1 y (Set.mem_univ y)), (Classical.choose_spec ((R p).hRD.2.1 y (Set.mem_univ y))).1⟩
  have hrep : ∀ p y, LocNG.Datum.Rel (rep p y).1 y := fun p y =>
    (Classical.choose_spec ((R p).hRD.2.1 y (Set.mem_univ y))).2
  have huniq : ∀ p y (a : (R p).RD), LocNG.Datum.Rel a.1 y → a = rep p y := fun p y a ha =>
    Subtype.ext ((R p).hRD.2.2 _ a.2 _ (rep p y).2 ((hEq p).trans ha ((hEq p).symm (hrep p y))))
  let ext : (∀ p : P, (R p.1).RD) → Dat Z FP := fun x p => if h : p ∈ P then (x ⟨p, h⟩).1 else d0 p
  have ext_in : ∀ x (p : P), ext x p.1 = (x p).1 := fun x p => by simp [ext, p.2]
  have ext_out : ∀ x p, p ∉ P → ext x p = d0 p := fun x p hp => by simp [ext, hp]
  let g : ∀ p : P, (R p.1).RD → ℝ≥0∞ := fun p d => ENNReal.ofReal (LocNG.Datum.wt (d0 p.1) d.1) * φ p.1 d.1

  have hR : ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1
      = ∑' x : (∀ p : P, (R p.1).RD), ENNReal.ofReal V * ∏ p : P, g p (x p) := by
    rw [ENNReal.tsum_mul_left, GlobalTheory.HL.tsum_pi_prod_ennreal g, ← Finset.prod_coe_sort P]

  rw [hR]
  let c : Quot (GRel (Z := Z) (FP := FP) F F') → ℝ≥0∞ := fun o =>
    (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p)

  have hx : ∀ x : (∀ p : P, (R p.1).RD), ENNReal.ofReal V * ∏ p : P, g p (x p)
      = ∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if InGen (ext x) o.out then c o else 0 := by
    intro x
    have h1 : ENNReal.ofReal V * ∏ p : P, g p (x p) = massA F F' (ext x) * ∏ p : P, φ p.1 (x p).1 := by
      by_cases hT : ∀ p : P, ∃ τ, LocNG.IsTermOver (FP p.1) (x p).1 τ
      · have hTall : ∀ p, ∃ τ, LocNG.IsTermOver (FP p) (ext x p) τ := by
          intro p
          by_cases hp : p ∈ P
          · rw [ext_in x ⟨p, hp⟩]; exact hT ⟨p, hp⟩
          · rw [ext_out x p hp]; exact hB.2.2.2.1 p
        rw [hM (ext x) (ext_out x) hTall, ENNReal.ofReal_mul hV,
          ENNReal.ofReal_prod_of_nonneg (fun p _ => datum_wt_nonneg p _ _), ← Finset.prod_coe_sort P, mul_assoc,
          ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl (fun p _ => ?_)
        simp only [g, ext_in x p]
      · push_neg at hT
        obtain ⟨p, hp⟩ := hT
        have h0 : φ p.1 (x p).1 = 0 := hφ0 p.1 _ (by push_neg; exact hp)
        rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp [g, h0]),
          Finset.prod_eq_zero (Finset.mem_univ p) h0, mul_zero, mul_zero]
    rw [h1, massA, ← ENNReal.tsum_mul_right]
    refine tsum_congr (fun o => ?_)
    split_ifs with hI
    · simp only [c]
      rw [← Finset.prod_coe_sort P (fun p => φ p (o.out p))]
      congr 1
      refine Finset.prod_congr rfl (fun p _ => ?_)
      have := hI.1 p.1
      rw [ext_in x p] at this
      exact hφ p.1 _ _ this
    · exact zero_mul _
  rw [tsum_congr hx, ENNReal.tsum_comm]
  refine tsum_congr (fun o => ?_)
  let x0 : ∀ p : P, (R p.1).RD := fun p => rep p.1 (o.out p.1)
  have hfin : ∀ x, {p | o.out p ≠ ext x p} ⊆ {p | o.out p ≠ d0 p} ∪ (P : Set (PlF D)) ∧
      {p | o.out p ≠ d0 p} ⊆ {p | o.out p ≠ ext x p} ∪ (P : Set (PlF D)) := by
    intro x
    constructor
    · intro p hp
      by_cases hpP : p ∈ P
      · exact Or.inr hpP
      · left; simpa [Set.mem_setOf_eq, ext_out x p hpP] using hp
    · intro p hp
      by_cases hpP : p ∈ P
      · exact Or.inr hpP
      · left; simpa [Set.mem_setOf_eq, ext_out x p hpP] using hp
  rw [tsum_eq_single x0]
  · have hiff : InGen (ext x0) o.out ↔ ((∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite) := by
      constructor
      · rintro ⟨hr, hf⟩
        refine ⟨fun p hp => ?_, ((hf.union P.finite_toSet).subset (hfin x0).2)⟩
        have := hr p; rwa [ext_out x0 p hp] at this
      · rintro ⟨hr, hf⟩
        refine ⟨fun p => ?_, ((hf.union P.finite_toSet).subset (hfin x0).1)⟩
        by_cases hp : p ∈ P
        · rw [ext_in x0 ⟨p, hp⟩]; exact hrep p _
        · rw [ext_out x0 p hp]; exact hr p hp
    simp only [hiff, c]
  · intro x hx
    rw [if_neg]
    rintro ⟨hr, _⟩
    apply hx
    funext p
    have := hr p.1
    rw [ext_in x p] at this
    exact huniq p.1 _ (x p) this

end GlobalTheory.GenMass
end
end

