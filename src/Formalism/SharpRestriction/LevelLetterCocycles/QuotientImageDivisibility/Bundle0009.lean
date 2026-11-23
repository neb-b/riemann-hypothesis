module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasics
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def GenUnitsC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (s : ℕ) (u : ℤ_[l]ˣ),
    ((u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) → ((u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) →
      Subgroup.closure (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) = ⊤

section Parts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevBasics (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  inj : Function.Injective (algebraMap O F)
  hp : ((PD.p : ℕ) : F) ≠ 0
  root : ∃ ζ : F, IsPrimitiveRoot ζ (PD.p ^ (s + 1))
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ (ζ : Rs F PD.p s) (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ : Rs F PD.p s, ev ζ (letE a) = 1
  ev_π : ∀ ζ : Rs F PD.p s, ev ζ letπ = (ζ : F) - 1
  ev_ps : ∀ ζ : Rs F PD.p s, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ : Rs F PD.p s, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g (ζ : Rs F PD.p s) x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤

end Parts

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.QpEqUnit
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Trans

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem qp_eq_unit (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∃ U : (LetA O n)ˣ, Formalism.MainNotions.LiftingTheory.qp W = (U : LetA O n) * W.Q := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))
      W.π₀ = Formalism.MainNotions.LiftingTheory.qp W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]
  rw [hE] at hw
  refine ⟨w⁻¹, ?_⟩
  rw [Q_eq_q W hs, hw, ← mul_assoc, Units.inv_mul, one_mul]

theorem trans_d [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (c : ZMod n)
    (δ : W.Gam) (hδ : δ ∈ W.DelF) (ζ ζ' : LL) (χ : LL) (hχ0 : χ ≠ 0)
    (hΔN : ∀ (x : ↥(W.N T)) (hx : W.γD T δ x ∈ W.N T) (k : ℤ),
      W.levN T c ζ ⟨W.γD T δ x, hx⟩ k = χ ^ k • W.levN T c ζ' x k)
    (hΔA : ∀ f : LetA O n, W.lev c ζ (W.γA δ f) = PowerSeries.rescale χ (W.lev c ζ' f))
    {w : W.DD T} (hwΔ : W.γD T δ w = w) {K : ℕ} (hK : W.Q ^ K • w ∈ W.N T)
    (u u' : PowerSeries LL) (hu : W.lev c ζ W.q = X * u) (hu' : W.lev c ζ' W.q = X * u')
    (hu0 : constantCoeff u ≠ 0)
    {dz dz' : ℤ → T.V ⊗[Qp] BdR} (hdz : ∃ m, LB m dz) (hdz' : ∃ m, LB m dz')
    (ez : W.levN T c ζ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u) ^ K) dz)
    (ez' : W.levN T c ζ' ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u') ^ K) dz') :
    dz = resc χ dz' := by
  obtain ⟨m, hm⟩ := hdz
  obtain ⟨m', hm'⟩ := hdz'
  have hQ : W.Q = W.q := Q_eq_q W hs
  obtain ⟨U, hU⟩ := qp_eq_unit W hs hR
  have hxeq : Formalism.MainNotions.LiftingTheory.qp W ^ K • w = (U : LetA O n) ^ K • (W.Q ^ K • w) := by
    rw [hU, mul_pow, mul_smul]
  have hxN : Formalism.MainNotions.LiftingTheory.qp W ^ K • w ∈ W.N T := by
    rw [hxeq]; exact (W.N T).smul_mem _ hK
  have hxΔ : W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ K • w) = Formalism.MainNotions.LiftingTheory.qp W ^ K • w := by
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', map_pow, (qp_mem_AΔ W hR) δ hδ, hwΔ]
  set x : ↥(W.N T) := ⟨Formalism.MainNotions.LiftingTheory.qp W ^ K • w, hxN⟩ with hxdef
  have hγx : W.γD T δ (x : W.DD T) ∈ W.N T := by rw [hxdef]; simp only; rw [hxΔ]; exact hxN
  have h1 : W.levN T c ζ x = resc χ (W.levN T c ζ' x) := by
    funext k
    simp only [resc]
    have hxx : (⟨W.γD T δ (x : W.DD T), hγx⟩ : ↥(W.N T)) = x := Subtype.ext hxΔ
    rw [← hΔN x hγx k, hxx]
  have hsplit : x = (U : LetA O n) ^ K • (⟨W.Q ^ K • w, hK⟩ : ↥(W.N T)) := Subtype.ext hxeq
  have h2 : ∀ (z : LL) (uz : PowerSeries LL) (dd : ℤ → T.V ⊗[Qp] BdR) (mm : ℤ), LB mm dd →
      W.levN T c z ⟨W.Q ^ K • w, hK⟩ = smulS ((X * uz) ^ K) dd →
      W.levN T c z x = smulS ((W.lev c z (U : LetA O n) * (X * uz)) ^ K) dd := by
    intro z uz dd mm hdd e
    rw [hsplit]
    have this : W.levN T c z ((U : LetA O n) ^ K • (⟨W.Q ^ K • w, hK⟩ : ↥(W.N T))) =
        smulS (W.lev c z ((U : LetA O n) ^ K)) (W.levN T c z ⟨W.Q ^ K • w, hK⟩) :=
      funext fun k => W.levN_smul T c z ((U : LetA O n) ^ K) ⟨W.Q ^ K • w, hK⟩ k
    rw [this, e, ← smulS_mul hdd, map_pow, ← mul_pow]
  have hz := h2 ζ u dz m hm ez
  have hz' := h2 ζ' u' dz' m' hm' ez'
  have hresc : PowerSeries.rescale χ (W.lev c ζ' (U : LetA O n) * (X * u')) =
      W.lev c ζ (U : LetA O n) * (X * u) := by
    have e1 : W.lev c ζ' (U : LetA O n) * (X * u') = W.lev c ζ' (Formalism.MainNotions.LiftingTheory.qp W) := by
      rw [hU, map_mul, hQ, hu']
    have e2 : W.lev c ζ (U : LetA O n) * (X * u) = W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W) := by
      rw [hU, map_mul, hQ, hu]
    rw [e1, e2, ← hΔA, (qp_mem_AΔ W hR) δ hδ]
  rw [h1, hz', ← smulS_rescale hm' χ hχ0, map_pow, hresc] at hz
  have hUc : constantCoeff (W.lev c ζ (U : LetA O n) * u) ≠ 0 := by
    rw [map_mul]
    refine mul_ne_zero ?_ hu0
    have hu1 : IsUnit (W.lev c ζ (U : LetA O n)) := (Units.isUnit U).map _
    exact (PowerSeries.isUnit_iff_constantCoeff.1 hu1).ne_zero
  have e3 : W.lev c ζ (U : LetA O n) * (X * u) = X * (W.lev c ζ (U : LetA O n) * u) := by ring
  rw [e3] at hz
  exact div_unique (m := min m m') (LB_mono hm (min_le_left _ _))
    (LB_mono (LB_resc hm' χ) (min_le_right _ _)) _ hUc K hz.symm

end Trans

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div2

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem smulS_div_mem {m : ℤ} {e : ℤ → V} (he : LB m e) (D : Submodule LL V) (hD : ∀ k, e k ∈ D)
    (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (m' : ℤ) (d : ℤ → V), LB m' d ∧ smulS f d = e ∧ ∀ k, d k ∈ D := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  set e' : ℤ → V := fun k => e (k + w) with he'
  have hLB' : LB (m - w) e' := fun k hk => he _ (by omega)
  refine ⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_, smulS_mem hLB' D (fun k => hD _) _⟩
  rw [smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem smulS_linMap {V' : Type} [AddCommGroup V'] [Module LL V'] (Φ : V →ₗ[LL] V') {m : ℤ}
    {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) :
    Φ (smulS g f k) = smulS g (fun j => Φ (f j)) k := by
  have hf' : LB m (fun j => Φ (f j)) := fun j hj => by simp [hf j hj]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N :=
    ⟨Int.toNat (k - m) + 1, by have := Int.self_le_toNat (k - m); push_cast; omega⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, map_sum]
  simp [map_smul]

end Div2

section Rules

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem levN_smulS (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) :
    W.levN T i ζ (a • x) = smulS (W.lev i ζ a) (W.levN T i ζ x) := by
  funext k
  rw [W.levN_smul]
  rfl

theorem isExp_unique (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T}
    {d d' : ℤ → T.V ⊗[Qp] BdR} (hd : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d)
    (hd' : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d') : d = d' := by
  obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hd
  obtain ⟨⟨m', hm'⟩, a', ha', hla', he'⟩ := hd'
  have hdl : LB (min m m') d := fun k hk => hm k (by omega)
  have hdl' : LB (min m m') d' := fun k hk => hm' k (by omega)
  have hlev : W.levN T i ζ ⟨a • x, ha⟩ = smulS (W.lev i ζ a) d := funext he
  have hlev' : W.levN T i ζ ⟨a' • x, ha'⟩ = smulS (W.lev i ζ a') d' := funext he'
  have e : a' • (⟨a • x, ha⟩ : ↥(W.N T)) = a • (⟨a' • x, ha'⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_smul, smul_smul, mul_comm])
  have h := congrArg (W.levN T i ζ) e
  rw [levN_smulS, levN_smulS, hlev, hlev', ← smulS_mul hdl, ← smulS_mul hdl', mul_comm] at h
  exact smulS_inj hdl hdl' _ (mul_ne_zero hla hla') h

theorem expRules_of (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (hN : GamN W) (hA' : GamA W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := by
  intro hA T hT i ζ hζ
  have hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i := fun x k => by
    have := (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1 x k
    rw [Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero] at this
    exact (Submodule.mem_inf.1 this).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x a ha hla
    obtain ⟨m, hm⟩ := W.levN_supp T i ζ ⟨a • x, ha⟩
    obtain ⟨m', d, hd, hde⟩ := smulS_div (m := m) hm _ hla
    have hE : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d :=
      ⟨⟨m', hd⟩, a, ha, hla, fun k => (congrFun hde k).symm⟩
    exact ⟨d, hE, fun d' hd' => isExp_unique W T i ζ hd' hE⟩
  ·
    intro x d _ hx k
    obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hx
    obtain ⟨m₀, hm₀⟩ := W.levN_supp T i ζ ⟨a • x, ha⟩
    obtain ⟨m', d₀, hd₀, hde₀, hmem⟩ := smulS_div_mem (m := m₀) hm₀ (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i)
      (fun k => hLv _ k) _ hla
    have hE₀ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d₀ :=
      ⟨⟨m', hd₀⟩, a, ha, hla, fun k => (congrFun hde₀ k).symm⟩
    rw [isExp_unique W T i ζ ⟨⟨m, hm⟩, a, ha, hla, he⟩ hE₀]
    exact hmem k
  ·
    rintro x y d e ⟨⟨m, hm⟩, a, ha, hla, hd⟩ ⟨⟨m', hm'⟩, b, hb, hlb, he⟩
    have hdl : LB (min m m') d := fun k hk => hm k (by omega)
    have hel : LB (min m m') e := fun k hk => hm' k (by omega)
    have hmem : (a * b) • (x + y) ∈ W.N T := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
      exact (W.N T).add_mem ((W.N T).smul_mem b ha) ((W.N T).smul_mem a hb)
    refine ⟨⟨min m m', LB_add hdl hel⟩, a * b, hmem, by rw [map_mul]; exact mul_ne_zero hla hlb,
      fun k => ?_⟩
    have e1 : (⟨(a * b) • (x + y), hmem⟩ : ↥(W.N T)) =
        b • (⟨a • x, ha⟩ : ↥(W.N T)) + a • (⟨b • y, hb⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        simp only [Submodule.coe_add, SetLike.val_smul]
        rw [smul_add, smul_smul, smul_smul, mul_comm b a])
    rw [e1, map_add (f := _), Pi.add_apply, levN_smulS, levN_smulS, funext hd, funext he]
    show smulS (W.lev i ζ b) (smulS (W.lev i ζ a) d) k + smulS (W.lev i ζ a) (smulS (W.lev i ζ b) e) k =
      smulS (W.lev i ζ (a * b)) (d + e) k
    rw [map_mul, smulS_add hdl hel, ← smulS_mul hdl, ← smulS_mul hel, mul_comm (W.lev i ζ b)]
    rfl
  ·
    rintro c x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • (c • x) ∈ W.N T := by
      rw [smul_comm]; exact (W.N T).smul_of_tower_mem c ha
    refine ⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • (c • x), hmem⟩ : ↥(W.N T)) =
        (algebraMap O (LetA O n) c) • (⟨a • x, ha⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        simp only [SetLike.val_smul]
        rw [algebraMap_smul, smul_comm])
    rw [e1, levN_smulS, funext hd, AlgHom.commutes, PowerSeries.algebraMap_apply]
    show smulS (PowerSeries.C (algebraMap O LL c)) (smulS (W.lev i ζ a) d) k =
      smulS (W.lev i ζ a) (fun k => algebraMap O LL c • d k) k
    rw [smulS_C (LB_smulS hm _)]
    have e2 : (fun k => algebraMap O LL c • d k) = algebraMap O LL c • d := rfl
    rw [e2, smulS_smul hm]
  ·
    rintro a' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • (a' • x) ∈ W.N T := by
      rw [smul_comm]; exact (W.N T).smul_mem a' ha
    refine ⟨⟨m, LB_smulS hm _⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • (a' • x), hmem⟩ : ↥(W.N T)) = a' • (⟨a • x, ha⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_comm])
    rw [e1, levN_smulS, funext hd]
    show smulS (W.lev i ζ a') (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (smulS (W.lev i ζ a') d) k
    rw [smulS_comm hm]
  ·
    rintro x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hχ : algebraMap O LL (W.χΓ W.gam : O) ≠ 0 :=
      ((Units.isUnit (W.χΓ W.gam)).map (algebraMap O LL)).ne_zero
    have hγN' : W.γ T (a • x) ∈ W.N T := W.N_Γ T W.gam _ ha
    have hmem : W.γA W.gam a • W.γ T x ∈ W.N T := by
      have h := hγN'
      change W.γD T W.gam (a • x) ∈ W.N T at h
      rw [RL.γD_smulA] at h
      exact h
    refine ⟨⟨m, LB_resc hm _⟩, W.γA W.gam a, hmem, ?_, fun k => ?_⟩
    · rw [hA' i ζ hζ a]
      intro h0
      exact hla (PowerSeries.rescale_injective hχ (h0.trans (map_zero _).symm))
    · have e1 : (⟨W.γA W.gam a • W.γ T x, hmem⟩ : ↥(W.N T)) =
          ⟨W.γ T ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), hγN'⟩ :=
        Subtype.ext (RL.γD_smulA W T W.gam a x).symm
      rw [e1, hN T hT i ζ hζ ⟨a • x, ha⟩ hγN' k, funext hd, hA' i ζ hζ a]
      show algebraMap O LL (W.χΓ W.gam : O) ^ k • smulS (W.lev i ζ a) d k =
        smulS (PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ a))
          (resc (algebraMap O LL (W.χΓ W.gam : O)) d) k
      rw [smulS_rescale hm _ hχ]
      rfl
  ·
    rintro T' F hT' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • W.map F x ∈ W.N T' := by
      rw [← RL.map_smulA]; exact W.map_N F hT hT' _ ha
    refine ⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • W.map F x, hmem⟩ : ↥(W.N T')) =
        ⟨W.map F ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), by rw [← RL.map_smulA] at hmem; exact hmem⟩ :=
      Subtype.ext (RL.map_smulA W F a x).symm
    rw [e1, W.levN_map F hT hT' i ζ, hd]
    exact smulS_linMap _ hm _ k

end Rules

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

