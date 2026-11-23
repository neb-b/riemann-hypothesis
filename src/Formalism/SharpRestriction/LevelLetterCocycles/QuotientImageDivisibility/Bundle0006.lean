module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0004
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpPowSubOne
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem div_exists {m : ℤ} {e : ℤ → V} (he : LB m e) (u : PowerSeries LL)
    (hu : constantCoeff u ≠ 0) (K : ℕ) :
    ∃ d : ℤ → V, LB (m - K) d ∧ smulS ((X * u) ^ K) d = e := by
  set e' : ℤ → V := fun k => e (k + K) with he'
  have hLB' : LB (m - K) e' := fun k hk => he _ (by omega)
  have huK : constantCoeff (u ^ K) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu
  refine ⟨smulS (u ^ K)⁻¹ e', LB_smulS hLB' _, ?_⟩
  rw [mul_pow, smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ huK,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem div_unique {m : ℤ} {d d' : ℤ → V} (hd : LB m d) (hd' : LB m d') (u : PowerSeries LL)
    (hu : constantCoeff u ≠ 0) (K : ℕ) (h : smulS ((X * u) ^ K) d = smulS ((X * u) ^ K) d') :
    d = d' := by
  have huK : constantCoeff (u ^ K) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu
  have h0 : smulS ((X * u) ^ K) (d - d') = 0 := by
    rw [smulS_sub hd hd', h, sub_self]
  rw [mul_pow, smulS_mul (LB_sub hd hd'), smulS_X_pow (LB_smulS (LB_sub hd hd') _)] at h0
  have h1 : smulS (u ^ K) (d - d') = 0 := by
    funext k
    have := congrFun h0 (k + K)
    simpa using this
  have h2 := smulS_inv (LB_sub hd hd') (u ^ K) huK
  rw [h1] at h2
  have h3 : smulS (u ^ K)⁻¹ (0 : ℤ → V) = 0 := by
    funext k
    simp [smulS]
  rw [h3] at h2
  exact sub_eq_zero.1 h2.symm

end Div

section Zero

variable {LL : Type} [Field LL]

theorem exp_pow_sub_one (E : PowerSeries LL) (h0 : constantCoeff E = 1)
    (hd : PowerSeries.derivative (R := LL) E = E) (p : ℕ) :
    ∃ w : PowerSeries LL, E ^ p - 1 = X * w ∧ constantCoeff w = (p : LL) := by
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E = 1 + X * E₁ := by
    refine ⟨PowerSeries.mk fun j => coeff (j + 1) E, ?_⟩
    have := PowerSeries.eq_X_mul_shift_add_const E
    rw [h0, map_one, add_comm] at this
    exact this
  have hc1 : constantCoeff E₁ = 1 := by
    have h1 := congrArg (coeff 0) hd
    rw [PowerSeries.coeff_derivative] at h1
    have h2 : coeff 1 E = constantCoeff E₁ := by
      rw [hE₁]; simp
    simp only [zero_add, Nat.cast_zero, mul_one, coeff_zero_eq_constantCoeff_apply, h0] at h1
    rw [← h2]
    simpa using h1
  refine ⟨E₁ * ∑ j ∈ Finset.range p, (1 + X * E₁) ^ j, ?_, ?_⟩
  · rw [hE₁, ← mul_assoc]
    have g := geom_sum_mul (1 + X * E₁) p
    rw [add_sub_cancel_left] at g
    rw [← g, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_mul, map_sum, hc1, one_mul]
      simp [map_pow]

end Zero

section Simple

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n)

theorem lev_q_simple (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev c ζ W.q = X * u ∧ constantCoeff u ≠ 0 := by
  have hp0 : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one PD.hp.one_lt
  have hπq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [letπ, LocWach.q, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
    exact W.q₀_def
  have hl := congrArg (W.lev c ζ) hπq
  rw [map_mul, map_sub, map_pow, map_add (f := _), map_one] at hl
  rw [hE, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul] at hl
  obtain ⟨w, hw, hw0⟩ := exp_pow_sub_one E hE0 hEd PD.p
  rw [hw] at hl
  have hπc : constantCoeff (W.lev c ζ letπ) ≠ 0 := by
    have := congrArg constantCoeff hE
    rw [map_add (f := _), map_one, map_mul, constantCoeff_C, hE0, mul_one] at this
    intro h0
    rw [h0, add_zero] at this
    exact hζ1 this.symm
  refine ⟨w * (W.lev c ζ letπ)⁻¹, ?_, ?_⟩
  · have h2 : W.lev c ζ letπ * W.lev c ζ W.q * (W.lev c ζ letπ)⁻¹ =
        X * w * (W.lev c ζ letπ)⁻¹ := by rw [hl]
    rw [mul_comm (W.lev c ζ letπ), mul_assoc, PowerSeries.mul_inv_cancel _ hπc, mul_one] at h2
    rw [h2, mul_assoc]
  · rw [map_mul, hw0, PowerSeries.constantCoeff_inv]
    exact mul_ne_zero hp0 (inv_ne_zero hπc)

end Simple

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PchainDNAlt
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Pass

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def Xd (i : ZMod n) (k : ℕ) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).map (W.π₀ • (LinearMap.id : W.DD T →ₗ[O] W.DD T)) ⊔
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.PhiPullΔ W T i).map
      ((Formalism.MainNotions.LiftingTheory.qp W ^ k) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

theorem NDl_N {i : ZMod n} {x : W.DD T} (hx : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) : x ∈ W.N T := by
  have h : x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := hx
  exact h.1

theorem NDl_DL {i : ZMod n} {x : W.DD T} (hx : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := by
  have h : x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := hx
  exact h.2

def Kc (i : ZMod n) : Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) where
  carrier := {z | Formalism.MainNotions.ArcLiftingSetup.cmpD W T (z : W.DD T) = 0}
  add_mem' := fun {a b} ha hb => by
    show Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((a : W.DD T) + b) = 0
    rw [cmpD_add W T (NDl_N W T a.2) (NDl_N W T b.2)]
    rw [show Formalism.MainNotions.ArcLiftingSetup.cmpD W T (a : W.DD T) = 0 from ha,
      show Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b : W.DD T) = 0 from hb, add_zero]
  zero_mem' := cmpD_zero W T
  smul_mem' := fun o z hz => by
    show Formalism.MainNotions.ArcLiftingSetup.cmpD W T (o • (z : W.DD T)) = 0
    rw [cmpD_osmul W T o (NDl_N W T z.2), show Formalism.MainNotions.ArcLiftingSetup.cmpD W T (z : W.DD T) = 0 from hz,
      smul_zero]

theorem Kc_le [IsDomain O] (i : ZMod n) (k : ℕ) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    Kc W T i ≤ (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype := by
  intro z hz
  obtain ⟨y, hyN, hyΔ, hzy⟩ := ker_NDl W T i h3 hmod hR z.2 hz
  rw [pow_one] at hzy
  have hzl : (letE i : LetA O n) • (z : W.DD T) = z := (NDl_DL W T z.2).1
  have hE := Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W i
  have hyE : (letE i : LetA O n) • y ∈ W.NΔ T :=
    Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hE ⟨hyN, hyΔ⟩
  refine Submodule.mem_sup_left (Submodule.mem_map.2 ⟨(letE i : LetA O n) • y, ?_, ?_⟩)
  · exact ⟨hyE.1, by rw [smul_smul, letE_sq], hyE.2⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [aself_comm W T, ← hzy, hzl]
    rfl

theorem pchain_DN (i : ZMod n) (k : ℕ) {m : ℕ} {cc : ℝ} {FF : Type} [AddCommGroup FF]
    [Module O FF] (K : Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))
    (hK : K ≤ (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype) (s : Finset (W.DD T))
    (hs : s.card ≤ m) (hsN : (↑s : Set (W.DD T)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) (L kO : ℕ)
    (hL : Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸
      (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype) ≤ (L : ℕ∞))
    (hkO : lenOl PD (O := O) = kO) (hLc : (L : ℝ) ≤ cc * kO) (A : Submodule O FF)
    (ψ : ↥A →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc A
      (kerSub A ψ (((Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype).map K.mkQ)) 1 1 := by
  set X := (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hXdef
  set Y := (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hYdef
  have hXY : X ≤ Y := Submodule.comap_mono le_sup_left
  have hKY : K ≤ Y := hK.trans hXY
  have hlen : Module.length O ((↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) ⧸ Y.map K.mkQ) ≤ (L : ℕ∞) := by
    rw [(Submodule.quotientQuotientEquivQuotient K Y hKY).length_eq]
    exact hL
  have h1 := pstep_len (m := m) (c := cc) A ψ (Y.map K.mkQ) L kO hlen hkO hLc
  set A₁ := kerSub A ψ (Y.map K.mkQ) with hA₁def
  have hA₁ : A₁ ≤ A := kerSub_le A ψ _
  set ψ₁ : ↥A₁ →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K := ψ.comp (Submodule.inclusion hA₁)
  set sN : Finset ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) := s.subtype (· ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)
  set s' := sN.image K.mkQ
  have hcard : s'.card ≤ m := by
    refine Finset.card_image_le.trans (le_trans ?_ hs)
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hspan : Submodule.span O (↑s : Set (W.DD T)) =
      (Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))).map
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hsN hy⟩, Finset.mem_subtype.2 hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_subtype.1 hz
  have hY : Y ≤ X ⊔ Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) := by
    intro z hz
    have hz' : (z : W.DD T) ∈ Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T)) := hz
    obtain ⟨x, hx, t, ht, hxt⟩ := Submodule.mem_sup.1 hz'
    rw [hspan] at ht
    obtain ⟨t', ht', rfl⟩ := Submodule.mem_map.1 ht
    have hxN : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i := by
      have e : x = (z : W.DD T) - (t' : W.DD T) := by rw [← hxt]; simp
      rw [e]; exact (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).sub_mem z.2 t'.2
    refine Submodule.mem_sup.2 ⟨⟨x, hxN⟩, hx, t', ht', Subtype.ext ?_⟩
    simpa using hxt
  have hgen : ∀ a, ψ₁ a ∈ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
    intro a
    have ha : ψ ⟨(a : FF), hA₁ a.2⟩ ∈ Y.map K.mkQ := (mem_kerSub_coe A ψ _ ⟨a, hA₁ a.2⟩).1 a.2
    have hle : Y.map K.mkQ ≤ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
      calc Y.map K.mkQ ≤ (X ⊔ Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_mono hY
        _ = X.map K.mkQ ⊔ (Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_sup _ _ _
        _ = X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
          rw [Submodule.map_span, Finset.coe_image]
    exact hle ha
  have h2 := pstep_gen (lenO := lenOl PD (O := O)) (m := m) (c := cc) A₁ ψ₁ (X.map K.mkQ) s' hcard hgen
  have heq : kerSub A₁ ψ₁ (X.map K.mkQ) = kerSub A ψ (X.map K.mkQ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A₁ ψ₁ _ x).1 hx
      exact (mem_kerSub A ψ _ x).2 ⟨hA₁ hx1, hx2⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A ψ _ x).1 hx
      have hx1' : x ∈ A₁ := (mem_kerSub A ψ _ x).2 ⟨hx1, Submodule.map_mono hXY hx2⟩
      exact (mem_kerSub A₁ ψ₁ _ x).2 ⟨hx1', hx2⟩
  rw [heq] at h2
  exact (pchain_of_len h1).trans (pchain_of_gen h2)

end Pass

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Pi0PowSmulInjective
section
set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.RL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

section Map

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

theorem map_smulA (a : LetA O n) (x : W.DD T₁) : W.map F (a • x) = a • W.map F x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

theorem map_γ' (x : W.DD T₁) : W.map F (W.γ T₁ x) = W.γ T₂ (W.map F x) := W.map_γ F W.gam x

variable (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ)
include hc₁ hc₂

theorem inPN_map {k : ℕ} {x : W.DD T₁} (h : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₁ k x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ k (W.map F x) := by
  obtain ⟨y, hy, hΔ, rfl⟩ := h
  exact ⟨W.map F y, W.map_N F hc₁ hc₂ y hy, fun δ hδ => by rw [← W.map_γ, hΔ δ hδ],
    map_smulA W F _ y⟩

theorem dl_map {i : ZMod n} {x : W.DD T₁} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ i x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i (W.map F x) :=
  ⟨by rw [← map_smulA, h.1], fun δ hδ => by rw [← W.map_γ, h.2 δ hδ]⟩

theorem polesFin_map {x : W.DD T₁} (h : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T₁ x) :
    Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T₂ (W.map F x) := by
  obtain ⟨k, K, hK⟩ := h
  exact ⟨k, K, by rw [← map_smulA]; exact W.map_N F hc₁ hc₂ _ hK⟩

theorem inI_map {i : ZMod n} {x : W.DD T₁} (h : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ i x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ i (W.map F x) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨dl_map W F hc₁ hc₂ h1, polesFin_map W F hc₁ hc₂ h2, ?_⟩
  rw [← map_γ', ← map_sub]
  exact inPN_map W F hc₁ hc₂ h3

end Map

theorem mem_Z1DΔ_iff (T : LocLat G Qp LL O) (p : W.DD T × W.DD T) :
    p ∈ W.wachCocyclesDelta T ↔ (W.γD T W.gamK p.1 - p.1 = W.φD T p.2 - p.2) ∧
      ∀ δ ∈ W.DelF, W.γD T δ p.1 = p.1 ∧ W.γD T δ p.2 = p.2 := by
  simp only [LocWach.wachCocyclesDelta, herrZ1Δ, herrCocycles, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.neg_apply,
    Submodule.mem_iInf, LinearMap.prodMap_apply, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero, sub_zero, add_neg_eq_zero, sub_eq_zero]

theorem map_mem_Z1DΔ {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (p : ↥(W.wachCocyclesDelta T₁)) :
    ((W.map F (p : W.DD T₁ × W.DD T₁).1, W.map F (p : W.DD T₁ × W.DD T₁).2) : W.DD T₂ × W.DD T₂) ∈
      W.wachCocyclesDelta T₂ := by
  obtain ⟨h1, h2⟩ := (mem_Z1DΔ_iff W T₁ _).1 p.2
  refine (mem_Z1DΔ_iff W T₂ _).2 ⟨?_, fun δ hδ => ?_⟩
  · simp only
    rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, h1]
  · simp only
    rw [← W.map_γ, ← W.map_γ, (h2 δ hδ).1, (h2 δ hδ).2]
    exact ⟨rfl, rfl⟩

theorem letE_mul_self' (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem pullJ_letter (T : LocLat G Qp LL O) (c : ZMod n) {P : W.DD T}
    (hP : P ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1) : (letE (c + 1) : LetA O n) • P = P := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨-, hyD⟩, rfl⟩ := hx
    rw [pow_one]
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.letter_phi W T (c + 1) (by rw [add_sub_cancel_right]; exact hyD.1)
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | smul a x _ hx => rw [smul_comm, hx]

theorem pullJ_le_φpull (T : LocLat G Qp LL O) (c : ZMod n) :
    Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1 ≤ W.φpull T := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ LocWach.φpull
  refine Submodule.span_mono ?_
  rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
  exact ⟨y, hy, by rw [pow_one]⟩

theorem trunc_letter (T : LocLat G Qp LL O) (c : ZMod n) {M X σ : ℕ} {w z : W.DD T}
    (hw : (letE c : LetA O n) • w = w) (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T c 1 M X σ w z) :
    (letE (c + 1) : LetA O n) • z = z := by
  obtain ⟨cs, r, s, hser, -, rfl⟩ := hz
  have hφ : ∀ y : W.DD T, (letE c : LetA O n) • y = y →
      (letE (c + 1) : LetA O n) • ((W.φD T) ^ 1) y = ((W.φD T) ^ 1) y := by
    intro y hy
    rw [pow_one]
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.letter_phi W T (c + 1) (by rw [add_sub_cancel_right]; exact hy)
  rw [smul_sub, smul_comm, hφ w hw, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_comm, hφ _ (hser.2.1 y).1.1]

theorem pk_succ (j : ℕ) : W.φA (Formalism.MainNotions.LiftingTheory.pk W j) = Formalism.MainNotions.LiftingTheory.pk W (j + 1) := by
  simp only [Formalism.MainNotions.LiftingTheory.pk, pow_succ', AlgHom.mul_apply]

theorem trunc_polesFin (T : LocLat G Qp LL O) (c : ZMod n) (η σ : ℕ) {w z : W.DD T}
    (hw : Formalism.MainNotions.CrystallineLiftingInputs.InI W T c w)
    (hz : (letE (c + 1) : LetA O n) • z = z)
    (hpull : z - ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ 1) w ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1)
    (h4 : ∀ x : W.DD T, x ∈ W.φpull T → (letE (c + 1) : LetA O n) • x = x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ W.N T) :
    Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T z := by
  obtain ⟨⟨hwc, -⟩, ⟨k, K, hK⟩, -⟩ := hw
  set P := z - ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ 1) w with hPdef
  have hwl : (letE (c + 1) : LetA O n) • W.φD T w = W.φD T w :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.letter_phi W T (c + 1) (by rw [add_sub_cancel_right]; exact hwc)
  have hPl : (letE (c + 1) : LetA O n) • P = P := pullJ_letter W T c hpull
  have hP : Formalism.MainNotions.LiftingTheory.qp W ^ η • P ∈ W.N T := h4 P (pullJ_le_φpull W T c hpull) hPl
  set a : LetA O n := (∏ j ∈ Finset.range k, Formalism.MainNotions.LiftingTheory.pk W j) ^ K with ha
  set Pq : LetA O n := ∏ j ∈ Finset.range k, Formalism.MainNotions.LiftingTheory.pk W (j + 1) with hPq
  have hφa : W.φD T (a • w) = Pq ^ K • W.φD T w := by
    have e := Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul W T 1 a w
    rw [pow_one, pow_one] at e
    rw [e, ha, map_pow, map_prod]
    simp only [pk_succ, hPq]
  have hφN : Pq ^ K • W.φD T w ∈ W.φpull T := by
    rw [← hφa]
    exact Submodule.subset_span ⟨a • w, hK, rfl⟩
  have hφl : (letE (c + 1) : LetA O n) • (Pq ^ K • W.φD T w) = Pq ^ K • W.φD T w := by
    rw [smul_comm, hwl]
  have hφq : Formalism.MainNotions.LiftingTheory.qp W ^ η • (Pq ^ K • W.φD T w) ∈ W.N T := h4 _ hφN hφl
  refine ⟨k + 1, K + η, ?_⟩
  have hprod : ∏ j ∈ Finset.range (k + 1), Formalism.MainNotions.LiftingTheory.pk W j = Pq * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [Finset.prod_range_succ']
    simp [Formalism.MainNotions.LiftingTheory.pk, hPq]
  rw [hprod]
  have hz' : z = P + ((PD.p : ℕ) : O) ^ σ • W.φD T w := by rw [hPdef, pow_one, sub_add_cancel]
  rw [hz', smul_add]
  refine (W.N T).add_mem ?_ ?_
  · have e : (Pq * Formalism.MainNotions.LiftingTheory.qp W) ^ (K + η) =
        (Pq ^ (K + η) * Formalism.MainNotions.LiftingTheory.qp W ^ K) * Formalism.MainNotions.LiftingTheory.qp W ^ η := by ring
    rw [e, mul_smul]
    exact (W.N T).smul_mem _ hP
  · have e : (Pq * Formalism.MainNotions.LiftingTheory.qp W) ^ (K + η) =
        (Pq ^ η * Formalism.MainNotions.LiftingTheory.qp W ^ K) * (Formalism.MainNotions.LiftingTheory.qp W ^ η * Pq ^ K) := by ring
    rw [e, smul_comm _ (((PD.p : ℕ) : O) ^ σ), mul_smul]
    refine Submodule.smul_of_tower_mem _ _ ((W.N T).smul_mem _ ?_)
    rw [mul_smul]
    exact hφq

theorem pi0_pow_smul_injective (T : LocLat G Qp LL O)
    (hu : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1)) (M : ℕ) {y y' : W.DD T}
    (h : W.π₀ ^ M • y = W.π₀ ^ M • y') : y = y' := by
  obtain ⟨u, hu⟩ := hu
  have hunit : IsUnit (algebraMap (LetA O n) W.EE (W.π₀ ^ M)) := by
    rw [map_pow, hu, map_mul, map_pow]
    exact IsUnit.pow _ (IsUnit.mul (u.isUnit.map _) (W.EE_π.pow _))
  rw [← algebraMap_smul W.EE (W.π₀ ^ M) y, ← algebraMap_smul W.EE (W.π₀ ^ M) y'] at h
  exact (hunit.smul_left_cancel).1 h

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem inPN_of_inv (T : LocLat G Qp LL O)
    (hu : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1))
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀) (M : ℕ) {x y : W.DD T} (hy : y ∈ W.N T)
    (hx : x = W.π₀ ^ M • y) (hxΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T M x := by
  refine ⟨y, hy, fun δ hδ => pi0_pow_smul_injective W T hu M ?_, hx⟩
  have := hxΔ δ hδ
  rw [hx, γD_smulA, map_pow, hΔπ δ hδ] at this
  exact this

theorem mem_ImF_of_cls {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (p : ↥(latticeCocycles T₂.L))
    (h : Submodule.Quotient.mk p ∈ (latticeFiniteCohomology PD T₁.L).map F.H1map) : (p : G → T₂.V) ∈ F.ImF PD := by
  obtain ⟨x, hx, hxp⟩ := h
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
  have hcZ : (c : G → T₁.V) ∈ latticeCocycles T₁.L := c.2
  have h0 : (Submodule.Quotient.mk (p - ⟨F.post c, F.post_Z1T c hcZ⟩) : LatticeCohomology T₂.L) = 0 := by
    rw [Submodule.Quotient.mk_sub, ← hxp]
    simp only [Submodule.mkQ_apply]
    rw [sub_eq_zero]
    rfl
  rw [Submodule.Quotient.mk_eq_zero] at h0
  have h2 : (p : G → T₂.V) = F.post c + ((p - ⟨F.post c, F.post_Z1T c hcZ⟩ : ↥(latticeCocycles T₂.L)) : G → T₂.V) := by
    simp
  rw [h2]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc) h0

end Formalism.MainNotions.N.Pv.LocalLengthBound.RL
end
end

