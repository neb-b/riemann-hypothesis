module

public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterIdempotentOfFixed

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CoboundaryMemInvariantCocycles
section
noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2C

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L
open Formalism.MainNotions.N.Pv.LocalLengthBound

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem coboundary_mem_invariant_cocycles {m : W.DD T} (hm : ∀ δ ∈ W.DelF, W.γD T δ m = m) :
    ((W.φD T m - m, W.γD T W.gamK m - m) : W.DD T × W.DD T) ∈ W.wachCocyclesDelta T := by
  refine (RL.mem_Z1DΔ_iff W T _).2 ⟨?_, fun δ hδ => ⟨?_, ?_⟩⟩
  · simp only [map_sub, W.φγ_comm]
    abel
  · simp only [map_sub, gammaD_frobenius_comm, hm δ hδ]
  · simp only [map_sub]
    rw [← W.γD_mul, mul_comm, W.γD_mul, hm δ hδ]

theorem sum_clK_eq_pow_smul_clK_of_level_decomposition [NeZero n] (M s σ : ℕ) (ev : Finset (ZMod n)) (hgam : W.gamK = W.gam)
    (hπ : W.π₀ ∈ W.AΔ)
    (hF2 : ∀ w, InPN W T M w → ∃! z, InPN W T M z ∧ W.φD T z - z = w)
    (hF3 : ∀ (i : ZMod n) (x : ↥(W.wachCocyclesDelta T)), DL W T i (x : W.DD T × W.DD T).1 →
      InPN W T M (x : W.DD T × W.DD T).2 → InPN W T M (x : W.DD T × W.DD T).1 → W.clK T x = 0)
    (hcob : ∀ x : ↥(W.wachCocyclesDelta T), (∃ m : W.DD T, (∀ δ ∈ W.DelF, W.γD T δ m = m) ∧
      (x : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) → W.clK T x = 0)
    (yz : ↥(W.wachCocyclesDelta T)) (mE : W.DD T) (hmE : ∀ δ ∈ W.DelF, W.γD T δ mE = mE)
    (Y : ZMod n → W.DD T) (x : ZMod n → ↥(W.wachCocyclesDelta T))
    (hY1 : ((PD.p : ℕ) : O) ^ s • (yz : W.DD T × W.DD T).1 + (W.φD T mE - mE) = ∑ c ∈ ev, Y c)
    (hY2 : InPN W T M (((PD.p : ℕ) : O) ^ s • (yz : W.DD T × W.DD T).2 + (W.γ T mE - mE)))
    (hYg : ∀ c ∈ ev, InPN W T M (W.γ T (Y c) - Y c))
    (hYΔ : ∀ c ∈ ev, ∀ δ ∈ W.DelF, W.γD T δ (Y c) = Y c)
    (hx1 : ∀ c ∈ ev, DL W T (c + 1) ((x c : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y c) ∧
      InPN W T M ((x c : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y c))
    (hx2 : ∀ c ∈ ev, InPN W T M (x c : W.DD T × W.DD T).2) :
    ∑ c ∈ ev, W.clK T (x c) = ((PD.p : ℕ) : O) ^ (s + σ) • W.clK T yz := by
  have hγ : W.γ T = W.γD T W.gamK := by rw [hgam]; rfl

  have hZex : ∀ c, ∃ z, c ∈ ev → InPN W T M z ∧ W.φD T z - z = W.γ T (Y c) - Y c := by
    intro c
    by_cases hc : c ∈ ev
    · obtain ⟨z, hz⟩ := (hF2 _ (hYg c hc)).exists
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => (hc h).elim⟩
  choose Z hZ using hZex
  have hCmem : ∀ c (hc : c ∈ ev), ((Y c, Z c) : W.DD T × W.DD T) ∈ W.wachCocyclesDelta T := by
    intro c hc
    refine (RL.mem_Z1DΔ_iff W T _).2 ⟨?_, fun δ hδ => ⟨hYΔ c hc δ hδ, ?_⟩⟩
    · simp only
      rw [← hγ, (hZ c hc).2]
    · exact uniformizerLattice_delta_fixed W T hπ (hZ c hc).1 δ hδ
  obtain ⟨C, hC⟩ : ∃ C : ZMod n → ↥(W.wachCocyclesDelta T), ∀ c (hc : c ∈ ev),
      (C c : W.DD T × W.DD T) = (Y c, Z c) :=
    ⟨fun c => if hc : c ∈ ev then ⟨(Y c, Z c), hCmem c hc⟩ else 0, fun c hc => by simp [hc]⟩

  have hxc : ∀ c ∈ ev, W.clK T (x c) = ((PD.p : ℕ) : O) ^ σ • W.clK T (C c) := by
    intro c hc
    have h0 := hF3 (c + 1) (x c - ((PD.p : ℕ) : O) ^ σ • C c)
      (by simpa [hC c hc] using (hx1 c hc).1)
      (by simpa [hC c hc] using
        (uniformizerLattice_sub W T (hx2 c hc) (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T (((PD.p : ℕ) : O) ^ σ) (hZ c hc).1)))
      (by simpa [hC c hc] using (hx1 c hc).2)
    have e := (W.clK T).map_sub (x c) (((PD.p : ℕ) : O) ^ σ • C c)
    have e' := (W.clK T).map_smul (((PD.p : ℕ) : O) ^ σ) (C c)
    have h1 := e.symm.trans h0
    rw [sub_eq_zero] at h1
    exact h1.trans e'

  let cb : ↥(W.wachCocyclesDelta T) := ⟨_, coboundary_mem_invariant_cocycles W T hmE⟩
  have hsum : ∑ c ∈ ev, C c = ((PD.p : ℕ) : O) ^ s • yz + cb := by
    have hyz := ((RL.mem_Z1DΔ_iff W T _).1 yz.2).1
    apply Subtype.ext
    rw [Submodule.coe_sum]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum, Finset.sum_congr rfl (fun c hc => congrArg Prod.fst (hC c hc))]
      simp only [Submodule.coe_add, Submodule.coe_smul, Prod.fst_add, Prod.smul_fst, cb]
      exact hY1.symm
    · rw [Prod.snd_sum, Finset.sum_congr rfl (fun c hc => congrArg Prod.snd (hC c hc))]
      simp only [Submodule.coe_add, Submodule.coe_smul, Prod.snd_add, Prod.smul_snd, cb]
      rw [← hγ]
      have hw : InPN W T M (W.γ T (∑ c ∈ ev, Y c) - ∑ c ∈ ev, Y c) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_induction _ _ (fun a b ha hb => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T ha hb)
          (uniformizerLattice_zero W T M) (fun c hc => hYg c hc)
      refine (hF2 _ hw).unique ⟨?_, ?_⟩ ⟨hY2, ?_⟩
      · exact Finset.sum_induction _ _ (fun a b ha hb => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T ha hb)
          (uniformizerLattice_zero W T M) (fun c hc => (hZ c hc).1)
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, ← Finset.sum_sub_distrib, map_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c hc => (hZ c hc).2
      · rw [← hY1]
        have hyz' : W.γ T (yz : W.DD T × W.DD T).1 - (yz : W.DD T × W.DD T).1 =
            W.φD T (yz : W.DD T × W.DD T).2 - (yz : W.DD T × W.DD T).2 := by rw [hγ]; exact hyz
        simp only [map_add (f := _), map_sub, map_smul, gamma_frobenius_comm]
        have e : ((PD.p : ℕ) : O) ^ s • W.γ T (yz : W.DD T × W.DD T).1 =
            ((PD.p : ℕ) : O) ^ s • (yz : W.DD T × W.DD T).1 +
              ((PD.p : ℕ) : O) ^ s • (W.φD T (yz : W.DD T × W.DD T).2 - (yz : W.DD T × W.DD T).2) := by
          rw [← hyz', smul_sub]; abel
        rw [e, smul_sub]
        abel
  have hcb : W.clK T cb = 0 := hcob cb ⟨mE, hmE, rfl⟩
  have e1 : W.clK T (∑ c ∈ ev, C c) = ∑ c ∈ ev, W.clK T (C c) := map_sum (W.clK T) _ _
  have e3 := congrArg (W.clK T) hsum
  have e2 : W.clK T (((PD.p : ℕ) : O) ^ s • yz + cb) = ((PD.p : ℕ) : O) ^ s • W.clK T yz := by
    have h1 := (W.clK T).map_add (((PD.p : ℕ) : O) ^ s • yz) cb
    have h2 := (W.clK T).map_smul (((PD.p : ℕ) : O) ^ s) yz
    rw [hcb, add_zero] at h1
    exact h1.trans h2
  calc ∑ c ∈ ev, W.clK T (x c) = ∑ c ∈ ev, ((PD.p : ℕ) : O) ^ σ • W.clK T (C c) :=
        Finset.sum_congr rfl hxc
    _ = ((PD.p : ℕ) : O) ^ σ • ∑ c ∈ ev, W.clK T (C c) := (Finset.smul_sum ..).symm
    _ = ((PD.p : ℕ) : O) ^ σ • W.clK T (∑ c ∈ ev, C c) := by rw [e1]
    _ = ((PD.p : ℕ) : O) ^ σ • W.clK T (((PD.p : ℕ) : O) ^ s • yz + cb) :=
        congrArg (fun u => ((PD.p : ℕ) : O) ^ σ • u) e3
    _ = ((PD.p : ℕ) : O) ^ σ • (((PD.p : ℕ) : O) ^ s • W.clK T yz) :=
        congrArg (fun u => ((PD.p : ℕ) : O) ^ σ • u) e2
    _ = ((PD.p : ℕ) : O) ^ (s + σ) • W.clK T yz := by rw [smul_smul, ← pow_add, add_comm σ s]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2C

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExistsLinearLiftOfFree
section
noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2T

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem basis_induction {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] (b : Module.Basis ι R M)
    (P : M → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (a : R) x, P x → P (a • x)) (hb : ∀ k, P (b k)) : ∀ x, P x := by
  intro x
  have hx : x ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hb k
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul a y _ hy => exact hsmul a y hy

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem exists_linear_lift_of_free [NeZero n] [IsDomain O] [IsPrincipalIdealRing O] (hZ : TTool2Z W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hp : 11 ≤ PD.p) {M η σ : ℕ} (hTC : TCase PD.p 1 M η σ)
    (hc : IsCrys PD T.ρ) (c : ZMod n) {FF : Type} [AddCommGroup FF] [Module O FF]
    [Module.Free O FF] [Module.Finite O FF] (F₁ : Submodule O FF) (ζL : FF →ₗ[O] W.DD T)
    (hζ : ∀ f, DL W T c (ζL f) ∧ InPN W T 1 (ζL f)) :
    ∃ tL : ↥F₁ →ₗ[O] W.DD T, ∀ f : ↥F₁, tL f ∈ pullJ W T c 1 ∧ DL W T (c + 1) (tL f) ∧
      (∃ p ∈ pullJ W T c 1, ((PD.p : ℕ) : O) ^ σ • W.φD T (ζL f) - (W.γ T (tL f) - tL f) =
        fMX W M η • p) ∧
      ∃ t', IsTrZ W T c 1 M η σ (ζL f) t' ∧ ∃ p ∈ pullJ W T c 1, tL f - t' = fMX W M η • p := by
  obtain ⟨Zex, Zpr, Zlin, -⟩ := hZ hA hp 1 M η σ hTC T hc c
  simp only [pow_one, Nat.cast_one] at Zpr
  let bF := Module.Free.chooseBasis O FF
  obtain ⟨r, b1⟩ := Submodule.basisOfPid bF F₁
  let tch : FF → W.DD T := fun f => Classical.epsilon (fun t => IsTrZ W T c 1 M η σ (ζL f) t)
  have htch : ∀ f, IsTrZ W T c 1 M η σ (ζL f) (tch f) := fun f =>
    Classical.epsilon_spec (Zex _ (hζ f).1 (hζ f).2)
  let tL : ↥F₁ →ₗ[O] W.DD T := b1.constr O (fun k => tch (b1 k : FF))
  refine ⟨tL, ?_⟩

  have hz0 : ∀ t, IsTrZ W T c 1 M η σ 0 t → ∃ p ∈ pullJ W T c 1, t = fMX W M η • p := by
    intro t ht
    have hd0 := invariantLetter_zero W T c
    have hp0 := uniformizerLattice_zero W T (k := 1)
    obtain ⟨p, hp, e⟩ := Zlin 0 0 0 0 t t t hd0 hp0 hd0 hp0 ht ht (by simpa using ht)
    exact ⟨p, hp, by simpa using e⟩
  refine basis_induction b1 _ ?_ ?_ ?_ ?_
  · obtain ⟨t0, ht0⟩ := Zex 0 (invariantLetter_zero W T c) (uniformizerLattice_zero W T 1)
    obtain ⟨p0, hp0, e0⟩ := hz0 t0 (by simpa using ht0)
    refine ⟨by simp, by simpa using invariantLetter_zero W T (c + 1), ⟨0, Submodule.zero_mem _, by simp⟩,
      t0, by simpa using ht0, -p0, Submodule.neg_mem _ hp0, ?_⟩
    simp [e0]
  · rintro x y ⟨hx1, hx2, ⟨px, hpx, ex⟩, tx, htx, qx, hqx, fx⟩ ⟨hy1, hy2, ⟨py, hpy, ey⟩, ty, hty, qy, hqy, fy⟩
    have hsum : ζL (x : FF) + ζL (y : FF) = ζL ((x + y : ↥F₁) : FF) := by
      rw [Submodule.coe_add, map_add (f := _)]
    obtain ⟨txy, htxy⟩ := Zex (ζL ((x + y : ↥F₁) : FF)) (hζ _).1 (hζ _).2
    obtain ⟨r1, hr1, e1⟩ := Zlin 1 1 _ _ tx ty txy (hζ x).1 (hζ x).2 (hζ y).1 (hζ y).2 htx hty
      (by rw [one_smul, one_smul, hsum]; exact htxy)
    refine ⟨by rw [map_add (f := _)]; exact Submodule.add_mem _ hx1 hy1,
      by rw [map_add (f := _)]; exact Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T hx2 hy2,
      ⟨px + py, Submodule.add_mem _ hpx hpy, ?_⟩, txy, htxy, qx + qy - r1,
      Submodule.sub_mem _ (Submodule.add_mem _ hqx hqy) hr1, ?_⟩
    · rw [smul_add, ← ex, ← ey, Submodule.coe_add, map_add ζL, map_add (W.φD T), smul_add,
        map_add tL, map_add (W.γ T)]
      abel
    · rw [smul_sub, smul_add, ← fx, ← fy, ← e1, map_add tL, one_smul, one_smul]
      abel
  · rintro a x ⟨hx1, hx2, ⟨px, hpx, ex⟩, tx, htx, qx, hqx, fx⟩
    have hsm : a • ζL (x : FF) = ζL ((a • x : ↥F₁) : FF) := by
      rw [Submodule.coe_smul, map_smul]
    obtain ⟨tax, htax⟩ := Zex (ζL ((a • x : ↥F₁) : FF)) (hζ _).1 (hζ _).2
    obtain ⟨r1, hr1, e1⟩ := Zlin a 0 _ _ tx tx tax (hζ x).1 (hζ x).2 (hζ x).1 (hζ x).2 htx htx
      (by rw [zero_smul, add_zero, hsm]; exact htax)
    refine ⟨by rw [map_smul]; exact Submodule.smul_of_tower_mem _ a hx1,
      by rw [map_smul]; exact Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T a hx2,
      ⟨a • px, Submodule.smul_of_tower_mem _ a hpx, ?_⟩, tax, htax, a • qx - r1,
      Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ a hqx) hr1, ?_⟩
    · rw [smul_comm (fMX W M η) a px, ← ex]
      simp only [map_smul, Submodule.coe_smul, smul_sub]
      rw [smul_comm]
    · rw [smul_sub, smul_comm (fMX W M η) a qx, ← fx, ← e1]
      simp only [map_smul, zero_smul, add_zero, smul_sub]
      abel
  · intro k
    have hk : tL (b1 k) = tch (b1 k : FF) := by simp [tL]
    obtain ⟨h1, h2, h3⟩ := Zpr _ _ (hζ _).1 (hζ _).2 (htch (b1 k : FF))
    refine ⟨by rw [hk]; exact h2, by rw [hk]; exact h1, by rw [hk]; exact h3, tch (b1 k : FF),
      htch _, 0, Submodule.zero_mem _, by rw [hk, sub_self, smul_zero]⟩

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2T

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.GammaSubCocycleComponent
section
noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2I

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Core

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (s₁ σ : ℕ) (yv zv : W.DD T)
  (ms t : ZMod n → W.DD T)

def gammaDefectOfLetterLift (c : ZMod n) : W.DD T :=
  ((PD.p : ℕ) : O) ^ s₁ • ((letE c : LetA O n) • zv) + (W.γ T (ms c) - ms c)

def liftCorrection (c : ZMod n) : W.DD T :=
  ((PD.p : ℕ) : O) ^ σ • W.φD T (ms c) +
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 1) : LetA O n) • yv) - t c

def gammaDefectOfLiftCorrection (c : ZMod n) : W.DD T :=
  ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 1) : LetA O n) • zv) +
    (W.γ T (liftCorrection W T s₁ σ yv ms t c) - liftCorrection W T s₁ σ yv ms t c)

def frobeniusShiftDefectOfLiftCorrection (c : ZMod n) : W.DD T :=
  W.φD T (liftCorrection W T s₁ σ yv ms t (c - 2)) +
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE c : LetA O n) • yv) - ((PD.p : ℕ) : O) ^ σ • ms c

def frobeniusSquareDefectOfLiftCorrection (c : ZMod n) : W.DD T :=
  ((PD.p : ℕ) : O) ^ (s₁ + σ) •
      ((letE (c + 1) : LetA O n) • yv + W.φD T ((letE c : LetA O n) • yv)) +
    W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t (c - 2))) - liftCorrection W T s₁ σ yv ms t c

def liftCorrectionSum [NeZero n] (d : ℕ) : W.DD T :=
  ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, (liftCorrection W T s₁ σ yv ms t c +
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 2) : LetA O n) • yv) +
      W.φD T (liftCorrection W T s₁ σ yv ms t c))

variable {W T s₁ σ yv zv}

theorem cocycle_relation_on_letter (hcoc : W.γ T yv - yv = W.φD T zv - zv) (i : ZMod n) :
    (letE (i + 1) : LetA O n) • W.γ T yv = (letE (i + 1) : LetA O n) • yv +
      W.φD T ((letE i : LetA O n) • zv) - (letE (i + 1) : LetA O n) • zv := by
  have h := congrArg (fun x => (letE (i + 1) : LetA O n) • x) hcoc
  simp only [smul_sub] at h
  rw [sub_eq_iff_eq_add] at h
  rw [frobenius_letter_shift, h]
  abel

theorem cocycleXi_eq (hcoc : W.γ T yv - yv = W.φD T zv - zv) (c : ZMod n) :
    gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c = ((PD.p : ℕ) : O) ^ σ • W.φD T (gammaDefectOfLetterLift W T s₁ zv ms c) -
      (W.γ T (t c) - t c) := by
  have hc := cocycle_relation_on_letter (W := W) (T := T) hcoc c
  unfold gammaDefectOfLiftCorrection liftCorrection gammaDefectOfLetterLift
  simp only [map_add (f := _), map_sub, map_smul, gamma_letter_smul, gamma_frobenius_comm, hc]
  simp only [smul_add, smul_sub, smul_smul, ← pow_add, add_comm σ s₁]
  abel

theorem gamma_sub_cocycleW (hcoc : W.γ T yv - yv = W.φD T zv - zv) (c : ZMod n) :
    W.γ T (frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c) - frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c =
      W.φD T (gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t (c - 2)) -
        ((PD.p : ℕ) : O) ^ σ • gammaDefectOfLetterLift W T s₁ zv ms c := by
  have hc := cocycle_relation_on_letter (W := W) (T := T) hcoc (c - 1)
  rw [sub_add_cancel] at hc
  have hl : W.φD T ((letE (c - 2 + 1) : LetA O n) • zv) = (letE c : LetA O n) • W.φD T zv := by
    rw [frobenius_letter_shift, show c - 2 + 1 + 1 = c by ring]
  have hl' : W.φD T ((letE (c - 1) : LetA O n) • zv) = (letE c : LetA O n) • W.φD T zv := by
    rw [frobenius_letter_shift, sub_add_cancel]
  unfold frobeniusShiftDefectOfLiftCorrection gammaDefectOfLiftCorrection gammaDefectOfLetterLift
  simp only [map_add (f := _), map_sub, map_smul, gamma_letter_smul, gamma_frobenius_comm, hc, hl, hl']
  simp only [smul_add, smul_sub, smul_smul, ← pow_add, add_comm σ s₁]
  abel

theorem cocycleY_eq_frobenius_add (c : ZMod n) :
    frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c = W.φD T (frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c) + t c := by
  unfold frobeniusSquareDefectOfLiftCorrection frobeniusShiftDefectOfLiftCorrection liftCorrection
  simp only [map_add (f := _), map_sub, map_smul, smul_add]
  abel

theorem gamma_sub_cocycle_component (hcoc : W.γ T yv - yv = W.φD T zv - zv) (c : ZMod n) :
    W.γ T (frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c) - frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c =
      W.φD T (W.φD T (gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t (c - 2))) - gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c := by
  rw [cocycleY_eq_frobenius_add, cocycleXi_eq ms t hcoc c]
  have h := congrArg (W.φD T) (gamma_sub_cocycleW (s₁ := s₁) (σ := σ) (ms := ms) (t := t) hcoc c)
  simp only [map_add (f := _), map_sub, map_smul, gamma_frobenius_comm] at h ⊢
  rw [show ∀ a b e : W.DD T, a - (b - e) = (a - b) + e from fun a b e => by abel, ← h]
  abel

theorem first_component_sum_eq [NeZero n] (hn : Even n) (d : ℕ) :
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • yv +
        (W.φD T (liftCorrectionSum W T s₁ σ yv ms t d) - liftCorrectionSum W T s₁ σ yv ms t d) =
      ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c := by
  have hy : yv = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      ((letE (c + 1) : LetA O n) • yv + (letE (c + 2) : LetA O n) • yv) := by
    conv_lhs => rw [← sum_letter_idempotents_smul W T yv]
    exact sum_eq_sum_evens_pairs hn d (fun i => (letE i : LetA O n) • yv)
  have key : ((PD.p : ℕ) : O) ^ (s₁ + σ) • yv = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      (((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 1) : LetA O n) • yv) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 2) : LetA O n) • yv)) := by
    conv_lhs => rw [hy]
    rw [Finset.smul_sum]
    simp only [smul_add]
  have h2 : ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t (c - 2))) =
      ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t c)) :=
    sum_evens_shift_sub_two hn d (fun c => W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t c)))
  have h3 : ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      ((PD.p : ℕ) : O) ^ (s₁ + σ) • W.φD T ((letE c : LetA O n) • yv) =
      ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • W.φD T ((letE (c + 2) : LetA O n) • yv) :=
    (sum_evens_shift_add_two hn d (fun c => ((PD.p : ℕ) : O) ^ (s₁ + σ) • W.φD T ((letE c : LetA O n) • yv))).symm
  have eY : ∀ c, frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c =
      ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 1) : LetA O n) • yv) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • W.φD T ((letE c : LetA O n) • yv) +
        W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t (c - 2))) - liftCorrection W T s₁ σ yv ms t c := by
    intro c; unfold frobeniusSquareDefectOfLiftCorrection; rw [smul_add]
  rw [Finset.sum_congr rfl (fun c _ => eY c)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h2, h3, key]
  unfold liftCorrectionSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_add (f := _), map_smul, Finset.sum_add_distrib]
  abel

theorem second_component_sum_eq [NeZero n] (hn : Even n) (d : ℕ) (hcoc : W.γ T yv - yv = W.φD T zv - zv) :
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • zv +
        (W.γ T (liftCorrectionSum W T s₁ σ yv ms t d) - liftCorrectionSum W T s₁ σ yv ms t d) =
      ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
        (gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c + W.φD T (gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c)) := by
  have hz : zv = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      ((letE (c + 1) : LetA O n) • zv + (letE (c + 2) : LetA O n) • zv) := by
    conv_lhs => rw [← sum_letter_idempotents_smul W T zv]
    exact sum_eq_sum_evens_pairs hn d (fun i => (letE i : LetA O n) • zv)
  have hc : ∀ c : ZMod n, (letE (c + 2) : LetA O n) • W.γ T yv = (letE (c + 2) : LetA O n) • yv +
      W.φD T ((letE (c + 1) : LetA O n) • zv) - (letE (c + 2) : LetA O n) • zv := by
    intro c
    have := cocycle_relation_on_letter (W := W) (T := T) hcoc (c + 1)
    rwa [show c + 1 + 1 = c + 2 by ring] at this
  unfold gammaDefectOfLiftCorrection liftCorrectionSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [hz]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [map_add (f := _), map_sub, map_smul, gamma_letter_smul, gamma_frobenius_comm, hc, smul_add, smul_sub]
  abel

end Core

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2I

end
end

