module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentNeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.RevTab

open Classical Formalism.L2.SG.HidaSetting

theorem pairTable_of {M A : Type} [Ring A] (p : M → M → A) (Z sm : A → Prop) (hZ : ∀ c, Z c → sm c)
    (hadd : ∀ a b, sm a → sm b → sm (a + b)) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M) (z : M) (u : A)
    (hu : sm (u - 1))
    (t1 : ∀ a c, Z (p (f a) (e c) - if a = c then 1 else 0)) (t2 : ∀ a j, Z (p (f a) (b j))) (t3 : ∀ a, Z (p (f a) z))
    (t4 : ∀ a c, Z (p (f a) (f c)))
    (t5 : ∀ i a, Z (p (b' i) (e a))) (t6 : ∀ i j, Z (p (b' i) (b j) - if i = j then u else 0)) (t7 : ∀ i, Z (p (b' i) z))
    (t8 : ∀ i a, Z (p (b' i) (f a)))
    (t9 : ∀ a, Z (p z (e a))) (t10 : ∀ j, Z (p z (b j))) (t11 : Z (p z z + 1)) (t12 : ∀ a, Z (p z (f a)))
    (t13 : ∀ a c, Z (p (e a) (e c))) (t14 : ∀ a j, Z (p (e a) (b j))) (t15 : ∀ a, Z (p (e a) z))
    (t16 : ∀ a c, Z (p (e a) (f c) - if a = c then 1 else 0)) :
    PairTable p sm e f b b' z := by
  refine ⟨fun a c => hZ _ (t1 a c), fun a j => hZ _ (t2 a j), fun a => hZ _ (t3 a), fun a c => hZ _ (t4 a c),
    fun i a => hZ _ (t5 i a), fun i j => ?_, fun i => hZ _ (t7 i), fun i a => hZ _ (t8 i a),
    fun a => hZ _ (t9 a), fun j => hZ _ (t10 j), hZ _ t11, fun a => hZ _ (t12 a),
    fun a c => hZ _ (t13 a c), fun a j => hZ _ (t14 a j), fun a => hZ _ (t15 a), fun a c => hZ _ (t16 a c)⟩
  have h := hZ _ (t6 i j)
  by_cases hij : i = j
  · simp only [hij, if_true] at h ⊢
    have := hadd _ _ h hu
    rwa [show p (b' j) (b j) - u + (u - 1) = p (b' j) (b j) - 1 by abel] at this
  · simpa only [hij, if_false] using h

variable {D : D7}

theorem smallAt_add {PP : Pl D.host.E} {a b : EAf D} (ha : SmallAt PP a) (hb : SmallAt PP b) : SmallAt PP (a + b) := by
  unfold SmallAt at *
  rw [RingHom.map_add (f := _)]
  exact Valuation.map_add_lt _ ha hb

theorem smallAt_of_mul {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((g : EAf D) * t) := by
  unfold SmallAt
  have hv : Valued.v (g : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (g : 𝓞 D.host.E)).2 hg
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  rw [RingHom.map_mul, map_natCast, Valuation.map_mul]
  have h1 := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  calc Valued.v (g : PP.adicCompletion D.host.E) * Valued.v (GlobalTheory.StdFrames.cpt PP t)
      ≤ Valued.v (g : PP.adicCompletion D.host.E) * 1 := mul_le_mul_of_nonneg_left h1 zero_le'
    _ = Valued.v (g : PP.adicCompletion D.host.E) := mul_one _
    _ < 1 := hv

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead.RevTab

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf
open scoped TensorProduct

section Cong

variable {I : Formalism.MainNotions.S.AutInst} {g : ℕ}

theorem zmod_swap {x y : VA I} {d : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F} (h : ZMod' I g (hA I x y - d)) :
    ZMod' I g (hA I y x - sigA I d) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [map_sub, ← unitaryCongruence.hA_symm] at this

theorem zmod_swap0 {x y : VA I} (h : ZMod' I g (hA I x y)) : ZMod' I g (hA I y x) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [← unitaryCongruence.hA_symm] at this

theorem zmod_swap_delta {ρ : ℕ} {x y : VA I} {a c : Fin ρ} (h : ZMod' I g (hA I x y - if c = a then 1 else 0)) :
    ZMod' I g (hA I y x - if a = c then 1 else 0) := by
  have := zmod_swap h
  by_cases hac : a = c
  · subst hac
    simpa using this
  · simpa [hac, Ne.symm hac] using this

theorem zmod_diag {k : ℕ} {bw bwd : Fin k → VA I} {ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F}
    (hD : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)) (i j : Fin k) :
    ZMod' I g (hA I (bw (Fin.rev i)) (bwd (Fin.rev j)) - if i = j then sigA I ew else 0) := by
  have := zmod_swap (hD (Fin.rev j) (Fin.rev i))
  by_cases hij : i = j
  · subst hij
    simpa using this
  · have h2 : ¬ Fin.rev j = Fin.rev i := fun h => hij (Fin.rev_injective h).symm
    simpa [hij, h2] using this

end Cong

variable {D : D7}

theorem smallAt_sg_sub_one {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {ew : EAf D}
    (hc0 : ∃ t ∈ GlobalTheory.StdFrames.OA D, 1 - ew - GlobalTheory.StdFrames.sg D ew = (g : EAf D) * t) (hid : ew * ew = ew)
    (hne : GlobalTheory.StdFrames.cpt PP ew ≠ 1) : SmallAt PP (GlobalTheory.StdFrames.sg D ew - 1) := by
  have h0 : GlobalTheory.StdFrames.cpt PP ew = 0 := by
    have h1 := congrArg (GlobalTheory.StdFrames.cpt PP) hid
    rw [map_mul] at h1
    have h2 : GlobalTheory.StdFrames.cpt PP ew * (GlobalTheory.StdFrames.cpt PP ew - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  obtain ⟨t, ht, hc⟩ := hc0
  have hs := smallAt_of_mul hg ht
  rw [← hc] at hs
  have e1 : GlobalTheory.StdFrames.sg D ew - 1 = -(1 - ew - GlobalTheory.StdFrames.sg D ew) - ew := by ring
  unfold SmallAt at *
  rw [e1, map_sub, map_neg, h0, sub_zero, Valuation.map_neg]
  exact hs

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf RevTab

theorem pairTable_rev : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) ≠ 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (fun i => bwT X h (Fin.rev i)) (z0T X h) := by
  intro D X h PP hg hne
  have hc0 : ZMod' X.B.I X.B.g (1 - X.ew - sigA X.B.I X.ew) := by
    have hz := X.vectorsInLattice.2.1
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 ((1 - X.ew - sigA X.B.I X.ew) • X.z0)) :=
      unitaryCongruence.mL_Qs X.B.I X.B.g hz (X.ew_full _ hz)
    rw [unitaryCongruence.hA_smul_right] at h2
    have hint : (1 - X.ew - sigA X.B.I X.ew) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
      sub_mem (sub_mem (one_mem _) X.ew_int) (unitaryCongruence.sigA_mem _ X.ew_int)
    have h4 := unitaryCongruence.Z_sub X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g hint X.formsAtZero.1) h2
    rwa [show (1 - X.ew - sigA X.B.I X.ew) * (hA X.B.I X.z0 X.z0 + 1) -
      (1 - X.ew - sigA X.B.I X.ew) * hA X.B.I X.z0 X.z0 = 1 - X.ew - sigA X.B.I X.ew by ring] at h4
  have hG := X.gramIntegral
  have hZ := X.formsAtZero
  have hW := X.weightVectorsIntegral
  have hD := X.bw_dual
  have hgq := X.g_eq
  have hid := X.ew_idem
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hc0 hG hZ hW hD hgq hid hne ⊢
  subst h
  subst hgq
  refine pairTable_of (hY D) (ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1)) (SmallAt PP)
    (fun c ⟨t, ht, hc⟩ => hc ▸ smallAt_of_mul hg ht) (fun a b => smallAt_add) _ _ _ _ _ _
    (smallAt_sg_sub_one hg hc0 hid hne)
    (fun a c => zmod_swap_delta (hG c a).2.2) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.2) (fun a => (hZ.2 a).2)
    (fun a c => (hG a c).2.1)
    (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).1) (fun i j => zmod_diag hD i j)
    (fun i => zmod_swap0 (hW (Fin.rev i)).1) (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).2.1)
    (fun a => zmod_swap0 (hZ.2 a).1) (fun j => (hW (Fin.rev j)).2.1) hZ.1 (fun a => zmod_swap0 (hZ.2 a).2)
    (fun a c => (hG a c).1) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.1) (fun a => (hZ.2 a).1)
    (fun a c => (hG a c).2.2)

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem smallAt_natCast_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((N : EAf D) * t) := by
  unfold SmallAt
  rw [map_mul, map_natCast, Valuation.map_mul]
  have hv : Valued.v (N : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (N : 𝓞 D.host.E)).2 hN
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  have ht' := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ht') hv

theorem sg_hY {D : D7} (x y : Fin (Yc D 0).rank → EAf D) : GlobalTheory.StdFrames.sg D (hY D x y) = hY D y x := by
  have := GlobalTheory.AdIsom.cjA_hA (Yc D 0) y x
  rw [GlobalTheory.AdIsom.hA_eq, GlobalTheory.AdIsom.hA_eq] at this
  exact this

theorem smallAt_of_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {c : EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c = (N : EAf D) * t) : SmallAt PP c := by
  obtain ⟨t, ht, rfl⟩ := h
  exact smallAt_natCast_mul hN ht

theorem smallAt_hY_of_swap {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} {d : EAf D} (hd : GlobalTheory.StdFrames.sg D d = d)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - d = (N : EAf D) * t) : SmallAt PP (hY D x y - d) := by
  obtain ⟨t, ht, e⟩ := h
  have e' := congrArg (GlobalTheory.StdFrames.sg D) e
  rw [map_sub, sg_hY, hd, map_mul, map_natCast] at e'
  rw [e']
  exact smallAt_natCast_mul hN (GlobalTheory.AdIsom.cjA_mem ht)

theorem smallAt_hY_of_swap0 {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x = (N : EAf D) * t) :
    SmallAt PP (hY D x y) := by
  have := smallAt_hY_of_swap hN (x := x) (y := y) (d := 0) (map_zero _) (by simpa using h)
  simpa using this

theorem smallAt_hY_of_swap_delta {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {a c : ι} {x y : Fin (Yc D 0).rank → EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - (if c = a then 1 else 0) = (N : EAf D) * t) :
    SmallAt PP (hY D x y - if a = c then 1 else 0) := by
  refine smallAt_hY_of_swap hN (by split_ifs <;> simp) ?_
  simpa only [eq_comm (a := a)] using h

theorem smallAt_sub_of_cpt {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {i j : ι} {c e : EAf D} (he : GlobalTheory.StdFrames.cpt PP e = 1)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c - (if i = j then e else 0) = (N : EAf D) * t) :
    SmallAt PP (c - if i = j then 1 else 0) := by
  obtain ⟨t, ht, e'⟩ := h
  have h1 : GlobalTheory.StdFrames.cpt PP (c - if i = j then 1 else 0) = GlobalTheory.StdFrames.cpt PP ((N : EAf D) * t) := by
    rw [← e']
    split_ifs <;> simp [he]
  have h2 := smallAt_natCast_mul hN ht
  unfold SmallAt at h2 ⊢
  rwa [h1]

theorem pairTable_of_cpt_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (bwT X h) (bwdT X h) (z0T X h) := by
  intro D X h PP hg hew
  have F0g := X.gramIntegral
  have F0z := X.formsAtZero
  have F0W := X.weightVectorsIntegral
  have bd := X.bw_dual
  have ge := X.g_eq
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h F0g F0z F0W bd ge hew ⊢
  subst h
  subst ge
  refine ⟨fun a c => smallAt_hY_of_swap_delta hg (F0g c a).2.2, fun a j => smallAt_of_mul hg ((F0W j).2.2 a).2.1,
    fun a => smallAt_of_mul hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).2.1,
    fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.1, fun i j => smallAt_sub_of_cpt hg hew (bd i j),
    fun i => smallAt_hY_of_swap0 hg (F0W i).2.1, fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.2,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).1, fun j => smallAt_of_mul hg (F0W j).1, smallAt_of_mul hg F0z.1,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).1,
    fun a j => smallAt_of_mul hg ((F0W j).2.2 a).1, fun a => smallAt_of_mul hg (F0z.2 a).1,
    fun a c => smallAt_of_mul hg (F0g a c).2.2⟩

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeConjRead
open Classical

theorem cast_fun_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) {m : ℕ} (f : Fin m → Formalism.L2.SG.HidaSetting.VA I)
    (hf : ∀ a, f a ∈ I.Lf) (a : Fin m) :
    (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin m → Formalism.L2.SG.HidaSetting.VA I) h) f) a ∈ J.Lf := by
  subst h
  exact hf a

theorem cast_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) (v : Formalism.L2.SG.HidaSetting.VA I) (hv : v ∈ I.Lf) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) v ∈ J.Lf := by
  subst h
  exact hv

theorem flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M)
    (z : M) (he : ∀ a, e a ∈ S) (hf : ∀ a, f a ∈ S) (hb : ∀ a, b a ∈ S) (hz : z ∈ S) (i : Fin n) :
    flagV ρ k n e f b z i ∈ S := by
  unfold flagV
  split_ifs
  exacts [he _, hb _, hz, hf _, h0]

theorem colMat_entry {D : D7} {n : ℕ} (M : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (M * colMat w) i j = Matrix.mulVec M (w j) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]

theorem flag_pair_int : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β₀ : GL (Fin (Yc D 0).rank) (EAf D)), Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 = GlobalTheory.NormSum.AdLattice.lat β₀ → ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank), ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D X h β₀ hL PP i j
  have hF : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := hL ▸ GlobalTheory.StdFrames.isFrame_lat β₀
  have hLf := GlobalTheory.KgFrame.Lf_eq D
  have key : ∀ v : Fin (Yc D 0).rank → EAf D, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf →
      Matrix.mulVec (β₀⁻¹).val v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro v hv
    rw [hLf] at hv
    exact (hF v).1 hv i
  set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf} with hS
  have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
    show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
    exact zero_mem _
  obtain ⟨hef, hz, hbw⟩ := X.vectorsInLattice
  have he : ∀ a, e0T X h a ∈ S := cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
  have hf : ∀ a, f0T X h a ∈ S := cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
  have hb : ∀ a, bwT X h a ∈ S := cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
  have hbd : ∀ a, bwdT X h a ∈ S := cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
  have hzz : z0T X h ∈ S := cast_mem_Lf h X.z0 hz
  refine ⟨?_, ?_⟩
  · rw [colMat_entry]
    apply key
    unfold flagAt
    split_ifs
    · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf hb hzz j
    · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf (fun a => hbd _) hzz j
  · rw [colMat_entry]
    apply key
    unfold pairAt
    split_ifs
    · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz j
    · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun a => hb _) hzz j

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLiftEqSmul
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
noncomputable section

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLiftScalar

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.MoveValues GlobalTheory.HeckeValues


set_option maxHeartbeats 1000000 in
theorem hkPtC_values_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧
    (∀ τ j, @IsLieImageH E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) p y.x z.x ψ (y.u τ j) (z.u τ j)) ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  intro E _ _ _ H Dw l Xo c σ p y z C hk
  letI := fieldCAt σ
  haveI := algClosedCAt σ
  obtain ⟨ψ, ψp, hiso, hL, htr⟩ := hk
  obtain ⟨β, s₁, n, cr, hβ, hs, hr, hv⟩ := isThetaTrace_iff.1 htr
  obtain ⟨β₀, hβ₀, hc₀⟩ := hs.exists_isRigIso
  have hK := transKer_of_isHkIsog hiso
  have hΨ : ∀ a, rpt a ≫ conj y.x z.x ψ = rpt (ψp a) := fun a => (sends_conj_iff ψ _ _).2 (hiso.2.2.1 a)
  refine ⟨ψ, ψp, n, cr, fun i j a => bv Xo.univ.t.PP β β₀ i j a, hiso, hL, hK ▸ hr, fun i j a _ _ => bv_ne i j a,
    fun i j i' j' a hi hj => ?_, fun i j hi hj => ?_, fun g e he i j => ?_, fun a i jm hi hj => ?_⟩
  · have mi := (mem_iff _ _).2 hi
    have mj := (mem_iff _ _).2 hj
    exact bv_trans hβ.2.1 hβ₀.2.1 a (ψp a) (hΨ a) mi.1 mi.2 mj.1 mj.2
  · have h1 : rpt (1 : Over.mk y.x ⟶ Xo.univ.t.G) ≫ conj y.x z.x ψ = rpt (1 : Over.mk z.x ⟶ Xo.univ.t.G) := by
      exact (hΨ 1).trans (congrArg (fun q => rpt q) (map_one ψp))
    exact bv_rig hβ hβ₀ h1 i j ((mem_iff _ _).2 hi) ((mem_iff _ _).2 hj)
  · have hfun : (fun w => rpt (e w)) = fun w => fibPt Xo.univ.t.G (e w) ≫ (swap y.x).inv :=
      funext fun w => (Iso.eq_comp_inv _).2 (fibPt_swap (e w))
    have hh : IsHolTo Set.univ (fun w => rpt (e w)) := by
      rw [hfun]
      exact (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G y.x g e he).2 _ (swap y.x).inv
    exact bv_hol hβ.2.1 hβ₀.2.1 ψp hΨ e hh i j
  · exact bv_values hβ.2.1 hβ₀.2.1 hc₀ cr (fun m => hr.1 m) hv a (ψp a) (hΨ a) i jm ((mem_iff _ _).2 hi)
      (fun m => (mem_iff _ _).2 (hj m))

end GlobalTheory.HeckeLiftScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateAdd
section
open GlobalTheory.FunObj

namespace GlobalTheory

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ A) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    show Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne (by omega : n ≠ j₀), chainTo_update_of_le k j₀ A n (by omega)]

theorem chainTo_update_succ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    chainTo (Function.update k j₀ A) (j₀ + 1) = A ∘ₗ chainTo k j₀ := by
  show Function.update k j₀ A j₀ ∘ₗ chainTo (Function.update k j₀ A) j₀ = _
  rw [Function.update_self, chainTo_update_of_le k j₀ A j₀ le_rfl]

theorem chainTo_update_add : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n := by
  intro V _ _ k j₀ A B n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [chainTo_update_succ, chainTo_update_succ, chainTo_update_succ, LinearMap.add_comp]
  | succ n hn ih =>
    show Function.update k j₀ (A + B) n ∘ₗ chainTo (Function.update k j₀ (A + B)) n =
      Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n + Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n
    have hne : n ≠ j₀ := by omega
    rw [Function.update_of_ne hne, Function.update_of_ne hne, Function.update_of_ne hne, ih, LinearMap.comp_add]

end GlobalTheory
end

