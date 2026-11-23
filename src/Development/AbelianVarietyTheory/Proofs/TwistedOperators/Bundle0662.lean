module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0613

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.VecsLast

open ValuativeRel

theorem exists_nat_val_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (d : ℕ) :
    ∃ N : ℕ, 0 < N ∧ valuation k (N : k) ≤ valuation k ((ϖ ^ d : kˣ) : k) := by
  refine ⟨GlobalTheory.SplitWeil.resCard k ^ d, pow_pos ?_ d, ?_⟩
  · unfold GlobalTheory.SplitWeil.resCard
    exact Nat.card_pos
  · rw [Nat.cast_pow, map_pow, Units.val_pow_eq_pow_val, map_pow, hϖ]
    exact pow_le_pow_left₀ zero_le' (le_uniformizer_iff.2 GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one) d

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

open ValuativeRel

variable {D : D7}

theorem isSBHalf_prodCoord {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {P : Finset (Pl D.host.E)}
    {A B : P → Type} [∀ w, Fintype (A w)] [∀ w, Fintype (B w)]
    (c : ∀ w : P, Mx D m n →+ Matrix (A w) (B w) (Kw w.1))
    (hc : ∀ z, IsHalf e z → (z ∈ Λ ↔ ∀ w : P, GlobalTheory.StepData.IntM (c w z)))
    (d : P → ℕ) (ψ : ∀ w : P, Matrix (A w) (B w) (Kw w.1) → ℂ)
    (h1 : ∀ w M, ψ w M ≠ 0 → GlobalTheory.StepData.IntM M)
    (h2 : ∀ w M N, (∀ i j, valuation (Kw w.1) (N i j) ≤ valuation (Kw w.1) ((unifAt w.1 ^ d w : (Kw w.1)ˣ) : Kw w.1)) →
      ψ w (M + N) = ψ w M) :
    IsSBHalf e Λ (fun z => if IsHalf e z then ∏ w : P, ψ w (c w z) else 0) := by
  classical
  choose N hN0 hN using fun w : P => exists_nat_val_le (isUnif_unifAt (D := D) w.1) (d w)
  have hk0 : 0 < ∏ w : P, N w := Finset.prod_pos fun w _ => hN0 w
  have hhalf : ∀ (a : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (a • u) := fun a u hu i j => by
    show e * (a • u) i j = (a • u) i j
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]
  have hadd : ∀ {t u : Mx D m n}, IsHalf e u → (IsHalf e (t + u) ↔ IsHalf e t) := fun {t u} hu => by
    constructor
    · intro h i j
      have h1 := h i j
      have h2 := hu i j
      simp only [Matrix.add_apply, mul_add] at h1
      linear_combination h1 - h2
    · intro h i j
      simp only [Matrix.add_apply, mul_add, h i j, hu i j]
  refine ⟨fun t ht => ?_, ∏ w : P, N w, hk0, fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra hc'
    exact ht (if_neg hc')
  · have hku := hhalf (∏ w : P, N w) u hue
    dsimp only
    by_cases ht : IsHalf e t
    · rw [if_pos ((hadd hku).2 ht), if_pos ht]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_add (f := _), map_nsmul]
      refine h2 w _ _ fun i j => ?_
      have hint := (hc u hue).1 hu w i j
      rw [Valuation.mem_integer_iff] at hint
      rw [Matrix.smul_apply, nsmul_eq_mul, map_mul]
      have hle : valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) ≤ valuation (Kw w.1) (N w : Kw w.1) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Nat.cast_mul, map_mul]
        exact mul_le_of_le_one_right' (GlobalTheory.RootEx.UnipPow.valuation_natCast_le_one _)
      calc valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) * valuation (Kw w.1) (c w u i j)
          ≤ valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) := mul_le_of_le_one_right' hint
        _ ≤ _ := hle.trans (hN w)
    · rw [if_neg (fun h => ht ((hadd hku).1 h)), if_neg ht]
  · dsimp only at ht
    have hE : IsHalf e t := by
      by_contra h
      exact ht (if_neg h)
    rw [if_pos hE] at ht
    have hmem : t ∈ Λ := (hc t hE).2 fun w => h1 w _ (Finset.prod_ne_zero_iff.1 ht w (Finset.mem_univ _))
    exact Λ.nsmul_mem hmem _

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

open ValuativeRel

variable {D : D7}

theorem isSBHalf_frames {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1))
    {A B : P → Type} [∀ w, Fintype (A w)] [∀ w, Fintype (B w)]
    (c : ∀ w : P, WO S T →+ Matrix (A w) (B w) (Kw w.1))
    (hc : ∀ (w : P) z, GlobalTheory.StepData.IntM (c w z) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w.1)))
    (d : P → ℕ) (ψ : ∀ w : P, Matrix (A w) (B w) (Kw w.1) → ℂ)
    (h1 : ∀ w M, ψ w M ≠ 0 → GlobalTheory.StepData.IntM M)
    (h2 : ∀ w M N, (∀ i j, valuation (Kw w.1) (N i j) ≤ valuation (Kw w.1) ((unifAt w.1 ^ d w : (Kw w.1)ˣ) : Kw w.1)) →
      ψ w (M + N) = ψ w M) :
    IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun z => if IsHalf e z then ∏ w : P, ψ w (c w z) else 0) := by
  refine isSBHalf_prodCoord c (fun z hz => ?_) d ψ h1 h2
  rw [GlobalTheory.ColLatDict.mem_latO_iff_intM hS hT hβS hβT he hAA z hz]
  exact ⟨fun h w => (hc w z).2 (h w.1 w.2), fun h w hw => (hc ⟨w, hw⟩ z).1 (h ⟨w, hw⟩)⟩

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem coord_add (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (x y : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (x + y) = B.coord t w hX hY x + B.coord t w hX hY y := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

noncomputable def coordHom (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) :
    Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D) →+
      Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w) :=
  AddMonoidHom.mk' (fun z => B.coord t w hX hY (z.map fun a => cpt w (toEAf D a))) fun x y => by
    rw [Matrix.map_add _ (fun a b => by rw [RingHom.map_add (f := _), RingHom.map_add (f := _)])]
    exact coord_add B t w hX hY _ _

theorem coordHom_int_iff (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) (z : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D)) :
    GlobalTheory.StepData.IntM (coordHom B t w hX hY z) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr (B.β X.1 X.2) (B.β Y.1 Y.2) (z.map (toEAf D))).map (cpt (D := D) w)) :=
  GlobalTheory.MixVacBig.coord_int_iff B t w hX hY z

theorem natDatum_props {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} {ϖ : kˣ} {dp : ℕ} {φ : Matrix a b k → ℂ} (h : GlobalTheory.SplitFlip.IsNatDatum ϖ dp φ) :
    (∀ M, φ M ≠ 0 → GlobalTheory.StepData.IntM M) ∧
      ∀ M N, (∀ i j, valuation k (N i j) ≤ valuation k ((ϖ ^ dp : kˣ) : k)) → φ (M + N) = φ M := by
  obtain ⟨hs, hi⟩ := h
  refine ⟨fun M hM i j => ?_, fun M N hN => hi M N ?_⟩
  · by_contra hc
    refine hM (hs M fun hm => hc ?_)
    have := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_diagLat.1 hm i j
    rw [Valuation.mem_integer_iff]
    simpa using this
  · exact GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_stdLat.2 hN

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

theorem vecs_last : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → (∀ j : Fin D.R.m, ∃ f, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f) ∧ ∀ i : Fin D.R.m, ∃ f, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t e he φ hφ
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hAA : ∀ w ∈ locPl ch.G t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  refine ⟨fun j => ?_, fun i => ?_⟩
  · have hS : IsSelfDualC (ch.G.pS (.mu t D.R.m j)) (ch.G.latS (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, j.2.le⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.mu t D.R.m j)) (ch.G.latT (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m ((j : ℕ) + 1)) ⟨le_rfl, j.2⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ)) le_rfl j.2.le
    have hβT := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ) + 1) le_rfl j.2
    have hmem : GlobalTheory.SplitFlip.Edge.theta D.R.m j ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    have hSB := isSBHalf_frames hS hT hβS hβT he hAA
      (fun w => coordHom ch.S.B t w.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩)
      (fun w z => coordHom_int_iff ch.S.B t w.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z) (fun w => depthAt ch.G w.1) (fun w => φ w (.theta D.R.m j))
      (fun w => (natDatum_props (hφ w _ hmem)).1) (fun w => (natDatum_props (hφ w _ hmem)).2)
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT
    obtain ⟨f, hf⟩ := GlobalTheory.FunObj.VecEx.exists_isThetaAt_of_vac inferInstance inferInstance hS hT he (ch.rm.vT_is t D.R.m j le_rfl j.2) hSB
    exact ⟨f, hSB, hf⟩
  · have hS : IsSelfDualC (ch.G.pS (.chi i D.R.m)) (ch.G.latS (.chi i D.R.m)) :=
      isSelfDualC_neg (node_isV ch.G hL (X := .grid ((i : ℕ) + 1) D.R.m) ⟨i.2, le_rfl⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.chi i D.R.m)) (ch.G.latT (.chi i D.R.m)) :=
      (node_isV ch.G hL (X := .grid (i : ℕ) D.R.m) ⟨i.2.le, le_rfl⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := (i : ℕ) + 1) (j := D.R.m) i.2 le_rfl
    have hβT := ch.S.B.isFrame_β hL (i := (i : ℕ)) (j := D.R.m) i.2.le le_rfl
    have hmem : GlobalTheory.SplitFlip.Edge.ex i D.R.m ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    have hSB := isSBHalf_frames hS hT hβS hβT he hAA
      (fun w => coordHom ch.S.B t w.1 (X := ((i : ℕ), D.R.m)) (Y := ((i : ℕ) + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩)
      (fun w z => coordHom_int_iff ch.S.B t w.1 (X := ((i : ℕ), D.R.m)) (Y := ((i : ℕ) + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ z) (fun w => depthAt ch.G w.1) (fun w => φ w (.ex i D.R.m))
      (fun w => (natDatum_props (hφ w _ hmem)).1) (fun w => (natDatum_props (hφ w _ hmem)).2)
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT
    obtain ⟨f, hf⟩ := GlobalTheory.FunObj.VecEx.exists_isThetaAt_of_vac inferInstance inferInstance hS hT he (ch.rm.vX_is i D.R.m i.2 le_rfl) hSB
    exact ⟨f, hSB, hf⟩

end GlobalTheory.VecsLast
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearLeftLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LastPositionLin
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

theorem lastDat_lin (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj))
    (g : GA D (G.V (.grid D.R.m j)))
    (Φ Φ' : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ) (c : ℂ)
    (hΦ : IsThetaFunO W.ψ _ _ Φ) (hΦ' : IsThetaFunO W.ψ _ _ Φ')
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (u v) :
    lastDat W hM j hj vN g (c • Φ + Φ') Φ₂ u v =
      c * lastDat W hM j hj vN g Φ Φ₂ u v + lastDat W hM j hj vN g Φ' Φ₂ u v := by
  set s := (lastAt G W t hM j hj vN).s with hs
  have hw := s.weil
  have h1 := hw.om_pres (g, 1) Φ hΦ
  have h2 := hw.om_pres (g, 1) Φ' hΦ'
  have h3 : IsThetaFunO W.ψ _ _ (c • s.om (g, 1) Φ) := GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c h1
  have e1 : (s.om (g, 1)) (c • Φ + Φ') = c • (s.om (g, 1)) Φ + (s.om (g, 1)) Φ' := by
    have := (s.om (g, 1)).map_add (c • Φ) Φ'
    have h' := (s.om (g, 1)).map_smul c Φ
    exact this.trans (congrArg (· + (s.om (g, 1)) Φ') h')
  have key : GlobalTheory.Unf.flatBF s (s.om (g, 1) (c • Φ + Φ')) =
      c • GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ) + GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ') := by
    rw [e1, (GlobalTheory.FlatLin.flatBF_linear D (GlobalTheory.Unf.Flat.flatLaw D) _ _ _ _ s _ _ c h3 h2).1,
      (GlobalTheory.FlatLin.flatBF_linear D (GlobalTheory.Unf.Flat.flatLaw D) _ _ _ _ s _ _ c h1 h1).2]
  have keyx : ∀ x, GlobalTheory.Unf.flatBF s (s.om (g, 1) (c • Φ + Φ')) x =
      c * GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ) x + GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ') x := fun x => by
    rw [key]; rfl
  unfold lastDat GlobalTheory.FinPl.lastBi GlobalTheory.MixModel.OrthDec.boxT
  rw [← hs]
  beta_reduce
  erw [keyx]
  ring

theorem conAt_last_lin (hM : M.Is t) (P : PolDown G) (h : Pts G) (Φ : SchDown G t) (j : ℕ) (hj : j + 2 = D.R.m)
    (a : Fin D.R.m) (ha : (a : ℕ) = j + 0) (φ φ' : Sch G (.down t D.R.m a)) (c : ℂ)
    (hφ : IsThetaFunO W.ψ _ _ φ) (hφ' : IsThetaFunO W.ψ _ _ φ') (u v) :
    conAt W hM (fockD W t (Function.update Φ a (c • φ + φ')) P) h j u v =
      c * conAt W hM (fockD W t (Function.update Φ a φ) P) h j u v +
        conAt W hM (fockD W t (Function.update Φ a φ') P) h j u v := by
  obtain ⟨k, hk⟩ := a
  simp only [add_zero] at ha
  subst ha
  have h0 : k + 2 * 0 + 2 = D.R.m := by omega
  unfold conAt
  rw [dite_eq_left h0, dite_eq_left h0, dite_eq_left h0]
  have hne : (⟨k + 1, by omega⟩ : Fin D.R.m) ≠ ⟨k, hk⟩ := fun e => by simp at e
  simp only [fockD, Function.update_self, Function.update_of_ne hne]
  have hf : W.fock (.mu t D.R.m k) (c • φ + φ') (P ⟨k, hk⟩) =
      c • W.fock (.mu t D.R.m k) φ (P ⟨k, hk⟩) + W.fock (.mu t D.R.m k) φ' (P ⟨k, hk⟩) :=
    GlobalTheory.FockFiniteHeis.pureTensorO_lin W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ c hφ hφ' _
  have th : ∀ f : Sch G (.down t D.R.m (⟨k, hk⟩ : Fin D.R.m)), IsThetaFunO W.ψ _ _ f →
      IsThetaFunO W.ψ (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1))) (W.fock (.mu t D.R.m k) f (P ⟨k, hk⟩)) :=
    fun f hf => Formalism.IndefR.Fin.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ f _ hf
  erw [hf]
  exact lastDat_lin W hM k h0 _ _ _ _ c (th φ hφ) (th φ' hφ') _ u v

end GlobalTheory.LastPositionLin


open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear in
theorem GlobalTheory.LastPositionLin.lastLin_zero : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _
  intro j _ hj t M hM P h Φ a ha φ φ' c _ hφ hφ' u v
  exact GlobalTheory.LastPositionLin.conAt_last_lin ch.W hM P h Φ j hj a ha φ φ' c hφ hφ' u v
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearRightLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.ConnectionLinear
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastLinR

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem castSch_lin {V : HSp D} {n n' : ℕ} (e : n = n') (c : ℂ) (f g : WO V (G.V (.grid D.R.m n)) → ℂ) :
    castSch G e (c • f + g) = c • castSch G e f + castSch G e g := by
  subst e; rfl

theorem lastDat_lin (Wl : G.Weil) {t : T} {M : Vol G} (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (c : ℂ) (Φ₂ Φ₂' : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (u v) :
    lastDat Wl hM j hj vN g Φ₁ (c • Φ₂ + Φ₂') u v = c * lastDat Wl hM j hj vN g Φ₁ Φ₂ u v + lastDat Wl hM j hj vN g Φ₁ Φ₂' u v := by
  simp only [lastDat, GlobalTheory.FinPl.lastBi, OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.LastLinR

namespace GlobalTheory.ConnectionLinear

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem lastLin_one (ch : Choice R) : LastLin ch 1 := by
  intro j hj hjm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  have h0 : j + 2 * 0 + 2 = D.R.m := by omega
  have hlt : j + 1 < D.R.m := by omega
  obtain rfl : a = ⟨j + 1, hlt⟩ := Fin.ext ha
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hlt⟩ := fun e => by simp [Fin.ext_iff] at e
  unfold conAt
  rw [dite_eq_left h0, dite_eq_left h0, dite_eq_left h0]
  simp only [fockD, Function.update_of_ne hne, Function.update_self]
  have hlin : ch.W.fock (.mu t D.R.m (j + 1)) (c • φ + φ') (P ⟨j + 1, hlt⟩) =
      c • ch.W.fock (.mu t D.R.m (j + 1)) φ (P ⟨j + 1, hlt⟩) + ch.W.fock (.mu t D.R.m (j + 1)) φ' (P ⟨j + 1, hlt⟩) := by
    simp only [GridData.Weil.fock]
    exact GlobalTheory.FockFiniteHeis.pureTensorO_lin _ _ _ _ ch.W.ψ_std ch.W.θ_is _ _ _ _ c hφ hφ' _
  rw [hlin, GlobalTheory.LastLinR.castSch_lin, GlobalTheory.LastLinR.lastDat_lin]

end

theorem big_lastLin_one : Big fun ch => LastLin ch 1 :=
  by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _
  exact lastLin_one ch

end GlobalTheory.ConnectionLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelFlatMapFourierJacobiStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LastStepOne

theorem first_step_flat : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hLoc : LocP ch) (hBes : BesP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (r r₀ h : Pts ch.G)
    (hpts : IsPts ch t w β p.e r r₀ h) (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt ch.G j 0 hj))
    (h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1))
    (h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j)),
    ∃ (F₀ : Frame (Kw w) (besAt ch.G hM j 0 hj vN).V₀.rank (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit))
      (T₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) →ₗ[ℂ]
        (WO (besAt ch.G hM j 0 hj vN).V₀ (ch.G.V (.top (j + 1))) → ℂ)),
      p.IsCoreFrame (besAt ch.G hM j 0 hj vN) (p.xi ^ 0)⁻¹ (frTop ch.S.toGridChoice t w j (by omega)) F₀ ∧
      p.IsModel ch.W.ψ F₀ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) T₁ ∧
      (∀ O, IsOne O → T₁ O = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
        ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r₀) j, 1) (v ⟨j, by omega⟩))) ∧
      ∃ Φ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)),
        Φ.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (datC h₁ h₂
          (phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j))) ∧
        T₁ Φ = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
          ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r) j, 1) (f ⟨j, by omega⟩)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f hvf j hj vN h₁ h₂
  have hm := D.R.two_le_m
  have hjm : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have hev : Even j := by
    obtain ⟨a, ha⟩ := D.R.m_even
    exact ⟨a - 1, by omega⟩
  have hL := hLoc t w hw p hp β r r₀ h hpts j hjm.le
  have hc := hChr t w hw p hp

  have hone : p.IsLoc (frRow ch.S.B t w (j + 1) hjm) 1
      ((epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, j + 1)) := by
    have e1 : (epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, j + 1) = 1 := by
      rw [Pi.mul_apply, epsV_eq_one t w (by omega), elt_eq_one t w β (by omega), one_mul]
    have hmt : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m (j + 1))) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    refine ⟨fun a b => ?_, ?_⟩
    · rw [hmt, sub_self]
      simp
    · rw [e1, hmt, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Matrix.mul_one, (frRow ch.S.B t w (j + 1) hjm).βγ]
  obtain ⟨Tm, hTm, hTmO, Φ, hΦ, hTmΦ⟩ := hArr t w hw p hp φ j hjm (v ⟨j, hjm⟩) (f ⟨j, hjm⟩) (hvf ⟨j, hjm⟩)
    (epsV ch.G t w) ((repsAt ch.G t w).elt β) (epsV_mem t w) (h j * r₀ j) ((r₀ j)⁻¹ * r j) 1 1 hL.1 hone
    _ _ (frame h₂) (frame h₁)
  have hB := hBes t w hw p hp M hM j 0 hj vN (h j * r₀ j) (hL.2.1 hev) (0 + 1) h₂
  have hJ := hJac t w hw p hp M hM j 0 hj vN 1 (Or.inl ⟨rfl, rfl⟩) 0 h₁
  have hs : ((p.xi ^ 0)⁻¹ : Kw w) ≠ 0 := by simp
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.Witness.exists_core p (besAt ch.G hM j 0 hj vN) hs
    (frTop ch.S.toGridChoice t w j (by omega))
  have hBF := GlobalTheory.FlatBFLoc.flatBF_of_laws D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  obtain ⟨T₀, hT₀, hT₀e⟩ := hBF (Kw w) p (unitVol w) (isUnitVol_unitVol w).1 ch.W.ψ (psiAt ch.W w) hc.1 0
    (besAt ch.G hM j 0 hj vN) (lastAt ch.G ch.W t hM j hj vN).J (lastAt ch.G ch.W t hM j hj vN).s (p.xi ^ 0)⁻¹ hs
    _ _ 0 (frTop ch.S.toGridChoice t w j (by omega)) F₀ _ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) _ hF₀ hB hJ Tm hTm
  have hψc : Continuous (psiAt ch.W w) := hc.2.1.continuous
  have hfl := GlobalTheory.LocFlat.flat_SB_onto (Kw w) (psiAt ch.W w) (unitVol w) hψc (isUnitVol_unitVol w).1
    (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j)) 0 (0 + 1) le_rfl
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator (Kw w) (psiAt ch.W w) (unitVol w) hc.2.1 (isUnitVol_unitVol w)
    (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j)) (Fin (topRank (locGrid ch.G t w) j)) 0 (0 + 1)
  refine ⟨F₀, T₀, hF₀, hT₀, fun O hO => ?_, ⟨_, (hfl.1 le_rfl).1 Φ.1 Φ.2⟩, ?_, ?_⟩
  · let Ob : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (0 + 1)) (Kw w)) :=
      ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
    have hOb : GlobalTheory.LocMod.IsOne Ob := rfl
    have e : O.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) Ob.1 := by
      rw [hO]
      show _ = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (Set.indicator _ _)
      rw [hun.1, ite_eq_right (by omega)]
    refine (hT₀e Ob O e).symm.trans ?_
    exact congrArg _ (hTmO Ob hOb)
  · show GlobalTheory.LocFlat.flCol _ _ _ Φ.1 = _
    congr 1
    funext z
    exact hΦ z
  · refine (hT₀e Φ ⟨_, (hfl.1 le_rfl).1 Φ.1 Φ.2⟩ rfl).symm.trans ?_
    refine congrArg _ (hTmΦ.trans ?_)
    have e : (h j * r₀ j * ((r₀ j)⁻¹ * r j), (1 : GA D (ch.G.V (.grid D.R.m (j + 1)))) * 1) = (h j * r j, 1) := by
      rw [mul_one, mul_assoc, mul_inv_cancel_left]
    rw [e]
    rfl

end GlobalTheory.LastStepOne
end
end

