module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrMemOfMemLatV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdPairTop

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_mem_latV (p : SplitPt D k) {S : HSp D} {L : Lat S}
    (hL : ∀ z ∈ L, z ∈ GlobalTheory.AdForm.intVec D S.rank) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L (· = p.v)) (i : Fin S.rank) : p.pr (y i) ∈ 𝒪[k] := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [p.int_iff, p.sec_pr, map_mul]
    refine FrameLat.mul_mem_intAE (FrameLat.e_mem_intAt p).2 ?_
    simp only [one_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, ⟨x i, hL x hx i⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => simpa using add_mem ha hb
  | neg a _ ha => simpa using neg_mem ha

theorem rat_mulVec_sec (p : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => p.sec (w i)) = fun i => p.sec (((rat Q).map p.pr *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (rat Q i j), FrameLat.sec_mul_right, mul_comm (w j)]

theorem hasVal_of_single {n : Type} [Fintype n] [DecidableEq n] (Q : GlobalTheory.LatPair.Pair k n) (l : n) (c : 𝓀[k])
    (hval : ∀ i, Q.HasVal (Pi.single i 1) (if i = l then c else 0)) (x : n → k) (hx : ∀ i, x i ∈ 𝒪[k]) :
    Q.HasVal x (residue 𝒪[k] ⟨x l, hx l⟩ * c) := by
  have key : ∀ T : Finset n, Q.HasVal (∑ i ∈ T, (⟨x i, hx i⟩ : 𝒪[k]) • (Pi.single i 1 : n → k))
      (∑ i ∈ T, residue 𝒪[k] ⟨x i, hx i⟩ * (if i = l then c else 0)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using GlobalTheory.LatPair.Pair.mem_ker.1 (zero_mem Q.ker)
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact ((hval a).smul _).add ih
  have h1 : (∑ i, (⟨x i, hx i⟩ : 𝒪[k]) • (Pi.single i 1 : n → k)) = x := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
  have h2 : (∑ i, residue 𝒪[k] ⟨x i, hx i⟩ * (if i = l then c else 0)) = residue 𝒪[k] ⟨x l, hx l⟩ * c := by
    simp [mul_ite]
  have := key Finset.univ
  rwa [h1, h2] at this

theorem mem_ker_iff {n : Type} (q : GlobalTheory.LatPair.Unif k) (Q : GlobalTheory.LatPair.Pair k n) (l : n) (c : 𝓀[k]) (hc : c ≠ 0)
    (hlat : ∀ x ∈ Q.lat, ∀ i, x i ∈ 𝒪[k])
    (hval : ∀ (x : n → k) (hx : ∀ i, x i ∈ 𝒪[k]), Q.HasVal x (residue 𝒪[k] ⟨x l, hx l⟩ * c)) (x : n → k) :
    x ∈ Q.ker ↔ (∀ i, x i ∈ 𝒪[k]) ∧ q.inv * x l ∈ 𝒪[k] := by
  have hq := q.ne_zero
  rw [GlobalTheory.LatPair.Pair.mem_ker]
  constructor
  · intro h
    have hx := hlat x h.mem
    refine ⟨hx, ?_⟩
    have h0 := (mul_eq_zero.1 ((hval x hx).unique h)).resolve_right hc
    obtain ⟨m, hm⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
    have hm' : x l = ((q.1 : 𝒪[k]) : k) * (m : k) := congrArg Subtype.val hm
    rw [hm', GlobalTheory.LatPair.Unif.inv, inv_mul_cancel_left₀ hq]
    exact m.2
  · rintro ⟨hx, h⟩
    have h0 : residue 𝒪[k] ⟨x l, hx l⟩ = 0 := (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨_, h⟩, Subtype.ext (by
      change x l = ((q.1 : 𝒪[k]) : k) * (q.inv * x l)
      rw [GlobalTheory.LatPair.Unif.inv, mul_inv_cancel_left₀ hq])⟩)
    have := hval x hx
    rwa [h0, zero_mul] at this

theorem row_eq_zero {S A L : HSp D} (o : OrthDec S A L) (hg : S.gram = 1) (ζ : Fin L.rank → D.host.E) (l : Fin S.rank)
    (a : D.host.E) (ha : a ≠ 0) (hv : ∀ r, vecB o ζ r = if r = l then a else 0) (j : Fin A.rank) : o.iA l j = 0 := by
  have h1 : star (vecB o ζ) ᵥ* o.iA = 0 := by
    have h := o.orth
    rw [hg, Matrix.mul_one] at h
    rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_zero]
  have h2 := congrFun h1 j
  simp only [Matrix.vecMul, dotProduct, Pi.star_apply, hv, Pi.zero_apply] at h2
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [if_neg hb, star_zero, zero_mul]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl] at h2
  exact (mul_eq_zero.1 h2).resolve_left (star_ne_zero.2 ha)

theorem ker_stdPair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (S A L : HSp D) (o : OrthDec S A L), S.gram = 1 → ∀ (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (π : 𝓞 D.host.E) (πc : D.host.E), (∀ r : Fin S.rank, vecB o ζ r = if r.1 + 1 = S.rank then ((π : 𝓞 D.host.E) : D.host.E) else 0) → valuation k (p.pr (incA D ((π : 𝓞 D.host.E) : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → valuation k (p.pr (incA D πc)) = 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LA : GlobalTheory.FinPl.Lat A), (∀ z, z ∈ LS ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → (∃ LZ : GlobalTheory.FinPl.Lat L, GlobalTheory.FinPl.OrthAt o LS LA LZ p.v) → ∀ (β : GlobalTheory.FinPl.Frame p S (Fin S.rank)) (Q : GlobalTheory.LatPair.Pair k (Fin S.rank)), β.b = 1 → β.IsLat LS Q.lat → (∀ z ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k], (s : k) = p.pr (incA D (πc * z r)) ∧ Q.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (z r'))) (residue 𝒪[k] s)) → ∃ (γ : GlobalTheory.FinPl.Frame p A (Fin A.rank)) (γ₀ : GlobalTheory.FinPl.Frame p S (Fin A.rank ⊕ Fin 1)), GlobalTheory.FinPl.IsSumFrame o ζ γ γ₀ ∧ ∃ (Λ : Submodule 𝒪[k] (Fin A.rank → k)) (s : 𝓀[k]ˣ), γ.IsLat LA Λ ∧ (∀ y, y ∈ Q.ker ↔ (γ₀.b' * β.b) *ᵥ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer Λ) ∧ Q.HasVal ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) s := by
  intro D k _ _ _ _ p q S A L o hg ζ hζ π πc hvec hπ hπc LS LA hLS hOrth β Q hb hlat hQ
  obtain ⟨LZ, hLZ⟩ := hOrth
  have hN : S.rank = A.rank + 1 := by rw [← o.rank_add, hζ.1]
  obtain ⟨l, hl⟩ : ∃ l : Fin S.rank, ∀ r : Fin S.rank, r.1 + 1 = S.rank ↔ r = l :=
    ⟨⟨A.rank, by omega⟩, fun r => by rw [Fin.ext_iff]; dsimp only; omega⟩
  simp only [hl] at hvec hQ
  have hb' : β.b' = 1 := by have := β.b'b; rwa [hb, Matrix.mul_one] at this
  have hsingle : ∀ i : Fin S.rank,
      (fun r' => p.pr (incA D ((Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) r'))) = Pi.single i 1 := by
    intro i
    funext r'
    by_cases h : r' = i
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, RingHom.map_one, RingHom.map_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, RingHom.map_zero, RingHom.map_zero]
  have hsLS : ∀ i : Fin S.rank, (Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) ∈ LS := by
    intro i
    rw [hLS]
    intro j
    by_cases h : j = i
    · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
  obtain ⟨s0, hs0, hv0⟩ := hQ _ (hsLS l) l rfl
  rw [hb', Matrix.one_mulVec, hsingle] at hv0
  rw [Pi.single_eq_same, mul_one] at hs0
  have hval : ∀ i : Fin S.rank, Q.HasVal (Pi.single i 1) (if i = l then residue 𝒪[k] s0 else 0) := by
    intro i
    split_ifs with h
    · subst h; exact hv0
    · obtain ⟨s, hs, hv⟩ := hQ _ (hsLS i) l rfl
      rw [hb', Matrix.one_mulVec, hsingle] at hv
      rw [Pi.single_eq_of_ne (Ne.symm h), mul_zero, RingHom.map_zero, RingHom.map_zero] at hs
      have h0 : s = 0 := Subtype.ext hs
      rwa [h0, RingHom.map_zero] at hv
  have hint := hasVal_of_single Q l _ hval
  have hres : ∀ s : 𝒪[k], valuation k (s : k) = 1 → residue 𝒪[k] s ≠ 0 := fun s hs =>
    (residue_ne_zero_iff_isUnit s).2 ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 hs)
  have hc : residue 𝒪[k] s0 ≠ 0 := hres s0 (by rw [hs0, hπc])
  have hlatV : ∀ x : Fin S.rank → k, x ∈ Q.lat ↔ (fun i => p.sec (x i)) ∈ latV S LS (· = p.v) := by
    intro x; rw [hlat x, hb, Matrix.one_mulVec]
  have hlatI : ∀ x : Fin S.rank → k, x ∈ Q.lat ↔ ∀ i, x i ∈ 𝒪[k] := by
    intro x
    refine ⟨fun h i => ?_, fun h => (hint x h).mem⟩
    have := pr_mem_of_mem_latV p (fun z hz => (hLS z).1 hz) ((hlatV x).1 h) i
    rwa [p.pr_sec] at this
  have hker := mem_ker_iff q Q l _ hc (fun x hx => (hlatI x).1 hx) hint
  have hq := q.ne_zero
  obtain ⟨πw, hπw⟩ : ∃ πw, p.pr (incA D ((π : 𝓞 D.host.E) : D.host.E)) = πw := ⟨_, rfl⟩
  have hqv : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  have hπ0 : ((π : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hqv (by
    rw [← hπ, h, RingHom.map_zero, RingHom.map_zero, Valuation.map_zero])
  rw [hπw] at hπ
  have hu : valuation k (q.inv * πw) = 1 := by
    rw [Valuation.map_mul, GlobalTheory.LatPair.Unif.inv, map_inv₀, hπ, inv_mul_cancel₀ hqv]
  have huO : q.inv * πw ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hu.le
  have hmulu : ∀ t : k, t * (q.inv * πw) ∈ 𝒪[k] ↔ t ∈ 𝒪[k] := fun t => by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]
  have hπO : πw ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by
    rw [hπ]; exact (Valuation.mem_integer_iff _ _).1 q.1.2)
  have hrow := row_eq_zero o hg ζ l _ hπ0 hvec
  obtain ⟨γ, hγ⟩ := ((_root_.GlobalTheory.InhPt.exists_splitPt_frame_char D).2 k p).1 A (Fin A.rank) 1 1 (Matrix.mul_one _) (Matrix.mul_one _)
  obtain ⟨γ₀, hsum⟩ := GlobalTheory.FinPl.DblInh.exists_sumFrame o hζ γ β
  have hact : ∀ (w : Fin A.rank ⊕ Fin 1 → k) (i : Fin S.rank), (γ₀.b *ᵥ w) i =
      (o.jA.map p.pr *ᵥ (w ∘ Sum.inl)) i + if i = l then πw * w (Sum.inr 0) else 0 := by
    intro w i
    have h : γ₀.b = _ := hsum
    rw [h, hγ, Matrix.mul_one]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
      replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, ratV, hvec]
    congr 1
    split_ifs
    · rw [hπw]
    · rw [RingHom.map_zero, RingHom.map_zero, zero_mul]
  have hlast : ∀ a : Fin A.rank → k, (o.jA.map p.pr *ᵥ a) l = 0 := fun a => by
    change ∑ j, p.pr (incA D (o.iA l j)) * a j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hrow, RingHom.map_zero, RingHom.map_zero, zero_mul]
  refine ⟨γ, γ₀, hsum, Q.lat.comap ((Matrix.mulVecLin (o.jA.map p.pr)).restrictScalars 𝒪[k]),
    Units.mk0 _ (mul_ne_zero (hres ⟨_, huO⟩ hu) hc), fun a => ?_, fun y => ?_, ?_⟩
  · change o.jA.map p.pr *ᵥ a ∈ Q.lat ↔ _
    have h := rat_mulVec_sec p o.iA a
    change o.jA *ᵥ _ = fun i => p.sec ((o.jA.map p.pr *ᵥ a) i) at h
    rw [hlatV, ← h, hLZ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.pA_jA, o.pB_jA, Matrix.one_mulVec,
      Matrix.zero_mulVec, hγ, Matrix.one_mulVec]
    exact and_iff_left (zero_mem _)
  · rw [hb, Matrix.mul_one, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, hker]
    obtain ⟨w, hw⟩ : ∃ w, γ₀.b' *ᵥ y = w := ⟨_, rfl⟩
    have hy : y = γ₀.b *ᵥ w := by rw [← hw, Matrix.mulVec_mulVec, γ₀.bb', Matrix.one_mulVec]
    rw [hw]
    change _ ↔ o.jA.map p.pr *ᵥ (w ∘ Sum.inl) ∈ Q.lat ∧ _
    have hyl : y l = πw * w (Sum.inr 0) := by rw [hy, hact, hlast, if_pos rfl, zero_add]
    have hyi : ∀ i, i ≠ l → y i = (o.jA.map p.pr *ᵥ (w ∘ Sum.inl)) i := fun i hi => by
      rw [hy, hact, if_neg hi, add_zero]
    rw [hlatI, hyl, ← mul_assoc, mul_comm _ (w (Sum.inr 0)), hmulu]
    refine and_congr_left fun ht => forall_congr' fun i => ?_
    by_cases hi : i = l
    · rw [hi, hyl, hlast]
      exact iff_of_true (mul_mem hπO ht) (zero_mem _)
    · rw [hyi i hi]
  · have hx : ∀ i, ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) i =
        if i = l then q.inv * πw else 0 := fun i => by
      have h0 : (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1) ∘ Sum.inl = 0 := by
        funext j; simp [GlobalTheory.LatPair.avec]
      have h1 : (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1) (Sum.inr 0) = q.inv := by
        simp [GlobalTheory.LatPair.avec]
      rw [hb', Matrix.one_mul, hact, h0, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add, mul_comm]
    have hO : ∀ i, ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) i ∈ 𝒪[k] := fun i => by
      rw [hx]
      split_ifs
      · exact huO
      · exact zero_mem _
    have h := hint _ hO
    have e : (⟨_, hO l⟩ : 𝒪[k]) = ⟨_, huO⟩ := Subtype.ext ((hx l).trans (if_pos rfl))
    rw [e] at h
    exact h

end GlobalTheory.StdPairTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelIntegralTwist
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence
open scoped Matrix

theorem core (I : AutInst) (g : ℕ) {r : ℕ} (e0 : Fin r → VA I) (z0 : VA I) (hz0 : z0 ∈ I.Lf)
    (hzz : ZMod' I g (hA I z0 z0 + 1)) (hze : ∀ a, ZMod' I g (hA I (e0 a) z0))
    (x : I.Gf) (hxK : x ∈ I.Kset) (hxz : InMod I g (Set.range e0) ((I.fmat x - 1) *ᵥ z0))
    (v v' : VA I) (hv : InAt I g g (v - z0)) (hv' : InAt I g g (v' - z0))
    (ε c c₂ : I.E ⊗[I.F] Af I.F) (hε : ε ∈ IntAf I.F I.E) (hc : c ∈ IntAf I.F I.E) (hc₂ : c₂ ∈ IntAf I.F I.E)
    (hyp : ε • (c • (I.fmat x *ᵥ v')) = ε • (c₂ • v)) :
    ∃ N : ℕ, N.Coprime g ∧ ZMod' I g (ε * (c - c₂) * (N : I.E ⊗[I.F] Af I.F)) := by
  obtain ⟨n, hn, hnv⟩ := hv
  obtain ⟨n', hn', hnv'⟩ := hv'
  refine ⟨n * n', Nat.Coprime.mul_left hn hn', ?_⟩

  have hQ : Mo I g (Set.range e0) ≤ Qs I g z0 := by
    refine sup_le (Submodule.span_le.2 ?_) (mL_Qs I g hz0)
    rintro _ ⟨a, rfl⟩
    show ZMod' I g (hA I z0 (e0 a))
    rw [hA_symm]; exact Z_sig I g (hze a)
  have hmL : mL I g ≤ Qs I g z0 := mL_Qs I g hz0
  have hxmL : ∀ w ∈ mL I g, I.fmat x *ᵥ w ∈ mL I g := fun w hw =>
    pres I hxK g ∅ (mL I g) (by simp) (by simp) le_rfl w (mL_Mo I hw)
  have hNint : ∀ m : ℕ, ((m : I.E ⊗[I.F] Af I.F)) ∈ IntAf I.F I.E := fun m => natCast_mem _ m

  have hA1 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ v') + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : I.fmat x *ᵥ v' = z0 + (I.fmat x - 1) *ᵥ z0 + I.fmat x *ᵥ (v' - z0) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
      abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ (v' - z0)) =
        (n : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0))) := by
      rw [Matrix.mulVec_smul, hA_smul_right, Nat.cast_mul]; ring
    have h2 : ZMod' I g (hA I z0 ((I.fmat x - 1) *ᵥ z0)) := hQ hxz
    have h3 : ZMod' I g (hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0)))) := hmL (hxmL _ hnv')
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g (Z_add I g h1 (Z_smul I g (hNint (n * n')) h2)) (Z_smul I g (hNint n) h3)
    rw [e, hA_add_right, hA_add_right]
    convert this using 1
    rw [← e2]; ring
  have hA2 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 v + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : v = z0 + (v - z0) := by abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (v - z0) =
        (n' : I.E ⊗[I.F] Af I.F) * hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0)) := by
      rw [hA_smul_right, Nat.cast_mul]; ring
    have h3 : ZMod' I g (hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0))) := hmL hnv
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g h1 (Z_smul I g (hNint n') h3)
    rw [e, hA_add_right]
    convert this using 1
    rw [← e2]; ring

  have key : ε * (c * hA I z0 (I.fmat x *ᵥ v')) = ε * (c₂ * hA I z0 v) := by
    have := congrArg (fun w => hA I z0 w) hyp
    simp only [hA_smul_right] at this
    exact this
  have := Z_sub I g (Z_smul I g (mul_mem hε hc) hA1) (Z_smul I g (mul_mem hε hc₂) hA2)
  convert this using 1
  linear_combination (-((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) * key

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem res_eq {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) (g : ℕ) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (N : ℕ) (hN : N.Coprime g)
    (hZ : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (ε * (c - c₂) * (N : Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨t, ht, he⟩ := hZ
  have hs : (⟨ε, hε⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (⟨c, hc⟩ - ⟨c₂, hc₂⟩) * (N : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (g : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨t, ht⟩ := Subtype.ext (by
    push_cast
    exact he)
  have hr := congrArg (Formalism.L2.DIV.resS D.host.F PP) hs
  simp only [map_mul, map_sub, map_natCast, hε1, one_mul] at hr
  have hg0 : ((g : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    show ((g : 𝓞 D.host.E) : 𝓞 D.host.E ⧸ PP.asIdeal) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hg
  have hN0 : ((N : ℕ) : Formalism.L2.DIV.kP PP) ≠ 0 := by
    intro h0
    have hNm : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h0
    have hco : IsCoprime ((N : ℤ) : 𝓞 D.host.E) ((g : ℤ) : 𝓞 D.host.E) :=
      (Nat.isCoprime_iff_coprime.2 hN).map (Int.castRingHom (𝓞 D.host.E))
    obtain ⟨a, b, hab⟩ := hco
    push_cast at hab
    apply PP.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hNm) (Ideal.mul_mem_left _ _ hg)
  rw [hg0, zero_mul] at hr
  exact sub_eq_zero.1 ((mul_eq_zero.1 hr).resolve_right hN0)

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem finE_inv_val {D : D7} (y : GA D (D.sp.Y 0)) :
    ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (((Formalism.IndefR.RationalEmbedding.iota D) y).2)⁻¹ :=
  (congrArg Units.val (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) (show GA D (Yc D 0) from y)).symm).trans
    ((GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) (y⁻¹ : GA D (D.sp.Y 0))).symm.trans
      (congrArg (fun p : (Formalism.IndefR.RationalEmbedding.inst D).GA => (Formalism.L2.SG.InstExistsPf.instOf D).fmat p.2) (map_inv (Formalism.IndefR.RationalEmbedding.iota D) y)))

theorem core_res {D : D7} {r : ℕ} (e0 : Fin r → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (g : ℕ) (hz0 : z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf)
    (hzz : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1)) (hze : ∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0))
    (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hxK : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) (hxz : InMod (Formalism.L2.SG.InstExistsPf.instOf D) g (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0))
    (v v' : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hv : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v - z0)) (hv' : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v' - z0))
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (w w' : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D)
    (hM : M = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x) (hw : w = v) (hw' : w' = v')
    (hyp : ε • (c • (M *ᵥ w')) = ε • (c₂ • w)) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  subst hM hw hw'
  obtain ⟨N, hN, hZ⟩ := core (Formalism.L2.SG.InstExistsPf.instOf D) g e0 z0 hz0 hzz hze x hxK hxz w w' hv hv' ε c c₂ hε hc hc₂ hyp
  exact res_eq PP g hg ε c c₂ hε hε1 hc hc₂ N hN hZ


set_option maxHeartbeats 400000 in
theorem frame_facts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = (Formalism.L2.SG.InstExistsPf.instOf D)) (hId : IdE X) :
    ∃ (e0 : Fin D.R.rS → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)), z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ∧ ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1) ∧
      (∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0)) ∧
      (∀ κ ∈ rowJ X h, ∃ x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf, ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = x ∧ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ∧
        InMod (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0)) ∧
      ∀ u : D.what₂.Word, ∃ (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)),
        ((Formalism.IndefR.RationalEmbedding.iota D) ((iotaX X h).symm (1, X.xu u))).2 = x ∧
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r)))) = z ∧
        InAt (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (D.host.g 0 * D.host.g 1) ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z - z0) := by
  have hi : ∀ u, (iotaX X h) ((iotaX X h).symm (1, X.xu u)) = (1, X.xu u) := fun u => (iotaX X h).apply_symm_apply _
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan, e_eq, xu, xu_fix, xu_z, xu_one, xu_K⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hs : ∀ y : D.host.E, ιE.symm y = y := fun y => by
    have := eq_of_heq (hId (ιE.symm y))
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨e0, z0, vectorsInLattice.2.1, formsAtZero.1, fun a => (formsAtZero.2 a).1, fun κ hκ => ?_, fun u => ?_⟩
  · have hk : ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 ∈ K2set (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw := hκ.2
    exact ⟨_, rfl, hk.1, hk.2.2.1⟩
  · refine ⟨xu u, incl (Formalism.L2.SG.InstExistsPf.instOf D) (crdOf (Formalism.L2.SG.InstExistsPf.instOf D) ιE bas (zu u)), congrArg Prod.snd (hi u), ?_, xu_z u⟩
    funext r
    show algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE (ιE.symm (bas.repr (zu u) r))) =
      algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE.symm (bas.repr (zu u) r))
    rw [RingEquiv.apply_symm_apply, hs]

theorem inv_mulVec_eq {D : D7} (y : GA D (D.sp.Y 0)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hx : ((Formalism.IndefR.RationalEmbedding.iota D) y).2 = x)
    (w : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hz : w = z) :
    Matrix.mulVec ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val w =
      ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) := by
  subst hx hz
  exact congrArg (fun M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D) => Matrix.mulVec M w) (finE_inv_val y)


set_option maxHeartbeats 400000 in
theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X)
    (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ rowJ X h)
    (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hE : ε • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u' (Fin.cast (rank_eq X h) r)))))) = ε • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r))))))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨e0, z0, hz0, hzz, hze, hK, hu⟩ := frame_facts X h hId
  obtain ⟨x, hx, hxK, hxz⟩ := hK κ hκ
  obtain ⟨y, z, hy, hz, hv⟩ := hu u
  obtain ⟨y', z', hy', hz', hv'⟩ := hu u'
  have e1 : (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x :=
    (GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) κ).symm.trans (congrArg (Formalism.L2.SG.InstExistsPf.instOf D).fmat hx)
  have e2 := inv_mulVec_eq _ y hy _ z hz
  have e3 := inv_mulVec_eq _ y' hy' _ z' hz'
  exact core_res e0 z0 _ hz0 hzz hze x hxK hxz _ _ hv hv' PP hg ε c c₂ hε hε1 hc hc₂ _ _ _ e1 e2 e3 hE

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

end GlobalTheory.CongFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMonomialLatticeSplitCoreStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceComponent_monomialLattice_splitCore : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A), MonoAt d L M p.v → (∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v)) → (∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v)) → LineAt (vecB o ζ) μ M p.v → SplitsAt o M p.v → TraceAt o g N M p.v → WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.wShape_of_mono | exact GlobalTheory.Core.Mi.LatMatch.wShape_of_mono | (intros; apply GlobalTheory.Core.Mi.LatMatch.wShape_of_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjugateStabilizerKeepsMovedFrameLattStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_conjugate_stabilizer_keeps_movedFrameLattice : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y), (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) → ∀ (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm) → ∀ g : GA D S, Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β → GlobalTheory.FinPl.Moves S g L L (· = q.v) := by
  first | exact @GlobalTheory.LocMod.StMoves.moves_of_mem_St | exact GlobalTheory.LocMod.StMoves.moves_of_mem_St | (intros; apply GlobalTheory.LocMod.StMoves.moves_of_mem_St <;> assumption)
end

