module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemCosetInOfRes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PenChart

section Orbits
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem corner_mul (g h : GL (n ⊕ Fin 0) k) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  ext i j
  rw [Units.val_mul]
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply]

theorem corner_one : (1 : GL (n ⊕ Fin 0) k).val.toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem box_stable {g : GL (n ⊕ Fin 0) k} (hg : g ∈ KO k _) (a : kˣ) {y : n → k} (hy : y ∈ box n a) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box n a := fun i => by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((mem_KO.1 hg).1 (Sum.inl i) (Sum.inl j)) (hy j)

theorem sameOrb_equiv {J : Subgroup (GL (n ⊕ Fin 0) k)} (hJ : J ≤ KO k _) (c : kˣ) : Equivalence (SameOrb J (box n c)) := by
  refine ⟨fun yb => ?_, fun {yb yb'} H => ?_, fun {yb yb' yb''} H H' => ?_⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
    exact ⟨1, one_mem _, y, rfl, by rw [corner_one, one_mulVec]⟩
  · obtain ⟨g, hg, y, rfl, e⟩ := H
    refine ⟨g⁻¹, inv_mem hg, g.val.toBlocks₁₁ *ᵥ y, e, ?_⟩
    rw [mulVec_mulVec, ← corner_mul, inv_mul_cancel, corner_one, one_mulVec]
  · obtain ⟨g, hg, y, rfl, e1⟩ := H
    obtain ⟨h, hh, y', e2, e3⟩ := H'
    refine ⟨h * g, mul_mem hh hg, y, rfl, ?_⟩
    rw [← e3, corner_mul, ← mulVec_mulVec, Submodule.Quotient.eq, ← mulVec_sub]
    rw [← e1] at e2
    exact box_stable (hJ hh) _ ((Submodule.Quotient.eq _).1 e2.symm)

theorem box_le {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (M : ℕ) {y : n → k} (hy : y ∈ box n (ϖ ^ M)) : y ∈ box n (ϖ ^ M)⁻¹ := fun i => by
  have h1 : valuation k ((ϖ ^ M : kˣ) : k) ≤ 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' ((hϖ _).2 le_rfl).le _
  refine ((hy i).trans h1).trans ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  exact (one_le_inv₀ ((Valuation.pos_iff _).2 (Units.ne_zero _))).2 h1

theorem mul_int_iff (c : kˣ) (x : k) : (c : k) * x ∈ 𝒪[k] ↔ valuation k x ≤ valuation k ((c⁻¹ : kˣ) : k) := by
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← mul_one (_⁻¹),
    le_inv_mul_iff₀ ((Valuation.pos_iff _).2 (Units.ne_zero _))]

theorem inv_sub_inv_int {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {q : k} (h : valuation k ((ϖ : k) - q) < valuation k (ϖ : k)) :
    q⁻¹ - ((ϖ⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 (Units.ne_zero _)
  have hq : valuation k q = valuation k (ϖ : k) := Valuation.map_eq_of_sub_lt _ (by rwa [Valuation.map_sub_swap])
  have hq0 : q ≠ 0 := fun e => by rw [e, map_zero] at hq; exact h0.ne hq
  have h1 := (hϖ (((ϖ : k) - q) / ϖ)).1 (by rw [map_div₀]; exact (div_lt_one₀ h0).2 h)
  have e : q⁻¹ - ((ϖ⁻¹ : kˣ) : k) = ((ϖ : k) - q) / ϖ / q := by
    rw [Units.val_inv_eq_inv_val]
    have := ϖ.ne_zero
    field_simp
  rw [e, Valuation.mem_integer_iff, map_div₀, hq]
  exact (div_le_one₀ h0).2 h1

end Orbits

section Restr
variable {D : D7} {c : Comm D} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl D.host.E} {G : QGeo v Bs PP} {χ : ℕ → (AE D)ˣ →* Circle}

def InBox (E : QExt G χ) (j : ℕ) (y : E.Ch j) : Prop :=
  ∀ h : j = G.s + 1, ∃ z ∈ box _ (G.ϖ ^ E.M)⁻¹, E.cos (h ▸ y) = Submodule.Quotient.mk z

theorem inBox_of_orb (E : QExt G χ) {y : E.Ch (G.s + 1)} {z} (hz : z ∈ box _ (G.ϖ ^ E.M)⁻¹)
    (h : SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ E.M)) (E.cos y) (Submodule.Quotient.mk z)) :
    InBox E (G.s + 1) y := by
  obtain ⟨g, hg, y', e1, e2⟩ := (sameOrb_equiv (E.le _ _ _) _).symm h
  refine fun _ => ⟨_, box_stable (E.le _ _ _ hg) _ ?_, e2.symm⟩
  have := add_mem (box_le G.unif _ ((Submodule.Quotient.eq _).1 e1)) hz
  rwa [sub_add_cancel] at this


set_option maxHeartbeats 4000000 in
@[reducible] def restr (E : QExt G χ) : QExt G χ :=
  { E with
    Ch := fun j => {y : E.Ch j // InBox E j y}
    fC := fun _ => Subtype.fintype _
    rep := fun j d h y => E.rep j d h y.1
    rep_bij := fun j d h => (E.rep_bij j d h).comp
      (Equiv.subtypeUnivEquiv (p := InBox E j) fun _ _ => by omega).bijective.bijOn_univ
    cos := fun y => E.cos y.1
    cos_inj := fun _ _ h => Subtype.ext (E.cos_inj _ _ h)
    cos_all := fun z hz => (E.cos_all z hz).elim fun y hy => ⟨⟨y, inBox_of_orb E hz hy⟩, hy⟩
    one := (Fintype.card_congr (Equiv.subtypeUnivEquiv (p := InBox E (G.s + 1 + 1)) fun _ _ => by omega)).trans E.one
    dL := fun j α γ => E.dL j α.1 γ.1
    dL_mid := fun j d H α γ => E.dL_mid j d H α.1 γ.1
    dL_pen := fun α y => E.dL_pen α.1 y.1
    dL_top := fun y u => E.dL_top y.1 u.1
    εL := fun j α => E.εL j α.1
    εL_at := fun j ρ hρ d h α => E.εL_at j ρ hρ d h α.1
    εL_zero := fun α => E.εL_zero α.1
    wt := fun j α => E.wt j α.1
    wt_mid := fun j d h α => E.wt_mid j d h α.1
    wt_pen := fun y => E.wt_pen y.1
    wt_top := fun u => E.wt_top u.1 }

end Restr

section Place
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)
  {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E} {G : QGeo v Bs PP}
  {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ)

abbrev Orb := SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box (XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1)) (G.ϖ ^ E.M))


variable (G) in
abbrev locV (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))) (z : Formalism.L2.Col.Sp B.fields.E (B.R.N (G.s + 1))) :
    XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) → G.k := fun r => (ofSplit G.q).pr (z (e r))

def OrbAt (j : ℕ) (y : E.Ch j) (β : Ch₀ j) : Prop :=
  ∀ (h : j = G.s + 1) (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
    Orb E (E.cos (h ▸ y)) (Submodule.Quotient.mk (locV G e (Formalism.L2.Col.repY (A.p0 (G.s + 1) (h ▸ β)).1.2)))

variable {A E} {P : BadPr I a} {hψ : Continuous G.ψk} {sg : ℂ}


set_option maxHeartbeats 1000000 in
theorem orb_iff (hI : I.Ok)
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (hM : E.M = (I.cst a).M) (b : Idx I.sel (I.tup a) (I.idx a) (G.s + 1)) (hQ : P.1 ∈ I.Q a) {e}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e) (z z') :
    Orb E (Submodule.Quotient.mk (locV G e z)) (Submodule.Quotient.mk (locV G e z')) ↔
      ∃ κ ∈ (levQ I a (G.s + 1) b ⟨P.1, hQ⟩).H, ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ (I.cst a).M)⁻¹ • (κ.1 z - z') ∈
        Formalism.L2.Col.stdAt B.fields.E (B.R.N (G.s + 1)) P.1 := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = G.s by omega] at hL
  have h := GlobalTheory.T.twistPrime_rational_coset_sameOrbit_iff_level B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) B.embLL P G.k _ G.s _ tw (I.idx a) I.glob hL
    (b.get (by omega)) hQ e he z z'
  have e1 : levQ I a (G.s + 1) b = (I.idx a).levQ (G.s + 1) (b.get (by omega)) := by
    unfold levQ levQAt
    rw [← b.some_get (by omega)]
    rfl
  rw [e1, ← h]
  unfold Orb
  rw [hM]
  rfl

theorem locV_mem_iff
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (M : ℕ) (e) (z) : locV G e z ∈ box _ (G.ϖ ^ M)⁻¹ ↔
      (Formalism.L2.Col.qOf P.1 : B.fields.E) ^ M • z ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N (G.s + 1)) P.1 := by
  letI := GlobalTheory.Mem.Col2.starE B
  rw [GlobalTheory.TopStep.mem_stdAt, mem_box, e.forall_congr_right.symm]
  refine forall_congr' fun r => ?_
  have hu : (G.ϖ : G.k) = _ := tw.compl.unif
  rw [← tw.compl.int, ← mul_int_iff, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hu, Units.val_pow_eq_pow_val]
  rfl

theorem orbAt_unique {j : ℕ} (hj : j + 1 = B.R.m) {y y' : E.Ch j} {β : Ch₀ j} (h : OrbAt A E j y β) (h' : OrbAt A E j y' β) : y = y' := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  obtain rfl : j = G.s + 1 := by omega
  obtain ⟨e, he⟩ := exists_xOrd B.R (G.s + 1)
  have H := sameOrb_equiv (E.le (G.s + 1) 0 rfl) (G.ϖ ^ E.M)
  exact E.cos_inj _ _ (H.trans (h rfl e he) (H.symm (h' rfl e he)))


set_option maxHeartbeats 1000000 in
theorem exists_orbAt (hI : I.Ok) (hA : A.Is)
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (hM : E.M = (I.cst a).M) {j : ℕ} (hj : j + 1 = B.R.m) (β : Ch₀ j) (hk : A.kb j β = TC.kStd X u (B.R.N j)) :
    ∃ y, InBox E j y ∧ OrbAt A E j y β := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  obtain rfl : j = G.s + 1 := by omega
  obtain ⟨e, he⟩ := exists_xOrd B.R (G.s + 1)
  have h0 := ownVec_mem A P tw.nmem tw.compl e β
  have hv := (MemChart.kStd_spec l.pr u (B.R.N (G.s + 1))).2.1
  rw [← hk] at hv
  have e1 := GlobalTheory.QTw.frsF_base_eq_self A hA hI P tw.nmem _ (by omega) β hv
  have e' : ownVec A G P e β = locV G e (Formalism.L2.Col.repY (A.p0 (G.s + 1) β).1.2) := by
    unfold ownVec
    rw [(LinearEquiv.symm_apply_eq _).2 (e1 _).symm]
  rw [e', ← hM] at h0
  obtain ⟨y, hy⟩ := E.cos_all _ h0
  refine ⟨y, inBox_of_orb E h0 hy, fun _ e' he' => ?_⟩
  obtain rfl : e' = e := Equiv.ext fun r => Fin.ext ((he' r).trans (he r).symm)
  exact hy


set_option maxHeartbeats 1000000 in
theorem lev_of_orbAt (hI : I.Ok) (hA : A.Is)
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (hM : E.M = (I.cst a).M) {j : ℕ} (hj : j + 1 = B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) (hQ : P.1 ∈ I.Q a) {y : E.Ch j}
    {β β' : Ch₀ j} (hk : A.kb j β = TC.kStd X u (B.R.N j)) (hk' : A.kb j β' = TC.kStd X u (B.R.N j))
    (h : OrbAt A E j y β) (h' : OrbAt A E j y β') :
    ∃ κ ∈ (levQ I a j b ⟨P.1, hQ⟩).H, ∃ z ∈ cosetIn (A.p0 j β) P, κ.1 z ∈ cosetIn (A.p0 j β') P := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  obtain rfl : j = G.s + 1 := by omega
  obtain ⟨e, he⟩ := exists_xOrd B.R (G.s + 1)
  have H := sameOrb_equiv (E.le (G.s + 1) 0 rfl) (G.ϖ ^ E.M)
  obtain ⟨κ, hκ, h1⟩ := (orb_iff hI tw hM b hQ he _ _).1 (H.trans (H.symm (h rfl e he)) (h' rfl e he))
  refine ⟨κ, hκ, _, repY_mem hI hA hj β hk P, mem_of_sub (repY_mem hI hA hj β' hk' P) ?_⟩
  rw [if_neg tw.nmem]
  exact h1


set_option maxHeartbeats 1000000 in
theorem exists_vec (hI : I.Ok) (hA : A.Is)
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (hM : E.M = (I.cst a).M) {j : ℕ} (hj : j + 1 = B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) {y : E.Ch j} (hy : InBox E j y) :
    ∃ z : Formalism.L2.Col.Sp B.fields.E (B.R.N j),
      (Formalism.L2.Col.qOf P.1 : B.fields.E) ^ (I.cst a).M • z ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N j) P.1 ∧
      ∀ (hQ : P.1 ∈ I.Q a) (β : Ch₀ j), A.kb j β = TC.kStd X u (B.R.N j) →
        (∃ κ ∈ (levQ I a j b ⟨P.1, hQ⟩).H, κ.1 z ∈ cosetIn (A.p0 j β) P) → OrbAt A E j y β := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  obtain rfl : j = G.s + 1 := by omega
  obtain ⟨e, he⟩ := exists_xOrd B.R (G.s + 1)
  obtain ⟨(w : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) → G.k), hw, hc⟩ := hy rfl
  have hap : ∀ x : G.k, ∃ z : B.fields.E, valuation G.k ((ofSplit G.q).pr z - x) ≤ valuation G.k ((G.ϖ ^ E.M : G.kˣ) : G.k) := fun x => by
    have hn : {y : G.k | valuation G.k (y - x) < valuation G.k ((G.ϖ ^ E.M : G.kˣ) : G.k)} ∈ nhds x :=
      IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ ((Valuation.ne_zero_iff _).2 (G.ϖ ^ E.M).ne_zero), fun y hy => by simpa using hy⟩
    obtain ⟨_, hy, z, rfl⟩ := mem_closure_iff_nhds.1 (tw.compl.dense x) _ hn
    exact ⟨z, le_of_lt hy⟩
  choose f hf using hap
  have h1 : locV G e (fun r => f (w (e.symm r))) - w ∈ box _ (G.ϖ ^ E.M) := fun r => by
    have := hf (w r)
    simpa only [Pi.sub_apply, locV, Equiv.symm_apply_apply] using this
  have h2 := add_mem (box_le G.unif _ h1) hw
  rw [sub_add_cancel] at h2
  refine ⟨fun r => f (w (e.symm r)), hM ▸ (locV_mem_iff tw _ e _).1 h2, ?_⟩
  rintro hQ β hk ⟨κ, hκ, h3⟩ _ e' he'
  obtain rfl : e' = e := Equiv.ext fun r => Fin.ext ((he' r).trans (he r).symm)
  have h4 := sub_of_mem hj (repY_mem hI hA hj β hk P) h3
  rw [if_neg tw.nmem] at h4
  have h5 := (orb_iff hI tw hM b hQ he _ _).2 ⟨κ, hκ, h4⟩
  have h6 : Submodule.Quotient.mk (locV G e' fun r => f (w (e'.symm r))) = E.cos y := ((Submodule.Quotient.eq _).2 h1).trans hc.symm
  exact (congrArg (fun x => Orb E x _) h6).mp h5

end Place

section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem couplingCoset_sub_basePoint_integral_typePrime (hI : I.Ok) (hA : A.Is) {s : ℕ} (hs : s + 1 + 1 = B.R.m) (S : GlobalTheory.SymChain.SymData k s B.R.k) (ι : B.fields.E →+* k)
    (P : BadPr I a) (hP : P.1 ∈ (B.primes X).vGs) (hint : ∀ x, ι x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x)
    (hu : valuation k ((S.ϖ : k) - ((Formalism.L2.Col.qOf P.1 : ℕ) : k)) < valuation k (S.ϖ : k)) (β : Ch₀ (s + 1))
    (hk : A.kb (s + 1) β = TC.kStd X u (B.R.N (s + 1))) (hβ : Good (A.p0 (s + 1) β))
    (e : XIx (Fin B.R.k) (Fin B.R.t) (s + 1) ≃ Fin (B.R.N (s + 1))) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e) (r) :
    ι (Formalism.L2.Col.repY (A.p0 (s + 1) β).1.2 (e r)) - S.y0 (Fin B.R.t) r ∈ 𝒪[k] := by
  letI := GlobalTheory.Mem.Col2.starE B
  have h1 := sub_of_mem hs (hβ P hP) (repY_mem hI hA hs β hk P)
  rw [if_pos hP, pow_zero, inv_one, one_smul] at h1
  have h2 := (hint _).2 (GlobalTheory.TopStep.mem_stdAt.1 h1 (e r))
  rw [Pi.sub_apply, map_sub, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast] at h2
  have h3 : ((Formalism.L2.Col.qOf P.1 : ℕ) : k)⁻¹ * ι (Formalism.L2.Col.Loc.eN B.fields.E (B.R.N (s + 1)) B.R.k (e r)) - S.y0 (Fin B.R.t) r ∈ 𝒪[k] := by
    have h0 : (e (Sum.inl (Sum.inr 0))).val = B.R.k := he _
    unfold Formalism.L2.Col.Loc.eN GlobalTheory.SymChain.SymData.y0
    by_cases hr : r = Sum.inl (Sum.inr 0)
    · subst hr
      rw [if_pos h0, map_one, mul_one, Pi.single_eq_same]
      exact inv_sub_inv_int S.unif hu
    · rw [if_neg fun h => hr (e.injective (Fin.ext (h.trans h0.symm))), map_zero, mul_zero, Pi.single_eq_of_ne hr, sub_zero]
      exact zero_mem _
  have := add_mem h2 h3
  rwa [sub_add_sub_cancel] at this

end Level


end GlobalTheory.PenChart
