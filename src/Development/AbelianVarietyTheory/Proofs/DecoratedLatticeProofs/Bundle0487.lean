module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QPl.EpsSupp

theorem exists_prod_of_mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

theorem eps_mem_grpAt {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ)
    (h0 : ∀ i β, (F.Q i).εL 0 β = Finsupp.single 1 1) (j : ℕ) (α : t.Ch j) :
    ∀ g ∈ ((F.pinTup sc cT).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ (F.pinTup sc cT).Q) := by
  classical
  intro g hg
  dsimp only [QFam.pinTup] at hg ⊢
  split_ifs at hg with hc
  · have hg' := Finsupp.support_smul hg
    obtain ⟨x, hx, rfl⟩ := exists_prod_of_mem_support_conv _ _ g hg'
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    have hP : (F.Q i).q.v ∈ Finset.univ.image fun i => (F.Q i).q.v := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rcases hc with ⟨ρ, hρ⟩ | hj
    · obtain ⟨e, -, he⟩ := (F.Q i).εL_at j ρ hρ (2 * ρ) (by have := (F.Q i).hs; omega) (F.eqv j α i)
      have hxi := hx i
      rw [he] at hxi
      obtain ⟨a, -, hax⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hxi)
      rw [← hax]
      exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D _ (F.Q i).q _ _ ((F.Q i).gl_loc _ _ _ a).1 _ hP
    · subst hj
      have hxi := hx i
      rw [h0] at hxi
      have h1 := Finsupp.support_single_subset hxi
      rw [Finset.mem_singleton] at h1
      rw [h1]
      exact one_mem _
  · simp at hg

end GlobalTheory.QPl.EpsSupp

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QPl.PinComb

variable {D : D7} {c : Comm D}

def mxSub (P : GlobalTheory.FinPl.Pl D → Prop) (S T : HSp D) : AddSubmonoid (WO S T) where
  carrier := {u | GlobalTheory.FinPl.MxAt P u}
  zero_mem' := fun i j => by
    simpa using (GlobalTheory.FinPl.idAt D P).zero_mem
  add_mem' {a b} ha hb := fun i j => by
    simpa using (GlobalTheory.FinPl.idAt D P).add_mem (ha i j) (hb i j)

theorem combAt_aconv {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} (l : List (WO S T →₀ ℂ))
    (hl : ∀ e ∈ l, GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P (aconv l) :=
  GlobalTheory.QPl.ThetaPin.aconv_support (mxSub P S T) l hl

theorem combAt_smul {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} (r : ℂ) {e : WO S T →₀ ℂ}
    (he : GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P (r • e) :=
  fun u hu => he u (Finsupp.support_smul hu)

theorem combAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} : GlobalTheory.FinPl.CombAt P (0 : WO S T →₀ ℂ) :=
  fun u hu => by simp at hu

theorem combAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {e : WO S T →₀ ℂ}
    (he : GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P' e :=
  fun u hu => GlobalTheory.DisjComb.mxAt_mono h (he u hu)

theorem combAt_of_isCombAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {q : GlobalTheory.FinPl.SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
    {e : WO S T →₀ ℂ} {Ξ : Matrix Y Y' k → ℂ} (h : (ofSplit q).IsCombAt ψ FS FT e Ξ) : GlobalTheory.FinPl.CombAt (· = q.v) e :=
  fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D k q u (h.1 u hu)

variable {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

theorem eL_combAt (Q : QAt v χ) (j : ℕ) (hj : j ≤ Q.s) : GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.eL j) := by
  obtain ⟨d, hd⟩ : ∃ d, j + d = Q.s := ⟨Q.s - j, by omega⟩
  exact combAt_of_isCombAt (Q.eL_at j d hd)

theorem eT_combAt (Q : QAt v χ) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.eT j h) := by
  have hj : j = Q.s := by have := Q.hs; omega
  subst hj
  exact combAt_of_isCombAt Q.eLT_at

theorem dL_combAt (Q : QAt v χ) (j : ℕ) (hj : j ≤ Q.s + 1) (α : Q.Ch j) (γ : Q.Ch (j + 1)) :
    GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.dL j α γ) := by
  rcases Nat.lt_or_ge j Q.s with h | h
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = Q.s := ⟨Q.s - (j + 1), by omega⟩
    exact combAt_of_isCombAt (Q.dL_mid j d hd α γ)
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      exact combAt_of_isCombAt (Q.dL_pen α γ)
    · have h'' : j = Q.s + 1 := by omega
      subst h''
      exact combAt_of_isCombAt (Q.dL_top α γ)

theorem pinTup_combAt {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ) (j : ℕ) :
    GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).eQ j) ∧
      (∀ h, GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).eQT j h)) ∧
      ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).dQ j α γ) := by
  have hQ : ∀ i, (F.Q i).q.v ∈ (F.pinTup sc cT).Q := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hmono : ∀ i {S T : HSp D} {e : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt (· = (F.Q i).q.v) e →
      GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) e :=
    fun i _ _ _ he => combAt_mono (fun p hp => hp ▸ hQ i) he
  have hs : ∀ i, (F.Q i).s + 1 + 1 = D.R.m := fun i => (F.Q i).hs
  refine ⟨?_, fun h => ?_, fun α γ => ?_⟩
  · show GlobalTheory.FinPl.CombAt _ (if j + 1 < D.R.m then aconv (List.ofFn fun i => (F.Q i).eL j) else 0)
    split_ifs with hj
    · refine combAt_aconv _ fun e he => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      exact hmono i (eL_combAt _ j (by have := hs i; omega))
    · exact combAt_zero
  · show GlobalTheory.FinPl.CombAt _ (aconv (List.ofFn fun i => (F.Q i).eT j h))
    refine combAt_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact hmono i (eT_combAt _ j h)
  · show GlobalTheory.FinPl.CombAt _ (if j < D.R.m then
      (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)) else 0)
    split_ifs with hj
    · refine combAt_smul _ (combAt_aconv _ fun e he => ?_)
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      exact hmono i (dL_combAt _ j (by have := hs i; omega) _ _)
    · exact combAt_zero

end GlobalTheory.QPl.PinComb


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.LevProd.SamePlace

open GlobalTheory.FinPl (Lat latV Moves SplitPt)
open GlobalTheory.IwaPlace (hermAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) {L : Lat V}

theorem half_mem (hL : IntIn q V F L) {g : GA D V} (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y)
    {y : Fin V.rank → Formalism.L2.Theta.AE D} (hy : y ∈ latV V L (· = q.v)) :
    q.e • (Formalism.L2.Theta.mt V g *ᵥ y) ∈ latV V L (· = q.v) := by
  have he : finPart D q.e ∈ intAE D := by
    rw [← GlobalTheory.FinPl.LatIndHalf.sec_one]; exact (q.int_iff 1).1 (one_mem _)
  have h2 : (Formalism.L2.Theta.mt V g).map q.pr = F.β * (GlobalTheory.LevIdx.locHom q V F g).val * F.γ :=
    (GlobalTheory.LevIdx.eq_locHom_iff q V F g _).2 rfl
  have e : q.e • (Formalism.L2.Theta.mt V g *ᵥ y) =
      fun i => q.sec ((F.β *ᵥ ((GlobalTheory.LevIdx.locHom q V F g).val *ᵥ (F.γ *ᵥ fun j => q.pr (y j)))) i) := by
    funext i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h2, Pi.smul_apply, smul_eq_mul, ← q.sec_pr]
    exact congrArg q.sec (RingHom.map_mulVec q.pr _ y i)
  rw [e]
  refine (hL _).1 (GlobalTheory.LocGl.mulVec_int ((GlobalTheory.LocGl.mem_KO_iff _).1 hg).1 ((hL _).2 ?_))
  rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
  simpa only [q.sec_pr] using GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he hy

theorem act_mem (hsd : IsSelfDualC V L) (hL : IntIn q V F L) {g : GA D V} (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y)
    {y : Fin V.rank → Formalism.L2.Theta.AE D} (hy : y ∈ latV V L (· = q.v)) :
    Formalism.L2.Theta.mt V g *ᵥ y ∈ latV V L (· = q.v) := by
  obtain ⟨s1, -, s2⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L q.v hsd
  have hs := GlobalTheory.IwaPlace.mulVec_mem_idAt (Formalism.L2.Theta.mt V g) (s1 y hy)
  have e : Formalism.L2.Theta.mt V g *ᵥ y =
      q.e • (Formalism.L2.Theta.mt V g *ᵥ y) + cA D q.e • (Formalism.L2.Theta.mt V g *ᵥ y) := by
    rw [← add_smul, GlobalTheory.LocGl.idem_eq]
    exact funext fun i => ((GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hs i)).symm
  have hg' : GlobalTheory.LevIdx.locHom q V F g⁻¹ ∈ KO k Y := by rw [map_inv]; exact inv_mem hg
  rw [e]
  refine add_mem (half_mem q F hL hg hy) ((s2 _ fun i => Ideal.mul_mem_left _ _ (hs i)).2 fun x hx => ?_)
  have e2 : q.e • x = Formalism.L2.Theta.mt V g *ᵥ (q.e • (Formalism.L2.Theta.mt V g⁻¹ *ᵥ x)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, mul_inv_cancel,
      GlobalTheory.MixModel.mt_one, Matrix.one_mulVec]
  change hermAt V (cA D q.e • (Formalism.L2.Theta.mt V g *ᵥ y)) x ∈ _
  rw [GlobalTheory.LocGl.hermAt_smul, e2, GlobalTheory.LocGl.hermAt_unitary]
  exact (s2 y (s1 y hy)).1 hy _ (half_mem q F hL hg' hx)

theorem moves_of_mem_KO (hsd : IsSelfDualC V L) (hL : IntIn q V F L) {g : GA D V}
    (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y) : Moves V g L L (· = q.v) := by
  refine fun y _ => ⟨act_mem q F hsd hL hg, fun hy => ?_⟩
  have := act_mem q F hsd hL (g := g⁻¹) (by rw [map_inv]; exact inv_mem hg) hy
  rwa [Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mulVec] at this


end GlobalTheory.LevProd.SamePlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeFinal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.LevProd.OffTwist

theorem entry_mem_of_stab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) (L : Submodule (𝓞 E) (Fin n → E))
    (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ s, (Pi.single s (T : E) : Fin n → E) ∈ L)
    {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ Formalism.UG.levelVL σ J v L) (r s : Fin n) :
    g.val r s ∈ intV E v := by
  replace hg : g ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L) := hg.2
  have hle : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L, ∀ j, y j ∈ intV E v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      intro j
      obtain ⟨c, hc⟩ := h1 x hx j
      refine Subring.subset_closure (Or.inl ⟨⟨x j, c, hc.symm⟩, rfl⟩)
    | zero => intro j; exact zero_mem _
    | add x y _ _ hx hy => intro j; exact add_mem (hx j) (hy j)
    | smul c x _ hx => intro j; exact mul_mem c.2 (hx j)
  have hv : Valued.v ((T : ℕ) : v.adicCompletion F) = 1 := by
    have e : ((T : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (T : 𝓞 F)) := by
      simp
    rw [e]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hT
  have hne : ((T : ℕ) : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact zero_ne_one hv
  have hinv : ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have hc : (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨_, hinv⟩, rfl⟩)
  have hmem : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s (T : E) : Fin n → E) i)) ∈
      Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L := Submodule.subset_span ⟨_, h2 s, rfl⟩
  have h3 := hle _ ((hg _).1 hmem) r
  have e3 : (g.val *ᵥ fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s (T : E) : Fin n → E) i)) r =
      g.val r s * (T : ℕ) := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [e3] at h3
  have e4 : ((T : ℕ) : E ⊗[F] v.adicCompletion F) * ((1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹) = 1 := by
    have : ((T : ℕ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F) :=
      (map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)) T).symm
    rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hne]
    rfl
  have h4 := mul_mem h3 hc
  rwa [mul_assoc, e4, mul_one] at h4

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prV_toEAf (v : GlobalTheory.FinPl.Pl D) (x : AE D) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D x) =
      Algebra.TensorProduct.comm D.host.F _ _ (GlobalTheory.FinPl.compAt D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero, map_zero]
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, map_add (f := _)]

theorem pr_eq_zero (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (hx : Formalism.UG.prV (E := D.host.E) q.v (toEAf D x) = 0) : q.pr x = 0 := by
  rw [prV_toEAf, map_eq_zero_iff _ (AlgEquiv.injective _)] at hx
  have h1 : GlobalTheory.FinPlLoc.idem D (· = q.v) * x = 0 := by
    rw [← GlobalTheory.FinPlLoc.mem_idOff_iff]
    refine (Submodule.mem_iInf _).2 ?_
    rintro ⟨w, rfl⟩
    exact RingHom.mem_ker.2 hx
  have he := (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.e_mem_idAt q)
  have h2 : q.sec (q.pr x) = 0 := by
    rw [q.sec_pr, ← he, mul_comm (GlobalTheory.FinPlLoc.idem D _), mul_assoc, h1, mul_zero]
  rw [← q.pr_sec (q.pr x), h2, map_zero]


set_option maxHeartbeats 1600000 in
theorem exists_int_lift (v : GlobalTheory.FinPl.Pl D) (y : D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) (hy : y ∈ intV D.host.E v) :
    ∃ x : AE D, finPart D x ∈ intAE D ∧ Formalism.UG.prV (E := D.host.E) v (toEAf D x) = y := by
  have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  induction hy using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨c, rfl⟩
    · refine ⟨(1 : AF D.host.F) ⊗ₜ (c : D.host.E), AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩, rfl⟩
    · let α : Af D.host.F := RestrictedProduct.mk (Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F)
        (Filter.Eventually.of_forall fun w => by
          by_cases h : w = v
          · subst h; rw [Pi.single_eq_same]; exact c.2
          · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
      have hα : α ∈ intAf D.host.F := fun w => by
        show (Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F) w ∈ _
        by_cases h : w = v
        · subst h; rw [Pi.single_eq_same]; exact c.2
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      refine ⟨pairA D.host.F 0 α ⊗ₜ (1 : D.host.E), ?_, ?_⟩
      · rw [GlobalTheory.FinPlLoc.finPart_pair]
        exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩
      · rw [prV_toEAf, GlobalTheory.FinPlLoc.compAt_pair, Algebra.TensorProduct.comm_tmul]
        show (1 : D.host.E) ⊗ₜ[D.host.F] ((Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F) v) = _
        rw [Pi.single_eq_same]
  | zero => exact ⟨0, by rw [RingHom.map_zero]; exact zero_mem _, by rw [RingHom.map_zero, RingHom.map_zero]⟩
  | one =>
    refine ⟨1, ?_, by rw [RingHom.map_one, RingHom.map_one]⟩
    rw [RingHom.map_one, Algebra.TensorProduct.one_def]
    exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, by rw [RingHom.map_add (f := _)]; exact add_mem hx hy, by rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]⟩
  | neg a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨-x, by rw [RingHom.map_neg]; exact neg_mem hx, by rw [RingHom.map_neg, RingHom.map_neg]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x * y, by rw [RingHom.map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE hx hy, by rw [RingHom.map_mul, RingHom.map_mul]⟩

theorem pr_mem_int (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (hx : Formalism.UG.prV (E := D.host.E) q.v (toEAf D x) ∈ intV D.host.E q.v) :
    q.pr x ∈ 𝒪[k] := by
  obtain ⟨x', h1, h2⟩ := exists_int_lift q.v _ hx
  have h3 : q.pr (x - x') = 0 := pr_eq_zero q _ (by rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self])
  rw [RingHom.map_sub, sub_eq_zero] at h3
  rw [h3, q.int_iff, q.sec_pr, RingHom.map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE ?_ h1
  have := (q.int_iff 1).1 (one_mem _)
  rwa [← map_one q.pr, q.sec_pr, mul_one] at this

theorem conj_int {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] {pos : Y → ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (hF : IsStdFr pos F)
    (M : Matrix (Fin N) (Fin N) k) (hM : ∀ r s, M r s ∈ 𝒪[k]) (a b : Y) : (F.γ * M * F.β) a b ∈ 𝒪[k] := by
  obtain ⟨e, -, he⟩ := hF
  have hγ : F.γ = (1 : Matrix (Fin N) (Fin N) k).submatrix e id := by
    have h1 : (1 : Matrix (Fin N) (Fin N) k).submatrix e id * F.β = 1 := by
      rw [he, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one, Matrix.submatrix_one_equiv]
    rw [← Matrix.one_mul F.γ, ← h1, Matrix.mul_assoc, F.βγ, Matrix.mul_one]
  have h : F.γ * M * F.β = M.submatrix e e := by
    rw [hγ, he]
    conv_lhs => rw [← Matrix.submatrix_id_id M]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.one_mul, Matrix.mul_one]
  rw [h]
  exact hM _ _

theorem locHom_mem_KO (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) {n : ℕ} (hn : S.rank = n) {Y : Type} [Fintype Y] [DecidableEq Y]
    {pos : Y → ℕ} (F : GlobalTheory.LocMod.Frame k S.rank Y) (hF : IsStdFr pos F) (T : ℕ) (hT : (T : 𝓞 D.host.F) ∉ q.v.asIdeal)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (h2 : ∀ s, (Pi.single s (T : D.host.E) : Fin n → D.host.E) ∈ L) {σ : D.host.E →ₐ[D.host.F] D.host.E}
    {J : Matrix (Fin n) (Fin n) D.host.E} (U : Subgroup (GA D S))
    (hU : ∀ g ∈ U, ∃ κ : GL (Fin n) (EF D), κ.val = finM S hn g ∧ Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) q.v) κ ∈
      Formalism.UG.levelVL σ J q.v L) :
    ∀ g ∈ U, GlobalTheory.LevIdx.locHom q S F g ∈ KO k Y := by
  subst hn
  have key : ∀ g ∈ U, ∀ a b, (GlobalTheory.LevIdx.locHom q S F g).val a b ∈ 𝒪[k] := by
    intro g hg
    obtain ⟨κ, hκ, hs⟩ := hU g hg
    refine conj_int F hF _ fun r s => ?_
    have h := entry_mem_of_stab q.v T hT L h1 h2 _ hs r s
    have e : (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) q.v) κ).val r s =
        Formalism.UG.prV (E := D.host.E) q.v (toEAf D (mt S g r s)) := by
      show Formalism.UG.prV (E := D.host.E) q.v (κ.val r s) = _
      rw [hκ]; rfl
    rw [e] at h
    exact pr_mem_int q _ h
  intro g hg
  rw [GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv]
  exact ⟨key g hg, key _ (inv_mem hg)⟩

end GlobalTheory.LevProd.OffTwist

end
end

