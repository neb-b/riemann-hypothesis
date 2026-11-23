module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues
open Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped commutatorElement
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem rec_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) (x : IrrGL (k := w.adicCompletion E))
    (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) : rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨a, ha, H⟩ := H
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified Pr.exh Pr.multi Pr.cos Pr.zel GlobalTheory.RecT.geometricLemma_holds Pr.bz (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← SatakeLaw.sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _
private theorem rec_algNorm_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  refine ⟨α, hαB.symm, ?_⟩
  have φ := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    rec_diag H (IrrGL.of σ.ρ σ.smooth σ.irred) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
  obtain ⟨a, ha, L⟩ := H
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
private theorem gd_diag {n : ℕ} (c : Fin n → ℂˣ) : Z.Win.Gd (WD.mk (WDRep.diag h c)) := by
  refine ⟨fun s t => ?_, WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))⟩
  have hd : deg (⁅s, t⁆ : Weil h) = 0 := by
    rw [commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]
    ring
  show WD.charPol _ _ = _
  rw [WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd]
  simp
private theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring
end UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues
open UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues in
theorem UpperTheory.V.Z.Desc.W.satFrobT_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    (∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRecT h rc → Z.Win.WDT ι r (rc (algNorm σ))) →
    FrobEig ι r w (algSat n (normV w) B) := by
  intro _ F Ω _ _ _ _ _ l _ ι n r _ w hl σ B hB H A h
  obtain ⟨rc, hrec⟩ := recTExists F Ω A w h
  obtain ⟨α, rfl, e⟩ := rec_algNorm_diag hrec σ B hB
  have hx := (H A h rc hrec).isWDOf (e ▸ gd_diag _)
  have hw := (hx.wdOf_eq hl).trans e
  obtain ⟨t, ht, φ, hφ, N', a, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw, WD.unr_mk]; exact WDRep.unr_diag _), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd] at this
  refine this.symm.trans ?_
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Win UpperTheory.GalN.V
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
end Loc
section
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
theorem AdInW.toIn_alt {ι : Qbar l ≃+* ℂ} {M m : ℕ} {r : G L Ω →* GL (Fin 2) (Qbar l)} (h : AdInW ι M m r) : _root_.UpperTheory.V.Z.Sym.AdInAlt ι M m r :=
  ⟨h.cont, _root_.UpperTheory.V.Z.Win.Birth.mkCsdW' h.aut fun _ => h.wit, h.irr, h.gap, h.unr, h.away, h.above⟩
end
structure PureWeightCompatibility : Prop where
  af : _root_.UpperTheory.V.Af.Hypotheses'
  gal : GalUnitaryT
  compat : CompatT
  same : Z.Desc.W.Same
  plain : PlainRec
  desc : Z.Desc.DescUse
def PlainOfAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L)))
    (ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    (∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1) → PT τ
def PsOfAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L))), PT τ →
    ∃ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      ∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1
def EigWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G L Ω →* GL (Fin n) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∀ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    ∀ s : Weil h, (r (s : G L Ω)).val.charpoly.map ι.toRingHom =
      psPol ψ (a s)
def AboveWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → ∀ m : ℕ, 2 ≤ m →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ HT, HasHTAt r HT w → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    (∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    (∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)) ∧
      ∃ b : ℤ, ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = {b, b + m}
def AwayWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → Unlinked (ad0 r) →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)
def GoodWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := L) A, r s = 1) → (∃ s, Ga.FrobAt w s ∧ s ∉ Ga.Bad r) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) ∧ Reg (ψ 0 / ψ 1)
def LocSubDAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Sig.Lev k)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
    GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ (V.J n) →
    (∀ d, Sig.SDom d → Hi.dc τ (V.J n) (V.J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ)
def GalExWAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ n : ℕ, 1 ≤ n → ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ∃ r : G L Ω →* GL (Fin n) (Qbar l), GalT ι σ r ∧
      (IsIrr r → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π ∧ Lifts σ π)
def AboveWeightAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ M m : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M → ∀ r : G L Ω →* GL (Fin 2) (Qbar l), AdInW ι M m r →
    ∃ (σ : Submodule ℂ (UA L 2 → ℂ)) (HT : (L →+* Qbar l) → Multiset ℤ), IsAutRepU σ ∧ GalT ι σ r ∧
      (∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → PT τ ∧ HasHTAt r HT w) ∧ (∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → IsUnramU σ w) ∧
      ∀ v : InfinitePlace L, ∃ lam, HasWeightAt σ v.embedding lam ∧ lam.w 0 - lam.w 1 = ((m - 1 : ℕ) : ℤ)
def Branch1WAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ₃ : Submodule ℂ (UA L 3 → ℂ), IsAutRepU σ₃ → (∀ᶠ w in Filter.cofinite, w ∈ P → CompSub σ₃ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) →
    ∃ π : CuspSub L 3, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι (tw (ad0 r) (cycBar L Ω l)⁻¹) π ∧ Lifts σ₃ π
def Branch2WAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ' : Submodule ℂ (UA L 2 → ℂ), IsAutRepU σ' →
    (∀ᶠ w in Filter.cofinite, w ∈ P → ∃ ψ', CompSub σ' w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2) → False
def PlainAtWAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (σ : Submodule ℂ (UA L 3 → ℂ)) (π : CuspSub L 3), IsAutRepU σ →
    Lifts σ π → ∀ w, IsSplitAt w → ∀ a : (Kw w)ˣ →* ℂˣ, NoLk a → CompSub σ w ![a, 1, a⁻¹] → ∀ τ, π.IsLocComp w τ → PT τ
end UpperTheory.V.Z.Sym.W
end
end
end

