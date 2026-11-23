module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianPairingOntoInverseIdealAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeeSaw.HzOnto

open GlobalTheory.IwaPlace

variable {D : D7}

def pz (S : HSp D) (z x : Fin S.rank → D.host.E) : D.host.E := ∑ i, ∑ j, star (x i) * S.gram i j * z j

theorem pz_add (S : HSp D) (z x y : Fin S.rank → D.host.E) : pz S z (x + y) = pz S z x + pz S z y := by
  simp only [pz, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem pz_smul (S : HSp D) (z x : Fin S.rank → D.host.E) (c : D.host.E) :
    pz S z (c • x) = star c * pz S z x := by
  simp only [pz, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def valSub (S : HSp D) (M : Lat S) (z : Fin S.rank → D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {a | ∃ x ∈ M, pz S z x = a}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, M.add_mem hx hy, pz_add S z x y⟩
  zero_mem' := ⟨0, M.zero_mem, by simp [pz]⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨c', hc'⟩ := GlobalTheory.FinPl.LatMem.star_int c
    refine ⟨c' • x, M.smul_mem c' hx, ?_⟩
    have e : (c' • x : Fin S.rank → D.host.E) = (c' : D.host.E) • x := by
      funext i; exact (algebraMap_smul D.host.E c' (x i)).symm
    rw [e, pz_smul, hc', star_star, Algebra.smul_def]

theorem valSub_isFractional (S : HSp D) (M : Lat S) (hM : IsSelfDualC S M) (z : Fin S.rank → D.host.E) :
    IsFractional (𝓞 D.host.E)⁰ (valSub S M z) := by
  obtain ⟨s, hs⟩ := hM.1.fg
  apply FractionalIdeal.isFractional_of_fg
  let N : Submodule (𝓞 D.host.E) D.host.E := Submodule.span _ (pz S z '' (s : Set _))
  have hle : valSub S M z ≤ N := by
    rintro a ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span (𝓞 D.host.E) (s : Set _) := by rw [hs]; exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simpa [pz] using N.zero_mem
    | add x y hx hy ihx ihy => simpa only [pz_add] using N.add_mem ihx ihy
    | smul c x hx ih =>
      obtain ⟨c', hc'⟩ := GlobalTheory.FinPl.LatMem.star_int c
      have e : (c • x : Fin S.rank → D.host.E) = (c : D.host.E) • x := by
        funext i; exact (algebraMap_smul D.host.E c (x i)).symm
      have hc : star (c : D.host.E) = (c' : D.host.E) := hc'.symm
      rw [e, pz_smul, hc, ← Algebra.smul_def]
      exact N.smul_mem c' ih
  exact (Submodule.fg_span (s.finite_toSet.image (pz S z))).of_le hle

def valIdl (S : HSp D) (M : Lat S) (hM : IsSelfDualC S M) (z : Fin S.rank → D.host.E) : FI D :=
  ⟨valSub S M z, valSub_isFractional S M hM z⟩

theorem mem_valIdl {S : HSp D} {M : Lat S} {hM : IsSelfDualC S M} {z : Fin S.rank → D.host.E} {a : D.host.E} :
    a ∈ valIdl S M hM z ↔ ∃ x ∈ M, pz S z x = a := Iff.rfl

theorem hermAt_gen (S : HSp D) (z x : Fin S.rank → D.host.E) (α : Af D.host.F) :
    hermAt S (ratV z) (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] pz S z x := by
  simp only [hermAt, pz, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change (pairA D.host.F 0 α ⊗ₜ[D.host.F] star (1 * x i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram i j) *
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] z j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]

theorem hermAt_add (S : HSp D) (w x y : Fin S.rank → AE D) : hermAt S w (x + y) = hermAt S w x + hermAt S w y := by
  simp only [hermAt, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hermAt_zero (S : HSp D) (w : Fin S.rank → AE D) : hermAt S w 0 = 0 := by
  simp [hermAt]

theorem hermAt_neg (S : HSp D) (w x : Fin S.rank → AE D) : hermAt S w (-x) = -hermAt S w x := by
  simp [hermAt, Finset.sum_neg_distrib]

theorem cA_sum_eq (S : HSp D) (Z y : Fin S.rank → AE D) :
    cA D (∑ l, (∑ m, cA D (Z m) * gA S m l) * y l) = hermAt S Z y := by
  have hg : ∀ m l, cA D (gA S m l) = gA S l m := fun m l => congrFun (congrFun (adj_gA S) l) m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, cA_cA, hermAt, Finset.sum_mul, hg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_not_intAt (v : Pl D) : ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := _root_.GlobalTheory.FinPl.NotIntAt.exists_not_intAt D v

theorem exists_not_mem_idV (v : Pl D) {𝔠 : FI D} (h : 𝔠 ≠ 0) : ∃ t ∈ idAt D (· = v), t ∉ idV 𝔠 v := by
  obtain ⟨x, hx, hg⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠 h
  obtain ⟨u, hu, hnu⟩ := exists_not_intAt (D := D) v
  have ht : incA D x * u ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hu
  refine ⟨incA D x * u, ht, fun hm => hnu ?_⟩
  have := ((hg _).1 hm).1
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

theorem hz_onto : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ g ∈ idV 𝔠⁻¹ v, ∃ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) = g := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hL h𝔠 g hg
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hSD := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M v hM
  set z := vecB o ζ with hzdef
  set 𝔦 : FI D := valIdl S M hM z with h𝔦def
  have hval : ∀ x ∈ latV S M (· = v), hermAt S (ratV z) x ∈ idV 𝔦 v := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, m, hm, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hermAt_gen]
      exact AddSubgroup.subset_closure ⟨α, hαi, hα, _, mem_valIdl.2 ⟨m, hm, rfl⟩, rfl⟩
    | zero => rw [hermAt_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hermAt_add]; exact add_mem hx hy
    | neg x _ hx => rw [hermAt_neg]; exact neg_mem hx
  have hkey : ∀ t ∈ idAt D (· = v),
      t ∈ idV 𝔠 v ↔ ∀ x ∈ latV S M (· = v), t * hermAt S (ratV z) x ∈ intAt D (· = v) := by
    intro t ht
    rw [← hL t ht, hSD.2.2 (t • ratV z) (fun i => Ideal.mul_mem_right _ _ ht)]
    simp only [GlobalTheory.IwaPlace.SDStable.hermAt_smul_left]
  have h𝔦 : 𝔦 ≠ 0 := by
    intro h0
    obtain ⟨t, ht, htn⟩ := exists_not_mem_idV v h𝔠
    refine htn ((hkey t ht).2 fun x hx => ?_)
    have := hval x hx
    rw [h0, idV_zero, AddSubgroup.mem_bot] at this
    rw [this, mul_zero]
    exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  have hsub : ∀ a ∈ idV 𝔦⁻¹ v, a ∈ idV 𝔠 v := by
    intro a ha
    have haA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ a ha
    refine (hkey a haA).2 fun x hx => ?_
    have e := (h2 𝔦 1 h𝔦 one_ne_zero a haA).2 (by rwa [one_mul])
    exact (h1 _).1 (e _ (hval x hx))
  have hgA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ g hg
  have hg' : g ∈ idV 𝔦 v := by
    have e := (h2 𝔦⁻¹ 1 (inv_ne_zero h𝔦) one_ne_zero g hgA).1 fun a ha =>
      (h2 𝔠 1 h𝔠 one_ne_zero g hgA).2 (by rwa [one_mul]) a (hsub a ha)
    rwa [one_mul, inv_inv] at e
  have honto : ∀ b ∈ idV 𝔦 v, ∃ y ∈ latV S M (· = v), hermAt S (ratV z) y = b := by
    intro b hb
    induction hb using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hw
      obtain ⟨m, hm, rfl⟩ := mem_valIdl.1 ha
      exact ⟨_, AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, m, hm, rfl⟩, hermAt_gen S z m α⟩
    | zero => exact ⟨0, zero_mem _, hermAt_zero S _⟩
    | add b b' _ _ hb hb' =>
      obtain ⟨y, hy, e⟩ := hb
      obtain ⟨y', hy', e'⟩ := hb'
      exact ⟨y + y', add_mem hy hy', by rw [hermAt_add, e, e']⟩
    | neg b _ hb =>
      obtain ⟨y, hy, e⟩ := hb
      exact ⟨-y, neg_mem hy, by rw [hermAt_neg, e]⟩
  obtain ⟨y, hy, e⟩ := honto g hg'
  exact ⟨y, hy, by rw [cA_sum_eq, e]⟩

end GlobalTheory.SeeSaw.HzOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvHaarVolumeToRealEqRelIndexIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped ENNReal

namespace GlobalTheory.HaarIdx

open MeasureTheory

theorem inv_toReal_eq_relIndex {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ] (μ : Measure Γ) [μ.IsMulLeftInvariant]
    (K H : Subgroup Γ) (hHK : H ≤ K) (hH : MeasurableSet (H : Set Γ)) (hK : μ (K : Set Γ) = 1)
    (hn : H.relIndex K ≠ 0) : ((μ (H : Set Γ)).toReal)⁻¹ = (H.relIndex K : ℝ) := by
  have hmeas : ∀ g : Γ, AEMeasurable (fun x => g * x) μ :=
    fun g => (measurable_const_mul g).aemeasurable
  have hpre : ∀ g : Γ, μ ((fun x => g * x) ⁻¹' (H : Set Γ)) = μ H := by
    intro g
    rw [← Measure.map_apply_of_aemeasurable (hmeas g) hH, map_mul_left_eq_self μ g]
  set L := H.subgroupOf K
  haveI : L.FiniteIndex := ⟨hn⟩
  haveI : Fintype (K ⧸ L) := Fintype.ofFinite _
  let C : (K ⧸ L) → Set Γ := fun q => (fun x => ((q.out : K) : Γ)⁻¹ * x) ⁻¹' (H : Set Γ)
  have hcov : (K : Set Γ) = ⋃ q, C q := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, C]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : K) : K ⧸ L), ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L (⟨x, hx⟩ : K)
      rw [hh]
      have : (((⟨x, hx⟩ : K) * (h : K) : K) : Γ)⁻¹ * x = ((h : K) : Γ)⁻¹ := by
        simp [_root_.mul_inv_rev, mul_assoc]
      rw [this]
      exact H.inv_mem (Subgroup.mem_subgroupOf.mp h.2)
    · rintro ⟨q, hq⟩
      have h1 : ((q.out : K) : Γ)⁻¹ * x ∈ K := hHK hq
      have h2 : ((q.out : K) : Γ) ∈ K := (q.out : K).2
      have := K.mul_mem h2 h1
      simpa [mul_assoc] using this
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) C) := by
    intro q q' hqq'
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro y hy hy'
    simp only [Set.mem_preimage, SetLike.mem_coe, C] at hy hy'
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change (QuotientGroup.mk q.out : K ⧸ L) = QuotientGroup.mk q'.out
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := H.mul_mem hy (H.inv_mem hy')
    simpa [_root_.mul_inv_rev, mul_assoc] using this
  have hnull : ∀ q, NullMeasurableSet (C q) μ := fun q =>
    (hmeas _).nullMeasurableSet_preimage hH
  have hsum : μ (K : Set Γ) = (Fintype.card (K ⧸ L) : ℝ≥0∞) * μ H := by
    rw [hcov, measure_iUnion₀ hdisj hnull, tsum_fintype]
    simp [C, hpre, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ L) : ℕ) = H.relIndex K := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hK, hcard] at hsum
  have hne : μ (H : Set Γ) ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by exact_mod_cast hn)] at hsum; exact ENNReal.one_ne_top hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hr
  have hpos : (μ (H : Set Γ)).toReal ≠ 0 := by
    intro h; rw [h, mul_zero] at hr; exact one_ne_zero hr
  field_simp
  linarith [hr]

end GlobalTheory.HaarIdx

namespace GlobalTheory


theorem QTw.QExt.m_inv_toReal_eq_relIndex : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GlobalTheory.QTw.QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : GlobalTheory.QTw.QExt G χ) (j : ℕ) (H : Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)), H ≤ KO G.k _ → MeasurableSet (H : Set (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)) → H.relIndex (KO G.k _) ≠ 0 → ((((E.m j H).toReal)⁻¹ : ℝ) : ℂ) = (H.relIndex (KO G.k _) : ℂ) := by
  intro D c v B PP G χ E j H hHK hH hn
  letI : MeasurableSpace (Matrix (XIx (Fin D.R.k) (Fin D.R.t) j) (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := Formalism.DoubleCosetMeasures.instMeasMat
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := G.k)
  haveI : BorelSpace (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : MeasurableMul (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := ⟨
    fun g => (continuous_const.mul continuous_id).measurable,
    fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI := (E.haar j).1
  rw [HaarIdx.inv_toReal_eq_relIndex (E.m j) _ H hHK hH (E.haar j).2 hn]
  push_cast
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelProdHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfProd

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm GlobalTheory.ExportSeries

variable {D : D7}

def prodHalf {m n : ℕ} (a b : AE D) (Ψ : Mx D m n → ℂ) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a • x) * Ψ (b • x) * (if IsHalf (a + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem prodHalf_apply {m n : ℕ} (a b : AE D) (Ψ Φ : Mx D m n → ℂ) (x : Mx D m n) :
    prodHalf a b Ψ Φ x = Φ (a • x) * Ψ (b • x) * (if IsHalf (a + b) x then 1 else 0) := rfl

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (d : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
  ∑ u ∈ d.support, d u • GlobalTheory.PlaceModel.heisL S T ψ u

theorem combL_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (d : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    combL ψ S T d f = comb ψ S T d f := by
  simp only [combL, comb, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

end GlobalTheory.HalfProd

namespace GlobalTheory.HalfProd

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm GlobalTheory.ExportSeries GlobalTheory.ExportSeries.RestrictHalfModel

variable {D : D7}

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem isSBHalf_prodHalf {m n : ℕ} {a b : AE D} (ha : a * a = a) (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Ψ Φ : Mx D m n → ℂ} (hΨ : IsSBHalf b Λ Ψ)
    (hΦ : IsSBHalf a Λ Φ) : IsSBHalf (a + b) Λ (prodHalf a b Ψ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  obtain ⟨-, k', hk', hinv', hlat'⟩ := hΨ
  refine ⟨fun t ht => ?_, k * k', Nat.mul_pos hk hk', fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [prodHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [prodHalf_apply]
    have e1 : a • (t + (k * k') • u) = a • t + k • (k' • (a • u)) := by
      rw [smul_add, mul_smul, smul_comm a k (k' • u), smul_comm a k' u]
    have e2 : b • (t + (k * k') • u) = b • t + k' • (k • (b • u)) := by
      rw [smul_add, mul_comm, mul_smul, smul_comm b k' (k • u), smul_comm b k u]
    have e3 : (a + b) • ((k * k') • u) = (k * k') • u := by rw [smul_comm, hhu]
    have ha' : IsHalf a (k' • (a • u)) := (isHalf_iff' _ _).2 (by rw [smul_comm, smul_smul, ha])
    have hb' : IsHalf b (k • (b • u)) := (isHalf_iff' _ _).2 (by rw [smul_comm, smul_smul, hb])
    rw [e1, e2, hinv _ (Λ.nsmul_mem (hΛ a ha u hu) k') ha', hinv' _ (Λ.nsmul_mem (hΛ b hb u hu) k) hb']
    simp only [isHalf_add_iff e3]
  · rw [prodHalf_apply] at ht
    have h1 : Φ (a • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : Ψ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (hlat _ h1) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (hlat' _ h2) k

theorem isPlaceModel_prodHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ}
    {a b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {Ψ : WO S T → ℂ} (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) (hΨ : IsSBHalf b Λ Ψ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 (T₀ (prodHalf a b Ψ (halfInd a Λ))) (T₀ ∘ₗ prodHalf a b Ψ) := by
  have hsb : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf (a + b) Λ (prodHalf a b Ψ Φ) :=
    fun Φ hΦ => isSBHalf_prodHalf ha hb hΛ hΨ hΦ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have e : prodHalf a b Ψ (fun t => Φ (t + x)) = fun t => prodHalf a b Ψ Φ (t + x) := by
      funext z
      simp only [prodHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x ((isHalf_iff' _ _).2 hax)
  · have hy' : IsHalf (cA D (a + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add (f := _), add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : prodHalf a b Ψ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * prodHalf a b Ψ Φ t := by
      funext z
      simp only [prodHalf_apply]
      rw [GlobalTheory.PlaceModel.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, one_smul]

theorem placeModel_eq {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : e * e = e) (hinf : infPart D e = 0)
    {f₁ : WO S T → ℂ} {T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₁ T₁)
    (h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₁ T₂)
    {Φ : WO S T → ℂ}
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ) :
    T₁ Φ = T₂ Φ := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  exact placeModel_unique_of_dual ψ _ hLL' hX hfin' hden h₁ h₂ hΦ

end GlobalTheory.HalfProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiveChartsKernelEqClassSumJetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liveCharts_kernel_eq_classSum_jets : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  first | exact @GlobalTheory.AdForm.ClsKLive.kval | exact GlobalTheory.AdForm.ClsKLive.kval | (intros; apply GlobalTheory.AdForm.ClsKLive.kval <;> assumption)
end

