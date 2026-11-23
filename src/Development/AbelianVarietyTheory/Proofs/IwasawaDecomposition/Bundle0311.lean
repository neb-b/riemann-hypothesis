module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Formalism.LocalToGlobal.UnitaryNorms.UnramT
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetAutWdTieLabConj
section
noncomputable section

namespace GlobalTheory.HeightCounting.TrueConjLabels

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne Pointwise

section General

variable {Ω : Type} [Field Ω]

theorem val_lt_iff {A B : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ x, x ∈ A ↔ c x ∈ B) (y : Ω) :
    B.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc, map_eq_zero_iff _ c.injective]

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem exists_transport_elt (s : E ≃+* E) (c : Ω ≃+* Ω) (hs : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (t : G E Ω) : ∃ γ : G E Ω, ∀ x, γ (c x) = c (t x) := by
  refine ⟨{ (c.symm.trans (t.toRingEquiv.trans c)) with commutes' := fun y => ?_ }, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective y
    show c (t (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, t.commutes]
  · show c (t (c.symm (c x))) = _
    rw [c.symm_apply_apply]

end General

section Host

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def conjInt (H : Host R) : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem coe_conjInt (x : 𝓞 H.E) : ((conjInt H x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := rfl

theorem isConjPl_iff {w w' : PlE H} : IsConjPl H w w' ↔ ∀ x, x ∈ w.asIdeal ↔ conjInt H x ∈ w'.asIdeal := by
  refine ⟨fun h x => h x _ (coe_conjInt x), fun h x y hy => ?_⟩
  have : y = conjInt H x := RingOfIntegers.ext (hy.trans (coe_conjInt x).symm)
  rw [this]; exact h x

theorem eq_of_isConjPl {w₀ w₁ w : PlE H} (h₀ : IsConjPl H w₀ w) (h₁ : IsConjPl H w₁ w) : w₀ = w₁ := by
  apply HeightOneSpectrum.ext
  ext x
  rw [isConjPl_iff.1 h₀, isConjPl_iff.1 h₁]

theorem exists_ext (N : NData R H what₂) {w₀ w : PlE H} (h : IsConjPl H w₀ w) : ∃ c : N.Om ≃+* N.Om,
    (∀ x : H.E, c (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x)) ∧
    ∀ x, x ∈ N.plOm.1 w₀ ↔ c x ∈ N.plOm.1 w := by
  let c₀ : N.Om ≃+* N.Om := IsAlgClosure.equivOfEquiv N.Om N.Om H.conj.toRingEquiv
  have h₀ : ∀ x : H.E, c₀ (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x) := fun x =>
    IsAlgClosure.equivOfEquiv_algebraMap N.Om N.Om H.conj.toRingEquiv x
  let B : ValuationSubring N.Om := (N.plOm.1 w₀).comap c₀.symm.toRingHom
  have hB : ∀ x, x ∈ N.plOm.1 w₀ ↔ c₀ x ∈ B := fun x => by
    simp [B, ValuationSubring.mem_comap]
  have hBw : IsPlaceOver (F := H.E) B w := fun y => by
    obtain ⟨x, rfl⟩ := (conjInt H).surjective y
    rw [coe_conjInt, ← h₀, val_lt_iff c₀ hB, ← isConjPl_iff.1 h]
    exact N.plOm.2 w₀ x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hBw (N.plOm.2 w)
  refine ⟨c₀.trans σ.toRingEquiv, fun x => ?_, fun x => ?_⟩
  · show σ (c₀ _) = _
    rw [h₀, σ.commutes]
  · show _ ↔ σ (c₀ x) ∈ _
    rw [hB, ← hσ, ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm

end Host

theorem exists_gamma (D : D7) (k : Fin 2) : ∃ γ : PlE D.host → G D.host.E D.nd.Om,
    (∀ v, γ (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ v w, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ w (c x) = c (D.ntypes.tg k v x) := by
  have key : ∀ w : PlE D.host, ∃ γ : G D.host.E D.nd.Om, (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ (c x) = c (D.ntypes.tg k v x) := by
    intro w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, h1, h2⟩ := exists_ext D.nd hv
      obtain ⟨γ, hγ⟩ := exists_transport_elt D.host.conj.toRingEquiv c h1 (D.ntypes.tg k v)
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, hγ⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_, fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  exact ⟨γ, fun v => h1 _ v rfl, fun v w hw => h2 w v hw⟩


set_option maxHeartbeats 1000000 in
theorem exists_labels_true_conj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl,
    (∀ k v, A.plGw k v = D.naut.plGw k v) ∧
    ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut,
      LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧
      ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl),
        (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w := by
  intro D hE Rw
  have hS : ∀ k v, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  let lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)) := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (Rw.par σ (D.naut.plGw k v))
  have h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ⟨WD.lab_monic _ _ _, ((WD.natDegree_lab_eq_iff (hS k v) _).2 (Rw.tame σ k v)).trans (Rw.dim σ _)⟩
  choose γ hγ1 hγ2 using exists_gamma D
  let A : NAut (ndLab D.nd lab h) := nAutWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj
    D.naut.plGw_nconj D.ntypes.teichC γ
  have hA : ∀ k v (a : A.LP (A.plGw k v)), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.items₂ k (A.plGw k v) a = WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (show WDAt D.nd (D.naut.plGw k v) from a) := fun k v a => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact congrArg (fun x => WD.lab (h := D.nd.plOm.2 (D.naut.plGw k v)) (D.ntypes.teichC k) x (show WDAt D.nd (D.naut.plGw k v) from a)) (hγ1 k v)
  have hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod := by
    intro k v L hL
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [hA k v L] at hL ⊢
    exact WD.inePol_eq_of_natDegree_lab _ _ _ hL
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ _ A hE
  refine ⟨lab, h, A, C, D.ntypes.tg_mem, D.ntypes.tg_gen, hl, fun _ _ => rfl,
    wdTieWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj D.ntypes.teichC γ,
    fun k v a => hA k v a, fun k v w hw => ?_, ⟨Rw.par, Rw.sat, fun k σ v => (hA k v _).symm⟩, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c, h1, h2, h3⟩ := hγ2 k v w hw
  exact ⟨c, γ k w, h1, h2, h3, fun _ => rfl⟩

end GlobalTheory.HeightCounting.TrueConjLabels

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_setAut_wdTie_labConj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl, (∀ k v, A.plGw k v = D.naut.plGw k v) ∧ ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut, LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧ ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl), (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w :=
  TrueConjLabels.exists_labels_true_conj

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankBaseRowsIsotypicEqGoodFormsIsotypicStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_baseRows_isotypic_eq_goodForms_isotypic : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → ∀ (i : Fin D.R.m) (π : D.what₂.FT), Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) = Module.finrank ℂ (principalLevelFrame.isotL R.toRealDat.θ (Y.PW i) (R.toRealDat.MW i (sg0 D A3.A)) (levS _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  first | exact @GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL | exact GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL | (intros; apply GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualInfinityInfinitesimalIffFie
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.FrobDense

namespace GlobalTheory.CuspRep.CsdInf

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem star_expU (z : Cinf L) :
    Units.map (starRingEnd (Cinf L)).toMonoidHom (expU z) = expU (star z) :=
  Units.ext (funext fun w => by
    change starRingEnd ℂ (Complex.exp (z w)) = Complex.exp (star (z w))
    rw [← Complex.exp_conj]
    rfl)

theorem lie_iff (χ : HChar L) :
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
      ∀ u : (Cinf L)ˣ, chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  constructor
  · intro h u
    obtain ⟨z, rfl⟩ : ∃ z, expU z = u := ⟨_, expU_log u⟩
    rw [star_expU, ← expU_add]
    apply Units.ext
    have h1 := h z
    rw [map_neg] at h1
    rw [chiInf_expU, map_add (f := _), ← h1, neg_add_cancel, Complex.exp_zero, Units.val_one]
  · intro h z
    have h1 : ∀ t : ℝ, Complex.exp (t * dchi χ (z + star z)) = 1 := fun t => by
      have h2 := h (expU (t • z))
      rw [star_expU, ← expU_add, star_smul, star_trivial, ← smul_add] at h2
      rw [← Complex.real_smul, ← map_smul, ← chiInf_expU, h2, Units.val_one]
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (z + star z))) (dchi χ (z + star z)) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (z + star z))).cexp
    rw [funext h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    rw [map_add (f := _)] at h3
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h3).symm

theorem inf_eq (χ : HChar L) (k : Lˣ) :
    χ.inf k = chiInf χ (Units.map (pInf L).toMonoidHom (diagUnits L k)) := by
  rw [HChar.inf, chiInf, MonoidHom.comp_apply, MonoidHom.comp_apply, NormTriv.infId_pInf, infDiag, MonoidHom.finsetProd_apply]
  rfl

theorem pInf_conj (k : Lˣ) :
    Units.map (pInf L).toMonoidHom (diagUnits L (Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj L)).toMonoidHom k)) =
      Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map (pInf L).toMonoidHom (diagUnits L k)) :=
  Units.ext (pInf_complexConj (k : L))

theorem field_iff (χ : HChar L) :
    (∀ k : Lˣ, χ.inf (Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj L)).toMonoidHom k) = (χ.inf k)⁻¹) ↔
      ∀ u : (Cinf L)ˣ, chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  classical
  constructor
  · intro h u
    let q : Loc (∅ : Finset (HeightOneSpectrum (𝓞 L))) →* Cinf L := (pInf L).toMonoidHom.comp (incl ∅)
    have hq : Continuous q := (continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst) : Continuous fun y w => q y w)
    have h2 : ∀ y, chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1 :=
      fun y => (denseRange_units ∅).induction_on
        (p := fun y => chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1) y
        (isClosed_eq ((continuous_chiInf χ).comp ((hq.units_map _).mul
          ((Continuous.units_map _ continuous_star).comp (hq.units_map _)))) continuous_const) fun k => by
        have e : Units.map q (Units.map (proj ∅) (diagUnits L k)) = Units.map (pInf L).toMonoidHom (diagUnits L k) := rfl
        rw [e, ← pInf_conj, map_mul, ← inf_eq, ← inf_eq, h k, mul_inv_cancel]
    have h3 := h2 (Units.map (proj ∅) (infId L u))
    have e : Units.map q (Units.map (proj ∅) (infId L u)) = u := Units.ext (by
      change (infEq L).symm (1 - infEq L 1 + infEq L u) = u
      simp)
    rwa [e] at h3
  · intro h k
    have h1 := h (Units.map (pInf L).toMonoidHom (diagUnits L k))
    rw [← pInf_conj, map_mul, ← inf_eq, ← inf_eq] at h1
    exact eq_inv_of_mul_eq_one_right h1

end GlobalTheory.CuspRep.CsdInf


open GlobalTheory.CuspRep.CsdInf in
theorem GlobalTheory.CuspRep.csdInf_iff : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H;
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
      ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by
  intro R H χ
  have := host_isCMField H
  have e : ∀ k : H.Eˣ, Units.map (MonoidHomClass.toMonoidHom H.conj) k =
      Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj H.E)).toMonoidHom k :=
    fun k => Units.ext (host_complexConj H k).symm
  show (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹
  simp only [e]
  exact (lie_iff χ).trans (field_iff χ).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSide
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt

variable {D : D7} {u : D.what₂.Word}

theorem exists_intF_of_conj_eq (z : 𝓞 D.host.E) (hz : D.host.conj (z : D.host.E) = z) :
    ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
  have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
  refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
  · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
      (RingOfIntegers.isIntegral_coe z)
  · rfl

theorem pos_iff_mem_Pv (A : AtTTied u) (v : (D.mem u).A.vT) (ν : AddValuation D.host.E (WithTop ℤ))
    (hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
      0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E))
    (hπ : 0 < ν (A.piU : D.host.E)) (y : 𝓞 D.host.E) : 0 < ν (y : D.host.E) ↔ y ∈ A.Pv v := by
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  have hinv := Formalism.L2.Host.conj_conj (D := D) D.host
  have hpb : A.res v (cO A.piU) ≠ 0 := A.res_conj v (cO A.piU) rfl
  have hπb : ν ((cO A.piU : 𝓞 D.host.E) : D.host.E) = 0 := by
    obtain ⟨zF, hzF⟩ := exists_intF_of_conj_eq (D := D) (A.piU + cO A.piU) (by
      push_cast; simp only [hcO, map_add (f := _), hinv]; ring)
    have hnot : zF ∉ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add (f := _), A.res_pi, zero_add]; exact hpb
    rw [hTau, hzF] at hnot
    refine le_antisymm (not_lt.mp fun h => hnot ?_) (Formalism.L2.Host.addVal_nonneg ν _)
    push_cast
    exact lt_of_lt_of_le (lt_min hπ h) (ν.map_add _ _)
  have hpos : ∀ y ∈ A.Pv v, 0 < ν (y : D.host.E) := by
    intro y hy
    have hy' : A.res v y = 0 := hy
    obtain ⟨zF, hzF⟩ := exists_intF_of_conj_eq (D := D) (y * cO A.piU + cO y * A.piU) (by
      push_cast; simp only [hcO, map_add (f := _), map_mul, hinv]; ring)
    have hin : zF ∈ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add (f := _), map_mul, map_mul, hy', A.res_pi]; simp
    rw [hTau, hzF] at hin
    push_cast at hin
    have h2 : 0 < ν (((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) := by
      rw [ν.map_mul]; exact lt_of_lt_of_le hπ (le_add_of_nonneg_left (Formalism.L2.Host.addVal_nonneg ν _))
    have h3 : 0 < ν ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E)) := by
      have : (y : D.host.E) * (cO A.piU : 𝓞 D.host.E) =
          ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E) + ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) -
            ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU := by ring
      rw [this]
      exact lt_of_lt_of_le (lt_min hin h2) (ν.map_sub _ _)
    rwa [ν.map_mul, hπb, add_zero] at h3
  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  refine ⟨fun h => ?_, hpos y⟩
  by_contra hy
  rw [Formalism.L2.Host.addVal_eq_zero_of_not_mem ν (A.Pv v) hPmax hpos y hy] at h
  exact lt_irrefl _ h

theorem mem_conjIdeal_Pv (P : Ideal (𝓞 D.host.E)) (x y : 𝓞 D.host.E) (hxy : (y : D.host.E) = D.host.conj (x : D.host.E)) :
    x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P ↔ y ∈ P := by
  have e : (y : D.host.E) = star (x : D.host.E) := hxy.trans (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [Formalism.L2.Col.mem_conjIdeal]
  have : Formalism.L2.Col.cO D.host.E x = y := RingOfIntegers.ext (by rw [e]; exact Formalism.L2.Col.algebraMap_cO x)
  rw [this]

theorem seenCl_of (A : AtTTied u) : SeenCl A := by
  intro w hw v x y hy
  let σ : D.host.E ≃ₐ[ℚ] D.host.E := D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
  let ν : AddValuation D.host.E (WithTop ℤ) :=
    (D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))
  have hyx : y = D.embE (σ (x : D.host.E)) :=
    D.what₂.embLL.injective (hy.trans (RingHom.congr_fun D.embE_φ₀ (σ (x : D.host.E))).symm)
  have hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
      0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF =>
    A.tauOf w hw v zF
  have hseen := A.seenP w hw ((D.fm u).tauOf w v)
  subst hyx
  by_cases hs : (D.fm u).seenP w = true
  · rw [if_pos hs] at hseen ⊢
    exact pos_iff_mem_Pv A v ν hTau hseen x
  · rw [if_neg hs] at hseen ⊢
    let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
    let ν' : AddValuation D.host.E (WithTop ℤ) := ν.comap (D.host.conj : D.host.E →+* D.host.E)
    have hinv := Formalism.L2.Host.conj_conj (D := D) D.host
    have hfix : ∀ zF : 𝓞 D.host.F, D.host.conj (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF =>
      (D.host.conjE_mem_hostF_iff _).1 (zF : D.host.F).2
    have hTau' : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
        0 < ν' ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF => by
      rw [hTau]
      show _ ↔ 0 < ν (D.host.conj _)
      rw [hfix]
    have h1 := pos_iff_mem_Pv A v ν' hTau' hseen (cO x)
    rw [mem_conjIdeal_Pv (A.Pv v) x (cO x) rfl, ← h1]
    show _ ↔ 0 < ν (D.host.conj (D.host.conj (x : D.host.E)))
    rw [hinv]
    rfl

theorem seenCl_atT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, SeenCl (F u).atT :=
  fun _ _ _ _ _ _ F _ _ u => seenCl_of (F u).atT

end GlobalTheory.Mem.Col2.HAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

noncomputable def pvPlace {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) :
    HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := A.Pv v
  isPrime := inferInstance
  ne_bot := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (A.eV v).1.ne_bot
    have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ A.Pv v := (A.res_v v x).1 hx
    rw [h, Ideal.mem_bot] at h1
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E) (by simpa using h1))

theorem pvPlace_isOver {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) :
    IsOver (A.eV v).1 (pvPlace A v) := by
  ext x
  exact A.res_v v x

theorem eq_Pv_or_conj {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT)
    (q : HeightOneSpectrum (𝓞 D.host.E)) (hq : q.under (𝓞 D.host.F) = (A.eV v).1) :
    q.asIdeal = A.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v) := by
  have hov : IsOver (A.eV v).1 q := by
    rw [← hq]
    rfl
  rcases rll_over_cases D.sp.cm (pvPlace_isOver A v) hov with e | e
  · exact Or.inl (congrArg HeightOneSpectrum.asIdeal e)
  · refine Or.inr ?_
    have h1 := conjIdeal_asIdeal (pvPlace A v)
    rw [e, ← h1]
    rfl

theorem primes_over_level_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u v (q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)), q.under (𝓞 (I.rec7 l Z).host.F) = ((F u).atT.eV v).1 → q.asIdeal = (F u).atT.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := (I.rec7 l Z).host.E) ((F u).atT.Pv v) :=
  fun _ _ _ _ _ _ F _ _ u v q hq => eq_Pv_or_conj (F u).atT v q hq

end GlobalTheory.Mem.Col2.HAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.IntNormFinExt

theorem mem_OL_iff_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥K.1), x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  fun l _ K x => GlobalTheory.EmbThroughCompletion.mem_OL_iff K x

end GlobalTheory.IntNormFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTupleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_twistPlace_referenceTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  intro B X I _ v ⟨P, hP, _⟩
  have hEmpty : P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) :=
    I.twistPrimes_reference_tuple_eq_empty ▸ hP
  simp at hEmpty
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgainStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reFace_zero_part_conventions_chosen_again : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  first | exact @GlobalTheory.Mem.R3.reFace_zero_parts | exact GlobalTheory.Mem.R3.reFace_zero_parts | (intros; apply GlobalTheory.Mem.R3.reFace_zero_parts <;> assumption)
end

