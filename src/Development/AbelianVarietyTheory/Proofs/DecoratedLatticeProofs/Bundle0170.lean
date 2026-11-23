module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem linearIndependent_of_isParamFunV : ∀ (D : D7) (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ι : Type)
    (f : ι → (GA D V → ℂ)) (B : ι → GlobalTheory.LFun.Fam D.host.E), (∀ i, f i ≠ 0) → (∀ i, GlobalTheory.LFun.IsParamFunV V Sb (f i) (B i)) →
    (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) →
    LinearIndependent ℂ f := by
  intro D V Sb ι f B h0 hP hB
  have hJ := GlobalTheory.LFun.sphOff_KsphC V Sb
  choose a ha using fun i => _root_.GlobalTheory.ParamEigen.eig_of_param D V (KsphC V ∅) (fun _ => 1) Sb hJ (B i)
  have hfix : ∀ i, ∀ v ∉ Sb, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v, ∀ g,
      f i (g * GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k) = f i g := by
    intro i v hv k hk g
    obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
      have := v.isPrime
      obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
    have hx := (hP i v hv w hw).mem_fixed
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hx k hk) g
  let α := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D V) //
    Hecke₂ V (KsphC V ∅) (fun _ => 1) Sb t.1 t.2.1 t.2.2}
  refine GlobalTheory.FinWeil.linearIndependent_of_simultaneous_eigen f (fun i (t : α) => a i t.1.1 t.1.2.1)
    (fun t : α => heckeLin V t.1.2.2) ?_ (fun t i => ha i (f i) (hP i) _ _ _ t.2) h0
  intro i i' hii
  by_contra hne
  obtain ⟨w, hw, hne'⟩ := hB i i' hne
  have hc : ∀ P d R, Hecke₂ V (KsphC V ∅) (fun _ => 1) Sb P d R → heckeLin V R (f i') = a i P d • f i' := by
    intro P d R hR
    have := congrFun hii ⟨(P, d, R), hR⟩
    rw [ha i' (f i') (hP i') P d R hR]
    exact congrArg (· • f i') this.symm
  have h1 := (GlobalTheory.LFun.isParamFunV_iff_isSysParamD hJ (h0 i) (hfix i) (ha i (f i) (hP i)) (B i)).1 (hP i)
  have h2 := (GlobalTheory.LFun.isParamFunV_iff_isSysParamD hJ (h0 i') (hfix i') hc (B i')).1 (hP i')
  exact hne' (GlobalTheory.LFun.IsSysParamOff.unique h1 h2 hw)

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentScaledBasisColumnsMatrixTranspo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem linearIndependent_eX_of_dual {D : D7} (X : HidaSetting D) : LinearIndependent D.host.E X.eX := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  have h1 := congrArg (fun y => (VS D).hT y (X.fY b)) hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, X.ef, map_zero,
    LinearMap.zero_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  simpa using h1

theorem eM_transpose_linearIndependent : ∀ {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → LinearIndependent D.host.E (GlobalTheory.Core.SBesEx.eM X h t lam).transpose := by
  intro D X h t lam ht hl
  set b := X.bas.reindex (finCongr (rank_eq X h)).symm with hb
  have hc : ∀ z, cY X h z = b.equivFun z := by
    intro z; funext k
    simp [cY, HidaSetting.crd, crdOf, hb, Module.Basis.repr_reindex]
  have h0 : LinearIndependent D.host.E (fun a => b.equivFun (X.eX a)) :=
    (linearIndependent_eX_of_dual X).map' b.equivFun.toLinearMap b.equivFun.ker
  have hs : ∀ a, scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have h1 := h0.units_smul (fun a => Units.mk0 (scl t lam a) (hs a))
  have he : (eM X h t lam).transpose =
      (fun a => Units.mk0 (scl t lam a) (hs a)) • fun a => b.equivFun (X.eX a) := by
    funext a k
    simp [eM, hc, Matrix.transpose_apply, Units.smul_def]
  rw [he]
  exact h1

end GlobalTheory.Core.SBesEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalVolumeAgreesRowSubgroupUnitary
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.VolBridge

theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

theorem vol_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hat
  have hLev := GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  haveI : ν.IsAddHaarMeasure := hν.1
  intro j c h γ g hg
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, hJc, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl

  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← _root_.GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := _root_.GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hlam : lamYat (Pr := Pr) (R := R) j P.1 = stdAt X.E _ P.1 := by
    ext v
    simp only [lamYat, if_neg hat.nmem, LocE.lamY, LocE.sclLat, Submodule.mem_comap]
    congr! 1
    funext l
    simp [LocE.scE]
  have hKO : ∀ x : AutY X R j, x ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) ↔ φ x ∈ KO k _ := by
    intro x
    rw [hlam]
    exact GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e x
  have hdN := _root_.GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  refine ⟨?_, ?_⟩
  ·
    have hH := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 le_rfl (by omega) ν
    haveI := hH.2.2.1
    obtain ⟨ho, hAc, hBc⟩ := _root_.GlobalTheory.UnipLevelTopo.isOpen_inf_isCompact J g hJo hJc
    have hst : stabLat (1 : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k) = KO k _ := by
      ext z; simp [stabLat, Subgroup.mem_comap]
    have hvol : volNat ν 1 (Cgrp J g) =
        (volN ν _ (c + 1) 1 ((Cgrp J g).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal /
        (volN ν _ (c + 1) 1 ((KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1))).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal := by
      rw [volNat, hst]
    rw [hvol, _root_.GlobalTheory.VolRatio.vol_ratio _ _ _ ho hAc hBc]
    set K := Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hKdef
    set U := KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hUdef
    have hA : (Cgrp J g).subgroupOf (N k _ (c + 1) 1) = K.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    have hB : (KO k _).subgroupOf (N k _ (c + 1) 1) = U.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    rw [hA, hB, Subgroup.relIndex_subgroupOf inf_le_right, Subgroup.relIndex_subgroupOf inf_le_right]
    have hKc : K.comap φ = Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ⊓ Loc.N1 X.E (R.N j) (cOf R j) := by
      ext x
      show φ x ∈ Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hC, hN1]
    have hUc : U.comap φ = Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) := by
      ext x
      show φ x ∈ KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hKO, hN1]; exact And.comm
    have hden : ∀ z, z ∈ K ∨ z ∈ U → ∃ x, (φ x)⁻¹ * z ∈ K ⊓ U := by
      intro z hz
      have hzN : z ∈ N k _ (c + 1) 1 := by rcases hz with hz | hz; exacts [hz.2, hz.2]
      have hO1 : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
        hJo.preimage (by fun_prop)
      have hO' := hO1.inter (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)))
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | v⁻¹ * z ∈ ({w | g⁻¹ * w * g ∈ J} ∩
          (KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) : Set (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)))} :=
        hO'.preimage (by fun_prop)
      obtain ⟨x, hx, hxV⟩ := hdN z hzN _ hV (by simp [J.one_mem, one_mem])
      refine ⟨x, ?_⟩
      have hxN := (hN1 x).1 hx
      have hm : (φ x)⁻¹ * z ∈ N k _ (c + 1) 1 := mul_mem (inv_mem hxN) hzN
      have hmR : (φ x)⁻¹ * z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := by unfold GlobalTheory.RootEx.R; exact Subgroup.mem_sup_right hm
      exact ⟨⟨mem_Cgrp.2 ⟨hmR, hxV.1⟩, hm⟩, hxV.2, hm⟩
    have h1 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ K U (fun z hz => hden z (Or.inr hz))
    have h2 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ U K (fun z hz => by
      obtain ⟨x, hx⟩ := hden z (Or.inl hz); exact ⟨x, by rwa [inf_comm]⟩)
    rw [hKc, hUc] at h1 h2
    rw [← h1, ← h2]
    simp [Loc.volN, map_div₀, map_natCast]
  · intro hle m hm hm1
    haveI := hm
    set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
    set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
    have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
      hJo.preimage (by fun_prop)
    have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1, z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
      simp [mem_Cgrp, hz]
    have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
    have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) :=
      _root_.GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
    have hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _ := fun y =>
      GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e' y
    have hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
      _root_.GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
    have hden : ∀ z, z ∈ prX (Cgrp J g) ∨ z ∈ KO k _ → ∃ y, (φ' y)⁻¹ * z ∈ prX (Cgrp J g) ⊓ KO k _ := by
      intro z _
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k | v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)} :=
        (hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)
      obtain ⟨y, hy⟩ := _root_.GlobalTheory.denseGL_completion ι hcompl.dense e' z _ hV (by simp [one_mem])
      exact ⟨y, hy⟩
    have hle' : prX (Cgrp J g) ≤ KO k _ := by
      intro z hz
      obtain ⟨y, hy1, hy2⟩ := hden z (Or.inl hz)
      have hyC : φ' y ∈ prX (Cgrp J g) := by
        have := mul_mem hz (inv_mem hy1); simpa using this
      have hyK : φ' y ∈ KO k _ := (hG y).1 (hle ((hP y).2 hyC))
      have := mul_mem hyK hy2; simpa using this
    have hidx := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ' (prX (Cgrp J g)) (KO k _)
      (fun z hz => hden z (Or.inr hz))
    have hc1 : (prX (Cgrp J g)).comap φ' = prCat (Pr := Pr) cst.sharp j P.1 γ := by ext y; exact (hP y).symm
    have hc2 : (KO k _).comap φ' = GLint X.E (R.N j) P.1 := by ext y; exact (hG y).symm
    rw [hc1, hc2] at hidx
    rw [hidx]
    exact _root_.GlobalTheory.OpenVolIndex.measure_toReal_inv_eq_relIndex m _ _ hle' hpo GlobalTheory.SplitFlip.isCompact_KO hm1

end GlobalTheory.VolBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaximalCompactSortedFrameActsThroughModelCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RealData

theorem isKC_comm_Jpq {p q : ℕ} {b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hb : IsKC b) :
    b * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * b := by
  ext a c
  rcases a with i | i <;> rcases c with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
  · rw [hb (Sum.inl i) (Sum.inr j) (by simp [sameBlock]), neg_zero]
  · rw [hb (Sum.inr i) (Sum.inl j) (by simp [sameBlock]), neg_zero]

theorem conj_mem_Kset {n p q : ℕ} (ε : Fin n → Bool) (e : Fin n ≃ Fin p ⊕ Fin q)
    (hJ : (Formalism.UG.Jpq p q).submatrix e e = Formalism.REAL.Jm ε) (fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr)
    (hg : gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g = frᴴ * Formalism.REAL.Jm ε * fr)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hb : IsKC b)
    (hbA : b * fr.submatrix e.symm id = fr.submatrix e.symm id * g) :
    fr * g * fr⁻¹ ∈ Formalism.REAL.Kset ε := by
  have hdet : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hinv : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet

  set X := b.submatrix e e with hX
  have hXfr : X * fr = fr * g := by
    have h1 := congrArg (fun N => N.submatrix e id) hbA
    rw [Matrix.submatrix_mul _ _ _ _ _ e.bijective, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id] at h1
    simpa [Matrix.submatrix_submatrix] using h1
  have hXe : fr * g * fr⁻¹ = X := by
    rw [← hXfr, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hXe]
  have hcomm : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
    rw [← hJ, hX, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective,
      isKC_comm_Jpq hb]

  have hiso : Xᴴ * Formalism.REAL.Jm ε * X = Formalism.REAL.Jm ε := by
    have hgX : g = fr⁻¹ * X * fr := by
      rw [Matrix.mul_assoc, hXfr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hinvH : (fr⁻¹)ᴴ * frᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
    have key : X = fr * g * fr⁻¹ := hXe.symm
    calc Xᴴ * Formalism.REAL.Jm ε * X
        = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g) * fr⁻¹ := by
          rw [key]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (fr⁻¹)ᴴ * frᴴ * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hinvH, hinv, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, hcomm⟩
  rw [Matrix.mem_unitaryGroup_iff']
  change Xᴴ * X = 1
  calc Xᴴ * X = Xᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = Xᴴ * Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc (Xᴴ * Formalism.REAL.Jm ε) X, hcomm]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hiso, Formalism.REAL.Jm_mul_self]

theorem conj_mem_Kset_of_mem_Kinf : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (hV : V.SigOK) (k : GA D V), IsInfFam θ → k ∈ GlobalTheory.Cusp.Kinf θ V (GlobalTheory.ChainOnto.RealData.sortedFrame M hV) → ∀ τ, M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) k * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
  intro D θ V S M hV k hθ hk τ
  obtain ⟨-, hkτ⟩ := GlobalTheory.Cusp.mem_Kinf.1 hk
  obtain ⟨b, hb, hbA⟩ := hkτ τ
  have hU := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  have hU' : (infMat D.sp.cm.sig V.gram (θ τ) k)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) *
      infMat D.sp.cm.sig V.gram (θ τ) k = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
    rw [M.fr_gram τ]; exact hU
  exact conj_mem_Kset (M.ε τ) (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ))
    (Jpq_submatrix _ _) (M.fr τ) _ (M.fr_unit τ) hU' b hb hbA

end GlobalTheory.ChainOnto.RealData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V) → ∀ F ∈ MultT θ M ∅ 1, (∀ w ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), ∀ κ ∈ J, ∀ g, F w (g * κ) = χ κ * F w g) → F ∈ MultT θ M J χ := by
  intro D V S M θ hθ J χ hJ F hF hk
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hF ⊢
  set T : MMap M := PiTensorProduct.lift.symm F with hTdef
  have hT : ∀ v : M.Vec, T v = F (PiTensorProduct.tprod ℂ v) := fun v => by
    rw [hTdef, PiTensorProduct.lift_symm]; rfl
  refine ⟨hF.aut, hF.cusp, fun v κ hκ g => ?_, hF.equiv, hF.cont⟩
  set U : MMap M := heckeOn M {κ} T - χ κ • T with hUdef
  have hU : U ∈ Mult θ M ∅ 1 :=
    sub_mem ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hF (hJ κ hκ)))
      (Submodule.smul_mem _ _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hF))
  have hUv : ∀ (u : M.Vec) (x : GA D V), U u x = T u (x * κ) - χ κ * T u x := fun u x => by
    simp [hUdef, heckeOn, postOn_apply, heckeLin_apply]
  have h0 : U = 0 := GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M ∅ 1 U hU fun u hu => by
    funext x
    rw [hUv, hT, Pi.zero_apply, sub_eq_zero]
    exact hk _ (Submodule.subset_span ⟨u, fun τ => Submodule.subset_span (hu τ), rfl⟩) κ hκ x
  have := hUv v g
  rw [h0] at this
  exact sub_eq_zero.1 this.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapRightTranslateRealPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealPointMove

theorem translate_eq_move : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ k ∈ GinfC V, ∀ v : M.Vec, ∃ v' : M.Vec, (∀ τ, (v' τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ)) ∧ ∀ x, T v (x * k) = T v' x := by
  intro D θ hθ V S M J χ T hT k hk v
  refine ⟨fun τ => ⟨M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ),
    GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) (v τ).2⟩,
    fun τ => rfl, fun x => ?_⟩
  have key := GlobalTheory.RealEquiv.mult_realElt D V S θ M J χ T (Submodule.subset_span hT)
    (fun τ => infMat D.sp.cm.sig V.gram (θ τ) k) (fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) v
    (fun τ => ⟨M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ),
      GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) (v τ).2⟩) (fun τ => rfl)
  rw [← GlobalTheory.RealTransSm.eq_realElt hθ hk] at key
  rw [key]
  rfl

end GlobalTheory.RealPointMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZeroStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero : ∀ (D : D7) (S : Set (FinPl D)) (a b : ℕ), AnalyticOnNhd ℂ (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b) (rightOf 0) ∧ ∀ s : ℂ, 0 < s.re → GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s ≠ 0 ∧ (∀ v : FinPl D, GlobalTheory.LFun.dv D.host.E a b v s ≠ 0) ∧ HasProd (fun v : {v : FinPl D // v ∉ S} => GlobalTheory.LFun.dv D.host.E a b v.1 s) (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s) := by
  first | exact @GlobalTheory.Core.Rk.IP.dSfun_analytic_ne_zero | exact GlobalTheory.Core.Rk.IP.dSfun_analytic_ne_zero | (intros; apply GlobalTheory.Core.Rk.IP.dSfun_analytic_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalParameterBound_split_place : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.BdSplit.paramBound_split | exact GlobalTheory.Core.Rk.BdSplit.paramBound_split | (intros; apply GlobalTheory.Core.Rk.BdSplit.paramBound_split <;> assumption)
end

