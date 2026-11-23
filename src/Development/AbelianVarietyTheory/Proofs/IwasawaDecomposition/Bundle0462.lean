module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAddCharConjEqProdPlaceResidueChars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0410
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRelationPreservesLevelFormLatticeNorm
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.R3.Rw.NormTie

section
open _root_.Formalism.L2.Col
variable {Y : Fields} {Pr : Primes Y} {R : Ranks} (W : Wts Y Pr.Word R) (Ch : Chars Y Pr R.m)
  (sel : HeightOneSpectrum (𝓞 Y.F) → HeightOneSpectrum (𝓞 Y.E)) {S : Set ℕ} (mu : Tup Y.F Y.E Y.K S)
  (P : Formalism.L2.Col.LevFam Y.E Y.K R.r Pr.vGs) (hX : Y.Ok)

theorem isFormOf_zOf (y) : IsFormOf W Ch sel mu hX P (ColTie.zOf W Ch sel mu P hX y) (TieModel.frm W Ch sel mu hX P y) :=
  ⟨(ColTie.resK W Ch sel mu hX).symm (ColTie.formK W Ch sel mu P hX y), ColTie.zOf_mem W Ch sel mu P hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩

end


set_option maxHeartbeats 2000000 in
theorem normAt_eq_norm_tie : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  intro X px I hX Xg tr a O _ φ s t e hcrd x
  have hs := GlobalTheory.Mem.ColTie.zOf_surjective X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX
  obtain ⟨y, rfl⟩ : ∃ y, (GlobalTheory.Mem.ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) = x := hs x
  have hF := isFormOf_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y
  obtain ⟨x', hx', hj⟩ := hcrd y
  have hx2 : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x' (TieModel.frm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) y) := hx'
  have hxx := TieModel.isFormOf_unique (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) hx2 hF
  subst hxx
  rw [← hj]
  have hmk := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX).2
    (InfinitePlace.mk X.B.embLL) (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)
  have hip : (Formalism.L2.Col.mtildeGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)).ip
      (Formalism.L2.Col.mtildeOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I))
      (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 =
      Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y :=
    ColTie.ipLev_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y
  have hin : inner ℂ (t.j y) (t.j y) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) :=
    t.forms.inner y y
  have hσ : ∀ z : X.B.fields.K, X.B.embLL (star z) = starRingEnd ℂ (X.B.embLL z) := ColTie.sig_starCx X.B
  have hn : ((‖t.j y‖ ^ 2 : ℝ) : ℂ) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) := by
    rw [← hin, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [LinearEquiv.refl_apply, Formalism.L2.Col.GSD.ipAt_eq_ipEmb] at hmk
  rcases InfinitePlace.embedding_mk_eq X.B.embLL with he | he
  · rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ, hip] at hmk
    have h2 := Complex.ofReal_injective (hmk.trans hn.symm)
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · have hσ' : ∀ w : X.B.fields.K, (ComplexEmbedding.conjugate X.B.embLL) (star w) =
        starRingEnd ℂ ((ComplexEmbedding.conjugate X.B.embLL) w) := by
      intro w
      simp only [ComplexEmbedding.conjugate_coe_eq, hσ]
    rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ', hip, ComplexEmbedding.conjugate_coe_eq, ← hn, Complex.conj_ofReal] at hmk
    have h2 := Complex.ofReal_injective hmk
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end GlobalTheory.Mem.R3.Rw.NormTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharMemF0Primes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

theorem resChar_symm_conjPl (D : Formalism.BasicNotions.D7) (v : D.what₂.places.Pl) :
    D.what₂.places.resChar (D.plEq.symm (Formalism.DivisionValues.conjPl (D.plEq v))) = D.what₂.places.resChar v := by
  refine Formalism.MainNotions.Inhab.eq_resChar_of_mem D _ _ (D.what₂.places.resChar_prime v) ?_
  rw [Equiv.apply_symm_apply]
  show _ ∈ Ideal.map _ _
  have h := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.what₂.LL) (Formalism.MainNotions.Inhab.resChar_mem D v)
  rwa [map_natCast] at h

theorem resChar_mem_f0Primes : ∀ (K : Ctx) (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K K.s (w.D Z)), B.places.resChar v ∈ GlobalTheory.Mem.NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre := by
  intro K B f T w Z v hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : (w.D Z).what₂.places.resChar ((w.D Z).plEq.symm y) = B.places.resChar v := by
    rcases hy with h | h
    · rw [h]; exact congrArg (w.D Z).what₂.places.resChar ((w.D Z).plEq.symm_apply_apply v)
    · rw [h]; exact resChar_symm_conjPl (w.D Z) v
  unfold F0K FK at hne
  rw [key] at hne
  show B.places.resChar v ∈ ({(w.D Z).host.g 0, (w.D Z).host.g 1, (w.D Z).host.d} ∪
    Finset.range (⌊K.s.X'' (w.D Z).R.n⌋₊ + 1) : Finset ℕ)
  split_ifs at hne with h1 h2 h3
  · obtain ⟨i, hi⟩ := h1
    rw [hi]
    fin_cases i <;> simp
  · refine Finset.mem_union_left _ ?_
    unfold Host.cls primeClass at h2
    split_ifs at h2 with e1 e2 e3 <;> first | simp [e3] | exact absurd h2 (by decide)
  · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h3.2)))
  · exact absurd rfl hne

end GlobalTheory.Mem.NonzeroPlacesOverPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowIdentificationsRealRowSideOfChainComparison
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SideTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {b : Bool}
  {rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {S : RowSide D EE} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE} {ty : Fin n → D.what₂.FT}
  {jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)}

def ids (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowIds S (y.C F) b where
  jE := (LinearEquiv.ofInjective t.jE t.jE_inj).trans (LinearEquiv.ofEq _ _ t.jE_range)
  jM μ hμ j h1 h2 := (LinearEquiv.ofInjective (t.jM μ j) (t.jM_inj μ ((hU μ).1 hμ) j h1 h2)).trans
    (LinearEquiv.ofEq _ _ (t.jM_range μ ((hU μ).1 hμ) j h1 h2))
  jX μ hμ := (S.multTop μ).toLinearEquiv.trans ((LinearEquiv.ofInjective (t.jX μ) (t.jX_inj μ ((hU μ).1 hμ))).trans
    (LinearEquiv.ofEq _ _ (t.jX_range μ ((hU μ).1 hμ))))
  prt π := y.prtE F b (rep π)

theorem real (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowSideReal S (y.C F) b (ids hU t) bs ty := by
  exact {
    parY j hj := by
      show Mult.parB (Ptw D) (min j D.R.m) = Mult.parB (Ptw D) j
      rw [min_eq_left (by have := y.hm; omega)]
    lvl μ _ := GlobalTheory.HilbertLevels.eec_le_cc R F y.tupT y.hm y.hTop b μ
    lvlP μ _ j _ h2 := GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := y.hm; omega)
    lvlX μ _ := GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ
    ee x x' := t.jE_ip x x'
    mult μ hμ j h1 h2 x x' := t.jM_ip μ ((hU μ).1 hμ) j h1 h2 x x'
    multX _ μ hμ x x' := by
      rw [← (S.multTop μ).inner_map_map x x']
      exact t.jX_ip μ ((hU μ).1 hμ) _ _
    io0 _ μ hμ _ x v := by
      have hmem : t.jM μ 1 v ∈ (y.C F).CC b μ 1 :=
        GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := D.R.two_le_m; omega) ((ids hU t).jM μ hμ 1 le_rfl (by have := D.R.two_le_m; omega) v).2
      have e := t.io0 μ ((hU μ).1 hμ) x v hmem
      refine e.trans ?_
      rfl
    io0X h := absurd h (by have := D.R.two_le_m; omega)
    io μ hμ _ j h1 h2 x v := by
      have hmem : t.jM μ (j + 1) v ∈ (y.C F).CC b μ (j + 1) :=
        GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by omega) ((ids hU t).jM μ hμ (j + 1) (by omega) h2 v).2
      exact (t.io μ ((hU μ).1 hμ) j h1 h2 x v hmem).trans rfl
    ioTop h μ hμ _ x v := by
      have hmem : t.jX μ (S.multTop μ v) ∈ (y.C F).CCX b μ :=
        GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ ((ids hU t).jX μ hμ v).2
      exact (t.ioTop μ ((hU μ).1 hμ) x v _ (cast_heq _ _) hmem).trans rfl
    ft σ := by
      have h := t.ft (ty σ)
      have hs : bs σ ∈ Submodule.span ℂ (bs '' {σ' | ty σ' = ty σ}) := Submodule.subset_span ⟨σ, rfl, rfl⟩
      rw [h] at hs
      exact hs
    prt_disj π π' h := t.disj π π' h
  }

end GlobalTheory.Mem.R3.Rw.SideTie


open GlobalTheory.Mem.R3.Rw.SideTie in
theorem GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y _ _ hU b rep EE _ _ _ S n bs ty jA t
  exact ⟨ids hU t, real hU t, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarCharacterEqProdAdditiveCharactersRoot
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem star_character_eq_prod_additive_characters_root : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ (ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → Fin D.R.r → (ZMod (D.host.g kv.1))ˣ), (∀ kv, ψ' kv ≠ 1) ∧ ∀ k ∈ X.K2, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) → star (X.chi2 k) = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j else 0) :=
  by
  intro D X h hE hg
  obtain ⟨ψ', hψ, hchar⟩ := _root_.GlobalTheory.Mem.SymChar.CharProd.psiEf_conj_eq_prod D X h hE hg
  refine ⟨ψ', fun kv i j => if GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j +
      GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j = 1 then 1 else -1, hψ, ?_⟩
  intro k hk Ns hM hU
  have hK : k ∈ X.B.I.Kset := hk.1
  rw [GlobalTheory.Mem.SymChar.otherInstanceCharacter_eq_psi_symmetricArgument, hchar _ _ _ (fun kv => _root_.GlobalTheory.Mem.SymChar.resid_at_w D X h hE hg kv k hK _ (hM kv))
    (fun kv => _root_.GlobalTheory.Mem.SymChar.ResBar.resBar D X h hE hg kv k hK (Ns kv) (hM kv) (hU kv))]
  refine Finset.prod_congr rfl fun kv _ => ?_
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases he : symEdge D.R.rS D.R.k i j
  · simp only [if_pos he]
    rw [← add_mul, ← Int.cast_add]
    rcases GlobalTheory.Mem.SymChar.wt_add D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j with h2 | h2
    · rw [h2]; simp
    · rw [h2]; simp
  · simp only [if_neg he, add_zero]

end GlobalTheory.Mem.SymChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueKernelJetsLiftDegreesAlgebraic
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap


set_option maxHeartbeats 1000000 in
theorem jetC_th_mem_Qbar : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ)
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ColIn.JetsIn I →
    ∀ u μ i, i < B.R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1))
      (m : DVar (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) →₀ ℕ),
      (∀ τ, ∑ β, ∑ α, m (τ, β, α) = ∑ r, nuT (I.rec7 l Z) u i τ r) → jetC (O u μ).dgen ((O u μ).Th i c c') m ∈ Qbar := by
  classical
  intro B X I hOk hPins l Z Qp O hO hJ u μ i hi c c' m hm
  rw [hO.dgen, hO.Th]
  have hdeg : ∀ τ, (monoDeg m τ : ℤ) = nuDeg B u i τ := by
    intro τ
    rw [monoDeg_eq_sum, hm τ, Nat.cast_sum]
    unfold nuDeg
    refine Finset.sum_congr rfl fun r _ => ?_
    have e1 : ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℝ) = DV.nuRow (I.rec7 l Z) u (i + 1) τ r := (nu_t_identity (I.rec7 l Z) u i hi τ r).1
    have e2 := GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2
    have e3 := B.wts.nuW_eq u hi τ r
    have e4 := lamOf_wtN (B.wts.hc u τ) hi.le r
    have key : (((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) : ℝ) = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
      rw [Int.cast_natCast, e1, e2, ← Rat.cast_intCast, e3]
      unfold Wts.lamN at e3 ⊢
      rw [e4]
      rfl
    exact_mod_cast key
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := _root_.GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true I hOk hPins l Z μ u i hi
  set p := (I.stp u μ i).rep c
  set p' := (I.stp u μ (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup μ) (I.cst μ) (I.idx μ) _ _ u i hX hPr
    hOk.sel_ok (hOk.T_mem u) hOk.g_mem (hOk.idx_ok μ) hi ⟨_, _, _, _, hOk.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  have span_of_self_dual {n : ℕ} {L : Submodule (𝓞 B.fields.E) (Sp B.fields.E n)} (hLat : IsSdLat L) :
      Submodule.span B.fields.E (L : Set (Sp B.fields.E n)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp B.fields.E n := fun i => star (f (Pi.single i 1))
    have hpair : hStd B.fields.E n v = f := by
      apply (Pi.basisFun B.fields.E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : B.fields.E) : r • v ∈ L := by
      rw [← show Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L = L from hLat.2, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd B.fields.E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd B.fields.E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := B.fields.E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      -- A nonzero coordinate would make the field finite over its ring of integers.
      let coord := (LinearMap.proj i : Sp B.fields.E n →ₗ[B.fields.E] B.fields.E).restrictScalars (𝓞 B.fields.E)
      have htop : L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.finite_def.mpr (htop ▸ hLat.1.fg.map coord)
      exact RingOfIntegers.not_isField B.fields.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  have hNfull : Submodule.IsFullLattice B.fields.E N :=
    { toIsLattice := hN.1, span_eq_top := span_of_self_dual hN }
  set cA := cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup μ) (I.cst μ) (I.idx μ) u i c.1 c'.1 p p'
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb μ u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hNfull hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb μ u) N N' cA cB hNfull hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u μ i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb μ u) N N')).comap (divLat cA (homAt (I.Sb μ u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb μ u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb μ u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl]
  have hsum := jetC_sum I.A.cD (fun q => I.A.σ₀ (Ξ (r q))) (fun q => I.A.thInd (I.Sb μ u) N N' cB (r q)) hs m
  have hchi : ∀ 𝔞, I.chi 𝔞 ≠ 0 := fun 𝔞 => by
    unfold ColIn.chi chiId
    exact Units.ne_zero _
  have hF0 : I.A.chiF _ _ N N' ≠ 0 := by
    show Th.chiFac B.host I.chi _ _ N N' ≠ 0
    unfold Th.chiFac
    exact mul_ne_zero (zpow_ne_zero _ (hchi _)) (zpow_ne_zero _ (hchi _))
  have hF : I.A.chiF _ _ N N' ∈ B.embLL.fieldRange := by
    show Th.chiFac B.host I.chi _ _ N N' ∈ B.embLL.fieldRange
    unfold Th.chiFac
    have hv := (GlobalTheory.Mem.ChiVal.chi_values B X I hOk).2
    exact mul_mem (zpow_mem (hv _) _) (zpow_mem (hv _) _)
  have hmem : (∑ q, I.A.σ₀ (Ξ (r q)) * jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m) ∈ B.embLL.fieldRange := by
    refine Subfield.sum_mem _ fun q _ => Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
    obtain ⟨y, hy⟩ := hJ.exists_eq (a := μ) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := m) hi
      ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ hdeg
    rw [← mul_inv_cancel_left₀ hF0 (jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m)]
    exact Subfield.mul_mem _ hF ⟨y, hy⟩
  have hQ : ∀ x ∈ B.embLL.fieldRange, x ∈ Qbar := by
    rintro _ ⟨y, rfl⟩
    exact mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y).algHom B.embLL.toRatAlgHom)
  show jetC I.A.cD (fun z => ∑ q, I.A.σ₀ (Ξ (r q)) * I.A.thInd (I.Sb μ u) N N' cB (r q) z) m ∈ Qbar
  rw [hsum]
  exact hQ _ hmem

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeRepresentativesPartsOtherLaterStages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Tr

theorem rowPsi_eq_of_psi {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl

theorem reps_parts_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs
  letI := alg b iK
  have hY0 : (rowPsi a y'.PY).ψ = y.PY.ψ := (by with_unfolding_all exact ((eq_of_heq hs.PY) :))
  have hY : rowPsi a y'.PY = y.PY := rowPsi_eq_of_psi _ _ hY0
  have hW0 : (fun i => (rowPsi a (y'.PW i)).ψ) = (fun i => (y.PW i).ψ) := (by with_unfolding_all exact ((eq_of_heq hs.PW) :))
  have hW : ∀ i, rowPsi a (y'.PW i) = y.PW i := fun i => rowPsi_eq_of_psi _ _ (congrFun hW0 i)
  have hocc : HEq (y'.occ (face b F)) (y.occ F) := by
    unfold Hd.occ principalLevelFrame.OccRows principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.occ F)) :))
  have e : y'.occ (face b F) = y.occ F := (by with_unfolding_all exact ((eq_of_heq hocc) :))
  refine ⟨?_, ?_, ?_⟩
  · intro Φ rep h
    exact ⟨h.fin, fun π => by rw [e]; exact h.mem π, fun π π' hi => h.inj π π' hi, fun ρ hρ => h.all ρ (by rw [e] at hρ; exact hρ)⟩
  · intro bb π
    unfold Hd.prtE principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtE F bb π)) :))
  · intro i π
    unfold Hd.prtW
    rw [isotL_eq a b]
    delta isotLB
    rw [hW i]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtW F i π)) :))

end GlobalTheory.Mem.R3.Tr

end
end

